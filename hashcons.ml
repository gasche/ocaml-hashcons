(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) Jean-Christophe Filliatre                               *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

(*s Hash tables for hash-consing. (Some code is borrowed from the ocaml
    standard library, which is copyright 1996 INRIA.) *)

type +'a hash_consed = {
  hkey : int;
  tag : int;
  node : 'a }

let gentag =
  let r = ref 0 in
  fun () -> incr r; !r

(* Enable this boolean to get performance information
   during program execution and on program exit. *)
let verbose = false

(* H.t is a representation of hashes as stored within the [hashes]
   array below. We reserve 0 to denote a distinguished 'void' value
   which corresponds to the absence of a key in this position.

   Note: François Pottier's implementation
   ( https://github.com/fpottier/hachis/ ) also contains
   a distinguished 'tomb' value for slots whose key has been removed
   (Hashtbl.remove). For hash-consing we do not need to handle
   explicit removal; we could use tombstones for keys that get erased
   by the GC, but we just leave the hashes around until the next
   resizing or compression.
*)
module H : sig
  type t = private int
  val void : t
  val of_int : int -> t
end = struct
  type t = int
  let void = 0
  let of_int x =
    (* Open-adressing hashtables need hash values that are "random
       enough" so that void elements are spread almost-randomly, to
       avoid long sequences of consecutive non-void elements. In this
       respect they are more sensitive than array-of-bucket designs.

       For example, if you consider the set of consecutive integers
       range [0,999], then (i -> i mod 500) is a reasonable hash
       function for an array-of-bucket design, you will get two
       conflict per hash and thus exactly two elements per bucket. But
       with an open-adressing hashable, it would give terrible
       results: if elements get added in order, when element '500'
       gets added all slots [0,499] will already be taken, so it will
       travel 500 steps until position 500, and similarly all other
       integers in [500,999] will be 500 position away from their
       hash.

       Getting such a consecutive range of hashes with overlaps is
       unfortunately relatively with common hand-written,
       user-provided hash functions, for example one that sends the
       pair (x, y) to the hash (alpha * x + y). These functions would
       provide good performance with an array-of-bucket
       implementation, but can result in catastrophic travel
       statistics for open-addressing schemes.

       To avoid this issue, we multiply the hashes by a large prime
       number (found in hash.c, the C implementation of hashing in the
       OCaml runtime), which will 'spread' consecutive integers to
       a much larger range with gaps between them. *)
    let x = x * 0xcc9e2d51 in
    if x = void then void + 1 else x
end

type 'a t = {
  mutable hashes : H.t array;
  mutable keys : 'a hash_consed Weak.t;
  mutable occupation : int;
  mutable mask : int; (* Array.length hashes - 1
    (note: the length must be a power of two) *)
  travel : int ref;
}

let create sz =
  (* We need to guarantee that there is always at least one [void]
     slot for search to terminate, so [sz] must be at least 1.
     We also guarantee that sizes are always a power of 2,
     to compute the modulo efficiently. *)
  let sz' = ref 1 in
  while !sz' < sz do sz' := 2 * !sz' done;
  let sz = !sz' in
  {
    hashes = Array.make sz H.void;
    keys = Weak.create sz;
    occupation = 0;
    mask = sz - 1;
    travel = ref 0;
  }

let clear t =
  Weak.fill t.keys 0 (Weak.length t.keys) None;
  Array.fill t.hashes 0 (Array.length t.hashes) H.void;
  t.occupation <- 0

let iter f t =
  let len = Array.length t.hashes in
  for i = 0 to len - 1 do
    match Weak.get t.keys i with
    | None -> ()
    | Some hc -> f hc
  done

let locate_calls = ref 0
let locate_travel = ref 0

let () = if verbose then at_exit (fun () ->
  Printf.eprintf "Hashcons locate: calls %d, average travel %g/call\n%!"
    !locate_calls
    (float !locate_travel /. float !locate_calls)
)

let rec locate_gen ~equal t k h =
  if verbose then incr locate_calls;
  let i = (h : H.t :> int) land t.mask in
  locate_gen_loop
    ~equal ~mask:t.mask ~travel:t.travel
    t.keys k t.hashes h i
and locate_gen_loop ~equal ~mask ~travel keys k hashes h i =
  incr travel;
  if verbose then incr locate_travel;
  let h' = Array.unsafe_get hashes i in
  let i' = (i + 1) land mask in
  if h' <> h then
    if h' = H.void then Error i
    else locate_gen_loop ~equal ~mask ~travel keys k hashes h i'
  else
    match Weak.get keys i with
    | Some hc when equal k hc.node -> Ok hc
    | _ ->
      (* When a value has been erased by the GC (case [None]), we must
         keep looking further for another value with the same hash. It
         would be incorrect to treat it as a [void] hash, for the same
         reason that François distinguishes [tomb] from [void]. *)
      locate_gen_loop ~equal ~mask ~travel keys k hashes h i'

let next_sz n = min (2*n) (Sys.max_array_length / 2)

let resize_count = ref 0

let resize_gen ~equal t =
  if verbose then incr resize_count;
  let old_occupation = t.occupation in
  let old_capacity = Array.length t.hashes in
  let old_hashes, old_keys = t.hashes, t.keys in
  let new_capacity = next_sz old_capacity in
  let new_mask = new_capacity - 1 in
  let new_hashes, new_keys =
    Array.make new_capacity H.void,
    Weak.create new_capacity
  in
  t.hashes <- new_hashes;
  t.keys <- new_keys;
  t.mask <- new_mask;
  t.occupation <- 0;
  for i = 0 to old_capacity - 1 do
    match Weak.get old_keys i with
    | None -> ()
    | Some hc ->
      let h = Array.unsafe_get old_hashes i in
      match locate_gen ~equal t hc.node h with
      | Ok _ ->
        failwith "resize: key already in the table?";
      | Error i ->
        t.occupation <- t.occupation + 1;
        Weak.set new_keys i (Some hc);
        new_hashes.(i) <- h;
  done;
  let new_occupation = t.occupation in
  if verbose then
    Printf.eprintf "[%.2d] Resize: size %d=>%d, occupation %d=>%d\n%!"
      !resize_count
      old_capacity new_capacity
      old_occupation new_occupation;
  ()

let compress ~equal t =
  if verbose then incr resize_count;
  let old_occupation = t.occupation in
  let first_void = Array.find_index ((=) H.void) t.hashes |> Option.get in
  let len = Array.length t.hashes in
  for i = 0 to len - 1 do
    let i = (first_void + i) mod len in
    let h = t.hashes.(i) in
    if h <> H.void then
      match Weak.get t.keys i with
      | None ->
        t.occupation <- t.occupation - 1;
        t.hashes.(i) <- H.void;
      | Some hc ->
        match locate_gen ~equal t hc.node h with
        | Ok _ -> ()
        | Error j ->
          Weak.set t.keys j (Some hc);
          Weak.set t.keys i None;
          t.hashes.(j) <- t.hashes.(i);
          t.hashes.(i) <- H.void;
  done;
  let new_occupation = t.occupation in
  if verbose then
    Printf.eprintf "[%.2d] Compression: occupation %d=>%d\n%!"
      !resize_count old_occupation new_occupation;
  ()

let[@inline] capacity t =
  t.mask + 1

let crowded t =
  (* resize at 82% occupation (105/128);
     from François Pottier's [hachis] library. *)
  128 * t.occupation > 105 * capacity t

let calls = ref 0
let hits = ref 0
let misses = ref 0
let () = if verbose then at_exit (fun () ->
  let ratio n = 100. *. float n /. float !calls in
  Printf.eprintf "Hachcons calls %d: hits %d (%g%%), misses %d (%g%%).\n%!"
    !calls
    !hits (ratio !hits)
    !misses (ratio !misses)
)

let hashcons_gen ~hash ~equal t k =
  if verbose then incr calls;
  if crowded t then begin
    (* Our estimation of occupation does not take into account weak
       keys that have been removed by the GC. When the occupation
       becomes high and we consider resizing, we first loook at
       whether the real occupation is low enough that no resizing is
       necessary -- in this case we just compress the data in-place,
       without moving to larger backing arrays. *)
    let real_occupation =
      let count = ref 0 in
      iter (fun _ -> incr count) t;
      !count
    in
    if real_occupation < capacity t / 2
    then compress ~equal t
    else resize_gen ~equal t;
    t.travel := 0;
  end
  else if !(t.travel) > 42 * capacity t then begin
    (* In workloads where hits dominate misses, the table grows very
       slowly, so the crowded criterion rarely applies. It remains
       useful to compress it from time to time, to get a chance to
       remove collected values and thus speedup future lookups.

       To compress regularly, we measure the 'travel' caused by
       lookups, the total number of positions they have visited since
       the last resizing or compression. When they have visited many
       times the total size of the structure, we have amortized the
       cost of a compression.

       On [test_qs.ml] from the [ocaml-hashcons] repository (99.8%
       hit rate), this extra source of compression reduces average
       lookup travel from 5.4 to 1.3, and runtime is reduced from 1.7s
       to 1.3s. *)
    compress ~equal t;
    t.travel := 0;
  end;
  let hkey = hash k in
  let h = H.of_int hkey in
  match locate_gen ~equal t k h with
  | Ok hc ->
    if verbose then incr hits;
    hc
  | Error i ->
    if verbose then incr misses;
    let hc = { hkey; tag = gentag (); node = k } in
    Weak.set t.keys i (Some hc);
    Array.unsafe_set t.hashes i h;
    t.occupation <- t.occupation + 1;
    hc

let stats t =
  (* len: number of non-void hashes. *)
  let len = t.occupation in
  (* count: number of live keys *)
  let count =
    let i = ref 0 in iter (fun _ -> incr i) t; !i in
  (* totlen: total capacity *)
  let totlen = Array.length t.hashes in
  (* For the statistical information that used to correspond to bucket
     sizes, we compute the size of filled intervals in-between void
     keys. *)
  let interval_lens =
    let voids = ref [] in
    Array.iteri (fun i h -> if h == H.void then voids := i :: !voids) t.hashes;
    let voids = Array.of_list (List.rev !voids) in
    List.init (Array.length voids - 1) (fun i ->
      if i < Array.length voids - 1 then
        voids.(i + 1) - voids.(i) - 1
      else
        Array.length t.hashes - voids.(i) - 1
        + voids.(0)
    )
    |> List.filter ((<>) 0) (* filter out empty gaps *)
    |> Array.of_list
  in
  let nb_intervals = Array.length interval_lens in
  Array.sort compare interval_lens;
  (len, count, totlen,
   interval_lens.(0),
   interval_lens.(nb_intervals / 2),
   interval_lens.(nb_intervals - 1))

(* Specialized definitions with Stdlib's hashing and comparison. *)

let hashcons t k =
  hashcons_gen ~hash:Hashtbl.hash ~equal:(=) t k

(* Functorial interface *)

module type HashedType =
  sig
    type t
    val equal : t -> t -> bool
    val hash : t -> int
  end

module type S =
  sig
    type key
    type t
    val create : int -> t
    val clear : t -> unit
    val hashcons : t -> key -> key hash_consed
    val iter : (key hash_consed -> unit) -> t -> unit
    val stats : t -> int * int * int * int * int * int
  end

module Make(K : HashedType) : (S with type key = K.t) = struct
  type key = K.t
  type nonrec t = K.t t

  let create = create
  let clear = clear
  let hashcons t k = hashcons_gen ~hash:K.hash ~equal:K.equal t k
  let iter = iter
  let stats = stats
end


(*s When comparing branching bits, one has to be careful with the sign bit *)
let unsigned_lt n m = n >= 0 && (m < 0 || n < m)

module Hmap = struct

  type 'a key = 'a hash_consed

  type ('a, 'b) t =
    | Empty
    | Leaf of 'a key * 'b
    | Branch of int * int * ('a, 'b) t * ('a, 'b) t

  let empty = Empty

  let is_empty = function Empty -> true | _ -> false

  let zero_bit k m = (k land m) == 0

  let rec mem k = function
    | Empty -> false
    | Leaf (j,_) -> k.tag == j.tag
    | Branch (_, m, l, r) -> mem k (if zero_bit k.tag m then l else r)

  let rec find k = function
    | Empty -> raise Not_found
    | Leaf (j,x) -> if k.tag == j.tag then x else raise Not_found
    | Branch (_, m, l, r) -> find k (if zero_bit k.tag m then l else r)

  let rec find_opt k = function
    | Empty -> None
    | Leaf (j,x) -> if k.tag == j.tag then Some x else None
    | Branch (_, m, l, r) -> find_opt k (if zero_bit k.tag m then l else r)

  let singleton k v = Leaf(k,v)

  let lowest_bit x = x land (-x)

  let branching_bit p0 p1 = lowest_bit (p0 lxor p1)

  let mask p m = p land (m-1)

  let join (p0,t0,p1,t1) =
    let m = branching_bit p0 p1 in
    if zero_bit p0 m then
      Branch (mask p0 m, m, t0, t1)
    else
      Branch (mask p0 m, m, t1, t0)

  let match_prefix k p m = (mask k m) == p

  let add k x t =
    let rec ins = function
      | Empty -> Leaf (k,x)
      | Leaf (j,_) as t ->
	if j.tag == k.tag then
	  Leaf (k,x)
	else
	  join (k.tag, Leaf (k,x), j.tag, t)
      | Branch (p,m,t0,t1) as t ->
	if match_prefix k.tag p m then
	  if zero_bit k.tag m then
	    Branch (p, m, ins t0, t1)
	  else
	    Branch (p, m, t0, ins t1)
	else
	  join (k.tag, Leaf (k,x), p, t)
    in
    ins t

  let branch = function
    | (_,_,Empty,t) -> t
    | (_,_,t,Empty) -> t
    | (p,m,t0,t1)   -> Branch (p,m,t0,t1)

  let remove k t =
    let rec rmv = function
      | Empty -> Empty
      | Leaf (j,_) as t -> if k.tag == j.tag then Empty else t
      | Branch (p,m,t0,t1) as t ->
	if match_prefix k.tag p m then
	  if zero_bit k.tag m then
	    branch (p, m, rmv t0, t1)
	  else
	    branch (p, m, t0, rmv t1)
	else
	  t
    in
    rmv t

  let rec update k f = function
    | Empty -> (match f None with Some v -> Leaf(k,v) | None -> Empty)
    | Leaf (j,x) as t ->
        if k.tag == j.tag then match f (Some x) with
          | None -> Empty
          | Some x -> Leaf(j,x)
        else (match f None with
          | None -> t
          | Some x -> join (k.tag, Leaf (k,x), j.tag, t))
    | Branch (p, m, t0, t1) as t ->
        if match_prefix k.tag p m then
          if zero_bit k.tag m then
            branch (p, m, update k f t0, t1)
          else
            branch (p, m, t0, update k f t1)
        else match f None with
        | None -> t
        | Some x -> join (k.tag, Leaf(k,x), p, t)

  let rec iter f = function
    | Empty -> ()
    | Leaf (k,x) -> f k x
    | Branch (_,_,t0,t1) -> iter f t0; iter f t1

  let rec cardinal = function
    | Empty -> 0
    | Leaf(_,_) -> 1
    | Branch(_,_,l,r) -> cardinal l + cardinal r

  let rec map f = function
    | Empty -> Empty
    | Leaf (k,x) -> Leaf (k, f x)
    | Branch (p,m,t0,t1) -> Branch (p, m, map f t0, map f t1)

  let rec mapi f = function
    | Empty -> Empty
    | Leaf (k,x) -> Leaf (k, f k x)
    | Branch (p,m,t0,t1) -> Branch (p, m, mapi f t0, mapi f t1)

  let rec fold f s accu = match s with
    | Empty -> accu
    | Leaf (k,x) -> f k x accu
    | Branch (_,_,t0,t1) -> fold f t0 (fold f t1 accu)

  let rec exists f = function
    | Empty -> false
    | Leaf (k,v) -> f k v
    | Branch(_,_,l,r) -> exists f l || exists f r

  let rec for_all f = function
    | Empty -> true
    | Leaf (k,v) -> f k v
    | Branch(_,_,l,r) -> for_all f l && for_all f r

  let rec filter f = function
    | Empty -> Empty
    | Leaf(k,v) as t -> if f k v then t else Empty
    | Branch(p,m,t0,t1) -> branch(p, m, filter f t0, filter f t1)

  let rec filter_map f = function
    | Empty -> Empty
    | Leaf(k,v) -> (match f k v with Some v' -> Leaf(k,v') | None -> Empty)
    | Branch(p,m,t0,t1) -> branch(p, m, filter_map f t0, filter_map f t1)

  let split k m =
    fold
      (fun k' v (lt, data, gt) ->
        if k.tag = k'.tag then (lt, Some v, gt)
        else if k.tag < k'.tag then (lt, data, add k' v gt)
        else (add k' v lt, data, gt))
      m (empty, None, empty)

  let bindings s =
    let rec bindings_aux acc = function
      | Empty -> acc
      | Leaf (k,v) -> (k,v) :: acc
      | Branch (_,_,l,r) -> bindings_aux (bindings_aux acc l) r
    in
    bindings_aux [] s

  let to_seq s =
    let rec to_seq_aux acc = function
      | Empty -> acc
      | Leaf (k,v) -> Seq.cons (k,v) acc
      | Branch (_,_,l,r) -> to_seq_aux (to_seq_aux acc l) r
    in
    to_seq_aux Seq.empty s

  let partition f m = fold (fun k v (m_true, m_false) ->
      if f k v then (add k v m_true, m_false) else (m_true, add k v m_false)
    ) m (Empty,Empty)

  let rec choose = function
    | Empty -> raise Not_found
    | Leaf (k, v) -> (k, v)
    | Branch (_, _, t0, _) -> choose t0

  let rec choose_opt = function
    | Empty -> None
    | Leaf (k, v) -> Some (k, v)
    | Branch (_, _, t0, _) -> choose_opt t0

  let rec equal equal_v t1 t2 = match t1, t2 with
    | Empty, Empty -> true
    | Leaf (k1,v1), Leaf (k2,v2) -> k1.tag == k2.tag && equal_v v1 v2
    | Branch (p1,m1,l1,r1), Branch (p2,m2,l2,r2) ->
        p1 = p2 && m1 = m2 && equal equal_v l1 l2 && equal equal_v r1 r2
    | _ -> false

  let rec compare compare_v t1 t2 = match t1,t2 with
    | Empty, Empty -> 0
    | Empty, _ -> -1
    | _, Empty -> 1
    | Leaf (k1,v1), Leaf (k2,v2) ->
        let cmp = Int.compare k1.tag k2.tag in
        if cmp = 0 then compare_v v1 v2 else cmp
    | Leaf _, Branch _ -> -1
    | Branch _, Leaf _ -> 1
    | Branch (p1,m1,l1,r1), Branch (p2,m2,l2,r2) ->
        let cmp = Int.compare p1 p2 in
        if cmp <> 0 then cmp else
        let cmp = Int.compare m1 m2 in
        if cmp <> 0 then cmp else
        let cmp = compare compare_v l1 l2 in
        if cmp <> 0 then cmp else
        compare compare_v r1 r2

  let merge f l r =
    let merge_l t = filter_map (fun k v -> f k (Some v) None) t in
    let merge_r t = filter_map (fun k v -> f k None (Some v)) t in
    let rec merge_aux l r = match l, r with
    | Empty, t -> merge_r t
    | t, Empty -> merge_l t
    | Leaf (k,v1), t ->
        filter_map (
          fun k' v -> f k' (if k.tag = k'.tag then (Some v1) else None) (Some v)
        ) t
    | t, Leaf (k,v2) ->
        filter_map (
          fun k' v -> f k' (Some v) (if k.tag = k'.tag then (Some v2) else None)
        ) t
    | (Branch (p,m,l0,l1) as l), (Branch (q,n,r0,r1) as r) ->
        if m = n && match_prefix q p m
        then branch (p, m, merge_aux l0 r0, merge_aux l1 r1)
        else if unsigned_lt m n && match_prefix q p m then
          (* [q] contains [p]. Merge [t] with a subtree of [s]. *)
          if zero_bit q m
          then branch (p, m, merge_aux l0 r, merge_l l1)
          else branch (p, m, merge_l l0, merge_aux l1 r)
        else if unsigned_lt n m && match_prefix p q n then
          (* [p] contains [q]. Merge [s] with a subtree of [t]. *)
          if zero_bit p n
          then branch (q, n, merge_aux l r0, merge_r r1)
          else branch (q, n, merge_r r0, merge_aux l r1)
        else
          (* The prefixes disagree, so the trees are disjoint. *)
          join (p, merge_l l, q, merge_r r)
        in merge_aux l r

  let rec union f l r = match l, r with
    | Empty, t
    | t, Empty -> t
    | Leaf (k,v1), t ->
        update k (function None -> Some v1 | Some v2 -> f k v1 v2) t
    | t, Leaf (k,v2) ->
        update k (function None -> Some v2 | Some v1 -> f k v1 v2) t
    | (Branch (p,m,s0,s1) as s), (Branch (q,n,t0,t1) as t) ->
        if m = n && match_prefix q p m
        then branch (p, m, union f s0 t0, union f s1 t1)
        else if unsigned_lt m n && match_prefix q p m then
          (* [q] contains [p]. Merge [t] with a subtree of [s]. *)
          if zero_bit q m
          then branch (p, m, union f s0 t, s1)
          else branch (p, m, s0, union f s1 t)
        else if unsigned_lt n m && match_prefix p q n then
          (* [p] contains [q]. Merge [s] with a subtree of [t]. *)
          if zero_bit p n
          then branch (q, n, union f s t0, t1)
          else branch (q, n, t0, union f s t1)
        else
          (* The prefixes disagree. *)
          join (p, s, q, t)

  let min_binding_opt m =
    fold
      (fun k v b ->
        match b with
        | None -> Some (k, v)
        | Some (k', _) -> if k'.tag <= k.tag then b else Some (k, v))
      m None

  let min_binding m = match min_binding_opt m with
    | Some x -> x
    | None -> raise Not_found

  let max_binding_opt m =
    fold
      (fun k v b ->
        match b with
        | None -> Some (k, v)
        | Some (k', _) -> if k'.tag >= k.tag then b else Some (k, v))
      m None

  let max_binding m = match max_binding_opt m with
    | Some x -> x
    | None -> raise Not_found

  let find_first_opt f m =
    fold
      (fun k v acc ->
        match acc with
        | None -> if f k then Some (k, v) else None
        | Some (k', _) ->
            if k'.tag <= k.tag then acc else
            if f k then Some (k, v) else acc)
      m None

  let find_first f m = match find_first_opt f m with
    | Some x -> x
    | None -> raise Not_found

  let find_last_opt f m =
    fold
      (fun k v acc ->
        match acc with
        | None -> if f k then Some (k, v) else None
        | Some (k', _) ->
            if k'.tag >= k.tag then acc else
            if f k then Some (k, v) else acc)
      m None

  let find_last f m = match find_last_opt f m with
    | Some x -> x
    | None -> raise Not_found

  let add_seq seq m = Seq.fold_left (fun m (k, v) -> add k v m) m seq
  let of_seq s = add_seq s Empty

  (*s Extra functions not in [Map.S] *)

  let find_any (type a b) f (m : (a, b) t) =
    let exception Found of (a key * b) in
    try
      iter (fun k v -> if f k v then raise (Found (k, v))) m;
      raise Not_found
    with Found x -> x
  let find_any_opt (type a b) f (m : (a, b) t) =
    let exception Found of (a key * b) in
    try
      iter (fun k v -> if f k v then raise (Found (k, v))) m;
      None
    with Found x -> Some x

  let is_singleton = function
    | Leaf(k,v) -> Some (k,v)
    | _ -> None
end

module Hset = struct
  (*s Sets of integers implemented as Patricia trees, following Chris
      Okasaki and Andrew Gill's paper {\em Fast Mergeable Integer Maps}
      ({\tt\small http://www.cs.columbia.edu/\~{}cdo/papers.html\#ml98maps}).
      Patricia trees provide faster operations than standard library's
      module [Set], and especially very fast [union], [subset], [inter]
      and [diff] operations. *)

  (*s The idea behind Patricia trees is to build a {\em trie} on the
      binary digits of the elements, and to compact the representation
      by branching only one the relevant bits (i.e. the ones for which
      there is at least on element in each subtree). We implement here
      {\em little-endian} Patricia trees: bits are processed from
      least-significant to most-significant. The trie is implemented by
      the following type [t]. [Empty] stands for the empty trie, and
      [Leaf k] for the singleton [k]. (Note that [k] is the actual
      element.) [Branch (m,p,l,r)] represents a branching, where [p] is
      the prefix (from the root of the trie) and [m] is the branching
      bit (a power of 2). [l] and [r] contain the subsets for which the
      branching bit is respectively 0 and 1. Invariant: the trees [l]
      and [r] are not empty. *)

  (*i*)
  type 'a elt = 'a hash_consed
  (*i*)

  type 'a t =
    | Empty
    | Leaf of 'a hash_consed
    | Branch of int * int * 'a t * 'a t

  (*s Example: the representation of the set $\{1,4,5\}$ is
      $$\mathtt{Branch~(0,~1,~Leaf~4,~Branch~(1,~4,~Leaf~1,~Leaf~5))}$$
      The first branching bit is the bit 0 (and the corresponding prefix
      is [0b0], not of use here), with $\{4\}$ on the left and $\{1,5\}$ on the
      right. Then the right subtree branches on bit 2 (and so has a branching
      value of $2^2 = 4$), with prefix [0b01 = 1]. *)

  (*s Empty set and singletons. *)

  let empty = Empty

  let is_empty = function Empty -> true | _ -> false

  let singleton k = Leaf k

  (*s Testing the occurrence of a value is similar to the search in a
      binary search tree, where the branching bit is used to select the
      appropriate subtree. *)

  let zero_bit k m = (k land m) == 0

  let rec mem k = function
    | Empty -> false
    | Leaf j -> k.tag == j.tag
    | Branch (_, m, l, r) -> mem k (if zero_bit k.tag m then l else r)

  let find k s = if mem k s then k else raise Not_found
  let find_opt k s = if mem k s then Some k else None

  (*s The following operation [join] will be used in both insertion and
      union. Given two non-empty trees [t0] and [t1] with longest common
      prefixes [p0] and [p1] respectively, which are supposed to
      disagree, it creates the union of [t0] and [t1]. For this, it
      computes the first bit [m] where [p0] and [p1] disagree and create
      a branching node on that bit. Depending on the value of that bit
      in [p0], [t0] will be the left subtree and [t1] the right one, or
      the converse. Computing the first branching bit of [p0] and [p1]
      uses a nice property of twos-complement representation of integers. *)

  let lowest_bit x = x land (-x)

  let branching_bit p0 p1 = lowest_bit (p0 lxor p1)

  let mask p m = p land (m-1)

  let join (p0,t0,p1,t1) =
    let m = branching_bit p0 p1 in
    if zero_bit p0 m then
      Branch (mask p0 m, m, t0, t1)
    else
      Branch (mask p0 m, m, t1, t0)

  (*s Then the insertion of value [k] in set [t] is easily implemented
      using [join].  Insertion in a singleton is just the identity or a
      call to [join], depending on the value of [k].  When inserting in
      a branching tree, we first check if the value to insert [k]
      matches the prefix [p]: if not, [join] will take care of creating
      the above branching; if so, we just insert [k] in the appropriate
      subtree, depending of the branching bit. *)

  let match_prefix k p m = (mask k m) == p

  let add k t =
    let rec ins = function
      | Empty -> Leaf k
      | Leaf j as t ->
	if j.tag == k.tag then t else join (k.tag, Leaf k, j.tag, t)
      | Branch (p,m,t0,t1) as t ->
	if match_prefix k.tag p m then
	  if zero_bit k.tag m then
	    Branch (p, m, ins t0, t1)
	  else
	    Branch (p, m, t0, ins t1)
	else
	  join (k.tag, Leaf k, p, t)
    in
    ins t

  (*s The code to remove an element is basically similar to the code of
      insertion. But since we have to maintain the invariant that both
      subtrees of a [Branch] node are non-empty, we use here the
      ``smart constructor'' [branch] instead of [Branch]. *)

  let branch = function
    | (_,_,Empty,t) -> t
    | (_,_,t,Empty) -> t
    | (p,m,t0,t1)   -> Branch (p,m,t0,t1)

  let remove k t =
    let rec rmv = function
      | Empty -> Empty
      | Leaf j as t -> if k.tag == j.tag then Empty else t
      | Branch (p,m,t0,t1) as t ->
	if match_prefix k.tag p m then
	  if zero_bit k.tag m then
	    branch (p, m, rmv t0, t1)
	  else
	    branch (p, m, t0, rmv t1)
	else
	  t
    in
    rmv t

  (*s One nice property of Patricia trees is to support a fast union
      operation (and also fast subset, difference and intersection
      operations). When merging two branching trees we examine the
      following four cases: (1) the trees have exactly the same
      prefix; (2/3) one prefix contains the other one; and (4) the
      prefixes disagree. In cases (1), (2) and (3) the recursion is
      immediate; in case (4) the function [join] creates the appropriate
      branching. *)

  let rec merge = function
    | Empty, t  -> t
    | t, Empty  -> t
    | Leaf k, t -> add k t
    | t, Leaf k -> add k t
    | (Branch (p,m,s0,s1) as s), (Branch (q,n,t0,t1) as t) ->
      if m == n && match_prefix q p m then
	(* The trees have the same prefix. Merge the subtrees. *)
	Branch (p, m, merge (s0,t0), merge (s1,t1))
      else if unsigned_lt m n && match_prefix q p m then
	(* [q] contains [p]. Merge [t] with a subtree of [s]. *)
	if zero_bit q m then
	  Branch (p, m, merge (s0,t), s1)
        else
	  Branch (p, m, s0, merge (s1,t))
      else if unsigned_lt n m && match_prefix p q n then
	(* [p] contains [q]. Merge [s] with a subtree of [t]. *)
	if zero_bit p n then
	  Branch (q, n, merge (s,t0), t1)
	else
	  Branch (q, n, t0, merge (s,t1))
      else
	(* The prefixes disagree. *)
	join (p, s, q, t)

  let union s t = merge (s,t)

  (*s When checking if [s1] is a subset of [s2] only two of the above
      four cases are relevant: when the prefixes are the same and when the
      prefix of [s1] contains the one of [s2], and then the recursion is
      obvious. In the other two cases, the result is [false]. *)

  let rec subset s1 s2 = match (s1,s2) with
    | Empty, _ -> true
    | _, Empty -> false
    | Leaf k1, _ -> mem k1 s2
    | Branch _, Leaf _ -> false
    | Branch (p1,m1,l1,r1), Branch (p2,m2,l2,r2) ->
      if m1 == m2 && p1 == p2 then
	subset l1 l2 && subset r1 r2
      else if unsigned_lt m2 m1 && match_prefix p1 p2 m2 then
	if zero_bit p1 m2 then
	  subset l1 l2 && subset r1 l2
	else
	  subset l1 r2 && subset r1 r2
      else
	false

  (*s To compute the intersection and the difference of two sets, we
      still examine the same four cases as in [merge]. The recursion is
      then obvious. *)

  let rec inter s1 s2 = match (s1,s2) with
    | Empty, _ -> Empty
    | _, Empty -> Empty
    | Leaf k1, _ -> if mem k1 s2 then s1 else Empty
    | _, Leaf k2 -> if mem k2 s1 then s2 else Empty
    | Branch (p1,m1,l1,r1), Branch (p2,m2,l2,r2) ->
      if m1 == m2 && p1 == p2 then
	merge (inter l1 l2, inter r1 r2)
      else if unsigned_lt m1 m2 && match_prefix p2 p1 m1 then
	inter (if zero_bit p2 m1 then l1 else r1) s2
      else if unsigned_lt m2 m1 && match_prefix p1 p2 m2 then
	inter s1 (if zero_bit p1 m2 then l2 else r2)
      else
	Empty

  let rec diff s1 s2 = match (s1,s2) with
    | Empty, _ -> Empty
    | _, Empty -> s1
    | Leaf k1, _ -> if mem k1 s2 then Empty else s1
    | _, Leaf k2 -> remove k2 s1
    | Branch (p1,m1,l1,r1), Branch (p2,m2,l2,r2) ->
      if m1 == m2 && p1 == p2 then
	merge (diff l1 l2, diff r1 r2)
      else if unsigned_lt m1 m2 && match_prefix p2 p1 m1 then
	if zero_bit p2 m1 then
	  merge (diff l1 s2, r1)
	else
	  merge (l1, diff r1 s2)
      else if unsigned_lt m2 m1 && match_prefix p1 p2 m2 then
	if zero_bit p1 m2 then diff s1 l2 else diff s1 r2
      else
	s1

  (*s All the following operations ([cardinal], [iter], [fold], [for_all],
      [exists], [filter], [partition], [choose], [choose_opt], [elements],
      [to_seq]) are implemented as for any other kind of binary trees. *)

  let rec cardinal = function
    | Empty -> 0
    | Leaf _ -> 1
    | Branch (_,_,t0,t1) -> cardinal t0 + cardinal t1

  let rec iter f = function
    | Empty -> ()
    | Leaf k -> f k
    | Branch (_,_,t0,t1) -> iter f t0; iter f t1

  let rec fold f s accu = match s with
    | Empty -> accu
    | Leaf k -> f k accu
    | Branch (_,_,t0,t1) -> fold f t0 (fold f t1 accu)

  let rec for_all p = function
    | Empty -> true
    | Leaf k -> p k
    | Branch (_,_,t0,t1) -> for_all p t0 && for_all p t1

  let rec exists p = function
    | Empty -> false
    | Leaf k -> p k
    | Branch (_,_,t0,t1) -> exists p t0 || exists p t1

  let rec filter pr = function
    | Empty -> Empty
    | Leaf k as t -> if pr k then t else Empty
    | Branch (p,m,t0,t1) -> branch (p, m, filter pr t0, filter pr t1)

  let partition p s =
    let rec part (t,f as acc) = function
      | Empty -> acc
      | Leaf k -> if p k then (add k t, f) else (t, add k f)
      | Branch (_,_,t0,t1) -> part (part acc t0) t1
    in
    part (Empty, Empty) s

  let rec choose = function
    | Empty -> raise Not_found
    | Leaf k -> k
    | Branch (_, _,t0,_) -> choose t0   (* we know that [t0] is non-empty *)

  let rec choose_opt = function
    | Empty -> None
    | Leaf k -> Some k
    | Branch (_, _,t0,_) -> choose_opt t0   (* we know that [t0] is non-empty *)

  let elements s =
    let rec elements_aux acc = function
      | Empty -> acc
      | Leaf k -> k :: acc
      | Branch (_,_,l,r) -> elements_aux (elements_aux acc l) r
    in
    elements_aux [] s

  let to_seq s =
    let rec to_seq_aux acc = function
      | Empty -> acc
      | Leaf k -> Seq.cons k acc
      | Branch (_,_,l,r) -> to_seq_aux (to_seq_aux acc r) l
    in
    to_seq_aux Seq.empty s

  let split elt s =
    fold (fun elt' (lt, present, gt) ->
      if elt'.tag < elt.tag then (add elt' lt, present, gt) else
      if elt'.tag > elt.tag then (lt, present, add elt' gt) else
      (lt, true, gt)
    ) s (Empty, false, Empty)

  (*s [map] and [filter_map] are implemented via [fold] and [add]
      since we can't relate the tag of [f elt] to that of [elt] *)
  let map f s = fold (fun elt s -> add (f elt) s) s Empty
  let filter_map f s = fold (fun elt s ->
      match f elt with
        | None -> s
        | Some elt' -> add elt' s)
    s Empty

  let add_seq seq s = Seq.fold_left (fun s elt -> add elt s) s seq

  let of_seq seq = add_seq seq Empty

  let of_list list = List.fold_left (fun s elt -> add elt s) Empty list

  (*s There is no way to give an efficient implementation of [min_elt]
      and [max_elt], as with binary search trees.  The following
      implementation is a traversal of all elements, barely more
      efficient than [fold min t (choose t)] (resp. [fold max t (choose
      t)]). Note that we use the fact that there is no constructor
      [Empty] under [Branch] and therefore always a minimal
      (resp. maximal) element there. *)

  let rec min_elt = function
    | Empty -> raise Not_found
    | Leaf k -> k
    | Branch (_,_,s,t) -> min (min_elt s) (min_elt t)

  let min_elt_opt = function
    | Empty -> None
    | x -> Some (min_elt x)

  let rec max_elt = function
    | Empty -> raise Not_found
    | Leaf k -> k
    | Branch (_,_,s,t) -> max (max_elt s) (max_elt t)

  let max_elt_opt = function
    | Empty -> None
    | x -> Some (max_elt x)

  (*s [find_first], [find_last] and their opt versions are less efficient
      then with binary search trees. They are linear time and can call [f] an
      arbitrary number of times, and not necessarily on elements smaller/larger
      than the witness. *)
  let find_first_opt f s =
    fold
      (fun elt acc ->
        match acc with
        | None -> if f elt then Some elt else None
        | Some witness ->
            if witness.tag <= elt.tag then acc else
            if f elt then Some elt else acc)
      s None

  let find_first f s =
    match find_first_opt f s with
      | Some elt -> elt
      | None -> raise Not_found

  let find_last_opt f s =
    fold
      (fun elt acc ->
        match acc with
        | None -> if f elt then Some elt else None
        | Some witness ->
            if witness.tag >= elt.tag then acc else
            if f elt then Some elt else acc)
      s None

  let find_last f s =
    match find_last_opt f s with
      | Some elt -> elt
      | None -> raise Not_found

  (*s Another nice property of Patricia trees is to be independent of the
      order of insertion. As a consequence, two Patricia trees have the
      same elements if and only if they are structurally equal.

      We could use OCaml's [=] and [compare] for this, but it's faster
      to reimplement them as we have a faster comparison on elements (comparing
      tags), where the standard comparisons will inspect the elements in depth.
       *)

  let rec equal l r = match (l, r) with
    | Empty, Empty -> true
    | Leaf l, Leaf r -> l.tag == r.tag
    | Branch (ai, aj, al, ar), Branch (bi, bj, bl, br) ->
        ai == bi && aj == bj && equal al bl && equal ar br
    | _ -> false


  let rec compare l r = match (l, r) with
    | Empty, Empty -> 0
    | Empty, _ -> -1
    | _, Empty -> 1
    | Leaf l, Leaf r -> Int.compare l.tag r.tag
    | Leaf _, _ -> -1
    | _, Leaf _ -> 1
    | Branch (ai, aj, al, ar), Branch (bi, bj, bl, br) ->
        let cmp = Int.compare ai bi in
        if cmp <> 0 then cmp else
        let cmp = Int.compare aj bj in
        if cmp <> 0 then cmp else
        let cmp = compare al bl in
        if cmp <> 0 then cmp else
        compare ar br

  (*i*)
  let _make l = List.fold_right add l empty
  (*i*)

  (*s Additional functions w.r.t to [Set.S]. *)

  let rec intersect s1 s2 = match (s1,s2) with
    | Empty, _ -> false
    | _, Empty -> false
    | Leaf k1, _ -> mem k1 s2
    | _, Leaf k2 -> mem k2 s1
    | Branch (p1,m1,l1,r1), Branch (p2,m2,l2,r2) ->
      if m1 == m2 && p1 == p2 then
        intersect l1 l2 || intersect r1 r2
      else if unsigned_lt m1 m2 && match_prefix p2 p1 m1 then
        intersect (if zero_bit p2 m1 then l1 else r1) s2
      else if unsigned_lt m2 m1 && match_prefix p1 p2 m2 then
        intersect s1 (if zero_bit p1 m2 then l2 else r2)
      else
        false

  let disjoint s1 s2 = not (intersect s1 s2)

  let find_any (type a) f (s : a t) =
    let exception Found of a elt in
    try
      iter (fun elt -> if f elt then raise (Found elt)) s;
      raise Not_found
    with Found elt -> elt
  let find_any_opt (type a) f (s : a t) =
    let exception Found of a elt in
    try
      iter (fun elt -> if f elt then raise (Found elt)) s;
      None
    with Found elt -> Some elt

  let bind f s = fold (fun elt s -> union (f elt) s) s empty

  let is_singleton = function
    | Leaf elt -> Some elt
    | _ -> None

end
