
type t =
  | Pvar of string
  | Pnot of t
  | Pand of t * t
  | Por of  t * t
  | Pimp of t * t
  | Piff of t * t
  | Ptrue
  | Pfalse

let pand p1 p2 = match p1, p2 with
  | Ptrue, p2 -> p2
  | p1, Ptrue -> p1
  | _ -> Pand (p1, p2)

let pands i j f =
  let rec mk k = if k > j then Ptrue else pand (f k) (mk (k+1)) in
  mk i

let piff p1 p2 = match p1, p2 with
  | Ptrue, p2 -> p2
  | p1, Ptrue -> p1
  | _ -> Piff (p1, p2)

let piffs i j f =
  let rec mk k = if k > j then Ptrue else piff (f k) (mk (k+1)) in
  mk i

let por p1 p2 = match p1, p2 with
  | Pfalse, _p2 -> p1
  | p1, Pfalse -> p1
  | _ -> Por (p1, p2)

let pors i j f =
  let rec mk k = if k > j then Pfalse else por (f k) (mk (k+1)) in
  mk i

(* de bruijn *)

let var i = Pvar ("p" ^ string_of_int i)

let iff p1 p2 = Pand (Pimp (p1, p2), Pimp (p2, p1))

(**
de_bruijn_p(n) == LHS(2*n+1) -> RHS(2*n+1)
de_bruijn_n(n) == LHS(2*n) -> (p0 v RHS(2*n) v ~p0)

RHS(m) = &&_{i=1..m} p(i)
LHS(m) = &&_{i=1..m} ((p(i)<->p(i+1)) -> c(n))
where addition is computed modulo m.
***)

let lhs m =
  pands 1 m (fun i -> Pnot (iff (var i) (var (if i=m then 1 else i+1))))

let de_bruijn_p n = Pnot (lhs (2*n+1))
let de_bruijn_n n = Pnot (lhs (2*n))

(* pigeons

ph_p(n) =def left(n) -> right(n)

left(n) =def &&_{p=1..n+1} (vv_{j=1,..n} occ(i,j) )
right(n) =def vv_{h=1..n, p1=1..{n+1}, p2={p1+1}..{n+1}} s(i1,i2,j)
s(p1,p2,h) =def occ(p1,h) & occ(p2,h)

*)

let occ i j = Pvar ("occ_" ^ string_of_int i ^ "_" ^ string_of_int j)

let left n = pands 1 (n+1) (fun i -> pors 1 n (fun j -> occ i j))
let right n =
  pors 1 n (fun h ->
	      pors 1 (n+1) (fun p1 ->
			      pors (p1+1) (n+1) (fun p2 -> Pand (occ p1 h,
							    occ p2 h))))

let pigeon_p n = Pimp (left n, right n)

let equiv_p n =
  let f = ref (var n) in
  for i = 1 to n-1 do f := Piff (var (n-i), !f) done;
  for i = 1 to n do f := Piff (var (n+1-i), !f) done;
  !f

let print fmt p =
  let open Printf in
  let rec pr fmt = function
    | Pvar s -> fprintf fmt "%s" s
    | Pnot f -> fprintf fmt "(~%a)" pr f
    | Pand (f1, f2) -> fprintf fmt "(%a &@ %a)" pr f1 pr f2
    | Por (f1, f2) -> fprintf fmt "(%a v@ %a)" pr f1 pr f2
    | Pimp (f1, f2) -> fprintf fmt "(%a ->@ %a)" pr f1 pr f2
    | Piff (f1, f2) -> fprintf fmt "(%a <->@ %a)" pr f1 pr f2
    | Ptrue -> fprintf fmt "true"
    | Pfalse -> fprintf fmt "false"
  in
  fprintf fmt "@[%a@]" pr p


module Workload () = struct
(* BDD *)

open Hashcons

type variable = int (* 1..max_var *)

let max_var = ref 10
let get_max_var () = !max_var
let set_max_var n = if n <= 0 then invalid_arg "Bdd.set_max_var"; max_var := n

type bdd = view hash_consed
and view = Zero | One | Node of variable * bdd (*low*) * bdd (*high*)

let view b = b.node

module HC = Hashcons.Make(
  struct
    type t = view
    let equal x y = match x, y with
      | (Zero | One), (Zero | One) ->
	  x == y
      | Node (v1, l1, h1), Node (v2, l2, h2) ->
	  v1 == v2 && l1 == l2 && h1 == h2
      | _ ->
	  false
    let hash = function
      | Zero -> 0
      | One -> 1
      | Node (v, l, h) -> abs (19 * (19 * l.tag + h.tag) + v)
  end)

let htable = HC.create 251

let zero = HC.hashcons htable Zero
let one = HC.hashcons htable One

let var b = match b.node with
  | Zero | One -> !max_var + 1
  | Node (v, _, _) -> v

let low b = match b.node with
  | Zero | One -> invalid_arg "Bdd.low"
  | Node (_, l, _) -> l

let high b = match b.node with
  | Zero | One -> invalid_arg "Bdd.low"
  | Node (_, _, h) -> h

let mk v ~low ~high =
  if low == high then low else HC.hashcons htable (Node (v, low, high))

let mk_var v = mk v ~low:zero ~high:one

module Bdd = struct
  type t = bdd
  let equal = (==)
  let hash b = b.tag
  let compare b1 b2 = Stdlib.compare b1.tag b2.tag
end
module H1 = Hashtbl.Make(Bdd)

let mk_not x =
  let cache = H1.create 251 in
  let rec mk_not_rec x =
    try
      H1.find cache x
    with Not_found ->
      let res = match x.node with
	| Zero -> one
	| One -> zero
	| Node (v, l, h) -> mk v ~low:(mk_not_rec l) ~high:(mk_not_rec h)
      in
      H1.add cache x res;
      res
  in
  mk_not_rec x

let bool_of = function Zero -> false | One -> true | _ -> invalid_arg "bool_of"
let of_bool b = if b then one else zero

module H2 = Hashtbl.Make(
  struct
    type t = bdd * bdd
    let equal (u1,v1) (u2,v2) = u1==u2 && v1==v2
    let hash (u,v) =
      (*abs (19 * u.tag + v.tag)*)
      let s = u.tag + v.tag in abs (s * (s+1) / 2 + u.tag)
  end)

let apply op =
  let op_z_z = of_bool (op false false) in
  let op_z_o = of_bool (op false true) in
  let op_o_z = of_bool (op true false) in
  let op_o_o = of_bool (op true true) in
  fun b1 b2 ->
    let cache = H2.create 251 in
    let rec app ((u1,u2) as u12) =
      try
	H2.find cache u12
      with Not_found ->
	let res = match u1.node, u2.node with
	  | Zero, Zero -> op_z_z
	  | Zero, One  -> op_z_o
	  | One,  Zero -> op_o_z
	  | One,  One  -> op_o_o
	  | _ ->
	      let v1 = var u1 in
	      let v2 = var u2 in
	      if v1 == v2 then
		mk v1 ~low:(app (low u1, low u2)) ~high:(app (high u1, high u2))
	      else if v1 < v2 then
		mk v1 ~low:(app (low u1, u2)) ~high:(app (high u1, u2))
	      else (* v1 > v2 *)
		mk v2 ~low:(app (u1, low u2)) ~high:(app (u1, high u2))
	in
	H2.add cache u12 res;
	res
    in
    app (b1, b2)


type boolean_op = bool -> bool -> bool
let op_and = (&&)
let op_or = (||)
let op_imp b1 b2 = (not b1) || b2

let mk_and = apply op_and
let mk_or = apply op_or
let mk_imp = apply op_imp

(* satisfiability *)

let is_sat b = b.node != Zero

let tautology b = b.node == One

(* formula -> bdd *)

type formula =
  | Ffalse
  | Ftrue
  | Fvar of variable
  | Fand of formula * formula
  | For  of formula * formula
  | Fimp of formula * formula
  | Fnot of formula

let rec build = function
  | Ffalse -> zero
  | Ftrue -> one
  | Fvar v -> mk_var v
  | Fand (f1, f2) -> mk_and (build f1) (build f2)
  | For (f1, f2) -> mk_or (build f1) (build f2)
  | Fimp (f1, f2) -> mk_imp (build f1) (build f2)
  | Fnot f -> mk_not (build f)


let bdd_of_formula f =
  let nbvar = ref 0 in
  let vars = Hashtbl.create 17 in
  let rec trans = function
    | Pvar s ->
	Fvar (try Hashtbl.find vars s
	      with Not_found -> incr nbvar; Hashtbl.add vars s !nbvar; !nbvar)
    | Pnot f -> Fnot (trans f)
    | Pand (f1, f2) -> Fand (trans f1, trans f2)
    | Por (f1, f2) -> For (trans f1, trans f2)
    | Pimp (f1, f2) -> Fimp (trans f1, trans f2)
    | Piff (f1, f2) -> let f1 = trans f1 and f2 = trans f2 in
                       Fand (Fimp (f1, f2), Fimp (f2, f1))
    | Ptrue -> Ftrue
    | Pfalse -> Ffalse
  in
  let f = trans f in
  set_max_var !nbvar;
  Printf.printf "nb var = %d\n%!" !nbvar;
  build f

end

(* bench *)

let domains = ref 1
type bench = De_bruijn | Pigeon
let bench = ref De_bruijn
let n = ref 10
let verbose = ref false

let () =
  Arg.parse
      ["-de-bruijn", Arg.Unit (fun () -> bench := De_bruijn), "";
       "-pigeon", Arg.Unit (fun () -> bench := Pigeon), "";
       "-v", Arg.Set verbose, "";
       "-domains", Arg.Set_int domains, "";
      ]
      (fun x -> n := int_of_string x)
      "";
  let f = match !bench with
    | De_bruijn -> de_bruijn_p !n
    | Pigeon    -> pigeon_p !n in
  let work () =
    let module W = Workload () in
    let b = W.bdd_of_formula f in
    assert (W.tautology b);
    if !verbose then begin
      let dom_id = (Domain.self () :> int) in
      let l,n,s,b1,b2,b3 = W.(HC.stats htable) in
      Printf.printf "[%d] table length: %d / nb. entries: %d / sum of bucket length: %d@."
        dom_id l n s;
      Printf.printf "[%d] smallest bucket: %d / median bucket: %d / biggest bucket: %d@."
        dom_id b1 b2 b3
    end
  in
  let workers = List.init (!domains - 1) (fun _ -> Domain.spawn work) in
  work ();
  List.iter Domain.join workers

