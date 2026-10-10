

open Ctypes_static

exception $Unsupported of string

$let rec liftable : 'a. 'a typ -> bool =
  fun (type a) (t : a typ) ->
  match t with
  | Void | Primitive _ | Abstract _ | OCaml _ -> true
  | Pointer ty -> liftable ty
  | Qualified (_, ty) -> liftable ty
  | Array (ty, _) -> liftable ty
  | Funptr fn -> fn_liftable fn
  | Struct _ | Union _ | View _ | Bigarray _ -> false
and fn_liftable : 'a. 'a fn -> bool =
  fun (type a) (fn : a fn) ->
  match fn with
  | Returns t -> liftable t
  | Function (t, rest) -> liftable t && fn_liftable rest

$let typ_expr : 'a. 'a typ -> 'a Ctypes.typ expr = fun t ->
  if not (liftable t) then
    raise (Unsupported
             "typ_expr: views, structs, unions and bigarrays (or types \
              containing them) cannot be lifted into generated code");
  match Expr.unsafe_lift_constant t with
  | e -> e
  | exception Invalid_argument m -> raise (Unsupported ("typ_expr: " ^ m))

$let prim_typ_expr : 'a. 'a Ctypes_primitive_types.prim -> 'a Ctypes.typ expr =
  fun p -> typ_expr (Primitive p)

$let addr_at : 'a. int -> ('a Ctypes.ptr -> char Ctypes.ptr) expr = fun off ->
  << fun p ->
     Ctypes.(+@) (Ctypes.from_voidp Ctypes.char (Ctypes.to_voidp p)) $(Expr.int off) >>

$let read_at : 'a 'b. 'a typ -> int -> ('b Ctypes.ptr -> 'a) expr =
  fun t off ->
  match t with
  | Primitive _ | Qualified (_, Primitive _) ->
    << fun sp ->
       Ctypes.(!@) (Ctypes.from_voidp $(typ_expr t)
                      (Ctypes.to_voidp ($(addr_at off) sp))) >>
  | _ -> raise (Unsupported "read_at: only primitive types are covered so far")

$let write_at : 'a 'b. 'a typ -> int -> ('b Ctypes.ptr -> 'a -> unit) expr =
  fun t off ->
  match t with
  | Primitive _ | Qualified (_, Primitive _) ->
    << fun sp v ->
       Ctypes.(<-@) (Ctypes.from_voidp $(typ_expr t)
                       (Ctypes.to_voidp ($(addr_at off) sp))) v >>
  | _ -> raise (Unsupported "write_at: only primitive types are covered so far")

$let getf : 'a 's 'k. ('a, ('s, 'k) structured) field ->
             ((('s, 'k) structured) Ctypes.ptr -> 'a) expr =
  fun f -> read_at f.ftype f.foffset

$let setf : 'a 's 'k. ('a, ('s, 'k) structured) field ->
             ((('s, 'k) structured) Ctypes.ptr -> 'a -> unit) expr =
  fun f -> write_at f.ftype f.foffset

$let getf2 : 'a 'b 's 'k 'k2.
  (('b, 'k2) structured, ('s, 'k) structured) field ->
  ('a, ('b, 'k2) structured) field ->
  ((('s, 'k) structured) Ctypes.ptr -> 'a) expr =
  fun outer inner ->
  match inner.ftype with
  | Primitive _ | Qualified (_, Primitive _) ->
    << fun sp ->
       Ctypes.(!@) (Ctypes.from_voidp $(typ_expr inner.ftype)
                      (Ctypes.to_voidp
                         ($(addr_at (outer.foffset + inner.foffset)) sp))) >>
  | _ -> raise (Unsupported "getf2: only primitive-typed inner fields are covered so far")

type ('a, 'b) staged_view = {
  sread : 'b expr -> 'a expr;
  swrite : 'a expr -> 'b expr;
  sty : 'b typ;
}

$let view_getf : 'a 'b 's 'k. ('b, ('s, 'k) structured) field -> ('a, 'b) staged_view ->
  ((('s, 'k) structured) Ctypes.ptr -> 'a) expr =
  fun f v ->
  match v.sty with
  | Primitive _ | Qualified (_, Primitive _) ->
    << fun sp ->
       $(v.sread
           << Ctypes.(!@) (Ctypes.from_voidp $(typ_expr v.sty)
                             (Ctypes.to_voidp ($(addr_at f.foffset) sp))) >>) >>
  | _ -> raise (Unsupported "view_getf: only primitive-backed views are covered so far")

$let view_setf : 'a 'b 's 'k. ('b, ('s, 'k) structured) field -> ('a, 'b) staged_view ->
  ((('s, 'k) structured) Ctypes.ptr -> 'a -> unit) expr =
  fun f v ->
  match v.sty with
  | Primitive _ | Qualified (_, Primitive _) ->
    << fun sp x ->
       Ctypes.(<-@) (Ctypes.from_voidp $(typ_expr v.sty)
                       (Ctypes.to_voidp ($(addr_at f.foffset) sp)))
         $(v.swrite <<x>>) >>
  | _ -> raise (Unsupported "view_setf: only primitive-backed views are covered so far")

module Probe = Ctypes_staged_probe
