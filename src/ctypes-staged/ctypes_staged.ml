

open Ctypes_static

exception Unsupported of string

macro prim_typ_expr : 'a. 'a Ctypes_primitive_types.prim -> 'a Ctypes.typ expr =
  fun (type a) (p : a Ctypes_primitive_types.prim) : a Ctypes.typ expr ->
  match p with
  | Ctypes_primitive_types.Char -> << Ctypes.char >>
  | Ctypes_primitive_types.Bool -> << Ctypes.bool >>
  | Ctypes_primitive_types.Int -> << Ctypes.int >>
  | Ctypes_primitive_types.Short -> << Ctypes.short >>
  | Ctypes_primitive_types.Int8_t -> << Ctypes.int8_t >>
  | Ctypes_primitive_types.Int16_t -> << Ctypes.int16_t >>
  | Ctypes_primitive_types.Float -> << Ctypes.float >>
  | Ctypes_primitive_types.Double -> << Ctypes.double >>
  | Ctypes_primitive_types.Schar -> << Ctypes.schar >>
  | Ctypes_primitive_types.Uchar -> << Ctypes.uchar >>
  | Ctypes_primitive_types.Long -> << Ctypes.long >>
  | Ctypes_primitive_types.Llong -> << Ctypes.llong >>
  | Ctypes_primitive_types.Ushort -> << Ctypes.ushort >>
  | Ctypes_primitive_types.Uint -> << Ctypes.uint >>
  | Ctypes_primitive_types.Ulong -> << Ctypes.ulong >>
  | Ctypes_primitive_types.Ullong -> << Ctypes.ullong >>
  | Ctypes_primitive_types.Size_t -> << Ctypes.size_t >>
  | Ctypes_primitive_types.Int32_t -> << Ctypes.int32_t >>
  | Ctypes_primitive_types.Int64_t -> << Ctypes.int64_t >>
  | Ctypes_primitive_types.Uint8_t -> << Ctypes.uint8_t >>
  | Ctypes_primitive_types.Uint16_t -> << Ctypes.uint16_t >>
  | Ctypes_primitive_types.Uint32_t -> << Ctypes.uint32_t >>
  | Ctypes_primitive_types.Uint64_t -> << Ctypes.uint64_t >>
  | Ctypes_primitive_types.Nativeint -> << Ctypes.nativeint >>
  | Ctypes_primitive_types.Camlint -> << Ctypes.camlint >>
  | _ -> raise (Unsupported "prim_typ_expr: primitive not yet covered")

macro rec typ_expr : 'a. 'a typ -> 'a Ctypes.typ expr =
  fun (type a) (t : a typ) : a Ctypes.typ expr ->
  match t with
  | Primitive p -> prim_typ_expr p
  | Pointer ty -> << Ctypes.ptr $(typ_expr ty) >>
  | Void -> << Ctypes.void >>
  | Qualified (_, ty) -> typ_expr ty
  | _ -> raise (Unsupported "typ_expr: type not yet covered")

macro addr_at : 'a. int -> ('a Ctypes.ptr -> char Ctypes.ptr) expr = fun off ->
  << fun p ->
     Ctypes.(+@) (Ctypes.from_voidp Ctypes.char (Ctypes.to_voidp p)) $(Expr.int off) >>

macro read_at : 'a 'b. 'a typ -> int -> ('b Ctypes.ptr -> 'a) expr =
  fun t off ->
  match t with
  | Primitive _ | Qualified (_, Primitive _) ->
    << fun sp ->
       Ctypes.(!@) (Ctypes.from_voidp $(typ_expr t)
                      (Ctypes.to_voidp ($(addr_at off) sp))) >>
  | _ -> raise (Unsupported "read_at: only primitive types are covered so far")

macro write_at : 'a 'b. 'a typ -> int -> ('b Ctypes.ptr -> 'a -> unit) expr =
  fun t off ->
  match t with
  | Primitive _ | Qualified (_, Primitive _) ->
    << fun sp v ->
       Ctypes.(<-@) (Ctypes.from_voidp $(typ_expr t)
                       (Ctypes.to_voidp ($(addr_at off) sp))) v >>
  | _ -> raise (Unsupported "write_at: only primitive types are covered so far")

macro getf : 'a 's 'k. ('a, ('s, 'k) structured) field ->
             ((('s, 'k) structured) Ctypes.ptr -> 'a) expr =
  fun f -> read_at f.ftype f.foffset

macro setf : 'a 's 'k. ('a, ('s, 'k) structured) field ->
             ((('s, 'k) structured) Ctypes.ptr -> 'a -> unit) expr =
  fun f -> write_at f.ftype f.foffset

macro getf2 : 'a 'b 's 'k 'k2.
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

macro view_getf : 'a 'b 's 'k. ('b, ('s, 'k) structured) field -> ('a, 'b) staged_view ->
  ((('s, 'k) structured) Ctypes.ptr -> 'a) expr =
  fun f v ->
  match v.sty with
  | Primitive _ | Qualified (_, Primitive _) ->
    << fun sp ->
       $(v.sread
           << Ctypes.(!@) (Ctypes.from_voidp $(typ_expr v.sty)
                             (Ctypes.to_voidp ($(addr_at f.foffset) sp))) >>) >>
  | _ -> raise (Unsupported "view_getf: only primitive-backed views are covered so far")

macro view_setf : 'a 'b 's 'k. ('b, ('s, 'k) structured) field -> ('a, 'b) staged_view ->
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
