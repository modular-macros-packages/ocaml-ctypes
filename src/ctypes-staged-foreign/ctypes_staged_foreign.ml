

open Ctypes_static

exception Unsupported of string

macro rec ffitype_expr : 'a. 'a typ -> 'a Ctypes_ffi_stubs.ffitype expr =
  fun (type a) (t : a typ) : a Ctypes_ffi_stubs.ffitype expr ->
  match t with
  | Primitive _ ->
        << match $(Ctypes_staged.typ_expr t) with
       | Ctypes_static.Primitive p -> Ctypes_ffi_stubs.primitive_ffitype p
       | _ -> assert false >>
  | Pointer _ -> << Ctypes_ffi_stubs.pointer_ffitype () >>
  | Funptr _ -> << Ctypes_ffi_stubs.pointer_ffitype () >>
  | Qualified (_, ty) -> ffitype_expr ty
  | _ -> raise (Unsupported "ffitype_expr: only primitive and pointer types are covered")

macro arg_setup : 'a. 'a typ ->
  (Ctypes_ffi_stubs.callspec -> ('a -> Ctypes_ptr.voidp -> unit)) expr =
  fun t ->
  << fun callspec ->
     let off = Ctypes_ffi_stubs.add_argument callspec $(ffitype_expr t) in
     let w = Ctypes_memory.write $(Ctypes_staged.typ_expr t) in
     fun v buf ->
       w v Ctypes_ptr.Fat.(add_bytes (make ~managed:None ~reftyp:Ctypes_static.Void buf) off) >>


macro rec gen : 'f 'r. 'r fn ->
  Ctypes_ffi_stubs.callspec expr ->
  (Obj.t option, unit fn) Ctypes_ptr.Fat.t expr ->
  string ->
  ((((Ctypes_ptr.voidp expr -> unit expr) list -> 'r expr) -> 'f expr)) ->
  'f expr =
  fun (type f r) (fn : r fn) csp addr name
      (wrap : ((Ctypes_ptr.voidp expr -> unit expr) list -> r expr) -> f expr) : f expr ->
  match fn with
  | Returns ret ->
    << let rd = Ctypes_memory.build $(Ctypes_staged.typ_expr ret) in
       let () = Ctypes_ffi_stubs.prep_callspec $csp
                  (Libffi_abi.abi_code Libffi_abi.default_abi)
                  $(ffitype_expr ret) in
       $( wrap (fun ws ->
            << Ctypes_ffi_stubs.call $(Expr.string name) $addr $csp
                 (fun buf _mov -> $(match ws with
                                    | [] -> << () >>
                                    | w0 :: rest ->
                                      List.fold_left (fun acc w -> << $acc; $(w <<buf>>) >>)
                                        (w0 <<buf>>) rest))
                 (fun p -> rd (Ctypes_ptr.Fat.make ~managed:None
                                 ~reftyp:Ctypes_static.Void p)) >>) ) >>
  | Function (Void, rest) ->
        gen rest csp addr name
      (fun leaf -> wrap (fun ws -> << fun () -> $(leaf ws) >>))
  | Function (t, rest) ->
    << let w = $(arg_setup t) $csp in
       $( gen rest csp addr name
            (fun leaf ->
              wrap (fun ws ->
                << fun x -> $(leaf (ws @ [fun buf -> << w x $buf >>])) >>)) ) >>

macro foreign : 'a 'b. string -> ('a -> 'b) fn -> ('a -> 'b) expr =
  fun name fn ->
  << let callspec =
       Ctypes_ffi_stubs.allocate_callspec ~check_errno:false
         ~runtime_lock:false ~thread_registration:false in
     let addr = Ctypes_ptr.Fat.make ~managed:None
                  ~reftyp:(Ctypes_static.Returns Ctypes_static.Void)
                  (Ctypes_ptr.Raw.of_nativeint
                     (Dl.dlsym ?handle:None ~symbol:$(Expr.string name))) in
     $( gen fn <<callspec>> <<addr>> name (fun tower -> tower []) ) >>
