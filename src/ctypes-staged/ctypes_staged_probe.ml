

type field_layout = { foff : int; fsize : int }
type struct_layout = { ssize : int; salign : int;
                       sfields : (string * field_layout) list }

$let probe_struct :
  ?cc:string -> headers:string list -> string -> string list -> struct_layout =
  fun ?cc ~headers name fields ->
  let cc = match cc with Some cc -> cc | None -> "cc" in
  let src = Filename.temp_file "ctypes_probe" ".c" in
  let exe = Filename.temp_file "ctypes_probe" ".exe" in
  let out = Filename.temp_file "ctypes_probe" ".out" in
  let oc = open_out src in
  output_string oc "#include <stdio.h>\n#include <stddef.h>\n";
  List.iter (fun h -> Printf.fprintf oc "#include %s\n" h) headers;
  Printf.fprintf oc "int main(void) {\n";
  Printf.fprintf oc "  printf(\"%%zu %%zu\\n\", sizeof(%s), _Alignof(%s));\n" name name;
  List.iter
    (fun f ->
      Printf.fprintf oc
        "  printf(\"%%zu %%zu\\n\", offsetof(%s, %s), sizeof(((%s *)0)->%s));\n"
        name f name f)
    fields;
  Printf.fprintf oc "  return 0;\n}\n";
  close_out oc;
  let run fmt = Printf.ksprintf (fun cmd ->
    if Sys.command cmd <> 0 then failwith ("ctypes_staged_probe: command failed: " ^ cmd)) fmt in
  run "%s %s -o %s" (Filename.quote cc) (Filename.quote src) (Filename.quote exe);
  run "%s > %s" (Filename.quote exe) (Filename.quote out);
  let ic = open_in out in
  let line () = Scanf.sscanf (input_line ic) "%d %d" (fun a b -> (a, b)) in
  let (ssize, salign) = line () in
  let sfields = List.map (fun f -> let (o, s) = line () in (f, { foff = o; fsize = s })) fields in
  close_in ic;
  List.iter (fun f -> try Sys.remove f with Sys_error _ -> ()) [src; exe; out];
  { ssize; salign; sfields }

$let field_offset : struct_layout -> string -> int = fun l f ->
  (List.assoc f l.sfields).foff
