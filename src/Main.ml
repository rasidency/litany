open Core

let level index =
  let rec count acc = function O -> acc | S n -> count (acc + 1) n in
  count 0 index

let emit code =
  let out = Buffer.create 256 in
  let add = Buffer.add_string out in
  let line depth format =
    Printf.ksprintf (fun text -> add (String.make depth ' '); add text; add "\n") format
  in
  let ty = "!timbda.set" in
  let ref_name i = Printf.sprintf "%%v%d" (level i) in
  let rec block depth top = function
    | Return value ->
        let name = ref_name value in
        if top then line depth "return %s : %s" name ty
        else line depth "\"timbda.yield\"(%s) : (%s) -> ()" name ty
    | Operation (opcode, result, operands, literal, body, rest) ->
        let name = match opcode with
          | Const_op -> "constant" | Int_op -> "int" | Fail_op -> "fail"
          | Range_op -> "range" | Apply_op -> "apply" | Choice_op -> "choice"
          | Lambda_op -> "lambda"
        in
        let refs = String.concat ", " (List.map ref_name operands) in
        let types = String.concat ", " (List.map (fun _ -> ty) operands) in
        let attrs = match literal with
          | None -> ""
          | Some z ->
              let width = level (integer_width z) in
              if width > 0xffffff then failwith "integer exceeds MLIR's maximum bit width";
              let spelling = String.of_seq (List.to_seq (print_integer z)) in
              Printf.sprintf " <{value = %s : si%d}>" spelling width
        in
        let result = ref_name result in
        (match body with
         | None ->
             line depth "%s = \"timbda.%s\"(%s)%s : (%s) -> %s"
               result name refs attrs types ty
         | Some (arg, nested) ->
             line depth "%s = \"timbda.%s\"(%s) ({" result name refs;
             line (depth + 2) "^bb0(%s: %s):" (ref_name arg) ty;
             block (depth + 4) false nested;
             line depth "})%s : (%s) -> %s" attrs types ty);
        block depth top rest
  in
  add "module {\n  func.func @main() -> !timbda.set {\n";
  block 4 true code;
  add "  }\n}\n";
  Buffer.contents out

let location source offset =
  let line = ref 1 and column = ref 1 in
  for i = 0 to offset - 1 do
    if source.[i] = '\n' then (incr line; column := 1)
    else if Char.code source.[i] land 0xc0 <> 0x80 then incr column
  done;
  !line, !column

let () =
  let file = match Array.to_list Sys.argv with
    | [_] | [_; "-"] -> "-"
    | [_; ("-h" | "--help")] -> print_endline "usage: litany [FILE|-]"; exit 0
    | [_; file] -> file
    | _ -> prerr_endline "usage: litany [FILE|-]"; exit 2
  in
  try
    let source =
      if file = "-" then In_channel.input_all stdin
      else In_channel.with_open_bin file In_channel.input_all
    in
    try
      match translate (Syntax.parse source) with
      | Compiled code -> print_string (emit code)
      | Rejected (offset, name) ->
          let name = String.of_seq (List.to_seq name) in
          raise (Syntax.Error (offset, "unbound variable " ^ name))
    with
    | Syntax.Error (offset, message) ->
        let line, column = location source offset in
        Printf.eprintf "%s:%d:%d: %s\n" file line column message;
        exit 1
  with
  | Sys_error message | Failure message ->
      Printf.eprintf "litany: %s\n" message;
      exit 1
