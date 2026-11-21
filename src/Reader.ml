open Core

module Names = Map.Make (String)

type token = Word of string | Quoted of string | Mark of char | End

let lexer source =
  let limit = String.length source in
  let rec scan test i = if i < limit && test source.[i] then scan test (i + 1) else i in
  let word c =
    match c with
    | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' | '.' | '%' | '^' | '!' | '@' | '$' -> true
    | _ -> false
  in
  let rec next i =
    if i = limit then End, i, i
    else
      match source.[i] with
      | ' ' | '\t' | '\r' | '\n' -> next (i + 1)
      | '-' when i + 1 < limit && source.[i + 1] = '>' -> Word "->", i, i + 2
      | '-' when i + 1 < limit && Syntax.digit source.[i + 1] ->
          let stop = scan Syntax.digit (i + 1) in
          Word (String.sub source i (stop - i)), i, stop
      | '"' ->
          let stop = scan (fun c -> c <> '"' && c <> '\n') (i + 1) in
          if stop = limit || source.[stop] <> '"' then raise (Syntax.Error (i, "unterminated string"));
          Quoted (String.sub source (i + 1) (stop - i - 1)), i, stop + 1
      | ('(' | ')' | '{' | '}' | '<' | '>' | ',' | ':' | '=') as c -> Mark c, i, i + 1
      | c when word c ->
          let stop = scan word (i + 1) in
          Word (String.sub source i (stop - i)), i, stop
      | _ -> raise (Syntax.Error (i, "unexpected character"))
  in
  next

let read source =
  let next = lexer source in
  let current = ref (next 0) in
  let peek () = let token, _, _ = !current in token in
  let error message = let _, at, _ = !current in raise (Syntax.Error (at, message)) in
  let take () = let token, _, stop = !current in current := next stop; token in
  let expect token = if peek () <> token then error "unexpected token in a Timbda-0 program"; ignore (take ()) in
  let marks = String.iter (fun c -> expect (Mark c)) in
  let words = List.iter (fun w -> expect (Word w)) in
  let set = "!timbda.set" in
  let value () =
    match take () with
    | Word name when String.length name > 1 && name.[0] = '%' -> name
    | _ -> error "expected an SSA value"
  in
  let lookup scope name =
    match Names.find_opt name scope with Some index -> index | None -> error ("undefined value " ^ name)
  in
  let rec sequence item close =
    if peek () = Mark close then (ignore (take ()); [])
    else
      let first = item () in
      let rec more () =
        match take () with
        | Mark c when c = close -> []
        | Mark ',' -> let x = item () in x :: more ()
        | _ -> error "expected a separator"
      in
      first :: more ()
  in
  let signature arity =
    marks ":(";
    let types = sequence (fun () -> words [ set ]) ')' in
    if List.length types <> arity then error "operand types do not match the operands";
    expect (Word "->")
  in
  let literal () =
    marks "<{";
    words [ "value" ];
    marks "=";
    let spelling = match take () with Word w -> w | _ -> error "expected an integer literal" in
    marks ":";
    (match take () with
     | Word w when String.length w > 2 && String.sub w 0 2 = "si" -> ()
     | _ -> error "expected a signed integer type");
    marks "}>";
    match parse_integer (Syntax.chars spelling) with
    | Some z -> z
    | None -> error "invalid integer literal"
  in
  let rec block top index scope =
    match peek () with
    | Word "return" when top ->
        ignore (take ());
        let result = lookup scope (value ()) in
        marks ":";
        words [ set ];
        Return result
    | Quoted "timbda.yield" when not top ->
        ignore (take ());
        marks "(";
        let result = lookup scope (value ()) in
        marks ")";
        signature 1;
        marks "()";
        Return result
    | Word _ ->
        let name = value () in
        marks "=";
        let opcode = match take () with
          | Quoted "timbda.constant" -> Const_op | Quoted "timbda.int" -> Int_op
          | Quoted "timbda.fail" -> Fail_op | Quoted "timbda.range" -> Range_op
          | Quoted "timbda.apply" -> Apply_op | Quoted "timbda.choice" -> Choice_op
          | Quoted "timbda.lambda" -> Lambda_op
          | _ -> error "expected a Timbda-0 operation"
        in
        marks "(";
        let operands = sequence (fun () -> lookup scope (value ())) ')' in
        let attribute = if peek () = Mark '<' then Some (literal ()) else None in
        let body =
          if opcode <> Lambda_op then None
          else begin
            marks "({";
            expect (Word "^bb0");
            marks "(";
            let argument = value () in
            marks ":";
            words [ set ];
            marks "):";
            let nested = block false (index + 1) (Names.add argument index scope) in
            marks "})";
            Some (index, nested)
          end
        in
        signature (List.length operands);
        words [ set ];
        Operation (opcode, index, operands, attribute, body, block top (index + 1) (Names.add name index scope))
    | _ -> error "expected a Timbda-0 operation or terminator"
  in
  words [ "module" ];
  marks "{";
  words [ "func.func"; "@main" ];
  marks "()";
  words [ "->"; set ];
  marks "{";
  let region = block true 0 Names.empty in
  marks "}}";
  expect End;
  region

let rec size = function
  | Return _ -> 0
  | Operation (_, _, _, _, body, rest) ->
      1 + (match body with Some (_, nested) -> size nested | None -> 0) + size rest
