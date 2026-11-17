open Core

type token =
  | Integer of string | Name of string | Int_token | Fail_token
  | Lambda_token | Bind | Dot | Colon | Bar | Left | Right | End

exception Error of int * string

let digit = function '0' .. '9' -> true | _ -> false
let letter = function 'a' .. 'z' | 'A' .. 'Z' | '_' -> true | _ -> false

let lexer source =
  let limit = String.length source in
  let rec scan test i =
    if i < limit && test source.[i] then scan test (i + 1) else i
  in
  let rec next i =
    if i = limit then End, i, i
    else
      let span token stop = token, i, stop in
      let at n c = n < limit && source.[n] = c in
      let word first test classify =
        let stop = scan test first in
        span (classify (String.sub source i (stop - i))) stop
      in
      match source.[i] with
      | ' ' | '\t' | '\r' | '\n' -> next (i + 1)
      | '(' -> span Left (i + 1)
      | ')' -> span Right (i + 1)
      | '.' -> span Dot (i + 1)
      | '|' -> span Bar (i + 1)
      | '\\' -> span Lambda_token (i + 1)
      | '\206' when at (i + 1) '\187' -> span Lambda_token (i + 2)
      | ':' when at (i + 1) '=' -> span Bind (i + 2)
      | ':' -> span Colon (i + 1)
      | '-' when i + 1 < limit && digit source.[i + 1] ->
          word (i + 2) digit (fun n -> Integer n)
      | c when digit c -> word (i + 1) digit (fun n -> Integer n)
      | c when letter c ->
          word (i + 1) (fun c -> letter c || digit c)
            (function "int" -> Int_token | "fail" -> Fail_token
              | "lambda" -> Lambda_token | s -> Name s)
      | _ -> raise (Error (i, "unexpected character"))
  in
  next

let chars s = List.of_seq (String.to_seq s)

let parse source =
  let next = lexer source in
  let current = ref (next 0) in
  let peek () = let token, _, _ = !current in token in
  let error message = let _, at, _ = !current in raise (Error (at, message)) in
  let take () =
    let token, _, stop = !current in
    current := next stop;
    token
  in
  let expect token message =
    if peek () <> token then error message;
    ignore (take ())
  in
  let rec expression () =
    let rec choices lhs =
      match peek () with
      | Bar -> ignore (take ()); choices (NamedChoice (lhs, application ()))
      | _ -> lhs
    in
    choices (application ())
  and application () =
    let rec arguments lhs =
      match peek () with
      | Integer _ | Name _ | Int_token | Fail_token | Left | Colon ->
          arguments (NamedApply (lhs, prefix ()))
      | _ -> lhs
    in
    arguments (prefix ())
  and prefix () =
    let token, at, _ = !current in
    match token with
    | Colon -> ignore (take ()); NamedRange (prefix ())
    | Integer spelling ->
        ignore (take ());
        (match parse_integer (chars spelling) with
         | Some z -> NamedLit z
         | None -> raise (Error (at, "invalid integer literal")))
    | Name name -> ignore (take ()); NamedVar (at, chars name)
    | Int_token -> ignore (take ()); NamedInt
    | Fail_token -> ignore (take ()); NamedFail
    | Left ->
        ignore (take ());
        let term = expression () in
        expect Right "expected ')'";
        term
    | Lambda_token ->
        ignore (take ());
        expect Left "expected '(' after lambda";
        let name = match peek () with
          | Name name -> ignore (take ()); name
          | _ -> error "expected a binder name"
        in
        expect Bind "expected ':=' after binder";
        let domain = expression () in
        expect Right "expected ')' after domain";
        expect Dot "expected '.' before the lambda body";
        NamedLambda (chars name, domain, expression ())
    | _ -> error "expected a Timbda-0 expression"
  in
  let term = expression () in
  expect End "unexpected trailing token";
  term
