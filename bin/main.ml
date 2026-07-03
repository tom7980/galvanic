type 'token input = 'token Seq.t
type ('token, 'result) monad = ('result * 'token input) option
type ('token, 'result) parser = 'token input -> ('result * 'token input) option


let parse parser input =
  match parser input with
  | Some(tok, _) -> Some tok
  | None -> None

let return token input = Some(token, input)

let (>>=) x f =
  function input ->
  match x input with
  | Some(result', input') -> f result' input'
  | None -> None

let (let*) = (>>=)

let rec prod a b =
  let* r = a in
  let* rs = b in
  return (r, rs)
                            
let (and*) = prod

let (=>) x f = x >>= fun r -> return (f r)
let (>>) a b = a >>= fun _ -> b
let (<<) a b = a >>= fun r -> b >>= fun _ -> return r
let (<~>) a b =
  a >>= fun r -> b >>= fun rs -> return (r :: rs)

let (<|>) a b =
  function input ->
  match a input with
  | Some _ as res -> res
  | None -> b input

let mzero _ = None

let eof x = function y ->
  match y () with
  | Seq.Nil -> Some(x, Seq.Nil)
  | _ -> None

let any = function x ->
  match x () with
  | Seq.Cons(token, input') -> Some(token, input')
  | Seq.Nil -> None

let rec choice = function
  | [] -> mzero
  | h :: t -> h <|> choice t

let (>=>) f g x =
  let* y = f x in
  g y

let (%) f g = fun x -> g (f x)

let collect l = String.concat "" (List.map (String.make 1) l)

let between pre post x = pre >> x << post

let option default x = x <|> return default
let optional x = option () (x >> return ())

let rec skip x = option () (x >>= fun _ -> skip x)
let skip_at_least_1 x = x >> skip x

let rec many x = option [] (x >>= fun r -> many x >>= fun rs -> return (r :: rs))
let many1 x = x <~> many x

let sep_by1 x sep = x <~> many (sep >> x)
let sep_by x sep = sep_by1 x sep <|> return []
                     
let end_by1 x sep = sep_by1 x sep << sep
let end_by x sep = end_by1 x sep <|> return []
                     
let chainl1 x op =
  let rec loop a = (op >>= fun f -> x >>= fun b -> loop (f a b)) <|> return a in
  x >>= loop
let chainl x op default = chainl1 x op <|> return default
                            
let rec chainr1 x op =
  x >>= fun a -> (op >>= fun f -> chainr1 x op >>= f a) <|> return a
let chainr x op default = chainr1 x op <|> return default

let satisfy test =
  any >>= (fun res -> Printf.printf "Test: %c \n" res; if test res then begin Printf.printf "Matches: %c \n" res; return res end else mzero)

let range low high = satisfy (fun x -> low <= x && x <= high)

let one_of l = satisfy (fun x -> List.mem x l)
let not_in l = satisfy (fun x -> not (List.mem x l))
let exactly x = satisfy ((=) x)
    
let digit = range '0' '9'
let lower = range 'a' 'z'
let upper = range 'A' 'Z'
let alpha = lower <|> upper
let alphanumeric = alpha <|> digit
let space = one_of [' '; '\t'; '\r'; '\n']
let spaces = many space

let lexeme x = spaces >> x

let token s =
  let rec loop s i =
    if i >= String.length s
    then return s
    else exactly s.[i] >> loop s (i + 1)
  in
  lexeme (loop s 0)

let reserved = [
  "true";
  "false";
  "if";
  "then";
  "else";
  "while";
  "do";
  "and";
  "or";
  "fn";
  "let";
  "ret";
]

exception Syntax_error
exception Runtime_error

let ident =
  let* s = (spaces >> alpha <~> many alphanumeric) => collect % String.lowercase_ascii in
  match s with
  | s when List.mem s reserved -> mzero
  | s -> return s

type op = Add
        | Minus
        | Mul
        | Div
        | And
        | Or
        | GT
        | LT

type expr = Var of string
          | Num of int
          | Arith of op * expr * expr
          | Bool of bool
          | BoolOp of op * expr * expr
          | Args of expr list
          | Call of string * expr
          | Unit

type stmt = Assign of string * expr 
          | Stmts of stmt list
          | If of expr * stmt * stmt
          | While of expr * stmt
          | FnDef of string * string list * stmt * expr

let parens = between (token "(") (token ")")

let number =
  let* num = spaces >> many1 digit => collect % int_of_string in
  return (Num num)

let var =
  let* s = ident in
  return (Var s)



let true_p = token "true" >> return (Bool true)
let false_p = token "false" >> return (Bool false)

let atom = var <|> number <|> true_p <|> false_p

let addop = token "+" >> return (fun x y -> Arith(Add, x, y))
let minusop = token "-" >> return (fun x y -> Arith(Minus, x, y))
let mulop = token "*" >> return (fun x y -> Arith(Mul, x, y))
let divop = token "/" >> return (fun x y -> Arith(Div, x, y))
let andop = token "and" >> return (fun x y -> BoolOp(And, x, y))
let orop = token "or" >> return (fun x y -> BoolOp(Or, x, y))
let gtop = token ">" >> return (fun x y -> BoolOp(GT, x, y))
let ltop = token "<" >> return (fun x y -> BoolOp(LT, x, y))
    

let rec expr input = (chainl1 and_expr orop) input
and and_expr input = (chainl1 rop_expr andop) input
and rop_expr input = (chainl1 add_expr (ltop <|> gtop)) input
and add_expr input = (chainl1 mul_expr (addop <|> minusop)) input
and mul_expr input = (chainl1 call_expr (mulop <|> divop)) input
and call_expr input = (call <|> prim_expr) input
and prim_expr input = (parens expr <|> atom) input
and args input =
  (let* l = sep_by1 expr (token ",") in
  return (Args l)) input
and call input =
  (let* name = ident
   and* args = token "(" >> args in
   token ")" >> return (Call(name, args))) input

let argnames =
  let* l = sep_by1 ident (token ",") in
  return l

let rec stmts input =
  (let* l = sep_by1 stmt (token ";") in
  return (Stmts l)) input
and stmt input =
  (if_stmt <|> while_stmt <|> assign_stmt <|> fn_stmt) input
and if_stmt input =
  (let* pred = token "if" >> expr
  and* thn = token "then" >> token "{" >> stmts
  and* els = token "}" >> token "else" >> token "{" >> stmts in
  token "}" >> return (If(pred, thn, els))) input
and while_stmt input =
  (let* guard = token "while" >> expr
  and* body = token "do" >> token "{" >> stmts in
  token "}" >> return (While(guard, body))) input
and assign_stmt input =
  (let* var = ident
  and* value = token "=" >> expr in
  return (Assign(var, value))) input
and fn_stmt input =
  (let* name = token "fn" >> ident
   and* args = token "(" >> argnames
   and* body = token ")" >> token "{" >> end_by1 stmt (token ";") >>= fun l -> return (Stmts l)
   and* rtrn = option Unit expr in
   token "}" >> return (FnDef(name, args, body, rtrn))) input

let program = stmts << (spaces << eof ())

let parse_prog input = parse program input

module Envir = struct

  type ('a, 'b, 'c) t = {
    vars: ('a, 'b) Hashtbl.t;
    funcs: ('a, 'c) Hashtbl.t;
  }

  let make_env = {
    vars = Hashtbl.create 10;
    funcs = Hashtbl.create 10;
  }

  let get_var env x =
    Hashtbl.find env.vars x

  let set_var env x value =
    Hashtbl.replace env.vars x value

  let push_func env x args body return =
    Hashtbl.replace env.funcs x (body, args, return)

  let get_func env x =
    Hashtbl.find env.funcs x

  let make_scoped_env env = {
      vars = Hashtbl.copy env.vars;
      funcs = Hashtbl.copy env.funcs;
    }
end

let pp_expr expr =
  match expr with
  | Args _ -> "Args"
  | Var _ -> "Var"
  | Num _ -> "Num"
  | Arith _ -> "Arith"
  | Bool _ -> "Bool"
  | BoolOp _ -> "BoolOp"
  | Call _ -> "Call"
  | Unit -> "Unit"

let rec eval env prog =
  match prog with
  | Stmts [] -> ()
  | Stmts (x :: xs) ->
    eval env x;
    eval env (Stmts xs)
  | Assign (var, value) ->
    let value = eval_arith env value in
    Envir.set_var env var value
  | If (pred, thn, els) ->
    if (eval_bool env pred) then
      eval env thn
    else
      eval env els
  | While (guard, body) ->
    let rec loop () =
      if (eval_bool env guard) then
        begin
          eval env body;
          loop ()
        end
      else ()
    in
    loop ()
  | FnDef (name, args, body, return) ->
    Envir.push_func env name args body return
    
and eval_func env args def_args body return =
  let scoped_env = Envir.make_scoped_env env in
  let vals = eval_args scoped_env args in
  List.iter2 (fun name value -> Envir.set_var scoped_env name value) def_args vals;
  eval scoped_env body;
  eval_arith scoped_env return

and eval_args env expr =
  match expr with
  | Args (x :: xs) ->
    let r = eval_arith env x in
    r :: eval_args env (Args xs)
  | Args [] ->
    []
  | _ ->
    Printf.printf "Args eval: %s" (pp_expr expr);
    raise Runtime_error


and eval_arith env expr =
  match expr with
  | Arith (Add, lhs, rhs) ->
    let lhs' = eval_arith env lhs
    and rhs' = eval_arith env rhs in
    lhs' + rhs'
  | Arith (Minus, lhs, rhs) ->
    let lhs' = eval_arith env lhs
    and rhs' = eval_arith env rhs in
    lhs' - rhs'
  | Arith (Mul, lhs, rhs) ->
    let lhs' = eval_arith env lhs
    and rhs' = eval_arith env rhs in
    lhs' * rhs'
  | Arith (Div, lhs, rhs) ->
    let lhs' = eval_arith env lhs
    and rhs' = eval_arith env rhs in
    lhs' / rhs'
  | Var x -> Envir.get_var env x
  | Num n -> n
  | Unit -> 0
  | Call (name, args) -> begin
    match Envir.get_func env name with 
    | (body, def_args, return) -> eval_func env args def_args body return
  end 
  | _ -> begin
      Printf.printf "Runtime error in eval arith\n";
      Printf.printf "Eval expr: %s\n" (pp_expr expr);
      raise Runtime_error
    end

and eval_bool env expr =
  match expr with
  | BoolOp (And, x, y) ->
    let x' = eval_bool env x
    and y' = eval_bool env y in
    x' && y'
  | BoolOp (Or, x, y) ->
    let x' = eval_bool env x
    and y' = eval_bool env y in
    x' || y'
  | BoolOp (GT, x, y) ->
    let x' = eval_arith env x
    and y' = eval_arith env y in
    x' > y'
  | BoolOp (LT, x, y) ->
    let x' = eval_arith env x
    and y' = eval_arith env y in
    x' < y'
  | Bool x -> x
  | _ -> begin
      Printf.printf "Runtime error in eval bool\n";
      raise Runtime_error
    end

let in_str = "fact = 1 ;
val = 10000 ;
cur = val ;
mod = 1000000007 ;

count = 0 ;

fn add(x) { x = x + 1 ; x } ;

while ( cur > 0 )
  do
   {
      fact = fact * cur ;
      fact = fact - fact / mod * mod ;
      cur = cur - 1 ;
      count = add(count)
   } ;

cur = 0"

let () =
  let input = String.to_seq in_str in
  match parse_prog input with
  | None -> raise Syntax_error
  | Some program ->
    Printf.printf "successful parse\n";
    let env = Envir.make_env in
    eval env program;
    let pairs = Hashtbl.fold (fun k v acc -> (k, v) :: acc) env.vars [] in
    let pairs' = List.sort (fun (k1, _) (k2, _) -> compare k1 k2) pairs in
    List.iter (fun (k, v) -> Printf.printf "%s %d\n" k v) pairs'
