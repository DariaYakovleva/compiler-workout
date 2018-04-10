(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators
                         
(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t = {g : string -> int; l : string -> int; scope : string list}

    (*Было
    (* Update: non-destructively "modifies" the state s by binding the variable x 
      to value v and returns the new state.
    *)
    let update x v s = fun y -> if x = y then v else s y
    *)

    (* Empty state *)
    let empty = let failF x = failwith (Printf.sprintf "Undefined variable %s" x) in {g = failF; l = failF; scope = []}

    let rec inScope x scope = match scope with
        | [] -> false
        | y::scope' -> if x == y then true else inScope x scope'

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s = let updateF x v s = fun y -> if x = y then v else s y in
        if inScope x s.scope 
        then {g = s.g; l = updateF x v s.l; scope = s.scope}
        else {g = updateF x v s.g; l = s.l; scope = s.scope}
        
                                
    (* Evals a variable in a state w.r.t. a scope *)
    let eval s x = if inScope x s.scope
                   then s.l x
                   else s.g x

    (* Creates a new scope, based on a given state *)
    let enter st xs = let emptyState = empty in {g = st.g; l = emptyState.l; scope = xs}

    (* Drops a scope *)
    let leave st st' = {g = st.g; l = st'.l; scope = st'.scope}

  end
    
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant *) | Const of int
    (* variable         *) | Var   of string
    (* binary operator  *) | Binop of string * t * t with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)
      
    (* Expression evaluator

          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
    *)                                                       
    let to_func op =
      let bti   = function true -> 1 | _ -> 0 in
      let itb b = b <> 0 in
      let (|>) f g   = fun x y -> f (g x y) in
      match op with
      | "+"  -> (+)
      | "-"  -> (-)
      | "*"  -> ( * )
      | "/"  -> (/)
      | "%"  -> (mod)
      | "<"  -> bti |> (< )
      | "<=" -> bti |> (<=)
      | ">"  -> bti |> (> )
      | ">=" -> bti |> (>=)
      | "==" -> bti |> (= )
      | "!=" -> bti |> (<>)
      | "&&" -> fun x y -> bti (itb x && itb y)
      | "!!" -> fun x y -> bti (itb x || itb y)
      | _    -> failwith (Printf.sprintf "Unknown binary operator %s" op)    
    
    let rec eval st expr =      
      match expr with
      | Const n -> n
      | Var   x -> State.eval st x
      | Binop (op, x, y) -> to_func op (eval st x) (eval st y)

    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string
                                                                                                                  
    *)
    ostap (                                      
      parse:
      !(Ostap.Util.expr 
             (fun x -> x)
         (Array.map (fun (a, s) -> a, 
                           List.map  (fun s -> ostap(- $(s)), (fun x y -> Binop (s, x, y))) s
                        ) 
              [|                
        `Lefta, ["!!"];
        `Lefta, ["&&"];
        `Nona , ["=="; "!="; "<="; "<"; ">="; ">"];
        `Lefta, ["+" ; "-"];
        `Lefta, ["*" ; "/"; "%"];
              |] 
         )
         primary);
      
      primary:
        n:DECIMAL {Const n}
      | x:IDENT   {Var x}
      | -"(" parse -")"
    )
    
  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Until of t * Expr.t    
    (* call a procedure                 *) | Call   of string * Expr.t list with show
                                                                    
    (* The type of configuration: a state, an input stream, an output stream *)
    type config = State.t * int list * int list 

    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment supplies the following method

           method definition : string -> (string list, string list, t)

       which returns a list of formal parameters, local variables, and a body for given definition
    *)
    let rec eval env ((st, i, o) as conf) stmt =
      match stmt with
      | Read    x       -> (match i with z::i' -> (State.update x z st, i', o) | _ -> failwith "Unexpected end of input")
      | Write   e       -> (st, i, o @ [Expr.eval st e])
      | Assign (x, e)   -> (State.update x (Expr.eval st e) st, i, o)
      | Skip            -> conf
      | Seq    (s1, s2) -> eval env (eval env conf s1) s2
      | If     (cond, condt, condf) -> eval env conf (if (Expr.eval st cond) <> 0 then condt else condf)
      | While  (cond, condt) -> if (Expr.eval st cond) = 0 then conf else eval env (eval env conf condt) stmt
      | Until (condt, cond) -> let (new_st, new_i, new_o) = eval env conf condt in
            if (Expr.eval st cond) = 0 then eval env (new_st, new_i, new_o) stmt else (new_st, new_i, new_o)
      | Call (fname, params) -> 
            let (args, locals, body) = env#definition fname in
            let args' = List.combine args (List.map (Expr.eval st) params) in
            let st' = State.enter st (args@locals) in
            let st' = List.fold_left (fun s (p, v) -> State.update p v s) st' args' in
            let (st'', i', o') = eval env (st', i, o) body in
                (State.leave st'' st, i', o')

    let rec parseElif elfs condf = match elfs with
        | [] -> condf
        | (cond, condt)::elfs' -> If (cond, condt, parseElif elfs' condf)
                    
    (* Statement parser *)
    ostap (
      parse:
        s:stmt ";" ss:parse {Seq (s, ss)}
      | stmt;
      stmt:
        "read" "(" x:IDENT ")"          {Read x}
      | "write" "(" e:!(Expr.parse) ")" {Write e}
      | x:IDENT ":=" e:!(Expr.parse)    {Assign (x, e)}            
      | %"skip" {Skip}
      | %"if" cond:!(Expr.parse) 
        %"then" condt:parse 
            cond2:(%"elif" !(Expr.parse) %"then" parse)*
            condf:(%"else" parse)?
        %"fi" {If (cond, condt, 
            match condf with 
              | None -> parseElif cond2 Skip
              | Some cond -> parseElif cond2 cond 
            )}
      | %"while" cond:!(Expr.parse) %"do" condt:parse %"od" {While (cond, condt)}
      | %"repeat" condt:parse %"until" cond:!(Expr.parse) {Until (condt, cond)}
      | %"for" init:parse "," cond:!(Expr.parse) "," step:parse %"do" condt:parse %"od" {Seq (init, While (cond, Seq (condt, step)))}
    )
      
  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (
      arg: IDENT;
      parse: %"fun" name:IDENT "(" args:!(Util.list0 arg) ")"
      locals: (%"local" !(Util.list arg))? "{" body:!(Stmt.parse)"}" {name, (args, (match locals with 
                                                                                    | None -> []
                                                                                    | Some vars -> vars), body) }
    )

  end
    
(* The top-level definitions *)

(* The top-level syntax category is a pair of definition list and statement (program body) *)
type t = Definition.t list * Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval (defs, p) i = 
  let module DefMap = Map.Make(String) in
  let definitions = List.fold_left (fun m ((name, _) as def) -> DefMap.add name def m) DefMap.empty defs in
  let env = (object method definition name = snd (DefMap.find name definitions) end) in
  let _, _, o = Stmt.eval env (State.empty, i, []) p
  in o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))

                                    