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
    let empty =
      let e x = failwith (Printf.sprintf "Undefined variable: %s" x) in
      {g = e; l = e; scope = []}

    let rec inScope x scope = match scope with
        | [] -> false
        | y::scope' -> if x == y then true else inScope x scope'

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let u x v s = fun y -> if x = y then v else s y in
      if List.mem x s.scope then {s with l = u x v s.l} else {s with g = u x v s.g}

    (* Evals a variable in a state w.r.t. a scope *)
    let eval s x = (if List.mem x s.scope then s.l else s.g) x

    (* Creates a new scope, based on a given state *)
    let enter st xs = {empty with g = st.g; scope = xs}

    (* Drops a scope *)
    let leave st st' = {st' with g = st.g}

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
    (* binary operator  *) | Binop of string * t * t
    (* function call    *) | Call  of string * t list with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * int option
                                                            
    (* Expression evaluator

          val eval : env -> config -> t -> config

       Takes an environment, a configuration and an expresion, and returns another configuration. The 
       environment supplies the following method

           method definition : env -> string -> int list -> config -> config

       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration, 
       an returns resulting configuration
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

    let rec eval env ((st, i, o, r) as conf) expr =      
      match expr with
      | Const n -> (st, i, o, Some n)
      | Var   x -> (st, i, o, Some (State.eval st x))   
      | Binop (op, x, y) -> 
            let (_, _, _, Some fst) = eval env conf x in
            let (_, _, _, Some snd) = eval env conf y in
                (st, i, o, Some(to_func op fst snd))
      | Call (fname, args) -> 
         let folder = (fun (v, conf) arg -> let (_, _, _, Some p) as conf = eval env conf arg in p :: v, conf) in
         let res, conf = List.fold_left folder ([], conf) args in
                    env#definition env fname (List.rev res) conf
         
    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string                                                                                                                  
    *)
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
      | x:IDENT s:( "(" args:!(Util.list0 parse) ")" {Call (x, args)} | empty {Var x}) {s}
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
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list with show

     let makeSeq x expr = match expr with
        | Skip -> x
        | y    -> Seq (x, y)                                                                
    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment is the same as for expressions
    *)
         
    (* Statement parser *)
    ostap (
      parse: empty {failwith "Not implemented"}

    let rec eval env ((st, i, o, r) as conf) k stmt =
      match stmt with
      | Read x -> eval env (match i with z::i' -> (State.update x z st, i', o, r) | _ -> failwith "Unexpected end of input") Skip k
      | Write e -> eval env (let (st, i, o, Some x) = Expr.eval env conf e in (st, i, o @ [x], r)) Skip k
      | Assign (x, e) -> eval env (let (st, i, o, Some t) = Expr.eval env conf e in (State.update x t st, i, o, r)) Skip k
      | Skip -> (match k with 
                | Skip -> conf
                | _ -> eval env conf Skip k)
      | Seq (s1, s2) -> eval env conf (makeSeq s2 k) s1
      | If (cond, condt, condf) -> 
        let (_, _, _, Some cond_res) as conf = Expr.eval env conf cond in
            eval env conf k (if cond_res <> 0 then condt else condf)
      | While  (cond, condt) -> 
        let (_, _, _, Some cond_res) as conf = Expr.eval env conf cond in
             (if cond_res == 0 then (eval env conf Skip k) else (eval env conf (makeSeq stmt k) condt))
      | Repeat (condt, cond) -> eval env conf (makeSeq (While (Expr.Binop ("==", cond, Expr.Const 0), condt)) k) condt
      | Call (fname, params) -> 
         let conf' = Expr.eval env conf (Expr.Call (fname, params)) in
            eval env conf' Skip k
      | Return res -> (match res with
         | None -> (st, i, o, None)
         | Some x -> Expr.eval env conf x)
      | _ -> failwith "No stmt match"

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
      | x:IDENT todo:(":=" e:!(Expr.parse) {Assign (x, e)} | "(" args:!(Util.list0)[Expr.parse] ")" {Call (x, args)}) {todo}
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
      | %"repeat" condt:parse %"until" cond:!(Expr.parse) {Repeat (condt, cond)}
      | %"for" init:parse "," cond:!(Expr.parse) "," step:parse %"do" condt:parse %"od" {Seq (init, While (cond, Seq (condt, step)))}
      | %"return" res:!(Expr.parse)? {Return res}
    )
      
  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (     
      parse: empty {failwith "Not implemented"}
    )

  end
    
(* The top-level definitions *)

(* The top-level syntax category is a pair of definition list and statement (program body) *)
type t = Definition.t list * Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval (defs, body) i =
  let module M = Map.Make (String) in
  let m          = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in  
  let _, _, o, _ =
    Stmt.eval
      (object
         method definition env f args (st, i, o, r) =
           let xs, locs, s      = snd @@ M.find f m in
           let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
           let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
           (State.leave st'' st, i', o', r')
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
