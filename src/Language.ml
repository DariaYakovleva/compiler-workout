(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT
open List

(* Opening a library for combinator-based syntax analysis *)
open Ostap.Combinators
    
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
                                                            
    (* State: a partial map from variables to integer values. *)
    type state = string -> int 

    (* Empty state: maps every variable into nothing. *)
    let empty = fun x -> failwith (Printf.sprintf "Undefined variable %s" x)

    (* Update: non-destructively "modifies" the state s by binding the variable x 
      to value v and returns the new state.
    *)
    let update x v s = fun y -> if x = y then v else s y

    (* Expression evaluator

          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
    *)
    let cast_to_int value = if value then 1 else 0;;
    let cast_to_bool value = value <> 0;;

    let rec eval state expression = match expression with
        | Const value -> value
        | Var name -> state name
        | Binop (operation, first, second) ->
            let a = eval state first in
            let b = eval state second in
            match operation with
                 | "+" -> a + b
                 | "-" -> a - b
                 | "*" -> a * b
                 | "/" -> a / b
                 | "%" -> a mod b
                 | "!!" -> cast_to_int (cast_to_bool a || cast_to_bool b)
                 | "&&" -> cast_to_int (cast_to_bool a && cast_to_bool b)
                 | "==" -> cast_to_int (a == b)
                 | "!=" -> cast_to_int (a != b)
                 | "<=" -> cast_to_int (a <= b)
                 | "<" -> cast_to_int (a < b)
                 | ">=" -> cast_to_int (a >= b)
                 | ">" -> cast_to_int (a > b)
                 | _ -> failwith (Printf.sprintf "Undefined operation %s" operation) 

    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string
   
    *)
    ostap (
      parse: empty {failwith "Not implemented yet"}
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
    (* composition                      *) | Seq    of t * t with show

    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list 

    (* Statement evaluator

          val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    *)
    let rec eval (state, instream, outstream) statement = match statement with
      | Read v -> (Expr.update v (hd instream) state, tl instream, outstream)
      | Write expression -> (state, instream, outstream @ [Expr.eval state expression])
      | Assign (variable, expression) -> (Expr.update variable (Expr.eval state expression) state, instream, outstream)
      | Seq (state1, state2) -> eval (eval (state, instream, outstream) state1) state2
      | _ -> failwith "Incorrect statement"                                                     
                                                         
    (* Statement parser *)
    ostap (
      parse: empty {failwith "Not implemented yet"}
    )

  end

(* The top-level definitions *)

(* The top-level syntax category is statement *)
type t = Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval p i =
  let _, _, o = Stmt.eval (Expr.empty, i, []) p in o
