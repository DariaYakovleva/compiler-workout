open GT       
open List
open Syntax
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string with show

(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Syntax.Stmt.config

(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
 *)                         
let rec eval (stack, (state, instream, outstream)) program = match program with
	| [] -> (stack, (state, instream, outstream))
	| firstinsn :: nextinsns -> match firstinsn with
        | CONST c -> eval (c :: stack, (state, instream, outstream)) nextinsns
        | READ -> eval (hd instream :: stack, (state, tl instream, outstream)) nextinsns
		| WRITE -> eval (tl stack, (state, instream, hd stack :: outstream)) nextinsns
		| LD variable -> eval (state variable :: stack, (state, instream, outstream)) nextinsns
		| ST variable -> eval (tl stack, (Expr.update variable (hd stack) state, instream, outstream)) nextinsns
		| BINOP binoper -> 
             let a :: b :: tlstack = stack in
             let res = Expr.eval state (Expr.Binop (binoper, Expr.Const a, Expr.Const b)) in
             eval (res :: tlstack, (state, instream, outstream)) nextinsns

(* Expression compiler
	val compileExpression : Expr.t -> prg

   Takes a expression and return program for the stack machine
*)

let rec compileExpression expression = match expression with
    | Expr.Const value -> [CONST value]
    | Expr.Var variable -> [LD variable]
    | Expr.Binop (operation, a, b) -> (compileExpression a) @ (compileExpression b) @ [BINOP operation]

(* Stack machine compiler

     val compile : Syntax.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)

let rec compile stmt = match stmt with
    | Stmt.Read v -> [READ; ST v]
    | Stmt.Write expression -> (compileExpression expression) @ [WRITE]
    | Stmt.Assign (variable, expression) -> (compileExpression expression) @ [ST variable]
    | Stmt.Seq (state1, state2) -> (compile state1) @ (compile state2)

