open GT       
open Language
open List
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string
(* create an S-expression          *) | SEXP    of string * int
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool
(* drops the top element off       *) | DROP
(* duplicates the top element      *) | DUP
(* swaps two top elements          *) | SWAP
(* checks the tag of S-expression  *) | TAG     of string
(* enters a scope                  *) | ENTER   of string list
(* leaves a scope                  *) | LEAVE
with show
                                                   
(* The type for the stack machine program *)
type prg = insn list
                            
(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
*)
type config = (prg * State.t) list * Value.t list * Expr.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)
let split n l =
  let rec unzip (taken, rest) = function
  | 0 -> (List.rev taken, rest)
  | n -> let h::tl = rest in unzip (h::taken, tl) (n-1)
  in
  unzip ([], l) n
        
let rec eval env ((cstack, stack, ((st, i, o) as c)) as conf) = function
| [] -> conf
| insn :: prg' ->
(match insn with
| JMP jmp -> eval env conf (env#labeled jmp)
| CJMP (cond, jmp) -> let x::stack' = stack in eval env (cstack, stack', c) 
    (if (cond = "z" && (Value.to_int x) = 0 || cond = "nz" && (Value.to_int x) <> 0)
    then (env#labeled jmp) 
    else prg')
| CALL (fname, n, p) -> if env#is_label fname
                        then eval env ((prg', st) :: cstack, stack, c) (env#labeled fname)
                        else eval env (env#builtin conf fname n p) prg'
| BEGIN (_, args, locals) -> 
    let rec zip accumulator args stack = (match args, stack with
        | [], _ -> List.rev accumulator, stack
        | a::args', head::stack' -> zip ((a, head)::accumulator) args' stack') in
    let acc, stack' = zip [] args stack in
    let state' = List.fold_left (fun s (x, v) -> State.update x v s) (State.enter st (args @ locals)) acc, i, o in
        eval env (cstack, stack', state') prg'
| END | RET _ -> (match cstack with
    | (prg, st') :: cstack' -> eval env (cstack', stack, (State.leave st st', i, o)) prg
    | [] -> conf)
| BINOP op -> let y::x::stack' = stack in eval env (cstack, Value.of_int (Expr.to_func op (Value.to_int x) (Value.to_int y)) :: stack', c) prg'
| CONST i  -> eval env (cstack, (Value.of_int i)::stack, c) prg'
| STRING s -> eval env (cstack, (Value.of_string s)::stack, c) prg'
| LD x     -> eval env (cstack, State.eval st x :: stack, c) prg'
| ST x     -> let z::stack' = stack in eval env (cstack, stack', (State.update x z st, i, o)) prg'
| STA (x, n) -> let v::is, stack' = split (n + 1) stack in (cstack, stack', (Language.Stmt.update st x v (List.rev is), i, o))
| SEXP (s, n) -> let v, stack' = split n stack in eval env (cstack, (Value.sexp s (List.rev v))::stack', c) prg'
| DROP -> eval env (cstack, List.tl stack, c) prg'
| DUP -> eval env (cstack, List.hd stack :: stack, c) prg'
| SWAP -> let a::b::stack' = stack in eval env (cstack, b::a::stack', c) prg'
| TAG t -> let a::stack' = stack in eval env (cstack, (Value.of_int (match a with Value.Sexp (t', _) when t' = t -> 1 | _ -> 0))::stack', c) prg'
| ENTER xs -> let vals, stack' = split (List.length xs) stack in let combined = List.combine xs vals in eval env (cstack, stack', (State.push st (List.fold_left (fun s (x, v) -> State.bind x v s) State.undefined combined) xs, i, o)) prg'
| LEAVE -> eval env (cstack, stack, (State.drop st, i, o)) prg'
| LABEL label -> eval env conf prg'
)

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, _, (_, _, o)) =
    eval
      (object
         method is_label l = M.mem l m
         method labeled l = M.find l m
         method builtin (cstack, stack, (st, i, o)) f n p =
           let f = match f.[0] with 'L' -> String.sub f 1 (String.length f - 1) | _ -> f in
           let args, stack' = split n stack in
           let (st, i, o, r) = Language.Builtin.eval (st, i, o, None) (List.rev args) f in
           let stack'' = if p then stack' else let Some r = r in r::stack' in
           Printf.printf "Builtin: %s\n";
           (cstack, stack'', (st, i, o))
       end
      )
      ([], [], (State.empty, i, []))
      p
  in
  o

class labels = 
  object (self)
    val cnt = 0
    method get_label = "label_" ^ string_of_int cnt, {<cnt = cnt + 1>}
    method get_flabel name = "L" ^ name
  end 

let rec compile_expr e =
   match e with
   | Expr.Const n -> [CONST n]
   | Expr.Var x -> [LD x]
   | Expr.Binop (op, a, b) -> compile_expr a @ compile_expr b @ [BINOP op]
   | Expr.Call (func, args) -> prep_args args @ [CALL (func, List.length args, false)]
and prep_args args = List.concat (List.rev_map compile_expr args)

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let rec compile (defs, p) =
  let label s = "L" ^ s in
  let rec expr = function
  | Expr.Var x -> [LD x]
  | Expr.Const n -> [CONST n]
  | Expr.String s -> [STRING s]
  | Expr.Array arr -> List.flatten (List.map expr arr) @ [CALL ("$array", List.length arr, false)]
  | Expr.Elem (arr, pos) -> expr arr @ expr pos @ [CALL ("$elem", 2, false)]
  | Expr.Length arr  -> expr arr @ [CALL ("$length", 1, false)]
  | Expr.Call (fname, args) -> (
      let comp_args = List.concat (List.map expr (List.rev args)) in
        comp_args @ [CALL ("L" ^ fname, List.length args, false)]
    )
  | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
  | Expr.Sexp (t, xs) -> List.flatten (List.map expr xs) @ [SEXP (t, List.length xs)]
  in 
  let rec call f args p = let args_code = List.concat @@ List.map expr args in args_code @ [CALL (label f, List.length args, p)]
  and pattern lfalse = function
    | Stmt.Pattern.Wildcard -> [DROP]
    | Stmt.Pattern.Sexp (t, ps) -> [DUP; TAG t; CJMP ("z", lfalse)] @ (List.concat (List.mapi (fun i p -> [DUP; CONST i; CALL (".elem", 2, false)] @ pattern lfalse p) ps))
    | Stmt.Pattern.Ident _ -> [DROP]
  and bindings p = let rec inner = function
    | Stmt.Pattern.Ident _ -> [SWAP]
    | Stmt.Pattern.Sexp (_, ps) -> (List.flatten (List.mapi (fun i p -> [DUP; CONST i; CALL (".elem", 2, false)] @ inner p) ps)) @ [DROP]
    | Stmt.Pattern.Wildcard -> [DROP]
    in inner p @ [ENTER (Stmt.Pattern.vars p)]
  in let rec compileStmt end_label labels = function  
  | Stmt.Assign (x, [], e) -> (labels, expr e @ [ST x])
  | Stmt.Assign (x, is, e) -> (labels, List.flatten (List.map expr (is @ [e])) @ [STA (x, List.length is)])
  | Stmt.Skip -> (labels, [])
  | Stmt.Seq (st1, st2) -> 
    let (c1, prg1) = compileStmt end_label labels st1 in
    let (c2, prg2) = compileStmt end_label c1 st2 in
    (c2, prg1 @ prg2)                                     
  | Stmt.If (cond, st1, st2) -> 
    let label_then, cur_labels = labels#get_label in
    let label_else, cur_labels = cur_labels#get_label in
    let c1, prg1 = compileStmt end_label cur_labels st1 in
    let c2, prg2 = compileStmt end_label c1 st2 in
    (c2, expr cond @ [CJMP ("z", label_then)] @ prg1 @ [JMP label_else; LABEL label_then] @ prg2 @ [LABEL label_else])                        
  | Stmt.While (cond, st) -> 
    let label_loop, cur_labels = labels#get_label in
    let label_check, cur_labels = cur_labels#get_label in
    let (c1, prg1) = compileStmt end_label cur_labels st in
    (c1, [JMP label_check; LABEL label_loop] @ prg1 @ [LABEL label_check] @ expr cond @ [CJMP ("nz", label_loop)])
  | Stmt.Repeat (st, cond) ->  
    let label_loop, cur_labels = labels#get_label in
    let (c1, prg1) = compileStmt end_label cur_labels st in
    (c1, [LABEL label_loop] @ prg1 @ expr cond @ [CJMP ("z", label_loop)])
  | Stmt.Call (fname, args) -> 
    let comp_args = List.concat (List.map expr (List.rev args)) in
        labels, comp_args @ [CALL (labels#get_flabel fname, List.length args, true)]
  | Stmt.Return res -> (labels, (match res with None -> [] | Some v -> compile_expr v) @ [RET (res <> None)])
  | Stmt.Leave -> labels, [LEAVE]
  | Stmt.Case (expr', [p, stm]) -> let labels1, res1 = compileStmt end_label labels (Stmt.Seq (stm, Stmt.Leave)) in labels1, expr expr' @ (pattern end_label p) @ bindings p @ res1
  | Stmt.Case (expr', cases) ->
    let n = List.length cases - 1 in let labels2, _, _, code = 
      List.fold_left (fun (env1, labels', i, code) (p, s) -> let (lf, env), jmp = if i = n then (end_label, env1), [] else labels#get_label, [JMP end_label] in 
        let labels1, stm = compileStmt end_label labels (Stmt.Seq (s, Stmt.Leave)) in  
        (labels1, Some lf, i + 1, ((match labels' with None -> [] | Some l -> [LABEL l]) @ (pattern lf p) @ bindings p @ stm @ jmp) :: code)) (labels, None, 0, []) cases
    in labels2, expr expr' @ (List.flatten (List.rev code))
  in
  let rec compileDef labels (fname, (params, locals, body)) =
    let end_label, labels = labels#get_label in 
    let labels', body' = compileStmt end_label labels body in
        labels', [LABEL fname; BEGIN (fname, params, locals)] @ body' @ [LABEL end_label; END]  
  in let end_label, labels = (new labels)#get_label
  in let (t_labels, prg) = List.fold_left (fun (l, b) (name, c) -> let (l', b') = compileDef l (labels#get_flabel name, c) in (l', b @ b'))
                                          (let (labels_stmt, prg_stmt) = compileStmt end_label labels p in (labels_stmt, prg_stmt @ [LABEL end_label; END])) defs
  in prg

