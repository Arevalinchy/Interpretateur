(** Module defining the interpreter of the course language defined in the module Ast.
    It contains the definition of the abstract machine on which it is runned, and the functions interpreting expressions, instructions and lists of functions declarations in the language.*)

exception Return_exp of Abstract_machine.value option
(** Exception that should be used for handling return values of function calls in the interpreter.*)

exception Non_variable_reference of Ast.expr
(** Exception raised by the interpreter in case something else than a variable is passed as a reference to a function call.*)

exception Non_bool_test of Ast.expr
(** Exception raised by the interpreter if a non-boolean value appears in an [if] or a [while].*)

exception Non_integer_array_position of Ast.expr
(** Exception raised by the interpreter whenever trying to access a non-integer position of an array, or declaring an array of non-integer size.*)

val operation_of_binop :
  Ast.binop ->
  Abstract_machine.value ->
  Abstract_machine.value ->
  Abstract_machine.value
(** Function that associates to a [binop] a function over machine values that corresponds to it. [operation_of_binop op v1 v2] returns the result of the application of [op] to [v1] and [v2].
    
  {b Raises :}
  - {!Abstract_machine.Wrong_type_operand} or [Failure] if the abstract machine instruction(s) called to simulate [op] do so.*)

val operation_of_unop :
  Ast.unop -> Abstract_machine.value -> Abstract_machine.value
(** Function that associates to a [unop] a function over machine values that corresponds to it. [operation_of_unop op v] returns the result of the application of [op] to [v].
    
  {b Raises :}
  - {!Abstract_machine.Wrong_type_operand} or [Failure] if the abstract machine instruction(s) called to simulate [op] do so.*)

val interpret_expr :
  Abstract_machine.value Util.Environment.t ->
  (Ast.argument list * Ast.instruction) Util.Environment.t ->
  Ast.expr ->
  Abstract_machine.value
(** [interpret_expr env functions expr] computes the value of [expr] with environment [env] and function list [functions]. It can modify [env] through side effects of function calls.
    
  {b Raises :}
  - {!Abstract_machine.Wrong_type_operand} or [Failure] if an operation of the abstract machine called here raises it.
  - Any exception raised by {!interpret_instruction} called for evaluating a {!Ast.Func} expression, except {!Return_exp} which is catched here.*)

val interpret_instruction :
  Abstract_machine.value Util.Environment.t ->
  (Ast.argument list * Ast.instruction) Util.Environment.t ->
  Ast.instruction ->
  unit
(** [interpret_instruction env functions instruction] applies the effect of instruction [instruction] on environment [env], in a context where the known functions are in [functions]. It does not return any value, as our instruction do not have values, so it only applies side-effects on [env].

  {b Raises: }
  {ul 
  {- {!Return_exp} when the instruction is (or contains) {!Ast.Return}.}
  {- {!Non_bool_test} when the instruction is {!Ast.IfThenElse} or {!Ast.While} and the expression that is the test does not evaluate as a boolean.}
  {- {!Non_variable_reference} when the instruction is {!Ast.Proc} and one of the expression provided for an argument that is passed for a reference argument is not of the form {!Ast.Var}.}
  {- Any exception raised by {!interpret_expr} when evaluating an expression inside [instruction].}
  }
*)

val interpret_func_decl :
  (Ast.argument list * Ast.instruction) Util.Environment.t ->
  Ast.function_decl ->
  unit
(** [interpret_func_decl functions declaration] modifies the functions environment [functions] to add to it the function declared by [declaration]. If the function declared in [declaration] was already mapped in [functions], the previous declaration is forgotten.*)

val interpret_prg : Ast.function_decl list -> string list -> unit
(** [interpret_prg prg] computes a function environment [functions] from the list of declarations [prg], and then calls the procedure called "main" on an empty environment with the known functions [functions]. It does not return anything, but the prints made by executing the program will be in [stdout].
    
  {b Raises: }
  - Anything that can be raised by {!interpret_instruction}, except {!Return_exp} which is catched here if it occurs during main, or by {!interpret_expr}.*)
