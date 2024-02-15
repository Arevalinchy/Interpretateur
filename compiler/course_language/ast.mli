(** This modules defines the language that we manipulate in this compilation course (see the poly for more details), alongside some functions for displaying programs in a readable manner.*)

(** Type representing the basic types of elements manipulated by the program. [TNull] stands for functions that do not return any value. These types are ignored by the interpreter (but will be used when compiling to a real machine, so they are included by completeness).*)
type type_basic = TInt | TFloat | TBool | TNull

(** Type representing the full types that can be manipulated by the program (variables and arguments). They are either a basic type or an array of basic types. As for [type_basic], the interpreter ignores them.*)
type type_value = Basic of type_basic | Array_t of type_basic

(** Type representing the type of arguments of function. An argument can either be a reference or a value, and in both cases are characterized by a type.*)
type type_argument = Reference | Value

(** Module representing annotations of AST nodes. Its type is generic for every node, and thus contains informations that are not useful for all node types.
    Contains
    - position in the source file (set by the parser, used for printing errors)
    - type (for {!expr})
    - type of arguments (for {!expr} that are used as an argument in a function call)
    - type of function (for {!function_decl}).

    {!instruction} do not use any type annotation.
    These annotation are useful in the semantic analysis phase, and the translation to low-level code phase.*)
module Annotation : sig
  type t
  (** The type of annotations*)

  val create : Util.Position.t -> t
  (** Creates an annotation with only the position set. Only used by the parser.*)

  val create_dummy : unit -> t
  (** Creates a dummy annotation for AST nodes that are created inside other functions not from the source.*)

  val get_pos : t -> Util.Position.t
  (** [get_pos annotation] returns the position of [annotation].*)

  val get_type : t -> type_value option
  (** [get_type annotation] returns [Some t] if annotation has [t] for type and [None] otherwise.*)

  val get_arg_type : t -> type_argument option
  (** [get_arg_type annotation] returns [Some t] if annotation has [t] for argument type and [None] otherwise.*)

  val get_function_type :
    t -> (type_basic * (type_argument * type_value) list) option
  (** [get_function_type annotation] returns [Some t] if annotation has [t] for function type and [None] otherwise.*)

  val set_type : t -> type_value -> unit
  (** [set_type annotation t] sets the type of [annotation] to [t].*)

  val set_arg_type : t -> type_argument -> unit
  (** [set_arg_type annotation t] sets the argument type of [annotation] to [t].*)

  val set_function_type :
    t -> type_basic * (type_argument * type_value) list -> unit
  (** [set_function_type annotation t] sets the function type of [annotation] to [t].*)
end

(** Type representing the binary operations that can act on elements manipulated by the program.*)
type binop =
  | Add  (** Addition*)
  | Sub  (** Substraction*)
  | Mul  (** Multiplication*)
  | Div  (** Division*)
  | Mod  (** Modulus*)
  | And  (** Boolean and*)
  | Or  (** Boolean or*)
  | Eq  (** Equality*)
  | Neq  (** Inequality*)
  | Lt  (** Strict less than*)
  | Gt  (** Strict greater than*)
  | Leq  (** Less than or equal*)
  | Geq  (** Greater than or equal*)

(** Type representing the unary operations that can act on elements manipulated by the program.*)
type unop = UMin  (** Integer unary minus*) | Not  (** Boolean negation*)

(** Type representing an expression of our language.*)
type expr =
  | Cst_i of int * Annotation.t
  | Cst_f of float * Annotation.t
  | Cst_b of bool * Annotation.t
  | Var of string * Annotation.t
  | Binop of binop * expr * expr * Annotation.t
  | Unop of unop * expr * Annotation.t
  | Array_val of string * expr * Annotation.t
      (** Value of a position of an array*)
  | Size_tab of string * Annotation.t
  | Func of string * expr list * Annotation.t  (** Function call*)

(** Type representing an instruction of our language.*)
type instruction =
  | Affect of string * expr * Annotation.t  (** Affectation to a variable*)
  | Block of instruction list * Annotation.t
  | IfThenElse of expr * instruction * instruction * Annotation.t
  | While of expr * instruction * Annotation.t
  | Affect_array of string * expr * expr * Annotation.t
      (** Affectation to an array cell. The first expression is the position and the second the value to affect*)
  | Array_decl of type_basic * string * expr * Annotation.t
  | Proc of string * expr list * Annotation.t  (** Procedure call*)
  | Return of expr option * Annotation.t
  | Print_str of string * Annotation.t
  | Print_expr of expr * Annotation.t
  | Var_decl of type_basic * string * Annotation.t

type argument = type_argument * type_value * string
(** Type representing the arguments of function declarations.*)

(** Type representing a declaration of function in our language.*)
type function_decl =
  | Func_decl of
      type_basic * string * argument list * instruction * Annotation.t

type t =
  | Program of function_decl list
  | Instruction of instruction
  | Expression of expr

(** Below are the functions devoted to print programs in a readable manner.*)

val string_of_type_basic : type_basic -> string
(** Returns a string representation of a basic type.*)

val string_of_type_value : type_value -> string
(** Returns a string representation of a full type.*)

val string_of_binop : binop -> string
(** Returns a string representation of a binary operation.*)

val string_of_unop : unop -> string
(** Returns a string representation of a unary operation.*)

val string_of_expr : expr -> string
(** Returns a string representation of an expression.*)

val pp_instruction : Format.formatter -> instruction -> unit
(** Pretty printer for an instruction (displays it on several lines if needed). Should be called by [Format.printf "@[<v 1>%a@]" pp_instruction inst] to print the instruction [inst] with nice output. [Format.printf] can be replaced by [Format.fprintf] to print in an arbitrary output channel, or [Format.asprintf] to print in a string. Cf Format library for more details.*)

val string_of_argument : argument -> string
(** Returns a string representation of an argument.*)

val pp_func_decl : Format.formatter -> function_decl -> unit
(** Pretty printer for declaration of functions.*)

val expr_get_annotation : expr -> Annotation.t
val instruction_get_annotation : instruction -> Annotation.t
val function_decl_get_annotation : function_decl -> Annotation.t

val expr_replace_annotation_position : expr -> Annotation.t -> unit
(** Replaces the position of the position of an expression by that given in argument. Useful for Expression simplification in some cases.*)