(** Module defining the abstract machine on which our language is executed.
          It defines the type of elements manipulated by the machine, two modules defining its memory, its basic operations, and exceptions that it can raise.*)

(** Type representing the different elements the abstract machine can manipulate.
        [VNone] should only be used for uninitialized values.*)
type value =
  | VInt of int  (** integer value *)
  | VFloat of float  (** floating point value *)
  | VBool of bool  (** boolean value *)
  | VArray of string * value Util.Environment.t
      (** Array value. VArray(name,size,env) states that the array values are stored in environment env in cells "<name>#0" to "<name>#<size>". *)
  | VNone  (** undefined value (uninitialized or error value) *)

exception Wrong_type_operand of string * value * value
(** Exception that should be raised whenever the abstract machine is asked to perform an operation over two elements on which it does not apply. It contains a message, and the two values on which the operation was applied.*)

val string_of_value : value -> string
(** Function that gives a textual representation of a value. For arrays, assumes that tab[i] is stored in name "tab#i".*)

val value_of_string : string -> value
(** Function that convert a textual representation of a value into said value. Only works for integer, floats and booleans. *)

val parse_complex_argument_and_affect :
  value Util.Environment.t -> string -> string -> unit
(** [parse_complex_argument_and_affect map name argument] converts [argument] into a value and attributes it to [name] inside [map]. If [argument] is the representation of an array as "\[v0,v1,...,vk\]", it associates [name] to an array of size k+1 and associates each value vi to [name]#i. It doesn't support arrays of arrays.*)

val pp_value_environment : Format.formatter -> value Util.Environment.t -> unit
(** Pretty-printer function for {!value} {!Util.Environment.t}, to see what the interpreter is doing.*)

(** In the following are the basic operations that the machine can apply to values. All of them behave the same way: if the operation is [op], [op v1 v2] returns the result of the operation applied to [v1] and [v2] if it is applicable, and raises an exception [Wrong_type_operand("op",v1,v2)] if it is not applicable because of its type : e.g., [add_i (VFloat 1.0) (VBool true)] will raise [WrongTypeOperent("add_i",(VFloat 1.0),(VBool true))]. On the contrary, [div_i (VInt 14) (VInt 0)] will raise [Division_by_zero], as the functions do not check that the OCaml operation called does not raise it).*)

val add_i : value -> value -> value
val sub_i : value -> value -> value
val mul_i : value -> value -> value
val div_i : value -> value -> value
val mod_i : value -> value -> value
val add_f : value -> value -> value
val sub_f : value -> value -> value
val mul_f : value -> value -> value
val div_f : value -> value -> value
val mod_f : value -> value -> value
val and_b : value -> value -> value
val or_b : value -> value -> value
val not_b : value -> value
val eq_m : value -> value -> value
val lt_m : value -> value -> value
