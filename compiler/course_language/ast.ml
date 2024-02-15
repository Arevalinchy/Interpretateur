type type_basic = TInt | TFloat | TBool | TNull
type type_value = Basic of type_basic | Array_t of type_basic
type type_argument = Reference | Value

module Annotation = struct
  type t = {
    mutable position : Util.Position.t;
    mutable typ : type_value option;
    mutable arg_typ : type_argument option;
    mutable function_typ :
      (type_basic * (type_argument * type_value) list) option;
  }

  let create pos =
    { position = pos; typ = None; arg_typ = None; function_typ = None }

  let create_dummy () = create (Lexing.dummy_pos, Lexing.dummy_pos)
  let get_pos annotation = annotation.position
  let get_type annotation = annotation.typ
  let get_arg_type annotation = annotation.arg_typ
  let get_function_type annotation = annotation.function_typ
  let set_type annotation typ = annotation.typ <- Some typ
  let set_arg_type annotation arg_type = annotation.arg_typ <- Some arg_type

  let set_function_type annotation function_type =
    annotation.function_typ <- Some function_type
end

type binop =
  | Add
  | Sub
  | Mul
  | Div
  | Mod
  | And
  | Or
  | Eq
  | Neq
  | Lt
  | Gt
  | Leq
  | Geq

type unop = UMin | Not

type expr =
  | Cst_i of int * Annotation.t
  | Cst_f of float * Annotation.t
  | Cst_b of bool * Annotation.t
  | Var of string * Annotation.t
  | Binop of binop * expr * expr * Annotation.t
  | Unop of unop * expr * Annotation.t
  | Array_val of string * expr * Annotation.t
  | Size_tab of string * Annotation.t
  | Func of string * expr list * Annotation.t

type instruction =
  | Affect of string * expr * Annotation.t
  | Block of instruction list * Annotation.t
  | IfThenElse of expr * instruction * instruction * Annotation.t
  | While of expr * instruction * Annotation.t
  | Affect_array of string * expr * expr * Annotation.t
  | Array_decl of type_basic * string * expr * Annotation.t
  | Proc of string * expr list * Annotation.t
  | Return of expr option * Annotation.t
  | Print_str of string * Annotation.t
  | Print_expr of expr * Annotation.t
  | Var_decl of type_basic * string * Annotation.t

type function_decl =
  | Func_decl of
      type_basic
      * string
      * (type_argument * type_value * string) list
      * instruction
      * Annotation.t

type t =
  | Program of function_decl list
  | Instruction of instruction
  | Expression of expr

let string_of_type_basic = function
  | TInt -> "int"
  | TFloat -> "float"
  | TBool -> "bool"
  | TNull -> "null"

let string_of_type_value = function
  | Basic t -> string_of_type_basic t
  | Array_t t -> string_of_type_basic t ^ "[]"

let string_of_type_argument = function Value -> "" | Reference -> "var "

type argument = type_argument * type_value * string

let string_of_argument = function
  | arg_t, typ, name ->
      Format.sprintf "%s%s %s"
        (string_of_type_argument arg_t)
        (string_of_type_value typ) name

let string_of_binop = function
  | Add -> "+"
  | Sub -> "-"
  | Mul -> "*"
  | Div -> "/"
  | Mod -> "%"
  | And -> "&&"
  | Or -> "||"
  | Eq -> "="
  | Neq -> "≠"
  | Lt -> "<"
  | Gt -> ">"
  | Leq -> "<="
  | Geq -> ">="

let string_of_unop = function UMin -> "-" | Not -> "!"

let rec string_of_expr = function
  | Var (s, _) -> s
  | Array_val (v, pos, _) -> v ^ "[" ^ string_of_expr pos ^ "]"
  | Cst_i (v, _) -> string_of_int v
  | Cst_f (v, _) -> string_of_float v
  | Cst_b (v, _) -> if v then "true" else "false"
  | Binop (op, t1, t2, _) ->
      "(" ^ string_of_expr t1 ^ " " ^ string_of_binop op ^ " "
      ^ string_of_expr t2 ^ ")"
  | Unop (op, t, _) -> string_of_unop op ^ "(" ^ string_of_expr t ^ ")"
  | Size_tab (name, _) -> name ^ ".size"
  | Func (func, args, _) ->
      func ^ "("
      ^ fst
          (List.fold_left
             (fun (acc, pos) el ->
               if pos then (acc ^ "," ^ string_of_expr el, true)
               else (string_of_expr el, true))
             ("", false) args)
      ^ ")"

let rec pp_instruction fmt = function
  | Affect (v, t, _) -> Format.fprintf fmt "%s := %s;" v (string_of_expr t)
  | Affect_array (v, pos, t, _) ->
      Format.fprintf fmt "%s[%s] := %s;" v (string_of_expr pos)
        (string_of_expr t)
  | IfThenElse (test, th, el, _) ->
      Format.fprintf fmt "@[<v 1>if %s then@,%a@]@,@[<v 1>else@,%a@]"
        (string_of_expr test) pp_instruction th pp_instruction el
  | While (test, loop, _) ->
      Format.fprintf fmt "@[<v 1>while %s@,%a@]" (string_of_expr test)
        pp_instruction loop
  | Var_decl (typ, name, _) ->
      Format.fprintf fmt "%s %s;" (string_of_type_basic typ) name
  | Array_decl (typ, name, size, _) ->
      Format.fprintf fmt "%s %s[%s];" (string_of_type_basic typ) name
        (string_of_expr size)
  | Proc (func, args, _) ->
      Format.fprintf fmt "%s(" func;
      List.iteri
        (fun pos el ->
          Format.fprintf fmt
            (if pos > 0 then ",%s" else "%s")
            (string_of_expr el))
        args;
      Format.fprintf fmt ");"
  | Return (Some exp, _) -> Format.fprintf fmt "return %s;" (string_of_expr exp)
  | Return (None, _) -> Format.fprintf fmt "return;"
  | Block (l, _) ->
      Format.fprintf fmt "{@[<v 2>";
      List.iter (Format.fprintf fmt "@,%a" pp_instruction) l;
      Format.fprintf fmt "@]@,}"
  | Print_str (str, _) ->
      Format.fprintf fmt "print \"%s\";" (String.escaped str)
  | Print_expr (expr, _) ->
      Format.fprintf fmt "print(%s);" (string_of_expr expr)

let pp_func_decl fmt = function
  | Func_decl (typ, name, args, body, _) ->
      Format.fprintf fmt "%s %s(" (string_of_type_basic typ) name;
      List.iteri
        (fun pos t ->
          Format.fprintf fmt
            (if pos > 0 then ",%s" else "%s")
            (string_of_argument t))
        args;
      Format.fprintf fmt ") ::= @,%a@," pp_instruction body

let expr_get_annotation = function
  | Var (_, a) -> a
  | Array_val (_, _, a) -> a
  | Cst_i (_, a) -> a
  | Cst_f (_, a) -> a
  | Cst_b (_, a) -> a
  | Binop (_, _, _, a) -> a
  | Unop (_, _, a) -> a
  | Size_tab (_, a) -> a
  | Func (_, _, a) -> a

let instruction_get_annotation = function
  | Affect (_, _, a) -> a
  | Block (_, a) -> a
  | IfThenElse (_, _, _, a) -> a
  | While (_, _, a) -> a
  | Affect_array (_, _, _, a) -> a
  | Array_decl (_, _, _, a) -> a
  | Proc (_, _, a) -> a
  | Return (_, a) -> a
  | Print_str (_, a) -> a
  | Print_expr (_, a) -> a
  | Var_decl (_, _, a) -> a

let function_decl_get_annotation = function Func_decl (_, _, _, _, a) -> a

let expr_replace_annotation_position expr annotation =
  (expr_get_annotation expr).position <- Annotation.(annotation.position)
