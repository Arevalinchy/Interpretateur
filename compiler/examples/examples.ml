open Examples_generated
open Course_language

type ast =
  | Expression of Ast.expr
  | Instruction of Ast.instruction
  | Program of Ast.function_decl list

let all_examples =
  List.map (fun (n, e) -> (n, Expression e)) expressions
  @ List.map (fun (n, i) -> (n, Instruction i)) instructions
  @ List.map (fun (n, f) -> (n, Program f)) programs

let print_possibilities fmt () =
  Format.fprintf fmt "@[<v 0>@[<v 2>Expressions:";
  List.iter (fun (n, _) -> Format.fprintf fmt "@,%s" n) expressions;
  Format.fprintf fmt "@]@,@,@[<v 2>Instructions:";
  List.iter (fun (n, _) -> Format.fprintf fmt "@,%s" n) instructions;
  Format.fprintf fmt "@]@,@,@[<v 2>Programs:";
  List.iter (fun (n, _) -> Format.fprintf fmt "@,%s" n) programs;
  Format.fprintf fmt "@]@,@]"

let parse_arguments_var list =
  let list =
    List.map
      (fun s ->
        let l = String.split_on_char ':' s in
        (List.hd l, List.hd (List.tl l)))
      list
  in
  let env = Util.Environment.new_environment () in
  List.iter
    (fun (n, a) -> Abstract_machine.parse_complex_argument_and_affect env n a)
    list;
  env

let print_example name =
  match
    try List.assoc name all_examples with _ -> failwith "undefined example"
  with
  | Expression e ->
      Format.printf "@[<v 0>Expression %s:@,%s@,@]" name (Ast.string_of_expr e)
  | Instruction i ->
      Format.printf "@[<v 0>Instruction %s@,%a@,@]" name Ast.pp_instruction i
  | Program p ->
      Format.printf "@[<v 0>Program %s@," name;
      List.iter (Format.printf "%a" Ast.pp_func_decl) p

let execute_example name arguments =
  let example =
    try List.assoc name all_examples with _ -> failwith "undefined example"
  in
  match example with
  | Expression e ->
      let memory = parse_arguments_var arguments in
      let functions = Util.Environment.new_environment () in
      Format.printf "@[<v 0>Initial Environment:@,%a@,"
        Abstract_machine.pp_value_environment memory;
      let res = Interpreter.interpret_expr memory functions e in
      Format.printf "Computed value :@,%s@,@]"
        (Abstract_machine.string_of_value res)
  | Instruction i ->
      let memory = parse_arguments_var arguments in
      let functions = Util.Environment.new_environment () in
      Format.printf "@[<v 0>Initial Environment:@,%a@,"
        Abstract_machine.pp_value_environment memory;
      Interpreter.interpret_instruction memory functions i;
      Format.printf "Final Environment:@,%a@,@]"
        Abstract_machine.pp_value_environment memory
  | Program p ->
      Format.printf "@[<v 0>Execution of %s@," name;
      Interpreter.interpret_prg p arguments;
      Format.printf "@,@]"
