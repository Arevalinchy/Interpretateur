module Command_line = struct
  let only_display = ref false
  let list_possibilities = ref false

  let arg_spec_list =
    [
      ( "-display",
        Arg.Set only_display,
        "if present, does not execute the program, only displays it in \
         readable format" );
      ( "-list",
        Arg.Set list_possibilities,
        "if present, does not analyse the command line, but only list the \
         known programs" );
    ]

  let usage_msg =
    "Usage: " ^ Sys.argv.(0)
    ^ " [program name] (arguments)\n\
       Utility program to test your interpreter. Might be used on expressions, \
       instructions or full programs that are defined in module Examples.\n\
       Format of arguments depend of the type of the program:\n\
      \  - if it is expressions or instruction, argument must be of the form \
       <var_name>:<value> where <var_name> is the name of the program variable \
       initialised with this value, and <value> is either an integer, a float, \
       a boolean, or an array of values of the form [<v1>,...,<vk>].\n\
      \  - if it is a full program, then the arguments are simply values that \
       are the arguments of the main function.\n\
       If too many arguments are provided, the excedentary ones will be \
       ignored. If some arguments are missing, their value will be set to \
       undefined (program is thus likely to crash).\n"

  let parse () =
    let filename = ref None in
    let arguments = ref [] in
    Arg.parse (Arg.align arg_spec_list)
      (fun a ->
        match !filename with
        | None -> filename := Some a
        | Some _ -> arguments := a :: !arguments)
      usage_msg;
    match !filename with
    | Some a -> (a, List.rev !arguments)
    | None ->
        if !list_possibilities then ("", [])
        else (
          Arg.usage arg_spec_list usage_msg;
          exit 0)
end

let example, arguments = Command_line.parse ()

let () =
  if !Command_line.list_possibilities then (
    Format.printf "%a" Examples.print_possibilities ();
    exit 0)

let () = Examples.print_example example
let () = if !Command_line.only_display then exit 0
let () = Examples.execute_example example arguments
