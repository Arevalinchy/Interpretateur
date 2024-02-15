type value =
  | VInt of int
  | VFloat of float
  | VBool of bool
  | VArray of string * value Util.Environment.t
  | VNone

exception Wrong_type_operand of string * value * value

let rec string_of_value = function
  | VInt v -> string_of_int v
  | VFloat v -> string_of_float v
  | VBool v -> if v then "true" else "false"
  | VArray (name, env) ->
      let size =
        try Option.get (Util.Environment.get env (name ^ "size"))
        with _ -> VNone
      in
      let res =
        ref (Format.asprintf "(%s:%s)-->[" name (string_of_value size))
      in
      (match size with
      | VInt size ->
          for i = 0 to size - 1 do
            res :=
              !res
              ^ (if i > 0 then "," else "")
              ^ string_of_value
                  (try
                     Option.get
                       (Util.Environment.get env (name ^ string_of_int i))
                   with _ -> VNone)
          done
      | _ -> res := !res ^ "error: non-integer sized array");
      !res ^ "]"
  | VNone -> "undefined"

let value_of_string argument =
  if argument = "" then VNone
  else if argument = "true" then VBool true
  else if argument = "false" then VBool false
  else
    try VInt (int_of_string argument)
    with _ -> (
      try VFloat (float_of_string argument)
      with _ -> failwith ("unrecognised argument : " ^ argument))

(*note : does not support arrays of array, while technically the machine supports it.*)
let parse_complex_argument_and_affect map name argument =
  if String.length argument > 0 && argument.[0] = '[' then (
    let list =
      String.split_on_char ','
        (String.sub argument 1 (String.length argument - 2))
    in
    Util.Environment.modify map name (VArray (name ^ "#", map));
    Util.Environment.modify map (name ^ "#size") (VInt (List.length list));
    List.iteri
      (fun i a ->
        Util.Environment.modify map
          (name ^ "#" ^ string_of_int i)
          (value_of_string a))
      list)
  else Util.Environment.modify map name (value_of_string argument)

let pp_value_environment =
  Util.Environment.pp_environment (fun fmt m ->
      Format.fprintf fmt "%s" (string_of_value m))

let add_i v1 v2 =
  match (v1, v2) with
  | VInt a, VInt b -> VInt (a + b)
  | _ -> raise (Wrong_type_operand ("add_i", v1, v2))

let sub_i v1 v2 =
  match (v1, v2) with
  | VInt a, VInt b -> VInt (a - b)
  | _ -> raise (Wrong_type_operand ("sub_i", v1, v2))

let mul_i v1 v2 =
  match (v1, v2) with
  | VInt a, VInt b -> VInt (a * b)
  | _ -> raise (Wrong_type_operand ("mul_i", v1, v2))

let div_i v1 v2 =
  match (v1, v2) with
  | VInt a, VInt b -> VInt (a / b)
  | _ -> raise (Wrong_type_operand ("div_i", v1, v2))

let mod_i v1 v2 =
  match (v1, v2) with
  | VInt a, VInt b -> VInt (a mod b)
  | _ -> raise (Wrong_type_operand ("mod_i", v1, v2))

let add_f v1 v2 =
  match (v1, v2) with
  | VFloat a, VFloat b -> VFloat (a +. b)
  | _ -> raise (Wrong_type_operand ("add_f", v1, v2))

let sub_f v1 v2 =
  match (v1, v2) with
  | VFloat a, VFloat b -> VFloat (a -. b)
  | _ -> raise (Wrong_type_operand ("sub_f", v1, v2))

let mul_f v1 v2 =
  match (v1, v2) with
  | VFloat a, VFloat b -> VFloat (a *. b)
  | _ -> raise (Wrong_type_operand ("mul_f", v1, v2))

let div_f v1 v2 =
  match (v1, v2) with
  | VFloat a, VFloat b -> VFloat (a /. b)
  | _ -> raise (Wrong_type_operand ("div_f", v1, v2))

let mod_f v1 v2 =
  match (v1, v2) with
  | VFloat a, VFloat b -> VFloat (mod_float a b)
  | _ -> raise (Wrong_type_operand ("mod_f", v1, v2))

let and_b v1 v2 =
  match (v1, v2) with
  | VBool a, VBool b -> VBool (a && b)
  | _ -> raise (Wrong_type_operand ("and_b", v1, v2))

let or_b v1 v2 =
  match (v1, v2) with
  | VBool a, VBool b -> VBool (a || b)
  | _ -> raise (Wrong_type_operand ("and_b", v1, v2))

let not_b v =
  match v with
  | VBool a -> VBool (not a)
  | _ -> raise (Wrong_type_operand ("not_b", v, v))

let eq_m v1 v2 =
  match (v1, v2) with
  | VInt a, VInt b -> VBool (a = b)
  | VFloat a, VFloat b -> VBool (a = b)
  | VBool a, VBool b -> VBool (a = b)
  | _ -> raise (Wrong_type_operand ("eq", v1, v2))

let lt_m v1 v2 =
  match (v1, v2) with
  | VInt a, VInt b -> VBool (a < b)
  | VFloat a, VFloat b -> VBool (a < b)
  | VBool a, VBool b -> VBool (a < b)
  | _ -> raise (Wrong_type_operand ("lt", v1, v2))


