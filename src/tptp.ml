open Dolmen
(* minimal.ml *)
module V6_3_0 = Dolmen_tptp_v6_3_0
(* module Location = V6_3_0.Location  Built-in location module *)
(* module MyTerm =  Built-in Term module *)

module Parser = V6_3_0.Make (Std.Loc)(Std.Id)(Std.Term)(Std.Statement)


open Std 
open Term

(* Unwrap an outer application with no arguments (if present) *)
let rec unwrap t =
  match t.term with
  | App (t', []) -> unwrap t'
  | _ -> t

(* Extract a list of inner terms from a "$data" application.
   It expects that t is an application whose function is the symbol "$data". *)
let extract_data_list t =
  match t.term with
  | App (f, args) ->
      (match f.term with
       | Symbol sym ->
           (match sym.Dolmen_std.Id.name with
            | Name.Simple "$data" -> args
            | _ -> failwith "Not a $data application")
       | _ -> failwith "Expected symbol in $data application")
  | _ -> failwith "Expected $data application"

(* Convert a term assumed to be a symbol with a simple name to its string *)
(* let get_simple_name t =
  match t.term with
  | Symbol sym ->
      (match sym.Dolmen_std.Id.name with
       | Name.Simple s -> s
       | _ -> failwith "Expected a simple name")
  | _ -> failwith "Expected a symbol" *)

(* Main extraction function.
   It expects an inference term of the form:
     inference(rule, terms1, terms2)
   where:
     - rule is a symbol with the rule name.
     - terms1 is a $data application containing terms
     - terms2 is a $data application containing terms
   Returns a triple: (rule, term list, term list)
*)
let extract_info (t) : string * (Term.t list) * (Term.t list) =
  let t = unwrap t in
  match t.term with
  | App (head, args) ->
      (match head.term with
       | Symbol sym ->
           (match sym.Dolmen_std.Id.name with
            | Name.Simple "inference" ->
                if List.length args < 3 then
                  failwith "Malformed inference term: less than 3 arguments"
                else
                  let rule_term = List.nth args 0 in
                  let int_term  = List.nth args 1 in
                  let name_term = List.nth args 2 in
                  let rule = 
                    match rule_term.term with
                    | Symbol r_sym ->
                        (match r_sym.Dolmen_std.Id.name with
                         | Name.Simple r -> r
                         | _ -> failwith "Expected a simple rule name")
                    | _ -> failwith "Expected rule as a symbol"
                  in
                  let ints = extract_data_list int_term in
                  let names = extract_data_list name_term in
                  (rule, ints, names)
            | _ -> failwith "Not an inference term")
       | _ -> failwith "Expected symbol for head of application")
  | _ -> failwith "Expected an application term"

type proof_step =
  (* Proof Steps for Egg-based proofs *)
  | Cut          of { name_theorem: string; name_in_context: string; and_then: string}
  | LeftForall   of { to_specialize:string; term: string ; and_then : string}
  | RightRefl
  | RightSubst   of { backward: bool ; rw: string; focus: string; and_then: string}

let replace_eq str =
  let len = String.length str in
  let buffer = Buffer.create len in
  let rec aux i =
    if i >= len then
      Buffer.contents buffer
    else if i + 1 < len && str.[i] = '=' && str.[i+1] = '=' then
      (Buffer.add_char buffer '=';
       aux (i + 2))
    else
      (Buffer.add_char buffer str.[i];
       aux (i + 1))
  in
  aux 0
(* let rec drop n lst =
  if n <= 0 then lst
  else match lst with
  | [] -> []
  | _::tl -> drop (n-1) tl *)

(* The main transformation function that converts an AST proof expression
   into our new proof_step datatype. *)
let transform_proof_step (ast_proof : Statement.t) =
  let open Statement in
  let inferenceTptp = try List.nth (ast_proof.attrs) 2 with _ -> failwith "Missing inference structure" in 
  let (name, param1, param2) = extract_info inferenceTptp in
      begin match name with
      | "cut" -> 
          Format.fprintf Format.str_formatter "%a" Term.print (List.nth param2 0);
          let thm = Format.flush_str_formatter () in
          Format.fprintf Format.str_formatter  "%a" Term.print (List.nth param2 1); 
          let after = Format.flush_str_formatter () in
          Format.fprintf Format.str_formatter  "%a" Term.print (List.nth param1 1);
          let name_ctx =  "TPTP"^ (Format.flush_str_formatter ()) in
          Cut { name_theorem = thm; name_in_context = name_ctx; and_then = after}
      | "leftForall" ->
          Format.fprintf Format.str_formatter  "%a" Term.print (List.nth param2 0); 
          let after = Format.flush_str_formatter () in
          Format.fprintf Format.str_formatter  "%a" Term.print (List.nth param1 1);
          let name_ctx =  "TPTP"^ (Format.flush_str_formatter ()) in
          Format.fprintf Format.str_formatter  "%a" Term.print (List.nth param1 2);
          let t = Format.flush_str_formatter () in
          LeftForall { to_specialize =name_ctx; term = t; and_then = after }
      | "rightRefl" ->
          RightRefl 
      | "rightSubst" ->
          Format.fprintf Format.str_formatter  "%a" Term.print (List.nth param2 0); 
          let after = Format.flush_str_formatter () in
          Format.fprintf Format.str_formatter  "%a" Term.print (List.nth param1 1);
          let name_ctx =  "TPTP"^ (Format.flush_str_formatter ()) in
          Format.fprintf Format.str_formatter  "%a" Term.print (List.nth param1 2);
          let bwd =  Format.flush_str_formatter () in
          Format.fprintf Format.str_formatter  "%a" Term.print (List.nth param1 3);
          let focus = "fun HOLE => " ^ (replace_eq (Format.flush_str_formatter ())) in
          RightSubst { backward= if bwd = "0" then false else true; rw = name_ctx ; focus = focus; and_then = after}
      | _ ->
          failwith ("Unsupported proof step: " ^ name)
      end
let generate_map steps =
  List.map (fun (t:Statement.t) -> 
    Format.fprintf Format.str_formatter  "%a" Id.print (Option.get t.id); 
    let id = Format.flush_str_formatter () in
    (id, transform_proof_step t)) (List.filter (fun (t:Statement.t) ->
          let kind = List.nth t.attrs 0 in 
          Format.fprintf Format.str_formatter "%a" Term.print kind;
          let s = Format.flush_str_formatter () in
          s = "(tptp_role plain)"
           ) steps)

let generate_proof file =
  let loc, parsed_statements_lazy = Parser.parse_all (`File file) in
  let parsed_statements = Lazy.force parsed_statements_lazy in
  generate_map  parsed_statements