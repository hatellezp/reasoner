

(*============================================================================*)

type tFact = {subsumed: Term.concept; subsumer: Term.concept}

let is_variable_t_fact f =
  (Term.is_variable_base f.subsumed.value) && (Term.is_variable_base f.subsumer.value)

let has_full_variable_t_fact f =
  (Term.has_full_variable_base f.subsumed.value) &&
  (Term.has_full_variable_base f.subsumer.value)

let is_grounded_t_fact f =
  (Term.is_grounded_concept f.subsumed) &&
  (Term.is_grounded_concept f.subsumer)


(*temporary change*)
let to_string_t_fact (tf:tFact): string =
  Printf.sprintf "[TF:%s < %s]" (Term.to_string_concept tf.subsumed) 
    (Term.to_string_concept tf.subsumer)

(*============================================================================*)

type aFact =  | Con of Term.constant * Term.concept
              | Rol of Term.constant * Term.constant * Term.role

let has_full_variable_a_fact af =
  match af with
  | Con(cons, cpt) -> (
    (Term.has_full_variable_constant cons) &&
    (Term.has_full_variable_base cpt.value)
  )
  | Rol(con1, con2, r) -> (
    (Term.has_full_variable_constant con1) &&
    (Term.has_full_variable_constant con2) &&
    (Term.has_full_variable_role r)
  )

let is_grounded_a_fact f =
  match f with
  | Con(cons, cpt) -> (
    (Term.is_grounded_constant cons) &&
    (Term.is_grounded_concept cpt)
  )
  | Rol(con1, con2, r) -> (
    (Term.is_grounded_constant con1) &&
    (Term.is_grounded_constant con2) &&
    (Term.is_grounded_role r)
  )
let to_string_a_fact (af:aFact): string =
  match af with
  | Con(cons, con) -> (
    Printf.sprintf "[AF: %s:%s]" (Term.to_string_constant cons) (Term.to_string_concept con) (*change this!!*)
  )
  | Rol(con1, con2, r) -> (
    Printf.sprintf "[AF: (%s, %s): %s" (Term.to_string_constant con1)
      (Term.to_string_constant con2)  (Term.to_string_role r)
  )

(*============================================================================*)

type fact = | A of aFact
            | T of tFact

let has_full_variable_fact f =
  match f with
  | A(a) -> has_full_variable_a_fact a
  | T(t) -> has_full_variable_t_fact t

let is_grounded_fact f =
  match f with
  | A(a) -> is_grounded_a_fact a
  | T(t) -> is_grounded_t_fact t

let to_string_fact f =
  match f with
  | A(af) -> to_string_a_fact af
  | T(tf) -> to_string_t_fact tf

(*============================================================================*)

type aBOX = aFact list

let is_grounded_a_box ab =
  List.fold_left (&&) true (List.map is_grounded_a_fact ab)

(*============================================================================*)

type tBOX = tFact list

let is_grounded_t_box tb =
  List.fold_left (&&) true (List.map is_grounded_t_fact tb)

(*============================================================================*)