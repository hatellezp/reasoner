

(*============================================================================*)

type tFact = {subsumed: Term.concept; subsumer: Term.concept}

let is_variable_t_fact f =
  (Term.is_variable_base f.subsumed.value) && (Term.is_variable_base f.subsumer.value)

let has_full_variable_t_fact f =
  (Term.has_full_variable_base f.subsumed.value) &&
  (Term.has_full_variable_base f.subsumer.value)

let to_string_t_fact (tf:tFact): string =
  Printf.sprintf "[TF:(%s) <= (%s)]" tf.subsumed.name tf.subsumer.name

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

let to_string_a_fact (af:aFact): string =
  match af with
  | Con(cons, con) -> (
    Printf.sprintf "[AF: (%s:%s)]" (Term.to_string_constant cons) con.name
  )
  | Rol(con1, con2, r) -> (
    Printf.sprintf "[AF: ((%s, %s): %s)" (Term.to_string_constant con1)
      (Term.to_string_constant con2)  (Term.to_string_role r)
  )

(*============================================================================*)

type fact = | A of aFact
            | T of tFact

let has_full_variable_fact f =
  match f with
  | A(a) -> has_full_variable_a_fact a
  | T(t) -> has_full_variable_t_fact t

let to_string_fact f =
  match f with
  | A(af) -> to_string_a_fact af
  | T(tf) -> to_string_t_fact tf

(*============================================================================*)

type aBOX = aFact list

type tBOX = tFact list
;;