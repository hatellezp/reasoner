

(*============================================================================*)

type conflict = Box.fact -> Box.fact -> bool



let not_empty_bottom (fa1:Box.fact) (fa2:Box.fact) =
  match fa1, fa2 with
  | A(a1), _ -> (
    match a1 with
    | Rol(_, _, _) -> false
    | Con(_,c) -> Term.equal_base Bottom c.value
  )
  | _, A(a2) -> (
    match a2 with
    | Rol(_, _, _) -> false
    | Con(_,c) -> Term.equal_base Bottom c.value
  )
  | _, _ -> false

let not_empty_implied_bottom (fa1:Box.fact) (fa2:Box.fact) =
  match fa1, fa2 with
  | A(a1), T(t2) -> (
    match a1 with
    | Con(_, c1) -> (
      (Term.equal_base c1.value t2.subsumed.value) &&
      (Term.equal_base Bottom t2.subsumer.value) 
    )
    | _ -> false
  )
  | T(t2), A(a1) -> (
    match a1 with
    | Con(_, c1) -> (
      (Term.equal_base c1.value t2.subsumed.value) &&
      (Term.equal_base Bottom t2.subsumer.value) 
    )
    | _ -> false
  )
  | _, _ -> false

let implied_disjoints (fa1:Box.fact) (fa2:Box.fact) =
  match fa1, fa2 with
  | T(t1), T(t2) -> (
    (Term.equal_base t1.subsumed.value t2.subsumed.value) &&
    (
      match t1.subsumer.value, t2.subsumer.value with
      | a, Negation(b) -> Term.equal_base a b 
      | Negation(a), b -> Term.equal_base a b
      | _, _ -> false
    )
  )
  | _, _ -> false