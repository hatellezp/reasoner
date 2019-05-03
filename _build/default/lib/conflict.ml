

(*============================================================================*)

type conflict = Box.fact -> Box.fact -> bool



let not_empty_bottom (fa1:Box.fact) (fa2:Box.fact) =
  match fa1, fa2 with
  | A(a1), _ -> (

  )
  | _, A(a2) -> false
  | _, _ -> false