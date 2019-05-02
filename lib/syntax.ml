

(*============================================================================*)

type syntaxer = { term_verififier: Term.term -> bool;
                  fact_verifier: Box.fact -> bool;
                  t_box_verifier: Box.tBOX -> Box.fact list option;
                  a_box_verifier: Box.aBOX -> Box.fact list option;
                }

let verify_syntax_term s t = s.term_verififier t
let verify_syntax_fact s f = s.fact_verifier f
let verify_syntax_t_box s t = s.t_box_verifier t
let verify_syntax_a_box s a = s.a_box_verifier a


(*============================================================================*)

(*DL-Lite syntax*)

let term_verifier_dl_lite (t:Term.term): bool =
  let vb (b:Term.base): bool =
    match b with
      | Variable(_) -> true
      | Base(_) -> true
      | Negation(Base(_)) -> true
      | Top -> true
      | Bottom -> true
      | Exists(_, Top) -> true
      | _ -> false
  in
  match t with
  | Constant(_) -> true
  | Role(_) -> true
  | Base(b) -> vb b
  | Concept(c) -> vb c.value

let fact_verifier_dl_lite (f:Box.fact): bool =
  match f with
  | T(t) -> (
    let sd:Term.term = Concept(t.subsumed) in
    let sr:Term.term = Concept(t.subsumer) in
    (term_verifier_dl_lite sd) && (term_verifier_dl_lite sr)
  )
  | A(a) -> (
    match a with
    | Con(_, ct) -> (
      let c:Term.term = Concept(ct) in
      term_verifier_dl_lite c
    )
    | Rol(_, _, r) -> (
      let rr:Term.term = Role(r) in
      term_verifier_dl_lite rr
    )
  )

let a_box_verifier_dl_lite ab =
  let pck (af:Box.aFact): Box.fact = A(af) in
  let rec mm li op =
    match li with
    | [] -> (match op with | [] -> None | _::_ -> Some(op))
    | hd::tl -> (
      if not (fact_verifier_dl_lite (pck hd))
      then mm tl (hd::op)
      else mm tl op
    )
  in
  mm ab []


let t_box_verifier_dl_lite tb =
  let pck (tf:Box.tFact): Box.fact = T(tf) in
  let rec mm (li:Box.tFact list) op =
    match li with
    | [] -> (match op with | [] -> None | _::_ -> Some(op))
    | hd::tl -> (
      match hd.subsumed.value with
      | Negation(_) -> mm tl (hd::op)
      | _ -> (
        if not (fact_verifier_dl_lite (pck hd))
        then mm tl (hd::op)
        else mm tl op
      )
    )
  in
  mm tb []

