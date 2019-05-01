

(*============================================================================*)

type syntaxer = { term_verififier: Term.term -> bool;
                  fact_verifier: Box.fact -> bool;
                  t_box_verifier: Box.tBOX -> bool;
                  a_box_verifier: Box.aBOX -> bool;
}

let verify_syntax_term s t = s.term_verififier t
let verify_syntax_fact s f = s.fact_verifier f
let verify_syntax_t_box s t = s.t_box_verifier t
let verify_syntax_a_box s a = s.a_box_verifier a