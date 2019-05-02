open Brain;;

let x = Term.make_raw "X" (Variable("X"))
let y = Term.make_raw "Y" (Variable("Y"))
let z = Term.make_raw "Z" (Variable("Z"))

let ax:Term.constant = Variable("x")
let ac:Term.constant = Base("a")


let x_in_y:Box.fact = T({subsumed=x;subsumer=y})
let y_in_z:Box.fact = T({subsumed=y;subsumer=z})
let x_in_z:Box.fact = T({subsumed=x;subsumer=z})

let a = Term.make_base "A"
let b = Term.make_base "B"
let c = Term.make_base "C"

let ax_in_x:Box.fact = A(Con(ax,x))
let ac_in_a:Box.fact = A(Con(ac,a))

let ax_in_y:Box.fact = A(Con(ax,y))

let a_in_b:Box.fact = T({subsumed=a;subsumer=b})
let b_in_c:Box.fact = T({subsumed=b;subsumer=c})


let rul:Rule.rule = { hFirstTerm=x_in_y;
                        hSecondTerm=y_in_z;
                        thesisTerm=x_in_z;
                        }

let rul2:Rule.rule = { hFirstTerm=ax_in_x;
                       hSecondTerm=x_in_y;
                       thesisTerm=ax_in_y;
                     }


let res = Rule.apply_rule rul a_in_b b_in_c
let res2 = Rule.apply_rule rul2 ac_in_a a_in_b

let unp op =
  match op with
  | None -> a_in_b
  | Some(c) -> c

let res = unp res
let res2 = unp res2

let () =
  print_endline "Hello World!";
  print_endline (Box.to_string_fact res);
  print_endline (Box.to_string_fact res2)