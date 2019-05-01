open Brain;;

let x = Term.make_raw "X" (Variable("X"))
let y = Term.make_raw "Y" (Variable("Y"))
let z = Term.make_raw "Z" (Variable("Z"))

let x_in_y:Box.fact = T({subsumed=x;subsumer=y})
let y_in_z:Box.fact = T({subsumed=y;subsumer=z})
let x_in_z:Box.fact = T({subsumed=x;subsumer=z})


let a = Term.make_base "A"
let b = Term.make_base "B"
let c = Term.make_base "C"

let a_in_b:Box.fact = T({subsumed=a;subsumer=b})
let b_in_c:Box.fact = T({subsumed=b;subsumer=c})


let rul:Mapper.rule = { hFirstTerm=x_in_y;
                        hSecondTerm=y_in_z;
                        thesisTerm=x_in_z;
                        }


let res = Mapper.apply_rule rul a_in_b b_in_c

let unp op =
  match op with
  | None -> a_in_b
  | Some(c) -> c

let res = unp res


let () =
  print_endline "Hello World!";
  print_endline (Box.to_string_fact res)