open Brain;;

let x = Term.make_raw "X" (Variable("X"))
let y = Term.make_raw "Y" (Variable("Y"))
let z = Term.make_raw "Z" (Variable("Z"))

let x_in_y:Box.fact = T({subsumed=x;subsumer=y})
let y_in_z:Box.fact = T({subsumed=y;subsumer=z})
let x_in_z:Box.fact = T({subsumed=x;subsumer=z})

let rul:Mapper.rule = { hFirstTerm=x_in_y;
                        hSecondTerm=y_in_z;
                        thesisTerm=x_in_z;
                        }


let () =
  print_endline "Hello World!";
