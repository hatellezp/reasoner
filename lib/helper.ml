(*most of functions here are to work on lists*)

(*returns -1 if the element is not present, the index otherwise, 
 *need a comparing function*)
let element_in_list ele lis equ =
  let rec element_in_list_helper el li eq index =
    match li with
    | [] -> -1
    | hd::tl -> if (eq el hd) 
      then index 
      else (element_in_list_helper el tl eq (index+1))
  in
  element_in_list_helper ele lis equ 0

let list_length li =
  let rec helper l len =
    match l with
    | [] -> len
    | _::tl -> helper tl (len+1)
  in
  helper li 0

let rec pop_i li index default =
  match li with
  | [] -> default
  | hd::tl -> if index==0 then hd else (pop_i tl (index-1) default)

let remove_all_duplicates li eqf =
  let rec helper lis co =
    match co with
    | [] -> []
    | hd::tl -> (
      if ((element_in_list hd lis eqf) <> -1)
      then helper lis tl
      else hd::(helper lis tl)
    )
  in helper li li