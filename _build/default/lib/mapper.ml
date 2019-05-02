

(*============================================================================*)

type bBinding = { implier: Term.base;
                  implied: Term.base
                }

let equal_b_binding bb1 bb2 =
  (Term.equal_base bb1.implier bb2.implier) &&
  (Term.equal_base bb1.implied bb2.implied)

let to_string_b_binding (bb:bBinding):string =
  Printf.sprintf "[bb: (%s) => (%s)]" (Term.to_string_base bb.implier) 
    (Term.to_string_base bb.implied)

let verify_consistency_b_binding bb =
  let rec vf li el =
    match li with
    | [] -> true
    | hd::tl -> (
      if ((Term.equal_base el.implier hd.implier) &&
        not (Term.equal_base el.implied hd.implied))
        ||
        ((Term.equal_base el.implied hd.implied) &&
        not (Term.equal_base el.implier hd.implier))
      then false
      else vf tl el
    )
  in
  let li = List.map (fun el -> vf bb el) bb in (*I prefer two lines*)
  List.fold_left (&&) true li

let is_for_rule_b_binding bb =
  (Term.is_grounded_base bb.implier) &&
  (Term.has_full_variable_base bb.implied)

(*============================================================================*)

type rBinding = { implier: Term.role;
                  implied: Term.role
                }

let equal_r_binding (rb1:rBinding) (rb2:rBinding) =
  (Term.equal_role rb1.implier rb2.implier) &&
  (Term.equal_role rb1.implied rb2.implied)

let to_string_r_binding (bb:rBinding):string =
  Printf.sprintf "[rb: (%s) => (%s)]" (Term.to_string_role bb.implier) 
    (Term.to_string_role bb.implied)

let verify_consistency_r_binding (rb:rBinding list): bool =
  let rec vf li el =
    match li with
    | [] -> true
    | hd::tl -> (
      if ((Term.equal_role el.implier hd.implier) &&
        not (Term.equal_role el.implied hd.implied))
        ||
        ((Term.equal_role el.implied hd.implied) &&
        not (Term.equal_role el.implier hd.implier))
      then false
      else vf tl el
    )
  in
  let li = List.map (fun el -> vf rb el) rb in (*I prefer two lines*)
  List.fold_left (&&) true li

let is_for_rule_r_binding bb =
  (Term.is_grounded_role bb.implier) &&
  (Term.has_full_variable_role bb.implied)

(*============================================================================*)

type cBinding = { implier: Term.constant;
                  implied: Term.constant;
                  }

let equal_c_binding (rb1:cBinding) (rb2:cBinding) =
  (Term.equal_constant rb1.implier rb2.implier) &&
  (Term.equal_constant rb1.implied rb2.implied)

let to_string_c_binding (bb:cBinding):string =
  Printf.sprintf "[cb: (%s) => (%s)]" (Term.to_string_constant bb.implier) 
    (Term.to_string_constant bb.implied)

let verify_consistency_c_binding (cb:cBinding list): bool =
  let rec vf li el =
    match li with
    | [] -> true
    | hd::tl -> (
      if ((Term.equal_constant el.implier hd.implier) &&
        not (Term.equal_constant el.implied hd.implied))
        ||
        ((Term.equal_constant el.implied hd.implied) &&
        not (Term.equal_constant el.implier hd.implier))
      then false
      else vf tl el
    )
  in
  let li = List.map (fun el -> vf cb el) cb in (*I prefer two lines*)
  List.fold_left (&&) true li

let is_for_rule_c_binding bb =
  (Term.is_grounded_constant bb.implier) &&
  (Term.has_full_variable_constant bb.implied)

(*============================================================================*)

type bindingType = | FromRule
                   | ToRule

(*============================================================================*)            

type binding = | R of rBinding (*role*)
               | B of bBinding (*base*)
               | C of cBinding (*constant*)

(* don't know what to do whith this
let type_binding bb =
  match bb with
  | R(r) -> (
    if (Term.has_full_variable_role r.implied)
    then ToRule
    else FromRule
  )
  | B(b) -> (
    if (Term.has_full_variable_base b.implied)
    then ToRule
    else FromRule
  )
  | C(c) -> (
    if (Term.has_full_variable_constant c.implied)
    then ToRule
    else FromRule
  )
*)

let equal_binding b1 b2 =
  match b1, b2 with
  | R(r1), R(r2) -> equal_r_binding r1 r2
  | B(bb1), B(bb2) ->  equal_b_binding bb1 bb2
  | C(c1), C(c2) -> equal_c_binding c1 c2
  | _, _ -> false

let to_string_binding bd =
  match bd with
  | R(rb) -> to_string_r_binding rb
  | B(bb) -> to_string_b_binding bb
  | C(cb) -> to_string_c_binding cb

let same_binding_type bdl =
  let rec verify li ty =
    match li with
    | [] -> true
    | hd::tl -> (
      match hd with
      | R(_) -> (
        if ty=="r" then verify tl ty
        else false
      )
      | B(_) -> (
        if ty=="b" then verify tl ty
        else false
      )
      | C(_) -> (
        if ty=="c" then verify tl ty
        else false
      )
    )
  in
  match bdl with
  | [] -> true
  | hd::tl -> (
    match hd with
    | R(_) -> verify tl "r"
    | B(_) -> verify tl "b"
    | C(_) -> verify tl "c"
  )

  let type_binding bb =
    if not (same_binding_type bb)
    then "n"
    else (
      match bb with
      | [] -> "n"
      | hd::_ -> (
        match hd with
        | R(_) -> "r"
        | B(_) -> "b"
        | C(_) -> "c"
      )
    )

let unpack_binding_c bb default =
  if (same_binding_type bb) && (type_binding bb)=="c"
  then (
    let unp rb =
      match rb with
      | C(e) -> e
      | _ -> default
    in
    List.map unp bb
  )
  else []


let unpack_binding_r bb default =
  if (same_binding_type bb) && (type_binding bb)=="r"
  then (
    let unp rb =
      match rb with
      | R(e) -> e
      | _ -> default
    in
    List.map unp bb
  )
  else []

let unpack_binding_b rb default =
  if (same_binding_type rb) && (type_binding rb)=="b"
  then (
    let unp rr =
      match rr with
      | B(e) -> e
      | _ -> default
    in
    List.map unp rb
  )
  else []

let is_for_rule_binding bb =
  match bb with
  | B(b) -> is_for_rule_b_binding b
  | R(r) -> is_for_rule_r_binding r
  | C(c) -> is_for_rule_c_binding c

(*============================================================================*)

type bindingBag = | Conjunction of (binding list)
                  | Disjunction of (binding list)

let verify_same_type_binding_bag bd =
  match bd with
  | Conjunction(l) -> same_binding_type l
  | Disjunction(l) -> same_binding_type l

let verify_consistency_binding bb =
  match bb with
  | Conjunction(_) -> false (*I don't know what to do for the moment*)
  | Disjunction(l) -> (
    if not (same_binding_type l) then false
    else (
      if (type_binding l)=="r"
      then (
        let default:rBinding = {
          implier:Term.role=Base("DEFAULT");
          implied:Term.role=Variable("DEFAULT");
        }
        in
        verify_consistency_r_binding (unpack_binding_r l default)
        )
      else (
        if (type_binding l)=="b"
        then (
          let default:bBinding = {
            implier:Term.base=Base("DEFAULT");
            implied:Term.base=Variable("DEFAULT");
          }
          in
          verify_consistency_b_binding (unpack_binding_b l default)
        )
        else (
          if (type_binding l)=="c"
          then (
            let defaul:cBinding = {
              implier:Term.constant=Base("DEFAULT");
              implied:Term.constant=Variable("DEFAULT");
            }
            in
            verify_consistency_c_binding (unpack_binding_c l defaul) 
          )
          else false
        )
      )
    )
  )

let is_for_rule_binding_bag bb =
  let mm bl =
    List.fold_left (&&) true (List.map is_for_rule_binding bl)
  in
  match bb with
  | Conjunction(l) -> mm l
  | Disjunction(l) -> mm l
  
let to_string_binding_bag bb =
  let rec lbbs binb str value =
    if value && (Helper.list_length binb) == 0 then (Printf.sprintf "%s]" str)
    else (
      match binb with
      | [] -> Printf.sprintf "\n%s,\n]" str
      | hd::tl -> lbbs tl 
        (Printf.sprintf "%s\n%s," str (to_string_binding hd)) false
    )
  in
  match bb with
  | Conjunction(r) -> lbbs r "Conjunction:[" true
  | Disjunction(b) -> lbbs b "Disjunction:[" true

(*============================================================================*)

(*This function takes two Term.base values and generates a set of binding to map
 *one to another*)

let map_to_from_constant cF cT =
  let cb:cBinding = {implier=cF; implied=cT} in
  cb::[]
  
let map_to_from_role rF rT =
  let rec mapp (rFrom:Term.role) (rTo:Term.role) rList value =
    if not (Term.has_full_variable_role rT) then (value && false, rList)
    else (
      match rTo with
      | Variable(_) -> (
        let rb:rBinding = { implier=rFrom; implied=rTo} in
        (value && true, rb::rList)
      )
      | Inverse(rT1) -> (
        match rFrom with
        | Inverse(rF1) -> mapp rF1 rT1 rList value
        | _ -> (value && false, rList)
      )
      | _ -> (value && false, rList)
    )
  in
  mapp rF rT [] true


let map_to_from_base bF bT =
  let rec mapp bFrom bTo bList rList value =
    if not (Term.has_full_variable_base bTo) then (false && value, bList, rList)
    else (
      match bTo with
      | Variable(_) -> ( 
        let res:bBinding = {implier=bFrom; implied=bTo} in
        (true && value, res::bList, rList)
      )
      | Negation(bTo1) -> (
        match bFrom with
        | Negation(bFrom1) -> (mapp bFrom1 bTo1 bList rList true)
        | _ -> (false && value, bList, rList)
      )
      | Intersection(bTo1, bTo2) -> (
        match bFrom with
        | Intersection(bFrom1, bFrom2) -> (
          let (v1, l1, r1) = mapp bFrom1 bTo1 bList rList value in
          let (v2, l2, r2) = mapp bFrom2 bTo2 bList rList value in
          let v = v1 && v2 && value in
          let newLi = Helper.remove_all_duplicates (List.concat [l1; l2]) 
            equal_b_binding  
          in
          let newRi = Helper.remove_all_duplicates (List.concat [r1; r2]) 
            equal_r_binding  
          in
          (v, newLi, newRi) 
        )
        | _ -> (false && value, bList, rList)
      )
      | Union(bTo1, bTo2) -> (
        match bFrom with
        | Union(bFrom1, bFrom2) -> (
          let (v1, l1, r1) = mapp bFrom1 bTo1 bList rList value in
          let (v2, l2, r2) = mapp bFrom2 bTo2 bList rList value in
          let v = v1 && v2 && value in
          let newLi = Helper.remove_all_duplicates (List.concat [l1; l2]) 
            equal_b_binding  
          in
          let newRi = Helper.remove_all_duplicates (List.concat [r1; r2]) 
            equal_r_binding  
          in
          (v, newLi, newRi)           
        )
        | _ -> (false && value, bList, rList)
      )
      | Exists(rT1, bT1) -> (
        match bFrom with
        | Exists(rF1, bF1) -> (
          let (rValue, rL) = map_to_from_role rF1 rT1 in
          mapp bF1 bT1 bList (List.concat [rL;rList]) (true && rValue && value)
        )
        | _ -> (false && value, bList, rList)
      )
      | ForAll(rT1, bT1) -> (
        match bFrom with
        | ForAll(rF1, bF1) -> (
          let (rValue, rL) = map_to_from_role rF1 rT1 in
          mapp bF1 bT1 bList (List.concat [rL;rList]) (true && rValue && value)
        )
        | _ -> (false && value, bList, rList)
      )
      | _ -> (false && value, bList, rList)
    )
  in
  mapp bF bT [] [] true

(*============================================================================*)