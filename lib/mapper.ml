

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


(*============================================================================*)

type bindingType = | FromRule
                   | ToRule

(*============================================================================*)            

type binding = | R of rBinding (*role*)
               | B of bBinding (*base*)
               | C of cBinding (*constant*)

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
  

type rule = { hFirstTerm: Box.fact; 
              hSecondTerm: Box.fact;
              thesisTerm: Box.fact;
            }

let is_valid_rule r =
  (Box.has_full_variable_fact r.hFirstTerm) &&
  (Box.has_full_variable_fact r.hSecondTerm) &&
  (Box.has_full_variable_fact r.thesisTerm)

let to_string_rule r =
  Printf.sprintf "R:[(%s) AND (%s) IMPLIES (%s)" 
    (Box.to_string_fact r.hFirstTerm) (Box.to_string_fact r.hSecondTerm)
    (Box.to_string_fact r.thesisTerm)

let rec to_grounded_constant cBindingList cns =
  if not (Term.has_full_variable_constant cns)
  then None
  else (
    let rec mm bL var =
      match bL with
      | [] -> None
      | hd::tl -> (
        if (Term.equal_constant hd.implied var)
        then Some(hd.implier)
        else mm tl var
      )
    in
    match cns with
    | Base(_) -> None
    | Variable(_) -> mm cBindingList cns
  )

let rec to_grounded_role (rBindingList: rBinding list) 
  (rol: Term.role): Term.role option =
  if not (Term.has_full_variable_role rol)
  then None
  else (
    let rec mm (bL: rBinding list) var =
      match bL with
      | [] -> None
      | hd::tl -> (
        if (Term.equal_role hd.implied var)
        then Some(hd.implier)
        else mm tl var
      )
    in
    match rol with
    | Base(_) -> None
    | Variable(_) -> mm rBindingList rol
    | Inverse(r1) -> (
      let res = mm rBindingList r1 in
      match res with
      | None -> None
      | Some(r) -> Some(Inverse(r))
    )
  )

let rec to_grounded_base rBindingList bBindingList bAse =
  if not (Term.has_full_variable_base bAse)
  then None
  else (
    let rec mm (bL: bBinding list) var =
      match bL with
      | [] -> None
      | hd::tl -> (
        if (Term.equal_base hd.implied var)
        then Some(hd.implier)
        else mm tl var
      )
    in
    match bAse with
    | Variable(_) -> mm bBindingList bAse
    | Negation(b1) -> (
      let res = mm bBindingList b1 in
      match res with
      | None -> None
      | Some(r) -> Some(Negation(r))
    )
    | Intersection(b1, b2) -> (
      let res1 = mm bBindingList b1 in
      let res2 = mm bBindingList b2 in
      match res1, res2 with
      | None, _ -> None
      | _, None -> None
      | Some(r1), Some(r2) -> Some(Intersection(r1, r2))
    )
    | Union(b1, b2) -> (
      let res1 = mm bBindingList b1 in
      let res2 = mm bBindingList b2 in
      match res1, res2 with
      | None, _ -> None
      | _, None -> None
      | Some(r1), Some(r2) -> Some(Union(r1, r2))
    )
    | Exists(r1, b1) -> (
      let rol1 = to_grounded_role rBindingList r1 in
      let res1 = mm bBindingList b1 in
      match rol1, res1 with
      | None, _ -> None
      | _, None -> None
      | Some(rr1), Some(bb1) -> Some(Exists(rr1, bb1))
    ) 
    | ForAll(r1, b1) -> (
      let rol1 = to_grounded_role rBindingList r1 in
      let res1 = mm bBindingList b1 in
      match rol1, res1 with
      | None, _ -> None
      | _, None -> None
      | Some(rr1), Some(bb1) -> Some(Exists(rr1, bb1))
    )
    | _ -> None
  )

let generate_fact_from_binding nmd nmr cbList rbList bbList (fa:Box.fact): 
  Box.fact option =
  match fa with
  | T(tf) -> (
    let new_subsumed_raw = to_grounded_base rbList bbList tf.subsumed.value in
    let new_subsumer_raw = to_grounded_base rbList bbList tf.subsumer.value in
    match new_subsumed_raw, new_subsumer_raw with
    | None, _ -> None
    | _, None -> None
    | Some(sd), Some(sr) -> (
      let nsd = Term.make_raw nmd sd in
      let nsr = Term.make_raw nmr sr in
      Some(T({subsumed=nsd; subsumer=nsr})) 
    )
  )
  | A(af) -> (
    match af with
    | Con(cns, cpt) -> (
      let ncs = to_grounded_constant cbList cns in
      let nct = to_grounded_base rbList bbList cpt.value in
      match ncs, nct with 
      | None, _ -> None
      | _, None -> None
      | Some(ns), Some(nt) -> (
        let nnt = Term.make_raw nmd nt in
        Some(A(Con(ns, nnt)))
      )
    )
    | Rol(cs1, cs2, rol) -> (
      let ncs1 = to_grounded_constant cbList cs1 in
      let ncs2 = to_grounded_constant cbList cs2 in
      let nrol = to_grounded_role rbList rol in
      match ncs1, ncs2, nrol with
      | None, _, _ -> None
      | _, None, _ -> None
      | _, _, None -> None
      | Some(c1), Some(c2), Some(r) -> (
        Some(A(Rol(c1, c2, r)))
      )
    )
  )

let apply_rule (rul:rule) (fact1:Box.fact) 
    (fact2:Box.fact) (default:Box.fact): Box.fact option =
  match (rul.hFirstTerm),fact1, rul.hSecondTerm, fact2 with
  | A(rulAfact1), A(fact1Afact), A(rulAfact2),A(fact2Afact) -> (
    match rulAfact1, fact1Afact, rulAfact2, fact2Afact with
    | Con(rcs1,rct1), Con(cs1, ct1), Con(rcs2, rct2), Con(cs2, ct2) -> (
      (*I need to unpack the base concepts*)
      let cL1 = map_to_from_constant cs1 rcs1 in
      let (bv1, bL1, rL1) = map_to_from_base ct1.value rct1.value in
      let cL2 = map_to_from_constant cs2 rcs2 in
      let (bv2, bL2, rL2) = map_to_from_base ct2.value rct2.value in
      
      if not (bv1 && bv2)
      then None
      else (
        let bList = List.concat [bL1; bL2] in
        let rList = List.concat [rL1; rL2] in
        let cList = List.concat [cL1; cL2] in

        let bV = verify_consistency_b_binding bList in
        let rV = verify_consistency_r_binding rList in
        let cV = verify_consistency_c_binding cList in

        if bV && rV && cV 
        then (
          generate_fact_from_binding "" "" cList rList bList rul.thesisTerm
        )
        else None
      )
    )
    | Con(rcs1,rct1), Con(cs1, ct1), Rol(rcs21, rcs22, rrol2), Rol(cs21, cs22, rol2) -> (
      (*unpacking too*)
      let cL1 = map_to_from_constant cs1 rcs1 in
      let cL21 = map_to_from_constant cs21 rcs21 in
      let cL22 = map_to_from_constant cs22 rcs22 in
      let (bv1, bL, rL1) = map_to_from_base ct1.value rct1.value in
      let (rv1, rL2) = map_to_from_role rol2 rrol2 in

      if not (bv1 && rv1) 
      then None
      else (
        let cL = List.concat [cL1; cL21; cL22] in
        let rL = List.concat [rL1; rL2] in

        let bV = verify_consistency_b_binding bL in
        let rV = verify_consistency_r_binding rL in
        let cV = verify_consistency_c_binding cL in

        if bV && rV && cV 
        then (
          generate_fact_from_binding "" "" cL rL bL rul.thesisTerm
        )
        else None
      )
    )
    | Rol(rcs11, rcs12, rrol1), Rol(cs11, cs12, rol1), Con(rcs2, rct2), Con(cs2, ct2) -> (
      (*unpacking too*)
      let cL1 = map_to_from_constant cs2 rcs2 in
      let cL21 = map_to_from_constant cs11 rcs11 in
      let cL22 = map_to_from_constant cs12 rcs12 in
      let (bv1, bL, rL1) = map_to_from_base ct2.value rct2.value in
      let (rv1, rL2) = map_to_from_role rol1 rrol1 in

      if not (bv1 && rv1) 
      then None
      else (
        let cL = List.concat [cL1; cL21; cL22] in
        let rL = List.concat [rL1; rL2] in

        let bV = verify_consistency_b_binding bL in
        let rV = verify_consistency_r_binding rL in
        let cV = verify_consistency_c_binding cL in

        if bV && rV && cV 
        then (
          generate_fact_from_binding "" "" cL rL bL rul.thesisTerm
        )
        else None
      )
    )
    | Rol(rcs11, rcs12, rrol1), Rol(cs11, cs12, rol1), Rol(rcs21, rcs22, rrol2), Rol(cs21, cs22, rol2) -> (
      (*unpacking too*)
      let cL11 = map_to_from_constant cs11 rcs11 in
      let cL12 = map_to_from_constant cs12 rcs12 in
      let (rv1, rL1) = map_to_from_role rol1 rrol1 in

      let cL21 = map_to_from_constant cs21 rcs21 in
      let cL22 = map_to_from_constant cs22 rcs22 in
      let (rv2, rL2) = map_to_from_role rol1 rrol1 in

      if not (rv1 && rv2) 
      then None
      else (
        let cL = List.concat [cL11; cL12; cL21; cL22] in
        let rL = List.concat [rL1; rL2] in

        let rV = verify_consistency_r_binding rL in
        let cV = verify_consistency_c_binding cL in

        if rV && cV 
        then (
          generate_fact_from_binding "" "" cL rL [] rul.thesisTerm
        )
        else None
      )
    )
    | _, _, _, _ -> None
  )
  | T(rulTfact1), T(fact1Tfact), A(rulAfact2),A(fact2Afact) -> (
    match rulAfact2, fact2Afact with
    | Con(rcs2, rct2), Con(cs2, ct2) -> (
      let (dV, dbL, drL) = map_to_from_base fact1Tfact.subsumed.value 
        rulTfact1.subsumed.value in
      let (rV1, rbL, rrL) = map_to_from_base fact1Tfact.subsumer.value
        rulTfact1.subsumer.value in

      let (v1, bL1, rL1) = map_to_from_base ct2.value rct2.value in
      let cL = map_to_from_constant cs2 rcs2 in

      if not (dV && rV1 && v1)
      then None
      else (
        let bL = List.concat [dbL; rbL; bL1] in
        let rL = List.concat [drL; rrL; rL1] in

        let bV = verify_consistency_b_binding bL in
        let rV = verify_consistency_r_binding rL in
        let cV = verify_consistency_c_binding cL in

        if not (bV && rV && cV)
        then None
        else (
          generate_fact_from_binding "" "" cL rL bL rul.thesisTerm
        )
      )
    )
    | Rol(rcs1, rcs2, rrol), Rol(cs1, cs2, rol) -> (
      let (dV, dbL, drL) = map_to_from_base fact1Tfact.subsumed.value 
        rulTfact1.subsumed.value in
      let (rV1, rbL, rrL) = map_to_from_base fact1Tfact.subsumer.value
        rulTfact1.subsumer.value in

      let cL1 = map_to_from_constant cs1 rcs1 in
      let cL2 = map_to_from_constant cs2 rcs2 in
      let (v1, rL1) = map_to_from_role rol rrol in

      if not (dV && rV1 && v1)
      then None
      else (
        let bL = List.concat [dbL; rbL] in
        let rL = List.concat [drL; rrL; rL1] in
        let cL = List.concat [cL1; cL2] in

        let bV = verify_consistency_b_binding bL in
        let rV = verify_consistency_r_binding rL in
        let cV = verify_consistency_c_binding cL in

        if bV && rV && cV
        then (
          generate_fact_from_binding "" "" cL rL bL rul.thesisTerm
        )
        else None
      )
    )
    | _, _ -> None
  )
  | A(rulAfact1), A(fact1Afact), T(rulTfact2),T(fact2Tfact) -> (
    match rulAfact1, fact1Afact with
    | Con(rcs2, rct2), Con(cs2, ct2) -> (
      let (dV, dbL, drL) = map_to_from_base fact2Tfact.subsumed.value 
        rulTfact2.subsumed.value in
      let (rV1, rbL, rrL) = map_to_from_base fact2Tfact.subsumer.value
        rulTfact2.subsumer.value in

      let (v1, bL1, rL1) = map_to_from_base ct2.value rct2.value in
      let cL = map_to_from_constant cs2 rcs2 in

      if not (dV && rV1 && v1)
      then None
      else (
        let bL = List.concat [dbL; rbL; bL1] in
        let rL = List.concat [drL; rrL; rL1] in

        let bV = verify_consistency_b_binding bL in
        let rV = verify_consistency_r_binding rL in
        let cV = verify_consistency_c_binding cL in

        if not (bV && rV && cV)
        then None
        else (
          generate_fact_from_binding "" "" cL rL bL rul.thesisTerm
        )
      )
    )
    | Rol(rcs1, rcs2, rrol), Rol(cs1, cs2, rol) -> (
      let (dV, dbL, drL) = map_to_from_base fact2Tfact.subsumed.value 
        rulTfact2.subsumed.value in
      let (rV1, rbL, rrL) = map_to_from_base fact2Tfact.subsumer.value
        rulTfact2.subsumer.value in

      let cL1 = map_to_from_constant cs1 rcs1 in
      let cL2 = map_to_from_constant cs2 rcs2 in
      let (v1, rL1) = map_to_from_role rol rrol in

      if not (dV && rV1 && v1)
      then None
      else (
        let bL = List.concat [dbL; rbL] in
        let rL = List.concat [drL; rrL; rL1] in
        let cL = List.concat [cL1; cL2] in

        let bV = verify_consistency_b_binding bL in
        let rV = verify_consistency_r_binding rL in
        let cV = verify_consistency_c_binding cL in

        if bV && rV && cV
        then (
          generate_fact_from_binding "" "" cL rL bL rul.thesisTerm
        )
        else None
      )
    )
    | _, _ -> None
  )
  | T(rulTfact1), T(fact1Tfact), T(rulTfact2),T(fact2Tfact) -> (
    let (dV1, dbL1, drL1) = map_to_from_base fact1Tfact.subsumed.value 
      rulTfact1.subsumed.value in
    let (rV1, rbL1, rrL1) = map_to_from_base fact1Tfact.subsumer.value
      rulTfact1.subsumer.value in

    let (dV2, dbL2, drL2) = map_to_from_base fact2Tfact.subsumed.value 
      rulTfact2.subsumed.value in
    let (rV2, rbL2, rrL2) = map_to_from_base fact2Tfact.subsumer.value
      rulTfact2.subsumer.value in
    
    if not (dV1 && rV1 && dV2 && rV2)
    then None
    else (
      let bL = List.concat [dbL1; dbL2; rbL1; rbL2] in
      let rL = List.concat [drL1; drL2; rrL1; rrL2] in
      
      let bV = verify_consistency_b_binding bL in
      let rV = verify_consistency_r_binding rL in

      if bV && rV 
      then (
        generate_fact_from_binding "" "" [] rL bL rul.thesisTerm
      )
      else None
    )
  )
  | _, _, _, _ -> None
