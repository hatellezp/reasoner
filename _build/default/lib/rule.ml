
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

let to_grounded_constant cBindingList cns =
if not (Term.has_full_variable_constant cns)
then None
else (
let rec mm (bL:Mapper.cBinding list) var =
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

let rec to_grounded_role (rBindingList: Mapper.rBinding list) 
(rol: Term.role): Term.role option =
if not (Term.has_full_variable_role rol)
then None
else (
let rec mm (bL:Mapper.rBinding list) var =
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
let res = to_grounded_role rBindingList r1 in
match res with
| None -> None
| Some(r) -> Some(Inverse(r))
)
)

let rec to_grounded_base rBindingList bBindingList bAse =
if not (Term.has_full_variable_base bAse)
then None
else (
let rec mm (bL: Mapper.bBinding list) var =
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
let res = to_grounded_base rBindingList bBindingList b1 in
match res with
| None -> None
| Some(r) -> Some(Negation(r))
)
| Intersection(b1, b2) -> (
let res1 = to_grounded_base rBindingList bBindingList b1 in
let res2 = to_grounded_base rBindingList bBindingList b2 in
match res1, res2 with
| None, _ -> None
| _, None -> None
| Some(r1), Some(r2) -> Some(Intersection(r1, r2))
)
| Union(b1, b2) -> (
let res1 = to_grounded_base rBindingList bBindingList b1 in
let res2 = to_grounded_base rBindingList bBindingList b2 in
match res1, res2 with
| None, _ -> None
| _, None -> None
| Some(r1), Some(r2) -> Some(Union(r1, r2))
)
| Exists(r1, b1) -> (
let rol1 = to_grounded_role rBindingList r1 in
let res1 = to_grounded_base rBindingList bBindingList b1 in
match rol1, res1 with
| None, _ -> None
| _, None -> None
| Some(rr1), Some(bb1) -> Some(Exists(rr1, bb1))
) 
| ForAll(r1, b1) -> (
let rol1 = to_grounded_role rBindingList r1 in
let res1 = to_grounded_base rBindingList bBindingList b1 in
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
(fact2:Box.fact): Box.fact option =
match (rul.hFirstTerm),fact1, rul.hSecondTerm, fact2 with
| A(rulAfact1), A(fact1Afact), A(rulAfact2),A(fact2Afact) -> (
match rulAfact1, fact1Afact, rulAfact2, fact2Afact with
| Con(rcs1,rct1), Con(cs1, ct1), Con(rcs2, rct2), Con(cs2, ct2) -> (
(*I need to unpack the base concepts*)
let cL1 = Mapper.map_to_from_constant cs1 rcs1 in
let (bv1, bL1, rL1) = Mapper.map_to_from_base ct1.value rct1.value in
let cL2 = Mapper.map_to_from_constant cs2 rcs2 in
let (bv2, bL2, rL2) = Mapper.map_to_from_base ct2.value rct2.value in

if not (bv1 && bv2)
then None
else (
let bList = List.concat [bL1; bL2] in
let rList = List.concat [rL1; rL2] in
let cList = List.concat [cL1; cL2] in

let bV = Mapper.verify_consistency_b_binding bList in
let rV = Mapper.verify_consistency_r_binding rList in
let cV = Mapper.verify_consistency_c_binding cList in

if bV && rV && cV 
then (
generate_fact_from_binding "" "" cList rList bList rul.thesisTerm
)
else None
)
)
| Con(rcs1,rct1), Con(cs1, ct1), Rol(rcs21, rcs22, rrol2), Rol(cs21, cs22, rol2) -> (
(*unpacking too*)
let cL1 = Mapper.map_to_from_constant cs1 rcs1 in
let cL21 = Mapper.map_to_from_constant cs21 rcs21 in
let cL22 = Mapper.map_to_from_constant cs22 rcs22 in
let (bv1, bL, rL1) = Mapper.map_to_from_base ct1.value rct1.value in
let (rv1, rL2) = Mapper.map_to_from_role rol2 rrol2 in

if not (bv1 && rv1) 
then None
else (
let cL = List.concat [cL1; cL21; cL22] in
let rL = List.concat [rL1; rL2] in

let bV = Mapper.verify_consistency_b_binding bL in
let rV = Mapper.verify_consistency_r_binding rL in
let cV = Mapper.verify_consistency_c_binding cL in

if bV && rV && cV 
then (
generate_fact_from_binding "" "" cL rL bL rul.thesisTerm
)
else None
)
)
| Rol(rcs11, rcs12, rrol1), Rol(cs11, cs12, rol1), Con(rcs2, rct2), Con(cs2, ct2) -> (
(*unpacking too*)
let cL1 = Mapper.map_to_from_constant cs2 rcs2 in
let cL21 = Mapper.map_to_from_constant cs11 rcs11 in
let cL22 = Mapper.map_to_from_constant cs12 rcs12 in
let (bv1, bL, rL1) = Mapper.map_to_from_base ct2.value rct2.value in
let (rv1, rL2) = Mapper.map_to_from_role rol1 rrol1 in

if not (bv1 && rv1) 
then None
else (
let cL = List.concat [cL1; cL21; cL22] in
let rL = List.concat [rL1; rL2] in

let bV = Mapper.verify_consistency_b_binding bL in
let rV = Mapper.verify_consistency_r_binding rL in
let cV = Mapper.verify_consistency_c_binding cL in

if bV && rV && cV 
then (
generate_fact_from_binding "" "" cL rL bL rul.thesisTerm
)
else None
)
)
| Rol(rcs11, rcs12, rrol1), Rol(cs11, cs12, rol1), Rol(rcs21, rcs22, rrol2), Rol(cs21, cs22, rol2) -> (
(*unpacking too*)
let cL11 = Mapper.map_to_from_constant cs11 rcs11 in
let cL12 = Mapper.map_to_from_constant cs12 rcs12 in
let (rv1, rL1) = Mapper.map_to_from_role rol1 rrol1 in

let cL21 = Mapper.map_to_from_constant cs21 rcs21 in
let cL22 = Mapper.map_to_from_constant cs22 rcs22 in
let (rv2, rL2) = Mapper.map_to_from_role rol2 rrol2 in

if not (rv1 && rv2) 
then None
else (
let cL = List.concat [cL11; cL12; cL21; cL22] in
let rL = List.concat [rL1; rL2] in

let rV = Mapper.verify_consistency_r_binding rL in
let cV = Mapper.verify_consistency_c_binding cL in

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
let (dV, dbL, drL) = Mapper.map_to_from_base fact1Tfact.subsumed.value 
rulTfact1.subsumed.value in
let (rV1, rbL, rrL) = Mapper.map_to_from_base fact1Tfact.subsumer.value
rulTfact1.subsumer.value in

let (v1, bL1, rL1) = Mapper.map_to_from_base ct2.value rct2.value in
let cL = Mapper.map_to_from_constant cs2 rcs2 in

if not (dV && rV1 && v1)
then None
else (
let bL = List.concat [dbL; rbL; bL1] in
let rL = List.concat [drL; rrL; rL1] in

let bV = Mapper.verify_consistency_b_binding bL in
let rV = Mapper.verify_consistency_r_binding rL in
let cV = Mapper.verify_consistency_c_binding cL in

if not (bV && rV && cV)
then None
else (
generate_fact_from_binding "" "" cL rL bL rul.thesisTerm
)
)
)
| Rol(rcs1, rcs2, rrol), Rol(cs1, cs2, rol) -> (
let (dV, dbL, drL) = Mapper.map_to_from_base fact1Tfact.subsumed.value 
rulTfact1.subsumed.value in
let (rV1, rbL, rrL) = Mapper.map_to_from_base fact1Tfact.subsumer.value
rulTfact1.subsumer.value in

let cL1 = Mapper.map_to_from_constant cs1 rcs1 in
let cL2 = Mapper.map_to_from_constant cs2 rcs2 in
let (v1, rL1) = Mapper.map_to_from_role rol rrol in

if not (dV && rV1 && v1)
then None
else (
let bL = List.concat [dbL; rbL] in
let rL = List.concat [drL; rrL; rL1] in
let cL = List.concat [cL1; cL2] in

let bV = Mapper.verify_consistency_b_binding bL in
let rV = Mapper.verify_consistency_r_binding rL in
let cV = Mapper.verify_consistency_c_binding cL in

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
let (dV, dbL, drL) = Mapper.map_to_from_base fact2Tfact.subsumed.value 
rulTfact2.subsumed.value in
let (rV1, rbL, rrL) = Mapper.map_to_from_base fact2Tfact.subsumer.value
rulTfact2.subsumer.value in

let (v1, bL1, rL1) = Mapper.map_to_from_base ct2.value rct2.value in
let cL = Mapper.map_to_from_constant cs2 rcs2 in

if not (dV && rV1 && v1)
then None
else (
let bL = List.concat [dbL; rbL; bL1] in
let rL = List.concat [drL; rrL; rL1] in

let bV = Mapper.verify_consistency_b_binding bL in
let rV = Mapper.verify_consistency_r_binding rL in
let cV = Mapper.verify_consistency_c_binding cL in

if not (bV && rV && cV)
then None
else (
generate_fact_from_binding "" "" cL rL bL rul.thesisTerm
)
)
)
| Rol(rcs1, rcs2, rrol), Rol(cs1, cs2, rol) -> (
let (dV, dbL, drL) = Mapper.map_to_from_base fact2Tfact.subsumed.value 
rulTfact2.subsumed.value in
let (rV1, rbL, rrL) = Mapper.map_to_from_base fact2Tfact.subsumer.value
rulTfact2.subsumer.value in

let cL1 = Mapper.map_to_from_constant cs1 rcs1 in
let cL2 = Mapper.map_to_from_constant cs2 rcs2 in
let (v1, rL1) = Mapper.map_to_from_role rol rrol in

if not (dV && rV1 && v1)
then None
else (
let bL = List.concat [dbL; rbL] in
let rL = List.concat [drL; rrL; rL1] in
let cL = List.concat [cL1; cL2] in

let bV = Mapper.verify_consistency_b_binding bL in
let rV = Mapper.verify_consistency_r_binding rL in
let cV = Mapper.verify_consistency_c_binding cL in

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
let (dV1, dbL1, drL1) = Mapper.map_to_from_base fact1Tfact.subsumed.value 
rulTfact1.subsumed.value in
let (rV1, rbL1, rrL1) = Mapper.map_to_from_base fact1Tfact.subsumer.value
rulTfact1.subsumer.value in

let (dV2, dbL2, drL2) = Mapper.map_to_from_base fact2Tfact.subsumed.value 
rulTfact2.subsumed.value in
let (rV2, rbL2, rrL2) = Mapper.map_to_from_base fact2Tfact.subsumer.value
rulTfact2.subsumer.value in

if not (dV1 && rV1 && dV2 && rV2)
then None
else (
let bL = List.concat [dbL1; dbL2; rbL1; rbL2] in
let rL = List.concat [drL1; drL2; rrL1; rrL2] in

let bV = Mapper.verify_consistency_b_binding bL in
let rV = Mapper.verify_consistency_r_binding rL in

if bV && rV 
then (
generate_fact_from_binding "" "" [] rL bL rul.thesisTerm
)
else None
)
)
| _, _, _, _ -> None
