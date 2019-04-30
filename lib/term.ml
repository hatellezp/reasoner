(*
   * don't forget to make all your functions tail recursive
*)

open Printf;;

(*============================================================================*)

type role = | Variable of string 
            | Base of string
            | Inverse of role


let rec copy_role r =
  match r with
  | Variable(s) -> Variable(s)
  | Base(s) -> Base(s)
  | Inverse(r1) -> Inverse(copy_role r1)

let depth_role r =
 let rec depth_role_helper r n =
  match r with
  | Variable(_) -> n + 1
  | Base(_) -> n + 1
  | Inverse(r1) -> depth_role_helper r1 (n+1)
  in
  depth_role_helper r 0

let size_role r = depth_role r

let rec equal_role r1 r2 =
  match r1, r2 with
  | Variable(s1), Variable(s2) -> s1 == s2
  | Base(s1), Base(s2) -> s1 == s2
  | Inverse(r11), Inverse(r22) -> equal_role r11 r22
  | _, _ -> false

let rec reduce_role r =
  match r with
  | Inverse(Inverse(r1)) -> r1
  | Inverse(r1) -> reduce_role r1
  | _ -> r

let is_variable_role (r:role): bool =
  match r with
  | Variable(_) -> true
  | _ -> false

let rec has_variable_role (r:role): bool =
  match r with
  | Variable(_) -> true
  | Inverse(r1) -> has_variable_role r1
  | _ -> false

let has_full_variable_role r = has_variable_role r

let rec to_string_role r =
  match r with
  | Variable(s) -> (sprintf "(v:%s)" s)
  | Base(s) -> (sprintf "(%s)" s)
  | Inverse(r1) -> ("-" ^ (to_string_role r1))


  
(*============================================================================*)

type concept_type = | Variable
                    | Top
                    | Bottom
                    | Base
                    | Negation
                    | Intersection
                    | Union
                    | Exists
                    | ForAll

let equal_concept_type ct1 ct2 =
  match ct1, ct2 with
  | Variable, Variable -> true
  | Top, Top -> true
  | Bottom, Bottom -> true
  | Base, Base -> true
  | Negation, Negation -> true
  | Intersection, Intersection -> true
  | Union, Union -> true
  | Exists, Exists -> true
  | ForAll, ForAll -> true
  | _, _ -> false

(*============================================================================*)

type base = | Variable of string
            | Top
            | Bottom
            | Base of string
            | Negation of base
            | Intersection of base * base
            | Union of base * base
            | Exists of  role * base
            | ForAll of role * base

let rec copy_base b =
  match b with
  | Variable(s) -> Variable(s)
  | Top -> Top
  | Bottom -> Bottom
  | Base(s) -> Base(s)
  | Negation(b1) -> Negation(copy_base b1)
  | Intersection(b1, b2) -> Intersection(copy_base b1, copy_base b2)
  | Union(b1, b2) -> Union(copy_base b1, copy_base b2)
  | Exists(r1, b1) -> Exists(copy_role r1, copy_base b1)
  | ForAll(r1, b1) -> ForAll(copy_role r1, copy_base b1)

let rec equal_base b1 b2 =
  match b1, b2 with
  | Variable(s1), Variable(s2) -> s1 == s2
  | Top, Top -> true
  | Bottom, Bottom -> true
  | Base(s1), Base(s2) -> s1 == s2
  | Negation(b11), Negation(b22) -> (equal_base b11 b22)
  | Intersection(b11, b12), Intersection(b21, b22) -> (
      ((equal_base b11 b21) && (equal_base b21 b22)) ||
      ((equal_base b11 b22) && (equal_base b12 b21))
    )
  | Union(b11, b12), Union(b21, b22) -> (
      ((equal_base b11 b21) && (equal_base b21 b22)) ||
      ((equal_base b11 b22) && (equal_base b12 b21))
    )
  | Exists(r1, b11), Exists(r2, b22) -> (
      (equal_role r1 r2) && (equal_base b11 b22)
    )
  | ForAll(r1, b11), ForAll(r2, b22) -> (
      (equal_role r1 r2) && (equal_base b11 b22)
    )
  | _, _ -> false

let recalculate_depth_base b =
  let rec recalculate_depth (b1:base) (n:int): int =
    match b1 with
    | Variable(_) -> n+1
    | Top -> n+1
    | Bottom -> n+1
    | Base(_) -> n+1
    | Negation(b11) -> recalculate_depth b11 (n+1)
    | Intersection(b11, b12) -> (
      max (recalculate_depth b11 (n+1))
      (recalculate_depth b12 (n+1))
    )
    | Union(b11, b12) -> (
      max (recalculate_depth b11 (n+1))
      (recalculate_depth b12 (n+1))
    )
    | Exists(_, b11) -> recalculate_depth b11 (n+1)
    | ForAll(_, b11) -> recalculate_depth b11 (n+1)
  in
  recalculate_depth b 0

let recalculate_size_base b =
  let rec recalculate_size_helper b1 n =
    match b1 with
    | Variable(_) -> n+1
    | Top -> n+1
    | Bottom -> n+1
    | Base(_) -> n+1
    | Negation(b11) -> recalculate_size_helper b11 (n+1)
    | Intersection(b11, b12) -> (
        (*this is an idea to test...*)
        recalculate_size_helper b11 (
          (n+1) +
          (recalculate_size_helper b12 0) (*all values are reagrouped here*)
          )
    )
    |Union(b11, b12) -> (
      (*this is an idea to test...*)
      recalculate_size_helper b11 (
        (n+1) +
        (recalculate_size_helper b12 0) (*all values are reagrouped here*)
        )
    )
    | Exists(_, b11) -> recalculate_size_helper b11 (n+1)
    | ForAll(_, b11) -> recalculate_size_helper b11 (n+1)
    in
    recalculate_size_helper b 0

let rec nnf b =
  match b with
  | Variable(s) -> Variable(s)
  | Top -> Top
  | Bottom -> Bottom
  | Base(s) -> Base(s)
  | Negation b1 -> (
      match b1 with
      | Variable(s) -> Negation(Variable(s))
      | Top -> Bottom
      | Bottom -> Top
      | Base(s) -> Negation(Base(s))
      | Negation(b2) -> nnf b2
      | Intersection(b2, b3) -> Union(nnf b2, nnf b3)
      | Union(b2, b3) -> Intersection(nnf b2, nnf b3)
      | Exists(r, b2) -> (
        let b22 = Negation(b2) in
        ForAll(r, nnf b22)
        )
      | ForAll(r, b2) -> (
        let b22 = Negation(b2) in
        Exists(r, nnf b22)
      )
  )
  | Intersection(b1, b2) -> Intersection(nnf b1, nnf b2)
  | Union(b1, b2) -> Union(nnf b1, nnf b2)
  | Exists(r, b1) -> Exists(r, nnf b1)
  | ForAll(r, b1) -> ForAll(r, nnf b1)

let rec to_string_base b =
  match b with
  | Variable(s) -> (sprintf "[V:%s]" s)
  | Base(s) -> ("[" ^ s ^ "]")
  | Top -> "TOP"
  | Bottom -> "BOTTOM"
  | Negation(b1) -> ("NOT(" ^ (to_string_base b1) ^ ")")
  | Intersection(b1, b2) -> (sprintf "[%s (AND) %s]" (to_string_base b1) 
    (to_string_base b2)
  )
  | Union(b1, b2) -> (sprintf "[%s (OR) %s]" (to_string_base b1) 
    (to_string_base b2)
  )
  | Exists(r1, b1) -> (sprintf "{E}%s.%s" (to_string_role r1) 
    (to_string_base b1)
  )
  | ForAll(r1, b1) -> (sprintf "{A}%s.%s" (to_string_role r1)
    (to_string_base b1)
  )

  (*I suppose that at this point the concepts are in negation normal form*)
  let rec reduce_base b =
    match b with
    | Variable(s) -> Variable(s)
    | Top -> Top
    | Bottom -> Bottom
    | Base(s) -> Base(s)
    | Negation(b1) -> (
      match b1 with
      | Top -> Bottom
      | Bottom -> Top
      | _ -> b
    )
    | Intersection(b1, b2) -> (
      let rd1 = reduce_base b1 in
      let rd2 = reduce_base b2 in
      if (equal_base rd1 rd2) then b else
      match rd1, rd2 with
      | Top, _ -> rd2
      | _, Top -> rd1
      | Bottom, _ -> Bottom
      | _, Bottom -> Bottom
      | _, _ -> Intersection(rd1, rd2)
    )
    | Union(b1, b2) -> (
      let rd1 = reduce_base b1 in
      let rd2 = reduce_base b2 in
      if (equal_base rd1 rd2) then b else
      match rd1, rd2 with
      | Top, _ -> Top
      | _, Top -> Top
      | Bottom, _ -> rd2
      | _, Bottom -> rd1
      | _, _ -> Union(rd1, rd2)
    )
    | Exists(r1, b1) -> ( (*after I need to add cases where 
                           *r being inverse matters*)
      match b1 with
      | Bottom -> Bottom
      | _ -> (
        let rd1 = reduce_base b1 in
        if (equal_base rd1 Bottom) then Bottom
        else Exists(r1, rd1)
      )
    )
    | ForAll(r1, b1) -> (
      match b1 with
      | Top -> Top
      | _ -> (
        let rd1 = reduce_base b1 in
        if (equal_base rd1 Top) then Top
        else ForAll(r1, rd1)
      )
    )

let nnf_and_reduce b =
  let b1 = nnf b in
  reduce_base b1


let rec generate_all_subbases b =
  match b with
  | Variable(s) -> Variable(s)::[]
  | Top -> Top::[]
  | Bottom -> Bottom::[]
  | Base(_) -> b::[]
  | Negation(b1) -> b::(generate_all_subbases b1)
  | Intersection(b11, b12) -> (
    let l1 = generate_all_subbases b11 in
    let l2 = generate_all_subbases b12 in
    b::(List.concat [l1;l2])
  )
  | Union(b11, b12) -> (
    let l1 = generate_all_subbases b11 in
    let l2 = generate_all_subbases b12 in
    b::(List.concat [l1;l2])
  )
  | Exists(_, b1) -> b::(generate_all_subbases b1)
  | ForAll(_, b1) -> b::(generate_all_subbases b1)


(*Now the hard part, implement if we can map a concept to another*)
(*This idea is not optimal at all*)
let is_sub_base sub super =
  let bag_of_concepts = generate_all_subbases super in
  Helper.element_in_list sub bag_of_concepts equal_base
  (*I choose to not open Helper at the top, this way I cant track what comes 
   * frome where.
   *)

let rec has_variable_base b =
  match b with
  | Variable(_) -> true
  | Negation(b1) -> has_variable_base b1
  | Intersection(b1, b2) -> (has_variable_base b1) || (has_variable_base b2)
  | Union(b1, b2) -> (has_variable_base b1) || (has_variable_base b2)
  | Exists(_, b1) -> has_variable_base b1
  | ForAll(_, b1) -> has_variable_base b1
  | _ -> false

let is_variable_base (b:base) =
  match b with
  | Variable(_) -> true
  | _ -> false

let rec has_full_variable_base b =
  match b with
  | Variable(_) -> true
  | Negation(b1) -> has_full_variable_base b1
  | Intersection(b1, b2) -> (has_full_variable_base b1) && 
    (has_full_variable_base b2)
  | Union(b1, b2) -> (has_full_variable_base b1) && (has_full_variable_base b2)
  | Exists(r1, b1) -> (has_full_variable_base b1) && (has_full_variable_role r1)
  | ForAll(r1, b1) -> (has_full_variable_base b1) && (has_full_variable_role r1)
  | _ -> false

let type_base (b:base):concept_type =
  match b with
  | Variable(_) -> Variable
  | Top -> Top
  | Bottom -> Bottom
  | Base(_) -> Base
  | Negation(_) -> Negation
  | Intersection(_, _) -> Intersection
  | Union(_, _) -> Union
  | Exists(_, _) -> Exists
  | ForAll(_, _) -> ForAll

(*============================================================================*)

(*I think all concepts should be made in nnf from the beginning*)

type concept = {name: string;
                  size: int;
                  depth: int;
                  typ: concept_type;
                  value: base
                 }

let equal_concept c1 c2 =
  (c1.name == c2.name) && (c1.size == c2.size) && (c1.depth == c2.depth) &&
  (equal_concept_type c1.typ c2.typ) && (equal_base c1.value c2.value)

let to_string_concept c = c.name

let has_full_variable_concept c = has_full_variable_base c.value

let make_raw (n:string) (b:base) =
  let b1 = nnf_and_reduce b in
  let dep = recalculate_depth_base b1 in
  let siz = recalculate_size_base b1 in
  let t = type_base b in
  {name=n; depth=dep; size=siz; typ=t; value=b1}

(*I need to incorporate nnf_and_reduce in all constructors*)

let make_variable n = { name=n;
                        size=1;
                        depth=1;
                        typ=Variable;
                        value=Variable(n)
                      }

let make_top = {name="TOP";
                size=1;
                depth=1;
                typ=Top;
                value=Top;
                }

let make_bottom = {name="BOTTOM";
                   size=1;
                   depth=1;
                   typ=Bottom;
                   value=Bottom;
                  }

let make_base n = {name=n;
                   size=1;
                   depth=1;
                   typ=Base;
                   value=Base(n)
                  }

let make_negation n b = {name=n;
                         size=b.size+1;
                         depth=b.depth+1;
                         typ=Negation;
                         value=Negation(b.value)
                        }

let make_intersection n b1 b2 = {name=n;
                                 size = b1.size + b2.size + 1;
                                 depth = (max b1.depth b2.depth) + 1;
                                 typ=Intersection;
                                 value=Intersection(b1.value, b2.value)
                                }
;;

(*============================================================================*)

type constant = | Variable of string
                | Base of string

let equal_constant (c1:constant) (c2:constant): bool =
  match c1, c2 with 
  | Variable(s1), Variable(s2) -> s1==s2
  | Base(s1), Base(s2) -> s1==s2
  | _, _ -> false

let has_full_variable_constant (c:constant): bool =
  match c with
  | Variable(_) -> true
  | _ -> false

let to_string_constant (c:constant): string =
  match c with
  | Variable(s) -> Printf.sprintf "(v:%s)" s
  | Base(s) -> Printf.sprintf "(c:%s)" s
(*============================================================================*)

type term = | Role of role
            | Base of base (*I want this here*)
            | Concept of concept
            | Constant of constant

type termType = | Role
                | Base
                | Concept
                | Constant

let term_type (t:term) =
  match t with
  | Role(_) -> Role
  | Base(_) -> Base
  | Concept(_) -> Concept
  | Constant(_) -> Constant

(*============================================================================*)