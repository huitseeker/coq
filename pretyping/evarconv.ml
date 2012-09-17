(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Util
open Names
open Term
open Closure
open Reduction
open Reductionops
open Termops
open Environ
open Recordops
open Evarutil
open Libnames
open Evd

type flex_kind_of_term =
  | Rigid of constr
  | PseudoRigid of constr (* approximated as rigid but not necessarily so *)
  | MaybeFlexible of constr (* approx'ed as reducible but not necessarily so *)
  | Flexible of existential

let flex_kind_of_term c l =
  match kind_of_term c with
    | Rel _ | Const _ | Var _ -> MaybeFlexible c
    | Lambda _ when l<>[] -> MaybeFlexible c
    | LetIn _  -> MaybeFlexible c
    | Evar ev -> Flexible ev
    | Lambda _ | Prod _ | Sort _ | Ind _ | Construct _ | CoFix _ -> Rigid c
    | Meta _ | Case _ | Fix _ -> PseudoRigid c
    | Cast _ | App _ -> assert false

let eval_flexible_term ts env c =
  match kind_of_term c with
  | Const c -> 
      if is_transparent_constant ts c
      then constant_opt_value env c
      else None
  | Rel n ->
      (try let (_,v,_) = lookup_rel n env in Option.map (lift n) v
      with Not_found -> None)
  | Var id ->
      (try
	 if is_transparent_variable ts id then
	   let (_,v,_) = lookup_named id env in v 
	 else None 
       with Not_found -> None)
  | LetIn (_,b,_,c) -> Some (subst1 b c)
  | Lambda _ -> Some c
  | _ -> assert false

let evar_apprec ts env evd stack c =
  let sigma =  evd in
  let rec aux s =
    let (t,stack) = whd_betaiota_deltazeta_for_iota_state ts env sigma s in
    match kind_of_term t with
      | Evar (evk,_ as ev) when Evd.is_defined sigma evk ->
	  aux (Evd.existential_value sigma ev, stack)
      | _ -> (t, list_of_stack stack)
  in aux (c, append_stack_list stack empty_stack)

let apprec_nohdbeta ts env evd c =
  match kind_of_term (fst (Reductionops.whd_stack evd c)) with
    | (Case _ | Fix _) -> applist (evar_apprec ts env evd [] c)
    | _ -> c

let position_problem l2r = function
  | CONV -> None
  | CUMUL -> Some l2r

(* [check_conv_record (t1,l1) (t2,l2)] tries to decompose the problem
   (t1 l1) = (t2 l2) into a problem

     l1 = params1@c1::extra_args1
     l2 = us2@extra_args2
     (t1 params1 c1) = (proji params (c xs))
     (t2 us2) = (cstr us)
     extra_args1 = extra_args2

   by finding a record R and an object c := [xs:bs](Build_R params v1..vn)
   with vi = (cstr us), for which we know that the i-th projection proji
   satisfies

      (proji params (c xs)) = (cstr us)

   Rem: such objects, usable for conversion, are defined in the objdef
   table; practically, it amounts to "canonically" equip t2 into a
   object c in structure R (since, if c1 were not an evar, the
   projection would have been reduced) *)

let check_conv_record (t1,l1) (t2,l2) =
  try
    let proji = global_of_constr t1 in
    let canon_s,l2_effective =
      try
	match kind_of_term t2 with
	    Prod (_,a,b) -> (* assert (l2=[]); *)
      	      if dependent (mkRel 1) b then raise Not_found
	      else lookup_canonical_conversion (proji, Prod_cs),[a;pop b]
	  | Sort s ->
	      lookup_canonical_conversion
		(proji, Sort_cs (family_of_sort s)),[]
	  | _ ->
	      let c2 = global_of_constr t2 in
		lookup_canonical_conversion (proji, Const_cs c2),l2
      with Not_found ->
	lookup_canonical_conversion (proji,Default_cs),[]
    in
    let { o_DEF = c; o_INJ=n; o_TABS = bs;
          o_TPARAMS = params; o_TCOMPS = us } = canon_s in
    let params1, c1, extra_args1 =
      match list_chop (List.length params) l1 with
	| params1, c1::extra_args1 -> params1, c1, extra_args1
	| _ -> raise Not_found in
    let us2,extra_args2 = list_chop (List.length us) l2_effective in
    c,bs,(params,params1),(us,us2),(extra_args1,extra_args2),c1,
    (n,applist(t2,l2))
  with Failure _ | Not_found ->
    raise Not_found

(* Precondition: one of the terms of the pb is an uninstantiated evar,
 * possibly applied to arguments. *)

let rec ise_try evd = function
    [] -> assert false
  | [f] -> f evd
  | f1::l ->
      let (evd',b) = f1 evd in
      if b then (evd',b) else ise_try evd l

let ise_and evd l =
  let rec ise_and i = function
      [] -> assert false
    | [f] -> f i
    | f1::l ->
        let (i',b) = f1 i in
        if b then  ise_and i' l else (evd,false) in
  ise_and evd l

let ise_list2 evd f l1 l2 =
  let rec ise_list2 i l1 l2 =
    match l1,l2 with
        [], [] -> (i, true)
      | [x], [y] -> f i x y
      | x::l1, y::l2 ->
          let (i',b) = f i x y in
          if b then ise_list2 i' l1 l2 else (evd,false)
      | _ -> (evd, false) in
  ise_list2 evd l1 l2

let ise_array2 evd f v1 v2 =
  let rec allrec i = function
    | -1 -> (i,true)
    | n ->
        let (i',b) = f i v1.(n) v2.(n) in
        if b then allrec i' (n-1) else (evd,false)
  in
  let lv1 = Array.length v1 in
  if lv1 = Array.length v2 then allrec evd (pred lv1)
  else (evd,false)

let rec evar_conv_x ts env evd pbty term1 term2 =
  let term1 = whd_head_evar evd term1 in
  let term2 = whd_head_evar evd term2 in
  (* Maybe convertible but since reducing can erase evars which [evar_apprec]
     could have found, we do it only if the terms are free of evar.
     Note: incomplete heuristic... *)
  let ground_test =
    if is_ground_term evd term1 && is_ground_term evd term2 then
      if is_trans_fconv pbty ts env evd term1 term2 then
        Some true
      else if is_ground_env evd env then Some false
      else None
    else None in
  match ground_test with
      Some b -> (evd,b)
    | None ->
	(* Until pattern-unification is used consistently, use nohdbeta to not
	   destroy beta-redexes that can be used for 1st-order unification *)
        let term1 = apprec_nohdbeta ts env evd term1 in
        let term2 = apprec_nohdbeta ts env evd term2 in
        if is_undefined_evar evd term1 then
          solve_simple_eqn (evar_conv_x ts) env evd
	    (position_problem true pbty,destEvar term1,term2)
        else if is_undefined_evar evd term2 then
          solve_simple_eqn (evar_conv_x ts) env evd
	    (position_problem false pbty,destEvar term2,term1)
        else
          evar_eqappr_x ts env evd pbty
            (decompose_app term1) (decompose_app term2)

and evar_eqappr_x ts env evd pbty (term1,l1 as appr1) (term2,l2 as appr2) =
  (* Evar must be undefined since we have flushed evars *)
  match (flex_kind_of_term term1 l1, flex_kind_of_term term2 l2) with
    | Flexible (sp1,al1 as ev1), Flexible (sp2,al2 as ev2) ->
	let f1 i =
	  if List.length l1 > List.length l2 then
            let (deb1,rest1) = list_chop (List.length l1-List.length l2) l1 in
            ise_and i
              [(fun i -> solve_simple_eqn (evar_conv_x ts) env i
	        (position_problem false pbty,ev2,applist(term1,deb1)));
              (fun i -> ise_list2 i
                  (fun i -> evar_conv_x ts env i CONV) rest1 l2)]
	  else
	    let (deb2,rest2) = list_chop (List.length l2-List.length l1) l2 in
            ise_and i
              [(fun i -> solve_simple_eqn (evar_conv_x ts) env i
	          (position_problem true pbty,ev1,applist(term2,deb2)));
              (fun i -> ise_list2 i
                  (fun i -> evar_conv_x ts env i CONV) l1 rest2)]
	and f2 i =
          if sp1 = sp2 then
            ise_and i
            [(fun i -> ise_list2 i
                  (fun i -> evar_conv_x ts env i CONV) l1 l2);
             (fun i -> solve_refl (evar_conv_x ts) env i sp1 al1 al2,
                  true)]
          else (i,false)
	in
	ise_try evd [f1; f2]

    | Flexible ev1, MaybeFlexible flex2 ->
	let f1 i =
	  if
	    is_unification_pattern_evar env ev1 l1 (applist appr2) &
	    not (occur_evar (fst ev1) (applist appr2))
	  then
	    (* Miller-Pfenning's patterns unification *)
	    (* Preserve generality (except that CCI has no eta-conversion) *)
	    let t2 = nf_evar evd (applist appr2) in
	    let t2 = solve_pattern_eqn env l1 t2 in
	    solve_simple_eqn (evar_conv_x ts) env evd
	      (position_problem true pbty,ev1,t2)
	  else if
            List.length l1 <= List.length l2
	  then
	    (* Try first-order unification *)
	    (* (heuristic that gives acceptable results in practice) *)
	    let (deb2,rest2) =
              list_chop (List.length l2-List.length l1) l2 in
            ise_and i
              (* First compare extra args for better failure message *)
              [(fun i -> ise_list2 i
                  (fun i -> evar_conv_x ts env i CONV) l1 rest2);
               (fun i -> evar_conv_x ts env i pbty term1 (applist(term2,deb2)))]
          else (i,false)
	and f2 i =
	  match eval_flexible_term ts env flex2 with
	    | Some v2 ->
		evar_eqappr_x ts env i pbty appr1 (evar_apprec ts env i l2 v2)
	    | None -> (i,false)
	in
	ise_try evd [f1; f2]

    | MaybeFlexible flex1, Flexible ev2 ->
	let f1 i =
	  if
	    is_unification_pattern_evar env ev2 l2 (applist appr1) &
	    not (occur_evar (fst ev2) (applist appr1))
	  then
	    (* Miller-Pfenning's patterns unification *)
	    (* Preserve generality (except that CCI has no eta-conversion) *)
	    let t1 = nf_evar evd (applist appr1) in
	    let t1 = solve_pattern_eqn env l2 t1 in
	    solve_simple_eqn (evar_conv_x ts) env evd
	      (position_problem false pbty,ev2,t1)
	  else if
       	    List.length l2 <= List.length l1
	  then
	    (* Try first-order unification *)
	    (* (heuristic that gives acceptable results in practice) *)
            let (deb1,rest1) = list_chop (List.length l1-List.length l2) l1 in
            ise_and i
            (* First compare extra args for better failure message *)
              [(fun i -> ise_list2 i
                  (fun i -> evar_conv_x ts env i CONV) rest1 l2);
               (fun i -> evar_conv_x ts env i pbty (applist(term1,deb1)) term2)]
          else (i,false)
	and f2 i =
	  match eval_flexible_term ts env flex1 with
	    | Some v1 ->
		evar_eqappr_x ts env i pbty (evar_apprec ts env i l1 v1) appr2
	    | None -> (i,false)
	in
	ise_try evd [f1; f2]

    | MaybeFlexible flex1, MaybeFlexible flex2 -> begin
        match kind_of_term flex1, kind_of_term flex2 with
        | LetIn (na,b1,t1,c'1), LetIn (_,b2,_,c'2) ->
        let f1 i =
          ise_and i
	    [(fun i -> evar_conv_x ts env i CONV b1 b2);
	     (fun i ->
	       let b = nf_evar i b1 in
	       let t = nf_evar i t1 in
	       evar_conv_x ts (push_rel (na,Some b,t) env) i pbty c'1 c'2);
	     (fun i -> ise_list2 i (fun i -> evar_conv_x ts env i CONV) l1 l2)]
	and f2 i =
          let appr1 = evar_apprec ts env i l1 (subst1 b1 c'1)
          and appr2 = evar_apprec ts env i l2 (subst1 b2 c'2)
	  in evar_eqappr_x ts env i pbty appr1 appr2
	in
	ise_try evd [f1; f2]

	| _, _ ->
	let f1 i =
	  if eq_constr flex1 flex2 then
	    ise_list2 i (fun i -> evar_conv_x ts env i CONV) l1 l2
	  else
	     (i,false)
	and f2 i =
	  (try conv_record ts env i
             (try check_conv_record appr1 appr2
	      with Not_found -> check_conv_record appr2 appr1)
           with Not_found -> (i,false))
	and f3 i =
          (* heuristic: unfold second argument first, exception made
             if the first argument is a beta-redex (expand a constant
             only if necessary) or the second argument is potentially
             usable as a canonical projection *)
	  if isLambda flex1 or is_open_canonical_projection i appr2
	  then
	    match eval_flexible_term ts env flex1 with
	    | Some v1 ->
		evar_eqappr_x ts env i pbty (evar_apprec ts env i l1 v1) appr2
	    | None ->
		match eval_flexible_term ts env flex2 with
		| Some v2 ->
		    evar_eqappr_x ts env i pbty appr1 (evar_apprec ts env i l2 v2)
		| None -> (i,false)
	  else
	    match eval_flexible_term ts env flex2 with
	    | Some v2 ->
		evar_eqappr_x ts env i pbty appr1 (evar_apprec ts env i l2 v2)
	    | None ->
		match eval_flexible_term ts env flex1 with
		| Some v1 ->
		    evar_eqappr_x ts env i pbty (evar_apprec ts env i l1 v1) appr2
		| None -> (i,false)
	in
	ise_try evd [f1; f2; f3]
      end

    | Rigid c1, Rigid c2 when isLambda c1 & isLambda c2 ->
        let (na,c1,c'1) = destLambda c1 in
        let (_,c2,c'2) = destLambda c2 in
        assert (l1=[] & l2=[]);
        ise_and evd
          [(fun i -> evar_conv_x ts env i CONV c1 c2);
           (fun i ->
	     let c = nf_evar i c1 in
	     evar_conv_x ts (push_rel (na,None,c) env) i CONV c'1 c'2)]

    | Flexible ev1, (Rigid _ | PseudoRigid _) ->
	if
	  is_unification_pattern_evar env ev1 l1 (applist appr2) &
	  not (occur_evar (fst ev1) (applist appr2))
	then
	  (* Miller-Pfenning's pattern unification *)
	  (* Preserve generality thanks to eta-conversion) *)
	  let t2 = nf_evar evd (applist appr2) in
	  let t2 = solve_pattern_eqn env l1 t2 in
	  solve_simple_eqn (evar_conv_x ts) env evd
	    (position_problem true pbty,ev1,t2)
	else
	  (* Postpone the use of an heuristic *)
	  add_conv_pb (pbty,env,applist appr1,applist appr2) evd,
	  true

    | (Rigid _ | PseudoRigid _), Flexible ev2 ->
	if
	  is_unification_pattern_evar env ev2 l2 (applist appr1) &
	  not (occur_evar (fst ev2) (applist appr1))
	then
	  (* Miller-Pfenning's pattern unification *)
	  (* Preserve generality thanks to eta-conversion) *)
	  let t1 = nf_evar evd (applist appr1) in
	  let t1 = solve_pattern_eqn env l2 t1 in
	  solve_simple_eqn (evar_conv_x ts) env evd
	    (position_problem false pbty,ev2,t1)
	else
	  (* Postpone the use of an heuristic *)
	  add_conv_pb (pbty,env,applist appr1,applist appr2) evd,
	  true

    | MaybeFlexible flex1, (Rigid _ | PseudoRigid _) ->
	let f3 i =
	  (try conv_record ts env i (check_conv_record appr1 appr2)
           with Not_found -> (i,false))
	and f4 i =
	  match eval_flexible_term ts env flex1 with
	    | Some v1 ->
		evar_eqappr_x ts env i pbty (evar_apprec ts env i l1 v1) appr2
	    | None -> (i,false)
	in
	ise_try evd [f3; f4]

    | (Rigid _ | PseudoRigid _), MaybeFlexible flex2 ->
	let f3 i =
	  (try conv_record ts env i (check_conv_record appr2 appr1)
           with Not_found -> (i,false))
	and f4 i =
	  match eval_flexible_term ts env flex2 with
	    | Some v2 ->
		evar_eqappr_x ts env i pbty appr1 (evar_apprec ts env i l2 v2)
	    | None -> (i,false)
	in
	ise_try evd [f3; f4]

    (* Eta-expansion *)
    | Rigid c1, _ when isLambda c1 ->
	assert (l1 = []);
	let (na,c1,c'1) = destLambda c1 in
        let c = nf_evar evd c1 in
	let env' = push_rel (na,None,c) env in
        let appr1 = evar_apprec ts env' evd [] c'1 in
	let appr2 = (lift 1 term2, List.map (lift 1) l2 @ [mkRel 1]) in
	evar_eqappr_x ts env' evd CONV appr1 appr2

    | _, Rigid c2 when isLambda c2 ->
	assert (l2 = []);
	let (na,c2,c'2) = destLambda c2 in
        let c = nf_evar evd c2 in
	let env' = push_rel (na,None,c) env in
	let appr1 = (lift 1 term1, List.map (lift 1) l1 @ [mkRel 1]) in
        let appr2 = evar_apprec ts env' evd [] c'2 in
	evar_eqappr_x ts env' evd CONV appr1 appr2

    | Rigid c1, Rigid c2 -> begin
        match kind_of_term c1, kind_of_term c2 with

	| Sort s1, Sort s2 when l1=[] & l2=[] ->
	    (try 
	       let evd' = 
		 if pbty = CONV 
		 then Evd.set_eq_sort evd s1 s2 
		 else Evd.set_leq_sort evd s1 s2 
	       in (evd', true)
	     with Univ.UniverseInconsistency _ -> (evd, false)
	     | _ -> (evd, false))

	| Prod (n,c1,c'1), Prod (_,c2,c'2) when l1=[] & l2=[] ->
            ise_and evd
              [(fun i -> evar_conv_x ts env i CONV c1 c2);
               (fun i ->
 	         let c = nf_evar i c1 in
	         evar_conv_x ts (push_rel (n,None,c) env) i pbty c'1 c'2)]

	| Ind sp1, Ind sp2 ->
	    if eq_ind sp1 sp2 then
              ise_list2 evd (fun i -> evar_conv_x ts env i CONV) l1 l2
            else (evd, false)

	| Construct sp1, Construct sp2 ->
	    if eq_constructor sp1 sp2 then
              ise_list2 evd (fun i -> evar_conv_x ts env i CONV) l1 l2
            else (evd, false)

	| CoFix (i1,(_,tys1,bds1 as recdef1)), CoFix (i2,(_,tys2,bds2)) ->
            if i1=i2  then
              ise_and evd
                [(fun i -> ise_array2 i
                    (fun i -> evar_conv_x ts env i CONV) tys1 tys2);
                 (fun i -> ise_array2 i
		     (fun i -> evar_conv_x ts (push_rec_types recdef1 env) i CONV)
		     bds1 bds2);
                 (fun i -> ise_list2 i
                     (fun i -> evar_conv_x ts env i CONV) l1 l2)]
            else (evd,false)

	| (Ind _ | Construct _ | Sort _ | Prod _ | CoFix _), _ -> (evd,false)
	| _, (Ind _ | Construct _ | Sort _ | Prod _ | CoFix _) -> (evd,false)

	| (App _ | Meta _ | Cast _ | Case _ | Fix _), _ -> assert false
	| (LetIn _ | Rel _ | Var _ | Const _ | Evar _), _ -> assert false
	| (Lambda _), _ -> assert false

      end

    | PseudoRigid c1, PseudoRigid c2 -> begin
        match kind_of_term c1, kind_of_term c2 with

	| Case (_,p1,c1,cl1), Case (_,p2,c2,cl2) ->
            ise_and evd
              [(fun i -> evar_conv_x ts env i CONV p1 p2);
               (fun i -> evar_conv_x ts env i CONV c1 c2);
	       (fun i -> ise_array2 i
                   (fun i -> evar_conv_x ts env i CONV) cl1 cl2);
               (fun i -> ise_list2 i (fun i -> evar_conv_x ts env i CONV) l1 l2)]

	| Fix (li1,(_,tys1,bds1 as recdef1)), Fix (li2,(_,tys2,bds2)) ->
            if li1=li2 then
              ise_and evd
                [(fun i -> ise_array2 i
                    (fun i -> evar_conv_x ts env i CONV) tys1 tys2);
                 (fun i -> ise_array2 i
		     (fun i -> evar_conv_x ts (push_rec_types recdef1 env) i CONV)
		     bds1 bds2);
	         (fun i -> ise_list2 i
                     (fun i -> evar_conv_x ts env i CONV) l1 l2)]
	    else (evd,false)

	| (Meta _ | Case _ | Fix _ | CoFix _),
	  (Meta _ | Case _ | Fix _ | CoFix _) -> (evd,false)

	| (App _ | Ind _ | Construct _ | Sort _ | Prod _), _ -> assert false
	| _, (App _ | Ind _ | Construct _ | Sort _ | Prod _) -> assert false

	| (LetIn _ | Cast _), _ -> assert false
	| _, (LetIn _ | Cast _) -> assert false

	| (Lambda _ | Rel _ | Var _ | Const _ | Evar _), _ -> assert false
	| _, (Lambda _ | Rel _ | Var _ | Const _ | Evar _) -> assert false
      end

    | PseudoRigid _, Rigid _ ->  (evd,false)

    | Rigid _, PseudoRigid _ ->  (evd,false)

and conv_record trs env evd (c,bs,(params,params1),(us,us2),(ts,ts1),c1,(n,t2)) =
  let (evd',ks,_) =
    List.fold_left
      (fun (i,ks,m) b ->
	 if m=n then (i,t2::ks, m-1) else
	 let dloc = (dummy_loc,InternalHole) in
         let (i',ev) = new_evar i env ~src:dloc (substl ks b) in
	 (i', ev :: ks, m - 1))
      (evd,[],List.length bs - 1) bs
  in
  ise_and evd'
    [(fun i ->
       ise_list2 i
         (fun i x1 x -> evar_conv_x trs env i CONV x1 (substl ks x))
         params1 params);
    (fun i ->
      ise_list2 i
        (fun i u1 u -> evar_conv_x trs env i CONV u1 (substl ks u))
        us2 us);
    (fun i -> evar_conv_x trs env i CONV c1 (applist (c,(List.rev ks))));
    (fun i -> ise_list2 i (fun i -> evar_conv_x trs env i CONV) ts ts1)]

(* We assume here |l1| <= |l2| *)

let first_order_unification ts env evd (ev1,l1) (term2,l2) =
  let (deb2,rest2) = list_chop (List.length l2-List.length l1) l2 in
  ise_and evd
    (* First compare extra args for better failure message *)
    [(fun i -> ise_list2 i (fun i -> evar_conv_x ts env i CONV) rest2 l1);
    (fun i ->
      (* Then instantiate evar unless already done by unifying args *)
      let t2 = applist(term2,deb2) in
      if is_defined_evar i ev1 then
	evar_conv_x ts env i CONV t2 (mkEvar ev1)
      else
	solve_simple_eqn ~choose:true (evar_conv_x ts) env i (None,ev1,t2))]

let choose_less_dependent_instance evk evd term args =
  let evi = Evd.find_undefined evd evk in
  let subst = make_pure_subst evi args in
  let subst' = List.filter (fun (id,c) -> c = term) subst in
  if subst' = [] then error "Too complex unification problem." else
  Evd.define evk (mkVar (fst (List.hd subst'))) evd

let apply_conversion_problem_heuristic ts env evd pbty t1 t2 =
  let t1 = apprec_nohdbeta ts env evd (whd_head_evar evd t1) in
  let t2 = apprec_nohdbeta ts env evd (whd_head_evar evd t2) in
  let (term1,l1 as appr1) = decompose_app t1 in
  let (term2,l2 as appr2) = decompose_app t2 in
  match kind_of_term term1, kind_of_term term2 with
  | Evar (evk1,args1), (Rel _|Var _) when l1 = [] & l2 = []
      & array_for_all (fun a -> a = term2 or isEvar a) args1 ->
      (* The typical kind of constraint coming from pattern-matching return
         type inference *)
      choose_less_dependent_instance evk1 evd term2 args1, true
  | (Rel _|Var _), Evar (evk2,args2) when l1 = [] & l2 = []
      & array_for_all (fun a -> a = term1 or isEvar a) args2 ->
      (* The typical kind of constraint coming from pattern-matching return
         type inference *)
      choose_less_dependent_instance evk2 evd term1 args2, true
  | Evar ev1,_ when List.length l1 <= List.length l2 ->
      (* On "?n t1 .. tn = u u1 .. u(n+p)", try first-order unification *)
      first_order_unification ts env evd (ev1,l1) appr2
  | _,Evar ev2 when List.length l2 <= List.length l1 ->
      (* On "u u1 .. u(n+p) = ?n t1 .. tn", try first-order unification *)
      first_order_unification ts env evd (ev2,l2) appr1
  | _ ->
      (* Some head evar have been instantiated, or unknown kind of problem *)
      evar_conv_x ts env evd pbty t1 t2

let consider_remaining_unif_problems ?(ts=full_transparent_state) env evd =
  let (evd,pbs) = extract_all_conv_pbs evd in
  let heuristic_solved_evd = List.fold_left
    (fun evd (pbty,env,t1,t2) ->
      let evd', b = apply_conversion_problem_heuristic ts env evd pbty t1 t2 in
	if b then evd' else Pretype_errors.error_cannot_unify env evd (t1, t2))
    evd pbs in
    Evd.fold_undefined (fun ev ev_info evd' -> match ev_info.evar_source with
			  |_,ImpossibleCase -> 
			     Evd.define ev (j_type (coq_unit_judge ())) evd'
			  |_ -> evd') heuristic_solved_evd heuristic_solved_evd

(* Main entry points *)

let the_conv_x ?(ts=full_transparent_state) env t1 t2 evd =
  match evar_conv_x ts env evd CONV  t1 t2 with
      (evd',true) -> evd'
    | _ -> raise Reduction.NotConvertible

let the_conv_x_leq ?(ts=full_transparent_state) env t1 t2 evd =
  match evar_conv_x ts env evd CUMUL t1 t2 with
      (evd', true) -> evd'
    | _ -> raise Reduction.NotConvertible

let e_conv ?(ts=full_transparent_state) env evd t1 t2 =
  match evar_conv_x ts env !evd CONV t1 t2 with
      (evd',true) -> evd := evd'; true
    | _ -> false

let e_cumul ?(ts=full_transparent_state) env evd t1 t2 =
  match evar_conv_x ts env !evd CUMUL t1 t2 with
      (evd',true) -> evd := evd'; true
    | _ -> false
