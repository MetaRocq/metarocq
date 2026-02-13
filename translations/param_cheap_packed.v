(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All Checker.
From MetaRocq.Translations Require Import translation_utils sigma.

Import MRMonadNotation.
Local Existing Instance config.default_checker_flags.
Local Existing Instance default_fuel.


Definition refresh_universe u :=
  if Universe.is_level u then u else fresh_universe.

Definition refresh_sort_universe := Sort.map refresh_universe.

Fixpoint refresh_universes (t : term) {struct t} :=
  match t with
  | tSort s => tSort (refresh_sort_universe s)
  | tProd na b t => tProd na b (refresh_universes t)
  | tLetIn na b t' t => tLetIn na b t' (refresh_universes t)
  | _ => t
  end.


Reserved Notation "'tsl_ty_param'".

Fixpoint tsl_rec1 (n : nat) (t : term) {struct t} : term :=
  match t with
  | tRel k => if ge_dec k n then proj1 t else t
  | tEvar k ts => tEvar k (List.map (tsl_rec1 n) ts)
  | tCast t c a => tCast (tsl_rec1 n t) c (tsl_rec1 n a)
  | tProd x A B => tProd x (tsl_rec1 n A) (tsl_rec1 (n+1) B)
  | tLambda x A t => tLambda x (tsl_rec1 n A) (tsl_rec1 (n+1) t)
  | tLetIn x a t u => tLetIn x (tsl_rec1 n a) (tsl_rec1 n t) (tsl_rec1 (n+1) u)
  | tApp t lu => tApp (tsl_rec1 n t) (List.map (tsl_rec1 n) lu)
  | tCase ik t u brs => tCase ik
      (map_predicate_k id tsl_rec1 n t) (tsl_rec1 n u)
      (map_branches_k tsl_rec1 n brs)
  | tProj p t => tProj p (tsl_rec1 n t)
  (* | tFix : mfixpoint term -> nat -> term *)
  (* | tCoFix : mfixpoint term -> nat -> term *)
  | _ => t
  end.


Fixpoint tsl_rec2 (fuel : nat) (Σ : global_env) (G : universe_model) (E : tsl_table) (Γ : context) (t : term) {struct fuel}
  : tsl_result term :=
  match fuel with
  | O => raise translation_utils.NotEnoughFuel
  | S fuel =>
  match t with
  | tRel n => ret (proj2 (tRel n))
  | tSort s => ret (tLambda (nNamed "A") (tSort s)
                           (tProd nAnon (tRel 0) (tSort s)))
  | tCast t c A => let t1 := tsl_rec1 0 t in
                  t2 <- tsl_rec2 fuel Σ G E Γ t ;;
                  A2 <- tsl_rec2 fuel Σ G E Γ A ;;
                  ret (tCast t2 c (tApp A2 [t1]))
  | tProd n A B => let ΠAB' := tsl_rec1 0 (tProd n A B) in
                  let B1 := tsl_rec1 0 B in
                  A' <- tsl_ty_param fuel Σ G E Γ A ;;
                  B2 <- tsl_rec2 fuel Σ G E (Γ ,, vass n A) B ;;
                  ret (tLambda (nNamed "f") ΠAB'
                               (tProd n (lift 1 0 A')
                                      (tApp (lift 1 1 B2)
                                            [tApp (tRel 1) [proj1 (tRel 0)]])))
  | tLambda n A t => A' <- tsl_ty_param fuel Σ G E Γ A ;;
                    t' <- tsl_rec2 fuel Σ G E (Γ ,, vass n A) t ;;
                    ret (tLambda n A' t')
  | tLetIn n t A u => t' <- tsl_term fuel Σ G E Γ t ;;
                     A' <- tsl_ty_param fuel Σ G E Γ A ;;
                     u' <- tsl_rec2 fuel Σ G E (Γ ,, vdef n t A) u ;;
                     ret (tLetIn n t' A' u')
  | tApp t u => t' <- tsl_rec2 fuel Σ G E Γ t ;;
               u' <- monad_map (tsl_term fuel Σ G E Γ) u ;;
               ret (tApp t' u')
  | tConst _ _ as t
  | tInd _ _ as t
  | tConstruct _ _ _ as t => t' <- tsl_term fuel Σ G E Γ t ;;
                            ret (proj2 t')
  | _ => raise TranslationNotHandeled
  end
  end
with tsl_term  (fuel : nat) (Σ : global_env) (G : universe_model) (E : tsl_table) (Γ : context) (t : term) {struct fuel}
  : tsl_result term :=
  match fuel with
  | O => raise translation_utils.NotEnoughFuel
  | S fuel =>
  match t with
  | tRel n => ret (tRel n)
  | tCast t c A => t' <- tsl_term fuel Σ G E Γ t ;;
                  A' <- tsl_ty_param fuel Σ G E Γ A ;;
                  ret (tCast t' c A')
  | tConst s univs => lookup_tsl_table' E (ConstRef s)
  | tInd i univs => lookup_tsl_table' E (IndRef i)
  | tConstruct i n univs => lookup_tsl_table' E (ConstructRef i n)
  | t => match infer Σ G Γ t with
        | Checked typ => let typ := refresh_universes typ in
                        let t1 := tsl_rec1 0 t in
                        t2 <- tsl_rec2 fuel Σ G E Γ t ;;
                        let typ1 := tsl_rec1 0 typ in
                        typ2 <- tsl_rec2 fuel Σ G E Γ typ ;;
                        ret (pair typ1 typ2 t1 t2)
        | TypeError t => raise (TypingError t)
        end
  end
  end
where "'tsl_ty_param'" := (fun fuel Σ G E Γ t =>
                        let t1 := tsl_rec1 0 t in
                        t2 <- tsl_rec2 fuel Σ G E Γ t ;;
                        ret (pack t1 t2)).




(* replace tRel k by t in u without decreasing tRels of u nor lifting them of t *)
Fixpoint replace t k u {struct u} :=
  match u with
  | tRel n =>
    match Nat.compare k n with
    | Datatypes.Eq => t
    | Datatypes.Gt => tRel n
    | Datatypes.Lt => tRel n
    end
  | tEvar ev args => tEvar ev (List.map (replace t k) args)
  | tLambda na T M => tLambda na (replace t k T) (replace (lift0 1 t) (S k) M)
  | tApp u v => tApp (replace t k u) (List.map (replace t k) v)
  | tProd na A B => tProd na (replace t k A) (replace (lift0 1 t) (S k) B)
  | tCast c kind ty => tCast (replace t k c) kind (replace t k ty)
  | tLetIn na b ty b' => tLetIn na (replace t k b) (replace t k ty) (replace (lift0 1 t) (S k) b')
  | tCase ind p c brs =>
    let p' := map_predicate_k id (replace t) k p in
    let brs' := map_branches_k (replace t) k brs in
    tCase ind p' (replace t k c) brs'
  | tProj p c => tProj p (replace t k c)
  | tFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (replace t k) (replace t k')) mfix in
    tFix mfix' idx
  | tCoFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (replace t k) (replace t k')) mfix in
    tCoFix mfix' idx
  | x => x
  end.

Definition clean_uctx (uctx : ContextSet.t) := (LevelSet.remove Level.lzero (fst uctx), snd uctx).

Definition tsl_mind_body (ΣE : tsl_context) (mp : modpath)
           (kn : kername) (mind : mutual_inductive_body)
  : tsl_result (tsl_table * list mutual_inductive_body).
  refine (
      let Σ := fst (fst ΣE) in
      match push_uctx init_model (clean_uctx (global_ext_uctx (fst ΣE))) with
      | None => raise (TypingError (UnsatisfiableConstraints (snd (global_ext_uctx (fst ΣE)))))
      | Some G =>
        let E := snd ΣE in
        let tsl_ty' := tsl_ty_param fuel Σ G E [] in
        let tsl2' := tsl_rec2 fuel Σ G E [] in
        let kn' : kername := (mp, tsl_ident (snd kn)) in _ end).
  simple refine (let arities := List.map ind_type mind.(ind_bodies) in
                 arities2 <- monad_map tsl2' arities ;;
                 bodies <- _ ;;
                 ret (_, [{| ind_npars := mind.(ind_npars);
                             ind_bodies := bodies ;
                 ind_universes := match mind.(ind_universes) with
                  | Monomorphic_ctx => Monomorphic_ctx
                  | Polymorphic_ctx ctx => Polymorphic_ctx ctx
                 end;
                 ind_variance := mind.(ind_variance) |}])).  (* FIXME always ok? *)
  (* L is [(tInd n, tRel 0); ... ; (tInd 0, tRel n)] *)
  simple refine (let L : list term := _ in _).

  - refine (let n := List.length arities - 1 in
            let L := List.combine arities arities2 in
            List.rev (mapi (fun i '(a,a2) => pair a a2 (tInd (mkInd kn i) []) (tRel (n-i))) L)).

  - (* inductive_body -> tsl_result inductive_body *)
    refine (monad_map_i _ mind.(ind_bodies)).
    intros i ind.
    refine (A <- _ ;; ctors <- _ ;;
            ret {| ind_name := tsl_ident ind.(ind_name);
                   ind_sort := ind.(ind_sort);
                   ind_indices := ind.(ind_indices); (* Not true, should change *)
                   ind_type := A;
                   ind_kelim := ind.(ind_kelim);
                   ind_ctors := ctors;
                   ind_projs := [];
                   ind_relevance := ind.(ind_relevance) |}).  (* TODO *)
    + (* arity  *)
      refine (t2 <- tsl2' ind.(ind_type) ;;
              let i1 := tsl_rec1 0 (tInd (mkInd kn i) []) in
              ret (try_reduce (fst (fst ΣE)) [] fuel (mkApp t2 i1))).
    + (* constructors *)
      refine (monad_map_i _ ind.(ind_ctors)).
      intros k c.
      refine (t2 <- tsl2' c.(cstr_type) ;;
              let t2 := fold_left_i (fun t i u => replace u i t) L t2 in
              let c1 := tsl_rec1 0 (tConstruct (mkInd kn i) k []) in
              match reduce_opt RedFlags.default (fst (fst ΣE)) [] (* for debugging but we could use try_reduce *)
                               fuel (mkApp t2 c1) with
              | Some t' => ret
                {| cstr_name := tsl_ident c.(cstr_name);
                   cstr_type := t';
                   cstr_args := c.(cstr_args); (* Not used by denotation yet *)
                   cstr_indices := c.(cstr_indices);
                   cstr_arity := c.(cstr_arity) |}
              | None => raise TranslationNotHandeled
              end).

  - refine (let L := List.combine mind.(ind_bodies) arities2 in
            fold_left_i (fun E i '(ind,a2) => _ :: _ ++ E) L []).
    + (* ind *)
      refine (IndRef (mkInd kn i), pair ind.(ind_type) a2 (tInd (mkInd kn i) []) (tInd (mkInd kn' i) [])).
    + (* ctors *)
      refine (fold_left_i (fun E k _ => _ :: E) ind.(ind_ctors) []).
      exact (ConstructRef (mkInd kn i) k, tConstruct (mkInd kn' i) k []).
  - exact mind.(ind_finite).
  - (* FIXME don't know what to do *) refine (mind.(ind_params)).
Defined.



#[export] Instance tsl_param : Translation
  := {| tsl_id := tsl_ident ;
        tsl_tm := fun ΣE t =>
      match push_uctx init_model (global_ext_uctx (fst ΣE)) with
      | None => raise (TypingError (UnsatisfiableConstraints (snd (global_ext_uctx (fst ΣE)))))
      | Some M => tsl_term fuel (fst (fst ΣE)) M (snd ΣE) [] t
      end;
        tsl_ty := Some (fun ΣE t =>
      match push_uctx init_model (global_ext_uctx (fst ΣE)) with
      | None => raise (TypingError (UnsatisfiableConstraints (snd (global_ext_uctx (fst ΣE)))))
      | Some M => tsl_ty_param fuel (fst (fst ΣE)) M (snd ΣE) [] t
      end);
        tsl_ind := tsl_mind_body |}.



Notation "'TYPE'" := (sigma Type (fun A => A -> Type)).
Notation "'El' A" := (sigma (π1 A) (π2 A)) (at level 20).

Definition ty := nat -> nat.
Definition to := Type.

MetaRocq Run (Translate emptyTC "nat" >>= tmDebug).

Require Vector.

Unset Universe Checking.
MetaRocq Run (Translate emptyTC "list" >>= tmDebug).
Check (listᵗ : forall (A : TYPE), list A.1 -> Type).
Check (nilᵗ : forall (A : TYPE), listᵗ A nil).
Check (consᵗ : forall (A : TYPE) (x : El A) (lH : ∃ l, listᵗ A l),
          listᵗ A (x.1 :: lH.1)).

(* Fixpoint recompose_prod (ns : list name) (As : list term) (B : term) : term := *)
(*   match (ns, As) with *)
(*   | (n :: ns, A :: As)  => tProd n A (recompose_prod ns As B) *)
(*   | _ => B *)
(*   end. *)

(* (* Definition pair_map {A A' B B'} (f : A -> A') (g : B -> B') *) *)
(* (*   : A * B -> A' * B' *) *)
(* (*   := fun w => (f (fst w), g (snd w)). *) *)

(* Fixpoint from_n {A} (f : nat -> A) (n : nat) : list A := *)
(*   match n with *)
(*   | O => [] *)
(*   | S n => f n :: (from_n f n) *)
(*   end. *)



(* Definition mkImpl (A B : term) : term := *)
(*   tProd nAnon A B. *)

(* (* Definition local_entry_map (f : term -> term) (m : local_entry) : local_entry *) *)
(* (*   := match m with *) *)
(* (*      | LocalDef t => LocalDef (f t) *) *)
(* (*      | LocalAssum t => LocalAssum (f t) *) *)
(* (*      end. *) *)

(* Definition local_entry_monad_map {M} {H : Monad M} *)
(*            (f : term -> M term) (m : local_entry) : M local_entry *)
(*   := match m with *)
(*      | LocalDef t => t' <- (f t);; ret (LocalDef t') *)
(*      | LocalAssum t => t' <- (f t);; ret (LocalDef t') *)
(*      end. *)

(* Definition mkApp t us := *)
(*   match t with *)
(*   | tApp t1 us1 => tApp t1 (us1 ++ us) *)
(*   | _ => match us with *)
(*         | nil => t *)
(*         | _ => tApp t us *)
(*         end *)
(*   end. *)

(* Definition get_local_entry (l : local_entry) : term := *)
(*   match l with *)
(*   | LocalDef t => t *)
(*   | LocalAssum t => t *)
(*   end. *)

(* Definition recompose_prod' (l : list (ident * local_entry) *)
(*                            (* Xn at the head of the list *)) *)
(*            (b : term) : term. *)
(*   apply List.rev in l. *)
(*   eapply List.split in l. eapply recompose_prod. *)
(*   exact (List.map nNamed (fst l)). *)
(*   exact (List.map get_local_entry (snd l)). *)
(*   exact b. *)
(* Defined. *)

(* Axiom error : forall {A B}, A -> B. *)



(* Definition tsl_mind_entry (ΣE : tsl_context) *)
(*            (id : ident) (mind : mutual_inductive_entry) *)
(*   : tsl_result (tsl_table * list mutual_inductive_entry). *)
(*   refine (let tsl_ty' := tsl_ty_param fuel (fst ΣE) (snd ΣE) [] in _). *)
(*   refine (let tsl2' := tsl_rec2 fuel (fst ΣE) (snd ΣE) [] in _). *)
(*   refine (X <- _ ;; Y <- _ ;; *)
(*           ret (_, [{| mind_entry_record := mind.(mind_entry_record); *)
(*                       mind_entry_finite := mind.(mind_entry_finite); *)
(*                       mind_entry_params := X; *)
(*                       mind_entry_inds := Y; *)
(*                       mind_entry_polymorphic := mind.(mind_entry_polymorphic); *)
(*                       mind_entry_private := mind.(mind_entry_private); *)
(*                    |}])). *)
(*   - (* params *) *)
(*     refine (monad_map _ mind.(mind_entry_params)). *)
(*     refine (fun x => y <- _ ;; ret (fst x, y)). *)
(*     exact (local_entry_monad_map tsl_ty' (snd x)). *)
(*   - (* inds *) *)
(*     simple refine (L <- _ ;; monad_map_i _ mind.(mind_entry_inds)). *)
(*     exact (list term). *)
(*     + (* L *) *)
(*       refine (let L0 := map_i (fun i _ => tRel i) mind.(mind_entry_params) in *)
(*               L1 <- _ ;; *)
(*               ret (L0 ++ L1)). *)
(*       pose (l := List.length mind.(mind_entry_params)). *)
(*       pose (p := List.length mind.(mind_entry_inds)-1). *)
(*       simple refine (monad_map_i _ mind.(mind_entry_inds)). *)
(*       simple refine (fun i _ => let arity_i := _ in *)
(*                              X <- _ ;; *)
(*                              ret (pair arity_i X *)
(*                                   (tInd (mkInd id (p-i)) []) (tRel (l+i)))). *)
(*       refine (let l := (List.nth (p-i) mind.(mind_entry_inds) *)
(*                                               (error "nth 1")) *)
(*               in recompose_prod' mind.(mind_entry_params) *)
(*                                         l.(mind_entry_arity)). *)
(*       refine (tsl2' arity_i). *)
(*     + (* one_inductive_entry -> one_inductive_entry *) *)
(*       intros i ind. *)
(*       refine (X <- _ ;; Y <- _ ;; *)
(*          ret {| mind_entry_typename := tsl_ident (ind.(mind_entry_typename)); *)
(*                 mind_entry_arity := X; *)
(*                 mind_entry_template := ind.(mind_entry_template); *)
(*                 mind_entry_consnames := List.map tsl_ident *)
(*                                                  ind.(mind_entry_consnames); *)
(*                 mind_entry_lc := Y; *)
(*                     |}). *)
(*       * (* arity  *) *)
(*         refine (t1 <- _ ;; ret (mkApp t1 [_])). *)
(*         exact (tsl2' ind.(mind_entry_arity)). *)
(*         refine (mkApp (tInd (mkInd id i) []) _). *)
(*         refine (from_n (fun n => proj1 (tRel n)) *)
(*                        (List.length mind.(mind_entry_params))). *)
(*       * (* constructors *) *)
(*         refine (monad_map_i _ ind.(mind_entry_lc)). *)
(*         intros k t. *)
(*         refine (t1 <- _ ;; ret (mkApp t1 [_])). *)
(*         refine (t' <- tsl2' t ;; *)
(*                 ret (fold_left_i (fun t i u => replace u i t) L t')). *)
(*         refine (mkApp (tConstruct (mkInd id i) k []) _). *)
(*         refine (from_n (fun n => proj1 (tRel n)) *)
(*                        (List.length mind.(mind_entry_params))). *)
(*   - refine (let id' := tsl_ident id in (* should be kn ? *) *)
(*             fold_left_i (fun E i ind => _ :: _ ++ E) mind.(mind_entry_inds) []). *)
(*     + (* ind *) *)
(*       refine (IndRef (mkInd id i), tInd (mkInd id' i) []). (* should be the pair *) *)
(*     + (* ctors *) *)
(*       refine (fold_left_i (fun E k ctor => _ :: E) ind.(mind_entry_consnames) []). *)
(*       exact (ConstructRef (mkInd id i) k, tConstruct (mkInd id' i) k []). *)
(* Defined. *)








(* Notation "'tΣ'" := (tInd (mkInd "Template.sigma.sigma" 0)). *)
(* Notation "'tproj1'" := (tProj (mkInd "Template.sigma.sigma" 0, 2, 0)). *)
(* Notation "'tImpl'" := (tProd nAnon). *)



(* (* Definition tsl_inductive (ind : inductive) : inductive. *) *)
(*   (* destruct ind. exact (mkInd (tsl_ident k) n). *) *)
(* (* Defined. *) *)


(* Definition tat := Type -> Type. *)

(* MetaRocq Run (tTranslate tsl_param ([],[]) "tat" *)
(*                                         >>= tmPrint). *)
(* About tatᵗ. *)

(* MetaRocq Run (tImplement tsl_param ([], []) "tu" (Type -> Type) >>= tmPrint). *)
(* Next Obligation. *)
(*   exists id. exact (fun _ _ => True). *)
(* Defined. *)
(* About tuᵗ. *)


(* Definition nat_entryT := Eval vm_compute in match tsl_mind_entry ([], []) "Stdlib.Init.Datatypes.nat" nat_entry with | Success (_, [e]) => e | _ => todo end. *)
(* MetaRocq Unquote Inductive nat_entryT. *)
(* Check (natᵗ : nat -> Set). *)
(* Check (Oᵗ : natᵗ O). *)
(* Check (Sᵗ : forall (N : exists n, natᵗ n), natᵗ (S N.1)). *)

(* MetaRocq Quote Recursively Definition bool_prog := bool. *)
(* Definition bool_entry := Eval compute in *)
(*       (mind_body_to_entry (option_get todo (extract_mind_body_from_program "Stdlib.Init.Datatypes.bool" bool_prog) )). *)
(* Definition bool_entryT := Eval vm_compute in match tsl_mind_entry ([], []) "Stdlib.Init.Datatypes.bool" bool_entry with | Success (_, [e]) => e | _ => todo end. *)
(* MetaRocq Unquote Inductive bool_entryT. *)


(* (* Inductive t (A : Set) : nat -> Set := *) *)
(* (*   vnil : t A 0 | vcons : A -> forall n : nat, t A n -> t A (S n). *) *)
(* (* MetaRocq Quote Recursively Definition vect_prog := t. *) *)
(* (* Definition vect_decl := Eval compute in *) *)
(* (*       extract_mind_body_from_program "Top.t" vect_prog. *) *)
(* (* Definition vect_entry := Eval compute in *) *)
(* (*       (mind_body_to_entry (option_get todo vect_decl)). *) *)
(* (* (* MetaRocq Quote Definition tnatT := (nat; natᵗ). *) *) *)
(* (* (* MetaRocq Quote Definition tOT := Oᵗ. *) *) *)
(* (* (* MetaRocq Quote Definition tST := Sᵗ. *) *) *)
(* (* Definition vect_entryT := Eval vm_compute in match tsl_mind_entry ([InductiveDecl "Stdlib.Init.Datatypes.nat" nat_decl], [(IndRef (mkInd "Stdlib.Init.Datatypes.nat" 0), tnatT); (ConstructRef (mkInd "Stdlib.Init.Datatypes.nat" 0) O, tOT); (ConstructRef (mkInd "Stdlib.Init.Datatypes.nat" 0) 1, tST)]) "Top.t" vect_entry *) *)
(* (*                                              with | Success (_, [e]) => e | _ => todo end. *) *)
(* (* (* Definition vect_entryT' := . *) *) *)
(* (* MetaRocq Unquote Inductive vect_entryT. *) *)

(* (* (* Require Vectors.VectorDef. *) *) *)
(* (* (* MetaRocq Quote Recursively Definition vect_prog := Vectors.VectorDef.t. *) *) *)
(* (* (* Definition vect_decl := Eval compute in *) *) *)
(* (* (*       extract_mind_body_from_program "Stdlib.Vectors.VectorDef.t" vect_prog. *) *) *)
(* (* (* Definition vect_entry := Eval compute in *) *) *)
(* (* (*       (mind_body_to_entry (option_get todo_coq vect_decl)). *) *) *)
(* (* (* (* MetaRocq Unquote Inductive vect_entry. *) *) *) *)
(* (* (* Definition vect_entryT := Eval vm_compute in tsl_mind_entry [InductiveDecl "Stdlib.Init.Datatypes.nat" nat_decl] [(IndRef (mkInd "Stdlib.Init.Datatypes.nat" 0), tnatT); (ConstructRef (mkInd "Stdlib.Init.Datatypes.nat" 0) O, tOT); (ConstructRef (mkInd "Stdlib.Init.Datatypes.nat" 0) 1, tST)] "Stdlib.Vectors.VectorDef.t" vect_entry. *) *) *)
(* (* (* (* Definition vect_entryT' := . *) *) *) *)
(* (* (* MetaRocq Unquote Inductive vect_entryT. *) *) *)
(* (* Check tᵗ : forall (A : exists A : Set, A -> Set) (N : exists n, natᵗ n), t A.1 N.1 -> Set. *) *)


(* (* Definition eq_entryT := Eval vm_compute in tsl_mind_entry [] [] "Stdlib.Init.Datatypes.eq" eq_entry. *) *)
(* (* Definition eq'_entry := Eval compute in *) *)
(* (*       (mind_body_to_entry (option_get todo_coq eq'_decl)). *) *)
(* (* Definition eq'_entryT := Eval vm_compute in tsl_mind_entry [] [] "Top.eq'" eq'_entry. *) *)
(* (* MetaRocq Unquote Inductive eq'_entryT. *) *)
(* (* Check eq'ᵗ : forall (A : exists A : Set, A -> Set) (x y : El A), eq' A.1 x.1 y.1 -> Prop. *) *)
(* (* Check eq_refl'ᵗ : forall (A : exists A : Set, A -> Set) (x : El A), *) *)
(* (*     eq'ᵗ A x x (eq_refl' A.1 x.1). *) *)

(* (* Inductive list (A : Set) : Set := *) *)
(* (*     nil : list A | cons : A -> list A -> list A. *) *)
(* (* MetaRocq Quote Recursively Definition list_prog := @list. *) *)
(* (* Definition list_entry := Eval compute in  *) *)
(* (*       (mind_body_to_entry *) *)
(* (*          (option_get todo_coq *) *)
(* (*                      (extract_mind_body_from_program "Top.list" list_prog))). *) *)
(* (* Definition list_entryT := Eval vm_compute in tsl_mind_entry [] [] "Top.list" list_entry. *) *)
(* (* MetaRocq Unquote Inductive list_entryT. *) *)
(* (* Check listᵗ : forall (A : exists A : Set, A -> Set), list A.1 -> Type. *) *)
(* (* Check nilᵗ : forall (A : exists A : Set, A -> Set), listᵗ A (nil A.1). *) *)
(* (* Check consᵗ : forall (A : exists A : Set, A -> Set) (X : El A) (L : exists l : list A.1, listᵗ A l), *) *)
(* (*     listᵗ A (cons A.1 X.1 L.1). *) *)


(* (* Require Import Even. *) *)
(* (* MetaRocq Quote Recursively Definition even_prog := even. *) *)
(* (* Definition even_entry := Eval compute in  *) *)
(* (*       (mind_body_to_entry *) *)
(* (*          (option_get todo_coq *) *)
(* (*                      (extract_mind_body_from_program "Stdlib.Arith.Even.even" even_prog) *) *)
(* (*       )). *) *)
(* (* (* MetaRocq Unquote Inductive even_entry. *) *) *)
(* (* (* Inductive even : nat -> Prop := *) *) *)
(* (* (*     even_O : even 0 | even_S : forall n : nat, odd n -> even (S n) *) *) *)
(* (* (*   with odd : nat -> Prop :=  odd_S : forall n : nat, even n -> odd (S n) *) *) *)
(* (* Definition even_entryT := Eval vm_compute in tsl_mind_entry [InductiveDecl "Stdlib.Init.Datatypes.nat" nat_decl] [(IndRef (mkInd "Stdlib.Init.Datatypes.nat" 0), tnatT); (ConstructRef (mkInd "Stdlib.Init.Datatypes.nat" 0) O, tOT); (ConstructRef (mkInd "Stdlib.Init.Datatypes.nat" 0) 1, tST)] "Stdlib.Arith.Even.even" even_entry. *) *)
(* (* MetaRocq Unquote Inductive even_entryT. *) *)
(* (* Check evenᵗ : forall (N : exists n, natᵗ n), even N.1 -> Prop. *) *)
(* (* Check oddᵗ : forall (N : exists n, natᵗ n), odd N.1 -> Prop. *) *)
(* (* Check even_Sᵗ : forall (N : exists n, natᵗ n) (P : exists p, oddᵗ N p), *) *)
(* (*     evenᵗ (S N.1; Sᵗ N) (even_S N.1 P.1). *) *)



(* (* Class TranslationInductive := *) *)
(* (*   { tsl_ind : mutual_inductive_entry -> global_context * tsl_table }. *) *)



(* (* Definition T := forall A B, list A -> list B. *) *)
(* (* Translate T. *) *)
(* (* Compute (El Tᵗ). *) *)

(* (* Lemma parametric_map_preserve_length (f : El Tᵗ) *) *)
(* (*   : forall A B (l : list A), length (f.1 A B l) = length l. *) *)
(* (*   compute in f. *) *)



(* (* Definition eval_in_mutual_inductive_body (rs : reductionStrategy) *) *)
(* (*            (mind : mutual_inductive_body) *) *)
(* (*   : TemplateMonad mutual_inductive_body. *) *)
(* (*   refine (X <- _ ;; *) *)
(* (*          ret {| ind_npars := mind.(ind_npars); *) *)
(* (*                 ind_bodies := X |}). *) *)
(* (*   refine (monad_map _ mind.(ind_bodies)). *) *)
(* (*   intro ind. *) *)
(* (*   refine (typ <- tmEval rs ind.(ind_type) ;; *) *)
(* (*           ctors <- _ ;; *) *)
(* (*           projs <- _ ;; *) *)
(* (*           ret {| ind_name := ind.(ind_name); *) *)
(* (*                 ind_type := typ; *) *)
(* (*                 ind_kelim := ind.(ind_kelim); *) *)
(* (*                 ind_ctors := ctors ; *) *)
(* (*                 ind_projs := projs |}). *) *)
(* (*   - refine (monad_map _ ind.(ind_ctors)). *) *)
(* (*     intros ((name,t),n). *) *)
(* (*     exact (t' <- tmEval rs t ;; ret ((name,t'),n)). *) *)
(* (*   - refine (monad_map _ ind.(ind_projs)). *) *)
(* (*     intros (name,t). *) *)
(* (*     exact (t' <- tmEval rs t ;; ret (name,t')). *) *)
(* (* Defined. *) *)
