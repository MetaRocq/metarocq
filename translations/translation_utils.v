(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.

From MetaRocq.Template Require Import Checker All.
Import MonadNotation.

Set Universe Checking.

(* Should be in AstUtils probably *)
Fixpoint subst_app (t : term) (us : list term) : term :=
  match t, us with
  | tLambda _ A t, u :: us => subst_app (t {0 := u}) us
  | _, [] => t
  | _, _ => mkApps t us
  end.


Definition tsl_table := list (global_reference * term).

Fixpoint lookup_tsl_table (E : tsl_table) (gr : global_reference)
  : option term :=
  match E with
  | nil => None
  | hd :: tl =>
    if gref_eqb gr (fst hd) then Some (snd hd)
    else lookup_tsl_table tl gr
  end.

Definition tsl_context := (global_env_ext * tsl_table)%type.

Definition emptyTC : tsl_context := (empty_ext empty_global_env, []).

Inductive tsl_error :=
| NotEnoughFuel
| TranslationNotFound (gr : global_reference)
| TranslationNotHandeled
| TypingError (t : type_error).

Inductive tsl_result A :=
| Success : A -> tsl_result A
| Error : tsl_error -> tsl_result A.

Arguments Success {_} _.
Arguments Error {_} _.

#[export] Instance tsl_monad : Monad tsl_result :=
  {| ret A a := Success a ;
     bind A B m f :=
       match m with
       | Success a => f a
       | Error e => Error e
       end
  |}.

#[export] Instance monad_exc : MonadExc tsl_error tsl_result :=
  { raise A e := Error e;
    catch A m f :=
      match m with
      | Success a => m
      | Error t => f t
      end
  }.

Definition lookup_tsl_table' E gr :=
  match lookup_tsl_table E gr with
  | Some t => ret t
  | None => raise (TranslationNotFound gr)
  end.




Class Translation :=
  { tsl_id : ident -> ident ;
    tsl_tm : tsl_context -> term -> tsl_result term ;
    tsl_ty : option (tsl_context -> term -> tsl_result term) ;

    (* modpath = ModPath in which the inductive will be declared *)
    tsl_ind : tsl_context -> modpath -> kername -> mutual_inductive_body
              -> tsl_result (tsl_table * list mutual_inductive_body) }.


Definition tsl_ident (id : ident) : ident := (id ^ "ᵗ").

Definition tsl_name0 tsl_ident n :=
  match n with
  | nAnon => nAnon
  | nNamed n => nNamed (tsl_ident n)
  end.

Definition nAnon := {| binder_name := nAnon; binder_relevance := Relevant |}.
Definition nNamed n := {| binder_name := nNamed n; binder_relevance := Relevant |}.

Definition tsl_name f := map_binder_annot (tsl_name0 f).


Definition tmDebug {A} : A -> TemplateMonad unit :=
  fun _ => ret tt.
  (* fun x => tmPrint x ;; ret tt. *)


Definition add_global_decl d (Σ : global_env_ext) : global_env_ext
  := (add_global_decl Σ.1 d, Σ.2).

Definition tmLocateCst (q : qualid) : TemplateMonad kername :=
  l <- tmLocate q ;;
  match l with
  | [] => tmFail ("Constant [" ^ q ^ "] not found")
  | (ConstRef kn) :: _ => tmReturn kn
  | _ :: _ => tmFail ("[" ^ q ^ "] is not a constant")
  end.

Definition monomorph_globref_term (gr : global_reference) : term :=
  match gr with
  | VarRef x => tVar x
  | ConstRef x => tConst x []
  | IndRef x => tInd x []
  | ConstructRef x x0 => tConstruct x x0 []
  end.


Definition Translate {tsl : Translation} (ΣE : tsl_context) (id : ident)
  : TemplateMonad tsl_context :=
  tmDebug ("Translate " ^ id);;
  gr <- tmLocate1 id ;;
  tmDebug gr;;
  match gr with
  | VarRef _ => tmFail "Section variable not supported for the moment"
  | ConstructRef (mkInd kn n) _
  | IndRef (mkInd kn n) =>
    mp <- tmCurrentModPath tt ;;
    d <- tmQuoteInductive kn ;;
    d' <- tmEval lazy (tsl_ind ΣE mp kn d) ;;
    match d' with
    | Error e =>
      print_nf e ;;
      fail_nf ("Translation error during the translation of the inductive " ^ id)
    | Success (E, decls) =>
      monad_iter (fun x => tmDebug x ;; tmMkInductive' x) decls ;;
      let Σ' := add_global_decl (kn,InductiveDecl d) (fst ΣE) in
      let E' := (E ++ snd ΣE) in
      Σ' <- tmEval lazy Σ' ;;
      E' <- tmEval lazy E' ;;
      tmMsg (string_of_kername kn ^ " has been translated.") ;;
      ret (Σ', E')
    end

  | ConstRef kn =>
    e <- tmQuoteConstant kn true ;;
    match e.(cst_body) with
    | None =>
      fail_nf (id ^ " is an axiom, not a definition. Use Implement Existing.")
    | Some t =>
      let A := e.(cst_type) in
      let univs := e.(cst_universes) in
      tmDebug t ;;
      t' <- tmEval lazy (tsl_tm ΣE t) ;;
      tmDebug t' ;;
      match t' with
      | Error e =>
        print_nf e ;;
        fail_nf ("Translation error during the translation of the body of " ^ id)
      | Success t' =>
        id' <- tmEval all (tsl_id id) ;;
        tmDebug "here" ;;
        tmDebug id' ;;
        tmDebug t' ;;
        tmMkDefinition id' t' ;;
        tmDebug "doneu" ;;
        gr' <- tmLocate1 id' ;;
        let decl := {| cst_universes := univs;
                       cst_type := A; cst_body := Some t;
                       cst_relevance := e.(cst_relevance) |} in
        let Σ' := add_global_decl (kn, ConstantDecl decl) (fst ΣE) in
        let E' := (ConstRef kn, monomorph_globref_term gr') :: (snd ΣE) in
        Σ' <- tmEval lazy Σ' ;;
        E' <- tmEval lazy E' ;;
        print_nf (id ^ " has been translated as " ^ id') ;;
        ret (Σ', E')
      end
    end
  end.


Definition Implement {tsl : Translation} (ΣE : tsl_context)
           (id : ident) (A : Type)
  : TemplateMonad (tsl_context) :=
  tA  <- tmQuote A ;;
  match tsl_ty with
  | None => tmFail "No implementation of tsl_ty provided for this translation."
  | Some tsl_ty =>
  tA' <- tmEval lazy (tsl_ty ΣE tA) ;;
  tmDebug tA' ;;
  match tA' with
  | Error e =>
    print_nf e ;;
    tmFail "Translation error during the translation of the type."
  | Success tA' =>
      id' <- tmEval all (tsl_id id) ;;
      tmBind (tmUnquoteTyped Type tA') (fun A' =>
      tmLemma id' A' ;;
      tmAxiom id A ;;
      kn <- tmLocateCst id ;;
      gr' <- tmLocate1 id' ;;
      let decl := {| cst_universes := Monomorphic_ctx;
                     cst_type := tA; cst_body := None;
                     cst_relevance := Relevant |} in
      let Σ' := add_global_decl (kn, ConstantDecl decl) (fst ΣE) in
      let E' := (ConstRef kn, monomorph_globref_term gr') :: (snd ΣE) in
      print_nf (id ^ " has been translated as " ^ id') ;;
      ret (Σ', E'))
  end
  end.


Definition ImplementExisting {tsl : Translation} (ΣE : tsl_context) (id : ident)
  : TemplateMonad tsl_context :=
  gr <- tmLocate1 id ;;
  id' <- tmEval all (tsl_id id) ;;
  mp <- tmCurrentModPath tt ;;
  match tsl_ty with
  | None => tmFail "No implementation of tsl_ty provided for this translation."
  | Some tsl_ty =>
  match gr with
  | VarRef _ => tmFail "Section variable not supported for the moment"
  | ConstRef kn =>
    e <- tmQuoteConstant kn true ;;
    let A := e.(cst_type) in
    tmDebug "plop1" ;;
    ΣE <- tmEval lazy ΣE ;;
    tmDebug ΣE ;;
    tA' <- tmEval lazy (tsl_ty ΣE A) ;;  (* long *)
    tmDebug "plop" ;;
    match tA' with
    | Error e =>
      print_nf e ;;
    fail_nf ("Translation error during the translation of the type of " ^ id)
    | Success tA' =>
      tmDebug "plop2" ;;
      tmBind (tmUnquoteTyped Type tA') (fun A' =>
      tmDebug "plop3" ;;
      tmLemma id' A' ;;
      gr' <- tmLocate1 id' ;;
      let decl := {| cst_universes := Monomorphic_ctx;
                     cst_type := A; cst_body := e.(cst_body);
                     cst_relevance := e.(cst_relevance) |} in
      let Σ' := add_global_decl (kn, ConstantDecl decl) (fst ΣE) in
      let E' := (ConstRef kn, monomorph_globref_term gr') :: (snd ΣE) in
      print_nf (id ^ " has been translated as " ^ id') ;;
      ret (Σ', E'))
    end
  | IndRef (mkInd kn n) =>
    d <- tmQuoteInductive kn ;;
    match List.nth_error (ind_bodies d) n with
      | None => fail_nf ("The declaration of "
                          ^ id ^ " has not enough bodies. This is a bug.")
      | Some {| ind_type := A |} =>
      tA' <- tmEval lazy (tsl_ty ΣE A) ;;
      match tA' with
      | Error e =>
        print_nf e ;;
        fail_nf ("Translation error during the translation of the type of " ^ id)
      | Success tA' =>
        id' <- tmEval all (tsl_id id) ;;
        tmBind (tmUnquoteTyped Type tA') (fun A' =>
        tmLemma id' A' ;;
        gr' <- tmLocate1 id' ;;
        let Σ' := add_global_decl (kn, InductiveDecl d) (fst ΣE) in
        let E' := (IndRef (mkInd kn n), monomorph_globref_term gr') :: (snd ΣE) in
        print_nf (id ^ " has been translated as " ^ id') ;;
        ret (Σ', E'))
      end
    end

  | ConstructRef (mkInd kn n) k =>
    d <- tmQuoteInductive kn ;;
    tmDebug "plop1" ;;
    match List.nth_error (ind_bodies d) n with
    | None => fail_nf ("The declaration of "
                        ^ id ^ " has not enough bodies. This is a bug.")
    | Some {| ind_ctors := ctors |} =>
      tmDebug "plop2" ;;
      match List.nth_error ctors k with
      | None => fail_nf ("The body of "
                          ^ id ^ " has not enough constructors. This is a bug.")
      | Some cstr =>  (* keep id? *)
        tmDebug "plop3" ;;
        let A := subst0 (inds kn [] (* FIXME uctx *) (ind_bodies d)) cstr.(cstr_type) in
        tmDebug "plop4" ;;
        tA' <- tmEval lazy (tsl_ty ΣE A) ;;
        tmDebug "plop5" ;;
        match tA' with
        | Error e =>
          print_nf e ;;
          fail_nf ("Translation error during the translation of the type of " ^ id)
        | Success tA' =>
          tmDebug "plop6" ;;
          id' <- tmEval all (tsl_id id) ;;
          tmBind (tmUnquoteTyped Type tA') (fun A' =>
          tmDebug "plop7" ;;
          tmLemma id' A' ;;
          gr' <- tmLocate1 id' ;;
          let E' := (ConstructRef (mkInd kn n) k, monomorph_globref_term gr') :: (snd ΣE) in
          print_nf (id ^ " has been translated as " ^ id') ;;
          ret (fst ΣE, E'))
        end
      end
    end
  end
  end.

Definition TranslateRec {tsl : Translation} (ΣE : tsl_context) {A} (t : A) :=
  p <- tmQuoteRec t ;;
  tmPrint "~~~~~~~~~~~~~~~~~~" ;;
  monad_fold_right (fun ΣE '(kn, decl) =>
    print_nf ("Translating " ^ string_of_kername kn) ;;
    match decl with
    | ConstantDecl decl =>
      match lookup_tsl_table (snd ΣE) (ConstRef kn) with
      | Some _ => print_nf (string_of_kername kn ^ " was already translated") ;; ret ΣE
      | None =>
        match decl with
        | {| cst_body := None |} =>
          fail_nf (string_of_kername kn ^ " is an axiom. Use Implement Existing.")

        | {| cst_type := A; cst_body := Some t; cst_universes := univs |} =>
          tmDebug "go";;
          t' <- tmEval lazy (tsl_tm ΣE t) ;;
          tmDebug "done";;
          match t' with
          | Error e =>
            print_nf e ;;
            fail_nf ("Translation error during the translation of the body of "
                       ^ string_of_kername kn)
          | Success t' =>
            let id := kn.2 in
            let id' := tsl_ident id in
            tmDebug "here";;
            tmDebug id' ;;
            tmDebug t' ;;
            tmMkDefinition id' t' ;;
            tmDebug "there";;
            gr' <- tmLocate1 id' ;;
            let Σ' := add_global_decl (kn, ConstantDecl decl) (fst ΣE) in
            let E' := (ConstRef kn, monomorph_globref_term gr') :: (snd ΣE) in
            Σ' <- tmEval lazy Σ' ;;
            E' <- tmEval lazy E' ;;
            print_nf  (id ^ " has been translated as " ^ id') ;;
            ret (Σ', E')
          end
        end
      end

    | InductiveDecl d =>
      match lookup_tsl_table (snd ΣE) (IndRef (mkInd kn 0)) with
      | Some _ => print_nf (string_of_kername kn ^ " was already translated") ;; ret ΣE
      | None =>
        tmDebug "go'";;
        mp <- tmCurrentModPath tt ;;
        d' <- tmEval lazy (tsl_ind ΣE mp kn d) ;;
        tmDebug "done'";;
         match d' with
         | Error e =>
           print_nf e ;;
           fail_nf ("Translation error during the translation of the inductive "
                      ^ string_of_kername kn)
         | Success (E, decls) =>
           monad_iter tmMkInductive' decls ;;
           let Σ' := add_global_decl (kn, InductiveDecl d) (fst ΣE) in
           let E' := (E ++ snd ΣE) in
           Σ' <- tmEval lazy Σ' ;;
           E' <- tmEval lazy E' ;;
           print_nf  (string_of_kername kn ^ " has been translated.") ;;
           ret (Σ', E')
         end
      end
    end)
  (fst p).(declarations) ΣE.
