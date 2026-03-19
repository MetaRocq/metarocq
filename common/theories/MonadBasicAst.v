(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils monad_utils MRList.
From MetaRocq.Common Require Import BasicAst.

Import MonadNotation.
Local Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.

Section with_monad.
  Context {T} {M : Monad T}.

  Definition monad_map_binder_annot {A B} (f : A -> T B) (b : binder_annot A) : T (binder_annot B) :=
    let '{| binder_name := binder_name;
           binder_relevance := binder_relevance |} := b in
    binder_name <- f binder_name;;
    ret {| binder_name := binder_name;
          binder_relevance := binder_relevance |}.

  Definition monad_map_def {A B} (tyf bodyf : A -> T B) (d : def A) :=
    let '{| dname := dname; dtype := dtype; dbody := dbody; rarg := rarg |} := d in
    dtype <- tyf dtype;;
    dbody <- bodyf dbody;;
    ret {| dname := dname; dtype := dtype; dbody := dbody; rarg := rarg |}.

  Definition monad_typ_or_sort_map {univ T' T''} (f: T' -> T T'') (t : judgment_ univ T') :=
    match t with
    | Judge tm ty u rel => ftm <- monad_option_map f tm;; fty <- f ty;; ret (Judge ftm fty u rel)
    end.

  Definition monad_map_decl {term term'} (f : term -> T term') (d : context_decl term) : T (context_decl term') :=
    let '{| decl_name := decl_name;
           decl_body := decl_body;
           decl_type := decl_type |} := d in
    decl_body <- monad_option_map f decl_body;;
    decl_type <- f decl_type;;
    ret {| decl_name := decl_name;
          decl_body := decl_body;
          decl_type := decl_type |}.

  Definition monad_map_context {term term'} (f : term -> T term') (c : list (context_decl term)) :=
    monad_map (monad_map_decl f) c.

  Section ContextMap.
    Context {term term' : Type} (f : nat -> term -> T term').

    (* N.B. this does not universe check without [Local Unset Universe Minimization ToSet.] above *)
    Fixpoint monad_mapi_context (c : list (context_decl term)) : T (list (context_decl term')) :=
      match c with
      | d :: Γ => d <- monad_map_decl (f #|Γ|) d;; Γ <- monad_mapi_context Γ;; ret (d :: Γ)
      | [] => ret []
      end.
  End ContextMap.

  Section Contexts.
    Context {term term' term'' : Type}.
    Abbreviation context term := (list (context_decl term)).

    Definition monad_fold_context_k (f : nat -> term -> T term') Γ :=
      Γ <- monad_map_i (fun k' decl => monad_map_decl (f k') decl) (rev Γ);; ret (rev Γ).

    Arguments monad_fold_context_k f Γ%_list_scope.

    Local Set Keyed Unification.

    Equations monad_mapi_context_In (ctx : context term) (f : nat -> forall (x : context_decl term), In x ctx -> T (context_decl term)) : T (context term) :=
      monad_mapi_context_In nil _ := ret nil;
      monad_mapi_context_In (cons x xs) f := fx <- (f #|xs| x _);; fxs <- monad_mapi_context_In xs (fun n x H => f n x _);; ret (cons fx fxs).

    Equations monad_fold_context_In (ctx : context term) (f : context term -> forall (x : context_decl term), In x ctx -> T (context_decl term)) : T (context term) :=
      monad_fold_context_In nil _ := ret nil;
      monad_fold_context_In (cons x xs) f :=
        xs' <- monad_fold_context_In xs (fun n x H => f n x _);;
        x' <- f xs' x _;;
        ret (cons x' xs').

    Equations monad_fold_context (f : context term -> context_decl term -> T (context_decl term)) (ctx : context term) : T (context term) :=
      monad_fold_context f nil := ret nil;
      monad_fold_context f (cons x xs) :=
        xs' <- monad_fold_context f xs;;
        x' <- f xs' x;;
        ret (cons x' xs').

  End Contexts.
End with_monad.
