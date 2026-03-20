(* Distributed under the terms of the MIT license. *)

(** Generic transofmations from one language to another,
    preserving an evaluation relation up-to some observational equality. *)

From Stdlib Require Import Program ssreflect ssrbool.
From Equations Require Import Equations.
From MetaRocq.Utils Require Import utils.
Import bytestring.
Local Open Scope bs.
Local Open Scope string_scope2.

(* Used to show timings of the ML execution *)

Definition time : forall {A B}, string -> (A -> B) -> A -> B :=
  fun A B s f x => f x.

Extract Constant time =>
  "(fun c f x -> let s = Caml_bytestring.caml_string_of_bytestring c in Tm_util.time (Pp.str s) f x)".

Module Transform.
  Definition program env term := env * term.
  Section Opt.
     Context {env env' : Type}.
     Context {term term' : Type}.
     Context {value value' : Type}.
     Abbreviation program' := (program env' term').
     Abbreviation program := (program env term).
     Context {eval :  program -> value -> Prop}.
     Context {eval' : program' -> value' -> Prop}.

     Definition preserves_eval pre (transform : forall p : program, pre p -> program')
      (obseq : forall p : program, pre p -> program' -> value -> value' -> Prop) :=
      forall p v (pr : pre p),
        eval p v ->
        let p' := transform p pr in
        exists v', eval' p' v' /\ obseq p pr p' v v'.

    Record t :=
    { name : string;
      pre : program -> Prop;
      transform : forall p : program, pre p -> program';
      post : program' -> Prop;
      correctness : forall input (p : pre input), post (transform input p);
      obseq : forall p : program, pre p -> program' -> value -> value' -> Prop;
      preservation : preserves_eval pre transform obseq }.

    Definition run (x : t) (p : program) (pr : pre x p) : program' :=
      time x.(name) (fun _ => x.(transform) p pr) tt.

  End Opt.
  Arguments t : clear implicits.

  Definition self_transform env term eval eval' := t env env term term term term eval eval'.

  Section Comp.
    Context {env env' env'' : Type}.
    Context {term term' term'' : Type}.
    Context {value value' value'' : Type}.
    Context {eval : program env term -> value -> Prop}.
    Context {eval' : program env' term' -> value' -> Prop}.
    Context {eval'' : program env'' term'' -> value'' -> Prop}.

    Local Obligation Tactic := idtac.
    Program Definition compose (o : t env env' term term' _ _ eval eval') (o' : t env' env'' term' term'' _ _ eval' eval'')
      (hpp : (forall p, o.(post) p -> o'.(pre) p))
      : t env env'' term term'' _ _ eval eval'' :=
      {|
        name := (o.(name) ^ " -> " ^ o'.(name))%bs;
        transform p hp := run o' (run o p hp) (hpp _ (o.(correctness) _ hp));
        pre := o.(pre);
        post := o'.(post);
        obseq g preg g' v v' :=
        exists v'', o.(obseq) g preg (run o g preg) v v'' ×
            o'.(obseq) (run o g preg) (hpp _ (o.(correctness) _ preg)) g' v'' v'
        |}.
    Next Obligation.
      intros o o' hpp inp pre.
      eapply o'.(correctness).
    Qed.
    Next Obligation.
      red. intros o o' hpp.
      intros p v pr ev.
      eapply (o.(preservation) _ _ pr) in ev; auto.
      cbn in ev. destruct ev as [v' [ev]].
      epose proof (o'.(preservation) (o.(transform) p pr) v').
      specialize (H0 (hpp _ (o.(correctness) _ pr)) ev).
      destruct H0 as [v'' [ev' obs'']].
      exists v''. constructor => //.
      exists v'. now split.
    Qed.

  End Comp.

  Declare Scope transform_scope.
  Bind Scope transform_scope with t.

  Notation " o ▷ o' " := (Transform.compose o o' _) (at level 50, left associativity) : transform_scope.

  Open Scope transform_scope.
End Transform.
