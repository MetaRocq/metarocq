From Stdlib Require Import List.
From MetaRocq.Template Require Import All Loader.
Import MonadNotation.
Open Scope bs.

Definition constructor (goal : Ast.term): TemplateMonad typed_term :=
  let '(hd, iargs) := decompose_app goal in
  match hd with
  | Ast.tInd ind u =>
      qi <- tmQuoteInductive (inductive_mind ind) ;;
      match nth_error qi.(Ast.Env.ind_bodies) (inductive_ind ind) with
      | Some oib =>
      let cstrs := Ast.Env.ind_ctors oib in
      match cstrs with
      | [] => tmFail "no constructor in this inductive type"
      | hd :: _ =>
          let args := cstr_args hd in
          let params := firstn qi.(ind_npars) iargs in
          let args := (params ++ map (fun _ => Ast.hole) args)%list in
          let term := Ast.tApp (Ast.tConstruct ind 0 u) args in
          term' <- tmEval all term ;;
          tmUnquote term'
      end
      | None => tmFail "anomaly"
      end
  | _ => tmFail "goal is not an inductive type"
  end.

Ltac constructor_tac :=
  match goal with
  |- ?T =>
      let k tm := refine tm.(my_projT2) in
      unshelve quote_term T ltac:(fun gl => run_template_program (constructor gl) k)
  end.

Goal True.
  constructor_tac.
Qed.

Goal True + False.
  repeat constructor_tac.
Qed.
