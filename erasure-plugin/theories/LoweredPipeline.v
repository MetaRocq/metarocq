(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Program ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import Transform.
From MetaRocq.Erasure Require Import EProgram EWellformed EWcbvEval
  EImplementLazyForce.
From MetaRocq.ErasurePlugin Require Import ETransform Erasure.
From MetaRocq.ErasurePlugin.transforms Require Import CoInductiveToInductive
  ConstsToValues ImplementLazyForce ImplementBox.
Import Transform.

(** * The verified λ□ pipeline followed by the lowering passes

  This is kept out of [Erasure], which is extracted as a whole to the
  plugin. *)

Local Obligation Tactic := program_simpl.

(** [verified_lambdabox_etransform], followed by the lowering passes:
  constants are compiled to values, lazy/force are implemented with lambdas
  and boxes with a fixpoint absorbing its arguments. First-order values are
  still read back exactly. *)
Program Definition verified_lambdabox_lowered_etransform
  (efl := ERemoveParams.switch_no_params EWellformed.all_env_flags) econf :
  ETransform.t extends_env extends_env fo_evalue fo_evalue_block
    is_eta_app (fun _ => True) :=
  let efl' := efl_coind_to_ind (EConstructorsAsBlocks.switch_cstr_as_blocks
    (EInlineProjections.disable_projections_env_flag efl)) in
  verified_lambdabox_etransform econf ⊳
  (* Constants are compiled to values *)
  consts_to_values_etransform efl' final_wcbv_flags eq_refl eq_refl eq_refl ⊳
  (* Lazy and force are implemented with lambdas *)
  implement_lazy_force_etransform efl' eq_refl eq_refl eq_refl eq_refl
    eq_refl true ⊳
  (* Boxes are implemented with a fixpoint absorbing its arguments *)
  implement_box_etransform (EImplementLazyForce.switch_off_thunk efl')
    eq_refl eq_refl eq_refl eq_refl eq_refl true.
