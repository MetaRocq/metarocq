(** Dearging analysis of the typed erasure: a relevant constructor argument
    whose type erases to [TAny] is kept when it is used, and does not
    prevent dearging the rest of the program. *)
From Stdlib Require Import List.
From MetaRocq.Utils Require Import bytestring ResultMonad.
From MetaRocq.Template Require Import All.
From MetaRocq.Erasure.Typed Require Import ExAst Optimize Extraction
  ExtractionCorrectness.
From MetaRocq.ErasurePlugin Require Import Loader.
Import ListNotations.

(* [x] is relevant, but its type erases to [TAny]. *)
Inductive T :=
| C (b : bool) (x : if b then nat else bool)
| D (A : Type) (n : nat).

Definition get (t : T) : nat :=
  match t with
  | C b x =>
    (if b as b return (if b then nat else bool) -> nat
     then fun n => n else fun _ => 0) x
  | D _ n => n
  end.

Definition poly (A : Type) (a : A) := a.

(* The use of [x] is in [get], in the environment. *)
Definition prog := get (C true 3) + poly nat 1 + get (D bool 2).

(* The use of [x] is in the main term. *)
Definition prog2 :=
  match C true 3 with
  | C b x =>
    (if b as b return (if b then nat else bool) -> nat
     then fun n => n else fun _ => 0) x
  | D _ n => n
  end + poly nat 1.

MetaRocq Erase -typed prog.
MetaRocq Erase -typed prog2.

(** The erased environment, before dearging. *)
Definition no_dearging : extract_template_env_params :=
  {| template_transforms := [];
     check_wf_env_func Σ := Ok (assume_env_wellformed Σ);
     pcuic_args :=
       {| optimize_prop_discr := true; extract_transforms := [] |} |}.

Definition erased_env (p : Ast.Env.program) : ExAst.global_env :=
  match p.2 with
  | Ast.tConst kn _ =>
    match extract_template_env no_dearging p.1 (KernameSet.singleton kn)
      (fun _ => false) with
    | Ok Σ => Σ
    | Err _ => []
    end
  | _ => []
  end.

Definition kn_of (t : Ast.term) : kername :=
  match t with
  | Ast.tConst kn _ | Ast.tInd {| inductive_mind := kn |} _ => kn
  | _ => (MPfile [], ""%bs)
  end.

MetaRocq Quote Definition qT := T.
MetaRocq Quote Definition qpoly := poly.
MetaRocq Quote Definition qprog2 := prog2.

Definition ctor_masks_of (ds : dearg_set) :=
  option_map Optimize.ctor_masks (get_mib_masks (ind_masks ds) (kn_of qT)).

Definition const_mask_of (ds : dearg_set) :=
  get_const_mask (const_masks ds) (kn_of qpoly).

(** Use in the environment: [x] is kept, [A] is removed from [D] and
    [poly], and the masks are valid. *)
MetaRocq Quote Recursively Definition qprog := prog.
Definition Σ1 := erased_env qprog.
Definition ds1 := analyze_env (fun _ => None) Σ1.

Example prog_ctor_masks :
  ctor_masks_of ds1 = Some [(0, 0, [false; false]); (0, 1, [true; false])].
Proof. vm_compute. reflexivity. Qed.

Example prog_poly_mask : const_mask_of ds1 = [true; false].
Proof. vm_compute. reflexivity. Qed.

Example prog_masks_valid :
  valid_masks_env (ind_masks ds1) (const_masks ds1) Σ1 = true.
Proof. vm_compute. reflexivity. Qed.

Example prog_dearged :
  match dearg_transform (fun _ => None) true false true true true Σ1 with
  | Ok _ => true
  | Err _ => false
  end = true.
Proof. vm_compute. reflexivity. Qed.

(** Use in the main term: the environment alone would remove [x], the
    analysis of the program keeps it. *)
MetaRocq Quote Recursively Definition qprog2_rec := prog2.
Definition Σ2_full := erased_env qprog2_rec.
Definition Σ2 :=
  filter (fun '(kn, _, _) => negb (eq_kername kn (kn_of qprog2))) Σ2_full.
Definition t2 :=
  match ExAst.lookup_env Σ2_full (kn_of qprog2) with
  | Some (ExAst.ConstantDecl {| ExAst.cst_body := Some t |}) => t
  | _ => EAst.tBox
  end.
Definition ds2 := analyze_program (fun _ => None) Σ2 t2.

Example prog2_env_ctor_masks :
  ctor_masks_of (analyze_env (fun _ => None) Σ2) =
    Some [(0, 0, [false; true]); (0, 1, [true; false])].
Proof. vm_compute. reflexivity. Qed.

Example prog2_ctor_masks :
  ctor_masks_of ds2 = Some [(0, 0, [false; false]); (0, 1, [true; false])].
Proof. vm_compute. reflexivity. Qed.

Example prog2_masks_valid :
  match compute_program_masks (fun _ => None) true false Σ2 t2 with
  | Ok ds => valid_cases (ind_masks ds) t2
  | Err _ => false
  end = true.
Proof. vm_compute. reflexivity. Qed.

(** Extraction from within Rocq checks the masks: they must not be
    trimmed, or constructors keeping their last argument fail the check. *)
Definition head0 (l : list nat) :=
  match l with cons x _ => x | nil => 0 end.
MetaRocq Quote Recursively Definition qhead0 := head0.

Example extract_within_coq_ok :
  match qhead0.2 with
  | Ast.tConst kn _ =>
    match extract_template_env_within_coq qhead0.1
      (KernameSet.singleton kn) (fun _ => false) with
    | Ok _ => true
    | Err _ => false
    end
  | _ => false
  end = true.
Proof. vm_compute. reflexivity. Qed.
