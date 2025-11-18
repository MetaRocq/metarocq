(** * Term and proof generation for the certifying transforms *)
From Stdlib Require Import List.
From Stdlib Require Import Ascii.
From Stdlib Require Import String.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import Kernames.
From MetaRocq.Template Require Import Ast Checker All.

Open Scope bs.
Import MRMonadNotation.

(* TODO: at some point we should provide StringExtra for byte strings *)
Definition replace_char (orig : ascii) (new : ascii) : String.string -> String.string :=
  fix f s :=
    match s with
    | EmptyString => EmptyString
    | String c s => if (c =? orig)%char then
                      String new (f s)
                    else
                      String c (f s)
    end.

Definition get_def_name (name : kername) : string :=
  let s_name := bytestring.String.to_string (string_of_kername name) in
  bytestring.String.of_string (replace_char "." "_" s_name).

Definition change_modpath (mpath : modpath) (suffix : string) (to_rename : kername -> bool)
  : term -> term :=
  fix go (t : term) : term :=
    match t with
    | tRel n => t
    | tVar id => t
    | tSort s => t
    | tEvar ev args => tEvar ev (map go args)
    | tCast t kind v => tCast (go t) kind (go v)
    | tProd na ty body => tProd na (go ty) (go body)
    | tLambda na ty body => tLambda na (go ty) (go body)
    | tLetIn na def def_ty body =>
      tLetIn na (go def) (go def_ty) (go body)
    | tApp f args => tApp (go f) (map go args)
    | tConst kn u => if to_rename kn then
                      tConst (mpath, get_def_name kn ++ suffix) u
                    else t
    | tInd ind u => t
    | tConstruct ind idx u => t
    | tCase ci p discr branches =>
      tCase ci (map_predicate id go go p)
            (go discr) (map_branches go branches)
    | tProj proj t => tProj proj (go t)
    | tFix mfix idx => tFix (map (map_def go go) mfix) idx
    | tCoFix mfix idx => tCoFix (map (map_def go go) mfix) idx
    | tInt n => tInt n
    | tFloat n => tFloat n
    | tString n => tString n
    | tArray l v def ty => tArray l (map go v) (go def) (go ty)
  end.

Fixpoint map_constants_global_decls (k : kername -> kername) (f : constant_body -> constant_body) (Σ : global_declarations) : global_declarations :=
  match Σ with
  | [] => []
  | (kn, ConstantDecl cb) :: Σ' => (k kn, ConstantDecl (f cb)) :: map_constants_global_decls k f Σ'
  | gd :: Σ' => gd :: map_constants_global_decls k f Σ'
  end.

Definition map_constants_global_env (k : kername -> kername) (f : constant_body -> constant_body) (Σ : global_env) : global_env :=
  {| universes := Σ.(universes);
     declarations := map_constants_global_decls k f Σ.(declarations);
     retroknowledge := Σ.(retroknowledge) |}.

Definition add_suffix_global_env (mpath : modpath) (suffix : string) (expansion_ignore : kername -> bool) (Σ : global_env) :=
  map_constants_global_env
    (fun kn => (mpath,get_def_name kn ++ suffix))
    (fun cb => {| cst_type := change_modpath mpath suffix expansion_ignore cb.(cst_type);
                cst_body := b <- cb.(cst_body);;
                           Some (change_modpath mpath suffix expansion_ignore b);
              cst_universes := cb.(cst_universes);
              cst_relevance := cb.(cst_relevance) |}) Σ.

Definition generate_proof_term (ty : term) (kn1 kn2 : kername) : term × term :=
  let proof_ty :=
      tApp <% @eq %> [ty; tConst kn1 []; tConst kn2 []] in
  let proof_body :=
      tApp <% @eq_refl %> [ty; tConst kn2 []] in
      (proof_ty, proof_body).

Definition gen_prog (ty body : term) (kn : kername) : TemplateMonad unit :=
  tmBind (tmUnquoteTyped Type ty)
         (fun A => ucst <- tmUnquoteTyped A body ;;
                  tmDefinition kn.2 ucst;;
                  ret tt).

Definition gen_proof (suffix : string) (Σ : global_declarations) (mpath : modpath) (kn : kername) : TemplateMonad unit :=
  match lookup_global Σ kn with
  | Some (ConstantDecl cb) =>
    let kn_after := (mpath, get_def_name kn ++ suffix) in
    '(p_ty, p_t) <- tmEval lazy (generate_proof_term cb.(cst_type) kn kn_after) ;;
    tmBind (tmUnquoteTyped Type p_ty)
           (fun B =>
              uproof <- tmUnquoteTyped B p_t ;;
              tmDefinition (kn_after.2 ++ "_convertible") uproof ;;
              tmPrint B)
  | _ => tmFail ("Not a defined constant" ++ string_of_kername kn)
  end.

Definition is_none {A} (o : option A) :=
  match o with
  | Some _ => false
  | None => true
  end.

Definition map_global_env_decls (f : global_declarations -> global_declarations)
           (Σ : global_env) : global_env :=
  {| universes := Σ.(universes);
     declarations := f Σ.(declarations);
     retroknowledge := Σ.(retroknowledge) |}.

(** Given the two environments [Σ1] and [Σ2] we traverse the first and lookup constants
    with the same name in the second. If such a constant is found, we compare the bodies
    for (syntactic) equality. If they are not equal, we expect them to be convertible, so
    we generate a new definition and save the name to [affected] list, which is returned
    when we traversed all definition in [Σ1] *)
Definition traverse_env (mpath : modpath) (suffix : string) (Σ1 Σ2 : global_declarations) :=
  let f := fix go (affected : KernameSet.t) (dΣ1 dΣ2 : global_declarations) : TemplateMonad KernameSet.t :=
      match dΣ1 with
      | [] => ret affected
      | (kn, ConstantDecl cb1) :: Σtail =>
          match lookup_global Σ2 kn with
          | Some (ConstantDecl cb2) =>
              match cb1, cb2 with
              | Build_constant_body ty1 (Some body1) _ _,
                (Build_constant_body ty2 (Some body2) _ _ ) =>
                  new_body2 <- tmEval lazy (change_modpath mpath suffix (fun kn => KernameSet.mem kn affected) body2);;
                  new_ty2 <-tmEval lazy (change_modpath mpath suffix (fun kn => KernameSet.mem kn affected) ty2);;
                  if @Checker.eq_term config.default_checker_flags init_model body1 new_body2 then
                    go affected Σtail dΣ2
                  else
                    gen_prog new_ty2 new_body2 (mpath, get_def_name kn ++ suffix);;
                    go (KernameSet.add kn affected) Σtail dΣ2
              | _,_ => go affected Σtail dΣ2
              end
          | Some _ | None => go affected Σtail dΣ2
          end
      | _ :: Σtail => go affected Σtail dΣ2
      end in
  f KernameSet.empty Σ1 Σ2.

(** We generate new definitions using [traverse_env] and then generate the proofs for all
   affected seeds. The proof is just [eq_refl], since we expect that the generated
   definitions are convertible to the originals. At this point all the affected definitions
   have been added to the current scope given by [mpath].
 *)
(** NOTE: we generate proofs for all affected constants, but we don't gnerate proofs of
    the types of constructors, that can be affected by inlining within types! *)
Definition gen_defs_and_proofs (Σold Σnew : global_declarations)
                               (mpath : modpath)
                               (suffix : string)
                               (seeds : KernameSet.t)
                               : TemplateMonad unit :=
  let filter_decls decls :=
    filter (fun '(kn,gd) =>
              match gd with
              | ConstantDecl cb => negb (is_none cb.(cst_body))
              | _ => false
              end) decls in
  let filteredΣold := filter_decls Σold in
  let filteredΣnew := filter_decls Σnew in
  affected_defs <- traverse_env mpath suffix (List.rev filteredΣold) filteredΣnew;;
  let affected_seeds := KernameSet.inter affected_defs seeds in
  monad_iter (gen_proof suffix Σnew mpath) (KernameSet.elements affected_seeds).
