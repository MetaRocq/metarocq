From MetaCoq.Template Require Import All.

Import MCMonadNotation.
Import bytestring.
Open Scope bs.
Open Scope list_scope.

Universes u0 u1.
Constraint u0 < u1.
MetaCoq Run (u <- tmQuote Type@{u0};;
             v <- tmTry (tmUnquoteTyped Type@{u0} u);;
             match v with
             | my_Value v => tmPrint (v -> True);; tmFail "first should not succeed"
             | my_Error _ => v' <- tmUnquoteTyped Type@{u1} u;;
                             ret (v' -> False)
             end >>= tmPrint).

(*MetaCoq Run (tmDefinition "a" I;; tmTry (tmDefinition "a" I) >>= tmPrint).*)
(*a is defined

Error: Anomaly "in Univ.repr: Universe MetaCoq.TestSuite.tmTry.101 undefined." Please report at http://coq.inria.fr/bugs/.*)
(*MetaCoq Run (tmTry (tmDefinition "b" I);; mp <- tmCurrentModPath tt;; tmUnquote (tConst (mp, "b") []) >>= tmPrint).*)
(*Error: Anomaly "Constant MetaCoq.TestSuite.tmTry.b does not appear in the environment."
Please report at http://coq.inria.fr/bugs/.*)
(*MetaCoq Run (tmDefinition "c" I;; mp <- tmCurrentModPath tt;;
             v <- tmTry (tmUnquoteTyped False (tConst (mp, "c") []));;
             match v with
             | my_Value v => ret (inl v)
             | my_Error _ => v' <- tmUnquoteTyped True (tConst (mp, "c") []);;
                             ret (inr v')
             end >>= tmPrint).*)
(*Error: Anomaly "in Univ.repr: Universe MetaCoq.TestSuite.tmTry.172 undefined." Please report at http://coq.inria.fr/bugs/.*)
MetaCoq Run (tmAxiom "a'" True;; tmTry (tmAxiom "a'" True) >>= tmPrint).
(*MetaCoq Run (tmTry (tmAxiom "b'" True);; mp <- tmCurrentModPath tt;; tmUnquote (tConst (mp, "b'") []) >>= tmPrint).*)
(*Error: Anomaly "Constant MetaCoq.TestSuite.tmTry.b' does not appear in the environment."
Please report at http://coq.inria.fr/bugs/.*)
MetaCoq Run (tmAxiom "c'" True;; mp <- tmCurrentModPath tt;;
             v <- tmTry (tmUnquoteTyped False (tConst (mp, "c'") []));;
             match v with
             | my_Value v => tmPrint v;; tmFail "too early"
             | my_Error _ => v' <- tmUnquoteTyped True (tConst (mp, "c'") []);;
                             ret v'
             end >>= tmPrint).
