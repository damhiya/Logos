Set Primitive Projections.

From Coq Require Import
  Relation_Definitions
  RelationClasses.

Section SYNTAX.

  Context {P : Type}.

  Inductive Formula : Type :=
  | VarF (p : P)
  | ImpF (A B : Formula)
  | ConjF (A B : Formula)
  | DisjF (A B : Formula)
  | FalseF : Formula
  | TrueF : Formula
  .

End SYNTAX.

Section MODEL.

  Context {W : Type} {R : relation W} `{R_PreOrder : PreOrder W R}.
  Context {P : Type} {interp : W -> P -> Prop}.
  Hypothesis interp_mono : forall w u, R w u -> forall p, interp w p -> interp u p.

  Declare Scope meta_scope.
  Open Scope meta_scope.

  Infix "≤" := R (at level 30, no associativity): meta_scope.
  Reserved Notation "w ⊩ A" (at level 30, no associativity).

  Fixpoint models (w : W) (f : Formula) : Prop :=
    match f with
    | VarF p => interp w p
    | ImpF A B => forall u, w ≤ u -> u ⊩ A -> u ⊩ B
    | ConjF A B => w ⊩ A /\ w ⊩ B
    | DisjF A B => w ⊩ A \/ w ⊩ B
    | FalseF => False
    | TrueF => True
    end
  where "w ⊩ A" := (models w A).

End MODEL.
