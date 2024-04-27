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

  Infix "≲" := R (at level 30, no associativity): meta_scope.
  Reserved Notation "w ⊩ A" (at level 30, no associativity).

  Fixpoint models (w : W) (f : Formula) : Prop :=
    match f with
    | VarF p => interp w p
    | ImpF A B => forall u, w ≲ u -> u ⊩ A -> u ⊩ B
    | ConjF A B => w ⊩ A /\ w ⊩ B
    | DisjF A B => w ⊩ A \/ w ⊩ B
    | FalseF => False
    | TrueF => True
    end
  where "w ⊩ A" := (models w A).

  Definition prod (A B P : W) : Prop :=
    P ≲ A /\ P ≲ B /\ forall X, X ≲ A -> X ≲ B -> X ≲ P.

  Definition sum (A B S : W) : Prop :=
    A ≲ S /\ B ≲ S /\ forall X, A ≲ X -> B ≲ X -> S ≲ X.

  Fixpoint models' (w : W) (f : Formula) : Prop :=
    match f with
    | VarF p => interp w p
    | ImpF A B => forall u v, sum w u v -> models' u A -> models' v B
    | ConjF A B => exists u v, sum u v w /\ models' u A /\ models' v B
    | DisjF A B => models' w A \/ models' w B
    | FalseF => False
    | TrueF => True
    end.

  Lemma models_mono : forall {A w u}, w ≲ u -> w ⊩ A -> u ⊩ A.
  Proof.
    intros A. induction A; firstorder.
  Qed.

  Lemma models_iff_models' : forall A w, models w A <-> models' w A.
  Proof.
    intros A. induction A.
    - simpl. tauto.
    - intros w; simpl. split.
      + intros H u v [H0 [H1 H2]] H3.
        apply IHA1 in H3. apply IHA2.
        apply H; auto. apply (models_mono H1). auto.
      + intros H u H0 H1.
        specialize (H u u).
        apply IHA2. apply H.
        * firstorder.
        * apply IHA1. auto.
    - intros w; simpl. split.
      + intros [H1 H2]. exists w, w. split.
        * firstorder.
        * split.
          -- apply IHA1. auto.
          -- apply IHA2. auto.
      + intros [u [v [[H0 [H1 H2]] [H3 H4]]]]. split.
        * apply (models_mono H0). apply IHA1. auto.
        * apply (models_mono H1). apply IHA2. auto.
    - simpl. firstorder.
    - simpl. tauto.
    - simpl. tauto.
  Qed.

End MODEL.
