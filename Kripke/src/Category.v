Set Primitive Projections.

From Coq Require Import
  Logic.ProofIrrelevance
  Relation_Definitions
  RelationClasses.

Section DEFINITION.

  Class Category : Type :=
    { Ob : Type
    ; Hom : Ob -> Ob -> Type
    ; compose : forall {x y z}, Hom y z -> Hom x y -> Hom x z
    ; id : forall x, Hom x x
    ; compose_assoc :
      forall {x y z w} (f : Hom x y) (g : Hom y z) (h : Hom z w),
        compose (compose h g) f = compose h (compose g f)
    ; compose_id_left : forall {x y} (f : Hom x y), compose (id y) f = f
    ; compose_id_right : forall {x y} (f : Hom x y), compose f (id x) = f
    }.

  #[global] Coercion Ob : Category >-> Sortclass.

End DEFINITION.

Declare Scope category_scope.
Delimit Scope category_scope with cat.

Notation "g ∘ f" := (compose g f) (at level 40, left associativity) : category_scope.
Notation "f ∗ g" := (compose g f) (at level 40, left associativity) : category_scope.

Section INSTANCES.

  #[global] Program Instance PreOrderCat {A : Type} (R : relation A) `{PreOrder A R} : Category :=
    {|
      Ob := A;
      Hom := R;
      compose := fun x y z g f => @transitivity A R _ x y z f g;
      id := fun x => @reflexivity A R _ x;
    |}.
  Next Obligation.
    apply proof_irrelevance.
  Qed.
  Next Obligation.
    apply proof_irrelevance.
  Qed.
  Next Obligation.
    apply proof_irrelevance.
  Qed.

End INSTANCES.

Section UNIVERSAL_CONSTRUCTION.

  Context `{C : Category}.
  Open Scope category_scope.

  Record isProduct (A B P : C) : Type :=
    { fst : Hom P A
    ; snd : Hom P B
    ; universal :
      forall {X} (fst' : Hom X A) (snd' : Hom X B),
      exists u, fst' = u ∗ fst /\ snd' = u ∗ snd
    }.

End UNIVERSAL_CONSTRUCTION.
