sig stlc_subsys.

kind ext (type -> type).
type z (ext A).
type s (A -> ext A).

kind ty type.
type fn (ty -> ty -> ty).
type prod (ty -> ty -> ty).
type sum (ty -> ty -> ty).
type unit ty.
type empty ty.

kind tm (type -> type).
type var (G -> tm G).
type lam (tm (ext G) -> tm G).
type app (tm G -> tm G -> tm G).
type pair (tm G -> tm G -> tm G).
type fst (tm G -> tm G).
type snd (tm G -> tm G).
type inl (tm G -> tm G).
type inr (tm G -> tm G).
type case (tm G -> tm (ext G) -> tm (ext G) -> tm G).
type tt (tm G).
type absurd (tm G -> tm G).
type anno (tm G -> ty -> tm G).

exportdef extty ((G -> ty -> o) -> ty -> (ext G -> ty -> o)).
exportdef check ((G -> ty -> o) -> tm G -> ty -> o).
exportdef infer ((G -> ty -> o) -> tm G -> ty -> o).
