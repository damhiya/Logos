sig stlc.

kind ty type.
type fn (ty -> ty -> ty).
type prod (ty -> ty -> ty).
type sum (ty -> ty -> ty).
type unit ty.
type empty ty.

kind tm type.
type lam ((tm -> tm) -> tm).
type app (tm -> tm -> tm).
type pair (tm -> tm -> tm).
type fst (tm -> tm).
type snd (tm -> tm).
type inl (tm -> tm).
type inr (tm -> tm).
type case (tm -> (tm -> tm) -> (tm -> tm) -> tm).
type tt tm.
type absurd (tm -> tm).
type anno (tm -> ty -> tm).

exportdef var   (tm -> ty -> o).
exportdef check (tm -> ty -> o).
exportdef infer (tm -> ty -> o).
