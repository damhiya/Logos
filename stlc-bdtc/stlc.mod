module stlc.

kind ty type.
type fn (ty -> ty -> ty).
type prod (ty -> ty -> ty).
type sum (ty -> ty -> ty).
type unit ty.
type empty ty.

kind tm type.
type anno (tm -> ty -> tm).
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

type check (tm -> ty -> o).
type infer (tm -> ty -> o).

check M            B          :- sigma A\ infer M A, A = B.
infer (anno M A)   A          :- check M A.
check (lam M)      (fn A B)   :- pi x\ infer x A => check (M x) B.
infer (app M N)    B          :- infer M (fn A B), check N A.
check (pair M N)   (prod A B) :- check M A, check N B.
infer (fst M)      A          :- sigma B\ infer M (prod A B).
infer (snd M)      B          :- sigma A\ infer M (prod A B).
check (inl M)      (sum A B)  :- check M A.
check (inr M)      (sum A B)  :- check M B.
check (case L M N) C          :- sigma A\ sigma B\
                                   infer L (sum A B),
                                   (pi x\ infer x A => check (M x) C),
                                   (pi y\ infer y B => check (N y) C).
check tt           unit.
check (absurd M)   C          :- infer M empty.
