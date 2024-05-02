module stlc_subsys.

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

type extty ((G -> ty -> o) -> ty -> (ext G -> ty -> o)).
type check ((G -> ty -> o) -> tm G -> ty -> o).
type infer ((G -> ty -> o) -> tm G -> ty -> o).

extty GT A z     A.
extty GT A (s X) B :- GT X B.

infer GT (var X)      A          :- GT X A.
check GT (lam M)      (fn A B)   :- check (extty GT A) M B.
check GT (pair M N)   (prod A B) :- check GT M A, check GT N A.
infer GT (fst M)      A          :- sigma B\ infer GT M (prod A B).
infer GT (snd M)      B          :- sigma A\ infer GT M (prod A B).
check GT (inl M)      (sum A B)  :- check GT M A.
check GT (inr M)      (sum A B)  :- check GT M B.
check GT (case L M N) C          :- sigma A\ sigma B\
                                      infer GT L (sum A B),
                                      check (extty GT A) M C,
                                      check (extty GT B) N C.
check GT tt           unit.
check GT (absurd M)   C          :- infer GT M empty.
infer GT (anno M A)   A          :- check GT M A.
check GT M            B          :- sigma A\ infer GT M A, A = B.
