module Statics.Inclusion where

open import Lib
open import Statics.Syntax

open Variables

NfTy⇒Ty : NfTy G → Ty G
Ne⇒Tm : Ne G → Tm G
Nf⇒Tm : Nf G → Tm G
NfTy⇒Ty (Π̇ M N) = Π̇ (NfTy⇒Ty M) (NfTy⇒Ty N)
NfTy⇒Ty ℕ̇ = ℕ̇
NfTy⇒Ty (U̇ n) = U̇ n
NfTy⇒Ty (T n M) = T n (Ne⇒Tm M)
Ne⇒Tm (# x) = # x
Ne⇒Tm (M · N) = Ne⇒Tm M · Nf⇒Tm N
Ne⇒Tm (rec C L M N) = rec (NfTy⇒Ty C) (Nf⇒Tm L) (Nf⇒Tm M) (Ne⇒Tm N)
Nf⇒Tm (⇄ M) = Ne⇒Tm M
Nf⇒Tm (ƛ M) = ƛ Nf⇒Tm M
Nf⇒Tm z· = z·
Nf⇒Tm (s· M) = s· Nf⇒Tm M
Nf⇒Tm (Π̌ n M N) = Π̌ n (Nf⇒Tm M) (Nf⇒Tm N)
Nf⇒Tm (ℕ̌ n) = ℕ̌ n
Nf⇒Tm (Ǔ n i) = Ǔ n i
Nf⇒Tm (Ť n i M) = Ť n i (Ne⇒Tm M)
