module Statics.Concise.ContextConversion where

open import Lib
open import Statics.Syntax
open import Statics.Concise
open import Statics.ConciseToVerbose
open import Statics.VerboseToConcise
import Statics.Verbose.ContextConversion as V

open Variables

conv-ty : Γ ≡ Γ′ ctx → Γ ⊢ A ty → Γ′ ⊢ A ty
conv-ty E H = V⇒C-ty (V.conv-ty (C⇒V-≡ctx E) (C⇒V-ty H))

conv-≡ty : Γ ≡ Γ′ ctx → Γ ⊢ A ≡ A′ ty → Γ′ ⊢ A ≡ A′ ty
conv-≡ty E H = V⇒C-≡ty (V.conv-≡ty (C⇒V-≡ctx E) (C⇒V-≡ty H))

conv-tm : Γ ≡ Γ′ ctx → Γ ⊢ M ⦂ A tm → Γ′ ⊢ M ⦂ A tm
conv-tm E H = V⇒C-tm (V.conv-tm (C⇒V-≡ctx E) (C⇒V-tm H))

conv-≡tm : Γ ≡ Γ′ ctx → Γ ⊢ M ≡ M′ ⦂ A tm → Γ′ ⊢ M ≡ M′ ⦂ A tm
conv-≡tm E H = V⇒C-≡tm (V.conv-≡tm (C⇒V-≡ctx E) (C⇒V-≡tm H)) 

conv-subst : Γ ≡ Γ′ ctx → Γ ⊢ σ ⦂ Δ subst → Γ′ ⊢ σ ⦂ Δ subst
conv-subst E H = V⇒C-subst (V.conv-subst (C⇒V-≡ctx E) (C⇒V-subst H))

conv-≡subst : Γ ≡ Γ′ ctx → Γ ⊢ σ ≡ σ′ ⦂ Δ subst → Γ′ ⊢ σ ≡ σ′ ⦂ Δ subst
conv-≡subst E H = V⇒C-≡subst (V.conv-≡subst (C⇒V-≡ctx E) (C⇒V-≡subst H))
