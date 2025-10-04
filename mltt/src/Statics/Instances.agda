open import Lib
open import Statics.Preterm
import Statics.System as V
open V using (_ctx; _≡_ctx; _⊢_ty; _⊢_≡_ty; _⊢_⦂_tm; _⊢_≡_⦂_tm; _⊢_⦂_sb; _⊢_≡_⦂_sb)
open Variables

module Statics.Instances where

instance
  -- ctx instances
  ctx-∙-wf : ∙ ctx
  ctx-∙-wf = V.∙-wf

  ctx-,-wf : {{Γ-wf : Γ ctx}} → {{A-wf : Γ ⊢ A ty}} → Γ , A ctx
  ctx-,-wf {{Γ-wf}} {{A-wf}} = V.,-wf Γ-wf A-wf

  -- ty instances
  Π̇-wf : {{Γ-wf : Γ ctx}} → {{A-wf : Γ ⊢ A ty}} → {{B-wf : Γ , A ⊢ B ty}} → Γ ⊢ Π̇ A B ty
  Π̇-wf {{Γ-wf}} {{A-wf}} {{B-wf}} = V.Π̇-wf Γ-wf A-wf B-wf

  ℕ̇-wf : {{Γ-wf : Γ ctx}} → Γ ⊢ ℕ̇ ty
  ℕ̇-wf {{Γ-wf}} = V.ℕ̇-wf Γ-wf

  U̇-wf : {{Γ-wf : Γ ctx}} → Γ ⊢ U̇ i ty
  U̇-wf {{Γ-wf}} = V.U̇-wf Γ-wf

  El-wf : {{Γ-wf : Γ ctx}} → {{M-wf : Γ ⊢ M ⦂ U̇ i tm}} → Γ ⊢ El i M ty
  El-wf {{Γ-wf}} {{M-wf}} = V.El-wf Γ-wf M-wf

  []ty-wf : {{Γ-wf : Γ ctx}} → {{Δ-wf : Δ ctx}} → {{A-wf : Γ ⊢ A ty}} → {{γ-wf : Δ ⊢ γ ⦂ Γ sb}} → Δ ⊢ A [ γ ] ty
  []ty-wf {{Γ-wf}} {{Δ-wf}} {{A-wf}} {{γ-wf}} = V.[]ty-wf Γ-wf Δ-wf A-wf γ-wf

  -- tm instances
  q-wf : {{Γ-wf : Γ ctx}} → {{Δ-wf : Δ ctx}} → {{A-wf : Γ ⊢ A ty}} → {{γ-wf : Δ ⊢ γ ⦂ Γ , A sb}} → Δ ⊢ q γ ⦂ A [ p γ ] tm
  q-wf {{Γ-wf}} {{Δ-wf}} {{A-wf}} {{γ-wf}} = V.q-wf Γ-wf Δ-wf A-wf γ-wf

  λ·-wf : {{Γ-wf : Γ ctx}} → {{A-wf : Γ ⊢ A ty}} → {{B-wf : Γ , A ⊢ B ty}} → {{M-wf : Γ , A ⊢ M ⦂ B tm}} → Γ ⊢ λ· M ⦂ Π̇ A B tm
  λ·-wf {{Γ-wf}} {{A-wf}} {{B-wf}} {{M-wf}} = V.λ·-wf Γ-wf A-wf B-wf M-wf

  ·-wf : {{Γ-wf : Γ ctx}} → {{A-wf : Γ ⊢ A ty}} → {{B-wf : Γ , A ⊢ B ty}} → {{M-wf : Γ ⊢ M ⦂ Π̇ A B tm}} → {{N-wf : Γ ⊢ N ⦂ A tm}} → Γ ⊢ M · N ⦂ B [ id , N ] tm
  ·-wf {{Γ-wf}} {{A-wf}} {{B-wf}} {{M-wf}} {{N-wf}} = V.·-wf Γ-wf A-wf B-wf M-wf N-wf

  z·-wf : {{Γ-wf : Γ ctx}} → Γ ⊢ z· ⦂ ℕ̇ tm
  z·-wf {{Γ-wf}} = V.z·-wf Γ-wf

  s·-wf : {{Γ-wf : Γ ctx}} → {{M-wf : Γ ⊢ M ⦂ ℕ̇ tm}} → Γ ⊢ s· M ⦂ ℕ̇ tm
  s·-wf {{Γ-wf}} {{M-wf}} = V.s·-wf Γ-wf M-wf

  ·rec-wf : {{Γ-wf : Γ ctx}} → {{L-wf : Γ ⊢ L ⦂ ℕ̇ tm}} → {{C-wf : Γ , ℕ̇ ⊢ C ty}} → {{M-wf : Γ ⊢ M ⦂ C [ id , z· ] tm}} → {{N-wf : Γ , ℕ̇ , C ⊢ N ⦂ C [ p (p id) , s· q (p id) ] tm}} → Γ ⊢ L ·rec[ C , M , N ] ⦂ C [ id , L ] tm
  ·rec-wf {{Γ-wf}} {{L-wf}} {{C-wf}} {{M-wf}} {{N-wf}} = V.·rec-wf Γ-wf L-wf C-wf M-wf N-wf

  Π̌-wf : {{Γ-wf : Γ ctx}} → {{M-wf : Γ ⊢ M ⦂ U̇ i tm}} → {{N-wf : Γ , El i M ⊢ N ⦂ U̇ i tm}} → Γ ⊢ Π̌ i M N ⦂ U̇ i tm
  Π̌-wf {{Γ-wf}} {{M-wf}} {{N-wf}} = V.Π̌-wf Γ-wf M-wf N-wf

  ℕ̌-wf : {{Γ-wf : Γ ctx}} → Γ ⊢ ℕ̌ i ⦂ U̇ i tm
  ℕ̌-wf {{Γ-wf}} = V.ℕ̌-wf Γ-wf

  Ǔ-wf : {{Γ-wf : Γ ctx}} → {{j<i : j < i}} → Γ ⊢ Ǔ i j ⦂ U̇ i tm
  Ǔ-wf {{Γ-wf}} {{j<i}} = V.Ǔ-wf Γ-wf j<i

  lift-wf : {{Γ-wf : Γ ctx}} → {{j≤i : j ≤ i}} → {{M-wf : Γ ⊢ M ⦂ U̇ j tm}} → Γ ⊢ lift i j M ⦂ U̇ i tm
  lift-wf {{Γ-wf}} {{j≤i}} {{M-wf}} = V.lift-wf Γ-wf j≤i M-wf

  []tm-wf : {{Γ-wf : Γ ctx}} → {{Δ-wf : Δ ctx}} → {{A-wf : Γ ⊢ A ty}} → {{M-wf : Γ ⊢ M ⦂ A tm}} → {{γ-wf : Δ ⊢ γ ⦂ Γ sb}} → Δ ⊢ M [ γ ] ⦂ A [ γ ] tm
  []tm-wf {{Γ-wf}} {{Δ-wf}} {{A-wf}} {{M-wf}} {{γ-wf}} = V.[]tm-wf Γ-wf Δ-wf A-wf M-wf γ-wf

  -- sb instances
  id-wf : {{Γ-wf : Γ ctx}} → Γ ⊢ id ⦂ Γ sb
  id-wf {{Γ-wf}} = V.id-wf Γ-wf

  ∘-wf : {{Γ-wf : Γ ctx}} → {{Δ-wf : Δ ctx}} → {{Θ-wf : Θ ctx}} → {{γ-wf : Δ ⊢ γ ⦂ Γ sb}} → {{δ-wf : Θ ⊢ δ ⦂ Δ sb}} → Θ ⊢ γ ∘ δ ⦂ Γ sb
  ∘-wf {{Γ-wf}} {{Δ-wf}} {{Θ-wf}} {{γ-wf}} {{δ-wf}} = V.∘-wf Γ-wf Δ-wf Θ-wf γ-wf δ-wf

  !-wf : {{Γ-wf : Γ ctx}} → Γ ⊢ ! ⦂ ∙ sb
  !-wf {{Γ-wf}} = V.!-wf Γ-wf

  p-wf : {{Γ-wf : Γ ctx}} → {{Δ-wf : Δ ctx}} → {{A-wf : Γ ⊢ A ty}} → {{γ-wf : Δ ⊢ γ ⦂ Γ , A sb}} → Δ ⊢ p γ ⦂ Γ sb
  p-wf {{Γ-wf}} {{Δ-wf}} {{A-wf}} {{γ-wf}} = V.p-wf Γ-wf Δ-wf A-wf γ-wf

  ,-wf : {{Γ-wf : Γ ctx}} → {{Δ-wf : Δ ctx}} → {{A-wf : Γ ⊢ A ty}} → {{γ-wf : Δ ⊢ γ ⦂ Γ sb}} → {{M-wf : Δ ⊢ M ⦂ A [ γ ] tm}} → Δ ⊢ γ , M ⦂ Γ , A sb
  ,-wf {{Γ-wf}} {{Δ-wf}} {{A-wf}} {{γ-wf}} {{M-wf}} = V.,-wf Γ-wf Δ-wf A-wf γ-wf M-wf
