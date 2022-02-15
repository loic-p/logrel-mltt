{-# OPTIONS --without-K --safe #-}

module Definition.Typed.Consequences.Reduction where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.EqRelInstance
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Fundamental.Reducibility

open import Tools.Product


-- Helper function where all reducible types can be reduced to WHNF.
whNorm′ : ∀ {A Γ l} ([A] : Γ ⊩⟨ l ⟩ A)
                → ∃ λ B → Whnf B × Γ ⊢ A :⇒*: B
whNorm′ (Uᵣ′ .⁰ 0<1 ⊢Γ) = U , Uₙ , idRed:*: (Uⱼ ⊢Γ)
whNorm′ (ℕᵣ D) = ℕ , ℕₙ , D
whNorm′ (ne′ K D neK K≡K) = K , ne neK , D
whNorm′ (Πᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) = Π F ▹ G , Πₙ , D
whNorm′ (emb′ 0<1 [A]) = whNorm′ [A]

-- Well-formed types can all be reduced to WHNF.
whNorm : ∀ {A Γ} → Γ ⊢ A → ∃ λ B → Whnf B × Γ ⊢ A :⇒*: B
whNorm A = whNorm′ (reducible A)

-- Helper function where reducible all terms can be reduced to WHNF.
whNormTerm′ : ∀ {a A Γ l} ([A] : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l ⟩ a ∷ A / [A]
                → ∃ λ b → Whnf b × Γ ⊢ a :⇒*: b ∷ A
whNormTerm′ (Uᵣ′ a b c) (Uₜ A d typeA A≡A [t]) = A , typeWhnf typeA , d
whNormTerm′ (ℕᵣ x) (ιx (ℕₜ n d n≡n prop)) =
  let natN = natural prop
  in  n , naturalWhnf natN , convRed:*: d (sym (subset* (red x)))
whNormTerm′ (ne′ K D neK K≡K) (ιx (neₜ k d (neNfₜ neK₁ ⊢k k≡k))) =
  k , ne neK₁ , convRed:*: d (sym (subset* (red D)))
whNormTerm′ (Πᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Πₜ f d funcF f≡f [f] [f]₁) =
  f , functionWhnf funcF , convRed:*: d (sym (subset* (red D)))
whNormTerm′ (emb′ 0<1 [A]) (ιx [a]) = whNormTerm′ [A] [a]

-- Well-formed terms can all be reduced to WHNF.
whNormTerm : ∀ {a A Γ} → Γ ⊢ a ∷ A → ∃ λ b → Whnf b × Γ ⊢ a :⇒*: b ∷ A
whNormTerm {a} {A} ⊢a =
  let [A] , [a] = reducibleTerm ⊢a
  in  whNormTerm′ [A] [a]
