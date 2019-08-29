{-# OPTIONS --without-K --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.ProofIrrelevance {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped as U hiding (wk)
open import Definition.Untyped.Properties using (wkSingleSubstId)
open import Definition.Typed
open import Definition.Typed.Weakening
open import Definition.Typed.Properties
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Substitution


open import Tools.Product
open import Tools.Unit
open import Tools.Empty
open import Tools.Nat

import Tools.PropositionalEquality as PE

~-quasirefl : ∀ {Γ n n′ A r} → Γ ⊢ n ~ n′ ∷ A ^ r → Γ ⊢ n ~ n ∷ A ^ r
~-quasirefl p = ~-trans p (~-sym p)

≅-quasirefl : ∀ {Γ n n′ A r} → Γ ⊢ n ≅ n′ ∷ A ^ r → Γ ⊢ n ≅ n ∷ A ^ r
≅-quasirefl p = ≅ₜ-trans p (≅ₜ-sym p)

proof-irrelevanceRel : ∀ {Γ A t u l} ([A] : Γ ⊩⟨ l ⟩ A ^ %)
                   → Γ ⊩⟨ l ⟩ t ∷ A ^ % / [A]
                   → Γ ⊩⟨ l ⟩ u ∷ A ^ % / [A]
                   → Γ ⊩⟨ l ⟩ t ≡ u ∷ A ^ % / [A]
proof-irrelevanceRel (Emptyᵣ x)
                   (Emptyₜ k [ ⊢t , ⊢k , d ] k≅ (ne (neNfₜ neK _ k~)))
                   (Emptyₜ k₁ [ ⊢t₁ , ⊢k₁ , d₁ ] k₁≅ (ne (neNfₜ neK₁ _ k₁~))) =
  let irr~ = (~-irrelevance ⊢k ⊢k₁ k~ k₁~)
      irr≅ = ~-to-≅ₜ irr~
  in Emptyₜ₌ k k₁ [ ⊢t , ⊢k , d ] [ ⊢t₁ , ⊢k₁ , d₁ ] irr≅ (ne (neNfₜ₌ neK neK₁ irr~))
proof-irrelevanceRel (ne x)
                   (neₜ k [ ⊢t , ⊢k , d ] (neNfₜ neK _ k~))
                   (neₜ k₁ [ ⊢t₁ , ⊢k₁ , d₁ ] (neNfₜ neK₁ _ k₁~)) =
  let irr = ~-irrelevance ⊢k ⊢k₁ k~ k₁~
  in neₜ₌ k k₁ [ ⊢t , ⊢k , d ] [ ⊢t₁ , ⊢k₁ , d₁ ] (neNfₜ₌ neK neK₁ irr)
proof-irrelevanceRel {Γ} {l = l} (Πᵣ′ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext) [f] [f₁] =
  let Πₜ f d funcF _ _ f-app = [f]
      Πₜ f₁ d₁ funcF₁ _ _ f₁-app = [f₁]
      [ ⊢t , ⊢f , t⇨f ] = d
      [ ⊢t₁ , ⊢f₁ , t₁⇨f₁ ] = d₁
      irrWk : (∀ {ρ Δ a} → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
            → ([a] : Δ ⊩⟨ l ⟩ a ∷ U.wk ρ F ^ rF / [F] [ρ] ⊢Δ)
            → Δ ⊩⟨ l ⟩ U.wk ρ f ∘ a ≡ U.wk ρ f₁ ∘ a ∷ U.wk (lift ρ) G [ a ] ^ % / [G] [ρ] ⊢Δ [a])
      irrWk [ρ] ⊢Δ [a] =
        let f-a = f-app [ρ] ⊢Δ [a]
            f₁-a = f₁-app [ρ] ⊢Δ [a]
        in proof-irrelevanceRel ([G] [ρ] ⊢Δ [a]) f-a f₁-a
      irr≅η′ =
        let ⊢Δ = (wf ⊢F) ∙ ⊢F
            [F′] = [F] (step id) ⊢Δ
            ⊢a = var ⊢Δ here
            [a] = neuTerm [F′] (var 0) ⊢a (~-var ⊢a)
        in escapeTermEq ([G] (step id) ⊢Δ [a]) (irrWk (step id) ⊢Δ [a])
      irr≅η = PE.subst (λ Gx → _ ⊢ _ ≅ _ ∷ Gx ^ _) (wkSingleSubstId G) irr≅η′
      irr≅ = ≅-η-eq ⊢F ⊢f ⊢f₁ funcF funcF₁ irr≅η
  in Πₜ₌ f f₁ d d₁ funcF funcF₁ irr≅ [f] [f₁] irrWk
proof-irrelevanceRel (emb 0<1 [A]) [t] [u] = proof-irrelevanceRel [A] [t] [u]

proof-irrelevanceᵛ : ∀ {Γ A t u l} ([Γ] : ⊩ᵛ Γ) ([A] : Γ ⊩ᵛ⟨ l ⟩ A ^ % / [Γ])
                   → Γ ⊩ᵛ⟨ l ⟩ t ∷ A ^ % / [Γ] / [A]
                   → Γ ⊩ᵛ⟨ l ⟩ u ∷ A ^ % / [Γ] / [A]
                   → Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A ^ % / [Γ] / [A]
proof-irrelevanceᵛ [Γ] [A] [t] [u] {σ = σ} ⊢Δ [σ] =
  proof-irrelevanceRel (proj₁ ([A] ⊢Δ [σ])) (proj₁ ([t] ⊢Δ [σ])) (proj₁ ([u] ⊢Δ [σ]))
