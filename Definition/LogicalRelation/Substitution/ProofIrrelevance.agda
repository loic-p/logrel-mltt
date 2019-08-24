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

proof-irrelevance′ : ∀ {Γ A t u l} ([A] : Γ ⊩⟨ l ⟩ A ^ %)
                   → Γ ⊩⟨ l ⟩ t ≡ t ∷ A ^ % / [A]
                   → Γ ⊩⟨ l ⟩ u ≡ u ∷ A ^ % / [A]
                   → Γ ⊩⟨ l ⟩ t ≡ u ∷ A ^ % / [A]
proof-irrelevance′ (Emptyᵣ x)
                   (Emptyₜ₌ k _ [ ⊢t , ⊢k , d ] _ k≅ (ne (neNfₜ₌ neK _ k~)))
                   (Emptyₜ₌ k₁ _ [ ⊢t₁ , ⊢k₁ , d₁ ] _ k₁≅ (ne (neNfₜ₌ neK₁ _ k₁~))) =
  let irr~ = (~-irrelevance ⊢k ⊢k₁ (~-quasirefl k~) (~-quasirefl k₁~))
      irr≅ = ~-to-≅ₜ irr~
  in Emptyₜ₌ k k₁ [ ⊢t , ⊢k , d ] [ ⊢t₁ , ⊢k₁ , d₁ ] irr≅ (ne (neNfₜ₌ neK neK₁ irr~))
proof-irrelevance′ (ne x)
                   (neₜ₌ k _ [ ⊢t , ⊢k , d ] _ (neNfₜ₌ neK _ k~))
                   (neₜ₌ k₁ _ [ ⊢t₁ , ⊢k₁ , d₁ ] _ (neNfₜ₌ neK₁ _ k₁~)) =
  let irr = ~-irrelevance ⊢k ⊢k₁ (~-quasirefl k~) (~-quasirefl k₁~)
  in neₜ₌ k k₁ [ ⊢t , ⊢k , d ] [ ⊢t₁ , ⊢k₁ , d₁ ] (neNfₜ₌ neK neK₁ irr)
proof-irrelevance′ {Γ} {l = l} (Πᵣ′ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Πₜ₌ f _ d _ funcF _ f≡g [f] _ [f≡g]) (Πₜ₌ f₁ _ d₁ _ funcF₁ _ f₁≡g₁ [f₁] _ [f₁≡g₁]) =
  let [ ⊢t , ⊢f , t⇨f ] = d
      [ ⊢t₁ , ⊢f₁ , t₁⇨f₁ ] = d₁
      Πₜ f′ [ _ , ⊢d′ , t⇨f′ ] funcF′ _ f′-ext _ = [f]
      f′≡f = whrDet*Term (t⇨f′ , functionWhnf funcF′) (t⇨f , functionWhnf funcF)
      Πₜ f₁′ [ _ , ⊢d₁′ , t₁⇨f₁′ ] funcF₁′ _ f₁′-ext _ = [f₁]
      f₁′≡f₁ = whrDet*Term (t₁⇨f₁′ , functionWhnf funcF₁′) (t₁⇨f₁ , functionWhnf funcF₁)
      irrWk : (∀ {ρ Δ a} → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
            → ([a] : Δ ⊩⟨ l ⟩ a ∷ U.wk ρ F ^ rF / [F] [ρ] ⊢Δ)
            → Δ ⊩⟨ l ⟩ U.wk ρ f ∘ a ≡ U.wk ρ f₁ ∘ a ∷ U.wk (lift ρ) G [ a ] ^ % / [G] [ρ] ⊢Δ [a])
      irrWk [ρ] ⊢Δ [a] =
        let f′-a = f′-ext [ρ] ⊢Δ [a] [a] (reflEqTerm ([F] [ρ] ⊢Δ) [a])
            f-a = PE.subst _ f′≡f f′-a
            f₁′-a = f₁′-ext [ρ] ⊢Δ [a] [a] (reflEqTerm ([F] [ρ] ⊢Δ) [a])
            f₁-a = PE.subst _ f₁′≡f₁ f₁′-a
        in proof-irrelevance′ ([G] [ρ] ⊢Δ [a]) f-a f₁-a
      irr≅η′ =
        let ⊢Δ = (wf ⊢F) ∙ ⊢F
            [F′] = [F] (step id) ⊢Δ
            ⊢a = var ⊢Δ here
            [a] = neuTerm [F′] (var 0) ⊢a (~-var ⊢a)
        in escapeTermEq ([G] (step id) ⊢Δ [a]) (irrWk (step id) ⊢Δ [a])
      irr≅η = PE.subst (λ Gx → _ ⊢ _ ≅ _ ∷ Gx ^ _) (wkSingleSubstId G) irr≅η′
      irr≅ = ≅-η-eq ⊢F ⊢f ⊢f₁ funcF funcF₁ irr≅η
  in Πₜ₌ f f₁ d d₁ funcF funcF₁ irr≅ [f] [f₁] irrWk
proof-irrelevance′ (emb 0<1 [A]) [t] [u] = proof-irrelevance′ [A] [t] [u]

proof-irrelevanceRel : ∀ {Γ A t u l} ([A] : Γ ⊩⟨ l ⟩ A ^ %)
                   → Γ ⊩⟨ l ⟩ t ∷ A ^ % / [A]
                   → Γ ⊩⟨ l ⟩ u ∷ A ^ % / [A]
                   → Γ ⊩⟨ l ⟩ t ≡ u ∷ A ^ % / [A]
proof-irrelevanceRel [A] [t] [u] = proof-irrelevance′ [A] (reflEqTerm [A] [t]) (reflEqTerm [A] [u])

proof-irrelevanceᵛ : ∀ {Γ A t u l} ([Γ] : ⊩ᵛ Γ) ([A] : Γ ⊩ᵛ⟨ l ⟩ A ^ % / [Γ])
                   → Γ ⊩ᵛ⟨ l ⟩ t ∷ A ^ % / [Γ] / [A]
                   → Γ ⊩ᵛ⟨ l ⟩ u ∷ A ^ % / [Γ] / [A]
                   → Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A ^ % / [Γ] / [A]
proof-irrelevanceᵛ [Γ] [A] [t] [u] {σ = σ} ⊢Δ [σ] =
  proof-irrelevanceRel (proj₁ ([A] ⊢Δ [σ])) (proj₁ ([t] ⊢Δ [σ])) (proj₁ ([u] ⊢Δ [σ]))
