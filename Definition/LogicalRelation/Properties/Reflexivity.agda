{-# OPTIONS --without-K --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Properties.Reflexivity {{eqrel : EqRelSet}} where

open import Definition.Untyped
open import Definition.Typed
open import Definition.LogicalRelation

open import Tools.Embedding
open import Tools.Product
import Tools.PropositionalEquality as PE


-- Reflexivity of reducible types.
reflEq : ∀ {l Γ A} ([A] : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l ⟩ A ≡ A / [A]
reflEq (Uᵣ′ l′ l< ⊢Γ) = (U₌ PE.refl)
reflEq (ℕᵣ D) = ιx (ℕ₌ (red D))
reflEq (ne′ K [ ⊢A , ⊢B , D ] neK K≡K) =
  ιx (ne₌ _ [ ⊢A , ⊢B , D ] neK K≡K)
reflEq (Πᵣ′ F G [ ⊢A , ⊢B , D ] ⊢F ⊢G A≡A [F] [G] G-ext) =
  Π₌ _ _ D A≡A
     (λ ρ ⊢Δ → reflEq ([F] ρ ⊢Δ))
     (λ ρ ⊢Δ [a] → reflEq ([G] ρ ⊢Δ [a]))
reflEq (emb′ 0<1 [A]) = ιx (reflEq [A])

reflNatural-prop : ∀ {Γ n}
                 → Natural-prop Γ n
                 → [Natural]-prop Γ n n
reflNatural-prop (sucᵣ (ℕₜ n d t≡t prop)) =
  sucᵣ (ℕₜ₌ n n d d t≡t
            (reflNatural-prop prop))
reflNatural-prop zeroᵣ = zeroᵣ
reflNatural-prop (ne (neNfₜ neK ⊢k k≡k)) = ne (neNfₜ₌ neK neK k≡k)

-- Reflexivity of reducible terms.
reflEqTerm : ∀ {l Γ A t} ([A] : Γ ⊩⟨ l ⟩ A)
           → Γ ⊩⟨ l ⟩ t ∷ A / [A]
           → Γ ⊩⟨ l ⟩ t ≡ t ∷ A / [A]
reflEqTerm (Uᵣ′ ⁰ 0<1 ⊢Γ) (Uₜ A d typeA A≡A [A]) =
  Uₜ₌ A A d d typeA typeA A≡A [A] [A] (reflEq [A])
reflEqTerm (ℕᵣ D) (ιx (ℕₜ n [ ⊢t , ⊢u , d ] t≡t prop)) =
  ιx (ℕₜ₌ n n [ ⊢t , ⊢u , d ] [ ⊢t , ⊢u , d ] t≡t
      (reflNatural-prop prop))
reflEqTerm (ne′ K D neK K≡K) (ιx (neₜ k d (neNfₜ neK₁ ⊢k k≡k))) =
  ιx (neₜ₌ k k d d (neNfₜ₌ neK₁ neK₁ k≡k))
reflEqTerm (Πᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Πₜ f d funcF f≡f [f] [f]₁) =
  Πₜ₌ f f d d funcF funcF f≡f
      (Πₜ f d funcF f≡f [f] [f]₁)
      (Πₜ f d funcF f≡f [f] [f]₁)
      (λ ρ ⊢Δ [a] → [f] ρ ⊢Δ [a] [a] (reflEqTerm ([F] ρ ⊢Δ) [a]))
reflEqTerm (emb′ 0<1 [A]) (ιx t) = ιx (reflEqTerm [A] t)
