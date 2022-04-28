{-# OPTIONS --without-K #-}

module Definition.LogicalRelation.Properties.Reflexivity where

open import Definition.Untyped
open import Definition.Typed
open import Definition.LogicalRelation

open import Tools.Product
import Tools.PropositionalEquality as PE


-- Reflexivity of reducible types.
reflEq : ∀ {l Γ A} ([A] : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l ⟩ A ≡ A / [A]
reflEq (U′ l′ l< ⊢Γ) = PE.refl
reflEq (ℕ D) = red D
reflEq (ne′ K [ ⊢A , ⊢B , D ] neK) =
  ne₌ _ [ ⊢A , ⊢B , D ] neK (==-refl K)
reflEq (Π′ F G [ ⊢A , ⊢B , D ] typeΠ ⊢F ⊢G [F] [G] G-ext) =
  Π₌ _ _ D typeΠ (refl (Π ⊢F ▹ ⊢G))
     (λ ρ ⊢Δ → reflEq ([F] ρ ⊢Δ))
     (λ ρ ⊢Δ [a] → reflEq ([G] ρ ⊢Δ [a]))
reflEq (emb 0<1 [A]) = reflEq [A]

-- Reflexivity of reducible terms.
reflEqTerm : ∀ {l Γ A t} ([A] : Γ ⊩⟨ l ⟩ A)
           → Γ ⊩⟨ l ⟩ t ∷ A / [A]
           → Γ ⊩⟨ l ⟩ t ≡ t ∷ A / [A]
reflEqTerm (U′ ⁰ 0<1 ⊢Γ) (Uₜ A [ ⊢t , ⊢u , d ] typeA [A]) =
  Uₜ₌ A A [ ⊢t , ⊢u , d ] [ ⊢t , ⊢u , d ] typeA typeA (refl ⊢u) [A] [A] (reflEq [A])
reflEqTerm (ℕ D) (ℕₜ n [ ⊢t , ⊢u , d ] prop) =
  ℕₜ₌ n n [ ⊢t , ⊢u , d ] [ ⊢t , ⊢u , d ] prop prop (==-refl n)
reflEqTerm (ne′ K D neK) (neₜ k d (neNfₜ neK₁ ⊢k)) =
  neₜ₌ k k d d (neNfₜ₌ neK₁ neK₁ (==-refl k))
reflEqTerm (Π′ F G D typeΠ ⊢F ⊢G [F] [G] G-ext) (Πₜ f d funcF [f] [f]₁) =
  let [ _ , ⊢f , _ ] = d in
  Πₜ₌ f f d d funcF funcF (==-refl f) (refl ⊢f)
      (Πₜ f d funcF [f] [f]₁)
      (Πₜ f d funcF [f] [f]₁)
      (λ ρ ⊢Δ [a] → [f] ρ ⊢Δ [a] [a] (reflEqTerm ([F] ρ ⊢Δ) [a]))
reflEqTerm (emb 0<1 [A]) t = reflEqTerm [A] t
