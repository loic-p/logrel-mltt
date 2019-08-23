{-# OPTIONS --without-K --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Properties.ProofIrrelevance {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.Weakening
open import Definition.LogicalRelation
open import Definition.LogicalRelation.ShapeView
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties.Reflexivity
open import Definition.LogicalRelation.Properties.Escape
open import Definition.LogicalRelation.Properties.Symmetry
open import Definition.LogicalRelation.Properties.Neutral

open import Tools.Product
import Tools.PropositionalEquality as PE

~-quasirefl : ∀ {Γ n n′ A r} → Γ ⊢ n ~ n′ ∷ A ^ r → Γ ⊢ n ~ n ∷ A ^ r
~-quasirefl p = ~-trans p (~-sym p)

proof-irrelevanceEq′ : ∀ {Γ A t u l} ([A] : Γ ⊩⟨ l ⟩ A ^ %)
       → Γ ⊩⟨ l ⟩ t ≡ t ∷ A ^ % / [A]
       → Γ ⊩⟨ l ⟩ u ≡ u ∷ A ^ % / [A]
       → Γ ⊩⟨ l ⟩ t ≡ u ∷ A ^ % / [A]
proof-irrelevanceEq′ {t = t} {u = u} (Emptyᵣ D) (Emptyₜ₌ k k′ [ ⊢t , ⊢k , d ] d′ k≡k (ne (neNfₜ₌ neK neK′ k~k′)))
                               (Emptyₜ₌ k₁ k₁′ [ ⊢t₁ , ⊢k₁ , d₁ ] d₁′ k≡k₁ (ne (neNfₜ₌ neK₁ neK₁′ k₁~k₁′))) =
  let irr = ~-irrelevance (~-quasirefl k~k′) (~-quasirefl k₁~k₁′) in
  Emptyₜ₌ k k₁ [ ⊢t , ⊢k , d ] [ ⊢t₁ , ⊢k₁ , d₁ ] (~-to-≅ₜ irr) (ne (neNfₜ₌ neK neK₁ irr))
proof-irrelevanceEq′ (ne′ K D neK K≡K) (neₜ₌ k k′ [ ⊢t , ⊢k , d ] d′ (neNfₜ₌ neK₁ ⊢k′ k~k′))
                                      (neₜ₌ k₁ k₁′ [ ⊢t₁ , ⊢k₁ , d₁ ] d₁′ (neNfₜ₌ neK₂ ⊢k₁′ k₁~k₁′)) =
  let irr = ~-irrelevance (~-quasirefl k~k′) (~-quasirefl k₁~k₁′) in
  neₜ₌ k k₁ [ ⊢t , ⊢k , d ] [ ⊢t₁ , ⊢k₁ , d₁ ] (neNfₜ₌ neK₁ neK₂ irr)
proof-irrelevanceEq′ (Πᵣ′ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                     (Πₜ₌ .(lam f) f′ [ ⊢t , ⊢f , d ] d′ (lamₙ {t = f}) funcF′ f≡f f′≡f′ [f] [f]₁)
                     (Πₜ₌ .(lam f₁) f₁′ [ ⊢t₁ , ⊢f₁ , d₁ ] d₁′ (lamₙ {t = f₁}) funcF₁′ f₁≡f₁ f₁′≡f₁′ [f₁] [f₁]₁) = {!!}
proof-irrelevanceEq′ (Πᵣ′ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                     (Πₜ₌ .(lam f) f′ [ ⊢t , ⊢f , d ] d′ (lamₙ {t = f}) funcF′ f≡f f′≡f′ [f] [f]₁)
                     (Πₜ₌ f₁ f₁′ [ ⊢t₁ , ⊢f₁ , d₁ ] d₁′ (ne neF₁) funcF₁′ f₁≡f₁ f₁′≡f₁′ [f₁] [f₁]₁) = {!!}
proof-irrelevanceEq′ (Πᵣ′ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                     (Πₜ₌ f f′ [ ⊢t , ⊢f , d ] d′ (ne neF) funcF′ f≡f f′≡f′ [f] [f]₁)
                     (Πₜ₌ .(lam f₁) f₁′ [ ⊢t₁ , ⊢f₁ , d₁ ] d₁′ (lamₙ {t = f₁}) funcF₁′ f₁≡f₁ f₁′≡f₁′ [f₁] [f₁]₁) = {!!}
proof-irrelevanceEq′ (Πᵣ′ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                     (Πₜ₌ f f′ [ ⊢t , ⊢f , d ] d′ (ne neF) funcF′ f≡f f′≡f′ [f] [f]₁)
                     (Πₜ₌ f₁ f₁′ [ ⊢t₁ , ⊢f₁ , d₁ ] d₁′ (ne neF₁) funcF₁′ f₁≡f₁ f₁′≡f₁′ [f₁] [f₁]₁) =
  let irr = ~-irrelevance {!!} {!!} in
  Πₜ₌ f f₁ [ ⊢t , ⊢f , d ] [ ⊢t₁ , ⊢f₁ , d₁ ] (ne neF) (ne neF₁) {!!} [f] [f₁] {!!}
proof-irrelevanceEq′ (emb 0<1 [A]) [t] [u] = proof-irrelevanceEq′ [A] [t] [u]

proof-irrelevanceEq : ∀ {Γ A t u l} ([A] : Γ ⊩⟨ l ⟩ A ^ %)
       → Γ ⊩⟨ l ⟩ t ∷ A ^ % / [A]
       → Γ ⊩⟨ l ⟩ u ∷ A ^ % / [A]
       → Γ ⊩⟨ l ⟩ t ≡ u ∷ A ^ % / [A]
proof-irrelevanceEq [A] [t] [u] = proof-irrelevanceEq′ [A] (reflEqTerm [A] [t]) (reflEqTerm [A] [u])
