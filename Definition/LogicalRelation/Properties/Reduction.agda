{-# OPTIONS --without-K #-}

module Definition.LogicalRelation.Properties.Reduction where

open import Definition.Untyped as U
open import Definition.Typed
open import Definition.Typed.Weakening
open import Definition.Typed.Properties
open import Definition.Typed.RedSteps
open import Definition.LogicalRelation
open import Definition.LogicalRelation.ShapeView
open import Definition.LogicalRelation.Properties.Reflexivity
open import Definition.LogicalRelation.Properties.Symmetry
open import Definition.LogicalRelation.Properties.Transitivity
open import Definition.LogicalRelation.Properties.Conversion
open import Definition.LogicalRelation.Properties.Universe
open import Definition.LogicalRelation.Properties.Escape

open import Tools.Product
open import Tools.Empty

import Tools.PropositionalEquality as PE


-- Weak head expansion of reducible types.
redSubst* : ∀ {A B l Γ}
          → Γ ⊢ A ⇒* B
          → Γ ⊩⟨ l ⟩ B
          → ∃ λ ([A] : Γ ⊩⟨ l ⟩ A)
          → Γ ⊩⟨ l ⟩ A ≡ B / [A]
redSubst* D (U′ l′ l< ⊢Γ) rewrite redU* D =
  U (U l′ l< ⊢Γ) , PE.refl
redSubst* D (ℕ [ ⊢B , ⊢ℕ , D′ ]) =
  let ⊢A = redFirst* D
  in  ℕ ([ ⊢A , ⊢ℕ , D ⇨* D′ ]) , D′
redSubst* D (ne′ K [ ⊢B , ⊢K , D′ ] neK) =
  let ⊢A = redFirst* D
  in  (ne′ K [ ⊢A , ⊢K , D ⇨* D′ ] neK)
  ,   (ne₌ _ [ ⊢B , ⊢K , D′ ] neK (==-refl K))
redSubst* D (Π′ F G [ ⊢B , ⊢ΠFG , D′ ] TyΠ ⊢F ⊢G [F] [G] G-ext) =
  let ⊢A = redFirst* D
  in  (Π′ F G [ ⊢A , ⊢ΠFG , D ⇨* D′ ] TyΠ ⊢F ⊢G [F] [G] G-ext)
  ,   (Π₌ _ _ [ ⊢B , ⊢ΠFG , D′ ] TyΠ (==-refl _) (λ ρ ⊢Δ → reflEq ([F] ρ ⊢Δ))
        (λ ρ ⊢Δ [a] → reflEq ([G] ρ ⊢Δ [a])))
redSubst* D (emb 0<1 x) with redSubst* D x
redSubst* D (emb 0<1 x) | y , y₁ = emb 0<1 y , y₁

-- Weak head expansion of reducible terms.
redSubst*Term : ∀ {A t u l Γ}
              → Γ ⊢ t ⇒* u ∷ A
              → ([A] : Γ ⊩⟨ l ⟩ A)
              → Γ ⊩⟨ l ⟩ u ∷ A / [A]
              → Γ ⊩⟨ l ⟩ t ∷ A / [A]
              × Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A]
redSubst*Term t⇒u (U′ .⁰ 0<1 ⊢Γ) (Uₜ A [ ⊢t , ⊢u , d ] typeA [u]) =
  let [d]  = [ ⊢t , ⊢u , d ]
      [d′] = [ redFirst*Term t⇒u , ⊢u , t⇒u ⇨∷* d ]
      q = redSubst* (univ* t⇒u) (univEq (U′ ⁰ 0<1 ⊢Γ) (Uₜ A [d] typeA [u]))
  in Uₜ A [d′] typeA (proj₁ q)
  ,  Uₜ₌ A A [d′] [d] typeA typeA (refl ⊢u) (proj₁ q) [u] (proj₂ q)
redSubst*Term t⇒u (ℕ D) (ℕₜ n [ ⊢u , ⊢n , d ] prop) =
  let A≡ℕ  = subset* (red D)
      ⊢t   = conv (redFirst*Term t⇒u) A≡ℕ
      t⇒u′ = conv* t⇒u A≡ℕ
  in  ℕₜ n [ ⊢t , ⊢n , t⇒u′ ⇨∷* d ] prop
  ,   ℕₜ₌ n n [ ⊢t , ⊢n , t⇒u′ ⇨∷* d ] [ ⊢u , ⊢n , d ]
          prop prop (==-refl n)
redSubst*Term t⇒u (ne′ K D neK) (neₜ k [ ⊢t , ⊢u , d ] (neNfₜ neK₁ ⊢k)) =
  let A≡K  = subset* (red D)
      [d]  = [ ⊢t , ⊢u , d ]
      [d′] = [ conv (redFirst*Term t⇒u) A≡K , ⊢u , conv* t⇒u A≡K ⇨∷* d ]
  in  neₜ k [d′] (neNfₜ neK₁ ⊢k) , neₜ₌ k k [d′] [d] (neNfₜ₌ neK₁ neK₁ (==-refl k))
redSubst*Term {A} {t} {u} {l} {Γ} t⇒u (Π′ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                  (Πₜ f [ ⊢t , ⊢u , d ] funcF [f] [f]₁) =
  let A≡ΠFG = subset* (red D)
      t⇒u′  = conv* t⇒u A≡ΠFG
      [d]  = [ ⊢t , ⊢u , d ]
      [d′] = [ conv (redFirst*Term t⇒u) A≡ΠFG , ⊢u , conv* t⇒u A≡ΠFG ⇨∷* d ]
  in  Πₜ f [d′] funcF [f] [f]₁
  ,   Πₜ₌ f f [d′] [d] funcF funcF (==-refl f) (refl ⊢u)
          (Πₜ f [d′] funcF [f] [f]₁)
          (Πₜ f [d] funcF [f] [f]₁)
          (λ [ρ] ⊢Δ [a] → reflEqTerm ([G] [ρ] ⊢Δ [a]) ([f]₁ [ρ] ⊢Δ [a]))
redSubst*Term t⇒u (emb 0<1 x) [u] = redSubst*Term t⇒u x [u]

-- Weak head expansion of reducible types with single reduction step.
redSubst : ∀ {A B l Γ}
         → Γ ⊢ A ⇒ B
         → Γ ⊩⟨ l ⟩ B
         → ∃ λ ([A] : Γ ⊩⟨ l ⟩ A)
         → Γ ⊩⟨ l ⟩ A ≡ B / [A]
redSubst A⇒B [B] = redSubst* (A⇒B ⇨ id (escape [B])) [B]

-- Weak head expansion of reducible terms with single reduction step.
redSubstTerm : ∀ {A t u l Γ}
             → Γ ⊢ t ⇒ u ∷ A
             → ([A] : Γ ⊩⟨ l ⟩ A)
             → Γ ⊩⟨ l ⟩ u ∷ A / [A]
             → Γ ⊩⟨ l ⟩ t ∷ A / [A]
             × Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A]
redSubstTerm t⇒u [A] [u] = redSubst*Term (t⇒u ⇨ id (escapeTerm [A] [u])) [A] [u]
