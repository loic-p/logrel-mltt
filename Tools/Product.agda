-- Σ type (also used as existential) and
-- cartesian product (also used as conjunction).

{-# OPTIONS --without-K --safe #-}

module Tools.Product where

open import Agda.Primitive

infixr 4 _,_
infixr 2 _×_

-- Dependent pair type (aka dependent sum, Σ type).

record Σ {ℓ ℓ′ : Level} (A : Set ℓ) (B : A → Set ℓ′) : Set (ℓ ⊔ ℓ′) where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

open Σ public

-- Existential quantification.

∃ : {ℓ ℓ′ : Level} → {A : Set ℓ} → (A → Set ℓ′) → Set (ℓ ⊔ ℓ′)
∃ = Σ _

∃₂ : {ℓ ℓ′ ℓ″ : Level} → {A : Set ℓ} {B : A → Set ℓ′}
     (C : (x : A) → B x → Set ℓ″) → Set (ℓ ⊔ ℓ′ ⊔ ℓ″)
∃₂ C = ∃ λ a → ∃ λ b → C a b

-- Cartesian product.

_×_ : {ℓ ℓ′ : Level} → (A : Set ℓ) → (B : Set ℓ′) → Set (ℓ ⊔ ℓ′)
A × B = Σ A (λ x → B)
