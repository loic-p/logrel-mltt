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

record Σω₀ {ℓ} (A : Set ℓ) (B : A → Setω) : Setω where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

open Σω₀ public

record Σω₂ {ℓ} (A : Setω) (B : A → Set ℓ) : Setω where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

open Σω₂ public

record Σω₃ (A : Setω) (B : A → Setω) : Setω where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

open Σω₃ public

record Σω₄ (A : Setω₁) (B : A → Setω) : Setω₁ where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

open Σω₄ public

-- Existential quantification.

∃ : {ℓ ℓ′ : Level} → {A : Set ℓ} → (A → Set ℓ′) → Set (ℓ ⊔ ℓ′)
∃ = Σ _

∃₂ : {ℓ ℓ′ ℓ″ : Level} → {A : Set ℓ} {B : A → Set ℓ′}
     (C : (x : A) → B x → Set ℓ″) → Set (ℓ ⊔ ℓ′ ⊔ ℓ″)
∃₂ C = ∃ λ a → ∃ λ b → C a b

∃ω₃ : {A : Setω} → (A → Setω) → Setω
∃ω₃ = Σω₃ _

∃ω₃² : {A : Setω} {B : A → Setω}
     (C : (x : A) → B x → Setω) → Setω
∃ω₃² C = ∃ω₃ λ a → ∃ω₃ λ b → C a b

∃ω₄ : {A : Setω₁} → (A → Setω) → Setω₁
∃ω₄ = Σω₄ _

-- Cartesian product.

_×_ : {ℓ ℓ′ : Level} → (A : Set ℓ) → (B : Set ℓ′) → Set (ℓ ⊔ ℓ′)
A × B = Σ A (λ x → B)

_×ω₂_ : {ℓ : Level} → (A : Setω) → (B : Set ℓ) → Setω
A ×ω₂ B = Σω₂ A (λ x → B)

_×ω₃_ : (A : Setω) → (B : Setω) → Setω
A ×ω₃ B = Σω₃ A (λ x → B)
