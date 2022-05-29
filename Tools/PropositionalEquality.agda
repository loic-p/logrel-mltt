-- Martin-Löf identity type without the K axiom
-- (we do not assume uniqueness of identity proofs).

{-# OPTIONS --without-K --safe #-}

module Tools.PropositionalEquality where

-- We reexport Agda's builtin equality type.

open import Agda.Builtin.Equality public using (_≡_; refl)
open import Tools.Empty

-- Inequality.

infix 4 _≢_

_≢_ : {A : Set} → A → A → Set
a ≢ b = a ≡ b → ⊥

-- Symmetry.

sym : {ℓ : Agda.Primitive.Level} {A : Set ℓ} {a b : A} → a ≡ b → b ≡ a
sym refl = refl

-- Transitivity.

trans : {ℓ : Agda.Primitive.Level} {A : Set ℓ} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl refl = refl

-- Non-dependent congruence rules.

cong : {ℓ ℓ′ : Agda.Primitive.Level} {A : Set ℓ} {B : Set ℓ′} {a b : A} (f : A → B) → a ≡ b → f a ≡ f b
cong f refl = refl

cong₂ : ∀ {A B C : Set} {a a′ b b′}
        (f : A → B → C) → a ≡ a′ → b ≡ b′
      → f a b ≡ f a′ b′
cong₂ f refl refl = refl

cong₃ : ∀ {A B C D : Set} {a a′ b b′ c c′}
        (f : A → B → C → D) → a ≡ a′ → b ≡ b′ → c ≡ c′
      → f a b c ≡ f a′ b′ c′
cong₃ f refl refl refl = refl

cong₄ : ∀ {A B C D E : Set} {a a′ b b′ c c′ d d′}
        (f : A → B → C → D → E) → a ≡ a′ → b ≡ b′ → c ≡ c′ → d ≡ d′
      → f a b c d ≡ f a′ b′ c′ d′
cong₄ f refl refl refl refl = refl

-- Substitution (type-cast).

subst : {ℓ ℓ′ : Agda.Primitive.Level} {A : Set ℓ} {a b : A} (F : A → Set ℓ′) → a ≡ b → F a → F b
subst F refl f = f

J : {ℓ ℓ′ : Agda.Primitive.Level} {A : Set ℓ} {a : A} (F : (b : A) → a ≡ b → Set ℓ′) → F a refl → (b : A) → (e : a ≡ b) → F b e
J F t _ refl = t

-- Two substitutions simultaneously.

subst₂ : ∀ {A B : Set} {a a′ b b′} {ℓ : Agda.Primitive.Level} (F : A → B → Set ℓ)
       → a ≡ a′ → b ≡ b′ → F a b → F a′ b′
subst₂ F refl refl f = f

-- Three substitutions simultaneously.

subst₃ : ∀ {A B C : Set} {a a′ b b′ c c′} (F : A → B → C → Set)
       → a ≡ a′ → b ≡ b′ → c ≡ c′ → F a b c → F a′ b′ c′
subst₃ F refl refl refl f = f
