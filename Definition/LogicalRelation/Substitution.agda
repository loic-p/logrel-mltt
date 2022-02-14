{-# OPTIONS --without-K --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution {{eqrel : EqRelSet}} where

open import Definition.Untyped
open import Definition.Typed
open import Definition.LogicalRelation

open import Tools.Product
open import Tools.Unit

record ⊤′ : Set₂ where
  instance constructor tt

-- since having a reducibility where the universe level depends
-- on l introduces a lot of problems, we need to have this equivalent
-- reducibility notion where the universe level is determined.

data _⊩³⟨_⟩_ (Γ : Con Term) : (l : TypeLevel) → (A : Term) → Set₃ where
  ι⁰ : ∀ {A} → Γ ⊩⟨ ⁰ ⟩ A → Γ ⊩³⟨ ⁰ ⟩ A
  ι¹ : ∀ {A} → Γ ⊩⟨ ¹ ⟩ A → Γ ⊩³⟨ ¹ ⟩ A

_⊩³⟨_⟩_∷_/_ : (Γ : Con Term) → (l : TypeLevel) → (t : Term) → (A : Term) → Γ ⊩³⟨ l ⟩ A → Set₂
Γ ⊩³⟨ ⁰ ⟩ t ∷ A / ι⁰ [A] = ι (Γ ⊩⟨ ⁰ ⟩ t ∷ A / [A])
Γ ⊩³⟨ ¹ ⟩ t ∷ A / ι¹ [A] = Γ ⊩⟨ ¹ ⟩ t ∷ A / [A]

_⊩³⟨_⟩_≡_/_ : (Γ : Con Term) → (l : TypeLevel) → (A : Term) → (B : Term) → Γ ⊩³⟨ l ⟩ A → Set₂
Γ ⊩³⟨ ⁰ ⟩ A ≡ B / ι⁰ [A] = ι (Γ ⊩⟨ ⁰ ⟩ A ≡ B / [A])
Γ ⊩³⟨ ¹ ⟩ A ≡ B / ι¹ [A] = Γ ⊩⟨ ¹ ⟩ A ≡ B / [A]

_⊩³⟨_⟩_≡_∷_/_ : (Γ : Con Term) → (l : TypeLevel) → (t u A : Term) → Γ ⊩³⟨ l ⟩ A → Set₂
Γ ⊩³⟨ ⁰ ⟩ t ≡ u ∷ A / ι⁰ [A] = ι (Γ ⊩⟨ ⁰ ⟩ t ≡ u ∷ A / [A])
Γ ⊩³⟨ ¹ ⟩ t ≡ u ∷ A / ι¹ [A] = Γ ⊩⟨ ¹ ⟩ t ≡ u ∷ A / [A]

out3 : ∀ {Γ l A} → Γ ⊩³⟨ l ⟩ A → Γ ⊩⟨ l ⟩ A
out3 (ι⁰ x) = x
out3 (ι¹ x) = x

out3Eq : ∀ {Γ l A B [A]} → Γ ⊩³⟨ l ⟩ A ≡ B / [A] → Γ ⊩⟨ l ⟩ A ≡ B / out3 [A]
out3Eq {[A] = ι⁰ [A]} (ιx [A≡B]) = [A≡B]
out3Eq {[A] = ι¹ [A]} [A≡B] = [A≡B]

out3Term : ∀ {Γ l A t [A]} → Γ ⊩³⟨ l ⟩ t ∷ A / [A] → Γ ⊩⟨ l ⟩ t ∷ A / out3 [A]
out3Term {[A] = ι⁰ [A]} (ιx [t]) = [t]
out3Term {[A] = ι¹ [A]} [t] = [t]

out3EqTerm : ∀ {Γ l A t u [A]} → Γ ⊩³⟨ l ⟩ t ≡ u ∷ A / [A] → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / out3 [A]
out3EqTerm {[A] = ι⁰ [A]} (ιx [t≡u]) = [t≡u]
out3EqTerm {[A] = ι¹ [A]} [t≡u] = [t≡u]

in3 : ∀ {Γ l A} →  Γ ⊩⟨ l ⟩ A → Γ ⊩³⟨ l ⟩ A
in3 {l = ⁰} [Γ] = ι⁰ [Γ]
in3 {l = ¹} [Γ] = ι¹ [Γ]

in3Eq : ∀ {Γ l A B [A]} → Γ ⊩⟨ l ⟩ A ≡ B / [A] → Γ ⊩³⟨ l ⟩ A ≡ B / in3 [A]
in3Eq {l = ⁰} [A≡B] = ιx [A≡B]
in3Eq {l = ¹} [A≡B] = [A≡B]

in3Term : ∀ {Γ l A t [A]} → Γ ⊩⟨ l ⟩ t ∷ A / [A] → Γ ⊩³⟨ l ⟩ t ∷ A / in3 [A]
in3Term {l = ⁰} [t] = ιx [t]
in3Term {l = ¹} [t] = [t]

in3EqTerm : ∀ {Γ l A t u [A]} → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A] → Γ ⊩³⟨ l ⟩ t ≡ u ∷ A / in3 [A]
in3EqTerm {l = ⁰} [t≡u] = ιx [t≡u]
in3EqTerm {l = ¹} [t≡u] = [t≡u]

data ι″ {ℓ} (A : Set ℓ) : Agda.Primitive.Setω where
  ιx : A → ι″ A

-- The validity judgements:
-- We consider expressions that satisfy these judgments valid

ValRel : Set₄
ValRel = (Γ : Con Term) → (⊩Subst : (Δ : Con Term) → Subst → ⊢ Δ → Set₂)
    → (⊩EqSubst : (Δ : Con Term) → (σ σ′ : Subst) → (⊢Δ : ⊢ Δ) → (⊩Subst Δ σ ⊢Δ) → Set₂)
    → Set₃

record ⊩ᵛ⁰_/_ (Γ : Con Term) (_⊩_▸_ : ValRel) : Set₃ where
  inductive
  eta-equality
  constructor VPack
  field
    ⊩Subst : (Δ : Con Term) → Subst → ⊢ Δ → Set₂
    ⊩EqSubst : (Δ : Con Term) → (σ σ′ : Subst) → (⊢Δ : ⊢ Δ) → (⊩Subst Δ σ ⊢Δ) → Set₂
    ⊩V : Γ ⊩ ⊩Subst ▸ ⊩EqSubst

_⊩ˢ⁰_∷_/_/_ : {R : ValRel} (Δ : Con Term) (σ : Subst) (Γ : Con Term) ([Γ] : ⊩ᵛ⁰ Γ / R) (⊢Δ : ⊢ Δ)
           → Set₂
Δ ⊩ˢ⁰ σ ∷ Γ / VPack ⊩Subst ⊩EqSubst ⊩V / ⊢Δ = ⊩Subst Δ σ ⊢Δ

_⊩ˢ⁰_≡_∷_/_/_/_ : {R : ValRel} (Δ : Con Term) (σ σ′ : Subst) (Γ : Con Term) ([Γ] : ⊩ᵛ⁰ Γ / R)
                 (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ˢ⁰ σ ∷ Γ / [Γ] / ⊢Δ) → Set₂
Δ ⊩ˢ⁰ σ ≡ σ′ ∷ Γ / VPack ⊩Subst ⊩EqSubst ⊩V / ⊢Δ / [σ] = ⊩EqSubst Δ σ σ′ ⊢Δ [σ]

-- Validity of types
_⊩ᵛ⁰⟨_⟩_/_ : {R : ValRel} (Γ : Con Term) (l : TypeLevel) (A : Term) → ⊩ᵛ⁰ Γ / R → Set₃
_⊩ᵛ⁰⟨_⟩_/_ Γ l A [Γ] =
  ∀ {Δ σ} (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ˢ⁰ σ ∷ Γ / [Γ] / ⊢Δ)
  → Σ (Δ ⊩³⟨ l ⟩ subst σ A) (λ [Aσ]
    → ∀ {σ′} ([σ′] : Δ ⊩ˢ⁰ σ′ ∷ Γ / [Γ] / ⊢Δ)
      ([σ≡σ′] : Δ ⊩ˢ⁰ σ ≡ σ′ ∷ Γ / [Γ] / ⊢Δ / [σ])
    → Δ ⊩³⟨ l ⟩ subst σ A ≡ subst σ′ A / [Aσ])

data _⊩V_▸_ : ValRel where
  Vε : ε
    ⊩V (λ Δ σ ⊢Δ → ⊤′)
    ▸ (λ Δ σ σ′ ⊢Δ [σ] → ⊤′)
  V∙ : ∀ {Γ A l}
    → ([Γ] : ⊩ᵛ⁰ Γ / _⊩V_▸_)
    → ([A] : Γ ⊩ᵛ⁰⟨ l ⟩ A / [Γ])
    → Γ ∙ A
        ⊩V (λ Δ σ ⊢Δ → Σ (Δ ⊩ˢ⁰ tail σ ∷ Γ / [Γ] / ⊢Δ)
                         (λ [tailσ] → (Δ ⊩³⟨ l ⟩ head σ ∷ subst (tail σ) A / proj₁ ([A] ⊢Δ [tailσ]))))
        ▸ (λ Δ σ σ′ ⊢Δ [σ] → (Δ ⊩ˢ⁰ tail σ ≡ tail σ′ ∷ Γ / [Γ] / ⊢Δ / proj₁ [σ]) ×
             (Δ ⊩³⟨ l ⟩ head σ ≡ head σ′ ∷ subst (tail σ) A / proj₁ ([A] ⊢Δ (proj₁ [σ]))))

⊩ᵛ : Con Term → Set₃
⊩ᵛ Γ = ⊩ᵛ⁰ Γ / _⊩V_▸_

_⊩ˢ_∷_/_/_ : (Δ : Con Term) (σ : Subst) (Γ : Con Term) ([Γ] : ⊩ᵛ Γ) (⊢Δ : ⊢ Δ)
           → Set₂
Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ = Δ ⊩ˢ⁰ σ ∷ Γ / [Γ] / ⊢Δ

_⊩ˢ_≡_∷_/_/_/_ : (Δ : Con Term) (σ σ′ : Subst) (Γ : Con Term) ([Γ] : ⊩ᵛ Γ)
                 (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ) → Set₂
Δ ⊩ˢ σ ≡ σ′ ∷ Γ / [Γ] / ⊢Δ / [σ] = Δ ⊩ˢ⁰ σ ≡ σ′ ∷ Γ / [Γ] / ⊢Δ / [σ]

-- Validity of types
_⊩ᵛ⟨_⟩_/_ : (Γ : Con Term) (l : TypeLevel) (A : Term) → ⊩ᵛ Γ → Set₃
Γ ⊩ᵛ⟨ l ⟩ A / [Γ] = Γ ⊩ᵛ⁰⟨ l ⟩ A / [Γ]

-- Validity of terms
_⊩ᵛ⟨_⟩_∷_/_/_ : (Γ : Con Term) (l : TypeLevel) (t A : Term) ([Γ] : ⊩ᵛ Γ)
                 ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ]) → Set₂
Γ ⊩ᵛ⟨ l ⟩ t ∷ A / [Γ] / [A] =
  ∀ {Δ σ} (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ) →
  Σ (Δ ⊩³⟨ l ⟩ subst σ t ∷ subst σ A / proj₁ ([A] ⊢Δ [σ])) λ [tσ] →
  ∀ {σ′} → Δ ⊩ˢ σ′ ∷ Γ / [Γ] / ⊢Δ → Δ ⊩ˢ σ ≡ σ′ ∷ Γ / [Γ] / ⊢Δ / [σ]
    → Δ ⊩³⟨ l ⟩ subst σ t ≡ subst σ′ t ∷ subst σ A / proj₁ ([A] ⊢Δ [σ])

-- Validity of type equality
_⊩ᵛ⟨_⟩_≡_/_/_ : (Γ : Con Term) (l : TypeLevel) (A B : Term) ([Γ] : ⊩ᵛ Γ)
                ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ]) → Set₂
Γ ⊩ᵛ⟨ l ⟩ A ≡ B / [Γ] / [A] =
  ∀ {Δ σ} (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
  → Δ ⊩³⟨ l ⟩ subst σ A ≡ subst σ B / proj₁ ([A] ⊢Δ [σ])

-- Validity of term equality
_⊩ᵛ⟨_⟩_≡_∷_/_/_ : (Γ : Con Term) (l : TypeLevel) (t u A : Term) ([Γ] : ⊩ᵛ Γ)
                    ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ]) → Set₂
Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A / [Γ] / [A] =
  ∀ {Δ σ} → (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
          → Δ ⊩³⟨ l ⟩ subst σ t ≡ subst σ u ∷ subst σ A / proj₁ ([A] ⊢Δ [σ])

-- Valid term equality with validity of its type and terms
record [_⊩ᵛ⟨_⟩_≡_∷_/_] (Γ : Con Term) (l : TypeLevel)
                       (t u A : Term) ([Γ] : ⊩ᵛ Γ) : Set₃ where
  constructor modelsTermEq
  field
    [A]   : Γ ⊩ᵛ⟨ l ⟩ A / [Γ]
    [t]   : Γ ⊩ᵛ⟨ l ⟩ t ∷ A / [Γ] / [A]
    [u]   : Γ ⊩ᵛ⟨ l ⟩ u ∷ A / [Γ] / [A]
    [t≡u] : Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A / [Γ] / [A]

-- Validity of reduction of terms
_⊩ᵛ_⇒_∷_/_ : (Γ : Con Term) (t u A : Term) ([Γ] : ⊩ᵛ Γ) → Set₂
Γ ⊩ᵛ t ⇒ u ∷ A / [Γ] = ∀ {Δ σ} (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
                       → Δ ⊢ subst σ t ⇒ subst σ u ∷ subst σ A
