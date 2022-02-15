{-# OPTIONS --without-K --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution {{eqrel : EqRelSet}} where

open import Agda.Primitive

open import Definition.Untyped
open import Definition.Typed
open import Definition.LogicalRelation

open import Tools.Embedding
open import Tools.Product
open import Tools.Unit

-- The validity judgements:
-- We consider expressions that satisfy these judgments valid

ValRel : Setω₂
ValRel = (Γ : Con Term) → (⊩Subst : (Δ : Con Term) → Subst → ⊢ Δ → Setω)
    → (⊩EqSubst : (Δ : Con Term) → (σ σ′ : Subst) → (⊢Δ : ⊢ Δ) → (⊩Subst Δ σ ⊢Δ) → Setω)
    → Setω₁

record ⊩ᵛ⁰_/_ (Γ : Con Term) (_⊩_▸_ : ValRel) : Setω₁ where
  inductive
  eta-equality
  constructor VPack
  field
    ⊩Subst : (Δ : Con Term) → Subst → ⊢ Δ → Setω
    ⊩EqSubst : (Δ : Con Term) → (σ σ′ : Subst) → (⊢Δ : ⊢ Δ) → (⊩Subst Δ σ ⊢Δ) → Setω
    ⊩V : Γ ⊩ ⊩Subst ▸ ⊩EqSubst

_⊩ˢ⁰_∷_/_/_ : {R : ValRel} (Δ : Con Term) (σ : Subst) (Γ : Con Term) ([Γ] : ⊩ᵛ⁰ Γ / R) (⊢Δ : ⊢ Δ)
           → Setω
Δ ⊩ˢ⁰ σ ∷ Γ / VPack ⊩Subst ⊩EqSubst ⊩V / ⊢Δ = ⊩Subst Δ σ ⊢Δ

_⊩ˢ⁰_≡_∷_/_/_/_ : {R : ValRel} (Δ : Con Term) (σ σ′ : Subst) (Γ : Con Term) ([Γ] : ⊩ᵛ⁰ Γ / R)
                 (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ˢ⁰ σ ∷ Γ / [Γ] / ⊢Δ) → Setω
Δ ⊩ˢ⁰ σ ≡ σ′ ∷ Γ / VPack ⊩Subst ⊩EqSubst ⊩V / ⊢Δ / [σ] = ⊩EqSubst Δ σ σ′ ⊢Δ [σ]

-- Validity of types
_⊩ᵛ⁰⟨_⟩_/_ : {R : ValRel} (Γ : Con Term) (l : TypeLevel) (A : Term) → ⊩ᵛ⁰ Γ / R → Setω
_⊩ᵛ⁰⟨_⟩_/_ Γ l A [Γ] =
  ∀ {Δ σ} (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ˢ⁰ σ ∷ Γ / [Γ] / ⊢Δ)
  → Σω₀ (Δ ⊩⟨ l ⟩ subst σ A) (λ [Aσ]
    → ∀ {σ′} ([σ′] : Δ ⊩ˢ⁰ σ′ ∷ Γ / [Γ] / ⊢Δ)
      ([σ≡σ′] : Δ ⊩ˢ⁰ σ ≡ σ′ ∷ Γ / [Γ] / ⊢Δ / [σ])
    → Δ ⊩⟨ l ⟩ subst σ A ≡ subst σ′ A / [Aσ])

data _⊩V_▸_ : ValRel where
  Vε : ε
    ⊩V (λ Δ σ ⊢Δ → ⊤′)
    ▸ (λ Δ σ σ′ ⊢Δ [σ] → ⊤′)
  V∙ : ∀ {Γ A l}
    → ([Γ] : ⊩ᵛ⁰ Γ / _⊩V_▸_)
    → ([A] : Γ ⊩ᵛ⁰⟨ l ⟩ A / [Γ])
    → Γ ∙ A
        ⊩V (λ Δ σ ⊢Δ → Σω₂ (Δ ⊩ˢ⁰ tail σ ∷ Γ / [Γ] / ⊢Δ)
                         (λ [tailσ] → (Δ ⊩⟨ l ⟩ head σ ∷ subst (tail σ) A / proj₁ ([A] ⊢Δ [tailσ]))))
        ▸ (λ Δ σ σ′ ⊢Δ [σ] → (Δ ⊩ˢ⁰ tail σ ≡ tail σ′ ∷ Γ / [Γ] / ⊢Δ / proj₁ [σ]) ×ω₂
             (Δ ⊩⟨ l ⟩ head σ ≡ head σ′ ∷ subst (tail σ) A / proj₁ ([A] ⊢Δ (proj₁ [σ]))))

⊩ᵛ : Con Term → Setω₁
⊩ᵛ Γ = ⊩ᵛ⁰ Γ / _⊩V_▸_

_⊩ˢ_∷_/_/_ : (Δ : Con Term) (σ : Subst) (Γ : Con Term) ([Γ] : ⊩ᵛ Γ) (⊢Δ : ⊢ Δ)
           → Setω
Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ = Δ ⊩ˢ⁰ σ ∷ Γ / [Γ] / ⊢Δ

_⊩ˢ_≡_∷_/_/_/_ : (Δ : Con Term) (σ σ′ : Subst) (Γ : Con Term) ([Γ] : ⊩ᵛ Γ)
                 (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ) → Setω
Δ ⊩ˢ σ ≡ σ′ ∷ Γ / [Γ] / ⊢Δ / [σ] = Δ ⊩ˢ⁰ σ ≡ σ′ ∷ Γ / [Γ] / ⊢Δ / [σ]

-- Validity of types
_⊩ᵛ⟨_⟩_/_ : (Γ : Con Term) (l : TypeLevel) (A : Term) → ⊩ᵛ Γ → Setω
Γ ⊩ᵛ⟨ l ⟩ A / [Γ] = Γ ⊩ᵛ⁰⟨ l ⟩ A / [Γ]

-- Validity of terms
_⊩ᵛ⟨_⟩_∷_/_/_ : (Γ : Con Term) (l : TypeLevel) (t A : Term) ([Γ] : ⊩ᵛ Γ)
                 ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ]) → Setω
Γ ⊩ᵛ⟨ l ⟩ t ∷ A / [Γ] / [A] =
  ∀ {Δ σ} (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ) →
  Σω₀ (Δ ⊩⟨ l ⟩ subst σ t ∷ subst σ A / proj₁ ([A] ⊢Δ [σ])) λ [tσ] →
  ∀ {σ′} → Δ ⊩ˢ σ′ ∷ Γ / [Γ] / ⊢Δ → Δ ⊩ˢ σ ≡ σ′ ∷ Γ / [Γ] / ⊢Δ / [σ]
    → Δ ⊩⟨ l ⟩ subst σ t ≡ subst σ′ t ∷ subst σ A / proj₁ ([A] ⊢Δ [σ])

-- Validity of type equality
_⊩ᵛ⟨_⟩_≡_/_/_ : (Γ : Con Term) (l : TypeLevel) (A B : Term) ([Γ] : ⊩ᵛ Γ)
                ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ]) → Setω
Γ ⊩ᵛ⟨ l ⟩ A ≡ B / [Γ] / [A] =
  ∀ {Δ σ} (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
  → Δ ⊩⟨ l ⟩ subst σ A ≡ subst σ B / proj₁ ([A] ⊢Δ [σ])

-- Validity of term equality
_⊩ᵛ⟨_⟩_≡_∷_/_/_ : (Γ : Con Term) (l : TypeLevel) (t u A : Term) ([Γ] : ⊩ᵛ Γ)
                    ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ]) → Setω
Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A / [Γ] / [A] =
  ∀ {Δ σ} → (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
          → Δ ⊩⟨ l ⟩ subst σ t ≡ subst σ u ∷ subst σ A / proj₁ ([A] ⊢Δ [σ])

-- Valid term equality with validity of its type and terms
record [_⊩ᵛ⟨_⟩_≡_∷_/_] (Γ : Con Term) (l : TypeLevel)
                       (t u A : Term) ([Γ] : ⊩ᵛ Γ) : Setω where
  constructor modelsTermEq
  field
    [A]   : Γ ⊩ᵛ⟨ l ⟩ A / [Γ]
    [t]   : Γ ⊩ᵛ⟨ l ⟩ t ∷ A / [Γ] / [A]
    [u]   : Γ ⊩ᵛ⟨ l ⟩ u ∷ A / [Γ] / [A]
    [t≡u] : Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A / [Γ] / [A]

-- Validity of reduction of terms
_⊩ᵛ_⇒_∷_/_ : (Γ : Con Term) (t u A : Term) ([Γ] : ⊩ᵛ Γ) → Setω
Γ ⊩ᵛ t ⇒ u ∷ A / [Γ] = ∀ {Δ σ} (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
                       → Δ ⊢ subst σ t ⇒ subst σ u ∷ subst σ A

_∙″_ : ∀ {Γ A l} → ([Γ] : ⊩ᵛ Γ) → Γ ⊩ᵛ⟨ l ⟩ A / [Γ] → ⊩ᵛ (Γ ∙ A)
[Γ] ∙″ [A] = (VPack _ _ (V∙ [Γ] [A]))

pattern ε′ = (VPack _ _ Vε)
pattern _∙′_ [Γ] [A] = (VPack _ _ (V∙ [Γ] [A]))
