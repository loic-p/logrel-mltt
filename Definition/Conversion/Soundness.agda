{-# OPTIONS --without-K --safe #-}

module Definition.Conversion.Soundness where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Conversion
open import Definition.Conversion.Whnf
open import Definition.Typed.Consequences.InverseUniv
open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.NeTypeEq

open import Tools.Product
import Tools.PropositionalEquality as PE


mutual
  -- Algorithmic equality of neutrals is well-formed.
  soundness~↑! : ∀ {k l A Γ} → Γ ⊢ k ~ l ↑! A → Γ ⊢ k ≡ l ∷ A ^ !
  soundness~↑! (var-refl x x≡y) = PE.subst (λ y → _ ⊢ _ ≡ var y ∷ _ ^ _) x≡y (refl x)
  soundness~↑! (app-cong k~l x₁) = app-cong (soundness~↓ k~l) (soundnessConv↑Term x₁)
  soundness~↑! (natrec-cong x₁ x₂ x₃ k~l) =
    natrec-cong (soundnessConv↑ x₁) (soundnessConv↑Term x₂)
                (soundnessConv↑Term x₃) (soundness~↓ k~l)
  soundness~↑! (Emptyrec-cong x₁ k~l) =
    Emptyrec-cong (soundnessConv↑ x₁) (soundness~↓ k~l)

  soundness~↑% : ∀ {k A Γ} → Γ ⊢ k ↑% A → Γ ⊢ k ∷ A ^ %
  soundness~↑% (var% x) = x
  soundness~↑% (app% k t) =
    let _ , ⊢k , _ = syntacticEqTerm (soundness~↓ k)
        _ , ⊢t , _ = syntacticEqTerm (soundnessConv↑Term t)
    in ⊢k ∘ⱼ ⊢t
  soundness~↑% (natrec% C z s n) =
    let ⊢C , _ = syntacticEq (soundnessConv↑ C)
        _ , ⊢z , _ = syntacticEqTerm (soundnessConv↑Term z)
        _ , ⊢s , _ = syntacticEqTerm (soundnessConv↑Term s)
        _ , ⊢n , _ = syntacticEqTerm (soundness~↓ n)
    in natrecⱼ ⊢C ⊢z ⊢s ⊢n
  soundness~↑% (Emptyrec% C n) =
    let ⊢C , _ = syntacticEq (soundnessConv↑ C)
        _ , ⊢n , _ = syntacticEqTerm (soundness~↓ n)
    in Emptyrecⱼ ⊢C ⊢n

  soundness~↑ : ∀ {k l A rA Γ} → Γ ⊢ k ~ l ↑ A ^ rA → Γ ⊢ k ≡ l ∷ A ^ rA
  soundness~↑ (relevant-neutrals x) = soundness~↑! x
  soundness~↑ (irrelevant-neutrals ac bc x x₁) =
    let ⊢x = soundness~↑% x
        ⊢x₁ = soundness~↑% x₁
        ⊢ac = soundnessConv↑ ac
        ⊢bc = soundnessConv↑ bc
    in proof-irrelevance (conv ⊢x (sym ⊢ac)) (conv ⊢x₁ ⊢bc)

  -- Algorithmic equality of neutrals in WHNF is well-formed.
  soundness~↓ : ∀ {k l A rA Γ} → Γ ⊢ k ~ l ↓ A ^ rA → Γ ⊢ k ≡ l ∷ A ^ rA
  soundness~↓ ([~] A₁ D whnfA k~l) = conv (soundness~↑ k~l) (subset* D)

  -- Algorithmic equality of types is well-formed.
  soundnessConv↑ : ∀ {A B rA Γ} → Γ ⊢ A [conv↑] B ^ rA → Γ ⊢ A ≡ B ^ rA
  soundnessConv↑ ([↑] A′ B′ D D′ whnfA′ whnfB′ A′<>B′) =
    trans (subset* D) (trans (soundnessConv↓ A′<>B′) (sym (subset* D′)))

  -- Algorithmic equality of types in WHNF is well-formed.
  soundnessConv↓ : ∀ {A B rA Γ} → Γ ⊢ A [conv↓] B ^ rA → Γ ⊢ A ≡ B ^ rA
  soundnessConv↓ (U-refl PE.refl ⊢Γ) = refl (Uⱼ ⊢Γ)
  soundnessConv↓ (ℕ-refl ⊢Γ) = refl (ℕⱼ ⊢Γ)
  soundnessConv↓ (Empty-refl ⊢Γ) = refl (Emptyⱼ ⊢Γ)
  soundnessConv↓ (ne x) = univ (soundness~↓ x)
  soundnessConv↓ (Π-cong PE.refl F c c₁) =
    Π-cong F (soundnessConv↑ c) (soundnessConv↑ c₁)

  -- Algorithmic equality of terms is well-formed.
  soundnessConv↑Term : ∀ {a b A rA Γ} → Γ ⊢ a [conv↑] b ∷ A ^ rA → Γ ⊢ a ≡ b ∷ A ^ rA
  soundnessConv↑Term ([↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u) =
    conv (trans (subset*Term d)
                (trans (soundnessConv↓Term t<>u)
                       (sym (subset*Term d′))))
         (sym (subset* D))

  -- Algorithmic equality of terms in WHNF is well-formed.
  soundnessConv↓Term : ∀ {a b A rA Γ} → Γ ⊢ a [conv↓] b ∷ A ^ rA → Γ ⊢ a ≡ b ∷ A ^ rA
  soundnessConv↓Term (ℕ-ins x) = soundness~↓ x
  soundnessConv↓Term (Empty-ins x) = soundness~↓ x
  soundnessConv↓Term (ne-ins t u x x₁) =
    let _ , neA , _ = ne~↓ x₁
        _ , t∷M , _ = syntacticEqTerm (soundness~↓ x₁)
        M≡A = neTypeEq neA t∷M t
    in  conv (soundness~↓ x₁) M≡A
  soundnessConv↓Term (univ x x₁ x₂) = inverseUnivEq x (soundnessConv↓ x₂)
  soundnessConv↓Term (zero-refl ⊢Γ) = refl (zeroⱼ ⊢Γ)
  soundnessConv↓Term (suc-cong c) = suc-cong (soundnessConv↑Term c)
  soundnessConv↓Term (η-eq F x x₁ y y₁ c) =
    η-eq F x x₁ (soundnessConv↑Term c)
