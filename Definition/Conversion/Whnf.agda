{-# OPTIONS --without-K --safe #-}

module Definition.Conversion.Whnf where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Conversion

open import Tools.Product


mutual
  -- Extraction of neutrality from algorithmic equality of neutrals.
  ne~↑ : ∀ {t u A rA Γ}
       → Γ ⊢ t ~ u ↑ A ^ rA
       → Neutral t × Neutral u
  ne~↑ (var-refl x₁ x≡y) = var _ , var _
  ne~↑ (app-cong x x₁) = let _ , q , w = ne~↓ x
                         in  ∘ₙ q , ∘ₙ w
  ne~↑ (natrec-cong x x₁ x₂ x₃) = let _ , q , w = ne~↓ x₃
                                  in  natrecₙ q , natrecₙ w
  ne~↑ (Emptyrec-cong x x₁) = let _ , q , w = ne~↓ x₁
                              in Emptyrecₙ q , Emptyrecₙ w
  ne~↑ (proof-irrelevance x x₁) = (proj₁ (ne~↑ x)) , (proj₁ (ne~↑ x₁))

  -- Extraction of neutrality and WHNF from algorithmic equality of neutrals
  -- with type in WHNF.
  ne~↓ : ∀ {t u A rA Γ}
       → Γ ⊢ t ~ u ↓ A ^ rA
       → Whnf A × Neutral t × Neutral u
  ne~↓ ([~] A₁ D whnfB k~l) = whnfB , ne~↑ k~l

-- Extraction of WHNF from algorithmic equality of types in WHNF.
whnfConv↓ : ∀ {A B rA Γ}
          → Γ ⊢ A [conv↓] B ^ rA
          → Whnf A × Whnf B
whnfConv↓ (U-refl _ x) = Uₙ , Uₙ
whnfConv↓ (ℕ-refl x) = ℕₙ , ℕₙ
whnfConv↓ (Empty-refl x) = Emptyₙ , Emptyₙ
whnfConv↓ (ne x) = let _ , neA , neB = ne~↓ x
                   in  ne neA , ne neB
whnfConv↓ (Π-cong _ x x₁ x₂) = Πₙ , Πₙ

-- Extraction of WHNF from algorithmic equality of terms in WHNF.
whnfConv↓Term : ∀ {t u A rA Γ}
              → Γ ⊢ t [conv↓] u ∷ A ^ rA
              → Whnf A × Whnf t × Whnf u
whnfConv↓Term (ℕ-ins x) = let _ , neT , neU = ne~↓ x
                          in ℕₙ , ne neT , ne neU
whnfConv↓Term (Empty-ins x) = let _ , neT , neU = ne~↓ x
                          in Emptyₙ , ne neT , ne neU
whnfConv↓Term (ne-ins t u x x₁) =
  let _ , neT , neU = ne~↓ x₁
  in ne x , ne neT , ne neU
whnfConv↓Term (univ x x₁ x₂) = Uₙ , whnfConv↓ x₂
whnfConv↓Term (zero-refl x) = ℕₙ , zeroₙ , zeroₙ
whnfConv↓Term (suc-cong x) = ℕₙ , sucₙ , sucₙ
whnfConv↓Term (η-eq x x₁ x₂ y y₁ x₃) = Πₙ , functionWhnf y , functionWhnf y₁
