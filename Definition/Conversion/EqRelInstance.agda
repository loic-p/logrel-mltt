{-# OPTIONS --without-K --safe #-}

module Definition.Conversion.EqRelInstance where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.Weakening using (_∷_⊆_; wkEq)
open import Definition.Conversion
open import Definition.Conversion.Reduction
open import Definition.Conversion.Universe
open import Definition.Conversion.Stability
open import Definition.Conversion.Soundness
open import Definition.Conversion.Lift
open import Definition.Conversion.Conversion
open import Definition.Conversion.Symmetry
open import Definition.Conversion.Transitivity
open import Definition.Conversion.Weakening
open import Definition.Typed.EqualityRelation
open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.Substitution
open import Definition.Typed.Consequences.Injectivity
open import Definition.Typed.Consequences.Equality
open import Definition.Typed.Consequences.Reduction

open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Function


-- Algorithmic equality of neutrals with injected conversion.
data _⊢_~_∷_^_ (Γ : Con Term) (k l A : Term) (r : Relevance) : Set where
  ↑ : ∀ {B} → Γ ⊢ A ≡ B ^ r → Γ ⊢ k ~ l ↑ B ^ r → Γ ⊢ k ~ l ∷ A ^ r

-- Properties of algorithmic equality of neutrals with injected conversion.

~-var : ∀ {x A r Γ} → Γ ⊢ var x ∷ A ^ r → Γ ⊢ var x ~ var x ∷ A ^ r
~-var x =
  let ⊢A = syntacticTerm x
  in  ↑ (refl ⊢A) (var-refl x PE.refl)

~-app : ∀ {f g a b F rF G rG Γ}
      → Γ ⊢ f ~ g ∷ Π F ^ rF ▹ G ^ rG
      → Γ ⊢ a [conv↑] b ∷ F ^ rF
      → Γ ⊢ f ∘ a ~ g ∘ b ∷ G [ a ] ^ rG
~-app (↑ A≡B x) x₁ =
  let _ , ⊢B = syntacticEq A≡B
      B′ , whnfB′ , D = whNorm ⊢B
      ΠFG≡B′ = trans A≡B (subset* (red D))
      H , E , B≡ΠHE = Π≡A ΠFG≡B′ whnfB′
      F≡H , _ , G≡E = injectivity (PE.subst (λ x → _ ⊢ _ ≡ x ^ _) B≡ΠHE ΠFG≡B′)
      _ , ⊢f , _ = syntacticEqTerm (soundnessConv↑Term x₁)
  in  ↑ (substTypeEq G≡E (refl ⊢f))
        (app-cong (PE.subst (λ x → _ ⊢ _ ~ _ ↓ x ^ _)
                       B≡ΠHE ([~] _ (red D) whnfB′ x))
             (convConvTerm x₁ F≡H))

~-natrec : ∀ {z z′ s s′ n n′ F F′ rF Γ}
         → (Γ ∙ ℕ ^ !) ⊢ F [conv↑] F′ ^ rF →
      Γ ⊢ z [conv↑] z′ ∷ (F [ zero ]) ^ rF →
      Γ ⊢ s [conv↑] s′ ∷ (Π ℕ ^ ! ▹ (F ^ rF ▹▹ F [ suc (var 0) ]↑)) ^ rF →
      Γ ⊢ n ~ n′ ∷ ℕ ^ ! →
      Γ ⊢ natrec F z s n ~ natrec F′ z′ s′ n′ ∷ (F [ n ]) ^ rF
~-natrec x x₁ x₂ (↑ A≡B x₄) =
  let _ , ⊢B = syntacticEq A≡B
      B′ , whnfB′ , D = whNorm ⊢B
      ℕ≡B′ = trans A≡B (subset* (red D))
      B≡ℕ = ℕ≡A ℕ≡B′ whnfB′
      k~l′ = PE.subst (λ x → _ ⊢ _ ~ _ ↓ x  ^ _) B≡ℕ
                      ([~] _ (red D) whnfB′ x₄)
      ⊢F , _ = syntacticEq (soundnessConv↑ x)
      _ , ⊢n , _ = syntacticEqTerm (soundness~↓ k~l′)
  in  ↑ (refl (substType ⊢F ⊢n))
        (natrec-cong x x₁ x₂ k~l′)

~-Emptyrec : ∀ {n n′ F F′ rF Γ}
         → Γ ⊢ F [conv↑] F′ ^ rF →
      Γ ⊢ n ~ n′ ∷ Empty ^ % →
      Γ ⊢ Emptyrec F n ~ Emptyrec F′ n′ ∷ F ^ rF
~-Emptyrec x (↑ A≡B x₄) =
  let _ , ⊢B = syntacticEq A≡B
      B′ , whnfB′ , D = whNorm ⊢B
      Empty≡B′ = trans A≡B (subset* (red D))
      B≡Empty = Empty≡A Empty≡B′ whnfB′
      k~l′ = PE.subst (λ x → _ ⊢ _ ~ _ ↓ x ^ _) B≡Empty
                      ([~] _ (red D) whnfB′ x₄)
      ⊢F , _ = syntacticEq (soundnessConv↑ x)
      _ , ⊢n , _ = syntacticEqTerm (soundness~↓ k~l′)
  in  ↑ (refl ⊢F)
        (Emptyrec-cong x k~l′)

~-sym : {k l A : Term} {r : Relevance} {Γ : Con Term} → Γ ⊢ k ~ l ∷ A ^ r → Γ ⊢ l ~ k ∷ A ^ r
~-sym (↑ A≡B x) =
  let ⊢Γ = wfEq A≡B
      B , A≡B′ , l~k = sym~↑ (reflConEq ⊢Γ) x
  in  ↑ (trans A≡B A≡B′) l~k

~-trans : {k l m A : Term} {r : Relevance} {Γ : Con Term}
        → Γ ⊢ k ~ l ∷ A ^ r → Γ ⊢ l ~ m ∷ A ^ r
        → Γ ⊢ k ~ m ∷ A ^ r
~-trans (↑ x x₁) (↑ x₂ x₃) =
  let ⊢Γ = wfEq x
      k~m , _ = trans~↑ (reflConEq ⊢Γ) x₁ x₃
  in  ↑ x k~m

~-wk : {k l A : Term} {r : Relevance} {ρ : Wk} {Γ Δ : Con Term} →
      ρ ∷ Δ ⊆ Γ →
      ⊢ Δ → Γ ⊢ k ~ l ∷ A ^ r → Δ ⊢ wk ρ k ~ wk ρ l ∷ wk ρ A ^ r
~-wk x x₁ (↑ x₂ x₃) = ↑ (wkEq x x₁ x₂) (wk~↑ x x₁ x₃)

~-conv : {k l A B : Term} {r : Relevance} {Γ : Con Term} →
      Γ ⊢ k ~ l ∷ A ^ r → Γ ⊢ A ≡ B ^ r → Γ ⊢ k ~ l ∷ B ^ r
~-conv (↑ x x₁) x₂ = ↑ (trans (sym x₂) x) x₁

~-to-conv : {k l A : Term} {r : Relevance} {Γ : Con Term} →
      Γ ⊢ k ~ l ∷ A ^ r → Γ ⊢ k [conv↑] l ∷ A ^ r
~-to-conv (↑ x x₁) = convConvTerm (lift~toConv↑ x₁) (sym x)


-- Algorithmic equality instance of the generic equality relation.
instance eqRelInstance : EqRelSet
eqRelInstance = eqRel _⊢_[conv↑]_^_ _⊢_[conv↑]_∷_^_ _⊢_~_∷_^_
                      ~-to-conv soundnessConv↑ soundnessConv↑Term
                      univConv↑
                      symConv symConvTerm ~-sym
                      transConv transConvTerm ~-trans
                      convConvTerm ~-conv
                      wkConv↑ wkConv↑Term ~-wk
                      reductionConv↑ reductionConv↑Term
                      (liftConv ∘ᶠ (U-refl PE.refl))
                      (liftConv ∘ᶠ ℕ-refl)
                      (λ x → liftConvTerm (univ (ℕⱼ x) (ℕⱼ x) (ℕ-refl x)))
                      (liftConv ∘ᶠ Empty-refl)
                      (λ x → liftConvTerm (univ (Emptyⱼ x) (Emptyⱼ x) (Empty-refl x)))
                      (λ x x₁ x₂ → liftConv (Π-cong PE.refl x x₁ x₂))
                      (λ x x₁ x₂ →
                         let _ , F∷U , H∷U = syntacticEqTerm (soundnessConv↑Term x₁)
                             _ , G∷U , E∷U = syntacticEqTerm (soundnessConv↑Term x₂)
                             ⊢Γ = wfTerm F∷U
                             F<>H = univConv↑ x₁
                             G<>E = univConv↑ x₂
                             F≡H = soundnessConv↑ F<>H
                             E∷U′ = stabilityTerm (reflConEq ⊢Γ ∙ F≡H) E∷U
                         in  liftConvTerm (univ (Πⱼ F∷U ▹ G∷U) (Πⱼ H∷U ▹ E∷U′)
                                                (Π-cong PE.refl x F<>H G<>E)))

                      (liftConvTerm ∘ᶠ zero-refl)
                      (liftConvTerm ∘ᶠ suc-cong)
                      (λ x x₁ x₂ x₃ x₄ x₅ → liftConvTerm (η-eq x x₁ x₂ x₃ x₄ x₅))
                      ~-var ~-app ~-natrec ~-Emptyrec
