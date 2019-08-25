{-# OPTIONS --without-K --safe #-}

module Definition.Conversion.Lift where

open import Definition.Untyped
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Weakening
open import Definition.Typed.Properties
open import Definition.Typed.EqRelInstance
open import Definition.Conversion
open import Definition.Conversion.Whnf
open import Definition.Conversion.Soundness
open import Definition.Conversion.Reduction
open import Definition.Conversion.Weakening
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Fundamental.Reducibility
open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.Reduction

open import Tools.Product
import Tools.PropositionalEquality as PE


-- Lifting of algorithmic equality of types from WHNF to generic types.
liftConv : ∀ {A B rA Γ}
          → Γ ⊢ A [conv↓] B ^ rA
          → Γ ⊢ A [conv↑] B ^ rA
liftConv A<>B =
  let ⊢A , ⊢B = syntacticEq (soundnessConv↓ A<>B)
      whnfA , whnfB = whnfConv↓ A<>B
  in  [↑] _ _ (id ⊢A) (id ⊢B) whnfA whnfB A<>B

-- Lifting of algorithmic equality of terms from WHNF to generic terms.
liftConvTerm : ∀ {t u A rA Γ}
             → Γ ⊢ t [conv↓] u ∷ A ^ rA
             → Γ ⊢ t [conv↑] u ∷ A ^ rA
liftConvTerm t<>u =
  let ⊢A , ⊢t , ⊢u = syntacticEqTerm (soundnessConv↓Term t<>u)
      whnfA , whnfT , whnfU = whnfConv↓Term t<>u
  in  [↑]ₜ _ _ _ (id ⊢A) (id ⊢t) (id ⊢u) whnfA whnfT whnfU t<>u


mutual
  -- Helper function for lifting from neutrals to generic terms in WHNF.
  lift~toConv↓′ : ∀ {t u A A′ rA Γ l}
                → Γ ⊩⟨ l ⟩ A′ ^ rA
                → Γ ⊢ A′ ⇒* A ^ rA
                → Γ ⊢ t ~ u ↓ A ^ rA
                → Γ ⊢ t [conv↓] u ∷ A ^ rA
  lift~toConv↓′ (Uᵣ′ _ .⁰ 0<1 ⊢Γ) D ([~] A D₁ whnfB k~l)
                rewrite PE.sym (whnfRed* D Uₙ) =
    let _ , ⊢t , ⊢u = syntacticEqTerm (conv (soundness~↑ k~l) (subset* D₁))
    in  univ ⊢t ⊢u (ne ([~] A D₁ Uₙ k~l))
  lift~toConv↓′ (ℕᵣ D) D₁ ([~] A D₂ whnfB k~l)
                rewrite PE.sym (whrDet* (red D , ℕₙ) (D₁ , whnfB)) =
    ℕ-ins ([~] A D₂ ℕₙ k~l)
  lift~toConv↓′ (Emptyᵣ D) D₁ ([~] A D₂ whnfB k~l)
                rewrite PE.sym (whrDet* (red D , Emptyₙ) (D₁ , whnfB)) =
    Empty-ins ([~] A D₂ Emptyₙ k~l)
  lift~toConv↓′ (ne′ K D neK K≡K) D₁ ([~] A D₂ whnfB k~l)
                rewrite PE.sym (whrDet* (red D , ne neK) (D₁ , whnfB)) =
    let _ , ⊢t , ⊢u = syntacticEqTerm (soundness~↑ k~l)
        A≡K = subset* D₂
    in  ne-ins (conv ⊢t A≡K) (conv ⊢u A≡K) neK ([~] A D₂ (ne neK) k~l)
  lift~toConv↓′ (Πᵣ′ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext) D₁ ([~] A D₂ whnfB k~l) with PE.sym (whrDet* (red D , Πₙ) (D₁ , whnfB))
  lift~toConv↓′ (Πᵣ′ ! F G D ⊢F ⊢G A≡A [F] [G] G-ext) D₁ ([~] A D₂ whnfB (relevant-neutrals k~l)) | PE.refl =
    let ⊢ΠFG , ⊢t , ⊢u = syntacticEqTerm (soundness~↓ ([~] A D₂ Πₙ (relevant-neutrals k~l)))
        neT , neU = ne~↑! k~l
        ⊢Γ = wf ⊢F
        var0 = neuTerm ([F] (step id) (⊢Γ ∙ ⊢F)) (var 0) (var (⊢Γ ∙ ⊢F) here)
                       (refl (var (⊢Γ ∙ ⊢F) here))
        0≡0 = lift~toConv↑′ ([F] (step id) (⊢Γ ∙ ⊢F)) (relevant-neutrals (var-refl (var (⊢Γ ∙ ⊢F) here) PE.refl))
        k∘0≡l∘0 = lift~toConv↑′ ([G] (step id) (⊢Γ ∙ ⊢F) var0)
                                (relevant-neutrals (app-cong (wk~↓ (step id) (⊢Γ ∙ ⊢F) ([~] A D₂ Πₙ (relevant-neutrals k~l))) 0≡0))
    in  η-eq ⊢F ⊢t ⊢u (ne neT) (ne neU)
             (PE.subst (λ x → _ ⊢ _ [conv↑] _ ∷ x ^ _)
                       (wkSingleSubstId _)
                       k∘0≡l∘0)
  lift~toConv↓′ (Πᵣ′ % F G D ⊢F ⊢G A≡A [F] [G] G-ext) D₁ ([~] A D₂ whnfB (relevant-neutrals k~l)) | PE.refl =
    let ⊢ΠFG , ⊢t , ⊢u = syntacticEqTerm (soundness~↓ ([~] A D₂ Πₙ (relevant-neutrals k~l)))
        neT , neU = ne~↑! k~l
        ⊢Γ = wf ⊢F
        ⊢var0 = var (⊢Γ ∙ ⊢F) here
        var0 = neuTerm ([F] (step id) (⊢Γ ∙ ⊢F)) (var 0) ⊢var0 (refl ⊢var0)
        0≡0 = lift~toConv↑′ ([F] (step id) (⊢Γ ∙ ⊢F))
                (irrelevant-neutrals (var _) (var _) ⊢var0 ⊢var0
                  {!!})
        k∘0≡l∘0 = lift~toConv↑′ ([G] (step id) (⊢Γ ∙ ⊢F) var0)
                                (relevant-neutrals (app-cong (wk~↓ (step id) (⊢Γ ∙ ⊢F) ([~] A D₂ Πₙ (relevant-neutrals k~l))) 0≡0))
    in  η-eq ⊢F ⊢t ⊢u (ne neT) (ne neU)
             (PE.subst (λ x → _ ⊢ _ [conv↑] _ ∷ x ^ _)
                       (wkSingleSubstId _)
                       k∘0≡l∘0)
  lift~toConv↓′ (Πᵣ′ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext) D₁ ([~] A D₂ whnfB (irrelevant-neutrals neK neL ⊢t ⊢u ([↑] A′ B′ D₃ D′ whnfA′ whnfB′ A′<>B′))) | PE.refl with whrDet* (D₃ , whnfA′) (D′ , whnfB′)
  ... | PE.refl with whrDet* (D₂ , Πₙ) (D₃ , whnfA′)
  lift~toConv↓′ (Πᵣ′ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext) D₁ ([~] A D₂ whnfB (irrelevant-neutrals neK neL ⊢t ⊢u ([↑] A′ B′ D₃ D′ whnfA′ whnfB′ (ne ([~] _ _ _ (relevant-neutrals ())))))) | PE.refl | PE.refl | PE.refl
  lift~toConv↓′ (Πᵣ′ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext) D₁ ([~] A D₂ whnfB (irrelevant-neutrals neK neL ⊢t ⊢u ([↑] A′ B′ D₃ D′ whnfA′ whnfB′ (Π-cong _ _ F↑ G↑)))) | PE.refl | PE.refl | PE.refl =
    let A≡Π = subset* D₃
        ⊢t = conv ⊢t A≡Π
        ⊢u = conv ⊢u A≡Π
        ⊢Γ = wf ⊢F
        ⊢var0 = (var (⊢Γ ∙ ⊢F) here)
        var0 = neuTerm ([F] (step id) (⊢Γ ∙ ⊢F)) (var 0) ⊢var0 (refl ⊢var0)
        ⊢t′ = wkTerm (step id) (⊢Γ ∙ ⊢F) ⊢t
        ⊢u′ = wkTerm (step id) (⊢Γ ∙ ⊢F) ⊢u
        k∘0≡l∘0 = lift~toConv↑′ ([G] (step id) (⊢Γ ∙ ⊢F) var0)
                                (irrelevant-neutrals (∘ₙ (wkNeutral _ neK)) (∘ₙ (wkNeutral _ neL))
                                  (⊢t′ ∘ⱼ ⊢var0) (⊢u′ ∘ⱼ ⊢var0)
                                    (PE.subst (λ Gx → _ ⊢ Gx [conv↑] Gx ^ _)
                                              (PE.sym (wkSingleSubstId G))
                                              G↑))
    in η-eq ⊢F ⊢t ⊢u (ne neK) (ne neL)
            (PE.subst (λ x → _ ⊢ _ [conv↑] _ ∷ x ^ _) (wkSingleSubstId _) k∘0≡l∘0)

  lift~toConv↓′ (emb 0<1 [A]) D t~u = lift~toConv↓′ [A] D t~u

  -- Helper function for lifting from neutrals to generic terms.
  lift~toConv↑′ : ∀ {t u A rA Γ l}
                → Γ ⊩⟨ l ⟩ A ^ rA
                → Γ ⊢ t ~ u ↑ A ^ rA
                → Γ ⊢ t [conv↑] u ∷ A ^ rA
  lift~toConv↑′ [A] t~u =
    let B , whnfB , D = whNorm′ [A]
        t~u↓ = [~] _ (red D) whnfB t~u
        neT , neU = ne~↑ t~u
        _ , ⊢t , ⊢u = syntacticEqTerm (soundness~↓ t~u↓)
    in  [↑]ₜ _ _ _ (red D) (id ⊢t) (id ⊢u) whnfB
             (ne neT) (ne neU) (lift~toConv↓′ [A] (red D) t~u↓)

-- Lifting of algorithmic equality of terms from neutrals to generic terms in WHNF.
lift~toConv↓ : ∀ {t u A rA Γ}
             → Γ ⊢ t ~ u ↓ A ^ rA
             → Γ ⊢ t [conv↓] u ∷ A ^ rA
lift~toConv↓ ([~] A₁ D whnfB k~l) =
  lift~toConv↓′ (reducible (proj₁ (syntacticRed D))) D ([~] A₁ D whnfB k~l)

-- Lifting of algorithmic equality of terms from neutrals to generic terms.
lift~toConv↑ : ∀ {t u A rA Γ}
             → Γ ⊢ t ~ u ↑ A ^ rA
             → Γ ⊢ t [conv↑] u ∷ A ^ rA
lift~toConv↑ t~u =
  lift~toConv↑′ (reducible (proj₁ (syntacticEqTerm (soundness~↑ t~u)))) t~u
