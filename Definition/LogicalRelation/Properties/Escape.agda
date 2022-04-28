{-# OPTIONS --without-K #-}

module Definition.LogicalRelation.Properties.Escape where

open import Definition.Untyped
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Weakening
open import Definition.Typed.Properties
open import Definition.Typed.Reduction
open import Definition.LogicalRelation

open import Tools.Product
import Tools.PropositionalEquality as PE


-- Reducible types are well-formed.
escape : ∀ {l Γ A} → Γ ⊩⟨ l ⟩ A → Γ ⊢ A
escape (U′ l′ l< ⊢Γ) = U ⊢Γ
escape (ℕ [ ⊢A , ⊢B , D ]) = ⊢A
escape (ne′ K [ ⊢A , ⊢B , D ] neK) = ⊢A
escape (Π′ F G [ ⊢A , ⊢B , D ] typeΠ ⊢F ⊢G [F] [G] G-ext) = ⊢A
escape (emb 0<1 A) = escape A

-- Reducible type equality respect the equality relation.
escapeEq : ∀ {l Γ A B} → ([A] : Γ ⊩⟨ l ⟩ A)
            → Γ ⊩⟨ l ⟩ A ≡ B / [A]
            → Γ ⊢ A ≡ B
escapeEq (U′ l′ l< ⊢Γ) PE.refl = refl (U ⊢Γ)
escapeEq (ℕ [ ⊢A , ⊢B , D ]) [A≡B] = reduction D [A≡B] (refl (ℕ (wf ⊢A)))
escapeEq (ne′ K [ ⊢A , ⊢B , D ] neK) (ne₌ M [ ⊢A′ , ⊢B′ , D′ ] neM K==M) =
  reduction D D′ (==-correct ⊢B (ne neK) ⊢B′ (ne neM) K==M)
escapeEq {Γ = Γ} (Π′ F G [ ⊢A , ⊢B , D ] typeΠ ⊢F ⊢G [F] [G] G-ext) (Π₌ F′ G′ D′ TyΠ′ Π≡Π [F≡F′] [G≡G′]) =
  reduction D D′ Π≡Π
escapeEq (emb 0<1 [A]) [A≡B] = escapeEq [A] [A≡B]

-- Reducible terms are well-formed.
escapeTerm : ∀ {l Γ A t} → ([A] : Γ ⊩⟨ l ⟩ A)
              → Γ ⊩⟨ l ⟩ t ∷ A / [A]
              → Γ ⊢ t ∷ A
escapeTerm (U (U l′ l< ⊢Γ)) (Uₜ A [ ⊢t , ⊢u , d ] typeA [A]) = ⊢t
escapeTerm (ℕ D) (ℕₜ n [ ⊢t , ⊢u , d ] prop) =
  conv ⊢t (sym (subset* (red D)))
escapeTerm (ne′ K D neK) (neₜ k [ ⊢t , ⊢u , d ] nf) =
  conv ⊢t (sym (subset* (red D)))
escapeTerm (Π′ F G D typeΠ ⊢F ⊢G [F] [G] G-ext)
               (f , [ ⊢t , ⊢u , d ] , funcF , [f] , [f]₁) =
  conv ⊢t (sym (subset* (red D)))
escapeTerm (emb 0<1 A) t = escapeTerm A t

-- Reducible term equality respect the equality relation.
escapeTermEq : ∀ {l Γ A t u} → ([A] : Γ ⊩⟨ l ⟩ A)
                → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A]
                → Γ ⊢ t ≡ u ∷ A
escapeTermEq (U (U l′ l< ⊢Γ)) (Uₜ₌ A B d d′ typeA typeB A≡B [A] [B] [A≡B]) =
  reductionₜ (id (U ⊢Γ)) (redₜ d) (redₜ d′) A≡B
escapeTermEq (ℕ D) (ℕₜ₌ k k′ [ ⊢t , ⊢u , d ] [ ⊢t′ , ⊢u′ , d′ ] natn natn′ eq) =
  reductionₜ (red D) d d′ (==-correctTerm ⊢u (naturalDnf natn) ⊢u′ (naturalDnf natn′) eq)
escapeTermEq (ne′ K D neK)
                 (neₜ₌ k m [ ⊢t , ⊢u , d ] [ ⊢t′ , ⊢u′ , d′ ] (neNfₜ₌ neT neU t≡u)) =
  let (_ , eq) = ==-correctNe ⊢u neT ⊢u′ neU t≡u in
  reductionₜ (red D) d d′ eq
escapeTermEq (Π′ F G D typeΠ ⊢F ⊢G [F] [G] G-ext)
                 (Πₜ₌ f g d d′ funcF funcG f==g f≡g [f] [g] [f≡g]) =
  reductionₜ (red D) (redₜ d) (redₜ d′) f≡g
escapeTermEq (emb 0<1 A) t≡u = escapeTermEq A t≡u
