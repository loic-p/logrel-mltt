{-# OPTIONS --without-K --allow-unsolved-metas #-}

module Definition.LogicalRelation.Properties.Normalize where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.Weakening
open import Definition.LogicalRelation
-- open import Definition.LogicalRelation.ShapeView
-- open import Definition.LogicalRelation.Irrelevance
-- open import Definition.LogicalRelation.Properties.Reflexivity
-- open import Definition.LogicalRelation.Properties.Escape
-- open import Definition.LogicalRelation.Properties.Symmetry

-- open import Tools.Empty
open import Tools.Product
import Tools.PropositionalEquality as PE

nf : ∀ {l Γ A}
   → Γ ⊩⟨ l ⟩ A
   → ∃ (λ A′ → Γ ⊢ A ↘ A′)
nf (U′ l′ l< ⊢Γ) = U , ((id (U ⊢Γ)) , U)
nf (ℕ [ ⊢A , ⊢B , D ]) = ℕ , (D , ℕ)
nf (ne′ K [ ⊢A , ⊢B , D ] neK) = K , (D , (ne neK))
nf (Π′ F G [ ⊢A , ⊢B , D ] typeΠ ⊢F ⊢G [F] [G] G-ext) = Π F ▹ G , D , (typeDnf typeΠ)
nf (emb 0<1 [A]) = nf [A]

nfEq : ∀ {l Γ A B}
     → ([A] : Γ ⊩⟨ l ⟩ A)
     → ([A≡B] : Γ ⊩⟨ l ⟩ A ≡ B / [A])
     → (∃₂ (λ A′ B′ → Γ ⊢ A ↘ A′ × (Γ ⊢ B ↘ B′ × A′ == B′)))
nfEq (U′ l′ l< ⊢Γ) PE.refl =
  U , U , (id (U ⊢Γ) , U) , (id (U ⊢Γ) , U) , ==-refl U
nfEq (ℕ [ ⊢A , ⊢B , D ]) [A≡B] =
  ℕ , ℕ , (D , ℕ) , ([A≡B] , ℕ) , ==-refl ℕ
nfEq (ne′ K [ ⊢A , ⊢B , D ] neK) (ne₌ M [ ⊢A₁ , ⊢B₁ , D₁ ] neM K==M) =
  K , M , (D , ne neK) , (D₁ , ne neM) , K==M
nfEq (Π′ F G D typeΠ ⊢F ⊢G [F] [G] G-ext) (Π₌ F′ G′ D′ typeΠ′ A≡B [F≡F′] [G≡G′]) =
  (Π F ▹ G) , (Π F′ ▹ G′) , (red D , typeDnf typeΠ) , (red D′ , typeDnf typeΠ′) , A≡B
nfEq (emb 0<1 [A]) [A≡B] = nfEq [A] [A≡B]

nfTerm : ∀ {l Γ A t}
       → ([A] : Γ ⊩⟨ l ⟩ A)
       → ([t] : Γ ⊩⟨ l ⟩ t ∷ A / [A])
       → ∃ (λ t′ → (Γ ⊢ t ↘ t′ ∷ A) × (Γ ⊩⟨ l ⟩ t′ ∷ A / [A]))
nfTerm (U′ l′ l< ⊢Γ) (Uₜ A d typeA [t]) = {!!}
nfTerm (ℕ [ ⊢A , ⊢B , D ]) (ℕₜ n d natn) = {!!}
nfTerm (ne′ K [ ⊢A , ⊢B , D ] neK) (neₜ k d nf₁) = {!!}
nfTerm (Π′ F G [ ⊢A , ⊢B , D ] typeΠ ⊢F ⊢G [F] [G] G-ext) [t] = {!!}
nfTerm (emb 0<1 [A]) [t] = nfTerm [A] [t]

nfTermEq : ∀ {l Γ A t u}
         → ([A] : Γ ⊩⟨ l ⟩ A)
         → ([t] : Γ ⊩⟨ l ⟩ t ∷ A / [A])
         → ([u] : Γ ⊩⟨ l ⟩ u ∷ A / [A])
         → ([t≡u] : Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A])
         → ∃₂ (λ t′ u′ → Γ ⊢ t ↘ t′ ∷ A × (Γ ⊢ u ↘ u′ ∷ A × t′ == u′))
nfTermEq = {!!}
