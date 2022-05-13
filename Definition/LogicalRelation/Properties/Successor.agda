{-# OPTIONS --without-K #-}

module Definition.LogicalRelation.Properties.Successor where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.ShapeView

open import Tools.Product

suc-red : ∀ {Γ n n′} → Γ ⊢ n ⇒* n′ ∷ ℕ → Γ ⊢ suc n ⇒* suc n′ ∷ ℕ
suc-red (id x) = id (suc x)
suc-red (x ⇨ d) = suc-subst x ⇨ (suc-red d)

-- Helper function for successors for specific reducible derivations.
sucTerm′ : ∀ {l Γ n}
           ([ℕ] : Γ ⊩⟨ l ⟩ℕ ℕ)
         → Γ ⊩⟨ l ⟩ n ∷ ℕ / ℕ-intr [ℕ]
         → Γ ⊩⟨ l ⟩ suc n ∷ ℕ / ℕ-intr [ℕ]
sucTerm′ (noemb D) (ℕₜ n [ ⊢t , ⊢u , d ] prop) =
  ℕₜ _ [ suc ⊢t , suc ⊢u , suc-red d ]
         (suc prop)
sucTerm′ (emb 0<1 x) [n] = sucTerm′ x [n]

-- Reducible natural numbers can be used to construct reducible successors.
sucTerm : ∀ {l Γ n} ([ℕ] : Γ ⊩⟨ l ⟩ ℕ)
        → Γ ⊩⟨ l ⟩ n ∷ ℕ / [ℕ]
        → Γ ⊩⟨ l ⟩ suc n ∷ ℕ / [ℕ]
sucTerm [ℕ] [n] =
  let [n]′ = irrelevanceTerm [ℕ] (ℕ-intr (ℕ-elim [ℕ])) [n]
  in  irrelevanceTerm (ℕ-intr (ℕ-elim [ℕ]))
                      [ℕ]
                      (sucTerm′ (ℕ-elim [ℕ]) [n]′)

-- Helper function for successor equality for specific reducible derivations.
sucEqTerm′ : ∀ {l Γ n n′}
             ([ℕ] : Γ ⊩⟨ l ⟩ℕ ℕ)
           → Γ ⊩⟨ l ⟩ n ≡ n′ ∷ ℕ / ℕ-intr [ℕ]
           → Γ ⊩⟨ l ⟩ suc n ≡ suc n′ ∷ ℕ / ℕ-intr [ℕ]
sucEqTerm′ (noemb D) (ℕₜ₌ k k′ [ ⊢t , ⊢u , d ]
                              [ ⊢t₁ , ⊢u₁ , d₁ ] prop₁ prop₂ u==u₁) =
  ℕₜ₌ _ _ [ suc ⊢t , suc ⊢u , suc-red d ] [ suc ⊢t₁ , suc ⊢u₁ , suc-red d₁ ]
    (suc prop₁) (suc prop₂) (==-suc-cong u==u₁)
sucEqTerm′ (emb 0<1 x) [n≡n′] = sucEqTerm′ x [n≡n′]

-- Reducible natural number equality can be used to construct reducible equality
-- of the successors of the numbers.
sucEqTerm : ∀ {l Γ n n′} ([ℕ] : Γ ⊩⟨ l ⟩ ℕ)
          → Γ ⊩⟨ l ⟩ n ≡ n′ ∷ ℕ / [ℕ]
          → Γ ⊩⟨ l ⟩ suc n ≡ suc n′ ∷ ℕ / [ℕ]
sucEqTerm [ℕ] [n≡n′] =
  let [n≡n′]′ = irrelevanceEqTerm [ℕ] (ℕ-intr (ℕ-elim [ℕ])) [n≡n′]
  in  irrelevanceEqTerm (ℕ-intr (ℕ-elim [ℕ])) [ℕ]
                        (sucEqTerm′ (ℕ-elim [ℕ]) [n≡n′]′)
