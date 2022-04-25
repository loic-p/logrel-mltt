{-# OPTIONS --without-K #-}

module Definition.Typed.Reduction where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties


-- expansion of type equality
reduction : ∀ {A A′ B B′ Γ}
          → Γ ⊢ A ⇒* A′
          → Γ ⊢ B ⇒* B′
          → Γ ⊢ A′ ≡ B′
          → Γ ⊢ A ≡ B
reduction D D′ A′≡B′ =
  trans (subset* D) (trans A′≡B′ (sym (subset* D′)))

reduction′ : ∀ {A A′ B B′ Γ}
          → Γ ⊢ A ⇒* A′
          → Γ ⊢ B ⇒* B′
          → Γ ⊢ A ≡ B
          → Γ ⊢ A′ ≡ B′
reduction′ D D′ A≡B =
  trans (sym (subset* D)) (trans A≡B (subset* D′))

-- expansion of term equality
reductionₜ : ∀ {a a′ b b′ A B Γ}
           → Γ ⊢ A ⇒* B
           → Γ ⊢ a ⇒* a′ ∷ B
           → Γ ⊢ b ⇒* b′ ∷ B
           → Γ ⊢ a′ ≡ b′ ∷ B
           → Γ ⊢ a ≡ b ∷ A
reductionₜ D d d′ a′≡b′ =
  conv (trans (subset*Term d)
              (trans a′≡b′ (sym (subset*Term d′))))
       (sym (subset* D))

reductionₜ′ : ∀ {a a′ b b′ A B Γ}
           → Γ ⊢ A ⇒* B
           → Γ ⊢ a ⇒* a′ ∷ B
           → Γ ⊢ b ⇒* b′ ∷ B
           → Γ ⊢ a ≡ b ∷ A
           → Γ ⊢ a′ ≡ b′ ∷ B
reductionₜ′ D d d′ a≡b =
  trans (sym (subset*Term d))
        (trans (conv a≡b (subset* D)) (subset*Term d′))
