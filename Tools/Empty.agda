-- The empty type; also used as absurd proposition (``Falsity'').

{-# OPTIONS --without-K --safe #-}

module Tools.Empty where

data ⊥ : Set where

-- Ex falsum quod libet.

⊥-elim : ∀ {a} {A : Set a} → ⊥ → A
⊥-elim ()

⊥-elimω : ∀ {A : Agda.Primitive.Setω} → ⊥ → A
⊥-elimω ()
