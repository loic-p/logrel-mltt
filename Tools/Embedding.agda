{-# OPTIONS --without-K --safe #-}

module Tools.Embedding where

open import Agda.Primitive

data ι {ℓ : Level} (A : Set ℓ) : Set (lsuc ℓ) where
  ιx : A → ι A

data ι′ {ℓ : Level} (A : Set) : Set ℓ where
  ιx : A → ι′ A

data ι″ {ℓ} (A : Set ℓ) : Setω where
  ιx : A → ι″ A
