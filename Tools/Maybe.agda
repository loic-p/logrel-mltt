-- Options/Maybe monad

{-# OPTIONS --without-K --safe #-}

module Tools.Maybe where
open import Tools.PropositionalEquality
open import Tools.Empty

data Maybe (P : Set) : Set where
  just  : P → Maybe P
  nothing : Maybe P

inversion : {P : Set} {x : P} → just x ≡ nothing → ⊥
inversion ()
