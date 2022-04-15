-- Options/Maybe monad

{-# OPTIONS --without-K --safe #-}

module Tools.Maybe where

data Maybe (P : Set) : Set where
  just  : P → Maybe P
  nothing : Maybe P
