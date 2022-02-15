{-# OPTIONS --without-K --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped as U
open import Definition.Typed
open import Definition.Typed.Weakening
open import Agda.Primitive

open import Tools.Product
open import Tools.Embedding
import Tools.PropositionalEquality as PE

-- The different cases of the logical relation are spread out through out
-- this file. This is due to them having different dependencies.

-- We will refer to expressions that satisfies the logical relation as reducible.

-- Reducibility of Neutrals:

-- Neutral type
record _⊩ne_ (Γ : Con Term) (A : Term) : Set where
  constructor ne
  field
    K   : Term
    D   : Γ ⊢ A :⇒*: K
    neK : Neutral K
    K≡K : Γ ⊢ K ~ K ∷ U

-- Neutral type equality
record _⊩ne_≡_/_ (Γ : Con Term) (A B : Term) ([A] : Γ ⊩ne A) : Set where
  constructor ne₌
  open _⊩ne_ [A]
  field
    M   : Term
    D′  : Γ ⊢ B :⇒*: M
    neM : Neutral M
    K≡M : Γ ⊢ K ~ M ∷ U

-- Neutral term in WHNF
record _⊩neNf_∷_ (Γ : Con Term) (k A : Term) : Set where
  inductive
  constructor neNfₜ
  field
    neK  : Neutral k
    ⊢k   : Γ ⊢ k ∷ A
    k≡k  : Γ ⊢ k ~ k ∷ A

-- Neutral term
record _⊩ne_∷_/_ (Γ : Con Term) (t A : Term) ([A] : Γ ⊩ne A) : Set where
  inductive
  constructor neₜ
  open _⊩ne_ [A]
  field
    k   : Term
    d   : Γ ⊢ t :⇒*: k ∷ K
    nf  : Γ ⊩neNf k ∷ K

-- Neutral term equality in WHNF
record _⊩neNf_≡_∷_ (Γ : Con Term) (k m A : Term) : Set where
  inductive
  constructor neNfₜ₌
  field
    neK  : Neutral k
    neM  : Neutral m
    k≡m  : Γ ⊢ k ~ m ∷ A

-- Neutral term equality
record _⊩ne_≡_∷_/_ (Γ : Con Term) (t u A : Term) ([A] : Γ ⊩ne A) : Set where
  constructor neₜ₌
  open _⊩ne_ [A]
  field
    k m : Term
    d   : Γ ⊢ t :⇒*: k ∷ K
    d′  : Γ ⊢ u :⇒*: m ∷ K
    nf  : Γ ⊩neNf k ≡ m ∷ K

-- Reducibility of natural numbers:

-- Natural number type
_⊩ℕ_ : (Γ : Con Term) (A : Term) → Set
Γ ⊩ℕ A = Γ ⊢ A :⇒*: ℕ

-- Natural number type equality
data _⊩ℕ_≡_ (Γ : Con Term) (A B : Term) : Set where
  ℕ₌ : Γ ⊢ B ⇒* ℕ → Γ ⊩ℕ A ≡ B

mutual
  -- Natural number term
  data _⊩ℕ_∷ℕ (Γ : Con Term) (t : Term) : Set where
    ℕₜ : (n : Term) (d : Γ ⊢ t :⇒*: n ∷ ℕ) (n≡n : Γ ⊢ n ≅ n ∷ ℕ)
         (prop : Natural-prop Γ n)
       → Γ ⊩ℕ t ∷ℕ

  -- WHNF property of natural number terms
  data Natural-prop (Γ : Con Term) : (n : Term) → Set where
    sucᵣ  : ∀ {n} → Γ ⊩ℕ n ∷ℕ → Natural-prop Γ (suc n)
    zeroᵣ : Natural-prop Γ zero
    ne    : ∀ {n} → Γ ⊩neNf n ∷ ℕ → Natural-prop Γ n

mutual
  -- Natural number term equality
  data _⊩ℕ_≡_∷ℕ (Γ : Con Term) (t u : Term) : Set where
    ℕₜ₌ : (k k′ : Term) (d : Γ ⊢ t :⇒*: k  ∷ ℕ) (d′ : Γ ⊢ u :⇒*: k′ ∷ ℕ)
          (k≡k′ : Γ ⊢ k ≅ k′ ∷ ℕ)
          (prop : [Natural]-prop Γ k k′) → Γ ⊩ℕ t ≡ u ∷ℕ

  -- WHNF property of Natural number term equality
  data [Natural]-prop (Γ : Con Term) : (n n′ : Term) → Set where
    sucᵣ  : ∀ {n n′} → Γ ⊩ℕ n ≡ n′ ∷ℕ → [Natural]-prop Γ (suc n) (suc n′)
    zeroᵣ : [Natural]-prop Γ zero zero
    ne    : ∀ {n n′} → Γ ⊩neNf n ≡ n′ ∷ ℕ → [Natural]-prop Γ n n′

-- Natural extraction from term WHNF property
natural : ∀ {Γ n} → Natural-prop Γ n → Natural n
natural (sucᵣ x) = sucₙ
natural zeroᵣ = zeroₙ
natural (ne (neNfₜ neK ⊢k k≡k)) = ne neK

-- Natural extraction from term equality WHNF property
split : ∀ {Γ a b} → [Natural]-prop Γ a b → Natural a × Natural b
split (sucᵣ x) = sucₙ , sucₙ
split zeroᵣ = zeroₙ , zeroₙ
split (ne (neNfₜ₌ neK neM k≡m)) = ne neK , ne neM

-- Type levels

data TypeLevel : Set where
  ⁰ : TypeLevel
  ¹ : TypeLevel

data _<_ : (i j : TypeLevel) → Set where
  0<1 : ⁰ < ¹

toLevel : TypeLevel → Level
toLevel ⁰ = lzero
toLevel ¹ = lsuc lzero

-- Logical relation

record LogRelKit (ℓ : Level) : Set (lsuc (lsuc ℓ)) where
  constructor Kit
  field
    _⊩U : (Γ : Con Term) → Set (lsuc ℓ)
    _⊩Π_ : (Γ : Con Term) → Term → Set (lsuc ℓ)

    _⊩_ : (Γ : Con Term) → Term → Set (lsuc ℓ)
    _⊩_≡_/_ : (Γ : Con Term) (A B : Term) → Γ ⊩ A → Set ℓ
    _⊩_∷_/_ : (Γ : Con Term) (t A : Term) → Γ ⊩ A → Set ℓ
    _⊩_≡_∷_/_ : (Γ : Con Term) (t u A : Term) → Γ ⊩ A → Set ℓ

module LogRel (l : TypeLevel) (rec : ∀ {l′} → l′ < l → LogRelKit (toLevel l)) where

  record _⊩¹U (Γ : Con Term) : Set (lsuc (lsuc (toLevel l))) where
    constructor Uᵣ
    field
      l′ : TypeLevel
      l< : l′ < l
      ⊢Γ : ⊢ Γ

  -- Universe type equality
  record _⊩¹U≡_ (Γ : Con Term) (B : Term) : Set (lsuc (toLevel l)) where
    constructor U₌
    field
      B≡U : B PE.≡ U

  -- Universe term
  record _⊩¹U_∷U/_ {l′} (Γ : Con Term) (t : Term) (l< : l′ < l) : Set (lsuc (toLevel l)) where
    constructor Uₜ
    open LogRelKit (rec l<)
    field
      A     : Term
      d     : Γ ⊢ t :⇒*: A ∷ U
      typeA : Type A
      A≡A   : Γ ⊢ A ≅ A ∷ U
      [t]   : Γ ⊩ t

  -- Universe term equality
  record _⊩¹U_≡_∷U/_ {l′} (Γ : Con Term) (t u : Term) (l< : l′ < l) : Set (lsuc (toLevel l)) where
    constructor Uₜ₌
    open LogRelKit (rec l<)
    field
      A B   : Term
      d     : Γ ⊢ t :⇒*: A ∷ U
      d′    : Γ ⊢ u :⇒*: B ∷ U
      typeA : Type A
      typeB : Type B
      A≡B   : Γ ⊢ A ≅ B ∷ U
      [t]   : Γ ⊩ t
      [u]   : Γ ⊩ u
      [t≡u] : Γ ⊩ t ≡ u / [t]

  RedRel : Set (lsuc (lsuc (lsuc (toLevel l))))
  RedRel = Con Term → Term → (Term → Set (lsuc (toLevel l))) → (Term → Set (lsuc (toLevel l))) → (Term → Term → Set (lsuc (toLevel l))) → Set (lsuc (lsuc (toLevel l)))

  record _⊩⁰_/_ (Γ : Con Term) (A : Term) (_⊩_▸_▸_▸_ : RedRel) : Set (lsuc (lsuc (toLevel l))) where
    inductive
    eta-equality
    constructor LRPack
    field
      ⊩Eq : Term → Set (lsuc (toLevel l))
      ⊩Term : Term → Set (lsuc (toLevel l))
      ⊩EqTerm : Term → Term → Set (lsuc (toLevel l))
      ⊩LR : Γ ⊩ A ▸ ⊩Eq ▸ ⊩Term ▸ ⊩EqTerm

  _⊩⁰_≡_/_ : {R : RedRel} (Γ : Con Term) (A B : Term) → Γ ⊩⁰ A / R → Set (lsuc (toLevel l))
  Γ ⊩⁰ A ≡ B / LRPack ⊩Eq ⊩Term ⊩EqTerm ⊩Red = ⊩Eq B

  _⊩⁰_∷_/_ : {R : RedRel} (Γ : Con Term) (t A : Term) → Γ ⊩⁰ A / R → Set (lsuc (toLevel l))
  Γ ⊩⁰ t ∷ A / LRPack ⊩Eq ⊩Term ⊩EqTerm ⊩Red = ⊩Term t

  _⊩⁰_≡_∷_/_ : {R : RedRel} (Γ : Con Term) (t u A : Term) → Γ ⊩⁰ A / R → Set (lsuc (toLevel l))
  Γ ⊩⁰ t ≡ u ∷ A / LRPack ⊩Eq ⊩Term ⊩EqTerm ⊩Red = ⊩EqTerm t u

  record _⊩¹Π_/_ (Γ : Con Term) (A : Term) (R : RedRel) : Set (lsuc (lsuc (toLevel l))) where
    inductive
    eta-equality
    constructor Πᵣ
    field
      F : Term
      G : Term
      D : Γ ⊢ A :⇒*: Π F ▹ G
      ⊢F : Γ ⊢ F
      ⊢G : Γ ∙ F ⊢ G
      A≡A : Γ ⊢ Π F ▹ G ≅ Π F ▹ G
      [F] : ∀ {ρ Δ} → ρ ∷ Δ ⊆ Γ → (⊢Δ : ⊢ Δ) → Δ ⊩⁰ U.wk ρ F / R
      [G] : ∀ {ρ Δ a}
          → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
          → Δ ⊩⁰ a ∷ U.wk ρ F / [F] [ρ] ⊢Δ
          → Δ ⊩⁰ U.wk (lift ρ) G [ a ] / R
      G-ext : ∀ {ρ Δ a b}
            → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
            → ([a] : Δ ⊩⁰ a ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
            → ([b] : Δ ⊩⁰ b ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
            → Δ ⊩⁰ a ≡ b ∷ U.wk ρ F / [F] [ρ] ⊢Δ
            → Δ ⊩⁰ U.wk (lift ρ) G [ a ] ≡ U.wk (lift ρ) G [ b ] / [G] [ρ] ⊢Δ [a]

  record _⊩¹Π_≡_/_ {R : RedRel} (Γ : Con Term) (A B : Term) ([A] : Γ ⊩¹Π A / R) : Set (lsuc (toLevel l)) where
    inductive
    eta-equality
    constructor Π₌
    open _⊩¹Π_/_ [A]
    field
      F′     : Term
      G′     : Term
      D′     : Γ ⊢ B ⇒* Π F′ ▹ G′
      A≡B    : Γ ⊢ Π F ▹ G ≅ Π F′ ▹ G′
      [F≡F′] : ∀ {ρ Δ}
             → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
             → Δ ⊩⁰ U.wk ρ F ≡ U.wk ρ F′ / [F] [ρ] ⊢Δ
      [G≡G′] : ∀ {ρ Δ a}
             → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
             → ([a] : Δ ⊩⁰ a ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
             → Δ ⊩⁰ U.wk (lift ρ) G [ a ] ≡ U.wk (lift ρ) G′ [ a ] / [G] [ρ] ⊢Δ [a]

  -- Term of Π-type
  _⊩¹Π_∷_/_ : {R : RedRel} (Γ : Con Term) (t A : Term) ([A] : Γ ⊩¹Π A / R) → Set (lsuc (toLevel l))
  Γ ⊩¹Π t ∷ A / Πᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext =
    ∃ λ f → Γ ⊢ t :⇒*: f ∷ Π F ▹ G
          × Function f
          × Γ ⊢ f ≅ f ∷ Π F ▹ G
          × (∀ {ρ Δ a b}
            → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
              ([a] : Δ ⊩⁰ a ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
              ([b] : Δ ⊩⁰ b ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
              ([a≡b] : Δ ⊩⁰ a ≡ b ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
            → Δ ⊩⁰ U.wk ρ f ∘ a ≡ U.wk ρ f ∘ b ∷ U.wk (lift ρ) G [ a ] / [G] [ρ] ⊢Δ [a])
          × (∀ {ρ Δ a} → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
            → ([a] : Δ ⊩⁰ a ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
            → Δ ⊩⁰ U.wk ρ f ∘ a ∷ U.wk (lift ρ) G [ a ] / [G] [ρ] ⊢Δ [a])
  -- Issue: Agda complains about record use not being strictly positive.
  --        Therefore we have to use ×


  -- Term equality of Π-type
  _⊩¹Π_≡_∷_/_ : {R : RedRel} (Γ : Con Term) (t u A : Term) ([A] : Γ ⊩¹Π A / R) → Set (lsuc (toLevel l))
  Γ ⊩¹Π t ≡ u ∷ A / Πᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext =
    let [A] = Πᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext
    in  ∃₂ λ f g →
        Γ ⊢ t :⇒*: f ∷ Π F ▹ G
    ×   Γ ⊢ u :⇒*: g ∷ Π F ▹ G
    ×   Function f
    ×   Function g
    ×   Γ ⊢ f ≅ g ∷ Π F ▹ G
    ×   Γ ⊩¹Π t ∷ A / [A]
    ×   Γ ⊩¹Π u ∷ A / [A]
    ×   (∀ {ρ Δ a} → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
        → ([a] : Δ ⊩⁰ a ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
        → Δ ⊩⁰ U.wk ρ f ∘ a ≡ U.wk ρ g ∘ a ∷ U.wk (lift ρ) G [ a ] / [G] [ρ] ⊢Δ [a])
  -- Issue: Same as above.


  -- Logical relation definition
  data _⊩LR_▸_▸_▸_ : RedRel where
    LRU : ∀ {Γ} (⊢Γ : ⊢ Γ) → (l' : TypeLevel) → (l< : l' < l) → Γ ⊩LR U
      ▸ (λ B → Γ ⊩¹U≡ B)
      ▸ (λ t → Γ ⊩¹U t ∷U/ l<)
      ▸ (λ t u → Γ ⊩¹U t ≡ u ∷U/ l<)
    LRℕ : ∀ {Γ A} → Γ ⊩ℕ A → Γ ⊩LR A
      ▸ (λ B → ι′ (Γ ⊩ℕ A ≡ B))
      ▸ (λ t → ι′ (Γ ⊩ℕ t ∷ℕ))
      ▸ (λ t u → ι′ (Γ ⊩ℕ t ≡ u ∷ℕ))
    LRne : ∀ {Γ A} → (neA : Γ ⊩ne A) → Γ ⊩LR A
      ▸ (λ B → ι′ (Γ ⊩ne A ≡ B / neA))
      ▸ (λ t → ι′ (Γ ⊩ne t ∷ A / neA))
      ▸ (λ t u → ι′ (Γ ⊩ne t ≡ u ∷ A / neA))
    LRΠ : ∀ {Γ A} → (ΠA : Γ ⊩¹Π A / _⊩LR_▸_▸_▸_) → Γ ⊩LR A
      ▸ (λ B → Γ ⊩¹Π A ≡ B / ΠA)
      ▸ (λ t → Γ ⊩¹Π t ∷ A / ΠA)
      ▸ (λ t u → Γ ⊩¹Π t ≡ u ∷ A / ΠA)
    LRemb : ∀ {Γ A l′} (l< : l′ < l) (let open LogRelKit (rec l<)) ([A] : Γ ⊩ A) → Γ ⊩LR A
      ▸ (λ B → ι (Γ ⊩ A ≡ B / [A]))
      ▸ (λ t → ι (Γ ⊩ t ∷ A / [A]))
      ▸ (λ t u → ι (Γ ⊩ t ≡ u ∷ A / [A]))

  _⊩¹_ : (Γ : Con Term) → (A : Term) → Set (lsuc (lsuc (toLevel l)))
  Γ ⊩¹ A = Γ ⊩⁰ A / _⊩LR_▸_▸_▸_

  _⊩¹_≡_/_ : (Γ : Con Term) (A B : Term) → Γ ⊩¹ A → Set (lsuc (toLevel l))
  Γ ⊩¹ A ≡ B / [A] = Γ ⊩⁰ A ≡ B / [A]

  _⊩¹_∷_/_ : (Γ : Con Term) (t A : Term) → Γ ⊩¹ A → Set (lsuc (toLevel l))
  Γ ⊩¹ t ∷ A / [A] = Γ ⊩⁰ t ∷ A / [A]

  _⊩¹_≡_∷_/_ : (Γ : Con Term) (t u A : Term) → Γ ⊩¹ A → Set (lsuc (toLevel l))
  Γ ⊩¹ t ≡ u ∷ A / [A] = Γ ⊩⁰ t ≡ u ∷ A / [A]

open LogRel public using (Uᵣ; Πᵣ; Π₌; U₌ ; Uₜ; Uₜ₌ ; LRU ; LRℕ ; LRne ; LRΠ ; LRemb ; LRPack)

pattern Πₜ f d funcF f≡f [f] [f]₁ = f , d , funcF , f≡f , [f] , [f]₁
pattern Πₜ₌ f g d d′ funcF funcG f≡g [f] [g] [f≡g] = f , g , d , d′ , funcF , funcG , f≡g , [f] , [g] , [f≡g]
pattern ℕᵣ a = LRPack _ _ _ (LRℕ a)
pattern emb′ a b = LRPack _ _ _ (LRemb a b)
pattern Uᵣ′ a b c = LRPack _ _ _ (LRU c a b)
pattern ne′ a b c d = LRPack _ _ _ (LRne (ne a b c d))
pattern Πᵣ′ a b c d e f g h i = LRPack _ _ _ (LRΠ (Πᵣ a b c d e f g h i))

kit₀ : LogRelKit (lsuc (lzero))
kit₀ = Kit _⊩¹U (λ Γ A → Γ ⊩¹Π A / _⊩LR_▸_▸_▸_) _⊩¹_ _⊩¹_≡_/_ _⊩¹_∷_/_ _⊩¹_≡_∷_/_ where open LogRel ⁰ (λ ())

logRelRec : ∀ l {l′} → l′ < l → LogRelKit (toLevel l)
logRelRec ⁰ = λ ()
logRelRec ¹ 0<1 = kit₀

kit : ∀ (l : TypeLevel) → LogRelKit (lsuc (toLevel l))
kit l = Kit _⊩¹U (λ Γ A → Γ ⊩¹Π A / _⊩LR_▸_▸_▸_) _⊩¹_ _⊩¹_≡_/_ _⊩¹_∷_/_ _⊩¹_≡_∷_/_ where open LogRel l (logRelRec l)

-- a bit of repetition in "kit ¹" definition, would work better with Fin 2 for
-- TypeLevel because you could recurse.

record _⊩′⟨_⟩U (Γ : Con Term) (l : TypeLevel) : Set where
  constructor Uᵣ
  field
    l′ : TypeLevel
    l< : l′ < l
    ⊢Γ : ⊢ Γ

_⊩′⟨_⟩Π_ : (Γ : Con Term) (l : TypeLevel) → Term → Set (lsuc (lsuc (toLevel l)))
Γ ⊩′⟨ l ⟩Π A = Γ ⊩Π A where open LogRelKit (kit l)

_⊩⟨_⟩_ : (Γ : Con Term) (l : TypeLevel) → Term → Set (lsuc (lsuc (toLevel l)))
Γ ⊩⟨ l ⟩ A = Γ ⊩ A where open LogRelKit (kit l)

_⊩⟨_⟩_≡_/_ : (Γ : Con Term) (l : TypeLevel) (A B : Term) → Γ ⊩⟨ l ⟩ A → Set (lsuc (toLevel l))
Γ ⊩⟨ l ⟩ A ≡ B / [A] = Γ ⊩ A ≡ B / [A] where open LogRelKit (kit l)

_⊩⟨_⟩_∷_/_ : (Γ : Con Term) (l : TypeLevel) (t A : Term) → Γ ⊩⟨ l ⟩ A → Set (lsuc (toLevel l))
Γ ⊩⟨ l ⟩ t ∷ A / [A] = Γ ⊩ t ∷ A / [A] where open LogRelKit (kit l)

_⊩⟨_⟩_≡_∷_/_ : (Γ : Con Term) (l : TypeLevel) (t u A : Term) → Γ ⊩⟨ l ⟩ A → Set (lsuc (toLevel l))
Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A] = Γ ⊩ t ≡ u ∷ A / [A] where open LogRelKit (kit l)
