{-# OPTIONS #-}

open import Definition.Typed.EqualityRelation

module Definition.Interpretation {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped as U
open import Definition.Typed
open import Definition.Typed.Weakening
open import Agda.Primitive

open import Tools.Product
open import Tools.Nat
open import Tools.Embedding
import Tools.PropositionalEquality as PE

postulate funext : ∀ {ℓ ℓ′} → {A : Set ℓ} → {B : A → Set ℓ′} → (f g : (x : A) → B x) → ((x : A) → f x PE.≡ g x) → f PE.≡ g

coe : {ℓ : Agda.Primitive.Level} → {A B : Set ℓ} → A PE.≡ B → A → B
coe PE.refl a = a

Σeq : ∀ {ℓ ℓ′} → {A B : Set ℓ} → {P : A → Set ℓ′} → {Q : B → Set ℓ′}
    → (e1 : A PE.≡ B) → (e2 : ∀ x → P x PE.≡ Q (coe e1 x))
    → Σ A P PE.≡ Σ B Q
Σeq PE.refl e2 = aux (funext _ _ e2)
  where
    aux : ∀ {ℓ ℓ′} → {A : Set ℓ} {P' Q' : A → Set ℓ′} → P' PE.≡ Q' → Σ A P' PE.≡ Σ A Q'
    aux PE.refl = PE.refl

Πeq : ∀ {ℓ ℓ′} → {A B : Set ℓ} → {P : A → Set ℓ′} → {Q : B → Set ℓ′}
    → (e1 : A PE.≡ B) → (e2 : ∀ x → P x PE.≡ Q (coe e1 x))
    → ((x : A) → P x) PE.≡ ((x : B) → Q x)
Πeq PE.refl e2 = aux (funext _ _ e2)
  where
    aux : ∀ {ℓ ℓ′} → {A : Set ℓ} {P' Q' : A → Set ℓ′} → P' PE.≡ Q' → ((x : A) → P' x) PE.≡ ((x : A) → Q' x)
    aux PE.refl = PE.refl

data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where

data ⊤₁ : Set₁ where
  tt : ⊤₁

inCon : Con Term → Nat → Set
inCon ε n = ⊥
inCon (Γ ∙ x) Nat.zero = ⊤
inCon (Γ ∙ x) (1+ n) = inCon Γ n

data ⊩_ : (Γ : Con Term) → Set₂
[[_]]C : ∀ {Γ} → ⊩ Γ → Set₁
data _/_⊩_ : (Γ : Con Term) (Γε : ⊩ Γ) (A : Term) → Set₂
[[_⊢_]]T : ∀ {Γ A} → (Γε : ⊩ Γ) → Γ / Γε ⊩ A → [[ Γε ]]C → Set₁
data _/_⊩_∷_ : (Γ : Con Term) (Γε : ⊩ Γ) (t : Term) ([A] : [[ Γε ]]C → Set₁) → Set₂
[[_⊢_∋_]]t : ∀ {Γ t} → (Γε : ⊩ Γ) → ([A] : [[ Γε ]]C → Set₁) → (tε : Γ / Γε ⊩ t ∷ [A]) → (ρ : [[ Γε ]]C) → [A] ρ

--data exCon : {Γ : Con Term} {[Γ] : Set₁} (Γε : ⊩ Γ ▸ [Γ]) (n : Nat) ([A] : [Γ] → Set₁) (a : ∀ ρ → [A] ρ) → Set₂

data ⊩_ where
  ε : ⊩ ε
  _∙_ : ∀ {Γ A} → (Γε : ⊩ Γ) → (Aε : Γ / Γε ⊩ A) → (⊩ Γ ∙ A)

[[ ε ]]C = ⊤₁
[[ Γε ∙ Aε ]]C = Σ [[ Γε ]]C (λ ρ → [[ Γε ⊢ Aε ]]T ρ)

data _/_⊩_ where
  ⊩U : ∀ {Γ} Γε → Γ / Γε ⊩ U
  ⊩Π : ∀ {Γ F G} Γε → (Fε : Γ / Γε ⊩ F) → Γ ∙ F / Γε ∙ Fε ⊩ G → Γ / Γε ⊩ (Π F ▹ G)
  ⊩uni : ∀ {Γ A} Γε → Γ / Γε ⊩ A ∷ (λ ρ → Set) → Γ / Γε ⊩ A

[[ Γε ⊢ ⊩U .Γε ]]T ρ = Set
[[ Γε ⊢ ⊩Π .Γε Fε Gε ]]T ρ = (x : [[ Γε ⊢ Fε ]]T ρ) → [[ Γε ∙ Fε ⊢ Gε ]]T (ρ , x)
[[ Γε ⊢ ⊩uni .Γε Aε ]]T ρ = ι ([[ Γε ⊢ (λ ρ → Set) ∋ Aε ]]t ρ)

data _/_⊩_∷_ where
  ⊩Π   : ∀ {Γ F G} → (Γε : ⊩ Γ)
       → (Fε : Γ / Γε ⊩ F ∷ (λ ρ → Set))
       → (Gε : Γ ∙ F / Γε ∙ (⊩uni Γε Fε) ⊩ G ∷ (λ ρ → Set))
       → Γ / Γε ⊩ (Π F ▹ G) ∷ (λ ρ → Set)
  ⊩app : ∀ {Γ t u} → (Γε : ⊩ Γ) → ([F] : [[ Γε ]]C → Set₁) → ([G] : (ρ : [[ Γε ]]C) → [F] ρ → Set₁)
       → (tε : Γ / Γε ⊩ t ∷ (λ ρ → (x : [F] ρ) → [G] ρ x))
       → (uε : Γ / Γε ⊩ u ∷ [F])
       → Γ / Γε ⊩ t ∘ u ∷ (λ ρ → [G] ρ ([[ Γε ⊢ [F] ∋ uε ]]t ρ))
  ⊩lam : ∀ {Γ F t} → (Γε : ⊩ Γ)
       → (Fε : Γ / Γε ⊩ F)
       → ([G] : (ρ : [[ Γε ∙ Fε ]]C) → Set₁)
       → (tε : Γ ∙ F / Γε ∙ Fε ⊩ t ∷ [G])
       → Γ / Γε ⊩ lam t ∷ (λ ρ → (x : [[ Γε ⊢ Fε ]]T ρ) → [G] (ρ , x))

[[ Γε ⊢ .(λ ρ → Set) ∋ ⊩Π .Γε Fε Gε ]]t ρ =
  (x : [[ Γε ⊢ (λ ρ → Set) ∋ Fε ]]t ρ) → [[ Γε ∙ ⊩uni Γε Fε ⊢ (λ ρ → Set) ∋ Gε ]]t (ρ , ιx x)
[[ Γε ⊢ .(λ ρ → [G] ρ ([[ Γε ⊢ [F] ∋ uε ]]t ρ)) ∋ ⊩app .Γε [F] [G] tε uε ]]t ρ =
  [[ Γε ⊢ (λ ρ → (x : [F] ρ) → [G] ρ x) ∋ tε ]]t ρ ([[ Γε ⊢ [F] ∋ uε ]]t ρ)
[[ Γε ⊢ .(λ ρ → (x : [[ Γε ⊢ Fε ]]T ρ) → [G] (ρ , x)) ∋ ⊩lam .Γε Fε [G] tε ]]t ρ x =
  [[ Γε ∙ Fε ⊢ [G] ∋ tε ]]t (ρ , x)

-- data exCon where
--   exzero : ∀ {Γ [Γ] A [A]} → (Γε : ⊩ Γ ▸ [Γ]) → (Aε : Γε ⊩ A ▸ [A]) → exCon (Γε ∙ Aε) Nat.zero (λ { (ρ , a) → [A] ρ }) (λ { (ρ , a) → a })
--   exsucc : ∀ {Γ [Γ] [A] a B [B] n} → (Γε : ⊩ Γ ▸ [Γ]) → (Bε : Γε ⊩ B ▸ [B]) → exCon Γε n [A] a → exCon (Γε ∙ Bε) (1+ n) (λ { (ρ , b) → [A] ρ }) (λ { (ρ , b) → a ρ })

--   ⊩var : ∀ {Γ [Γ] n [A] a} → (Γε : ⊩ Γ ▸ [Γ]) → exCon Γε n [A] a
--        → Γε ⊩ var n ▸ [A] ∋ a

data PathΣ {ℓ : Agda.Primitive.Level} {A : Set ℓ} (B : A → Set ℓ) (a : A) (t : B a) : (b : A) → B b → Set ℓ where
  refl : PathΣ B a t a t

irrCon : ∀ {Γ} → (Γε Γε' : ⊩ Γ) → Γε PE.≡ Γε'
irrTy : ∀ {Γ Γε A} → (Aε Aε' : Γ / Γε ⊩ A) → Aε PE.≡ Aε'
irrTm₁ : ∀ {Γ Γε t A} → (tε tε' : Γ / Γε ⊩ t ∷ A) → tε PE.≡ tε'
irrTm₂ : ∀ {Γ Γε t A A'} → (tε : Γ / Γε ⊩ t ∷ A) (tε' : Γ / Γε ⊩ t ∷ A') → A PE.≡ A'
irrTmHet : ∀ {Γ Γε t A A'} → (tε : Γ / Γε ⊩ t ∷ A) (tε' : Γ / Γε ⊩ t ∷ A') → Σ (A PE.≡ A') (λ E → PE.subst (λ X → Γ / Γε ⊩ t ∷ X) E tε PE.≡ tε')

irrCon {ε} ε ε = PE.refl
irrCon {Γ ∙ A} (Γε ∙ Aε) (Γε' ∙ Aε') with (irrCon Γε Γε')
irrCon {Γ ∙ A} (Γε ∙ Aε) (.Γε ∙ Aε') | PE.refl with (irrTy Aε Aε')
irrCon {Γ ∙ A} (Γε ∙ Aε) (.Γε ∙ Aε') | PE.refl | PE.refl = PE.refl

irrTy (⊩U _) (⊩U _) = PE.refl
irrTy (⊩Π _ Fε Gε) (⊩Π _ Fε' Gε') with (irrTy Fε Fε')
irrTy (⊩Π _ Fε Gε) (⊩Π _ Fε Gε') | PE.refl with (irrTy Gε Gε')
irrTy (⊩Π _ Fε Gε) (⊩Π _ Fε Gε) | PE.refl | PE.refl = PE.refl
irrTy (⊩uni _ Aε) (⊩uni _ Aε') with (irrTm₁ Aε Aε')
irrTy (⊩uni _ Aε) (⊩uni _ Aε) | PE.refl = PE.refl
irrTy Aε Aε' = {!!}

irrTm₁ tε tε₁ with (irrTmHet tε tε₁)
irrTm₁ tε .(PE.subst (_/_⊩_∷_ _ _ _) PE.refl tε) | PE.refl , PE.refl = PE.refl

irrTm₂ tε tε₁ with (irrTmHet tε tε₁)
irrTm₂ tε tε₁ | PE.refl , proj₄ = PE.refl

irrTmHet (⊩Π _ Fε Gε) (⊩Π _ Fε' Gε') with (irrTm₁ Fε Fε')
irrTmHet (⊩Π _ Fε Gε) (⊩Π _ Fε Gε') | PE.refl with (irrTm₁ Gε Gε')
irrTmHet (⊩Π _ Fε Gε) (⊩Π _ Fε Gε') | PE.refl | PE.refl = PE.refl , PE.refl
irrTmHet (⊩app _ [F] [G] tε uε) (⊩app _ [F]₁ [G]₁ tε' uε') = {!!}
irrTmHet (⊩lam _ Fε [G] tε) (⊩lam _ Fε₁ [G]₁ tε') = {!!}

convTy : ∀ {Γ A} → (Γε : ⊩ Γ) → (Aε : Γ / Γε ⊩ A) → (Γε' : ⊩ Γ) → Γ / Γε' ⊩ A
convTy Γε Aε Γε' with (irrCon Γε Γε')
convTy Γε Aε Γε | PE.refl = Aε

-- convTm : ∀ {Γ Γε Γε' t [A] [A]'} → Γ / Γε ⊩ t ∷ [A] → Γ / Γε' ⊩ t ∷ [A]'
-- convTm {Γ} {Γε} {Γε'} tε with (irrCon Γε Γε')
-- convTm {Γ} {Γε} {Γε'} tε | PE.refl = {!!}

record valTy (Γ : Con Term) (A : Term) : Set₂ where
  constructor mkValTy
  eta-equality
  field
    Γε : ⊩ Γ
    Aε : Γ / Γε ⊩ A

record valTm (Γ : Con Term) (A t : Term) : Set₂ where
  constructor mkValTm
  eta-equality
  field
    Γε : ⊩ Γ
    Aε : Γ / Γε ⊩ A
    tε : Γ / Γε ⊩ t ∷ [[ Γε ⊢ Aε ]]T

funCon : ∀ {Γ} → ⊢ Γ → ⊩ Γ
funTy : ∀ {Γ A} → Γ ⊢ A → valTy Γ A
funTm : ∀ {Γ A t} → Γ ⊢ t ∷ A → valTm Γ A t
--funVar : ∀ {Γ [Γ] A x} → x ∷ A ∈ Γ → (Γε : ⊩ Γ ▸ [Γ]) → valTm Γ A (var x)

funCon ε = ε
funCon (⊢Γ ∙ ⊢A) =
  let mkValTy Γε Aε = funTy ⊢A in
  Γε ∙ Aε

funTy (ℕⱼ x) = {!NOT DOING IT!}
funTy (Uⱼ ⊢Γ) =
  let Γε = funCon ⊢Γ in
  mkValTy Γε (⊩U Γε)
funTy (Πⱼ ⊢F ▹ ⊢G) =
  let mkValTy Γε Fε = funTy ⊢F in
  let mkValTy ΓFε Gε = funTy ⊢G in
  mkValTy Γε (⊩Π Γε Fε (convTy ΓFε Gε (Γε ∙ Fε)))
funTy (univ ⊢A) =
  let mkValTm Γε Uε Aε = funTm ⊢A in
  let e = irrTy Uε (⊩U Γε) in
  mkValTy Γε (⊩uni Γε (PE.subst (λ X → _ / Γε ⊩ _ ∷ [[ Γε ⊢ X ]]T) e Aε ))

funTm (conv ⊢t x) = {!!}
funTm (Πⱼ ⊢t ▹ ⊢t₁) = {!!}
funTm (var ⊢Γ A∈Γ) = {!!}
funTm (lamⱼ ⊢F ⊢t) =
  let mkValTy Γε Fε = funTy ⊢F in
  let mkValTm Γε' Πε tε = funTm ⊢t in
  {!!}
funTm (⊢t ∘ⱼ ⊢t₁) = {!!}

funTm (ℕⱼ x) = {!NOT DOING IT!}
funTm (zeroⱼ x) = {!NOT DOING IT!}
funTm (sucⱼ ⊢t) = {!NOT DOING IT!}
funTm (natrecⱼ x ⊢t ⊢t₁ ⊢t₂) = {!NOT DOING IT!}
