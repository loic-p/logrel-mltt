{-# OPTIONS --without-K #-}

module Definition.Typed.Properties where

open import Tools.Empty using (⊥; ⊥-elim)
open import Tools.Product

open import Definition.Untyped as U hiding (wk)
open import Definition.Untyped.Properties
open import Definition.Typed
open import Tools.Nat
import Tools.PropositionalEquality as PE


-- Escape context extraction

wfTerm : ∀ {Γ A t} → Γ ⊢ t ∷ A → ⊢ Γ
wfTerm (ℕ ⊢Γ) = ⊢Γ
wfTerm (Π F ▹ G) = wfTerm F
wfTerm (var ⊢Γ x₁) = ⊢Γ
wfTerm (lam F t) with wfTerm t
wfTerm (lam F t) | ⊢Γ ∙ F′ = ⊢Γ
wfTerm (g ∘ a) = wfTerm a
wfTerm (zero ⊢Γ) = ⊢Γ
wfTerm (suc n) = wfTerm n
wfTerm (natrec F z s n) = wfTerm z
wfTerm (conv t A≡B) = wfTerm t
wfTerm (cast A B t) = wfTerm t

wf : ∀ {Γ A} → Γ ⊢ A → ⊢ Γ
wf (ℕ ⊢Γ) = ⊢Γ
wf (U ⊢Γ) = ⊢Γ
wf (Π F ▹ G) = wf F
wf (univ A) = wfTerm A

wfEqTerm : ∀ {Γ A t u} → Γ ⊢ t ≡ u ∷ A → ⊢ Γ
wfEqTerm (refl t) = wfTerm t
wfEqTerm (sym t≡u) = wfEqTerm t≡u
wfEqTerm (trans t≡u u≡r) = wfEqTerm t≡u
wfEqTerm (conv t≡u A≡B) = wfEqTerm t≡u
wfEqTerm (Π-cong F F≡H G≡E) = wfEqTerm F≡H
wfEqTerm (app-cong f≡g a≡b) = wfEqTerm f≡g
wfEqTerm (β-red F t a) = wfTerm a
wfEqTerm (η-eq F f g f0≡g0) = wfTerm f
wfEqTerm (suc-cong n) = wfEqTerm n
wfEqTerm (natrec-cong F≡F′ z≡z′ s≡s′ n≡n′) = wfEqTerm z≡z′
wfEqTerm (natrec-zero F z s) = wfTerm z
wfEqTerm (natrec-suc n F z s) = wfTerm n
wfEqTerm (cast-cong A B t) = wfEqTerm t
wfEqTerm (cast-conv A≡B t) = wfTerm t

wfEq : ∀ {Γ A B} → Γ ⊢ A ≡ B → ⊢ Γ
wfEq (univ A≡B) = wfEqTerm A≡B
wfEq (refl A) = wf A
wfEq (sym A≡B) = wfEq A≡B
wfEq (trans A≡B B≡C) = wfEq A≡B
wfEq (Π-cong F F≡H G≡E) = wfEq F≡H

-- Those should be provable by mutual induction
postulate
  ==-correctNe : ∀ {Γ A B n m} → Γ ⊢ n ∷ A → Neutral n → Γ ⊢ m ∷ B → Neutral m → n == m → (Γ ⊢ A ≡ B) × (Γ ⊢ n ≡ m ∷ A)
  ==-correctTerm : ∀ {Γ A t u} → Γ ⊢ t ∷ A → Dnf t → Γ ⊢ u ∷ A → Dnf u → t == u → Γ ⊢ t ≡ u ∷ A
  ==-correct : ∀ {Γ A B} → Γ ⊢ A → Dnf A → Γ ⊢ B → Dnf B → A == B → Γ ⊢ A ≡ B

-- Reduction is a subset of conversion

subsetTerm : ∀ {Γ A t u} → Γ ⊢ t ⇒ u ∷ A → Γ ⊢ t ≡ u ∷ A
subsetTerm (conv t⇒u A≡B) = conv (subsetTerm t⇒u) A≡B
subsetTerm (app-subst t a⇒b) = app-cong (refl t) (subsetTerm a⇒b)
subsetTerm (app-subst-2 t⇒u a _) = app-cong (subsetTerm t⇒u) (refl a)
subsetTerm (β-red A t _ a _) = β-red A t a
subsetTerm (natrec-subst F⇒F′ z s n) = natrec-cong (univ (subsetTerm F⇒F′)) (refl z) (refl s) (refl n)
subsetTerm (natrec-subst-2 F _ z⇒z′ s n) = natrec-cong (refl F) (subsetTerm z⇒z′) (refl s) (refl n)
subsetTerm (natrec-subst-3 F _ z _ s⇒s′ n) = natrec-cong (refl F) (refl z) (subsetTerm s⇒s′) (refl n)
subsetTerm (natrec-subst-4 F _ z _ s _ n⇒n′) = natrec-cong (refl F) (refl z) (refl s) (subsetTerm n⇒n′)
subsetTerm (natrec-zero F _ z _ s _) = natrec-zero F z s
subsetTerm (natrec-suc n _ F _ z _ s _) = natrec-suc n F z s
subsetTerm (cast-subst A B t⇒t′) = cast-cong (refl A) (refl B) (subsetTerm t⇒t′)
subsetTerm (cast-subst-2 A⇒A′ B t _) = cast-cong (univ (subsetTerm A⇒A′)) (refl B) (refl t)
subsetTerm (cast-subst-3 A _ B⇒B′ t _) = cast-cong (refl A) (univ (subsetTerm B⇒B′)) (refl t)
subsetTerm (cast-conv A nfA B nfB e t _) = cast-conv (==-correct A nfA B nfB e) t

subset : ∀ {Γ A B} → Γ ⊢ A ⇒ B → Γ ⊢ A ≡ B
subset (univ A⇒B) = univ (subsetTerm A⇒B)

subset*Term : ∀ {Γ A t u} → Γ ⊢ t ⇒* u ∷ A → Γ ⊢ t ≡ u ∷ A
subset*Term (id t) = refl t
subset*Term (t⇒t′ ⇨ t⇒*u) = trans (subsetTerm t⇒t′) (subset*Term t⇒*u)

subset* : ∀ {Γ A B} → Γ ⊢ A ⇒* B → Γ ⊢ A ≡ B
subset* (id A) = refl A
subset* (A⇒A′ ⇨ A′⇒*B) = trans (subset A⇒A′) (subset* A′⇒*B)


-- Can extract left-part of a reduction

redFirstTerm : ∀ {Γ t u A} → Γ ⊢ t ⇒ u ∷ A → Γ ⊢ t ∷ A
redFirstTerm (conv t⇒u A≡B) = conv (redFirstTerm t⇒u) A≡B
redFirstTerm (app-subst t a⇒b) = t ∘ (redFirstTerm a⇒b)
redFirstTerm (app-subst-2 t⇒u a _) = (redFirstTerm t⇒u) ∘ a
redFirstTerm (β-red A t _ a _) = (lam A t) ∘ a
redFirstTerm (natrec-subst F⇒F′ z s n) = natrec (univ (redFirstTerm F⇒F′)) z s n
redFirstTerm (natrec-subst-2 F _ z⇒z′ s n) = natrec F (redFirstTerm z⇒z′) s n
redFirstTerm (natrec-subst-3 F _ z _ s⇒s′ n) = natrec F z (redFirstTerm s⇒s′) n
redFirstTerm (natrec-subst-4 F _ z _ s _ n⇒n′) = natrec F z s (redFirstTerm n⇒n′)
redFirstTerm (natrec-zero F _ z _ s _) = natrec F z s (zero (wfTerm z))
redFirstTerm (natrec-suc n _ F _ z _ s _) = natrec F z s (suc n)
redFirstTerm (cast-subst A B t⇒t′) = cast A B (redFirstTerm t⇒t′)
redFirstTerm (cast-subst-2 A⇒A′ B t _) = cast (univ (redFirstTerm A⇒A′)) B t
redFirstTerm (cast-subst-3 A _ B⇒B′ t _ ) = cast A (univ (redFirstTerm B⇒B′)) t
redFirstTerm (cast-conv A _ B _ _ t _) = cast A B t

redFirst : ∀ {Γ A B} → Γ ⊢ A ⇒ B → Γ ⊢ A
redFirst (univ A⇒B) = univ (redFirstTerm A⇒B)

redFirst*Term : ∀ {Γ t u A} → Γ ⊢ t ⇒* u ∷ A → Γ ⊢ t ∷ A
redFirst*Term (id t) = t
redFirst*Term (t⇒t′ ⇨ t′⇒*u) = redFirstTerm t⇒t′

redFirst* : ∀ {Γ A B} → Γ ⊢ A ⇒* B → Γ ⊢ A
redFirst* (id A) = A
redFirst* (A⇒A′ ⇨ A′⇒*B) = redFirst A⇒A′


-- No neutral terms are well-formed in an empty context
-- not true with casts

-- noNe : ∀ {t A} → ε ⊢ t ∷ A → Neutral t → ⊥
-- noNe (var x₁ ()) (var x)
-- noNe (conv ⊢t x) (var n) = noNe ⊢t (var n)
-- noNe (⊢t ∘ ⊢t₁) (_∘_ neT ) = noNe ⊢t neT
-- noNe (conv ⊢t x) (_∘_ neT) = noNe ⊢t (_∘_ neT)
-- noNe (natrec x ⊢t ⊢t₁ ⊢t₂) (natrec neT) = noNe ⊢t₂ neT
-- noNe (conv ⊢t x) (natrec neT) = noNe ⊢t (natrec neT)

-- Dnfs do not reduce
dnfRedTerm : ∀ {Γ t u A} (d : Γ ⊢ t ⇒ u ∷ A) (w : Dnf t) → ⊥

dnfRedTerm (conv d x) n = dnfRedTerm d n
dnfRedTerm (app-subst x d) (ne (n ∘ a)) = dnfRedTerm d a
dnfRedTerm (app-subst-2 d x x₁) (ne (n ∘ a)) = dnfRedTerm d (ne n)
dnfRedTerm (β-red x x₁ x₂ x₃ x₄) (ne (() ∘ x₅))
dnfRedTerm (natrec-subst d x x₁ x₂) (ne (natrec n F x₄ x₅)) = dnfRedTerm d F
dnfRedTerm (natrec-subst-2 x x₁ d x₂ x₃) (ne (natrec n x₄ z x₆)) = dnfRedTerm d z
dnfRedTerm (natrec-subst-3 x x₁ x₂ x₃ d x₄) (ne (natrec n x₅ x₆ s)) = dnfRedTerm d s
dnfRedTerm (natrec-subst-4 x x₁ x₂ x₃ x₄ x₅ d) (ne (natrec n x₆ x₇ x₈)) = dnfRedTerm d (ne n)
dnfRedTerm (natrec-zero x x₁ x₂ x₃ x₄ x₅) (ne (natrec () x₆ x₇ x₈))
dnfRedTerm (natrec-suc x x₁ x₂ x₃ x₄ x₅ x₆ x₇) (ne (natrec () x₈ x₉ x₁₀))
dnfRedTerm (cast-subst x x₁ d) (ne (cast x₂ x₃ x₄ t)) = dnfRedTerm d t
dnfRedTerm (cast-subst-2 d x x₁ x₂) (ne (cast A x₄ x₅ x₆)) = dnfRedTerm d A
dnfRedTerm (cast-subst-3 x x₁ d x₂ x₃) (ne (cast x₄ B x₆ x₇)) = dnfRedTerm d B
dnfRedTerm (cast-conv x x₁ x₂ x₃ e x₅ x₆) (ne (cast x₇ x₈ d x₁₀)) = d e

dnfRed : ∀ {Γ A B} (d : Γ ⊢ A ⇒ B) (w : Dnf A) → ⊥
dnfRed (univ x) w = dnfRedTerm x w

-- Neutrals do not reduce

neRedTerm : ∀ {Γ t u A} (d : Γ ⊢ t ⇒ u ∷ A) (n : Neutral t) → ⊥
neRedTerm d n = dnfRedTerm d (ne n)

neRed : ∀ {Γ A B} (d : Γ ⊢ A ⇒ B) (N : Neutral A) → ⊥
neRed (univ x) N = neRedTerm x N

dnfRed*Term : ∀ {Γ t u A} (d : Γ ⊢ t ⇒* u ∷ A) (w : Dnf t) → t PE.≡ u
dnfRed*Term (id x) y = PE.refl
dnfRed*Term (x ⇨ d) w = ⊥-elim (dnfRedTerm x w)

dnfRed* : ∀ {Γ A B} (d : Γ ⊢ A ⇒* B) (w : Dnf A) → A PE.≡ B
dnfRed* (id x) w = PE.refl
dnfRed* (x ⇨ d) w = ⊥-elim (dnfRed x w)

-- reduction is deterministic

redDetTerm : ∀{Γ t u A u′ A′} (d : Γ ⊢ t ⇒ u ∷ A) (d′ : Γ ⊢ t ⇒ u′ ∷ A′) → u PE.≡ u′
redDetTerm (conv d x) d′ = redDetTerm d d′
redDetTerm d (conv d′ x) = redDetTerm d d′
redDetTerm (app-subst x d) (app-subst x₁ d′) rewrite redDetTerm d d′ = PE.refl
redDetTerm (app-subst x d) (app-subst-2 d′ x₁ x₂) = ⊥-elim (dnfRedTerm d x₂)
redDetTerm (app-subst x d) (β-red x₁ x₂ x₃ x₄ x₅) = ⊥-elim (dnfRedTerm d x₅)
redDetTerm (app-subst-2 d x x₁) (app-subst x₂ d′) = ⊥-elim (dnfRedTerm d′ x₁)
redDetTerm (app-subst-2 d x x₁) (app-subst-2 d′ x₂ x₃) rewrite redDetTerm d d′ = PE.refl
redDetTerm (app-subst-2 d x x₁) (β-red x₂ x₃ x₄ x₅ x₆) = ⊥-elim (dnfRedTerm d (lam x₄))
redDetTerm (β-red x x₁ x₂ x₃ x₄) (app-subst x₅ d′) = ⊥-elim (dnfRedTerm d′ x₄)
redDetTerm (β-red x x₁ x₂ x₃ x₄) (app-subst-2 d′ x₅ x₆) = ⊥-elim (dnfRedTerm d′ (lam x₂))
redDetTerm (β-red x x₁ x₂ x₃ x₄) (β-red x₅ x₆ x₇ x₈ x₉) = PE.refl
redDetTerm (natrec-subst d x x₁ x₂) (natrec-subst d′ x₃ x₄ x₅) rewrite redDetTerm d d′ = PE.refl
redDetTerm (natrec-subst d x x₁ x₂) (natrec-subst-2 x₃ x₄ d′ x₅ x₆) = ⊥-elim (dnfRedTerm d x₄)
redDetTerm (natrec-subst d x x₁ x₂) (natrec-subst-3 x₃ x₄ x₅ x₆ d′ x₇) = ⊥-elim (dnfRedTerm d x₄)
redDetTerm (natrec-subst d x x₁ x₂) (natrec-subst-4 x₃ x₄ x₅ x₆ x₇ x₈ d′) = ⊥-elim (dnfRedTerm d x₄)
redDetTerm (natrec-subst d x x₁ x₂) (natrec-zero x₃ x₄ x₅ x₆ x₇ x₈) = ⊥-elim (dnfRedTerm d x₄)
redDetTerm (natrec-subst d x x₁ x₂) (natrec-suc x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀) = ⊥-elim (dnfRedTerm d x₆)
redDetTerm (natrec-subst-2 x x₁ d x₂ x₃) (natrec-subst d′ x₄ x₅ x₆) = ⊥-elim (dnfRedTerm d′ x₁)
redDetTerm (natrec-subst-2 x x₁ d x₂ x₃) (natrec-subst-2 x₄ x₅ d′ x₆ x₇) rewrite redDetTerm d d′ = PE.refl
redDetTerm (natrec-subst-2 x x₁ d x₂ x₃) (natrec-subst-3 x₄ x₅ x₆ x₇ d′ x₈) = ⊥-elim (dnfRedTerm d x₇)
redDetTerm (natrec-subst-2 x x₁ d x₂ x₃) (natrec-subst-4 x₄ x₅ x₆ x₇ x₈ x₉ d′) = ⊥-elim (dnfRedTerm d x₇)
redDetTerm (natrec-subst-2 x x₁ d x₂ x₃) (natrec-zero x₄ x₅ x₆ x₇ x₈ x₉) = ⊥-elim (dnfRedTerm d x₇)
redDetTerm (natrec-subst-2 x x₁ d x₂ x₃) (natrec-suc x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁) = ⊥-elim (dnfRedTerm d x₉)
redDetTerm (natrec-subst-3 x x₁ x₂ x₃ d x₄) (natrec-subst d′ x₅ x₆ x₇) = ⊥-elim (dnfRedTerm d′ x₁)
redDetTerm (natrec-subst-3 x x₁ x₂ x₃ d x₄) (natrec-subst-2 x₅ x₆ d′ x₇ x₈) = ⊥-elim (dnfRedTerm d′ x₃)
redDetTerm (natrec-subst-3 x x₁ x₂ x₃ d x₄) (natrec-subst-3 x₅ x₆ x₇ x₈ d′ x₉) rewrite redDetTerm d d′ = PE.refl
redDetTerm (natrec-subst-3 x x₁ x₂ x₃ d x₄) (natrec-subst-4 x₅ x₆ x₇ x₈ x₉ x₁₀ d′) = ⊥-elim (dnfRedTerm d x₁₀)
redDetTerm (natrec-subst-3 x x₁ x₂ x₃ d x₄) (natrec-zero x₅ x₆ x₇ x₈ x₉ x₁₀) = ⊥-elim (dnfRedTerm d x₁₀)
redDetTerm (natrec-subst-3 x x₁ x₂ x₃ d x₄) (natrec-suc x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂) = ⊥-elim (dnfRedTerm d x₁₂)
redDetTerm (natrec-subst-4 x x₁ x₂ x₃ x₄ x₅ d) (natrec-subst d′ x₆ x₇ x₈) = ⊥-elim (dnfRedTerm d′ x₁)
redDetTerm (natrec-subst-4 x x₁ x₂ x₃ x₄ x₅ d) (natrec-subst-2 x₆ x₇ d′ x₈ x₉) = ⊥-elim (dnfRedTerm d′ x₃)
redDetTerm (natrec-subst-4 x x₁ x₂ x₃ x₄ x₅ d) (natrec-subst-3 x₆ x₇ x₈ x₉ d′ x₁₀) = ⊥-elim (dnfRedTerm d′ x₅)
redDetTerm (natrec-subst-4 x x₁ x₂ x₃ x₄ x₅ d) (natrec-subst-4 x₆ x₇ x₈ x₉ x₁₀ x₁₁ d′) rewrite redDetTerm d d′ = PE.refl
redDetTerm (natrec-subst-4 x x₁ x₂ x₃ x₄ x₅ d) (natrec-zero x₆ x₇ x₈ x₉ x₁₀ x₁₁) = ⊥-elim (dnfRedTerm d zero)
redDetTerm (natrec-subst-4 x x₁ x₂ x₃ x₄ x₅ d) (natrec-suc x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃) = ⊥-elim (dnfRedTerm d (suc x₇))
redDetTerm (natrec-zero x x₁ x₂ x₃ x₄ x₅) (natrec-subst d′ x₆ x₇ x₈) = ⊥-elim (dnfRedTerm d′ x₁)
redDetTerm (natrec-zero x x₁ x₂ x₃ x₄ x₅) (natrec-subst-2 x₆ x₇ d′ x₈ x₉) = ⊥-elim (dnfRedTerm d′ x₃)
redDetTerm (natrec-zero x x₁ x₂ x₃ x₄ x₅) (natrec-subst-3 x₆ x₇ x₈ x₉ d′ x₁₀) = ⊥-elim (dnfRedTerm d′ x₅)
redDetTerm (natrec-zero x x₁ x₂ x₃ x₄ x₅) (natrec-subst-4 x₆ x₇ x₈ x₉ x₁₀ x₁₁ d′) = ⊥-elim (dnfRedTerm d′ zero)
redDetTerm (natrec-zero x x₁ x₂ x₃ x₄ x₅) (natrec-zero x₆ x₇ x₈ x₉ x₁₀ x₁₁) = PE.refl
redDetTerm (natrec-suc x x₁ x₂ x₃ x₄ x₅ x₆ x₇) (natrec-subst d′ x₈ x₉ x₁₀) = ⊥-elim (dnfRedTerm d′ x₃)
redDetTerm (natrec-suc x x₁ x₂ x₃ x₄ x₅ x₆ x₇) (natrec-subst-2 x₈ x₉ d′ x₁₀ x₁₁) = ⊥-elim (dnfRedTerm d′ x₅)
redDetTerm (natrec-suc x x₁ x₂ x₃ x₄ x₅ x₆ x₇) (natrec-subst-3 x₈ x₉ x₁₀ x₁₁ d′ x₁₂) = ⊥-elim (dnfRedTerm d′ x₇)
redDetTerm (natrec-suc x x₁ x₂ x₃ x₄ x₅ x₆ x₇) (natrec-subst-4 x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃ d′) = ⊥-elim (dnfRedTerm d′ (suc x₁))
redDetTerm (natrec-suc x x₁ x₂ x₃ x₄ x₅ x₆ x₇) (natrec-suc x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃ x₁₄ x₁₅) = PE.refl
redDetTerm (cast-subst x x₁ d) (cast-subst x₂ x₃ d′) rewrite redDetTerm d d′ = PE.refl
redDetTerm (cast-subst x x₁ d) (cast-subst-2 d′ x₂ x₃ x₄) = ⊥-elim (dnfRedTerm d x₄)
redDetTerm (cast-subst x x₁ d) (cast-subst-3 x₂ x₃ d′ x₄ x₅) = ⊥-elim (dnfRedTerm d x₅)
redDetTerm (cast-subst x x₁ d) (cast-conv x₂ x₃ x₄ x₅ x₆ x₇ x₈) = ⊥-elim (dnfRedTerm d x₈)
redDetTerm (cast-subst-2 d x x₁ x₂) (cast-subst x₃ x₄ d′) = ⊥-elim (dnfRedTerm d′ x₂)
redDetTerm (cast-subst-2 d x x₁ x₂) (cast-subst-2 d′ x₃ x₄ x₅) rewrite redDetTerm d d′ = PE.refl
redDetTerm (cast-subst-2 d x x₁ x₂) (cast-subst-3 x₃ x₄ d′ x₅ x₆) = ⊥-elim (dnfRedTerm d x₄)
redDetTerm (cast-subst-2 d x x₁ x₂) (cast-conv x₃ x₄ x₅ x₆ x₇ x₈ x₉) = ⊥-elim (dnfRedTerm d x₄)
redDetTerm (cast-subst-3 x x₁ d x₂ x₃) (cast-subst x₄ x₅ d′) = ⊥-elim (dnfRedTerm d′ x₃)
redDetTerm (cast-subst-3 x x₁ d x₂ x₃) (cast-subst-2 d′ x₄ x₅ x₆) = ⊥-elim (dnfRedTerm d′ x₁)
redDetTerm (cast-subst-3 x x₁ d x₂ x₃) (cast-subst-3 x₄ x₅ d′ x₆ x₇) rewrite redDetTerm d d′ = PE.refl
redDetTerm (cast-subst-3 x x₁ d x₂ x₃) (cast-conv x₄ x₅ x₆ x₇ x₈ x₉ x₁₀) = ⊥-elim (dnfRedTerm d x₇)
redDetTerm (cast-conv x x₁ x₂ x₃ x₄ x₅ x₆) (cast-subst x₇ x₈ d′) = ⊥-elim (dnfRedTerm d′ x₆)
redDetTerm (cast-conv x x₁ x₂ x₃ x₄ x₅ x₆) (cast-subst-2 d′ x₇ x₈ x₉) = ⊥-elim (dnfRedTerm d′ x₁)
redDetTerm (cast-conv x x₁ x₂ x₃ x₄ x₅ x₆) (cast-subst-3 x₇ x₈ d′ x₉ x₁₀) = ⊥-elim (dnfRedTerm d′ x₃)
redDetTerm (cast-conv x x₁ x₂ x₃ x₄ x₅ x₆) (cast-conv x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃) = PE.refl

redDet : ∀{Γ A B B′} (d : Γ ⊢ A ⇒ B) (d′ : Γ ⊢ A ⇒ B′) → B PE.≡ B′
redDet (univ x) (univ x₁) = redDetTerm x x₁

redDet↘Term : ∀{Γ t u A u′} (d : Γ ⊢ t ↘ u ∷ A) (d′ : Γ ⊢ t ⇒* u′ ∷ A) → Γ ⊢ u′ ⇒* u ∷ A
redDet↘Term (proj₁ , proj₂) (id x) = proj₁
redDet↘Term (id x , proj₂) (x₁ ⇨ d′) = ⊥-elim (dnfRedTerm x₁ proj₂)
redDet↘Term (x ⇨ proj₁ , proj₂) (x₁ ⇨ d′) =
  redDet↘Term (PE.subst (λ x₂ → _ ⊢ x₂ ↘ _ ∷ _) (redDetTerm x x₁) (proj₁ , proj₂)) d′

redDet*Term : ∀{Γ t u A u′} (d : Γ ⊢ t ↘ u ∷ A) (d′ : Γ ⊢ t ↘ u′ ∷ A) → u PE.≡ u′
redDet*Term (id x , proj₂) (id x₁ , proj₄) = PE.refl
redDet*Term (id x , proj₂) (x₁ ⇨ proj₃ , proj₄) = ⊥-elim (dnfRedTerm x₁ proj₂)
redDet*Term (x ⇨ proj₁ , proj₂) (id x₁ , proj₄) = ⊥-elim (dnfRedTerm x proj₄)
redDet*Term (x ⇨ proj₁ , proj₂) (x₁ ⇨ proj₃ , proj₄) =
  redDet*Term (proj₁ , proj₂) (PE.subst (λ x₂ → _ ⊢ x₂ ↘ _ ∷ _)
                                    (redDetTerm x₁ x) (proj₃ , proj₄))

redDet* : ∀{Γ A B B′} (d : Γ ⊢ A ↘ B) (d′ : Γ ⊢ A ↘ B′) → B PE.≡ B′
redDet* (id x , proj₂) (id x₁ , proj₄) = PE.refl
redDet* (id x , proj₂) (x₁ ⇨ proj₃ , proj₄) = ⊥-elim (dnfRed x₁ proj₂)
redDet* (x ⇨ proj₁ , proj₂) (id x₁ , proj₄) = ⊥-elim (dnfRed x proj₄)
redDet* (A⇒A′ ⇨ A′⇒*B , whnfB) (A⇒A″ ⇨ A″⇒*B′ , whnfB′) =
  redDet* (A′⇒*B , whnfB) (PE.subst (λ x → _ ⊢ x ↘ _)
                                     (redDet A⇒A″ A⇒A′)
                                     (A″⇒*B′ , whnfB′))

-- Identity of syntactic reduction

idRed:*: : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ A :⇒*: A
idRed:*: A = [ A , A , id A ]

idRedTerm:*: : ∀ {Γ A t} → Γ ⊢ t ∷ A → Γ ⊢ t :⇒*: t ∷ A
idRedTerm:*: t = [ t , t , id t ]

-- U cannot be a term

UnotInA : ∀ {A Γ} → Γ ⊢ U ∷ A → ⊥
UnotInA (conv U∷U x) = UnotInA U∷U

UnotInA[t] : ∀ {A B t a Γ}
         → t [ a ] PE.≡ U
         → Γ ⊢ a ∷ A
         → Γ ∙ A ⊢ t ∷ B
         → ⊥
UnotInA[t] x₁ x₂ (var x₃ here) rewrite x₁ = UnotInA x₂
UnotInA[t] x x₁ (conv x₂ x₃) = UnotInA[t] x x₁ x₂

redU*Term′ : ∀ {A B U′ Γ} → U′ PE.≡ U → Γ ⊢ A ⇒ U′ ∷ B → ⊥
redU*Term′ U′≡U (conv A⇒U x) = redU*Term′ U′≡U A⇒U
redU*Term′ U′≡U (β-red x x₁ _ x₂ _) = UnotInA[t] U′≡U x₂ x₁
redU*Term′ U′≡U (natrec-zero x _ x₁ _ x₂ _) rewrite U′≡U = UnotInA x₁
redU*Term′ U′≡U (cast-conv x x₁ x₂ x₃ x₄ x₅ x₆) rewrite U′≡U = UnotInA x₅

redU*Term : ∀ {A B Γ} → Γ ⊢ A ⇒* U ∷ B → ⊥
redU*Term (id x) = UnotInA x
redU*Term (x ⇨ A⇒*U) = redU*Term A⇒*U

-- Nothing reduces to U

redU : ∀ {A Γ} → Γ ⊢ A ⇒ U → ⊥
redU (univ x) = redU*Term′ PE.refl x

redU* : ∀ {A Γ} → Γ ⊢ A ⇒* U → A PE.≡ U
redU* (id x) = PE.refl
redU* (x ⇨ A⇒*U) rewrite redU* A⇒*U = ⊥-elim (redU x)
