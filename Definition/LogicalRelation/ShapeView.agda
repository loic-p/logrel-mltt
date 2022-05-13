{-# OPTIONS --without-K #-}

module Definition.LogicalRelation.ShapeView where

open import Definition.Untyped
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Properties.Escape
open import Definition.LogicalRelation.Properties.Reflexivity

open import Tools.Product
open import Tools.Empty using (⊥; ⊥-elim)
import Tools.PropositionalEquality as PE

-- Type for maybe embeddings of reducible types
data MaybeEmb (l : TypeLevel) (⊩⟨_⟩ : TypeLevel → Set) : Set where
  noemb : ⊩⟨ l ⟩ → MaybeEmb l ⊩⟨_⟩
  emb   : ∀ {l′} → l′ < l → MaybeEmb l′ ⊩⟨_⟩ → MaybeEmb l ⊩⟨_⟩

-- Specific reducible types with possible embedding

_⊩⟨_⟩U : (Γ : Con Term) (l : TypeLevel) → Set
Γ ⊩⟨ l ⟩U = MaybeEmb l (λ l′ → Γ ⊩′⟨ l′ ⟩U)

_⊩⟨_⟩ℕ_ : (Γ : Con Term) (l : TypeLevel) (A : Term) → Set
Γ ⊩⟨ l ⟩ℕ A = MaybeEmb l (λ l′ → Γ ⊩ℕ A)

_⊩⟨_⟩ne_ : (Γ : Con Term) (l : TypeLevel) (A : Term) → Set
Γ ⊩⟨ l ⟩ne A = MaybeEmb l (λ l′ → Γ ⊩ne A)

_⊩⟨_⟩Π_ : (Γ : Con Term) (l : TypeLevel) (A : Term) → Set
Γ ⊩⟨ l ⟩Π A = MaybeEmb l (λ l′ → Γ ⊩′⟨ l′ ⟩Π A)

-- Construct a general reducible type from a specific

U-intr : ∀ {Γ l} → Γ ⊩⟨ l ⟩U → Γ ⊩⟨ l ⟩ U
U-intr (noemb x) = U x
U-intr (emb 0<1 x) = emb 0<1 (U-intr x)

ℕ-intr : ∀ {A Γ l} → Γ ⊩⟨ l ⟩ℕ A → Γ ⊩⟨ l ⟩ A
ℕ-intr (noemb x) = ℕ x
ℕ-intr (emb 0<1 x) = emb 0<1 (ℕ-intr x)

ne-intr : ∀ {A Γ l} → Γ ⊩⟨ l ⟩ne A → Γ ⊩⟨ l ⟩ A
ne-intr (noemb x) = ne x
ne-intr (emb 0<1 x) = emb 0<1 (ne-intr x)

Π-intr : ∀ {A Γ l} → Γ ⊩⟨ l ⟩Π A → Γ ⊩⟨ l ⟩ A
Π-intr (noemb x) = Π x
Π-intr (emb 0<1 x) = emb 0<1 (Π-intr x)

-- Construct a specific reducible type from a general with some criterion

U-elim : ∀ {Γ l} → Γ ⊩⟨ l ⟩ U → Γ ⊩⟨ l ⟩U
U-elim (U′ l′ l< ⊢Γ) = noemb (U l′ l< ⊢Γ)
U-elim (ℕ D) = ⊥-elim (U≢ℕ (dnfRed* (red D) U))
U-elim (ne′ K D neK) = ⊥-elim (U≢ne neK (dnfRed* (red D) U))
U-elim (Π′ F G D typeΠ ⊢F ⊢G [F] [G] G-ext) = ⊥-elim (U≢Π (dnfRed* (red D) U))
U-elim (emb 0<1 x) with U-elim x
U-elim (emb 0<1 x) | noemb x₁ = emb 0<1 (noemb x₁)
U-elim (emb 0<1 x) | emb () x₁

ℕ-elim′ : ∀ {A Γ l} → Γ ⊢ A ⇒* ℕ → Γ ⊩⟨ l ⟩ A → Γ ⊩⟨ l ⟩ℕ A
ℕ-elim′ D (U′ l′ l< ⊢Γ) = ⊥-elim (U≢ℕ (redDet* (id (U ⊢Γ) , U) (D , ℕ)))
ℕ-elim′ D (ℕ D′) = noemb D′
ℕ-elim′ D (ne′ K D′ neK) =
  ⊥-elim (ℕ≢ne neK (redDet* (D , ℕ) (red D′ , ne neK)))
ℕ-elim′ D (Π′ F G D′ typeΠ ⊢F ⊢G [F] [G] G-ext) =
  ⊥-elim (ℕ≢Π (redDet* (D , ℕ) (red D′ , typeDnf typeΠ)))
ℕ-elim′ D (emb 0<1 x) with ℕ-elim′ D x
ℕ-elim′ D (emb 0<1 x) | noemb x₁ = emb 0<1 (noemb x₁)
ℕ-elim′ D (emb 0<1 x) | emb () x₂

ℕ-elim : ∀ {Γ l} → Γ ⊩⟨ l ⟩ ℕ → Γ ⊩⟨ l ⟩ℕ ℕ
ℕ-elim [ℕ] = ℕ-elim′ (id (escape [ℕ])) [ℕ]

ne-elim′ : ∀ {A Γ l K} → Γ ⊢ A ⇒* K → Neutral K → Γ ⊩⟨ l ⟩ A → Γ ⊩⟨ l ⟩ne A
ne-elim′ D neK (U′ l′ l< ⊢Γ) =
  ⊥-elim (U≢ne neK (redDet* (id (U ⊢Γ) , U) (D , ne neK)))
ne-elim′ D neK (ℕ D′) = ⊥-elim (ℕ≢ne neK (redDet* (red D′ , ℕ) (D , ne neK)))
ne-elim′ D neK (ne′ K D′ neK′) = noemb (ne K D′ neK′)
ne-elim′ D neK (Π′ F G D′ typeΠ ⊢F ⊢G [F] [G] G-ext) =
  ⊥-elim (Π≢ne neK (redDet* (red D′ , typeDnf typeΠ) (D , ne neK)))
ne-elim′ D neK (emb 0<1 x) with ne-elim′ D neK x
ne-elim′ D neK (emb 0<1 x) | noemb x₁ = emb 0<1 (noemb x₁)
ne-elim′ D neK (emb 0<1 x) | emb () x₂

ne-elim : ∀ {Γ l K} → Neutral K  → Γ ⊩⟨ l ⟩ K → Γ ⊩⟨ l ⟩ne K
ne-elim neK [K] = ne-elim′ (id (escape [K])) neK [K]

Πred : ∀ {Γ F G A} → Γ ⊢ Π F ▹ G ⇒ A → Σ Term (λ F′ → Σ Term (λ G′ → A PE.≡ Π F′ ▹ G′))
ΠredTerm : ∀ {Γ F G A X} → Γ ⊢ Π F ▹ G ⇒ A ∷ X → Σ Term (λ F′ → Σ Term (λ G′ → A PE.≡ Π F′ ▹ G′))
Πred (univ x) = ΠredTerm x
Πred {G = G} (Π-subst {F′ = F′} x d x₁) = F′ , (G , PE.refl)
Πred {F = F} (Π-subst-2 {G′ = G′} x x₁ d) = F , (G′ , PE.refl)
ΠredTerm (conv d x) = ΠredTerm d
ΠredTerm {G = G} (Π-subst {F′ = F′} x d x₁) = F′ , (G , PE.refl)
ΠredTerm {F = F} (Π-subst-2 {G′ = G′} x x₁ d) = F , (G′ , PE.refl)

Πred*′ : ∀ {Γ F G A A′} → Γ ⊢ A ⇒* A′ → A PE.≡ Π F ▹ G → Σ Term (λ F′ → Σ Term (λ G′ → A′ PE.≡ Π F′ ▹ G′))
Πred*′ {F = F} {G = G} (id x) PE.refl = F , (G , PE.refl)
Πred*′ (x ⇨ d) PE.refl = let F′ , (G′ , e′) = Πred x in Πred*′ d e′

Πred* : ∀ {Γ F G A} → Γ ⊢ Π F ▹ G ⇒* A → Σ Term (λ F′ → Σ Term (λ G′ → A PE.≡ Π F′ ▹ G′))
Πred* d = Πred*′ d PE.refl

Ured : ∀ {Γ A} → Γ ⊢ U ⇒ A → A PE.≡ U
UredTerm : ∀ {Γ A X} → Γ ⊢ U ⇒ A ∷ X → A PE.≡ U
Ured (univ x) = UredTerm x
UredTerm (conv d x) = UredTerm d

Ured* : ∀ {Γ A} → Γ ⊢ U ⇒* A → U PE.≡ A
Ured* (id x) = PE.refl
Ured* (x ⇨ d) rewrite (Ured x) = Ured* d

¬Π⇒ℕ : ∀ {Γ F G} → Γ ⊢ Π F ▹ G ⇒* ℕ → ⊥
¬Π⇒ℕ d with Πred* d
¬Π⇒ℕ d | _ , (_ , ())

¬Π⇒ne : ∀ {Γ F G n} → Γ ⊢ Π F ▹ G ⇒* n → Neutral n → ⊥
¬Π⇒ne d nen with Πred* d
¬Π⇒ne d () | _ , _ , PE.refl

Π-elim′ : ∀ {A Γ F G l} → Γ ⊢ A ⇒* Π F ▹ G → Γ ⊩⟨ l ⟩ A → Γ ⊩⟨ l ⟩Π A
Π-elim′ D (U′ l′ l< ⊢Γ) = ⊥-elim (U≢Π (Ured* D))
Π-elim′ D (ℕ D′) = ⊥-elim (¬Π⇒ℕ (redDet↘ ((red D′) , ℕ) D))
Π-elim′ D (ne′ K D′ neK) = ⊥-elim (¬Π⇒ne (redDet↘ ((red D′) , ne neK) D) neK)
Π-elim′ D (Π′ F G D′ typeΠ ⊢F ⊢G [F] [G] G-ext) =
  noemb (Π F G D′ typeΠ ⊢F ⊢G [F] [G] G-ext)
Π-elim′ D (emb 0<1 x) with Π-elim′ D x
Π-elim′ D (emb 0<1 x) | noemb x₁ = emb 0<1 (noemb x₁)
Π-elim′ D (emb 0<1 x) | emb () x₂

Π-elim : ∀ {Γ F G l} → Γ ⊩⟨ l ⟩ Π F ▹ G → Γ ⊩⟨ l ⟩Π Π F ▹ G
Π-elim [Π] = Π-elim′ (id (escape [Π])) [Π]

-- Extract a type and a level from a maybe embedding
extractMaybeEmb : ∀ {l ⊩⟨_⟩} → MaybeEmb l ⊩⟨_⟩ → ∃ λ l′ → ⊩⟨ l′ ⟩
extractMaybeEmb (noemb x) = _ , x
extractMaybeEmb (emb 0<1 x) = extractMaybeEmb x

-- A view for constructor equality of types where embeddings are ignored
data ShapeView Γ : ∀ l l′ A B (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l′ ⟩ B) → Set where
  U : ∀ {l l′} UA UB → ShapeView Γ l l′ U U (U UA) (U UB)
  ℕ : ∀ {A B l l′} ℕA ℕB → ShapeView Γ l l′ A B (ℕ ℕA) (ℕ ℕB)
  ne  : ∀ {A B l l′} neA neB
      → ShapeView Γ l l′ A B (ne neA) (ne neB)
  Π : ∀ {A B l l′} ΠA ΠB
    → ShapeView Γ l l′ A B (Π ΠA) (Π ΠB)
  emb⁰¹ : ∀ {A B l p q}
        → ShapeView Γ ⁰ l A B p q
        → ShapeView Γ ¹ l A B (emb 0<1 p) q
  emb¹⁰ : ∀ {A B l p q}
        → ShapeView Γ l ⁰ A B p q
        → ShapeView Γ l ¹ A B p (emb 0<1 q)

-- Construct an shape view from an equality
goodCases : ∀ {l l′ Γ A B} ([A] : Γ ⊩⟨ l ⟩ A) ([B] : Γ ⊩⟨ l′ ⟩ B)
          → Γ ⊩⟨ l ⟩ A ≡ B / [A] → ShapeView Γ l l′ A B [A] [B]
goodCases (U UA) (U UB) A≡B = U UA UB
goodCases (U′ _ _ ⊢Γ) (ℕ D) PE.refl = ⊥-elim (U≢ℕ (dnfRed* (red D) U))
goodCases (U′ _ _ ⊢Γ) (ne′ K D neK) PE.refl = ⊥-elim (U≢ne neK (dnfRed* (red D) U))
goodCases (U′ _ _ ⊢Γ) (Π′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) PE.refl =
  ⊥-elim (U≢Π (dnfRed* (red D) U))
goodCases (ℕ D) (U ⊢Γ) A≡B = ⊥-elim (U≢ℕ (dnfRed* A≡B U))
goodCases (ℕ ℕA) (ℕ ℕB) A≡B = ℕ ℕA ℕB
goodCases (ℕ D) (ne′ K D₁ neK) A≡B =
  ⊥-elim (ℕ≢ne neK (redDet* (A≡B , ℕ) (red D₁ , ne neK)))
goodCases (ℕ D) (Π′ F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) A≡B =
  ⊥-elim (¬Π⇒ℕ (redDet↘ (A≡B , ℕ) (red D₁)))
goodCases (ne′ K D neK) (U ⊢Γ) (ne₌ M D′ neM K≡M) =
  ⊥-elim (U≢ne neM (dnfRed* (red D′) U))
goodCases (ne′ K D neK) (ℕ D₁) (ne₌ M D′ neM K≡M) =
  ⊥-elim (ℕ≢ne neM (redDet* (red D₁ , ℕ) (red D′ , ne neM)))
goodCases (ne neA) (ne neB) A≡B = ne neA neB
goodCases (ne′ K D neK) (Π′ F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) (ne₌ M D′ neM K≡M) =
  ⊥-elim (¬Π⇒ne (redDet↘ ((red D′) , ne neM) (red D₁)) neM)
goodCases (Π′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (U ⊢Γ)
          (Π₌ F′ G′ D′ TyΠ′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (U≢Π (dnfRed* (red D′) U))
goodCases (Π′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ℕ D₁)
          (Π₌ F′ G′ D′ TyΠ′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (¬Π⇒ℕ (redDet↘ ((red D₁) , ℕ) (red D′)))
goodCases (Π′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ne′ K D₁ neK)
          (Π₌ F′ G′ D′ TyΠ′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (¬Π⇒ne (redDet↘ ((red D₁) , ne neK) (red D′)) neK)
goodCases (Π ΠA) (Π ΠB) A≡B = Π ΠA ΠB
goodCases {l} [A] (emb 0<1 x) A≡B =
  emb¹⁰ (goodCases {l} {⁰} [A] x A≡B)
goodCases {l′ = l} (emb 0<1 x) [B] A≡B =
  emb⁰¹ (goodCases {⁰} {l} x [B] A≡B)

-- Construct an shape view between two derivations of the same type
goodCasesRefl : ∀ {l l′ Γ A} ([A] : Γ ⊩⟨ l ⟩ A) ([A′] : Γ ⊩⟨ l′ ⟩ A)
              → ShapeView Γ l l′ A A [A] [A′]
goodCasesRefl [A] [A′] = goodCases [A] [A′] (reflEq [A])


-- A view for constructor equality between three types
data ShapeView₃ Γ : ∀ l l′ l″ A B C
                 (p : Γ ⊩⟨ l   ⟩ A)
                 (q : Γ ⊩⟨ l′  ⟩ B)
                 (r : Γ ⊩⟨ l″ ⟩ C) → Set where
  U : ∀ {l l′ l″} UA UB UC → ShapeView₃ Γ l l′ l″ U U U (U UA) (U UB) (U UC)
  ℕ : ∀ {A B C l l′ l″} ℕA ℕB ℕC
    → ShapeView₃ Γ l l′ l″ A B C (ℕ ℕA) (ℕ ℕB) (ℕ ℕC)
  ne  : ∀ {A B C l l′ l″} neA neB neC
      → ShapeView₃ Γ l l′ l″ A B C (ne neA) (ne neB) (ne neC)
  Π : ∀ {A B C l l′ l″} ΠA ΠB ΠC
    → ShapeView₃ Γ l l′ l″ A B C (Π ΠA) (Π ΠB) (Π ΠC)
  emb⁰¹¹ : ∀ {A B C l l′ p q r}
         → ShapeView₃ Γ ⁰ l l′ A B C p q r
         → ShapeView₃ Γ ¹ l l′ A B C (emb 0<1 p) q r
  emb¹⁰¹ : ∀ {A B C l l′ p q r}
         → ShapeView₃ Γ l ⁰ l′ A B C p q r
         → ShapeView₃ Γ l ¹ l′ A B C p (emb 0<1 q) r
  emb¹¹⁰ : ∀ {A B C l l′ p q r}
         → ShapeView₃ Γ l l′ ⁰ A B C p q r
         → ShapeView₃ Γ l l′ ¹ A B C p q (emb 0<1 r)

-- Combines two two-way views into a three-way view
combine : ∀ {Γ l l′ l″ l‴ A B C [A] [B] [B]′ [C]}
        → ShapeView Γ l l′ A B [A] [B]
        → ShapeView Γ l″ l‴ B C [B]′ [C]
        → ShapeView₃ Γ l l′ l‴ A B C [A] [B] [C]
combine (U UA₁ UB₁) (U UA UB) = U UA₁ UB₁ UB
combine (U UA UB) (ℕ ℕA ℕB) = ⊥-elim (U≢ℕ (dnfRed* (red ℕA) U))
combine (U UA UB) (ne (ne K D neK) neB) =
  ⊥-elim (U≢ne neK (dnfRed* (red D) U))
combine (U UA UB) (Π (Π F G D ⊢F ⊢G A≡A [F] [G] G-ext) ΠB) =
  ⊥-elim (U≢Π (dnfRed* (red D) U))
combine (ℕ ℕA ℕB) (U UA UB) = ⊥-elim (U≢ℕ (dnfRed* (red ℕB) U))
combine (ℕ ℕA₁ ℕB₁) (ℕ ℕA ℕB) = ℕ ℕA₁ ℕB₁ ℕB
combine (ℕ ℕA ℕB) (ne (ne K D neK) neB) =
  ⊥-elim (ℕ≢ne neK (redDet* (red ℕB , ℕ) (red D , ne neK)))
combine (ℕ ℕA ℕB) (Π (Π F G D ⊢F ⊢G A≡A [F] [G] G-ext) ΠB) =
  ⊥-elim (¬Π⇒ℕ (redDet↘ (red ℕB , ℕ) (red D)))
combine (ne neA (ne K D neK)) (U UA UB) =
  ⊥-elim (U≢ne neK (dnfRed* (red D) U))
combine (ne neA (ne K D neK)) (ℕ ℕA ℕB) =
  ⊥-elim (ℕ≢ne neK (redDet* (red ℕA , ℕ) (red D , ne neK)))
combine (ne neA₁ neB₁) (ne neA neB) = ne neA₁ neB₁ neB
combine (ne neA (ne K D₁ neK)) (Π (Π F G D ⊢F ⊢G A≡A [F] [G] G-ext) ΠB) =
  ⊥-elim (¬Π⇒ne (redDet↘ ((red D₁) , ne neK) (red D)) neK)
combine (Π ΠA (Π F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (U UA UB) =
  ⊥-elim (U≢Π (dnfRed* (red D) U))
combine (Π ΠA (Π F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (ℕ ℕA ℕB) =
  ⊥-elim (¬Π⇒ℕ (redDet↘ (red ℕA , ℕ) (red D)))
combine (Π ΠA (Π F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext)) (ne (ne K D neK) neB) =
  ⊥-elim (¬Π⇒ne (redDet↘ ((red D) , ne neK) (red D₁)) neK)
combine (Π ΠA₁ ΠB₁) (Π ΠA ΠB) = Π ΠA₁ ΠB₁ ΠB
combine (emb⁰¹ [AB]) [BC] = emb⁰¹¹ (combine [AB] [BC])
combine (emb¹⁰ [AB]) [BC] = emb¹⁰¹ (combine [AB] [BC])
combine [AB] (emb⁰¹ [BC]) = combine [AB] [BC]
combine [AB] (emb¹⁰ [BC]) = emb¹¹⁰ (combine [AB] [BC])
