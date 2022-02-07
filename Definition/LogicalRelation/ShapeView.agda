{-# OPTIONS --without-K --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.ShapeView {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Agda.Primitive

open import Definition.Untyped
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

-- _⊩⟨_⟩U : (Γ : Con Term) (l : TypeLevel) → Set
-- Γ ⊩⟨ l ⟩U = MaybeEmb l (λ l′ → Γ ⊩′⟨ l′ ⟩U)

_⊩⟨_⟩ℕ_ : (Γ : Con Term) (l : TypeLevel) (A : Term) → Set
Γ ⊩⟨ l ⟩ℕ A = MaybeEmb l (λ l′ → Γ ⊩ℕ A)

_⊩⟨_⟩ne_ : (Γ : Con Term) (l : TypeLevel) (A : Term) → Set
Γ ⊩⟨ l ⟩ne A = MaybeEmb l (λ l′ → Γ ⊩ne A)

-- _⊩⟨_⟩Π_ : (Γ : Con Term) (l : TypeLevel) (A : Term) → Set
-- Γ ⊩⟨ l ⟩Π A = MaybeEmb l (λ l′ → Γ ⊩′⟨ l′ ⟩Π A)

-- -- Construct a general reducible type from a specific

-- U-intr : ∀ {Γ l} → Γ ⊩⟨ l ⟩U → Γ ⊩⟨ l ⟩ U
-- U-intr (noemb x) = Uᵣ x
-- U-intr (emb 0<1 x) = emb 0<1 (U-intr x)

ℕ-intr : ∀ {A Γ l} → Γ ⊩⟨ l ⟩ℕ A → Γ ⊩⟨ l ⟩ A
ℕ-intr (noemb x) = ℕᵣ x
ℕ-intr (emb 0<1 x) = emb′ 0<1 (ℕ-intr x)

ne-intr : ∀ {A Γ l} → Γ ⊩⟨ l ⟩ne A → Γ ⊩⟨ l ⟩ A
ne-intr (noemb x) = LRPack _ _ _ (LRne x)
ne-intr (emb 0<1 x) = emb′ 0<1 (ne-intr x)

-- Π-intr : ∀ {A Γ l} → Γ ⊩⟨ l ⟩Π A → Γ ⊩⟨ l ⟩ A
-- Π-intr (noemb x) = Πᵣ x
-- Π-intr (emb 0<1 x) = emb 0<1 (Π-intr x)

-- -- Construct a specific reducible type from a general with some criterion

-- U-elim : ∀ {Γ l} → Γ ⊩⟨ l ⟩ U → Γ ⊩⟨ l ⟩U
-- U-elim (Uᵣ′ l′ l< ⊢Γ) = noemb (Uᵣ l′ l< ⊢Γ)
-- U-elim (ℕᵣ D) = ⊥-elim (U≢ℕ (whnfRed* (red D) Uₙ))
-- U-elim (Emptyᵣ D) = ⊥-elim (U≢Empty (whnfRed* (red D) Uₙ))
-- U-elim (ne′ K D neK K≡K) = ⊥-elim (U≢ne neK (whnfRed* (red D) Uₙ))
-- U-elim (Πᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) = ⊥-elim (U≢Π (whnfRed* (red D) Uₙ))
-- U-elim (emb 0<1 x) with U-elim x
-- U-elim (emb 0<1 x) | noemb x₁ = emb 0<1 (noemb x₁)
-- U-elim (emb 0<1 x) | emb () x₁

ℕ-elim′ : ∀ {A Γ l} → Γ ⊢ A ⇒* ℕ → Γ ⊩⟨ l ⟩ A → Γ ⊩⟨ l ⟩ℕ A
ℕ-elim′ D (Uᵣ′ l′ l< ⊢Γ) = ⊥-elim (U≢ℕ (whrDet* (id (Uⱼ ⊢Γ) , Uₙ) (D , ℕₙ)))
ℕ-elim′ D (ℕᵣ D′) = noemb D′
ℕ-elim′ D (ne′ K D′ neK K≡K) =
  ⊥-elim (ℕ≢ne neK (whrDet* (D , ℕₙ) (red D′ , ne neK)))
ℕ-elim′ D (Πᵣ′ F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) =
  ⊥-elim (ℕ≢Π (whrDet* (D , ℕₙ) (red D′ , Πₙ)))
ℕ-elim′ D (emb′ 0<1 x) with ℕ-elim′ D x
ℕ-elim′ D (emb′ 0<1 x) | noemb x₁ = emb 0<1 (noemb x₁)
ℕ-elim′ D (emb′ 0<1 x) | emb () x₂

ℕ-elim : ∀ {Γ l} → Γ ⊩⟨ l ⟩ ℕ → Γ ⊩⟨ l ⟩ℕ ℕ
ℕ-elim [ℕ] = ℕ-elim′ (id (escape [ℕ])) [ℕ]

ne-elim′ : ∀ {A Γ l K} → Γ ⊢ A ⇒* K → Neutral K → Γ ⊩⟨ l ⟩ A → Γ ⊩⟨ l ⟩ne A
ne-elim′ D neK (Uᵣ′ l′ l< ⊢Γ) =
  ⊥-elim (U≢ne neK (whrDet* (id (Uⱼ ⊢Γ) , Uₙ) (D , ne neK)))
ne-elim′ D neK (ℕᵣ D′) = ⊥-elim (ℕ≢ne neK (whrDet* (red D′ , ℕₙ) (D , ne neK)))
ne-elim′ D neK (ne′ K D′ neK′ K≡K) = noemb (ne K D′ neK′ K≡K)
ne-elim′ D neK (Πᵣ′ F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) =
  ⊥-elim (Π≢ne neK (whrDet* (red D′ , Πₙ) (D , ne neK)))
ne-elim′ D neK (emb′ 0<1 x) with ne-elim′ D neK x
ne-elim′ D neK (emb′ 0<1 x) | noemb x₁ = emb 0<1 (noemb x₁)
ne-elim′ D neK (emb′ 0<1 x) | emb () x₂

ne-elim : ∀ {Γ l K} → Neutral K  → Γ ⊩⟨ l ⟩ K → Γ ⊩⟨ l ⟩ne K
ne-elim neK [K] = ne-elim′ (id (escape [K])) neK [K]

-- Π-elim′ : ∀ {A Γ F G l} → Γ ⊢ A ⇒* Π F ▹ G → Γ ⊩⟨ l ⟩ A → Γ ⊩⟨ l ⟩Π A
-- Π-elim′ D (Uᵣ′ l′ l< ⊢Γ) = ⊥-elim (U≢Π (whrDet* (id (Uⱼ ⊢Γ) , Uₙ) (D , Πₙ)))
-- Π-elim′ D (ℕᵣ D′) = ⊥-elim (ℕ≢Π (whrDet* (red D′ , ℕₙ) (D , Πₙ)))
-- Π-elim′ D (Emptyᵣ D′) = ⊥-elim (Empty≢Π (whrDet* (red D′ , Emptyₙ) (D , Πₙ)))
-- Π-elim′ D (ne′ K D′ neK K≡K) =
--   ⊥-elim (Π≢ne neK (whrDet* (D , Πₙ) (red D′ , ne neK)))
-- Π-elim′ D (Πᵣ′ F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) =
--   noemb (Πᵣ F G D′ ⊢F ⊢G A≡A [F] [G] G-ext)
-- Π-elim′ D (emb 0<1 x) with Π-elim′ D x
-- Π-elim′ D (emb 0<1 x) | noemb x₁ = emb 0<1 (noemb x₁)
-- Π-elim′ D (emb 0<1 x) | emb () x₂

-- Π-elim : ∀ {Γ F G l} → Γ ⊩⟨ l ⟩ Π F ▹ G → Γ ⊩⟨ l ⟩Π Π F ▹ G
-- Π-elim [Π] = Π-elim′ (id (escape [Π])) [Π]

-- -- Extract a type and a level from a maybe embedding
-- extractMaybeEmb : ∀ {l ⊩⟨_⟩} → MaybeEmb l ⊩⟨_⟩ → ∃ λ l′ → ⊩⟨ l′ ⟩
-- extractMaybeEmb (noemb x) = _ , x
-- extractMaybeEmb (emb 0<1 x) = extractMaybeEmb x

-- emb, but with a propositional equality for the target level
emb″ : ∀ {Γ A} (l : TypeLevel) → (l PE.≡ ¹) → (p : Γ ⊩⟨ ⁰ ⟩ A) → Γ ⊩⟨ l ⟩ A
emb″ .¹ PE.refl p = emb′ 0<1 p

-- A view for constructor equality of types where embeddings are ignored
data ShapeView Γ (l l′ : TypeLevel) : ∀ A B (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l′ ⟩ B)
     → Set (lsuc (lsuc (toLevel l ⊔ toLevel l′))) where
  Uᵥ : ∀ l'A l<A ⊢ΓA l'B l<B ⊢ΓB
    → ShapeView Γ l l′ U U
      (LRPack _ _ _ (LRU ⊢ΓA l'A l<A))
      (LRPack _ _ _ (LRU ⊢ΓB l'B l<B))
  ℕᵥ : ∀ {A B} ℕA ℕB
    → ShapeView Γ l l′ A B
      (LRPack _ _ _ (LRℕ ℕA))
      (LRPack _ _ _ (LRℕ ℕB))
  ne  : ∀ {A B} neA neB
      → ShapeView Γ l l′ A B
        (LRPack _ _ _ (LRne neA))
        (LRPack _ _ _ (LRne neB))
  Πᵥ : ∀ {A B} ΠA ΠB
     → ShapeView Γ l l′ A B
       (LRPack _ _ _ (LRΠ ΠA))
       (LRPack _ _ _ (LRΠ ΠB))
  emb⁰¹ : ∀ {A B p q}
        → (l≡ : l PE.≡ ¹)
        → ShapeView Γ ⁰ l′ A B p q
        → ShapeView Γ l l′ A B (emb″ l l≡ p) q
  emb¹⁰ : ∀ {A B p q}
        → (l≡ : l′ PE.≡ ¹)
        → ShapeView Γ l ⁰ A B p q
        → ShapeView Γ l l′ A B p (emb″ l′ l≡ q)

-- Construct an shape view from an equality
goodCases : ∀ {l l′ Γ A B} ([A] : Γ ⊩⟨ l ⟩ A) ([B] : Γ ⊩⟨ l′ ⟩ B)
          → Γ ⊩⟨ l ⟩ A ≡ B / [A] → ShapeView Γ l l′ A B [A] [B]
goodCases (Uᵣ′ lA l<A ⊢ΓA) (Uᵣ′ lB l<B ⊢ΓB) A≡B = Uᵥ lA l<A ⊢ΓA lB l<B ⊢ΓB
goodCases (Uᵣ′ _ _ ⊢Γ) (ℕᵣ D) (U₌ PE.refl) = ⊥-elim (U≢ℕ (whnfRed* (red D) Uₙ))
goodCases (Uᵣ′ _ _ ⊢Γ) (ne′ K D neK K≡K) (U₌ PE.refl) = ⊥-elim (U≢ne neK (whnfRed* (red D) Uₙ))
goodCases (Uᵣ′ _ _ ⊢Γ) (Πᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (U₌ PE.refl) =
  ⊥-elim (U≢Π (whnfRed* (red D) Uₙ))
goodCases (ℕᵣ D) (Uᵣ′ _ _ ⊢Γ) (ιx (ℕ₌ A≡B)) = ⊥-elim (U≢ℕ (whnfRed* A≡B Uₙ))
goodCases (ℕᵣ ℕA) (ℕᵣ ℕB) A≡B = ℕᵥ ℕA ℕB
goodCases (ℕᵣ D) (ne′ K D₁ neK K≡K) (ιx (ℕ₌ A≡B)) =
  ⊥-elim (ℕ≢ne neK (whrDet* (A≡B , ℕₙ) (red D₁ , ne neK)))
goodCases (ℕᵣ D) (Πᵣ′ F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) (ιx (ℕ₌ A≡B)) =
  ⊥-elim (ℕ≢Π (whrDet* (A≡B , ℕₙ) (red D₁ , Πₙ)))
goodCases (ne′ K D neK K≡K) (Uᵣ′ _ _ ⊢Γ) (ιx (ne₌ M D′ neM K≡M)) =
  ⊥-elim (U≢ne neM (whnfRed* (red D′) Uₙ))
goodCases (ne′ K D neK K≡K) (ℕᵣ D₁) (ιx (ne₌ M D′ neM K≡M)) =
  ⊥-elim (ℕ≢ne neM (whrDet* (red D₁ , ℕₙ) (red D′ , ne neM)))
goodCases (ne′ K D neK K≡K) (ne′ K′ D′ neK′ K≡K′) A≡B = ne (ne K D neK K≡K) (ne K′ D′ neK′ K≡K′)
goodCases (ne′ K D neK K≡K) (Πᵣ′ F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) (ιx (ne₌ M D′ neM K≡M)) =
  ⊥-elim (Π≢ne neM (whrDet* (red D₁ , Πₙ) (red D′ , ne neM)))
goodCases (Πᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Uᵣ′ _ _ ⊢Γ)
          (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (U≢Π (whnfRed* D′ Uₙ))
goodCases (Πᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ℕᵣ D₁)
          (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (ℕ≢Π (whrDet* (red D₁ , ℕₙ) (D′ , Πₙ)))
goodCases (Πᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ne′ K D₁ neK K≡K)
          (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (Π≢ne neK (whrDet* (D′ , Πₙ) (red D₁ , ne neK)))
goodCases (LRPack _ _ _ (LRΠ ΠA)) (LRPack _ _ _ (LRΠ ΠB)) A≡B = Πᵥ ΠA ΠB
goodCases {l} [A] (emb′ 0<1 x) A≡B =
  emb¹⁰ PE.refl (goodCases {l} {⁰} [A] x A≡B)
goodCases {l′ = l} (emb′ 0<1 x) [B] (ιx A≡B) =
  emb⁰¹ PE.refl (goodCases {⁰} {l} x [B] A≡B)

-- Construct an shape view between two derivations of the same type
goodCasesRefl : ∀ {l l′ Γ A} ([A] : Γ ⊩⟨ l ⟩ A) ([A′] : Γ ⊩⟨ l′ ⟩ A)
              → ShapeView Γ l l′ A A [A] [A′]
goodCasesRefl [A] [A′] = goodCases [A] [A′] (reflEq [A])


-- A view for constructor equality between three types
data ShapeView₃ Γ (l l′ l″ : TypeLevel) : ∀ A B C
                 (p : Γ ⊩⟨ l  ⟩ A)
                 (q : Γ ⊩⟨ l′ ⟩ B)
                 (r : Γ ⊩⟨ l″ ⟩ C)
                 → Set (lsuc (lsuc (toLevel l ⊔ toLevel l′ ⊔ toLevel l″))) where
  Uᵥ : ∀ lA l<A ⊢ΓA lB l<B ⊢ΓB lC l<C ⊢ΓC
    → ShapeView₃ Γ l l′ l″ U U U
      (LRPack _ _ _ (LRU ⊢ΓA lA l<A))
      (LRPack _ _ _ (LRU ⊢ΓB lB l<B))
      (LRPack _ _ _ (LRU ⊢ΓC lC l<C))
  ℕᵥ : ∀ {A B C} ℕA ℕB ℕC
    → ShapeView₃ Γ l l′ l″ A B C
      (LRPack _ _ _ (LRℕ ℕA))
      (LRPack _ _ _ (LRℕ ℕB))
      (LRPack _ _ _ (LRℕ ℕC))
  ne  : ∀ {A B C} neA neB neC
      → ShapeView₃ Γ l l′ l″ A B C
        (LRPack _ _ _ (LRne neA))
        (LRPack _ _ _ (LRne neB))
        (LRPack _ _ _ (LRne neC))
  Πᵥ : ∀ {A B C} ΠA ΠB ΠC
     → ShapeView₃ Γ l l′ l″ A B C
       (LRPack _ _ _ (LRΠ ΠA))
       (LRPack _ _ _ (LRΠ ΠB))
       (LRPack _ _ _ (LRΠ ΠC))
  emb⁰¹¹ : ∀ {A B C p q r}
        → (l≡ : l PE.≡ ¹)
        → ShapeView₃ Γ ⁰ l′ l″ A B C p q r
        → ShapeView₃ Γ l l′ l″ A B C (emb″ l l≡ p) q r
  emb¹⁰¹ : ∀ {A B C p q r}
        → (l≡ : l′ PE.≡ ¹)
        → ShapeView₃ Γ l ⁰ l″ A B C p q r
        → ShapeView₃ Γ l l′ l″ A B C p (emb″ l′ l≡ q) r
  emb¹¹⁰ : ∀ {A B C p q r}
        → (l≡ : l″ PE.≡ ¹)
        → ShapeView₃ Γ l l′ ⁰ A B C p q r
        → ShapeView₃ Γ l l′ l″ A B C p q (emb″ l″ l≡ r)

-- Combines two two-way views into a three-way view
combine : ∀ {Γ l l′ l″ l‴ A B C [A] [B] [B]′ [C]}
        → ShapeView Γ l l′ A B [A] [B]
        → ShapeView Γ l″ l‴ B C [B]′ [C]
        → ShapeView₃ Γ l l′ l‴ A B C [A] [B] [C]
combine (Uᵥ lA l<A ⊢ΓA lB l<B ⊢ΓB) (Uᵥ _ _ _ lC l<C ⊢ΓC) = Uᵥ lA l<A ⊢ΓA lB l<B ⊢ΓB lC l<C ⊢ΓC
combine (Uᵥ lA l<A ⊢ΓA lB l<B ⊢ΓB) (ℕᵥ ℕA ℕB) = ⊥-elim (U≢ℕ (whnfRed* (red ℕA) Uₙ))
combine (Uᵥ lA l<A ⊢ΓA lB l<B ⊢ΓB) (ne (ne K D neK K≡K) neB) =
  ⊥-elim (U≢ne neK (whnfRed* (red D) Uₙ))
combine (Uᵥ lA l<A ⊢ΓA lB l<B ⊢ΓB) (Πᵥ (Πᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) ΠB) =
  ⊥-elim (U≢Π (whnfRed* (red D) Uₙ))
combine (ℕᵥ ℕA ℕB) (Uᵥ lB l<B ⊢ΓB lC l<C ⊢ΓC) = ⊥-elim (U≢ℕ (whnfRed* (red ℕB) Uₙ))
combine (ℕᵥ ℕA₁ ℕB₁) (ℕᵥ ℕA ℕB) = ℕᵥ ℕA₁ ℕB₁ ℕB
combine (ℕᵥ ℕA ℕB) (ne (ne K D neK K≡K) neB) =
  ⊥-elim (ℕ≢ne neK (whrDet* (red ℕB , ℕₙ) (red D , ne neK)))
combine (ℕᵥ ℕA ℕB) (Πᵥ (Πᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) ΠB) =
  ⊥-elim (ℕ≢Π (whrDet* (red ℕB , ℕₙ) (red D , Πₙ)))
combine (ne neA (ne K D neK K≡K)) (Uᵥ lB l<B ⊢ΓB lC l<C ⊢ΓC) =
  ⊥-elim (U≢ne neK (whnfRed* (red D) Uₙ))
combine (ne neA (ne K D neK K≡K)) (ℕᵥ ℕA ℕB) =
  ⊥-elim (ℕ≢ne neK (whrDet* (red ℕA , ℕₙ) (red D , ne neK)))
combine (ne neA₁ neB₁) (ne neA neB) = ne neA₁ neB₁ neB
combine (ne neA (ne K D₁ neK K≡K)) (Πᵥ (Πᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) ΠB) =
  ⊥-elim (Π≢ne neK (whrDet* (red D , Πₙ) (red D₁ , ne neK)))
combine (Πᵥ ΠA (Πᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Uᵥ lB l<B ⊢ΓB lC l<C ⊢ΓC) =
  ⊥-elim (U≢Π (whnfRed* (red D) Uₙ))
combine (Πᵥ ΠA (Πᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (ℕᵥ ℕA ℕB) =
  ⊥-elim (ℕ≢Π (whrDet* (red ℕA , ℕₙ) (red D , Πₙ)))
combine (Πᵥ ΠA (Πᵣ F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext)) (ne (ne K D neK K≡K) neB) =
  ⊥-elim (Π≢ne neK (whrDet* (red D₁ , Πₙ) (red D , ne neK)))
combine (Πᵥ ΠA₁ ΠB₁) (Πᵥ ΠA ΠB) = Πᵥ ΠA₁ ΠB₁ ΠB
combine (emb⁰¹ l≡ [AB]) [BC] = emb⁰¹¹ l≡ (combine [AB] [BC])
combine (emb¹⁰ l≡ [AB]) [BC] = emb¹⁰¹ l≡ (combine [AB] [BC])
combine [AB] (emb⁰¹ l≡ [BC]) = combine [AB] [BC]
combine [AB] (emb¹⁰ l≡ [BC]) = emb¹¹⁰ l≡ (combine [AB] [BC])
