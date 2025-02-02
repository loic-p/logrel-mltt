{-# OPTIONS --without-K --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Properties.Symmetry {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.LogicalRelation
open import Definition.LogicalRelation.ShapeView
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties.Conversion

open import Tools.Embedding
open import Tools.Product
import Tools.PropositionalEquality as PE


mutual
  -- Helper function for symmetry of type equality using shape views.
  symEqT : ∀ {Γ A B l l′} {[A] : Γ ⊩⟨ l ⟩ A} {[B] : Γ ⊩⟨ l′ ⟩ B}
         → ShapeView Γ l l′ A B [A] [B]
         → Γ ⊩⟨ l  ⟩ A ≡ B / [A]
         → Γ ⊩⟨ l′ ⟩ B ≡ A / [B]
  symEqT (ℕᵥ D D′) A≡B = ιx (ℕ₌ (red D))
  symEqT (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁)) (ιx (ne₌ M D′ neM K≡M))
         rewrite whrDet* (red D′ , ne neM) (red D₁ , ne neK₁) =
    ιx (ne₌ _ D neK
        (~-sym K≡M))
  symEqT {Γ = Γ} (Πᵥ (Πᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                     (Πᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁))
         (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
    let ΠF₁G₁≡ΠF′G′   = whrDet* (red D₁ , Πₙ) (D′ , Πₙ)
        F₁≡F′ , G₁≡G′ = Π-PE-injectivity ΠF₁G₁≡ΠF′G′
        [F₁≡F] : ∀ {Δ} {ρ} [ρ] ⊢Δ → _
        [F₁≡F] {Δ} {ρ} [ρ] ⊢Δ =
          let ρF′≡ρF₁ ρ = PE.cong (wk ρ) (PE.sym F₁≡F′)
              [ρF′] {ρ} [ρ] ⊢Δ = PE.subst (λ x → Δ ⊩⟨ _ ⟩ wk ρ x) F₁≡F′ ([F]₁ [ρ] ⊢Δ)
          in  irrelevanceEq′ {Δ} (ρF′≡ρF₁ ρ)
                             ([ρF′] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ)
                             (symEq ([F] [ρ] ⊢Δ) ([ρF′] [ρ] ⊢Δ)
                                    ([F≡F′] [ρ] ⊢Δ))
    in  Π₌ _ _ (red D) (≅-sym (PE.subst (λ x → Γ ⊢ Π F ▹ G ≅ x) (PE.sym ΠF₁G₁≡ΠF′G′) A≡B))
          [F₁≡F]
          (λ {ρ} [ρ] ⊢Δ [a] →
               let ρG′a≡ρG₁′a = PE.cong (λ x → wk (lift ρ) x [ _ ]) (PE.sym G₁≡G′)
                   [ρG′a] = PE.subst (λ x → _ ⊩⟨ _ ⟩ wk (lift ρ) x [ _ ]) G₁≡G′
                                     ([G]₁ [ρ] ⊢Δ [a])
                   [a]₁ = convTerm₁ ([F]₁ [ρ] ⊢Δ) ([F] [ρ] ⊢Δ) ([F₁≡F] [ρ] ⊢Δ) [a]
               in  irrelevanceEq′ ρG′a≡ρG₁′a
                                  [ρG′a]
                                  ([G]₁ [ρ] ⊢Δ [a])
                                  (symEq ([G] [ρ] ⊢Δ [a]₁) [ρG′a]
                                         ([G≡G′] [ρ] ⊢Δ [a]₁)))
  symEqT (Uᵥ _ _ _ _ _ _) A≡B = U₌ PE.refl
  symEqT (emb⁰¹ PE.refl x) (ιx A≡B) = symEqT x A≡B
  symEqT (emb¹⁰ PE.refl x) A≡B = ιx (symEqT x A≡B)

  -- Symmetry of type equality.
  symEq : ∀ {Γ A B l l′} ([A] : Γ ⊩⟨ l ⟩ A) ([B] : Γ ⊩⟨ l′ ⟩ B)
        → Γ ⊩⟨ l ⟩ A ≡ B / [A]
        → Γ ⊩⟨ l′ ⟩ B ≡ A / [B]
  symEq [A] [B] A≡B = symEqT (goodCases [A] [B] A≡B) A≡B

symNeutralTerm : ∀ {t u A Γ}
               → Γ ⊩neNf t ≡ u ∷ A
               → Γ ⊩neNf u ≡ t ∷ A
symNeutralTerm (neNfₜ₌ neK neM k≡m) = neNfₜ₌ neM neK (~-sym k≡m)

symNatural-prop : ∀ {Γ k k′}
                → [Natural]-prop Γ k k′
                → [Natural]-prop Γ k′ k
symNatural-prop (sucᵣ (ℕₜ₌ k k′ d d′ t≡u prop)) =
  sucᵣ (ℕₜ₌ k′ k d′ d (≅ₜ-sym t≡u) (symNatural-prop prop))
symNatural-prop zeroᵣ = zeroᵣ
symNatural-prop (ne prop) = ne (symNeutralTerm prop)

-- Symmetry of term equality.
symEqTerm : ∀ {l Γ A t u} ([A] : Γ ⊩⟨ l ⟩ A)
          → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A]
          → Γ ⊩⟨ l ⟩ u ≡ t ∷ A / [A]
symEqTerm (Uᵣ′ .⁰ 0<1 ⊢Γ) (Uₜ₌ A B d d′ typeA typeB A≡B [A] [B] [A≡B]) =
  Uₜ₌ B A d′ d typeB typeA (≅ₜ-sym A≡B) [B] [A] (symEq [A] [B] [A≡B])
symEqTerm (ℕᵣ D) (ιx (ℕₜ₌ k k′ d d′ t≡u prop)) =
  ιx (ℕₜ₌ k′ k d′ d (≅ₜ-sym t≡u) (symNatural-prop prop))
symEqTerm (ne′ K D neK K≡K) (ιx (neₜ₌ k m d d′ nf)) =
  ιx (neₜ₌ m k d′ d (symNeutralTerm nf))
symEqTerm (Πᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
          (Πₜ₌ f g d d′ funcF funcG f≡g [f] [g] [f≡g]) =
  Πₜ₌ g f d′ d funcG funcF (≅ₜ-sym f≡g) [g] [f]
      (λ ρ ⊢Δ [a] → symEqTerm ([G] ρ ⊢Δ [a]) ([f≡g] ρ ⊢Δ [a]))
symEqTerm (emb′ 0<1 x) (ιx t≡u) = ιx (symEqTerm x t≡u)
