{-# OPTIONS --without-K #-}

module Definition.LogicalRelation.Properties.Symmetry where

open import Definition.Untyped as U
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.Weakening
open import Definition.LogicalRelation
open import Definition.LogicalRelation.ShapeView
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties.Conversion

open import Tools.Product
import Tools.PropositionalEquality as PE


mutual
  -- Helper function for symmetry of type equality using shape views.
  symEqT : ∀ {Γ A B l l′} {[A] : Γ ⊩⟨ l ⟩ A} {[B] : Γ ⊩⟨ l′ ⟩ B}
         → ShapeView Γ l l′ A B [A] [B]
         → Γ ⊩⟨ l  ⟩ A ≡ B / [A]
         → Γ ⊩⟨ l′ ⟩ B ≡ A / [B]
  symEqT (ℕ D D′) A≡B = red D
  symEqT (ne (ne K D neK) (ne K₁ D₁ neK₁)) (ne₌ M D′ neM K≡M)
         rewrite redDet* (red D′ , ne neM) (red D₁ , ne neK₁) =
    ne₌ _ D neK (==-sym K≡M)
  symEqT {Γ = Γ} (Π (Π F G D TyΠ ⊢F ⊢G [F] [G] G-ext)
                    (Π F₁ G₁ D₁ TyΠ₁ ⊢F₁ ⊢G₁ [F]₁ [G]₁ G-ext₁))
         (Π₌ F′ G′ D′ TyΠ′ A≡B [F≡F′] [G≡G′]) =
    let ΠF₁G₁≡ΠF′G′   = redDet* (red D₁ , typeDnf TyΠ₁) (red D′ , typeDnf TyΠ′)
        F₁≡F′ , G₁≡G′ = Π-PE-injectivity ΠF₁G₁≡ΠF′G′
        [F₁≡F] : ∀ {Δ} {ρ} [ρ] ⊢Δ → _
        [F₁≡F] {Δ} {ρ} [ρ] ⊢Δ =
          let ρF′≡ρF₁ ρ = PE.cong (U.wk ρ) (PE.sym F₁≡F′)
              [ρF′] {ρ} [ρ] ⊢Δ = PE.subst (λ x → Δ ⊩⟨ _ ⟩ U.wk ρ x) F₁≡F′ ([F]₁ [ρ] ⊢Δ)
          in  irrelevanceEq′ {Δ} (ρF′≡ρF₁ ρ)
                             ([ρF′] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ)
                             (symEq ([F] [ρ] ⊢Δ) ([ρF′] [ρ] ⊢Δ)
                                    ([F≡F′] [ρ] ⊢Δ))
    in  Π₌ _ _ D TyΠ (==-sym (PE.subst (λ x → Π F ▹ G == x) (PE.sym ΠF₁G₁≡ΠF′G′) A≡B))
          [F₁≡F]
          (λ {ρ} [ρ] ⊢Δ [a] →
               let ρG′a≡ρG₁′a = PE.cong (λ x → U.wk (lift ρ) x [ _ ]) (PE.sym G₁≡G′)
                   [ρG′a] = PE.subst (λ x → _ ⊩⟨ _ ⟩ U.wk (lift ρ) x [ _ ]) G₁≡G′
                                     ([G]₁ [ρ] ⊢Δ [a])
                   [a]₁ = convTerm₁ ([F]₁ [ρ] ⊢Δ) ([F] [ρ] ⊢Δ) ([F₁≡F] [ρ] ⊢Δ) [a]
               in  irrelevanceEq′ ρG′a≡ρG₁′a
                                  [ρG′a]
                                  ([G]₁ [ρ] ⊢Δ [a])
                                  (symEq ([G] [ρ] ⊢Δ [a]₁) [ρG′a]
                                         ([G≡G′] [ρ] ⊢Δ [a]₁)))
  symEqT (U (U _ _ _) (U _ _ _)) A≡B = PE.refl
  symEqT (emb⁰¹ x) A≡B = symEqT x A≡B
  symEqT (emb¹⁰ x) A≡B = symEqT x A≡B

  -- Symmetry of type equality.
  symEq : ∀ {Γ A B l l′} ([A] : Γ ⊩⟨ l ⟩ A) ([B] : Γ ⊩⟨ l′ ⟩ B)
        → Γ ⊩⟨ l ⟩ A ≡ B / [A]
        → Γ ⊩⟨ l′ ⟩ B ≡ A / [B]
  symEq [A] [B] A≡B = symEqT (goodCases [A] [B] A≡B) A≡B

symNeutralTerm : ∀ {t u A Γ}
               → Γ ⊩neNf t ≡ u ∷ A
               → Γ ⊩neNf u ≡ t ∷ A
symNeutralTerm (neNfₜ₌ neK neM k≡m) = neNfₜ₌ neM neK (==-sym k≡m)

-- Symmetry of term equality.
symEqTerm : ∀ {l Γ A t u} ([A] : Γ ⊩⟨ l ⟩ A)
          → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A]
          → Γ ⊩⟨ l ⟩ u ≡ t ∷ A / [A]
symEqTerm (U′ .⁰ 0<1 ⊢Γ) (Uₜ₌ A B d d′ typeA typeB A≡B [A] [B] [A≡B]) =
  Uₜ₌ B A d′ d typeB typeA (sym A≡B) [B] [A] (symEq [A] [B] [A≡B])
symEqTerm (ℕ D) (ℕₜ₌ k k′ d d′ prop prop₁ t≡u) =
  ℕₜ₌ k′ k d′ d prop₁ prop (==-sym t≡u)
symEqTerm (ne′ K D neK) (neₜ₌ k m d d′ nf) =
  neₜ₌ m k d′ d (symNeutralTerm nf)
symEqTerm (Π′ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
          (Πₜ₌ f g d d′ funcF funcG f==g f≡g [f] [g] [f≡g]) =
  Πₜ₌ g f d′ d funcG funcF (==-sym f==g) (sym f≡g) [g] [f]
      (λ ρ ⊢Δ [a] → symEqTerm ([G] ρ ⊢Δ [a]) ([f≡g] ρ ⊢Δ [a]))
symEqTerm (emb 0<1 x) t≡u = symEqTerm x t≡u
