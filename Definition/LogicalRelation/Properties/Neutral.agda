{-# OPTIONS --without-K --allow-unsolved-metas #-}

module Definition.LogicalRelation.Properties.Neutral where

open import Definition.Untyped as U
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.Weakening
open import Definition.LogicalRelation
open import Definition.LogicalRelation.ShapeView
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties.Reflexivity
open import Definition.LogicalRelation.Properties.Escape
open import Definition.LogicalRelation.Properties.Symmetry
open import Definition.LogicalRelation.Properties.Reduction
open import Definition.LogicalRelation.Properties.Conversion
open import Definition.LogicalRelation.Properties.Normalize

open import Tools.Empty
open import Tools.Product
import Tools.PropositionalEquality as PE


-- Neutral reflexive types are reducible.
neu : ∀ {l Γ A} (neA : Neutral A)
    → Γ ⊢ A
    → Γ ⊩⟨ l ⟩ A
neu neA A = ne′ _ (idRed:*: A) neA

-- Helper function for reducible neutral equality of a specific type of derivation.
neuEq′ : ∀ {l Γ A B} ([A] : Γ ⊩⟨ l ⟩ne A)
         (neA : Neutral A)
         (neB : Neutral B)
       → Γ ⊢ A → Γ ⊢ B
       → A == B
       → Γ ⊩⟨ l ⟩ A ≡ B / ne-intr [A]
neuEq′ (noemb (ne K [ ⊢A , ⊢B , D ] neK)) neA neB A B A~B =
  let A≡K = dnfRed* D (ne neA)
  in  ne₌ _ (idRed:*: B) neB (PE.subst (λ x → x == _) A≡K A~B)
neuEq′ (emb 0<1 x) neB A:≡:B = neuEq′ x neB A:≡:B

-- Neutrally equal types are of reducible equality.
neuEq : ∀ {l Γ A B} ([A] : Γ ⊩⟨ l ⟩ A)
        (neA : Neutral A)
        (neB : Neutral B)
      → Γ ⊢ A → Γ ⊢ B
      → A == B
      → Γ ⊩⟨ l ⟩ A ≡ B / [A]
neuEq [A] neA neB A B A~B =
  irrelevanceEq (ne-intr (ne-elim neA [A]))
                [A]
                (neuEq′ (ne-elim neA [A]) neA neB A B A~B)

app-red : ∀ {Γ l F G t u u′}
  → ([F] : Γ ⊩⟨ l ⟩ F)
  → ([G] : ∀ {a} → Γ ⊩⟨ l ⟩ a ∷ F / [F] → Γ ⊩⟨ l ⟩ G [ a ])
  → (G-ext : ∀ {a b} → ([a] : Γ ⊩⟨ l ⟩ a ∷ F / [F])
             → ([b] : Γ ⊩⟨ l ⟩ b ∷ F / [F]) → Γ ⊩⟨ l ⟩ a ≡ b ∷ F / [F]
             → Γ ⊩⟨ l ⟩ G [ a ] ≡ G [ b ] / [G] [a])
  → Γ ⊢ t ∷ Π F ▹ G
  → Γ ⊩⟨ l ⟩ u′ ∷ F / [F]
  → Γ ⊢ u ⇒* u′ ∷ F
  → Γ ⊢ t ∘ u ⇒* t ∘ u′ ∷ G [ u′ ]
app-red [F] [G] G-ext ⊢t [u′] (id x) = id (⊢t ∘ x)
app-red {Γ} {l} {F} {G} {u = u} {u′ = u′} [F] [G] G-ext ⊢t [u′] (_⇨_ {t′ = t′} x D) =
  let
    [u] , [u≡u′] = redSubst*Term (x ⇨ D) [F] [u′]
    e = (escapeEq ([G] [u])  (G-ext [u] [u′] [u≡u′]))
  in conv (app-subst ⊢t x) e ⇨ app-red [F] [G] G-ext ⊢t [u′] D

mutual
  -- Neutral reflexive terms are reducible.
  neuTerm : ∀ {l Γ A n} ([A] : Γ ⊩⟨ l ⟩ A) (neN : Neutral n)
          → Γ ⊢ n ∷ A
          → Γ ⊩⟨ l ⟩ n ∷ A / [A]
  neuTerm (U′ .⁰ 0<1 ⊢Γ) neN n =
    Uₜ _ (idRedTerm:*: n) (ne neN) (neu neN (univ n))
  neuTerm (ℕ [ ⊢A , ⊢B , D ]) neN n =
    let A≡ℕ  = subset* D
    in  ℕₜ _ (idRedTerm:*: (conv n A≡ℕ)) (ne neN)
  neuTerm (ne′ K [ ⊢A , ⊢B , D ] neK) neN n =
    let A≡K = subset* D
    in  neₜ _ (idRedTerm:*: (conv n A≡K)) (neNfₜ neN (conv n A≡K))
  neuTerm (Π′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) neN n =
    let A≡ΠFG = subset* (red D)
    in  Πₜ _ (idRedTerm:*: (conv n A≡ΠFG)) (ne neN)
           (λ {ρ} [ρ] ⊢Δ [a] [b] [a≡b] →
              let A≡ΠFG = subset* (red D)
                  ρA≡ρΠFG = wkEq [ρ] ⊢Δ (subset* (red D))
                  a′ , da , b′ , db , a′==b′ = nfTermEq ([F] [ρ] ⊢Δ) [a] [b] [a≡b]
              in {!!})
           (λ {ρ} [ρ] ⊢Δ [a] →
              let ρA≡ρΠFG = wkEq [ρ] ⊢Δ (subset* (red D))
                  a = escapeTerm ([F] [ρ] ⊢Δ) [a]
                  a′ , (d , dnfa′) , [a′] = nfTerm ([F] [ρ] ⊢Δ) [a]
                  ⊢a′ = escapeTerm ([F] [ρ] ⊢Δ) [a′]
                  ⊢wkn = (conv (wkTerm [ρ] ⊢Δ n) ρA≡ρΠFG)
                  d′ = (app-red ([F] [ρ] ⊢Δ) ([G] [ρ] ⊢Δ) (G-ext [ρ] ⊢Δ) ⊢wkn [a′] d)
                  [a≡a′] = proj₂ (redSubst*Term d ([F] [ρ] ⊢Δ) [a′])
                  [n∘a′] = neuTerm ([G] [ρ] ⊢Δ [a′]) (_∘_ (wkNeutral ρ neN) dnfa′) (⊢wkn ∘ ⊢a′)
                  [n∘a] , _ = redSubst*Term d′ ([G] [ρ] ⊢Δ [a′]) [n∘a′]
              in convTerm₂ ([G] [ρ] ⊢Δ [a]) ([G] [ρ] ⊢Δ [a′]) (G-ext [ρ] ⊢Δ [a] [a′] [a≡a′]) [n∘a])
  neuTerm (emb 0<1 x) neN n = neuTerm x neN n

  -- Neutrally equal terms are of reducible equality.
  neuEqTerm : ∀ {l Γ A n n′} ([A] : Γ ⊩⟨ l ⟩ A)
              (neN : Neutral n) (neN′ : Neutral n′)
            → Γ ⊢ n  ∷ A
            → Γ ⊢ n′ ∷ A
            → n == n′
            → Γ ⊩⟨ l ⟩ n ≡ n′ ∷ A / [A]
  neuEqTerm = {!!}
  -- neuEqTerm (U′ .⁰ 0<1 ⊢Γ) neN neN′ n n′ n~n′ =
  --   let [n]  = neu neN  (univ n) (~-trans n~n′ (~-sym n~n′))
  --       [n′] = neu neN′ (univ n′) (~-trans (~-sym n~n′) n~n′)
  --   in  Uₜ₌ _ _ (idRedTerm:*: n) (idRedTerm:*: n′) (ne neN) (ne neN′)
  --           (~-to-≅ₜ n~n′) [n] [n′] (neuEq [n] neN neN′ (univ n) (univ n′) n~n′)
  -- neuEqTerm (ℕ [ ⊢A , ⊢B , D ]) neN neN′ n n′ n~n′ =
  --   let A≡ℕ = subset* D
  --       n~n′₁ = ~-conv n~n′ A≡ℕ
  --       n≡n′ = ~-to-≅ₜ n~n′₁
  --   in  ℕₜ₌ _ _ (idRedTerm:*: (conv n A≡ℕ)) (idRedTerm:*: (conv n′ A≡ℕ))
  --           n≡n′ (ne (neNfₜ₌ neN neN′ n~n′₁))
  -- neuEqTerm (ne (ne K [ ⊢A , ⊢B , D ] neK K≡K)) neN neN′ n n′ n~n′ =
  --   let A≡K = subset* D
  --   in  neₜ₌ _ _ (idRedTerm:*: (conv n A≡K)) (idRedTerm:*: (conv n′ A≡K))
  --            (neNfₜ₌ neN neN′ (~-conv n~n′ A≡K))
  -- neuEqTerm (Π′ F G [ ⊢A , ⊢B , D ] ⊢F ⊢G A≡A [F] [G] G-ext) neN neN′ n n′ n~n′ =
  --   let [ΠFG] = Π′ F G [ ⊢A , ⊢B , D ] ⊢F ⊢G A≡A [F] [G] G-ext
  --       A≡ΠFG = subset* D
  --       n~n′₁ = ~-conv n~n′ A≡ΠFG
  --       n≡n′ = ~-to-≅ₜ n~n′₁
  --       n~n = ~-trans n~n′ (~-sym n~n′)
  --       n′~n′ = ~-trans (~-sym n~n′) n~n′
  --   in  Πₜ₌ _ _ (idRedTerm:*: (conv n A≡ΠFG)) (idRedTerm:*: (conv n′ A≡ΠFG))
  --           (ne neN) (ne neN′) n≡n′
  --           (neuTerm [ΠFG] neN n n~n) (neuTerm [ΠFG] neN′ n′ n′~n′)
  --           (λ {ρ} [ρ] ⊢Δ [a] →
  --              let ρA≡ρΠFG = wkEq [ρ] ⊢Δ A≡ΠFG
  --                  ρn = wkTerm [ρ] ⊢Δ n
  --                  ρn′ = wkTerm [ρ] ⊢Δ n′
  --                  a = escapeTerm ([F] [ρ] ⊢Δ) [a]
  --                  a≡a = escapeTermEq ([F] [ρ] ⊢Δ)
  --                                         (reflEqTerm ([F] [ρ] ⊢Δ) [a])
  --                  neN∙a   = _∘_ (wkNeutral ρ neN)
  --                  neN′∙a′ = _∘_ (wkNeutral ρ neN′)
  --              in  neuEqTerm ([G] [ρ] ⊢Δ [a]) neN∙a neN′∙a′
  --                            (conv ρn  ρA≡ρΠFG ∘ a)
  --                            (conv ρn′ ρA≡ρΠFG ∘ a)
  --                            (~-app (~-wk [ρ] ⊢Δ n~n′₁) a≡a))
  -- neuEqTerm (emb 0<1 x) neN neN′ n:≡:n′ = neuEqTerm x neN neN′ n:≡:n′
