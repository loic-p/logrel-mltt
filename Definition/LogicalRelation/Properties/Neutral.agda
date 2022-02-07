{-# OPTIONS --without-K --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Properties.Neutral {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.Weakening
open import Definition.LogicalRelation
open import Definition.LogicalRelation.ShapeView
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties.Reflexivity
open import Definition.LogicalRelation.Properties.Escape
open import Definition.LogicalRelation.Properties.Symmetry

open import Tools.Product
import Tools.PropositionalEquality as PE


-- Neutral reflexive types are reducible.
neu : ∀ {l Γ A} (neA : Neutral A)
    → Γ ⊢ A
    → Γ ⊢ A ~ A ∷ U
    → Γ ⊩⟨ l ⟩ A
neu neA A A~A = ne′ _ (idRed:*: A) neA A~A

  -- Helper function for reducible neutral equality of a specific type of derivation.
neuEq′ : ∀ {l Γ A B} ([A] : Γ ⊩⟨ l ⟩ne A)
         (neA : Neutral A)
         (neB : Neutral B)
       → Γ ⊢ A → Γ ⊢ B
       → Γ ⊢ A ~ B ∷ U
       → Γ ⊩⟨ l ⟩ A ≡ B / ne-intr [A]
neuEq′ (noemb (ne K [ ⊢A , ⊢B , D ] neK K≡K)) neA neB A B A~B =
  let A≡K = whnfRed* D (ne neA)
  in  ιx (ne₌ _ (idRed:*: B) neB (PE.subst (λ x → _ ⊢ x ~ _ ∷ _) A≡K A~B))
neuEq′ (emb 0<1 x) neA neB A B A~B  = ιx (neuEq′ x neA neB A B A~B)

-- Neutrally equal types are of reducible equality.
neuEq : ∀ {l Γ A B} ([A] : Γ ⊩⟨ l ⟩ A)
        (neA : Neutral A)
        (neB : Neutral B)
      → Γ ⊢ A → Γ ⊢ B
      → Γ ⊢ A ~ B ∷ U
      → Γ ⊩⟨ l ⟩ A ≡ B / [A]
neuEq [A] neA neB A B A~B =
  irrelevanceEq (ne-intr (ne-elim neA [A]))
                [A]
                (neuEq′ (ne-elim neA [A]) neA neB A B A~B)

mutual
  -- Neutral reflexive terms are reducible.
  neuTerm : ∀ {l Γ A n} ([A] : Γ ⊩⟨ l ⟩ A) (neN : Neutral n)
          → Γ ⊢ n ∷ A
          → Γ ⊢ n ~ n ∷ A
          → Γ ⊩⟨ l ⟩ n ∷ A / [A]
  neuTerm (Uᵣ′ .⁰ 0<1 ⊢Γ) neN n n~n =
    Uₜ _ (idRedTerm:*: n) (ne neN) (~-to-≅ₜ n~n) (neu neN (univ n) n~n)
  neuTerm (ℕᵣ [ ⊢A , ⊢B , D ]) neN n n~n =
    let A≡ℕ  = subset* D
        n~n′ = ~-conv n~n A≡ℕ
        n≡n  = ~-to-≅ₜ n~n′
    in ιx (ℕₜ _ (idRedTerm:*: (conv n A≡ℕ)) n≡n (ne (neNfₜ neN (conv n A≡ℕ) n~n′)))
  neuTerm (ne′ K [ ⊢A , ⊢B , D ] neK K≡K) neN n n~n =
    let A≡K = subset* D
    in ιx (neₜ _ (idRedTerm:*: (conv n A≡K)) (neNfₜ neN (conv n A≡K)
            (~-conv n~n A≡K)))
  neuTerm (Πᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) neN n n~n =
    let A≡ΠFG = subset* (red D)
    in  Πₜ _ (idRedTerm:*: (conv n A≡ΠFG)) (ne neN) (~-to-≅ₜ (~-conv n~n A≡ΠFG))
           (λ {ρ} [ρ] ⊢Δ [a] [b] [a≡b] →
              let A≡ΠFG = subset* (red D)
                  ρA≡ρΠFG = wkEq [ρ] ⊢Δ (subset* (red D))
                  G[a]≡G[b] = escapeEq ([G] [ρ] ⊢Δ [b])
                                          (symEq ([G] [ρ] ⊢Δ [a]) ([G] [ρ] ⊢Δ [b])
                                                 (G-ext [ρ] ⊢Δ [a] [b] [a≡b]))
                  a = escapeTerm ([F] [ρ] ⊢Δ) [a]
                  b = escapeTerm ([F] [ρ] ⊢Δ) [b]
                  a≡b = escapeTermEq ([F] [ρ] ⊢Δ) [a≡b]
                  ρn = conv (wkTerm [ρ] ⊢Δ n) ρA≡ρΠFG
                  neN∘a = ∘ₙ (wkNeutral ρ neN)
                  neN∘b = ∘ₙ (wkNeutral ρ neN)
              in  neuEqTerm ([G] [ρ] ⊢Δ [a]) neN∘a neN∘b
                            (ρn ∘ⱼ a)
                            (conv (ρn ∘ⱼ b) (≅-eq G[a]≡G[b]))
                            (~-app (~-wk [ρ] ⊢Δ (~-conv n~n A≡ΠFG)) a≡b))
           (λ {ρ} [ρ] ⊢Δ [a] →
              let ρA≡ρΠFG = wkEq [ρ] ⊢Δ (subset* (red D))
                  a = escapeTerm ([F] [ρ] ⊢Δ) [a]
                  a≡a = escapeTermEq ([F] [ρ] ⊢Δ) (reflEqTerm ([F] [ρ] ⊢Δ) [a])
              in  neuTerm ([G] [ρ] ⊢Δ [a]) (∘ₙ (wkNeutral ρ neN))
                          (conv (wkTerm [ρ] ⊢Δ n) ρA≡ρΠFG ∘ⱼ a)
                          (~-app (~-wk [ρ] ⊢Δ (~-conv n~n A≡ΠFG)) a≡a))
  neuTerm (emb′ 0<1 x) neN n n~n = ιx (neuTerm x neN n n~n)

  -- Neutrally equal terms are of reducible equality.
  neuEqTerm : ∀ {l Γ A n n′} ([A] : Γ ⊩⟨ l ⟩ A)
              (neN : Neutral n) (neN′ : Neutral n′)
            → Γ ⊢ n  ∷ A
            → Γ ⊢ n′ ∷ A
            → Γ ⊢ n ~ n′ ∷ A
            → Γ ⊩⟨ l ⟩ n ≡ n′ ∷ A / [A]
  neuEqTerm (Uᵣ′ .⁰ 0<1 ⊢Γ) neN neN′ n n′ n~n′ =
    let [n]  = neu neN  (univ n) (~-trans n~n′ (~-sym n~n′))
        [n′] = neu neN′ (univ n′) (~-trans (~-sym n~n′) n~n′)
    in  Uₜ₌ _ _ (idRedTerm:*: n) (idRedTerm:*: n′) (ne neN) (ne neN′)
            (~-to-≅ₜ n~n′) [n] [n′] (neuEq [n] neN neN′ (univ n) (univ n′) n~n′)
  neuEqTerm (ℕᵣ [ ⊢A , ⊢B , D ]) neN neN′ n n′ n~n′ =
    let A≡ℕ = subset* D
        n~n′₁ = ~-conv n~n′ A≡ℕ
        n≡n′ = ~-to-≅ₜ n~n′₁
    in ιx (ℕₜ₌ _ _ (idRedTerm:*: (conv n A≡ℕ)) (idRedTerm:*: (conv n′ A≡ℕ))
            n≡n′ (ne (neNfₜ₌ neN neN′ n~n′₁)))
  neuEqTerm (ne′ K [ ⊢A , ⊢B , D ] neK K≡K) neN neN′ n n′ n~n′ =
    let A≡K = subset* D
    in ιx (neₜ₌ _ _ (idRedTerm:*: (conv n A≡K)) (idRedTerm:*: (conv n′ A≡K))
             (neNfₜ₌ neN neN′ (~-conv n~n′ A≡K)))
  neuEqTerm (Πᵣ′ F G [ ⊢A , ⊢B , D ] ⊢F ⊢G A≡A [F] [G] G-ext) neN neN′ n n′ n~n′ =
    let [ΠFG] = Πᵣ′ F G [ ⊢A , ⊢B , D ] ⊢F ⊢G A≡A [F] [G] G-ext
        A≡ΠFG = subset* D
        n~n′₁ = ~-conv n~n′ A≡ΠFG
        n≡n′ = ~-to-≅ₜ n~n′₁
        n~n = ~-trans n~n′ (~-sym n~n′)
        n′~n′ = ~-trans (~-sym n~n′) n~n′
    in  Πₜ₌ _ _ (idRedTerm:*: (conv n A≡ΠFG)) (idRedTerm:*: (conv n′ A≡ΠFG))
            (ne neN) (ne neN′) n≡n′
            (neuTerm [ΠFG] neN n n~n) (neuTerm [ΠFG] neN′ n′ n′~n′)
            (λ {ρ} [ρ] ⊢Δ [a] →
               let ρA≡ρΠFG = wkEq [ρ] ⊢Δ A≡ΠFG
                   ρn = wkTerm [ρ] ⊢Δ n
                   ρn′ = wkTerm [ρ] ⊢Δ n′
                   a = escapeTerm ([F] [ρ] ⊢Δ) [a]
                   a≡a = escapeTermEq ([F] [ρ] ⊢Δ)
                                          (reflEqTerm ([F] [ρ] ⊢Δ) [a])
                   neN∙a   = ∘ₙ (wkNeutral ρ neN)
                   neN′∙a′ = ∘ₙ (wkNeutral ρ neN′)
               in  neuEqTerm ([G] [ρ] ⊢Δ [a]) neN∙a neN′∙a′
                             (conv ρn  ρA≡ρΠFG ∘ⱼ a)
                             (conv ρn′ ρA≡ρΠFG ∘ⱼ a)
                             (~-app (~-wk [ρ] ⊢Δ n~n′₁) a≡a))
  neuEqTerm (emb′ 0<1 x) neN neN′ n n′ n~n′ = ιx (neuEqTerm x neN neN′ n n′ n~n′)
