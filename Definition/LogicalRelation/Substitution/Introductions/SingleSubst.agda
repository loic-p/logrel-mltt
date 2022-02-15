{-# OPTIONS --without-K --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Introductions.SingleSubst {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Weakening using (id)
open import Definition.Typed.Properties
open import Definition.LogicalRelation
open import Definition.LogicalRelation.ShapeView
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Properties
open import Definition.LogicalRelation.Substitution.Conversion
open import Definition.LogicalRelation.Substitution.Weakening

open import Tools.Embedding
open import Tools.Product
import Tools.PropositionalEquality as PE


-- Validity of substitution of single variable in types.
substS : ∀ {F G t Γ l} ([Γ] : ⊩ᵛ Γ)
         ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
         ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / ([Γ] ∙″ [F]))
         ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ F / [Γ] / [F])
       → Γ ⊩ᵛ⟨ l ⟩ G [ t ] / [Γ]
substS {F} {G} {t} [Γ] [F] [G] [t] {σ = σ} ⊢Δ [σ] =
  let Geq = substConsId G
      G[t] = proj₁ ([G] ⊢Δ ([σ] , (proj₁ ([t] ⊢Δ [σ]))))
      G[t]′ = irrelevance′ Geq G[t]
  in  G[t]′
  ,   (λ {σ′} [σ′] [σ≡σ′] →
         irrelevanceEq″ Geq
                         (substConsId G)
                         G[t] G[t]′
                         (proj₂ ([G] ⊢Δ
                                     ([σ] , proj₁ ([t] ⊢Δ [σ])))
                                     ([σ′] , proj₁ ([t] ⊢Δ [σ′]))
                                     (([σ≡σ′] , (proj₂ ([t] ⊢Δ [σ]) [σ′] [σ≡σ′])))))

-- Validity of substitution of single variable in type equality.
substSEq : ∀ {F F′ G G′ t t′ Γ l} ([Γ] : ⊩ᵛ Γ)
           ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
           ([F′] : Γ ⊩ᵛ⟨ l ⟩ F′ / [Γ])
           ([F≡F′] : Γ ⊩ᵛ⟨ l ⟩ F ≡ F′ / [Γ] / [F])
           ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / ([Γ] ∙″ [F]))
           ([G′] : Γ ∙ F′ ⊩ᵛ⟨ l ⟩ G′ / ([Γ] ∙″ [F′]))
           ([G≡G′] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G ≡ G′ / [Γ] ∙″ [F] / [G])
           ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ F / [Γ] / [F])
           ([t′] : Γ ⊩ᵛ⟨ l ⟩ t′ ∷ F′ / [Γ] / [F′])
           ([t≡t′] : Γ ⊩ᵛ⟨ l ⟩ t ≡ t′ ∷ F / [Γ] / [F])
         → Γ ⊩ᵛ⟨ l ⟩ G [ t ] ≡ G′ [ t′ ] / [Γ]
                   / substS {F} {G} {t} [Γ] [F] [G] [t]
substSEq {F} {F′} {G} {G′} {t} {t′}
         [Γ] [F] [F′] [F≡F′] [G] [G′] [G≡G′] [t] [t′] [t≡t′] {σ = σ} ⊢Δ [σ] =
  let Geq = substConsId G
      G′eq = substConsId G′
      G[t] = (proj₁ ([G] ⊢Δ ([σ] , (proj₁ ([t] ⊢Δ [σ])))))
      G[t]′ = irrelevance′ Geq G[t]
      [t]′ = convᵛ {t} {F} {F′} [Γ] [F] [F′] [F≡F′] [t]
      G′[t] = (proj₁ ([G′] ⊢Δ ([σ] , proj₁ ([t]′ ⊢Δ [σ]))))
      G[t]≡G′[t] = irrelevanceEq′ Geq G[t] G[t]′
                                  ([G≡G′] ⊢Δ ([σ] , proj₁ ([t] ⊢Δ [σ])))
      G′[t]≡G′[t′] = irrelevanceEq″ PE.refl G′eq G′[t] G′[t]
                       (proj₂ ([G′] ⊢Δ ([σ] , proj₁ ([t]′ ⊢Δ [σ])))
                              ([σ] , proj₁ ([t′] ⊢Δ [σ]))
                              (reflSubst [Γ] ⊢Δ [σ] ,
                                convEqᵛ {t} {t′} {F} {F′}
                                        [Γ] [F] [F′] [F≡F′] [t≡t′] ⊢Δ [σ]))
      G′[t′] = (proj₁ ([G′] ⊢Δ ([σ] , proj₁ ([t′] ⊢Δ [σ]))))
      G′[t′]′ = irrelevance′ G′eq G′[t′]
  in  transEq G[t]′ G′[t] G′[t′]′ G[t]≡G′[t] G′[t]≡G′[t′]

-- Validity of substitution of single variable in terms.
substSTerm : ∀ {F G t f Γ l} ([Γ] : ⊩ᵛ Γ)
             ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
             ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / ([Γ] ∙″ [F]))
             ([f] : Γ ∙ F ⊩ᵛ⟨ l ⟩ f ∷ G / ([Γ] ∙″ [F]) / [G])
             ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ F / [Γ] / [F])
           → Γ ⊩ᵛ⟨ l ⟩ f [ t ] ∷ G [ t ] / [Γ]
                      / substS {F} {G} {t} [Γ] [F] [G] [t]
substSTerm {F} {G} {t} {f} [Γ] [F] [G] [f] [t] {σ = σ} ⊢Δ [σ] =
  let prfG = substConsId G
      prff = substConsId f
      G[t] = proj₁ ([G] ⊢Δ ([σ] , proj₁ ([t] ⊢Δ [σ])))
      G[t]′ = irrelevance′ prfG G[t]
      f[t] = proj₁ ([f] ⊢Δ ([σ] , proj₁ ([t] ⊢Δ [σ])))
      f[t]′ = irrelevanceTerm″ prfG prff G[t] G[t]′ f[t]
  in  f[t]′
  ,   (λ {σ′} [σ′] [σ≡σ′] →
         irrelevanceEqTerm″
           prff
           (substConsId f)
           prfG G[t] G[t]′
           (proj₂ ([f] ⊢Δ ([σ] , proj₁ ([t] ⊢Δ [σ])))
                  ([σ′] , proj₁ ([t] ⊢Δ [σ′]))
                  ([σ≡σ′] , proj₂ ([t] ⊢Δ [σ]) [σ′] [σ≡σ′])))

-- Validity of substitution of single lifted variable in types.
subst↑S : ∀ {F G t Γ l} ([Γ] : ⊩ᵛ Γ)
          ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
          ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / ([Γ] ∙″ [F]))
          ([t] : Γ ∙ F ⊩ᵛ⟨ l ⟩ t ∷ wk1 F / ([Γ] ∙″ [F])
                              / wk1ᵛ {F} {F} [Γ] [F] [F])
        → Γ ∙ F ⊩ᵛ⟨ l ⟩ G [ t ]↑ / ([Γ] ∙″ [F])
subst↑S {F} {G} {t} [Γ] [F] [G] [t] {σ = σ} ⊢Δ [σ] =
  let [wk1F] = wk1ᵛ {F} {F} [Γ] [F] [F]
      [σwk1F] = proj₁ ([wk1F] {σ = σ} ⊢Δ [σ])
      [σwk1F]′ = proj₁ ([F] {σ = tail σ} ⊢Δ (proj₁ [σ]))
      [t]′ = irrelevanceTerm′ (subst-wk F) [σwk1F] [σwk1F]′ (proj₁ ([t] ⊢Δ [σ]))
      G[t] = proj₁ ([G] {σ = consSubst (tail σ) (subst σ t)} ⊢Δ
                               (proj₁ [σ] , [t]′))
      G[t]′ = irrelevance′ (substConsTailId {G} {t} {σ}) G[t]
  in  G[t]′
  ,   (λ {σ′} [σ′] [σ≡σ′] →
         let [σ′t] = irrelevanceTerm′ (subst-wk F)
                                      (proj₁ ([wk1F] {σ = σ′} ⊢Δ [σ′]))
                                      (proj₁ ([F] ⊢Δ (proj₁ [σ′])))
                                      (proj₁ ([t] ⊢Δ [σ′]))
             [σt≡σ′t] = irrelevanceEqTerm′ (subst-wk F) [σwk1F] [σwk1F]′
                                           (proj₂ ([t] ⊢Δ [σ]) [σ′] [σ≡σ′])
             [σG[t]≡σ′G[t]] = proj₂ ([G] ⊢Δ (proj₁ [σ] , [t]′))
                                    (proj₁ [σ′] , [σ′t])
                                    (proj₁ [σ≡σ′] , [σt≡σ′t])
         in irrelevanceEq″ (substConsTailId {G} {t} {σ}) (substConsTailId {G} {t} {σ′})
                            G[t] G[t]′ [σG[t]≡σ′G[t]])

-- Validity of substitution of single lifted variable in type equality.
subst↑SEq : ∀ {F G G′ t t′ Γ l} ([Γ] : ⊩ᵛ Γ)
            ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
            ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / ([Γ] ∙″ [F]))
            ([G′] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G′ / ([Γ] ∙″ [F]))
            ([G≡G′] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G ≡ G′ / [Γ] ∙″ [F] / [G])
            ([t] : Γ ∙ F ⊩ᵛ⟨ l ⟩ t ∷ wk1 F / [Γ] ∙″ [F]
                                / wk1ᵛ {F} {F} [Γ] [F] [F])
            ([t′] : Γ ∙ F ⊩ᵛ⟨ l ⟩ t′ ∷ wk1 F / [Γ] ∙″ [F]
                                 / wk1ᵛ {F} {F} [Γ] [F] [F])
            ([t≡t′] : Γ ∙ F ⊩ᵛ⟨ l ⟩ t ≡ t′ ∷ wk1 F / [Γ] ∙″ [F]
                                   / wk1ᵛ {F} {F} [Γ] [F] [F])
          → Γ ∙ F ⊩ᵛ⟨ l ⟩ G [ t ]↑ ≡ G′ [ t′ ]↑ / [Γ] ∙″ [F]
                        / subst↑S {F} {G} {t} [Γ] [F] [G] [t]
subst↑SEq {F} {G} {G′} {t} {t′}
          [Γ] [F] [G] [G′] [G≡G′] [t] [t′] [t≡t′] {σ = σ} ⊢Δ [σ] =
  let [wk1F] = wk1ᵛ {F} {F} [Γ] [F] [F]
      [σwk1F] = proj₁ ([wk1F] {σ = σ} ⊢Δ [σ])
      [σwk1F]′ = proj₁ ([F] {σ = tail σ} ⊢Δ (proj₁ [σ]))
      [t]′ = irrelevanceTerm′ (subst-wk F) [σwk1F] [σwk1F]′ (proj₁ ([t] ⊢Δ [σ]))
      [t′]′ = irrelevanceTerm′ (subst-wk F) [σwk1F] [σwk1F]′ (proj₁ ([t′] ⊢Δ [σ]))
      [t≡t′]′ = irrelevanceEqTerm′ (subst-wk F) [σwk1F] [σwk1F]′ ([t≡t′] ⊢Δ [σ])
      G[t] = proj₁ ([G] ⊢Δ (proj₁ [σ] , [t]′))
      G[t]′ = irrelevance′ (substConsTailId {G} {t} {σ}) G[t]
      G′[t] = proj₁ ([G′] ⊢Δ (proj₁ [σ] , [t]′))
      G′[t]′ = irrelevance′ (substConsTailId {G′} {t} {σ}) G′[t]
      G′[t′] = proj₁ ([G′] ⊢Δ (proj₁ [σ] , [t′]′))
      G′[t′]′ = irrelevance′ (substConsTailId {G′} {t′} {σ}) G′[t′]
      G[t]≡G′[t] = irrelevanceEq″ (substConsTailId {G} {t} {σ}) (substConsTailId {G′} {t} {σ})
                                   G[t] G[t]′ ([G≡G′] ⊢Δ (proj₁ [σ] , [t]′))
      G′[t]≡G′[t′] = irrelevanceEq″ (substConsTailId {G′} {t} {σ})
                                     (substConsTailId {G′} {t′} {σ})
                                     G′[t] G′[t]′
                                     (proj₂ ([G′] ⊢Δ (proj₁ [σ] , [t]′))
                                            (proj₁ [σ] , [t′]′)
                                            (reflSubst [Γ] ⊢Δ (proj₁ [σ]) , [t≡t′]′))
  in  transEq G[t]′ G′[t]′ G′[t′]′ G[t]≡G′[t] G′[t]≡G′[t′]

-- Helper function for reducible substitution of Π-types with specific typing derivations.
substSΠ₁′ : ∀ {F G t Γ l l′}
           ([ΠFG] : Γ ⊩⟨ l ⟩Π Π F ▹ G)
           ([F] : Γ ⊩⟨ l′ ⟩ F)
           ([t] : Γ ⊩⟨ l′ ⟩ t ∷ F / [F])
         → Γ ⊩⟨ l ⟩ G [ t ]
substSΠ₁′ {t = t} (noemb (Πᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) [F]₁ [t] =
  let F≡F′ , G≡G′ = Π-PE-injectivity (whnfRed* (red D) Πₙ)
      Feq = PE.trans F≡F′ (PE.sym (wk-id _))
      Geq = PE.cong (λ x → x [ _ ]) (PE.trans (wk-lift-id _) (PE.sym G≡G′))
      ⊢Γ = wf (escape [F]₁)
      [t]′ = irrelevanceTerm′ Feq [F]₁ ([F] id ⊢Γ) [t]
  in  irrelevance′ Geq ([G] id ⊢Γ [t]′)
substSΠ₁′ (emb 0<1 x) [F]₁ [t] = emb′ 0<1 (substSΠ₁′ x [F]₁ [t])

-- Reducible substitution of Π-types.
substSΠ₁ : ∀ {F G t Γ l l′}
           ([ΠFG] : Γ ⊩⟨ l ⟩ Π F ▹ G)
           ([F] : Γ ⊩⟨ l′ ⟩ F)
           ([t] : Γ ⊩⟨ l′ ⟩ t ∷ F / [F])
         → Γ ⊩⟨ l ⟩ G [ t ]
substSΠ₁ [ΠFG] [F] [t] = substSΠ₁′ (Π-elim [ΠFG]) [F] [t]

-- Helper function for reducible substitution of Π-congurence with specific typing derivations.
substSΠ₂′ : ∀ {F F′ G G′ t t′ Γ l l′ l″ l‴}
           ([ΠFG] : Γ ⊩⟨ l ⟩Π Π F ▹ G)
           ([ΠFG≡ΠF′G′] : Γ ⊩⟨ l ⟩ Π F ▹ G ≡ Π F′ ▹ G′ / Π-intr [ΠFG])
           ([F] : Γ ⊩⟨ l′ ⟩ F)
           ([F′] : Γ ⊩⟨ l′ ⟩ F′)
           ([t] : Γ ⊩⟨ l′ ⟩ t ∷ F / [F])
           ([t′] : Γ ⊩⟨ l′ ⟩ t′ ∷ F′ / [F′])
           ([t≡t′] : Γ ⊩⟨ l′ ⟩ t ≡ t′ ∷ F / [F])
           ([G[t]] : Γ ⊩⟨ l″ ⟩ G [ t ])
           ([G′[t′]] : Γ ⊩⟨ l‴ ⟩ G′ [ t′ ])
         → Γ ⊩⟨ l″ ⟩ G [ t ] ≡ G′ [ t′ ] / [G[t]]
substSΠ₂′ (noemb (Πᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext))
          (Π₌ F″ G″ D′ A≡B [F≡F′] [G≡G′])
          [F]₁ [F′] [t] [t′] [t≡t′] [G[t]] [G′[t′]] =
  let F≡F′ , G≡G′ = Π-PE-injectivity (whnfRed* (red D) Πₙ)
      F′≡F″ , G′≡G″ = Π-PE-injectivity (whnfRed* D′ Πₙ)
      Feq = PE.trans F≡F′ (PE.sym (wk-id _))
      F′eq = PE.trans F′≡F″ (PE.sym (wk-id _))
      Geq = PE.cong (λ x → x [ _ ]) (PE.trans (wk-lift-id _) (PE.sym G≡G′))
      Geq′ = PE.cong (λ x → x [ _ ]) (PE.trans G′≡G″ (PE.sym (wk-lift-id _)))
      ⊢Γ = wf (escape [F]₁)
      [t]′ = irrelevanceTerm′ Feq [F]₁ ([F] id ⊢Γ) [t]
      [t′]′ = convTerm₂′ F′eq ([F] id ⊢Γ) [F′] ([F≡F′] id ⊢Γ) [t′]
      [t≡t′]′ = irrelevanceEqTerm′ Feq [F]₁ ([F] id ⊢Γ) [t≡t′]
      [Gt≡Gt′] = G-ext id ⊢Γ [t]′ [t′]′ [t≡t′]′
      [Gt′≡G′t′] = [G≡G′] id ⊢Γ [t′]′
  in  irrelevanceEq′ Geq ([G] id ⊢Γ [t]′) [G[t]]
        (transEq′ PE.refl Geq′ ([G] id ⊢Γ [t]′) ([G] id ⊢Γ [t′]′)
                  [G′[t′]] [Gt≡Gt′] [Gt′≡G′t′])
substSΠ₂′ (emb 0<1 x) (ιx y) = substSΠ₂′ x y

-- Reducible substitution of Π-congurence.
substSΠ₂ : ∀ {F F′ G G′ t t′ Γ l l′ l″ l‴}
           ([ΠFG] : Γ ⊩⟨ l ⟩ Π F ▹ G)
           ([ΠFG≡ΠF′G′] : Γ ⊩⟨ l ⟩ Π F ▹ G ≡ Π F′ ▹ G′ / [ΠFG])
           ([F] : Γ ⊩⟨ l′ ⟩ F)
           ([F′] : Γ ⊩⟨ l′ ⟩ F′)
           ([t] : Γ ⊩⟨ l′ ⟩ t ∷ F / [F])
           ([t′] : Γ ⊩⟨ l′ ⟩ t′ ∷ F′ / [F′])
           ([t≡t′] : Γ ⊩⟨ l′ ⟩ t ≡ t′ ∷ F / [F])
           ([G[t]] : Γ ⊩⟨ l″ ⟩ G [ t ])
           ([G′[t′]] : Γ ⊩⟨ l‴ ⟩ G′ [ t′ ])
         → Γ ⊩⟨ l″ ⟩ G [ t ] ≡ G′ [ t′ ] / [G[t]]
substSΠ₂ [ΠFG] [ΠFG≡ΠF′G′] =
  let [ΠFG≡ΠF′G′]′ = irrelevanceEq [ΠFG] (Π-intr (Π-elim [ΠFG])) [ΠFG≡ΠF′G′]
  in  substSΠ₂′ (Π-elim [ΠFG]) [ΠFG≡ΠF′G′]′

-- Valid substitution of Π-types.
substSΠ : ∀ {F G t Γ l}
          ([Γ] : ⊩ᵛ Γ)
          ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
          ([ΠFG] : Γ ⊩ᵛ⟨ l ⟩ Π F ▹ G / [Γ])
          ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ F / [Γ] / [F])
        → Γ ⊩ᵛ⟨ l ⟩ G [ t ] / [Γ]
substSΠ {F} {G} {t} [Γ] [F] [ΠFG] [t] ⊢Δ [σ] =
  let [σG[t]] = substSΠ₁ (proj₁ ([ΠFG] ⊢Δ [σ])) (proj₁ ([F] ⊢Δ [σ]))
                         (proj₁ ([t] ⊢Δ [σ]))
      [σG[t]]′ = irrelevance′ (PE.sym (singleSubstLift G t))
                          [σG[t]]
  in  [σG[t]]′
  ,   (λ [σ′] [σ≡σ′] →
         irrelevanceEq″ (PE.sym (singleSubstLift G t))
                         (PE.sym (singleSubstLift G t))
                         [σG[t]] [σG[t]]′
                         (substSΠ₂ (proj₁ ([ΠFG] ⊢Δ [σ]))
                                   (proj₂ ([ΠFG] ⊢Δ [σ]) [σ′] [σ≡σ′])
                                   (proj₁ ([F] ⊢Δ [σ])) (proj₁ ([F] ⊢Δ [σ′]))
                                   (proj₁ ([t] ⊢Δ [σ])) (proj₁ ([t] ⊢Δ [σ′]))
                                   (proj₂ ([t] ⊢Δ [σ]) [σ′] [σ≡σ′]) [σG[t]]
                                   (substSΠ₁ (proj₁ ([ΠFG] ⊢Δ [σ′]))
                                             (proj₁ ([F] ⊢Δ [σ′]))
                                             (proj₁ ([t] ⊢Δ [σ′])))))

-- Valid substitution of Π-congurence.
substSΠEq : ∀ {F G F′ G′ t u Γ l}
            ([Γ] : ⊩ᵛ Γ)
            ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
            ([F′] : Γ ⊩ᵛ⟨ l ⟩ F′ / [Γ])
            ([ΠFG] : Γ ⊩ᵛ⟨ l ⟩ Π F ▹ G / [Γ])
            ([ΠF′G′] : Γ ⊩ᵛ⟨ l ⟩ Π F′ ▹ G′ / [Γ])
            ([ΠFG≡ΠF′G′] : Γ ⊩ᵛ⟨ l ⟩ Π F ▹ G ≡ Π F′ ▹ G′ / [Γ] / [ΠFG])
            ([t]   : Γ ⊩ᵛ⟨ l ⟩ t ∷ F / [Γ] / [F])
            ([u]   : Γ ⊩ᵛ⟨ l ⟩ u ∷ F′ / [Γ] / [F′])
            ([t≡u] : Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ F / [Γ] / [F])
          → Γ ⊩ᵛ⟨ l ⟩ G [ t ] ≡ G′ [ u ] / [Γ]
                    / substSΠ {F} {G} {t} [Γ] [F] [ΠFG] [t]
substSΠEq {F} {G} {F′} {G′} {t} {u} [Γ] [F] [F′] [ΠFG] [ΠF′G′] [ΠFG≡ΠF′G′]
           [t] [u] [t≡u] {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [σΠFG] = proj₁ ([ΠFG] ⊢Δ [σ])
      Πᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁ = extractMaybeEmbΠ (Π-elim [σΠFG])
      F≡F₁ , G≡G₁ = Π-PE-injectivity (whnfRed* (red D₁) Πₙ)
      [σΠF′G′] = proj₁ ([ΠF′G′] ⊢Δ [σ])
      Πᵣ F₂ G₂ D₂ ⊢F₂ ⊢G₂ A≡A₂ [F]₂ [G]₂ G-ext₂ = extractMaybeEmbΠ (Π-elim [σΠF′G′])
      F′≡F₂ , G′≡G₂ = Π-PE-injectivity (whnfRed* (red D₂) Πₙ)
      [σF] = proj₁ ([F] ⊢Δ [σ])
      [σF′] = proj₁ ([F′] ⊢Δ [σ])
      [σt] = proj₁ ([t] ⊢Δ [σ])
      [σu] = proj₁ ([u] ⊢Δ [σ])
      [σt]′ = irrelevanceTerm′ (PE.trans F≡F₁ (PE.sym (wk-id F₁)))
                               [σF] ([F]₁ id ⊢Δ) [σt]
      [σu]′ = irrelevanceTerm′ (PE.trans F′≡F₂ (PE.sym (wk-id F₂)))
                               [σF′] ([F]₂ id ⊢Δ) [σu]
      [σt≡σu] = [t≡u] ⊢Δ [σ]
      [G[t]] = irrelevance′ (PE.cong (λ x → x [ subst σ t ])
                                     (PE.trans (wk-lift-id G₁) (PE.sym G≡G₁)))
                            ([G]₁ id ⊢Δ [σt]′)
      [G′[u]] = irrelevance′ (PE.cong (λ x → x [ subst σ u ])
                                      (PE.trans (wk-lift-id G₂) (PE.sym G′≡G₂)))
                             ([G]₂ id ⊢Δ [σu]′)
  in  irrelevanceEq″ (PE.sym (singleSubstLift G t))
                      (PE.sym (singleSubstLift G′ u))
                      [G[t]]
                        (proj₁ (substSΠ {F} {G} {t} [Γ] [F] [ΠFG] [t] ⊢Δ [σ]))
                      (substSΠ₂ {subst σ F} {subst σ F′}
                                {subst (liftSubst σ) G}
                                {subst (liftSubst σ) G′}
                                (proj₁ ([ΠFG] ⊢Δ [σ]))
                                ([ΠFG≡ΠF′G′] ⊢Δ [σ])
                                [σF] [σF′] [σt] [σu] [σt≡σu] [G[t]] [G′[u]])
