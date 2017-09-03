module Section7 where

open import Section6 public


-- 7. Correspondence between proof trees and terms
-- ===============================================

mutual
  ⌊_⌋ : ∀ {Γ A} → Γ ⊢ A → Tm
  ⌊ ν x i ⌋ = ν x
  ⌊ ƛ x M ⌋ = ƛ x ⌊ M ⌋
  ⌊ M ∙ N ⌋ = ⌊ M ⌋ ∙ ⌊ N ⌋
  ⌊ M ▶ γ ⌋ = ⌊ M ⌋ ▶ ⌊ γ ⌋⋆

  ⌊_⌋⋆ : ∀ {Γ Γ′} → Γ′ ⋙ Γ → Sub
  ⌊ π⟨ c ⟩ ⌋⋆        = []
  ⌊ γ ● γ′ ⌋⋆        = ⌊ γ ⌋⋆ ● ⌊ γ′ ⌋⋆
  ⌊ [ γ , x ≔ M ] ⌋⋆ = [ ⌊ γ ⌋⋆ , x ≔ ⌊ M ⌋ ]

-- Lemma 12.
mutual
  lem₁₂ : ∀ {Γ A} → (M : Γ ⊢ A) → Γ ⊢ ⌊ M ⌋ ∷ A
  lem₁₂ (ν x i) = ν x i
  lem₁₂ (ƛ x M) = ƛ x (lem₁₂ M)
  lem₁₂ (M ∙ N) = lem₁₂ M ∙ lem₁₂ N
  lem₁₂ (M ▶ γ) = lem₁₂ M ▶ lem₁₂⋆ γ

  lem₁₂⋆ : ∀ {Γ Γ′} → (γ : Γ′ ⋙ Γ) → Γ′ ⋙ ⌊ γ ⌋⋆ ∷ Γ
  lem₁₂⋆ (π⟨ c ⟩)        = ↑⟨ c ⟩ refl
  lem₁₂⋆ (γ ● γ′)        = lem₁₂⋆ γ ● lem₁₂⋆ γ′
  lem₁₂⋆ ([ γ , x ≔ M ]) = [ lem₁₂⋆ γ , x ≔ lem₁₂ M ]

mutual
  infix 3 _DecoratesTo_
  data _DecoratesTo_ : ∀ {Γ A} → Tm → Γ ⊢ A → Set where
    ν    : ∀ {Γ A} →
             (x : Name) (i : Γ ∋ x ∷ A) →
             ν x DecoratesTo ν x i
    ƛ    : ∀ {Γ A B t} →
             (x : Name) {{_ : T (fresh x Γ)}} {M : [ Γ , x ∷ A ] ⊢ B} → t DecoratesTo M →
             ƛ x t DecoratesTo ƛ x M
    _∙_  : ∀ {Γ A B t u} {M : Γ ⊢ A ⊃ B} {N : Γ ⊢ A} →
             t DecoratesTo M → u DecoratesTo N →
             t ∙ u DecoratesTo M ∙ N
    _▶_  : ∀ {Γ Γ′ A s t} {M : Γ ⊢ A} {γ : Γ′ ⋙ Γ} →
             t DecoratesTo M → s DecoratesTo⋆ γ →
             t ▶ s DecoratesTo M ▶ γ
    π⟨_⟩ : ∀ {Γ Γ′ A t} {M : Γ ⊢ A} →
             (c : Γ′ ⊇ Γ) → t DecoratesTo M →
             t DecoratesTo M ▶ π⟨ c ⟩

  infix 3 _DecoratesTo⋆_
  data _DecoratesTo⋆_ : ∀ {Γ Γ′} → Sub → Γ′ ⋙ Γ → Set where
    π⟨_⟩    : ∀ {Γ Γ′} →
                (c : Γ′ ⊇ Γ) →
                [] DecoratesTo⋆ π⟨ c ⟩
    _●_     : ∀ {Γ Γ′ Γ″ s s′} {γ : Γ′ ⋙ Γ} {γ′ : Γ″ ⋙ Γ′} →
                s DecoratesTo⋆ γ → s′ DecoratesTo⋆ γ′ →
                s ● s′ DecoratesTo⋆ γ ● γ′
    [_,_≔_] : ∀ {Γ Γ′ A s t} {γ : Γ′ ⋙ Γ} {M : Γ′ ⊢ A} →
                s DecoratesTo⋆ γ → (x : Name) {{_ : T (fresh x Γ)}} → t DecoratesTo M →
                [ s , x ≔ t ] DecoratesTo⋆ [ γ , x ≔ M ]
    𝒟⋆-↑⟨_⟩ : ∀ {Γ Γ′ Δ s} {δ : Γ ⋙ Δ} →
                (c : Γ′ ⊇ Γ) → s DecoratesTo⋆ δ →
                s DecoratesTo⋆ ↑⟨ c ⟩ δ
    𝒟⋆-↓⟨_⟩ : ∀ {Γ Γ′ Δ s} {δ : Δ ⋙ Γ′} →
                (c : Γ′ ⊇ Γ) → s DecoratesTo⋆ δ →
                s DecoratesTo⋆ ↓⟨ c ⟩ δ

-- Lemma 13.
mutual
  lem₁₃ : ∀ {Γ A} → (M : Γ ⊢ A) → ⌊ M ⌋ DecoratesTo M
  lem₁₃ (ν x i) = ν x i
  lem₁₃ (ƛ x M) = ƛ x (lem₁₃ M)
  lem₁₃ (M ∙ N) = lem₁₃ M ∙ lem₁₃ N
  lem₁₃ (M ▶ γ) = lem₁₃ M ▶ lem₁₃⋆ γ

  lem₁₃⋆ : ∀ {Γ Γ′} → (γ : Γ′ ⋙ Γ) → ⌊ γ ⌋⋆ DecoratesTo⋆ γ
  lem₁₃⋆ π⟨ c ⟩        = π⟨ c ⟩
  lem₁₃⋆ (γ ● γ′)      = lem₁₃⋆ γ ● lem₁₃⋆ γ′
  lem₁₃⋆ [ γ , x ≔ M ] = [ lem₁₃⋆ γ , x ≔ lem₁₃ M ]

-- Lemma 14.
postulate
  lem₁₄ : ∀ {Γ A t} → Γ ⊢ t ∷ A → Σ (Γ ⊢ A) (λ M → ⌊ M ⌋ ≡ t)

-- Lemma 15.
lem₁₅ : ∀ {Γ A t} → Γ ⊢ t ∷ A → Σ (Γ ⊢ A) (λ M → t DecoratesTo M)
lem₁₅ D = case lem₁₄ D of λ { (M , refl) → M , lem₁₃ M }

-- TODO:
-- “As a consequence of this lemma we can now define the semantics of a well-typed term in
-- a Kripke model as the semantics of the decorated term.  In the remaining text, however, we
-- study only the correspondence between terms and proof trees since the translation to the
-- semantics is direct.”

-- Lemma 16.
mutual
  postulate
    lem₁₆ : ∀ {Γ A t} {M M′ : Γ ⊢ A} {{_ : ENF M}} {{_ : ENF M′}} →
              t DecoratesTo M → t DecoratesTo M′ →
              M ≡ M′

  postulate
    lem₁₆′ : ∀ {Γ A A′ t} {M : Γ ⊢ A} {N : Γ ⊢ A′} {{_ : ANF M}} {{_ : ANF N}} →
               t DecoratesTo M → t DecoratesTo N →
               A ≡ A′

-- TODO: Uh oh. Heterogeneous equality?
--  postulate
--    lem₁₆″ : ∀ {Γ A A′ t} {M : Γ ⊢ A} {M′ : Γ ⊢ A′} {{_ : ANF M}} {{_ : ANF M′}} →
--               t DecoratesTo M → t DecoratesTo M′ →
--               M ≡ M′

  postulate
    lem₁₆″ : ∀ {Γ A t} {M M′ : Γ ⊢ A} {{_ : ANF M}} {{_ : ANF M′}} →
               t DecoratesTo M → t DecoratesTo M′ →
               M ≡ M′

-- Corollary 2.
postulate
  cor₂ : ∀ {Γ A} → (M M′ : Γ ⊢ A) → ⌊ nf M ⌋ ≡ ⌊ nf M′ ⌋ → M ≅ M′


-- 7.1. Reduction
-- --------------

mutual
  data WHNF : Tm → Set where
    whnf-λ : ∀ {t x} → WHNF t → WHNF (ƛ x t)
    whnf-a : ∀ {t} → WHANF t → WHNF t

  data WHANF : Tm → Set where
    whanf-ν : ∀ {x} → WHANF (ν x)
    whanf-∙ : ∀ {t u} → WHANF t → WHNF u → WHANF (t ∙ u)

mutual
  infix 3 _⇢_
  data _⇢_ : Tm → Tm → Set where
    red₁ : ∀ {s t u x} →
             (ƛ x t ▶ s) ∙ u ⇢ t ▶ [ s , x ≔ u ]
    red₂ : ∀ {t t′ u} →
             t ⇢ t′ →
             t ∙ u ⇢ t′ ∙ u
    red₃ : ∀ {s t x} →
             ν x ▶ [ s , x ≔ t ] ⇢ t
    red₄ : ∀ {s t x y} {{_ : x ≢ y}} →
             ν x ▶ [ s , y ≔ t ] ⇢ ν x ▶ s
    red₅ : ∀ {x} →
             ν x ▶ [] ⇢ ν x
    red₆ : ∀ {s s′ x} →
             s ⇢⋆ s′ →
             x ▶ s ⇢ x ▶ s′
    red₇ : ∀ {s t u} →
             (t ∙ u) ▶ s ⇢ (t ▶ s) ∙ (u ▶ s)
    red₈ : ∀ {s s′ t} →
             (t ▶ s) ▶ s′ ⇢ t ▶ (s ● s′)

  infix 3 _⇢⋆_
  data _⇢⋆_ : Sub → Sub → Set where
    red⋆₁ : ∀ {s s′ t x} →
              [ s , x ≔ t ] ● s′ ⇢⋆ [ s ● s′ , x ≔ t ▶ s′ ]
    red⋆₂ : ∀ {s s′ s″} →
              (s ● s′) ● s″ ⇢⋆ s ● (s′ ● s″)
    red⋆₃ : ∀ {s} →
              [] ● s ⇢⋆ s

infix 3 _⇒_
data _⇒_ : Tm → Tm → Set where
  eval₁ : ∀ {t} {{_ : WHNF t}} →
            t ⇒ t
  eval₂ : ∀ {t t′ t″} →
            t ⇢ t′ → t′ ⇒ t″ →
            t ⇒ t″

mutual
  infix 3 _⊢_⇣_∷_
  data _⊢_⇣_∷_ : 𝒞 → Tm → Tm → 𝒯 → Set where
    red₁ : ∀ {Γ t t″} →
             Σ Tm (λ t′ → t ⇒ t′ × Γ ⊢ t′ ⇣ₛ t″ ∷ ⋆) →
             Γ ⊢ t ⇣ t″ ∷ ⋆
    -- TODO
  infix 3 _⊢_⇣ₛ_∷_
  data _⊢_⇣ₛ_∷_ : 𝒞 → Tm → Tm → 𝒯 → Set where


-- 7.2. Equivalence between proof trees and terms
-- ----------------------------------------------

-- TODO: Lemma 17.

-- TODO: Theorem 8.

-- TODO: Corollary 3.