module Section6 where

open import Section5 public


-- 6. Application to terms
-- =======================

-- 6.1. Definition of terms
-- ------------------------

mutual
  data Tm : Set where
    ν   : Name → Tm
    ƛ   : Name → Tm → Tm
    _∙_ : Tm → Tm → Tm
    _▶_ : Tm → Sub → Tm

  data Sub : Set where
    []      : Sub
    _●_     : Sub → Sub → Sub
    [_,_≔_] : Sub → Name → Tm → Sub


-- 6.2. Typing rules
-- -----------------

mutual
  infix 3 _⊢_∷_
  data _⊢_∷_ : 𝒞 → Tm → 𝒯 → Set where
    ν        : ∀ {Γ A} →
                 (x : Name) → Γ ∋ x ∷ A →
                 Γ ⊢ ν x ∷ A
    ƛ        : ∀ {Γ t A B} →
                 (x : Name) {{_ : T (fresh x Γ)}} → [ Γ , x ∷ A ] ⊢ t ∷ B →
                 Γ ⊢ ƛ x t ∷ A ⊃ B
    _∙_      : ∀ {Γ t u A B} →
                 Γ ⊢ t ∷ A ⊃ B → Γ ⊢ u ∷ A →
                 Γ ⊢ t ∙ u ∷ B
    _▶_      : ∀ {Γ Γ′ s t A} →
                 Γ ⊢ t ∷ A → Γ′ ⋙ s ∷ Γ →
                 Γ′ ⊢ t ▶ s ∷ A
    ⊢∷-↑⟨_⟩ : ∀ {Γ Γ′ t A} →
                 Γ′ ⊇ Γ → Γ ⊢ t ∷ A →
                 Γ′ ⊢ t ∷ A

  infix 3 _⋙_∷_
  data _⋙_∷_ : 𝒞 → Sub → 𝒞 → Set where
    refl      : ∀ {Γ} →
                  Γ ⋙ [] ∷ Γ
    _●_       : ∀ {Γ Γ′ Γ″ s s′} →
                  Γ′ ⋙ s ∷ Γ → Γ″ ⋙ s′ ∷ Γ′ →
                  Γ″ ⋙ s ● s′ ∷ Γ
    [_,_≔_]   : ∀ {Γ Γ′ s t A} →
                  Γ′ ⋙ s ∷ Γ → (x : Name) {{_ : T (fresh x Γ)}} → Γ′ ⊢ t ∷ A →
                  Γ′ ⋙ [ s , x ≔ t ] ∷ [ Γ , x ∷ A ]
    ⋙∷-↑⟨_⟩ : ∀ {Γ Γ′ Δ s} →
                  Γ′ ⊇ Γ → Γ ⋙ s ∷ Δ →
                  Γ′ ⋙ s ∷ Δ
    ⋙∷-↓⟨_⟩ : ∀ {Γ Γ′ Δ s} →
                  Γ′ ⊇ Γ → Δ ⋙ s ∷ Γ′ →
                  Δ ⋙ s ∷ Γ

instance
  raise-⊢∷ : ∀ {t A} → Raiseable (_⊢ t ∷ A)
  raise-⊢∷ = record { ↑⟨_⟩ = ⊢∷-↑⟨_⟩ }

  raise-⋙∷ : ∀ {Γ s} → Raiseable (_⋙ s ∷ Γ)
  raise-⋙∷ = record { ↑⟨_⟩ = ⋙∷-↑⟨_⟩ }

  lower-⋙∷ : ∀ {Δ s} → Lowerable (Δ ⋙ s ∷_)
  lower-⋙∷ = record { ↓⟨_⟩ = ⋙∷-↓⟨_⟩ }


-- 6.3. Convertibility of terms
-- ----------------------------

mutual
  infix 3 _⊢_≊_∷_
  data _⊢_≊_∷_ : 𝒞 → Tm → Tm → 𝒯 → Set where
    ≊-refl  : ∀ {Γ A t} →
                Γ ⊢ t ≊ t ∷ A
    ≊-sym   : ∀ {Γ A t t′} →
                Γ ⊢ t ≊ t′ ∷ A →
                Γ ⊢ t′ ≊ t ∷ A
    ≊-trans : ∀ {Γ A t t′ t″} →
                Γ ⊢ t ≊ t′ ∷ A → Γ ⊢ t′ ≊ t″ ∷ A →
                Γ ⊢ t ≊ t″ ∷ A

    ≊-cong-ƛ : ∀ {Γ A B t t′ x} {{_ : T (fresh x Γ)}} →
                 [ Γ , x ∷ A ] ⊢ t ≊ t′ ∷ B →
                 Γ ⊢ ƛ x t ≊ ƛ x t′ ∷ A ⊃ B
    ≊-cong-∙ : ∀ {Γ A B t t′ u u′} →
                 Γ ⊢ t ≊ t′ ∷ A ⊃ B → Γ ⊢ u ≊ u′ ∷ A →
                 Γ ⊢ t ∙ u ≊ t′ ∙ u′ ∷ B
    ≊-cong-▶ : ∀ {Γ Γ′ A t t′ s s′} →
                 Γ ⊢ t ≊ t′ ∷ A → Γ′ ⋙ s ≊⋆ s′ ∷ Γ →
                 Γ ⊢ t ▶ s ≊ t′ ▶ s′ ∷ A

    ≊-conv₁ : ∀ {Γ A t} →
                Γ ⊢ t ∷ A →
                Γ ⊢ t ≊ t ∷ A
    ≊-conv₂ : ∀ {Γ Γ′ A B s t u x} {{_ : T (fresh x Γ)}} →
                Γ′ ⋙ s ∷ Γ → [ Γ , x ∷ A ] ⊢ t ∷ B → Γ′ ⊢ u ∷ A →
                Γ′ ⊢ (ƛ x t ▶ s) ∙ u ≊ t ▶ [ s , x ≔ u ] ∷ B
    ≊-conv₃ : ∀ {Γ A B t x} {{_ : T (fresh x Γ)}} →
                Γ ⊢ t ∷ A ⊃ B →
                Γ ⊢ t ≊ ƛ x (t ∙ ν x) ∷ A ⊃ B
    ≊-conv₄ : ∀ {Γ Γ′ A t t′} →
                Γ′ ⊇ Γ → Γ ⊢ t ≊ t′ ∷ A →
                Γ′ ⊢ t ≊ t′ ∷ A
    ≊-conv₅ : ∀ {Γ Γ′ A s t x} {{_ : T (fresh x Γ)}} →
                Γ′ ⋙ s ∷ Γ → Γ′ ⊢ t ∷ A →
                Γ′ ⊢ ν x ▶ [ s , x ≔ t ] ≊ t ∷ A
    ≊-conv₆ : ∀ {Γ A t} →
                Γ ⊢ t ∷ A →
                Γ ⊢ t ▶ [] ≊ t ∷ A
    ≊-conv₇ : ∀ {Γ Γ′ A B s t u} →
                Γ ⊢ t ∷ A ⊃ B → Γ ⊢ u ∷ A → Γ′ ⋙ s ∷ Γ →
                Γ′ ⊢ (t ∙ u) ▶ s ≊ (t ▶ s) ∙ (u ▶ s) ∷ B
    ≊-conv₈ : ∀ {Γ Γ′ Γ″ A s s′ t} →
                Γ′ ⋙ s ∷ Γ → Γ″ ⋙ s′ ∷ Γ′ → Γ ⊢ t ∷ A →
                Γ″ ⊢ (t ▶ s) ▶ s′ ≊ t ▶ (s ● s′) ∷ A

  data _⋙_≊⋆_∷_ : 𝒞 → Sub → Sub → 𝒞 → Set where
    ≊⋆-refl  : ∀ {Γ Γ′ s} →
                 Γ′ ⋙ s ≊⋆ s ∷ Γ
    ≊⋆-sym   : ∀ {Γ Γ′ s s′} →
                 Γ′ ⋙ s ≊⋆ s′ ∷ Γ →
                 Γ′ ⋙ s′ ≊⋆ s ∷ Γ
    ≊⋆-trans : ∀ {Γ Γ′ s s′ s″} →
                 Γ′ ⋙ s ≊⋆ s′ ∷ Γ → Γ′ ⋙ s′ ≊⋆ s″ ∷ Γ →
                 Γ′ ⋙ s ≊⋆ s″ ∷ Γ

    -- TODO: cong, conv
