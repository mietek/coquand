module Section6 where

open import Section5 public


-- 6. Application to terms
-- =======================
--
-- In practice we may not want to work with proof trees but rather well-typed terms.  As an
-- application of the results above we show how to give semantics to a formulation of Martin-
-- Löf’s substitution calculus [13, 20] in the simply typed setting.  In this calculus we have a
-- set of untyped terms, `𝕋`, and we define when a term in `𝕋` is well-typed and when two terms
-- of a given type are convertible with each other.
--
-- In order to give semantics to untyped terms, we first define an erasure function that
-- translates a proof tree `M` to an untyped term, denoted `M ⁻`.  The main theorem is then to prove
-- that if two proof trees `M, N` erase to the same term, `M ⁻ ≡ N ⁻`, then `M ≅ N`; it follows that
-- `M` and `N` have the same semantics.  For this we first prove that `nf M ⁻ ≡ nf N ⁻` implies
-- `M ≅ N`.  We also define a reduction on the untyped terms `Γ ⊢ t₁ ⇓ t₂ ∷ A` that is deterministic
-- (i.e., if `Γ ⊢ t ⇓ t₁ ∷ A` and `Γ ⊢ t ⇓ t₂ ∷ A`, then `t₁ ≡ t₂`) such that `Γ ⊢ M ⁻ ⇓ nf M ⁻ ∷ A`.
-- We then prove that if a proof tree `M` erases to a well-typed term `t`, then `t ⇓ nf M ⁻`.  Now,
-- if two proof trees `M` and `N` erase to the same well-typed term `t`, then `t ⇓ nf M ⁻` and
-- `t ⇓ nf N ⁻`.  Since the reduction is deterministic we have that `nf M ⁻` and `nf N ⁻` are the
-- same, and hence `M ≅ N`.  The idea of this proof comes from Streicher [19] (chapter IV).


-- 6.1. Definition of terms
-- ------------------------
--
-- We mutually define the set of terms, `𝕋 : Set`, and substitutions, `𝕊 : Set`.  (…)

mutual
  data 𝕋 : Set where
    ν   : Name → 𝕋
    ƛ   : Name → 𝕋 → 𝕋
    _∙_ : 𝕋 → 𝕋 → 𝕋
    _▶_ : 𝕋 → 𝕊 → 𝕋

  data 𝕊 : Set where
    []      : 𝕊
    [_,_≔_] : 𝕊 → Name → 𝕋 → 𝕊
    _●_     : 𝕊 → 𝕊 → 𝕊


-- 6.2. Typing rules
-- -----------------
--
-- We give the typing rules for terms and substitutions mutually inductively.  (…)

mutual
  infix 3 _⊢_∷_
  data _⊢_∷_ : 𝒞 → 𝕋 → 𝒯 → Set where
    ↑⟨_⟩⊢∷ : ∀ {Γ Δ A t} →
                Γ ⊇ Δ → Δ ⊢ t ∷ A →
                Γ ⊢ t ∷ A
    ν       : ∀ {Γ A} →
                (x : Name) → Γ ∋ x ∷ A →
                Γ ⊢ ν x ∷ A
    ƛ       : ∀ {Γ A B t} →
                (x : Name) {{_ : T (fresh x Γ)}} → [ Γ , x ∷ A ] ⊢ t ∷ B →
                Γ ⊢ ƛ x t ∷ A ⊃ B
    _∙_     : ∀ {Γ A B t₁ t₂} →
                Γ ⊢ t₁ ∷ A ⊃ B → Γ ⊢ t₂ ∷ A →
                Γ ⊢ t₁ ∙ t₂ ∷ B
    _▶_     : ∀ {Γ Δ A s t} →
                Δ ⊢ t ∷ A → Γ ⋙ s ∷ Δ →
                Γ ⊢ t ▶ s ∷ A

  infix 3 _⋙_∷_
  data _⋙_∷_ : 𝒞 → 𝕊 → 𝒞 → Set where
    ↑⟨_⟩⋙∷ : ∀ {Γ Δ Θ s} →
                Θ ⊇ Γ → Γ ⋙ s ∷ Δ →
                Θ ⋙ s ∷ Δ
    ↓⟨_⟩⋙∷ : ∀ {Γ Δ Θ s} →
                Δ ⊇ Θ → Γ ⋙ s ∷ Δ →
                Γ ⋙ s ∷ Θ
    refl⋙∷ : ∀ {Γ} →
                Γ ⋙ [] ∷ Γ
    [_,_≔_] : ∀ {Γ Δ A s t} →
                Γ ⋙ s ∷ Δ → (x : Name) {{_ : T (fresh x Δ)}} → Γ ⊢ t ∷ A →
                Γ ⋙ [ s , x ≔ t ] ∷ [ Δ , x ∷ A ]
    _●_     : ∀ {Γ Δ Θ s₁ s₂} →
                Δ ⋙ s₂ ∷ Θ → Γ ⋙ s₁ ∷ Δ →
                Γ ⋙ s₂ ● s₁ ∷ Θ

module _ where
  instance
    raise⊢∷ : ∀ {A t} → Raiseable (_⊢ t ∷ A)
    raise⊢∷ = record { ↑⟨_⟩ = ↑⟨_⟩⊢∷ }

    raise⋙∷ : ∀ {Γ s} → Raiseable (_⋙ s ∷ Γ)
    raise⋙∷ = record { ↑⟨_⟩ = ↑⟨_⟩⋙∷ }

    lower⋙∷ : ∀ {Δ s} → Lowerable (Δ ⋙ s ∷_)
    lower⋙∷ = record { ↓⟨_⟩ = ↓⟨_⟩⋙∷ }


-- 6.3. Convertibility of terms
-- ----------------------------
--
-- We mutually inductively define when two terms are convertible with each other together
-- with the definition of convertibility between substitutions.  (…)

mutual
  infix 3 _⊢_≊_∷_
  data _⊢_≊_∷_ : 𝒞 → 𝕋 → 𝕋 → 𝒯 → Set where
    refl≊  : ∀ {Γ A t} →
               Γ ⊢ t ≊ t ∷ A
    sym≊   : ∀ {Γ A t t′} →
               Γ ⊢ t ≊ t′ ∷ A →
               Γ ⊢ t′ ≊ t ∷ A
    trans≊ : ∀ {Γ A t t′ t″} →
               Γ ⊢ t ≊ t′ ∷ A → Γ ⊢ t′ ≊ t″ ∷ A →
               Γ ⊢ t ≊ t″ ∷ A

    congƛ≊ : ∀ {Γ A B t t′ x} {{_ : T (fresh x Γ)}} →
               [ Γ , x ∷ A ] ⊢ t ≊ t′ ∷ B →
               Γ ⊢ ƛ x t ≊ ƛ x t′ ∷ A ⊃ B
    cong∙≊ : ∀ {Γ A B t t′ u u′} →
               Γ ⊢ t ≊ t′ ∷ A ⊃ B → Γ ⊢ u ≊ u′ ∷ A →
               Γ ⊢ t ∙ u ≊ t′ ∙ u′ ∷ B
    cong▶≊ : ∀ {Γ Δ A t t′ s s′} →
               Γ ⊢ t ≊ t′ ∷ A → Δ ⋙ s ≊ₛ s′ ∷ Γ →
               Γ ⊢ t ▶ s ≊ t′ ▶ s′ ∷ A

    conv₁≊ : ∀ {Γ A t} →
               Γ ⊢ t ∷ A →
               Γ ⊢ t ≊ t ∷ A
    conv₂≊ : ∀ {Γ Δ A B s t₁ t₂ x} {{_ : T (fresh x Δ)}} →
               Γ ⋙ s ∷ Δ → [ Δ , x ∷ A ] ⊢ t₁ ∷ B → Γ ⊢ t₂ ∷ A →
               Γ ⊢ (ƛ x t₁ ▶ s) ∙ t₂ ≊ t₁ ▶ [ s , x ≔ t₂ ] ∷ B
    conv₃≊ : ∀ {Γ A B t x} {{_ : T (fresh x Γ)}} →
               Γ ⊢ t ∷ A ⊃ B →
               Γ ⊢ t ≊ ƛ x (t ∙ ν x) ∷ A ⊃ B
    conv₄≊ : ∀ {Γ Δ A t₁ t₂} →
               Γ ⊇ Δ → Δ ⊢ t₁ ≊ t₂ ∷ A →
               Γ ⊢ t₁ ≊ t₂ ∷ A
    conv₅≊ : ∀ {Γ Δ A s t x} {{_ : T (fresh x Δ)}} →
               Γ ⋙ s ∷ Δ → Γ ⊢ t ∷ A →
               Γ ⊢ ν x ▶ [ s , x ≔ t ] ≊ t ∷ A
    conv₆≊ : ∀ {Γ A t} →
               Γ ⊢ t ∷ A →
               Γ ⊢ t ▶ [] ≊ t ∷ A
    conv₇≊ : ∀ {Γ Δ A B s t₁ t₂} →
               Δ ⊢ t₁ ∷ A ⊃ B → Δ ⊢ t₂ ∷ A → Γ ⋙ s ∷ Δ →
               Γ ⊢ (t₁ ∙ t₂) ▶ s ≊ (t₁ ▶ s) ∙ (t₂ ▶ s) ∷ B
    conv₈≊ : ∀ {Γ₁ Γ₂ Γ₃ A s₁ s₂ t} →
               Γ₂ ⋙ s₁ ∷ Γ₃ → Γ₁ ⋙ s₂ ∷ Γ₂ → Γ₃ ⊢ t ∷ A →
               Γ₁ ⊢ (t ▶ s₁) ▶ s₂ ≊ t ▶ (s₁ ● s₂) ∷ A

  data _⋙_≊ₛ_∷_ : 𝒞 → 𝕊 → 𝕊 → 𝒞 → Set where
    refl≊ₛ  : ∀ {Γ Δ s} →
                Δ ⋙ s ≊ₛ s ∷ Γ
    sym≊ₛ   : ∀ {Γ Δ s s′} →
                Δ ⋙ s ≊ₛ s′ ∷ Γ →
                Δ ⋙ s′ ≊ₛ s ∷ Γ
    trans≊ₛ : ∀ {Γ Δ s s′ s″} →
                Δ ⋙ s ≊ₛ s′ ∷ Γ → Δ ⋙ s′ ≊ₛ s″ ∷ Γ →
                Δ ⋙ s ≊ₛ s″ ∷ Γ

    cong≔≊ₛ : ∀ {Γ Δ A s s′ t t′ x} {{_ : T (fresh x Δ)}} →
                Γ ⋙ s ≊ₛ s′ ∷ Δ → Γ ⊢ t ≊ t′ ∷ A →
                Γ ⋙ [ s , x ≔ t ] ≊ₛ [ s′ , x ≔ t′ ] ∷ [ Δ , x ∷ A ]
    cong●≊ₛ : ∀ {Γ Δ Θ s₁ s₁′ s₂ s₂′} →
                Δ ⋙ s₂ ≊ₛ s₂′ ∷ Θ → Γ ⋙ s₁ ≊ₛ s₁′ ∷ Δ →
                Γ ⋙ s₂ ● s₁ ≊ₛ s₂′ ● s₁′ ∷ Θ

    conv₁≊ₛ : ∀ {Γ₁ Γ₂ Δ s₁ s₂} →
                Γ₁ ⊇ Γ₂ → Γ₂ ⋙ s₁ ≊ₛ s₂ ∷ Δ →
                Γ₁ ⋙ s₁ ≊ₛ s₂ ∷ Δ
    conv₂≊ₛ : ∀ {Γ Δ₁ Δ₂ s₁ s₂} →
                Δ₁ ⊇ Δ₂ → Γ ⋙ s₁ ≊ₛ s₂ ∷ Δ₁ →
                Γ ⋙ s₁ ≊ₛ s₂ ∷ Δ₂
    conv₃≊ₛ : ∀ {Γ Δ s} →
                Γ ⋙ s ∷ Δ →
                Γ ⋙ s ● [] ≊ₛ s ∷ Δ
    conv₄≊ₛ : ∀ {Γ₁ Γ₂ Γ₃ Δ s₁ s₂ s₃} →
                Γ₁ ⋙ s₃ ∷ Γ₂ → Γ₂ ⋙ s₂ ∷ Γ₃ → Γ₃ ⋙ s₁ ∷ Δ →
                Γ₃ ⋙ (s₁ ● s₂) ● s₃ ≊ₛ s₁ ● (s₂ ● s₃) ∷ Δ
    conv₅≊ₛ : ∀ {Γ₁ Γ₂ Δ A s₁ s₂ t x} {{_ : T (fresh x Δ)}} →
                Γ₁ ⋙ s₂ ∷ Γ₂ → Γ₂ ⋙ s₁ ∷ Δ → Γ₂ ⊢ t ∷ A →
                Γ₁ ⋙ [ s₁ , x ≔ t ] ● s₂ ≊ₛ [ s₁ ● s₂ , x ≔ t ▶ s₂ ] ∷ [ Δ , x ∷ A ]
    conv₆≊ₛ : ∀ {Γ s} →
                Γ ⋙ s ∷ [] →
                Γ ⋙ s ≊ₛ [] ∷ []
    conv₇≊ₛ : ∀ {Γ Δ A s x} {{_ : T (fresh x Δ)}} →
                Γ ⋙ s ∷ [ Δ , x ∷ A ] →
                Γ ⋙ s ≊ₛ [ s , x ≔ ν x ▶ s ] ∷ [ Δ , x ∷ A ]
    conv₈≊ₛ : ∀ {Γ Δ A s t x} {{_ : T (fresh x Δ)}} →
                Γ ⋙ s ∷ Δ → Δ ⊢ t ∷ A →
                Γ ⋙ [ s , x ≔ t ] ≊ₛ s ∷ Δ
    conv₉≊ₛ : ∀ {Γ Δ s} →
                Γ ⋙ s ∷ Δ →
                Γ ⋙ [] ● s ≊ₛ s ∷ Δ

-- It is straightforward to prove that if two terms (substitutions) are convertible with each
-- other, then they are also well-typed.

-- TODO: What to do about the above paragraph?
