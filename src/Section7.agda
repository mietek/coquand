{-# OPTIONS --no-positivity-check #-}

module Section7 where

open import Section6 public


-- 7. Correspondence between proof trees and terms
-- ===============================================
--
-- We define a function that translates the proof trees to the corresponding untyped terms nad
-- likewise for the substitutions, we write `M ⁻` and `γ ⁻ˢ` for these operations.  The definitions
-- are:

mutual
  _⁻ : ∀ {Γ A} → Γ ⊢ A → 𝕋
  (ν x i) ⁻ = ν x
  (ƛ x M) ⁻ = ƛ x (M ⁻)
  (M ∙ N) ⁻ = (M ⁻) ∙ (N ⁻)
  (M ▶ γ) ⁻ = (M ⁻) ▶ (γ ⁻ˢ)

  _⁻ˢ : ∀ {Δ Γ} → Δ ⋙ Γ → 𝕊
  π⟨ c ⟩ ⁻ˢ        = []
  (γ ● γ′) ⁻ˢ      = (γ ⁻ˢ) ● (γ′ ⁻ˢ)
  [ γ , x ≔ M ] ⁻ˢ = [ γ ⁻ˢ , x ≔ M ⁻ ]

-- It is easy to prove that the translation of a proof tree is well-typed:

-- Lemma 12.
mutual
  lem₁₂ : ∀ {Γ A} → (M : Γ ⊢ A) → Γ ⊢ M ⁻ ∷ A
  lem₁₂ (ν x i) = ν x i
  lem₁₂ (ƛ x M) = ƛ x (lem₁₂ M)
  lem₁₂ (M ∙ N) = lem₁₂ M ∙ lem₁₂ N
  lem₁₂ (M ▶ γ) = lem₁₂ M ▶ lem₁₂ₛ γ

  lem₁₂ₛ : ∀ {Γ Γ′} → (γ : Γ′ ⋙ Γ) → Γ′ ⋙ γ ⁻ˢ ∷ Γ
  lem₁₂ₛ π⟨ c ⟩        = ↑⟨ c ⟩ refl⋙∷
  lem₁₂ₛ (γ ● γ′)      = lem₁₂ₛ γ ● lem₁₂ₛ γ′
  lem₁₂ₛ [ γ , x ≔ M ] = [ lem₁₂ₛ γ , x ≔ lem₁₂ M ]

-- In general, we may have `M ⁻ ≡ N ⁻` but `M` different from `N`.  Take for example
-- `(λ(y : B ⊃ B).z) ∙ λ(x : B).x : [ z : A ] ⊢ A` and `(λ(y : C ⊃ C).z ∙ λ(x : C).x : [ z : A ] ⊢ A`
-- which are both
-- translated into `(λ y.z) ∙ λ x.x`.  This shows that a given term can be decorated into different
-- proof trees.
--
-- We define a relation between terms and their possible decorations (and likewise for the
-- substitutions) as an inductively defined set.  (…)
--
-- The introduction rules are:  (…)

mutual
  infix 3 _𝒟_
  data _𝒟_ : ∀ {Γ A} → 𝕋 → Γ ⊢ A → Set where
    ν    : ∀ {Γ A} →
             (x : Name) (i : Γ ∋ x ∷ A) →
             ν x 𝒟 ν x i
    _∙_  : ∀ {Γ A B t₁ t₂} {M : Γ ⊢ A ⊃ B} {N : Γ ⊢ A} →
             t₁ 𝒟 M → t₂ 𝒟 N →
             t₁ ∙ t₂ 𝒟 M ∙ N
    π⟨_⟩ : ∀ {Γ Δ A t} {M : Δ ⊢ A} →
             (c : Γ ⊇ Δ) → t 𝒟 M →
             t 𝒟 M ▶ π⟨ c ⟩
    _▶_  : ∀ {Γ Δ A s t} {M : Δ ⊢ A} {γ : Γ ⋙ Δ} →
             t 𝒟 M → s 𝒟ₛ γ →
             t ▶ s 𝒟 M ▶ γ
    ƛ    : ∀ {Γ A B t} →
             (x : Name) {{_ : T (fresh x Γ)}} {M : [ Γ , x ∷ A ] ⊢ B} → t 𝒟 M →
             ƛ x t 𝒟 ƛ x M

  infix 3 _𝒟ₛ_
  data _𝒟ₛ_ : ∀ {Γ Δ} → 𝕊 → Γ ⋙ Δ → Set where
    π⟨_⟩    : ∀ {Γ Δ} →
                (c : Γ ⊇ Δ) →
                [] 𝒟ₛ π⟨ c ⟩
    [_,_≔_] : ∀ {Γ Δ A s t} {γ : Δ ⋙ Γ} {M : Δ ⊢ A} →
                s 𝒟ₛ γ → (x : Name) {{_ : T (fresh x Γ)}} → t 𝒟 M →
                [ s , x ≔ t ] 𝒟ₛ [ γ , x ≔ M ]
    ↓⟨_⟩𝒟ₛ  : ∀ {Γ Δ Θ s} {γ : Θ ⋙ Γ} →
                (c : Γ ⊇ Δ) → s 𝒟ₛ γ →
                s 𝒟ₛ ↓⟨ c ⟩ γ
    ↑⟨_⟩𝒟ₛ  : ∀ {Γ Δ Θ s} {γ : Γ ⋙ Δ} →
                (c : Θ ⊇ Γ) → s 𝒟ₛ γ →
                s 𝒟ₛ ↑⟨ c ⟩ γ
    _●_     : ∀ {Γ Δ Θ s₁ s₂} {γ₂ : Γ ⋙ Δ} {γ₁ : Θ ⋙ Γ} →
                s₂ 𝒟ₛ γ₂ → s₁ 𝒟ₛ γ₁ →
                s₂ ● s₁ 𝒟ₛ γ₂ ● γ₁

-- It is straightforward to prove Lemma 13
-- mutually with a corresponding lemma for substitutions.

-- Lemma 13.
mutual
  lem₁₃ : ∀ {Γ A} → (M : Γ ⊢ A) → M ⁻ 𝒟 M
  lem₁₃ (ν x i) = ν x i
  lem₁₃ (ƛ x M) = ƛ x (lem₁₃ M)
  lem₁₃ (M ∙ N) = lem₁₃ M ∙ lem₁₃ N
  lem₁₃ (M ▶ γ) = lem₁₃ M ▶ lem₁₃ₛ γ

  lem₁₃ₛ : ∀ {Γ Γ′} → (γ : Γ′ ⋙ Γ) → γ ⁻ˢ 𝒟ₛ γ
  lem₁₃ₛ π⟨ c ⟩        = π⟨ c ⟩
  lem₁₃ₛ (γ ● γ′)      = lem₁₃ₛ γ ● lem₁₃ₛ γ′
  lem₁₃ₛ [ γ , x ≔ M ] = [ lem₁₃ₛ γ , x ≔ lem₁₃ M ]

-- Using the discussion in Section 3.3 on how to define the monotonicity and projection
-- rules with `π⟨_⟩` we can find a proof tree that corresponds to a well-typed term:

-- Lemma 14.
postulate
  lem₁₄ : ∀ {Γ A t} → Γ ⊢ t ∷ A → Σ (Γ ⊢ A) (λ M → M ⁻ ≡ t)

-- As a direct consequence of this lemma and Lemma 13 we know that every well-typed term
-- has a decoration.

-- Lemma 15.
lem₁₅ : ∀ {Γ A t} → Γ ⊢ t ∷ A → Σ (Γ ⊢ A) (λ M → t 𝒟 M)
lem₁₅ D = case lem₁₄ D of λ { (M , refl) → M , lem₁₃ M }

-- As a consequence of this lemma we can now define the semantics of a well-typed term in
-- a Kripke model as the semantics of the decorated term.  In the remaining text, however, we
-- study only the correspondence between terms and proof trees since the translation to the
-- semantics is direct.
--
-- TODO: What to do about the above paragraph?
--
-- As we mentioned above a well-typed term may be decorated to several proof trees.  We
-- can however prove that if two proof trees are in η-normal form and they are decorations of
-- the same term, then the two proof trees are convertible.  We prove Lemma 16
-- together with two corresponding lemmas for proof trees in applicative normal form:

-- Lemma 16.
mutual
  postulate
    lem₁₆ : ∀ {Γ A t} {M M′ : Γ ⊢ A} {{_ : enf M}} {{_ : enf M′}} →
              t 𝒟 M → t 𝒟 M′ →
              M ≡ M′

  postulate
    lem₁₆′ : ∀ {Γ A A′ t} {M : Γ ⊢ A} {N : Γ ⊢ A′} {{_ : anf M}} {{_ : anf N}} →
               t 𝒟 M → t 𝒟 N →
               A ≡ A′

-- TODO: Uh oh. Heterogeneous equality?
-- postulate
--   lem₁₆″ : ∀ {Γ A A′ t} {M : Γ ⊢ A} {M′ : Γ ⊢ A′} {{_ : anf M}} {{_ : anf M′}} →
--              t 𝒟 M → t 𝒟 M′ →
--              M ≡ M′

  postulate
    lem₁₆″ : ∀ {Γ A t} {M M′ : Γ ⊢ A} {{_ : anf M}} {{_ : anf M′}} →
               t 𝒟 M → t 𝒟 M′ →
               M ≡ M′

-- As a consequence we get that if `nf M ⁻` and `nf N ⁻` are the same, then `M ≅ N`.

-- Corollary 2.
postulate
  cor₂ : ∀ {Γ A} → (M M′ : Γ ⊢ A) → nf M ⁻ ≡ nf M′ ⁻ → M ≅ M′

-- Proof: By Lemma 16 and Theorem 7 we get `nf N ≡ nf M` and by Theorem 5 we get `M ≅ N`.


-- 7.1. Reduction
-- --------------
--
-- We mutually inductively define when a term is in weak head normal form (abbreviated
-- `whnf`) and in weak head applicative normal form (abbreviated `whanf`) by:

mutual
  data whnf : 𝕋 → Set where
    ƛ : ∀ {t} →
          (x : Name) → whnf t →
          whnf (ƛ x t)
    α : ∀ {t} → whanf t →
          whnf t

  data whanf : 𝕋 → Set where
    ν   : (x : Name) →
          whanf (ν x)
    _∙_ : ∀ {t u} →
          whanf t → whnf u →
          whanf (t ∙ u)

-- We inductively define a deterministic untyped one-step reduction on terms and
-- substitutions:  (…)

mutual
  infix 3 _⟶_
  data _⟶_ : 𝕋 → 𝕋 → Set where
    red₁ : ∀ {a s t x} →
             (ƛ x t ▶ s) ∙ a ⟶ t ▶ [ s , x ≔ a ]
    red₂ : ∀ {t t₁ t₂} →
             t₁ ⟶ t₂ →
             t₁ ∙ t ⟶ t₂ ∙ t
    red₃ : ∀ {s t x} →
             ν x ▶ [ s , x ≔ t ] ⟶ t
    red₄ : ∀ {s t x y} {{_ : x ≢ y}} →
             ν x ▶ [ s , y ≔ t ] ⟶ ν x ▶ s
    red₅ : ∀ {x} →
             ν x ▶ [] ⟶ ν x
    red₆ : ∀ {s₁ s₂ x} →
             s₁ ⟶ₛ s₂ →
             x ▶ s₁ ⟶ x ▶ s₂
    red₇ : ∀ {s t₁ t₂} →
             (t₁ ∙ t₂) ▶ s ⟶ (t₁ ▶ s) ∙ (t₂ ▶ s)
    red₈ : ∀ {s₁ s₂ t} →
             (t ▶ s₁) ▶ s₂ ⟶ t ▶ (s₁ ● s₂)

  infix 3 _⟶ₛ_
  data _⟶ₛ_ : 𝕊 → 𝕊 → Set where
    red₁ₛ : ∀ {s₀ s₁ t x} →
              [ s₀ , x ≔ t ] ● s₁ ⟶ₛ [ s₀ ● s₁ , x ≔ t ▶ s₁ ]
    red₂ₛ : ∀ {s₁ s₂ s₃} →
              (s₁ ● s₂) ● s₃ ⟶ₛ s₁ ● (s₂ ● s₃)
    red₃ₛ : ∀ {s} →
              [] ● s ⟶ₛ s

-- The untyped evaluation to `whnf`, `_⟹_`, is inductively defined by:

infix 3 _⟹_
data _⟹_ : 𝕋 → 𝕋 → Set where
  eval₁ : ∀ {t} {{_ : whnf t}} →
            t ⟹ t
  eval₂ : ∀ {t₁ t₂ t₃} →
            t₁ ⟶ t₂ → t₂ ⟹ t₃ →
            t₁ ⟹ t₃

-- It is easy to see that this relation is deterministic.
--
-- TODO: What to do about the above paragraph?
--
-- In order to define a deterministic reduction that gives a term on long η-normal form
-- we need to use its type.  We define this typed reduction, `_⊢_↓_∷_`, simultaneously with `_⊢_↓ₛ_∷_` which
-- η-expands the arguments in an application on `whnf`:

mutual
  infix 3 _⊢_↓_∷_
  data _⊢_↓_∷_ : 𝒞 → 𝕋 → 𝕋 → 𝒯 → Set where
    red₁ : ∀ {Γ t₀ t₂} →
             Σ 𝕋 (λ t₁ → t₀ ⟹ t₁ × Γ ⊢ t₁ ↓ₛ t₂ ∷ •) →
             Γ ⊢ t₀ ↓ t₂ ∷ •
    red₂ : ∀ {Γ A B t₁ t₂} →
             let z , φ = gensym Γ in
             let instance _ = φ in
             [ Γ , z ∷ A ] ⊢ t₁ ∙ ν z ↓ t₂ ∷ B →
             Γ ⊢ t₁ ↓ ƛ z t₂ ∷ A ⊃ B

  infix 3 _⊢_↓ₛ_∷_
  data _⊢_↓ₛ_∷_ : 𝒞 → 𝕋 → 𝕋 → 𝒯 → Set where
    red₁ₛ : ∀ {Γ A x} →
              Γ ∋ x ∷ A →
              Γ ⊢ ν x ↓ₛ ν x ∷ A
    red₂ₛ : ∀ {Γ B t₁ t₂ t₁′ t₂′} →
              Σ 𝒯 (λ A → Γ ⊢ t₁ ↓ₛ t₁′ ∷ A ⊃ B × Γ ⊢ t₂ ↓ t₂′ ∷ A) →
              Γ ⊢ t₁ ∙ t₂ ↓ₛ t₁′ ∙ t₂′ ∷ B

-- Finally we define `Γ ⊢ t ⇓ t′ ∷ A` to hold if `Γ ⊢ t [] ↓ t′ ∷ A`.

_⊢_⇓_∷_ : 𝒞 → 𝕋 → 𝕋 → 𝒯 → Set
Γ ⊢ t ⇓ t′ ∷ A = Γ ⊢ t ▶ [] ↓ t′ ∷ A


-- 7.2. Equivalence between proof trees and terms
-- ----------------------------------------------
--
-- We can prove that if `M : Γ ⊢ A`, then `Γ ⊢ M ⁻ ⇓ nf M ⁻ ∷ A`.  This we do by defining a
-- Kripke logical relation, `_ℛ_`.  (…)
--
-- When `f : Γ ⊩ •` we intuitively have that `t ℛ f` holds if `Γ ⊢ t ↓ f ⁻`.
--
-- When `f : Γ ⊩ A ⊃ B`, then `t ℛ f` holds if for all `t′` and `a : Γ ⊩ A` such that `t′ ℛ a`, we
-- have that `t ∙ t′ ℛ f ⟦∙⟧ a`.

infix 3 _ℛ_
data _ℛ_ : ∀ {Γ A} → 𝕋 → Γ ⊩ A → Set where
  𝓇• : ∀ {Δ} →
         (t : 𝕋) (f : Δ ⊩ •) →
         (∀ {Γ} →
            (c : Γ ⊇ Δ) (t′ : 𝕋) → t′ 𝒟 f ⟦g⟧⟨ c ⟩ →
            Γ ⊢ t ↓ t′ ∷ •) →
         t ℛ f
  𝓇⊃ : ∀ {Δ A B} →
         (t : 𝕋) (f : Δ ⊩ A ⊃ B) →
         (∀ {Γ} →
           (c : Γ ⊇ Δ) (a : Γ ⊩ A) (t′ : 𝕋) → Γ ⊢ t′ ∷ A → t′ ℛ a →
           t ∙ t′ ℛ f ⟦∙⟧⟨ c ⟩ a) →
         t ℛ f

-- For the substitutions we define correspondingly:

infix 3 _ℛₛ_
data _ℛₛ_ : ∀ {Γ Δ} → 𝕊 → Γ ⊩⋆ Δ → Set where
  𝓇ₛ[] : ∀ {Δ s} →
           Δ ⋙ s ∷ [] →
           s ℛₛ ([] {w = Δ})
  -- NOTE: Mistake in paper?  Changed `v : Δ ⊩ A` to `a : Γ ⊩ A`.
  rₛ≔  : ∀ {Γ Δ A s x} {{_ : T (fresh x Γ)}} {{_ : T (fresh x Δ)}} →
           Δ ⋙ s ∷ [ Γ , x ∷ A ] → (ρ : Γ ⊩⋆ Δ) (a : Γ ⊩ A) → s ℛₛ ρ → ν x ▶ s ℛ a →
           s ℛₛ [ ρ , x ≔ a ]

-- The following lemmas are straightforward to prove:

postulate
  aux₇₂₁ : ∀ {Γ A t₁ t₂} →
             (a : Γ ⊩ A) → t₁ ℛ a → t₂ ⟶ t₁ →
             t₂ ℛ a

postulate
  aux₇₂₂ : ∀ {Γ Δ s₁ s₂} →
             (ρ : Γ ⊩⋆ Δ) → Δ ⋙ s₁ ∷ Γ → s₁ ⟶ₛ s₂ → s₂ ℛₛ ρ →
             s₁ ℛₛ ρ

-- NOTE: Mistake in paper?  Changed `Occur(x, A, Γ)` to `Δ ∋ x ∷ A`.
postulate
  aux₇₂₃ : ∀ {Γ Δ A s x} →
             (ρ : Γ ⊩⋆ Δ) (i : Δ ∋ x ∷ A) → Δ ⋙ s ∷ Γ →
             ν x ▶ s ℛ lookup ρ i

postulate
  aux₇₂₄⟨_⟩ : ∀ {Γ Δ A t} →
                (c : Γ ⊇ Δ) (a : Δ ⊩ A) → t ℛ a →
                t ℛ ↑⟨ c ⟩ a

-- NOTE: Mistake in paper?  Changed `ρ ∈ Γ ⊩ Δ` to `ρ : Δ ⊩⋆ Γ`.
postulate
  aux₇₂₅⟨_⟩ : ∀ {Γ Δ Θ s} →
                (c : Θ ⊇ Δ) → Δ ⋙ s ∷ Γ → (ρ : Δ ⊩⋆ Γ) → s ℛₛ ρ →
                s ℛₛ ↑⟨ c ⟩ ρ

-- NOTE: Mistake in paper?  Changed `ρ ∈ Γ ⊩ Δ` to `ρ : Δ ⊩⋆ Γ`.
postulate
  aux₇₂₆⟨_⟩ : ∀ {Γ Δ Θ s} →
                (c : Γ ⊇ Θ) → Δ ⋙ s ∷ Γ → (ρ : Δ ⊩⋆ Γ) → s ℛₛ ρ →
                s ℛₛ ↓⟨ c ⟩ ρ

postulate
  aux₇₂₇ : ∀ {Γ Δ A s t x} →
             Γ ⊢ t ∷ A → Γ ⋙ s ∷ Δ → (ρ : Γ ⊩⋆ Δ) → s ℛₛ ρ →
             [ s , x ≔ t ] ℛₛ ρ

-- Using these lemmas we can prove by mutual induction on the proof tree of terms and
-- substitutions that:

-- NOTE: Mistake in paper?  Changed `ρ ∈ Γ ⊩ Δ` to `ρ : Δ ⊩⋆ Γ`.
postulate
  aux₇₂₈ : ∀ {Γ Δ A s t} →
             (M : Γ ⊢ A) (ρ : Δ ⊩⋆ Γ) → Δ ⋙ s ∷ Γ → t 𝒟 M → s ℛₛ ρ →
             t ▶ s ℛ ⟦ M ⟧ ρ

postulate
  aux₇₂₉ : ∀ {Γ Δ Θ s₁ s₂} →
             (γ : Γ ⋙ Θ) (ρ : Δ ⊩⋆ Γ) → Δ ⋙ s₂ ∷ Γ → s₁ 𝒟ₛ γ → s₂ ℛₛ ρ →
             s₂ ● s₁ ℛₛ ⟦ γ ⟧ₛ ρ

-- We also show, intuitively, that if `t ℛ a`, `a : Γ ⊩ A`, then `Γ ⊢ t ↓ reify a ⁻ ∷ A`
-- together with a corresponding lemma for `val`:

-- Lemma 17.
mutual
  postulate
    lem₁₇ : ∀ {Γ A t₀ t₁} →
              Γ ⊢ t₀ ∷ A → (a : Γ ⊩ A) → t₀ ℛ a → t₁ 𝒟 reify a →
              Γ ⊢ t₀ ↓ t₁ ∷ A

  -- NOTE: Mistake in paper?  Changed `t ℛ val(f)` to `t₀ ℛ val f`.
  postulate
    aux₇₂₁₀ : ∀ {Γ A t₀} →
                Γ ⊢ t₀ ∷ A → whanf t₀ →
                (f : ∀ {Δ} → (c : Δ ⊇ Γ) → Δ ⊢ A) →
                (∀ {Δ} → (c : Δ ⊇ Γ) → Δ ⊢ t₀ ↓ₛ f c ⁻ ∷ A) →
                t₀ ℛ val f

-- The proof that the translation of proof trees reduces to the translation of its normal form
-- follows directly:

-- Theorem 8.
postulate
  thm₈ : ∀ {Γ A t} →
           (M : Γ ⊢ A) → t 𝒟 M →
           Γ ⊢ t ⇓ nf M ⁻ ∷ A

-- As a consequence we get that if two proof trees are decorations of the same term, then they
-- are convertible with each other:

-- Corollary 3.
postulate
  cor₃ : ∀ {Γ A t} →
           (M N : Γ ⊢ A) → t 𝒟 M → t 𝒟 N →
           M ≅ N

-- Proof: By Theorem 8 we get that `Γ ⊢ t ⇓ nf M ⁻ ∷ A` and `Γ ⊢ t ⇓ nf N ⁻ ∷ A`.  Since
-- the reduction is deterministic we get `nf M ⁻ ≡ nf N ⁻` and by Corollary 2 we get that
-- `M ≅ N`.
