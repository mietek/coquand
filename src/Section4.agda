{-# OPTIONS --no-positivity-check #-}

module Section4 where

open import Section3 public


-- 4. The semantic model
-- =====================
--
-- As we want to deal with full conversion on open terms and the η-rule, we choose to describe
-- the semantics in a Kripke style model [6, 11, 15].  A Kripke model is a set of possible worlds,
-- `𝒲 : Set`, with a partial ordering `⊒ : 𝒲 → 𝒲 → Set`, of extensions of worlds.  We also have
-- a family of ground sets `𝒢 : 𝒲 → Set` over possible worlds which are the interpretation of
-- the base type.  We also need independence of the proof of `_⊒_`, i.e., if `c₁, c₂ : w′ ⊒ w`, then
-- `c₁ ≡ c₂`.  (…)

record Model : Set₁ where
  infix 3 _⊒_
  field
    𝒲     : Set
    _⊒_   : 𝒲 → 𝒲 → Set
    refl⊒ : ∀ {w} → w ⊒ w
    _◇_   : ∀ {w w′ w″} → w′ ⊒ w → w″ ⊒ w′ → w″ ⊒ w
    uniq⊒ : ∀ {w w′} → (c c′ : w′ ⊒ w) → c ≡ c′
    𝒢     : 𝒲 → Set
open Model {{…}} public

module _ {{_ : Model}} where
  trans⊒ : ∀ {w w′ w″} → w″ ⊒ w′ → w′ ⊒ w → w″ ⊒ w
  trans⊒ = flip _◇_

  id◇₁ : ∀ {w w′} → (c : w ⊒ w) (c′ : w′ ⊒ w) → c ◇ c′ ≡ c′
  id◇₁ c c′ = uniq⊒ (c ◇ c′) c′

  id◇₂ : ∀ {w w′} → (c : w′ ⊒ w) (c′ : w′ ⊒ w′) → c ◇ c′ ≡ c
  id◇₂ c c′ = uniq⊒ (c ◇ c′) c

  assoc◇ : ∀ {w w′ w″ w‴} → (c : w′ ⊒ w) (c′ : w″ ⊒ w′) (c″ : w‴ ⊒ w″) →
             c ◇ (c′ ◇ c″) ≡ (c ◇ c′) ◇ c″
  assoc◇ c c′ c″ = uniq⊒ (c ◇ (c′ ◇ c″)) ((c ◇ c′) ◇ c″)

  comp◇ : ∀ {w w′ w″} → (c : w′ ⊒ w) (c′ : w″ ⊒ w′) (c″ : w″ ⊒ w) →
            c ◇ c′ ≡ c″
  comp◇ c c′ c″ = uniq⊒ (c ◇ c′) c″


-- 4.1. Semantic objects
-- ---------------------
--
-- We define the set of semantic objects as usual in Kripke semantics.
--
-- Forcing is written `w ⊩ A`.  For the base type an element in `w ⊩ ⋆` is a family of
-- elements in `𝒢 w′`, `w′ ⊒ w`.  For the type `A ⊃ B` an element in `w ⊩ A ⊃ B` is a family of
-- functions from `w′ ⊩ A` to `w′ ⊩ B`, `w′ ⊒ w`.  (…)

module _ {{_ : Model}} where
  -- TODO: Replace with strictly positive definition
  infix 3 _⊩_
  data _⊩_ : 𝒲 → 𝒯 → Set where
    ⟦𝒢⟧ : ∀ {w} →
            (∀ {w′} → w′ ⊒ w → 𝒢 w′) →
            w ⊩ ⋆
    ⟦ƛ⟧ : ∀ {w A B} →
            (∀ {w′} → w′ ⊒ w → w′ ⊩ A → w′ ⊩ B) →
            w ⊩ A ⊃ B

-- We use the notational convention `⟦𝒢⟧` for the semantics of the ground type and
-- `⟦ƛ⟧` for the semantics of the function type.
--
-- We define the following two elimination rules:

module _ {{_ : Model}} where
  _⟦ℊ⟧⟨_⟩ : ∀ {w w′} → w ⊩ ⋆ → w′ ⊒ w → 𝒢 w′
  (⟦𝒢⟧ f) ⟦ℊ⟧⟨ c ⟩ = f c

  _⟦∙⟧⟨_⟩_ : ∀ {w w′ A B} → w ⊩ A ⊃ B → w′ ⊒ w → w′ ⊩ A → w′ ⊩ B
  (⟦ƛ⟧ f) ⟦∙⟧⟨ c ⟩ v = f c v

-- (…)  The monotonicity function `↑⟨_⟩⊩` lifts a semantic object in one world into a semantic object
-- in a bigger world and is defined by induction on the type.  (…)

module _ {{_ : Model}} where
  ↑⟨_⟩⊩ : ∀ {A w w′} → w′ ⊒ w → w ⊩ A → w′ ⊩ A
  ↑⟨_⟩⊩ {⋆}     c u = ⟦𝒢⟧ (λ c′ → u ⟦ℊ⟧⟨ c ◇ c′ ⟩)
  ↑⟨_⟩⊩ {A ⊃ B} c u = ⟦ƛ⟧ (λ c′ v → u ⟦∙⟧⟨ c ◇ c′ ⟩ v)

  instance
    raise⊩ : ∀ {A} → Raiseable (_⊩ A)
    raise⊩ = record { ↑⟨_⟩ = ↑⟨_⟩⊩ }

-- We also need to define an equality, `Eq`, on semantic objects.  For the soundness of the
-- η-rule we need `u : w ⊩ A ⊃ B` to be equal to `⟦ƛ⟧ (λ c v → u ⟦∙⟧⟨ c ⟫ v)`, which corresponds
-- to η-expansion on the semantic level.  This means that the equality on our model must be
-- extensional and that application and the monotonicity function commutes, i.e., lifting the
-- result of an application up to a bigger world should be equal to first lifting the arguments and
-- then doing the application.  We say that a semantic object is uniform, `𝒰`, if the application and
-- monotonicity functions commute for this object (see Scott [17] for a discussion regarding
-- commutativity).  The predicates `Eq` and `𝒰` are mutually defined.
--
-- They both are defined by induction on the types; this way of defining extensionality is
-- presented by Gandy [10].  Two semantic objects of base type are equal if they are intensionally
-- equal in all bigger worlds and two semantic objects of function type are equal if the
-- application of them to a uniform semantic object in a bigger world is extensionally equal.
--
-- A semantic object of base type is always uniform.  A semantic object of function type is uniform
-- if it sends a uniform semantic object in a bigger world to a uniform semantic object,
-- if it sends two extensionally equal uniform objects in a bigger worlds to extensionally equal
-- semantic objects and if application and monotonicity commute for the semantic object.  (…)

module _ {{_ : Model}} where
  mutual
    Eq : ∀ {A w} → w ⊩ A → w ⊩ A → Set
    Eq {⋆}     {w} u u′ = ∀ {w′} → (c : w′ ⊒ w) →
                            u ⟦ℊ⟧⟨ c ⟩ ≡ u′ ⟦ℊ⟧⟨ c ⟩
    Eq {A ⊃ B} {w} u u′ = ∀ {w′} → (c : w′ ⊒ w) (v : w′ ⊩ A) → 𝒰 v →
                            Eq (u ⟦∙⟧⟨ c ⟩ v) (u′ ⟦∙⟧⟨ c ⟩ v)

    𝒰 : ∀ {A w} → w ⊩ A → Set
    𝒰 {⋆}     {w} u = ⊤
    𝒰 {A ⊃ B} {w} u = (∀ {w′} → (c : w′ ⊒ w) (v : w′ ⊩ A) → 𝒰 v →
                           𝒰 (u ⟦∙⟧⟨ c ⟩ v))
                    × (∀ {w′} → (c : w′ ⊒ w) (v v′ : w′ ⊩ A) → 𝒰 v → 𝒰 v′ → Eq v v′ →
                         Eq (u ⟦∙⟧⟨ c ⟩ v) (u ⟦∙⟧⟨ c ⟩ v′))
                    × (∀ {w′ w″} → (c : w′ ⊒ w) (c′ : w″ ⊒ w′) (c″ : w″ ⊒ w) (v : w′ ⊩ A) → 𝒰 v →
                         Eq (↑⟨ c′ ⟩ (u ⟦∙⟧⟨ c ⟩ v)) (u ⟦∙⟧⟨ c″ ⟩ (↑⟨ c′ ⟩ v)))

-- The equality `Eq` is transitive and symmetric and it is reflexive for uniform objects.  (?)

module _ {{_ : Model}} where
  -- NOTE: Doesn’t need `𝒰 u`!
  reflEq : ∀ {A w} → (s : w ⊩ A) → Eq s s
  reflEq {⋆}     s = λ c      → refl
  reflEq {A ⊃ B} s = λ c t uₜ → reflEq (s ⟦∙⟧⟨ c ⟩ t)

  symEq : ∀ {A w} → (s s′ : w ⊩ A) → Eq s s′ → Eq s′ s
  symEq {⋆}     s s′ eₛ = λ c      → sym (eₛ c)
  symEq {A ⊃ B} s s′ eₛ = λ c t uₜ → symEq (s ⟦∙⟧⟨ c ⟩ t) (s′ ⟦∙⟧⟨ c ⟩ t) (eₛ c t uₜ)

  transEq : ∀ {A w} → (s s′ s″ : w ⊩ A) → Eq s s′ → Eq s′ s″ → Eq s s″
  transEq {⋆}     s s′ s″ eₛ eₛ′ = λ c      → trans (eₛ c) (eₛ′ c)
  transEq {A ⊃ B} s s′ s″ eₛ eₛ′ = λ c t uₜ → transEq (s ⟦∙⟧⟨ c ⟩ t) (s′ ⟦∙⟧⟨ c ⟩ t) (s″ ⟦∙⟧⟨ c ⟩ t)
                                                         (eₛ c t uₜ) (eₛ′ c t uₜ)

  ≡→Eq : ∀ {A w} → (s s′ : w ⊩ A) → s ≡ s′ → Eq s s′
  ≡→Eq s s′ refl = reflEq s

  module EqReasoning where
    infix 1 begin_
    begin_ : ∀ {A w} {s s′ : w ⊩ A} → Eq s s′ → Eq s s′
    begin p = p

    infixr 2 _Eq⟨⟩_
    _Eq⟨⟩_ : ∀ {A w} (s {s′} : w ⊩ A) → Eq s s′ → Eq s s′
    s Eq⟨⟩ p = p

    infixr 2 _Eq⟨_⟩_
    _Eq⟨_⟩_ : ∀ {A w} (s {s′ s″} : w ⊩ A) → Eq s s′ → Eq s′ s″ → Eq s s″
    s Eq⟨ p ⟩ q = transEq s _ _ p q

    infixr 2 _≡⟨⟩_
    _≡⟨⟩_ : ∀ {A w} (s {s′} : w ⊩ A) → Eq s s′ → Eq s s′
    s ≡⟨⟩ p = p

    infixr 2 _≡⟨_⟩_
    _≡⟨_⟩_ : ∀ {A w} (s {s′ s″} : w ⊩ A) → s ≡ s′ → Eq s′ s″ → Eq s s″
    s ≡⟨ p ⟩ q = transEq s _ _ (≡→Eq s _ p) q

    infix 3 _∎
    _∎ : ∀ {A w} (s : w ⊩ A) → Eq s s
    s ∎ = reflEq s

-- Equal uniform values can be substituted in `⟦∙⟧⟨_⟩` and the function `↑⟨_⟩` returns uniform objects
-- for uniform input and equal results for equal input.

module _ {{_ : Model}} where
  Eq-cong-⟦∙⟧ : ∀ {A B w w′} → (s s′ : w ⊩ A ⊃ B) → 𝒰 s → 𝒰 s′ → Eq s s′ →
                  (c : w′ ⊒ w) (t t′ : w′ ⊩ A) → 𝒰 t → 𝒰 t′ → Eq t t′ →
                  Eq (s ⟦∙⟧⟨ c ⟩ t) (s′ ⟦∙⟧⟨ c ⟩ t′)
  Eq-cong-⟦∙⟧ s s′ (xₛ , yₛ , zₛ) (xₛ′ , yₛ′ , zₛ′) eₛ c t t′ uₜ uₜ′ eₜ =
      transEq (s ⟦∙⟧⟨ c ⟩ t) (s ⟦∙⟧⟨ c ⟩ t′) (s′ ⟦∙⟧⟨ c ⟩ t′)
               (yₛ c t t′ uₜ uₜ′ eₜ) (eₛ c t′ uₜ′)

  Eq-cong-↑⟨_⟩ : ∀ {A w w′} → (c : w′ ⊒ w) (s s′ : w ⊩ A) → Eq s s′ →
                   Eq (↑⟨ c ⟩ s) (↑⟨ c ⟩ s′)
  Eq-cong-↑⟨_⟩ {⋆}     c s s′ eₛ c′ = eₛ (c ◇ c′)
  Eq-cong-↑⟨_⟩ {A ⊃ B} c s s′ eₛ c′ = eₛ (c ◇ c′)

  𝒰-cong-↑⟨_⟩ : ∀ {A w w′} → (c : w′ ⊒ w) (s : w ⊩ A) → 𝒰 s →
                  𝒰 (↑⟨ c ⟩ s)
  𝒰-cong-↑⟨_⟩ {⋆}     c s uₛ             = tt
  𝒰-cong-↑⟨_⟩ {A ⊃ B} c s (xₛ , yₛ , zₛ) = (λ c′ t uₜ           → xₛ (c ◇ c′) t uₜ)
                                           , (λ c′ t t′ uₜ uₜ′ eₜ → yₛ (c ◇ c′) t t′ uₜ uₜ′ eₜ)
                                           , (λ c′ c″ c‴ t uₜ     → zₛ (c ◇ c′) c″ (c ◇ c‴) t uₜ)

-- We also need to prove the following properties about `Eq` and `𝒰` which are used in the proofs of
-- soundness and completeness below.

module _ {{_ : Model}} where
  -- NOTE: Doesn’t need `𝒰 u`!
  aux₄₁₁ : ∀ {A w} → (c : w ⊒ w) (s : w ⊩ A) →
             Eq (↑⟨ c ⟩ s) s
  aux₄₁₁ {⋆}     c s = λ c′      → cong (s ⟦ℊ⟧⟨_⟩) (id◇₁ c c′)
  aux₄₁₁ {A ⊃ B} c s = λ c′ t uₜ → ≡→Eq (s ⟦∙⟧⟨ c ◇ c′ ⟩ t)
                                          (s ⟦∙⟧⟨ c′ ⟩ t)
                                      (cong (s ⟦∙⟧⟨_⟩ t)
                                        (id◇₁ c c′))

  -- NOTE: Doesn’t need `𝒰 u`!
  aux₄₁₂ : ∀ {A w w′ w″} → (c : w′ ⊒ w) (c′ : w″ ⊒ w′) (c″ : w″ ⊒ w) (s : w ⊩ A) →
             Eq (↑⟨ c′ ⟩ (↑⟨ c ⟩ s)) (↑⟨ c″ ⟩ s)
  aux₄₁₂ {⋆}     c c′ c″ s = λ c‴      → cong (s ⟦ℊ⟧⟨_⟩)
                                            (trans (assoc◇ c c′ c‴)
                                                   (comp◇ (c ◇ c′) c‴ (c″ ◇ c‴)))
  aux₄₁₂ {A ⊃ B} c c′ c″ s = λ c‴ t uₜ → ≡→Eq (s ⟦∙⟧⟨ c ◇ (c′ ◇ c‴) ⟩ t)
                                                (s ⟦∙⟧⟨ c″ ◇ c‴ ⟩ t)
                                            (cong (s ⟦∙⟧⟨_⟩ t)
                                              (trans (assoc◇ c c′ c‴)
                                                     (comp◇ (c ◇ c′) c‴ (c″ ◇ c‴))))

  -- NOTE: Doesn’t need `𝒰 u` or `𝒰 v`!
  aux₄₁₃ : ∀ {A B w w′} → (c : w′ ⊒ w) (c′ : w′ ⊒ w′) (s : w ⊩ A ⊃ B) (t : w′ ⊩ A) →
             Eq (s ⟦∙⟧⟨ c ⟩ t) (↑⟨ c ⟩ s ⟦∙⟧⟨ c′ ⟩ t)
  aux₄₁₃ c c′ s t = ≡→Eq (s ⟦∙⟧⟨ c ⟩ t)
                          (s ⟦∙⟧⟨ c ◇ c′ ⟩ t)
                      (cong (s ⟦∙⟧⟨_⟩ t)
                        (sym (id◇₂ c c′)))


-- 4.2. Semantic environments
-- --------------------------

module _ {{_ : Model}} where
  infix 3 _⊩⋆_
  data _⊩⋆_ : 𝒲 → 𝒞 → Set where
    []      : ∀ {w} →
                w ⊩⋆ []
    [_,_≔_] : ∀ {Γ A w} →
                w ⊩⋆ Γ → (x : Name) {{_ : T (fresh x Γ)}} → w ⊩ A →
                w ⊩⋆ [ Γ , x ∷ A ]

  lookup : ∀ {Γ A w x} → w ⊩⋆ Γ → Γ ∋ x ∷ A → w ⊩ A
  lookup [ ρ , x ≔ s ] zero    = s
  lookup [ ρ , y ≔ t ] (suc i) = lookup ρ i

  ⊩⋆-↑⟨_⟩ : ∀ {Γ w w′} → w′ ⊒ w → w ⊩⋆ Γ → w′ ⊩⋆ Γ
  ⊩⋆-↑⟨ c ⟩ []            = []
  ⊩⋆-↑⟨ c ⟩ [ ρ , x ≔ s ] = [ ⊩⋆-↑⟨ c ⟩ ρ , x ≔ ↑⟨ c ⟩ s ]

  ⊩⋆-↓⟨_⟩ : ∀ {Γ Δ w} → Δ ⊇ Γ → w ⊩⋆ Δ → w ⊩⋆ Γ
  ⊩⋆-↓⟨ done             ⟩ ρ = []
  ⊩⋆-↓⟨ weak {x = x} c i ⟩ ρ = [ ⊩⋆-↓⟨ c ⟩ ρ , x ≔ lookup ρ i ]

  instance
    raise-⊩⋆ : ∀ {Γ} → Raiseable (_⊩⋆ Γ)
    raise-⊩⋆ = record { ↑⟨_⟩ = ⊩⋆-↑⟨_⟩ }

    lower-⊩⋆ : ∀ {w} → Lowerable (w ⊩⋆_)
    lower-⊩⋆ = record { ↓⟨_⟩ = ⊩⋆-↓⟨_⟩ }

module _ {{_ : Model}} where
  Eq⋆ : ∀ {Γ w} → w ⊩⋆ Γ → w ⊩⋆ Γ → Set
  Eq⋆ []            []               = ⊤
  Eq⋆ [ ρ , x ≔ i ] [ ρ′ , .x ≔ i′ ] = Eq⋆ ρ ρ′ × Eq i i′

  𝒰⋆ : ∀ {Γ w} → w ⊩⋆ Γ → Set
  𝒰⋆ []            = ⊤
  𝒰⋆ [ ρ , x ≔ s ] = 𝒰⋆ ρ × 𝒰 s

  -- NOTE: Doesn’t need `𝒰⋆ ρ`!
  Eq⋆-refl : ∀ {Γ w} → (ρ : w ⊩⋆ Γ) → Eq⋆ ρ ρ
  Eq⋆-refl []            = tt
  Eq⋆-refl [ ρ , x ≔ s ] = Eq⋆-refl ρ
                         , reflEq s

  Eq⋆-sym : ∀ {Γ w} → (ρ ρ′ : w ⊩⋆ Γ) → Eq⋆ ρ ρ′ → Eq⋆ ρ′ ρ
  Eq⋆-sym []            []               tt        = tt
  Eq⋆-sym [ ρ , x ≔ s ] [ ρ′ , .x ≔ s′ ] (eᵨ , eₛ) = Eq⋆-sym ρ ρ′ eᵨ
                                                   , symEq s s′ eₛ

  Eq⋆-trans : ∀ {Γ w} → (ρ ρ′ ρ″ : w ⊩⋆ Γ) → Eq⋆ ρ ρ′ → Eq⋆ ρ′ ρ″ → Eq⋆ ρ ρ″
  Eq⋆-trans []            []               []               tt        tt          = tt
  Eq⋆-trans [ ρ , x ≔ s ] [ ρ′ , .x ≔ s′ ] [ ρ″ , .x ≔ s″ ] (eᵨ , eₛ) (eᵨ′ , eₛ′) = Eq⋆-trans ρ ρ′ ρ″ eᵨ eᵨ′
                                                                                  , transEq s s′ s″ eₛ eₛ′

  ≡→Eq⋆ : ∀ {Γ w} → (ρ ρ′ : w ⊩⋆ Γ) → ρ ≡ ρ′ → Eq⋆ ρ ρ′
  ≡→Eq⋆ ρ .ρ refl = Eq⋆-refl ρ

  Eq-cong-lookup : ∀ {Γ A w x} → (ρ ρ′ : w ⊩⋆ Γ) → Eq⋆ ρ ρ′ → (i : Γ ∋ x ∷ A) →
                     Eq (lookup ρ i) (lookup ρ′ i)
  Eq-cong-lookup [ ρ , x ≔ s ] [ ρ′ , .x ≔ s′ ] (eᵨ , eₛ) zero    = eₛ
  Eq-cong-lookup [ ρ , y ≔ t ] [ ρ′ , .y ≔ t′ ] (eᵨ , eₜ) (suc i) = Eq-cong-lookup ρ ρ′ eᵨ i

  Eq⋆-cong-↑⟨_⟩ : ∀ {Γ w w′} → (c : w′ ⊒ w) (ρ ρ′ : w ⊩⋆ Γ) → Eq⋆ ρ ρ′ →
                    Eq⋆ (↑⟨ c ⟩ ρ) (↑⟨ c ⟩ ρ′)
  Eq⋆-cong-↑⟨ c ⟩ []            []               tt        = tt
  Eq⋆-cong-↑⟨ c ⟩ [ ρ , x ≔ s ] [ ρ′ , .x ≔ s′ ] (eᵨ , eₛ) = Eq⋆-cong-↑⟨ c ⟩ ρ ρ′ eᵨ
                                                           , Eq-cong-↑⟨ c ⟩ s s′ eₛ

  Eq⋆-cong-↓⟨_⟩ : ∀ {Γ Δ w} → (c : Δ ⊇ Γ) (ρ ρ′ : w ⊩⋆ Δ) → Eq⋆ ρ ρ′ →
                    Eq⋆ (↓⟨ c ⟩ ρ) (↓⟨ c ⟩ ρ′)
  Eq⋆-cong-↓⟨ done ⟩     ρ ρ′ eᵨ = tt
  Eq⋆-cong-↓⟨ weak c i ⟩ ρ ρ′ eᵨ = Eq⋆-cong-↓⟨ c ⟩ ρ ρ′ eᵨ
                                 , Eq-cong-lookup ρ ρ′ eᵨ i

  𝒰-cong-lookup : ∀ {Γ A w x} → (ρ : w ⊩⋆ Γ) → 𝒰⋆ ρ → (i : Γ ∋ x ∷ A) →
                    𝒰 (lookup ρ i)
  𝒰-cong-lookup []            tt        ()
  𝒰-cong-lookup [ ρ , x ≔ s ] (uᵨ , uₛ) zero    = uₛ
  𝒰-cong-lookup [ ρ , x ≔ s ] (uᵨ , uₛ) (suc i) = 𝒰-cong-lookup ρ uᵨ i

  𝒰⋆-cong-↑⟨_⟩ : ∀ {Γ w w′} → (c : w′ ⊒ w) (ρ : w ⊩⋆ Γ) → 𝒰⋆ ρ →
                     𝒰⋆ (↑⟨ c ⟩ ρ)
  𝒰⋆-cong-↑⟨ c ⟩ []            tt        = tt
  𝒰⋆-cong-↑⟨ c ⟩ [ ρ , x ≔ s ] (uᵨ , uₛ) = 𝒰⋆-cong-↑⟨ c ⟩ ρ uᵨ
                                           , 𝒰-cong-↑⟨ c ⟩ s uₛ

  𝒰⋆-cong-↓⟨_⟩ : ∀ {Γ Δ w} → (c : Δ ⊇ Γ) (ρ : w ⊩⋆ Δ) → 𝒰⋆ ρ →
                     𝒰⋆ (↓⟨ c ⟩ ρ)
  𝒰⋆-cong-↓⟨ done ⟩     ρ uᵨ = tt
  𝒰⋆-cong-↓⟨ weak c i ⟩ ρ uᵨ = 𝒰⋆-cong-↓⟨ c ⟩ ρ uᵨ
                               , 𝒰-cong-lookup ρ uᵨ i

  postulate
    aux₄₂₁ : ∀ {Γ Δ A w x} → (c : Δ ⊇ Γ) (ρ : w ⊩⋆ Δ) → 𝒰⋆ ρ →
               (i : Γ ∋ x ∷ A) (i′ : Δ ∋ x ∷ A) →
               Eq (lookup ρ i′) (lookup (↓⟨ c ⟩ ρ) i)
  -- aux₄₂₁ c []            uᵨ i i′ = {!!}
  -- aux₄₂₁ c [ ρ , x ≔ s ] uᵨ i i′ = {!!}

  postulate
    aux₄₂₂ : ∀ {Γ A w w′ x} → (c : w′ ⊒ w) (ρ : w ⊩⋆ Γ) → 𝒰⋆ ρ →
               (i : Γ ∋ x ∷ A) →
               Eq (↑⟨ c ⟩ (lookup ρ i)) (lookup (↑⟨ c ⟩ ρ) i)

  postulate
    aux₄₂₃ : ∀ {Γ Δ A w x} {{_ : T (fresh x Γ)}} {{_ : T (fresh x Δ)}} →
               (c : Δ ⊇ Γ) (c′ : [ Δ , x ∷ A ] ⊇ Γ) (ρ : w ⊩⋆ Δ) → 𝒰⋆ ρ →
               (s : w ⊩ A) →
               Eq⋆ (↓⟨ c′ ⟩ [ ρ , x ≔ s ]) (↓⟨ c ⟩ ρ)

  postulate
    aux₄₂₄ : ∀ {Γ w} → (c : Γ ⊇ Γ) (ρ : w ⊩⋆ Γ) → 𝒰⋆ ρ →
               Eq⋆ (↓⟨ c ⟩ ρ) ρ
  -- aux₄₂₄ done       []          tt        = tt
  -- aux₄₂₄ (weak c i) (ρ , x ∷ s) (uᵨ , uₛ) = {!!}
  --                                         , ≡→Eq _ _
  --                                             (cong (lookup (ρ , x ∷ s))
  --                                               (uniq∋ i zero))

  postulate
    aux₄₂₅ : ∀ {Γ w} → (c : w ⊒ w) (ρ : w ⊩⋆ Γ) → 𝒰⋆ ρ →
               Eq⋆ (↑⟨ c ⟩ ρ) ρ

  postulate
    aux₄₂₆ : ∀ {Γ Δ Θ w} → (c : Δ ⊇ Γ) (c′ : Θ ⊇ Δ) (c″ : Θ ⊇ Γ) (ρ : w ⊩⋆ Θ) → 𝒰⋆ ρ →
               Eq⋆ (↓⟨ c ⟩ (↓⟨ c′ ⟩ ρ)) (↓⟨ c″ ⟩ ρ)

  postulate
    aux₄₂₇ : ∀ {Γ w w′ w″} → (c : w′ ⊒ w) (c′ : w″ ⊒ w′) (c″ : w″ ⊒ w) (ρ : w ⊩⋆ Γ) → 𝒰⋆ ρ →
               Eq⋆ (↑⟨ c′ ⟩ (↑⟨ c ⟩ ρ)) (↑⟨ c″ ⟩ ρ)

  postulate
    aux₄₂₈ : ∀ {Γ Δ w w′} → (c : Δ ⊇ Γ) (c′ : w′ ⊒ w) (ρ : w ⊩⋆ Δ) → 𝒰⋆ ρ →
               Eq⋆ (↑⟨ c′ ⟩ (↓⟨ c ⟩ ρ)) (↓⟨ c ⟩ (↑⟨ c′ ⟩ ρ))


-- 4.3. The semantics of the λ-calculus
-- ------------------------------------

module _ {{_ : Model}} where
  mutual
    ⟦_⟧ : ∀ {Γ A w} → Γ ⊢ A → w ⊩⋆ Γ → w ⊩ A
    ⟦ ν x i ⟧ ρ = lookup ρ i
    ⟦ ƛ x M ⟧ ρ = ⟦ƛ⟧ (λ c t → ⟦ M ⟧ [ ↑⟨ c ⟩ ρ , x ≔ t ])
    ⟦ M ∙ N ⟧ ρ = ⟦ M ⟧ ρ ⟦∙⟧⟨ refl⊒ ⟩ ⟦ N ⟧ ρ
    ⟦ M ▶ γ ⟧ ρ = ⟦ M ⟧ (⟦ γ ⟧⋆ ρ)

    ⟦_⟧⋆ : ∀ {Γ Δ w} → Δ ⋙ Γ → w ⊩⋆ Δ → w ⊩⋆ Γ
    ⟦ π⟨ c ⟩ ⟧⋆        ρ = ↓⟨ c ⟩ ρ
    ⟦ γ ● γ′ ⟧⋆        ρ = ⟦ γ ⟧⋆ (⟦ γ′ ⟧⋆ ρ)
    ⟦ [ γ , x ≔ M ] ⟧⋆ ρ = [ ⟦ γ ⟧⋆ ρ , x ≔ ⟦ M ⟧ ρ ]


-- 4.4. The inversion function
-- ---------------------------

instance
  canon : Model
  canon = record
    { 𝒲      = 𝒞
    ; _⊒_    = _⊇_
    ; refl⊒ = refl⊇
    ; _◇_    = _○_
    ; uniq⊒ = uniq⊇
    ; 𝒢      = _⊢ ⋆
    }

-- TODO: Can we do better than this?
postulate
  gensym : (Γ : 𝒞) → Σ Name (λ x → T (fresh x Γ))

var-↑⟨_⟩ : ∀ {Γ Δ A} → Δ ⊇ Γ → (x : Name) → Γ ∋ x ∷ A → Δ ⊢ A
var-↑⟨ c ⟩ x i = ν x (↑⟨ c ⟩ i)

mutual
  reify : ∀ {A Γ} → Γ ⊩ A → Γ ⊢ A
  reify {⋆}     {Γ} s = s ⟦ℊ⟧⟨ refl⊇ ⟩
  reify {A ⊃ B} {Γ} s = let x , φ = gensym Γ in
                        let instance _ = φ in
                        ƛ x (reify (s ⟦∙⟧⟨ weak⊇ ⟩ val-var zero))

  val : ∀ {A Γ} → (∀ {Δ} → Δ ⊇ Γ → Δ ⊢ A) → Γ ⊩ A
  val {⋆}     f = ⟦𝒢⟧ f
  val {A ⊃ B} f = ⟦ƛ⟧ (λ c t → val (λ c′ → f (c ○ c′) ∙ reify (↑⟨ c′ ⟩ t)))

  val-var : ∀ {x Γ A} → Γ ∋ x ∷ A → Γ ⊩ A
  val-var {x} i = val (λ c → var-↑⟨ c ⟩ x i)

aux₄₄₁ : ∀ {A Γ} → (f f′ : (∀ {Δ} → Δ ⊇ Γ → Δ ⊢ A)) → (∀ {Δ} → (c : Δ ⊇ Γ) → f c ≡ f′ c) →
           Eq (val f) (val f′)
aux₄₄₁ {⋆}     f f′ h = λ c      → h c
aux₄₄₁ {A ⊃ B} f f′ h = λ c t uₜ → aux₄₄₁ (λ c′ → f (c ○ c′) ∙ reify (↑⟨ c′ ⟩ t))
                                           (λ c′ → f′ (c ○ c′) ∙ reify (↑⟨ c′ ⟩ t))
                                           (λ c′ → cong (_∙ reify (↑⟨ c′ ⟩ t))
                                                      (h (c ○ c′)))

aux₄₄₂ : ∀ {A Γ Δ} → (c : Δ ⊇ Γ) (f : (∀ {Δ} → Δ ⊇ Γ → Δ ⊢ A)) →
           Eq (↑⟨ c ⟩ (val f)) (val (λ c′ → f (c ○ c′)))
aux₄₄₂ {⋆}     c f = λ c′      → cong f refl
aux₄₄₂ {A ⊃ B} c f = λ c′ t uₜ → aux₄₄₁ (λ c″ → f ((c ○ c′) ○ c″) ∙ reify (↑⟨ c″ ⟩ t))
                                         (λ c″ → f (c ○ (c′ ○ c″)) ∙ reify (↑⟨ c″ ⟩ t))
                                         (λ c″ → cong (_∙ reify (↑⟨ c″ ⟩ t))
                                                    (cong f
                                                      (sym (assoc○ c c′ c″))))

-- Theorem 1.
mutual
  thm₁ : ∀ {A Γ} → (s s′ : Γ ⊩ A) → Eq s s′ → reify s ≡ reify s′
  thm₁ {⋆}     {Γ} s s′ eₛ = eₛ refl⊇
  thm₁ {A ⊃ B} {Γ} s s′ eₛ = let x , φ = gensym Γ in
                             let instance _ = φ in
                             cong (ƛ x)
                               (thm₁ (s ⟦∙⟧⟨ weak⊇ ⟩ val-var zero)
                                     (s′ ⟦∙⟧⟨ weak⊇ ⟩ val-var zero)
                                     (eₛ weak⊇ (val-var zero) (𝒰-var zero)))

  aux₄₄₃ : ∀ {A Γ} → (f : ∀ {Δ} → Δ ⊇ Γ → Δ ⊢ A) → 𝒰 (val f)
  aux₄₄₃ {⋆}     f = tt
  aux₄₄₃ {A ⊃ B} f = (λ c t uₜ           → aux₄₄₃ (λ c′ → f (c ○ c′) ∙ reify (↑⟨ c′ ⟩ t)))
                   , (λ c t t′ uₜ uₜ′ eₜ → aux₄₄₁ (λ c′ → f (c ○ c′) ∙ reify (↑⟨ c′ ⟩ t))
                                                   (λ c′ → f (c ○ c′) ∙ reify (↑⟨ c′ ⟩ t′))
                                                   (λ c′ → cong (f (c ○ c′) ∙_)
                                                              (thm₁ (↑⟨ c′ ⟩ t) (↑⟨ c′ ⟩ t′)
                                                                (Eq-cong-↑⟨ c′ ⟩ t t′ eₜ))))

                   , (λ c c′ c″ t uₜ     → transEq (↑⟨ c′ ⟩ (val (λ c‴ → f (c ○ c‴) ∙ reify (↑⟨ c‴ ⟩ t))))
                                                     (val (λ c‴ → f (c ○ (c′ ○ c‴)) ∙ reify (↑⟨ c′ ○ c‴ ⟩ t)))
                                                     (val (λ c‴ → f (c″ ○ c‴) ∙ reify (↑⟨ c‴ ⟩ (↑⟨ c′ ⟩ t))))
                                              (aux₄₄₂ c′ (λ c‴ → f (c ○ c‴) ∙ reify (↑⟨ c‴ ⟩ t)))
                                              (aux₄₄₁ (λ c‴ → f (c ○ (c′ ○ c‴)) ∙ reify (↑⟨ c′ ○ c‴ ⟩ t))
                                                      (λ c‴ → f (c″ ○ c‴) ∙ reify (↑⟨ c‴ ⟩ (↑⟨ c′ ⟩ t)))
                                                      (λ c‴ → cong² _∙_
                                                                 (cong f
                                                                   (trans (assoc○ c c′ c‴)
                                                                          (comp○ (c ○ c′) c‴ (c″ ○ c‴))))
                                                                 (thm₁ (↑⟨ c′ ○ c‴ ⟩ t)
                                                                       (↑⟨ c‴ ⟩ (↑⟨ c′ ⟩ t))
                                                                       (symEq (↑⟨ c‴ ⟩ (↑⟨ c′ ⟩ t))
                                                                               (↑⟨ c′ ○ c‴ ⟩ t)
                                                                               (aux₄₁₂ c′ c‴ (c′ ○ c‴) t))))))

  𝒰-var : ∀ {x Γ A} → (i : Γ ∋ x ∷ A) → 𝒰 (val-var i)
  𝒰-var {x} i = aux₄₄₃ (λ c → var-↑⟨ c ⟩ x i)

⊩⋆-proj : ∀ {Γ Δ} → Δ ⊇ Γ → Δ ⊩⋆ Γ
⊩⋆-proj done               = []
⊩⋆-proj (weak {x = x} c i) = [ ⊩⋆-proj c , x ≔ val-var i ]

⊩⋆-refl : ∀ {Γ} → Γ ⊩⋆ Γ
⊩⋆-refl = ⊩⋆-proj refl⊇

nf : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ A
nf M = reify (⟦ M ⟧ ⊩⋆-refl)

-- Corollary 1
cor₁ : ∀ {Γ A} → (M M′ : Γ ⊢ A) → Eq (⟦ M ⟧ ⊩⋆-refl) (⟦ M′ ⟧ ⊩⋆-refl) →
         nf M ≡ nf M′
cor₁ M M′ = thm₁ (⟦ M ⟧ ⊩⋆-refl) (⟦ M′ ⟧ ⊩⋆-refl)


-- 4.5. Soundness and completeness of proof trees
-- ----------------------------------------------
--
-- (…)


-- 4.6. Completeness of the conversion rules for proof trees
-- ---------------------------------------------------------

data CV : ∀ {Γ A} → Γ ⊢ A → Γ ⊩ A → Set where
  cv-⋆ : ∀ {Γ} {M : Γ ⊢ ⋆} {s : Γ ⊩ ⋆} →
           (∀ {Δ} → (c : Δ ⊇ Γ) → M ▶ π⟨ c ⟩ ≅ s ⟦ℊ⟧⟨ c ⟩) →
           CV M s
  cv-⊃ : ∀ {Γ A B} {M : Γ ⊢ A ⊃ B} {s : Γ ⊩ A ⊃ B} →
           (∀ {Δ N t} → (c : Δ ⊇ Γ) → CV N t → CV ((M ▶ π⟨ c ⟩) ∙ N) (s ⟦∙⟧⟨ c ⟩ t)) →
           CV M s

data CV⋆ : ∀ {Γ Δ} → Δ ⋙ Γ → Δ ⊩⋆ Γ → Set where
  cv-[] : ∀ {Γ} →
           (γ : Γ ⋙ []) →
           CV⋆ γ []
  cv-≔  : ∀ {Γ Δ A x} {{_ : T (fresh x Γ)}}
            {γ : Δ ⋙ [ Γ , x ∷ A ]} {c : [ Γ , x ∷ A ] ⊇ Γ} {ρ : Δ ⊩⋆ Γ} {s : Δ ⊩ A} →
            CV⋆ (π⟨ c ⟩ ● γ) ρ → CV (ν x zero ▶ γ) s →
            CV⋆ γ [ ρ , x ≔ s ]

postulate
  aux₄₆₁ : ∀ {Γ A} {M M′ : Γ ⊢ A} {s : Γ ⊩ A} →
             M ≅ M′ → CV M′ s →
             CV M s

postulate
  aux₄₆₂ : ∀ {Γ Δ} {γ γ′ : Δ ⋙ Γ} {ρ : Δ ⊩⋆ Γ} →
             γ ≅ₛ γ′ → CV⋆ γ′ ρ →
             CV⋆ γ ρ

postulate
  aux₄₆₃ : ∀ {Γ Δ A} {M : Γ ⊢ A} {s : Γ ⊩ A} →
             (c : Δ ⊇ Γ) → CV M s →
             CV (M ▶ π⟨ c ⟩) (↑⟨ c ⟩ s)

postulate
  aux₄₆₄ : ∀ {Γ Δ A x} {γ : Δ ⋙ Γ} {ρ : Δ ⊩⋆ Γ} {i : Γ ∋ x ∷ A} →
             CV⋆ γ ρ →
             CV (ν x i ▶ γ) (lookup ρ i)

postulate
  aux₄₆₅ : ∀ {Γ Δ Θ} {γ : Δ ⋙ Γ} {ρ : Δ ⊩⋆ Γ} →
             (c : Θ ⊇ Δ) → CV⋆ γ ρ →
             CV⋆ (γ ● π⟨ c ⟩) (↑⟨ c ⟩ ρ)

postulate
  aux₄₆₆ : ∀ {Γ Δ Θ} {γ : Θ ⋙ Δ} {ρ : Θ ⊩⋆ Δ} →
             (c : Δ ⊇ Γ) → CV⋆ γ ρ →
             CV⋆ (π⟨ c ⟩ ● γ) (↓⟨ c ⟩ ρ)

-- Lemma 8.
mutual
  postulate
    lem₈ : ∀ {Γ Δ A} {γ : Δ ⋙ Γ} {ρ : Δ ⊩⋆ Γ} →
             (M : Γ ⊢ A) → CV⋆ γ ρ →
             CV (M ▶ γ) (⟦ M ⟧ ρ)

  postulate
    lem₈⋆ : ∀ {Γ Δ Θ} {γ′ : Θ ⋙ Δ} {ρ : Θ ⊩⋆ Δ} →
              (γ : Δ ⋙ Γ) → CV⋆ γ′ ρ →
              CV⋆ (γ ● γ′) (⟦ γ ⟧⋆ ρ)

-- Lemma 9.
mutual
  postulate
    lem₉ : ∀ {Γ A} {M : Γ ⊢ A} {s : Γ ⊩ A} →
             CV M s →
             M ≅ reify s

  postulate
    lem₉⋆ : ∀ {Γ Δ A} {M : Γ ⊢ A} {f : ∀ {Δ} → Δ ⊇ Γ → Δ ⊢ A} →
              (c : Δ ⊇ Γ) → M ▶ π⟨ c ⟩ ≅ f c →
              CV M (val f)

postulate
  CV⋆-proj : ∀ {Γ Δ} → (c : Δ ⊇ Γ) → CV⋆ (π⟨ c ⟩) (⊩⋆-proj c)

CV⋆-refl : ∀ {Γ} → CV⋆ π⟨ refl⊇ ⟩ (⊩⋆-refl {Γ})
CV⋆-refl = CV⋆-proj refl⊇

postulate
  aux₄₆₇ : ∀ {Γ A} {M : Γ ⊢ A} {c : Γ ⊇ Γ} →
             M ▶ π⟨ c ⟩ ≅ nf M

-- Theorem 2.
postulate
  thm₂ : ∀ {Γ A} → (M : Γ ⊢ A) →
           M ≅ nf M

-- Theorem 3.
postulate
  thm₃ : ∀ {Γ A} → (M M′ : Γ ⊢ A) → Eq (⟦ M ⟧ ⊩⋆-refl) (⟦ M′ ⟧ ⊩⋆-refl) →
           M ≅ M′


-- 4.7. Completeness of the conversion rules for substitutions
-- -----------------------------------------------------------

reify⋆ : ∀ {Γ Δ} → Δ ⊩⋆ Γ → Δ ⋙ Γ
reify⋆ []            = π⟨ done ⟩
reify⋆ [ ρ , x ≔ s ] = [ reify⋆ ρ , x ≔ reify s ]

nf⋆ : ∀ {Δ Γ} → Δ ⋙ Γ → Δ ⋙ Γ
nf⋆ γ = reify⋆ (⟦ γ ⟧⋆ ⊩⋆-refl)

postulate
  thm₂⋆ : ∀ {Γ Δ} → (γ : Δ ⋙ Γ) →
            γ ≅ₛ nf⋆ γ

postulate
  thm₃⋆ : ∀ {Γ Δ} → (γ γ′ : Δ ⋙ Γ) → Eq⋆ (⟦ γ ⟧⋆ ⊩⋆-refl) (⟦ γ′ ⟧⋆ ⊩⋆-refl) →
            γ ≅ₛ γ′


-- 4.8. Soundness of the conversion rules
-- --------------------------------------

postulate
  aux₄₈₁ : ∀ {Γ Δ A} {M : Γ ⊢ A} {ρ : Δ ⊩⋆ Γ} →
             𝒰⋆ ρ → 𝒰 (⟦ M ⟧ ρ)

postulate
  aux₄₈₂ : ∀ {Γ Δ} {γ : Γ ⋙ Δ} {ρ : Δ ⊩⋆ Γ} →
             𝒰⋆ ρ → 𝒰⋆ (⟦ γ ⟧⋆ ρ)

postulate
  aux₄₈₃ : ∀ {Γ Δ A} {M : Γ ⊢ A} {ρ ρ′ : Δ ⊩⋆ Γ} →
             Eq⋆ ρ ρ′ → Eq (⟦ M ⟧ ρ) (⟦ M ⟧ ρ′)

postulate
  aux₄₈₄ : ∀ {Γ Δ} {γ : Γ ⋙ Δ} {ρ ρ′ : Δ ⊩⋆ Γ} →
             Eq⋆ ρ ρ′ → Eq⋆ (⟦ γ ⟧⋆ ρ) (⟦ γ ⟧⋆ ρ′)

postulate
  aux₄₈₅ : ∀ {Γ Δ Θ A} {M : Γ ⊢ A} {ρ : Δ ⊩⋆ Γ} {c : Θ ⊇ Δ} →
             Eq (↑⟨ c ⟩ (⟦ M ⟧ ρ)) (⟦ M ⟧ (↑⟨ c ⟩ ρ))

postulate
  aux₄₈₆ : ∀ {Γ Δ Θ} {γ : Γ ⋙ Δ} {ρ : Δ ⊩⋆ Γ} {c : Θ ⊇ Δ} →
             Eq⋆ (↑⟨ c ⟩ (⟦ γ ⟧⋆ ρ)) (⟦ γ ⟧⋆ (↑⟨ c ⟩ ρ))

-- Theorem 4.
mutual
  postulate
    thm₄ : ∀ {Γ A w} {M M′ : Γ ⊢ A} → M ≅ M′ → (ρ : w ⊩⋆ Γ) →
             Eq (⟦ M ⟧ ρ) (⟦ M′ ⟧ ρ)

  postulate
    thm₄⋆ : ∀ {Γ Δ w} {γ γ′ : Γ ⋙ Δ} → γ ≅ₛ γ′ → (ρ : w ⊩⋆ Γ) →
              Eq⋆ (⟦ γ ⟧⋆ ρ) (⟦ γ′ ⟧⋆ ρ)


-- 4.9. Decision algorithm for conversion
-- --------------------------------------

-- Theorem 5.
thm₅ : ∀ {Γ A} → (M M′ : Γ ⊢ A) → nf M ≡ nf M′ → M ≅ M′
thm₅ M M′ p = begin
                M
              ≅⟨ thm₂ M ⟩
                nf M
              ≡⟨ p ⟩
                nf M′
              ≅⟨ sym≅ (thm₂ M′) ⟩
                M′
              ∎
              where
                open ≅-Reasoning

-- Theorem 6.
thm₆ : ∀ {Γ A} → (M M′ : Γ ⊢ A) → M ≅ M′ → nf M ≡ nf M′
thm₆ M M′ p = cor₁ M M′ (thm₄ p ⊩⋆-refl)
