{-# OPTIONS --no-positivity-check #-}

module Section4a where

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

  id₁◇ : ∀ {w w′} → (c : w ⊒ w) (c′ : w′ ⊒ w) → c ◇ c′ ≡ c′
  id₁◇ c c′ = uniq⊒ (c ◇ c′) c′

  id₂◇ : ∀ {w w′} → (c : w′ ⊒ w) (c′ : w′ ⊒ w′) → c ◇ c′ ≡ c
  id₂◇ c c′ = uniq⊒ (c ◇ c′) c

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
-- Forcing is written `w ⊩ A`.  For the base type an element in `w ⊩ •` is a family of
-- elements in `𝒢 w′`, `w′ ⊒ w`.  For the type `A ⊃ B` an element in `w ⊩ A ⊃ B` is a family of
-- functions from `w′ ⊩ A` to `w′ ⊩ B`, `w′ ⊒ w`.  (…)

module _ {{_ : Model}} where
  -- TODO: Replace with strictly positive definition
  infix 3 _⊩_
  data _⊩_ : 𝒲 → 𝒯 → Set where
    ⟦𝒢⟧ : ∀ {w} →
            (∀ {w′} → w′ ⊒ w → 𝒢 w′) →
            w ⊩ •
    ⟦ƛ⟧ : ∀ {w A B} →
            (∀ {w′} → w′ ⊒ w → w′ ⊩ A → w′ ⊩ B) →
            w ⊩ A ⊃ B

-- We use the notational convention `⟦𝒢⟧` for the semantics of the ground type and
-- `⟦ƛ⟧` for the semantics of the function type.
--
-- We define the following two elimination rules:  (…)

module _ {{_ : Model}} where
  _⟦g⟧⟨_⟩ : ∀ {w w′} → w ⊩ • → w′ ⊒ w → 𝒢 w′
  (⟦𝒢⟧ f) ⟦g⟧⟨ c ⟩ = f c

  _⟦∙⟧⟨_⟩_ : ∀ {w w′ A B} → w ⊩ A ⊃ B → w′ ⊒ w → w′ ⊩ A → w′ ⊩ B
  (⟦ƛ⟧ f) ⟦∙⟧⟨ c ⟩ a = f c a

-- The monotonicity function `↑⟨_⟩⊩` lifts a semantic object in one world into a semantic object
-- in a bigger world and is defined by induction on the type.  (…)

module _ {{_ : Model}} where
  ↑⟨_⟩⊩ : ∀ {A w w′} → w′ ⊒ w → w ⊩ A → w′ ⊩ A
  ↑⟨_⟩⊩ {•}     c f = ⟦𝒢⟧ (λ c′   → f ⟦g⟧⟨ c ◇ c′ ⟩)
  ↑⟨_⟩⊩ {A ⊃ B} c f = ⟦ƛ⟧ (λ c′ a → f ⟦∙⟧⟨ c ◇ c′ ⟩ a)

  instance
    raise⊩ : ∀ {A} → Raiseable (_⊩ A)
    raise⊩ = record { ↑⟨_⟩ = ↑⟨_⟩⊩ }

-- We also need to define an equality, `Eq`, on semantic objects.  For the soundness of the
-- η-rule we need `f : w ⊩ A ⊃ B` to be equal to `⟦ƛ⟧ (λ c a → f ⟦∙⟧⟨ c ⟩ a)`, which corresponds
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
-- semantic objects and if application and monotonicity commute for the semantic object.
--
-- The sets `Eq` and `𝒰` are defined by:  (…)

module _ {{_ : Model}} where
  mutual
    data Eq : ∀ {A w} → w ⊩ A → w ⊩ A → Set where
      eq• : ∀ {w} {f f′ : w ⊩ •} →
              (∀ {w′} →
                 (c : w′ ⊒ w) →
                 f ⟦g⟧⟨ c ⟩ ≡ f′ ⟦g⟧⟨ c ⟩) →
              Eq f f′
      eq⊃ : ∀ {A B w} {f f′ : w ⊩ A ⊃ B} →
              (∀ {w′} →
                 (c : w′ ⊒ w) → {a : w′ ⊩ A} → 𝒰 a →
                 Eq (f ⟦∙⟧⟨ c ⟩ a) (f′ ⟦∙⟧⟨ c ⟩ a)) →
              Eq f f′

    data 𝒰 : ∀ {A w} → w ⊩ A → Set where
      𝓊• : ∀ {w} {f : w ⊩ •} →
             𝒰 f
      𝓊⊃ : ∀ {A B w} {f : w ⊩ A ⊃ B} →
             (∀ {w′} →
                (c : w′ ⊒ w) → {a : w′ ⊩ A} → 𝒰 a →
                𝒰 (f ⟦∙⟧⟨ c ⟩ a)) →
             (∀ {w′} →
                (c : w′ ⊒ w) → {a a′ : w′ ⊩ A} → Eq a a′ → 𝒰 a → 𝒰 a′ →
                Eq (f ⟦∙⟧⟨ c ⟩ a) (f ⟦∙⟧⟨ c ⟩ a′)) →
             (∀ {w′ w″} →
                (c : w′ ⊒ w) (c′ : w″ ⊒ w′) (c″ : w″ ⊒ w) → {a : w′ ⊩ A} → 𝒰 a →
                Eq (↑⟨ c′ ⟩ (f ⟦∙⟧⟨ c ⟩ a)) (f ⟦∙⟧⟨ c″ ⟩ (↑⟨ c′ ⟩ a))) →
             𝒰 f

-- The equality `Eq` is transitive and symmetric and it is reflexive for uniform objects.

module _ {{_ : Model}} where
  reflEq : ∀ {A w} {a : w ⊩ A} → 𝒰 a → Eq a a
  reflEq 𝓊•            = eq• (λ c    → refl)
  reflEq (𝓊⊃ h₀ h₁ h₂) = eq⊃ (λ c uₐ → reflEq (h₀ c uₐ))

  -- TODO: Why do we restrict `Eq` so that it is reflexive only for uniform objects?
  reflEq′ : ∀ {A w} {a : w ⊩ A} → Eq a a
  reflEq′ {•}     = eq• (λ c    → refl)
  reflEq′ {A ⊃ B} = eq⊃ (λ c uₐ → reflEq′)

  symEq : ∀ {A w} {a a′ : w ⊩ A} → Eq a a′ → Eq a′ a
  symEq {•}     (eq• h) = eq• (λ c    → sym (h c))
  symEq {A ⊃ B} (eq⊃ h) = eq⊃ (λ c uₐ → symEq (h c uₐ))

  transEq : ∀ {A w} {a a′ a″ : w ⊩ A} → Eq a a′ → Eq a′ a″ → Eq a a″
  transEq {•}     (eq• h) (eq• h′) = eq• (λ c    → trans (h c) (h′ c))
  transEq {A ⊃ B} (eq⊃ h) (eq⊃ h′) = eq⊃ (λ c uₐ → transEq (h c uₐ) (h′ c uₐ))

module _ {{_ : Model}} where
  ≡→Eq : ∀ {A w} {a a′ : w ⊩ A} → 𝒰 a → a ≡ a′ → Eq a a′
  ≡→Eq u refl = reflEq u

  module EqReasoning where
    infix 1 begin_
    begin_ : ∀ {A w} {a a′ : w ⊩ A} → Eq a a′ → Eq a a′
    begin eq = eq

    infixr 2 _Eq⟨⟩_
    _Eq⟨⟩_ : ∀ {A w} (a {a′} : w ⊩ A) → Eq a a′ → Eq a a′
    a Eq⟨⟩ eq = eq

    infixr 2 _Eq⟨_⟩_
    _Eq⟨_⟩_ : ∀ {A w} (a {a′ a″} : w ⊩ A) → Eq a a′ → Eq a′ a″ → Eq a a″
    a Eq⟨ eq ⟩ eq′ = transEq eq eq′

    infixr 2 _≡⟨⟩_
    _≡⟨⟩_ : ∀ {A w} (a {a′} : w ⊩ A) → Eq a a′ → Eq a a′
    a ≡⟨⟩ eq = eq

    infixr 2 _≡⟨_∣_⟩_
    _≡⟨_∣_⟩_ : ∀ {A w} (a {a′ a″} : w ⊩ A) → a ≡ a′ → 𝒰 a → Eq a′ a″ → Eq a a″
    a ≡⟨ eq ∣ u ⟩ eq′ = transEq (≡→Eq u eq) eq′

    infix 3 _∎⟨_⟩
    _∎⟨_⟩ : ∀ {A w} (a : w ⊩ A) → 𝒰 a → Eq a a
    a ∎⟨ u ⟩ = reflEq u

-- Equal uniform values can be substituted in `⟦∙⟧⟨_⟩` and the function `↑⟨_⟩` returns uniform objects
-- for uniform input and equal results for equal input.

module _ {{_ : Model}} where
  cong⟦∙⟧⟨_⟩Eq : ∀ {A B w w′} {f f′ : w ⊩ A ⊃ B} {a a′ : w′ ⊩ A} →
                   (c : w′ ⊒ w) → Eq f f′ → 𝒰 f → 𝒰 f′ → Eq a a′ → 𝒰 a → 𝒰 a′ →
                   Eq (f ⟦∙⟧⟨ c ⟩ a) (f′ ⟦∙⟧⟨ c ⟩ a′)
  cong⟦∙⟧⟨ c ⟩Eq (eq⊃ h) (𝓊⊃ h₀ h₁ h₂) (𝓊⊃ h₀′ h₁′ h₂′) eqₐ uₐ uₐ′ =
    transEq (h₁ c eqₐ uₐ uₐ′) (h c uₐ′)

  cong↑⟨_⟩Eq : ∀ {A w w′} {a a′ : w ⊩ A} →
                 (c : w′ ⊒ w) → Eq a a′ →
                 Eq (↑⟨ c ⟩ a) (↑⟨ c ⟩ a′)
  cong↑⟨ c ⟩Eq (eq• h) = eq• (λ c′    → h (c ◇ c′))
  cong↑⟨ c ⟩Eq (eq⊃ h) = eq⊃ (λ c′ uₐ → h (c ◇ c′) uₐ)

  cong↑⟨_⟩𝒰 : ∀ {A w w′} {a : w ⊩ A} →
                (c : w′ ⊒ w) → 𝒰 a →
                𝒰 (↑⟨ c ⟩ a)
  cong↑⟨ c ⟩𝒰 𝓊•            = 𝓊•
  cong↑⟨ c ⟩𝒰 (𝓊⊃ h₀ h₁ h₂) = 𝓊⊃ (λ c′ uₐ         → h₀ (c ◇ c′) uₐ)
                                 (λ c′ eqₐ uₐ uₐ′ → h₁ (c ◇ c′) eqₐ uₐ uₐ′)
                                 (λ c′ c″ c‴ uₐ   → h₂ (c ◇ c′) c″ (c ◇ c‴) uₐ)

-- We also need to prove the following properties about `Eq` and `𝒰` which are used in the proofs of
-- soundness and completeness below.

module _ {{_ : Model}} where
  aux₄₁₁⟨_⟩ : ∀ {A w} →
                (c : w ⊒ w) → {a : w ⊩ A} → 𝒰 a →
                Eq (↑⟨ c ⟩ a) a
  aux₄₁₁⟨ c ⟩ {f} 𝓊•            = eq• (λ c′        → cong (f ⟦g⟧⟨_⟩)
                                                        (id₁◇ c c′))
  aux₄₁₁⟨ c ⟩ {f} (𝓊⊃ h₀ h₁ h₂) = eq⊃ (λ c′ {a} uₐ → ≡→Eq (h₀ (c ◇ c′) uₐ)
                                                        (cong (f ⟦∙⟧⟨_⟩ a)
                                                          (id₁◇ c c′)))

  aux₄₁₂ : ∀ {A w w′ w″} →
             (c : w′ ⊒ w) (c′ : w″ ⊒ w′) (c″ : w″ ⊒ w) → {a : w ⊩ A} → 𝒰 a →
             Eq (↑⟨ c′ ⟩ (↑⟨ c ⟩ a)) (↑⟨ c″ ⟩ a)
  aux₄₁₂ c c′ c″ {f} 𝓊•            = eq• (λ c‴        → cong (f ⟦g⟧⟨_⟩)
                                                           (trans (assoc◇ c c′ c‴)
                                                                  (comp◇ (c ◇ c′) c‴ (c″ ◇ c‴))))
  aux₄₁₂ c c′ c″ {f} (𝓊⊃ h₀ h₁ h₂) = eq⊃ (λ c‴ {a} uₐ → ≡→Eq (h₀ (c ◇ (c′ ◇ c‴)) uₐ)
                                                           (cong (f ⟦∙⟧⟨_⟩ a)
                                                             (trans (assoc◇ c c′ c‴)
                                                                    (comp◇ (c ◇ c′) c‴ (c″ ◇ c‴)))))
  aux₄₁₃ : ∀ {A B w w′} →
             (c : w′ ⊒ w) (c′ : w′ ⊒ w′) → {f : w ⊩ A ⊃ B} → 𝒰 f → {a : w′ ⊩ A} → 𝒰 a →
             Eq (f ⟦∙⟧⟨ c ⟩ a) (↑⟨ c ⟩ f ⟦∙⟧⟨ c′ ⟩ a)
  aux₄₁₃ c c′ {f} (𝓊⊃ h₀ h₁ h₂) {a} uₐ = ≡→Eq (h₀ c uₐ)
                                           (cong (f ⟦∙⟧⟨_⟩ a)
                                             (sym (id₂◇ c c′)))


-- 4.2. Semantic environments
-- --------------------------
--
-- We define the set of environments `_⊩⋆_`
-- where each variable in a context is associated with a semantic object.  (…)
--
-- The set is introduced by:  (…)

module _ {{_ : Model}} where
  infix 3 _⊩⋆_
  data _⊩⋆_ : 𝒲 → 𝒞 → Set where
    []      : ∀ {w} →
                w ⊩⋆ []
    [_,_≔_] : ∀ {Γ A w} →
                w ⊩⋆ Γ → (x : Name) {{_ : T (fresh x Γ)}} → w ⊩ A →
                w ⊩⋆ [ Γ , x ∷ A ]

-- We write `[]` for the empty environment and `[ ρ , x ≔ a ]` for updating an environment.
-- We define the following operations on semantic environments:
--
-- The function `lookup` is defined by induction on the environment.  (…)

module _ {{_ : Model}} where
  lookup : ∀ {Γ A w x} → w ⊩⋆ Γ → Γ ∋ x ∷ A → w ⊩ A
  lookup [ ρ , x ≔ a ] zero    = a
  lookup [ ρ , y ≔ b ] (suc i) = lookup ρ i

-- The function `↑⟨_⟩⊩⋆` that lifts
-- an environment into a bigger world is also defined by induction on the environment.  (…)

module _ {{_ : Model}} where
  ↑⟨_⟩⊩⋆ : ∀ {Γ w w′} → w′ ⊒ w → w ⊩⋆ Γ → w′ ⊩⋆ Γ
  ↑⟨ c ⟩⊩⋆ []            = []
  ↑⟨ c ⟩⊩⋆ [ ρ , x ≔ a ] = [ ↑⟨ c ⟩⊩⋆ ρ , x ≔ ↑⟨ c ⟩ a ]

  instance
    raise⊩⋆ : ∀ {Γ} → Raiseable (_⊩⋆ Γ)
    raise⊩⋆ = record { ↑⟨_⟩ = ↑⟨_⟩⊩⋆ }

-- The last function `↓⟨_⟩⊩⋆` is the projection on
-- environments and it is defined by induction on the proof of `Γ ⊇ Δ`.  (…)

module _ {{_ : Model}} where
  ↓⟨_⟩⊩⋆ : ∀ {Γ Δ w} → Γ ⊇ Δ → w ⊩⋆ Γ → w ⊩⋆ Δ
  ↓⟨ done ⟩⊩⋆             ρ = []
  ↓⟨ step {x = x} c i ⟩⊩⋆ ρ = [ ↓⟨ c ⟩⊩⋆ ρ , x ≔ lookup ρ i ]

  instance
    lower⊩⋆ : ∀ {w} → Lowerable (w ⊩⋆_)
    lower⊩⋆ = record { ↓⟨_⟩ = ↓⟨_⟩⊩⋆ }

-- We say that an environment is uniform `𝒰⋆ ρ : Set`, where `ρ : w ⊩⋆ Γ`, if each semantic
-- object in the environment is uniform.  Two environments are equal `Eq⋆ ρ ρ′ : Set`,
-- where `ρ, ρ′ : w ⊩⋆ Γ`, if they are equal component-wise.

module _ {{_ : Model}} where
  data Eq⋆ : ∀ {Γ w} → w ⊩⋆ Γ → w ⊩⋆ Γ → Set where
    eq⋆[] : ∀ {w} →
              Eq⋆ ([] {w}) ([] {w})
    eq⋆≔  : ∀ {Γ A w x} {{_ : T (fresh x Γ)}} {ρ ρ′ : w ⊩⋆ Γ} {a a′ : w ⊩ A} →
              Eq⋆ ρ ρ′ → Eq a a′ →
              Eq⋆ [ ρ , x ≔ a ] [ ρ′ , x ≔ a′ ]

  data 𝒰⋆ : ∀ {Γ w} → w ⊩⋆ Γ → Set where
    𝓊⋆[] : ∀ {w} →
             𝒰⋆ ([] {w})
    𝓊⋆≔  : ∀ {Γ A w x} {{_ : T (fresh x Γ)}} {ρ : w ⊩⋆ Γ} {a : w ⊩ A} →
             𝒰⋆ ρ → 𝒰 a →
             𝒰⋆ [ ρ , x ≔ a ]

-- The equality on semantic environments, `Eq⋆`, is transitive, symmetric, and for uniform
-- environments also reflexive.

module _ {{_ : Model}} where
  reflEq⋆ : ∀ {Γ w} {ρ : w ⊩⋆ Γ} → 𝒰⋆ ρ → Eq⋆ ρ ρ
  reflEq⋆ 𝓊⋆[]       = eq⋆[]
  reflEq⋆ (𝓊⋆≔ u⋆ u) = eq⋆≔ (reflEq⋆ u⋆) (reflEq u)

  symEq⋆ : ∀ {Γ w} {ρ ρ′ : w ⊩⋆ Γ} → Eq⋆ ρ ρ′ → Eq⋆ ρ′ ρ
  symEq⋆ eq⋆[]         = eq⋆[]
  symEq⋆ (eq⋆≔ eq⋆ eq) = eq⋆≔ (symEq⋆ eq⋆) (symEq eq)

  transEq⋆ : ∀ {Γ w} {ρ ρ′ ρ″ : w ⊩⋆ Γ} → Eq⋆ ρ ρ′ → Eq⋆ ρ′ ρ″ → Eq⋆ ρ ρ″
  transEq⋆ eq⋆[]         eq⋆[]           = eq⋆[]
  transEq⋆ (eq⋆≔ eq⋆ eq) (eq⋆≔ eq⋆′ eq′) = eq⋆≔ (transEq⋆ eq⋆ eq⋆′) (transEq eq eq′)

module _ {{_ : Model}} where
  ≡→Eq⋆ : ∀ {Γ w} {ρ ρ′ : w ⊩⋆ Γ} → 𝒰⋆ ρ → ρ ≡ ρ′ → Eq⋆ ρ ρ′
  ≡→Eq⋆ u⋆ refl = reflEq⋆ u⋆

  module Eq⋆Reasoning where
    infix 1 begin_
    begin_ : ∀ {Γ w} {ρ ρ′ : w ⊩⋆ Γ} → Eq⋆ ρ ρ′ → Eq⋆ ρ ρ′
    begin eq⋆ = eq⋆

    infixr 2 _Eq⋆⟨⟩_
    _Eq⋆⟨⟩_ : ∀ {Γ w} (ρ {ρ′} : w ⊩⋆ Γ) → Eq⋆ ρ ρ′ → Eq⋆ ρ ρ′
    ρ Eq⋆⟨⟩ eq⋆ = eq⋆

    infixr 2 _Eq⋆⟨_⟩_
    _Eq⋆⟨_⟩_ : ∀ {Γ w} (ρ {ρ′ ρ″} : w ⊩⋆ Γ) → Eq⋆ ρ ρ′ → Eq⋆ ρ′ ρ″ → Eq⋆ ρ ρ″
    ρ Eq⋆⟨ eq⋆ ⟩ eq⋆′ = transEq⋆ eq⋆ eq⋆′

    infixr 2 _≡⟨⟩_
    _≡⟨⟩_ : ∀ {Γ w} (ρ {ρ′} : w ⊩⋆ Γ) → Eq⋆ ρ ρ′ → Eq⋆ ρ ρ′
    ρ ≡⟨⟩ eq⋆ = eq⋆

    infixr 2 _≡⟨_∣_⟩_
    _≡⟨_∣_⟩_ : ∀ {Γ w} (ρ {ρ′ ρ″} : w ⊩⋆ Γ) → ρ ≡ ρ′ → 𝒰⋆ ρ → Eq⋆ ρ′ ρ″ → Eq⋆ ρ ρ″
    ρ ≡⟨ eq⋆ ∣ u⋆ ⟩ eq⋆′ = transEq⋆ (≡→Eq⋆ u⋆ eq⋆) eq⋆′

    infix 3 _∎⟨_⟩
    _∎⟨_⟩ : ∀ {Γ w} (ρ : w ⊩⋆ Γ) → 𝒰⋆ ρ → Eq⋆ ρ ρ
    ρ ∎⟨ u⋆ ⟩ = reflEq⋆ u⋆

-- We can substitute equal semantic environments in `lookup`, `↑⟨_⟩`, `↓⟨_⟩`
-- and the result of applying these functions to uniform environments is also uniform.

module _ {{_ : Model}} where
  conglookupEq : ∀ {Γ A w x} →
                   {ρ ρ′ : w ⊩⋆ Γ} → Eq⋆ ρ ρ′ → (i : Γ ∋ x ∷ A) →
                   Eq (lookup ρ i) (lookup ρ′ i)
  conglookupEq eq⋆[]         ()
  conglookupEq (eq⋆≔ eq⋆ eq) zero    = eq
  conglookupEq (eq⋆≔ eq⋆ eq) (suc i) = conglookupEq eq⋆ i

  cong↑⟨_⟩Eq⋆ : ∀ {Γ w w′} →
                  (c : w′ ⊒ w) → {ρ ρ′ : w ⊩⋆ Γ} → Eq⋆ ρ ρ′ →
                  Eq⋆ (↑⟨ c ⟩ ρ) (↑⟨ c ⟩ ρ′)
  cong↑⟨ c ⟩Eq⋆ eq⋆[]         = eq⋆[]
  cong↑⟨ c ⟩Eq⋆ (eq⋆≔ eq⋆ eq) = eq⋆≔ (cong↑⟨ c ⟩Eq⋆ eq⋆) (cong↑⟨ c ⟩Eq eq)

  cong↓⟨_⟩Eq⋆ : ∀ {Γ Δ w} →
                  (c : Γ ⊇ Δ) → {ρ ρ′ : w ⊩⋆ Γ} → Eq⋆ ρ ρ′ →
                  Eq⋆ (↓⟨ c ⟩ ρ) (↓⟨ c ⟩ ρ′)
  cong↓⟨ done ⟩Eq⋆     eq⋆ = eq⋆[]
  cong↓⟨ step c i ⟩Eq⋆ eq⋆ = eq⋆≔ (cong↓⟨ c ⟩Eq⋆ eq⋆) (conglookupEq eq⋆ i)

  conglookup𝒰 : ∀ {Γ A w x} →
                  {ρ : w ⊩⋆ Γ} → 𝒰⋆ ρ → (i : Γ ∋ x ∷ A) →
                  𝒰 (lookup ρ i)
  conglookup𝒰 𝓊⋆[]       ()
  conglookup𝒰 (𝓊⋆≔ u⋆ u) zero    = u
  conglookup𝒰 (𝓊⋆≔ u⋆ u) (suc i) = conglookup𝒰 u⋆ i

  cong↑⟨_⟩𝒰⋆ : ∀ {Γ w w′} →
                 (c : w′ ⊒ w) → {ρ : w ⊩⋆ Γ} → 𝒰⋆ ρ →
                 𝒰⋆ (↑⟨ c ⟩ ρ)
  cong↑⟨ c ⟩𝒰⋆ 𝓊⋆[]       = 𝓊⋆[]
  cong↑⟨ c ⟩𝒰⋆ (𝓊⋆≔ u⋆ u) = 𝓊⋆≔ (cong↑⟨ c ⟩𝒰⋆ u⋆) (cong↑⟨ c ⟩𝒰 u)

  cong↓⟨_⟩𝒰⋆ : ∀ {Γ Δ w} →
                 (c : Γ ⊇ Δ) → {ρ : w ⊩⋆ Γ} → 𝒰⋆ ρ →
                 𝒰⋆ (↓⟨ c ⟩ ρ)
  cong↓⟨ done ⟩𝒰⋆     u⋆ = 𝓊⋆[]
  cong↓⟨ step c i ⟩𝒰⋆ u⋆ = 𝓊⋆≔ (cong↓⟨ c ⟩𝒰⋆ u⋆) (conglookup𝒰 u⋆ i)

-- We also
-- need to prove the following properties about `Eq⋆` for semantic environments which basically
-- say that it doesn’t matter in which order we lift and project the substitution:

module _ {{_ : Model}} where
  aux₄₂₁⟨_⟩ : ∀ {Γ Δ A w x} →
                (c : Γ ⊇ Δ) → {ρ : w ⊩⋆ Γ} → 𝒰⋆ ρ → (i : Γ ∋ x ∷ A) (j : Δ ∋ x ∷ A) →
                Eq (lookup ρ i) (lookup (↓⟨ c ⟩ ρ) j)
  aux₄₂₁⟨ done ⟩      u⋆ i ()
  aux₄₂₁⟨ step c i′ ⟩ u⋆ i zero    = subst (λ i′ → Eq (lookup _ i) (lookup _ i′))
                                           (uniq∋ i i′)
                                           (conglookupEq (reflEq⋆ u⋆) i)
  aux₄₂₁⟨ step c i′ ⟩ u⋆ i (suc j) = aux₄₂₁⟨ c ⟩ u⋆ i j

  conglookup↑⟨_⟩Eq : ∀ {Γ A w w′ x} {ρ : w ⊩⋆ Γ} →
                       (c : w′ ⊒ w) → 𝒰⋆ ρ → (i : Γ ∋ x ∷ A) →
                       Eq (↑⟨ c ⟩ (lookup ρ i)) (lookup (↑⟨ c ⟩ ρ) i)
  conglookup↑⟨ c ⟩Eq 𝓊⋆[]       ()
  conglookup↑⟨ c ⟩Eq (𝓊⋆≔ u⋆ u) zero    = cong↑⟨ c ⟩Eq (reflEq u)
  conglookup↑⟨ c ⟩Eq (𝓊⋆≔ u⋆ u) (suc i) = conglookup↑⟨ c ⟩Eq u⋆ i

  aux₄₂₃ : ∀ {Γ Δ A w x} {{_ : T (fresh x Δ)}} {{_ : T (fresh x Γ)}} →
             (c : Γ ⊇ Δ) (c′ : [ Γ , x ∷ A ] ⊇ Δ) → {ρ : w ⊩⋆ Γ} → 𝒰⋆ ρ → {a : w ⊩ A} →
             Eq⋆ (↓⟨ c′ ⟩ [ ρ , x ≔ a ]) (↓⟨ c ⟩ ρ)
  aux₄₂₃               done       done               u⋆ = eq⋆[]
  aux₄₂₃ {x = x} {{φ}} (step c i) (step c′ zero)     u⋆ = elim⊥ (freshlem₁ x φ)
  aux₄₂₃ {x = x} {{φ}} (step c i) (step c′ (suc i′)) u⋆ =
    subst (λ i′ → Eq⋆ [ _ , _ ≔ lookup _ i′ ] _)
          (uniq∋ i i′)
          (eq⋆≔ (aux₄₂₃ {{freshlem₂ x φ}} c c′ u⋆)
                (reflEq (conglookup𝒰 u⋆ i)))

  aux₄₂₄⟨_⟩ : ∀ {Γ w} →
                (c : Γ ⊇ Γ) → {ρ : w ⊩⋆ Γ} → 𝒰⋆ ρ →
                Eq⋆ (↓⟨ c ⟩ ρ) ρ
  aux₄₂₄⟨ done ⟩     𝓊⋆[]       = eq⋆[]
  aux₄₂₄⟨ step c i ⟩ (𝓊⋆≔ u⋆ u) = eq⋆≔ (transEq⋆ (aux₄₂₃ refl⊇ c u⋆)
                                                 (aux₄₂₄⟨ refl⊇ ⟩ u⋆))
                                       (aux₄₂₁⟨ refl⊇ ⟩ (𝓊⋆≔ u⋆ u) i zero)

  aux₄₂₅⟨_⟩ : ∀ {Γ w} →
                (c : w ⊒ w) → {ρ : w ⊩⋆ Γ} → 𝒰⋆ ρ →
                Eq⋆ (↑⟨ c ⟩ ρ) ρ
  aux₄₂₅⟨ c ⟩ 𝓊⋆[]       = eq⋆[]
  aux₄₂₅⟨ c ⟩ (𝓊⋆≔ u⋆ u) = eq⋆≔ (aux₄₂₅⟨ c ⟩ u⋆) (aux₄₁₁⟨ c ⟩ u)

  aux₄₂₆ : ∀ {Γ Δ Θ w} →
             (c : Δ ⊇ Γ) (c′ : Θ ⊇ Δ) (c″ : Θ ⊇ Γ) → {ρ : w ⊩⋆ Θ} → 𝒰⋆ ρ →
             Eq⋆ (↓⟨ c ⟩ (↓⟨ c′ ⟩ ρ)) (↓⟨ c″ ⟩ ρ)
  aux₄₂₆ done        c′ done         u⋆ = eq⋆[]
  aux₄₂₆ (step c i)  c′ (step c″ i″) u⋆ = eq⋆≔ (aux₄₂₆ c c′ c″ u⋆)
                                               (symEq (aux₄₂₁⟨ c′ ⟩ u⋆ i″ i))

  aux₄₂₇ : ∀ {Γ w w′ w″} →
             (c : w′ ⊒ w) (c′ : w″ ⊒ w′) (c″ : w″ ⊒ w) → {ρ : w ⊩⋆ Γ} → 𝒰⋆ ρ →
             Eq⋆ (↑⟨ c′ ⟩ (↑⟨ c ⟩ ρ)) (↑⟨ c″ ⟩ ρ)
  aux₄₂₇ c c′ c″ 𝓊⋆[]       = eq⋆[]
  aux₄₂₇ c c′ c″ (𝓊⋆≔ u⋆ u) = eq⋆≔ (aux₄₂₇ c c′ c″ u⋆) (aux₄₁₂ c c′ c″ u)

  aux₄₂₈ : ∀ {Γ Δ w w′} →
             (c : Δ ⊇ Γ) (c′ : w′ ⊒ w) → {ρ : w ⊩⋆ Δ} → 𝒰⋆ ρ →
             Eq⋆ (↑⟨ c′ ⟩ (↓⟨ c ⟩ ρ)) (↓⟨ c ⟩ (↑⟨ c′ ⟩ ρ))
  aux₄₂₈ done       c′ u⋆ = eq⋆[]
  aux₄₂₈ (step c i) c′ u⋆ = eq⋆≔ (aux₄₂₈ c c′ u⋆) (conglookup↑⟨ c′ ⟩Eq u⋆ i)

-- These properties are used in the proofs of soundness and completeness below.


-- 4.3. The semantics of the λ-calculus
-- ------------------------------------
--
-- We define evaluation functions for proof trees and substitutions in a given environment:  (…)

module _ {{_ : Model}} where
  mutual
    ⟦_⟧ : ∀ {Γ A w} → Γ ⊢ A → w ⊩⋆ Γ → w ⊩ A
    ⟦ ν x i ⟧ ρ = lookup ρ i
    ⟦ ƛ x M ⟧ ρ = ⟦ƛ⟧ (λ c a → ⟦ M ⟧ [ ↑⟨ c ⟩ ρ , x ≔ a ])
    ⟦ M ∙ N ⟧ ρ = ⟦ M ⟧ ρ ⟦∙⟧⟨ refl⊒ ⟩ ⟦ N ⟧ ρ
    ⟦ M ▶ γ ⟧ ρ = ⟦ M ⟧ (⟦ γ ⟧ₛ ρ)

    ⟦_⟧ₛ : ∀ {Γ Δ w} → Δ ⋙ Γ → w ⊩⋆ Δ → w ⊩⋆ Γ
    ⟦ π⟨ c ⟩ ⟧ₛ        ρ = ↓⟨ c ⟩ ρ
    ⟦ γ ● γ′ ⟧ₛ        ρ = ⟦ γ ⟧ₛ (⟦ γ′ ⟧ₛ ρ)
    ⟦ [ γ , x ≔ M ] ⟧ₛ ρ = [ ⟦ γ ⟧ₛ ρ , x ≔ ⟦ M ⟧ ρ ]

