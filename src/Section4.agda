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
  reflEq 𝓊•            = eq• (λ c   → refl)
  reflEq (𝓊⊃ h₀ h₁ h₂) = eq⊃ (λ c u → reflEq (h₀ c u))

  symEq : ∀ {A w} {a a′ : w ⊩ A} → Eq a a′ → Eq a′ a
  symEq {•}     (eq• h) = eq• (λ c   → sym (h c))
  symEq {A ⊃ B} (eq⊃ h) = eq⊃ (λ c u → symEq (h c u))

  transEq : ∀ {A w} {a a′ a″ : w ⊩ A} → Eq a a′ → Eq a′ a″ → Eq a a″
  transEq {•}     (eq• h) (eq• h′) = eq• (λ c   → trans (h c) (h′ c))
  transEq {A ⊃ B} (eq⊃ h) (eq⊃ h′) = eq⊃ (λ c u → transEq (h c u) (h′ c u))

module _ {{_ : Model}} where
  ≡→Eq : ∀ {A w} {a a′ : w ⊩ A} → 𝒰 a → a ≡ a′ → Eq a a′
  ≡→Eq q refl = reflEq q

  module EqReasoning where
    infix 1 begin_
    begin_ : ∀ {A w} {a a′ : w ⊩ A} → Eq a a′ → Eq a a′
    begin e = e

    infixr 2 _Eq⟨⟩_
    _Eq⟨⟩_ : ∀ {A w} (a {a′} : w ⊩ A) → Eq a a′ → Eq a a′
    a Eq⟨⟩ e = e

    infixr 2 _Eq⟨_⟩_
    _Eq⟨_⟩_ : ∀ {A w} (a {a′ a″} : w ⊩ A) → Eq a a′ → Eq a′ a″ → Eq a a″
    a Eq⟨ e ⟩ e′ = transEq e e′

    infixr 2 _≡⟨⟩_
    _≡⟨⟩_ : ∀ {A w} (a {a′} : w ⊩ A) → Eq a a′ → Eq a a′
    a ≡⟨⟩ e = e

    infixr 2 _/_≡⟨_⟩_
    _/_≡⟨_⟩_ : ∀ {A w} (a {a′ a″} : w ⊩ A) → 𝒰 a → a ≡ a′ → Eq a′ a″ → Eq a a″
    a / u ≡⟨ e ⟩ e′ = transEq (≡→Eq u e) e′

    infix 3 _/_∎
    _/_∎ : ∀ {A w} (a : w ⊩ A) → 𝒰 a → Eq a a
    a / u ∎ = reflEq u

-- Equal uniform values can be substituted in `⟦∙⟧⟨_⟩` and the function `↑⟨_⟩` returns uniform objects
-- for uniform input and equal results for equal input.

module _ {{_ : Model}} where
  congEq⟦∙⟧⟨_⟩ : ∀ {A B w w′} →
                   (c : w′ ⊒ w) → {f f′ : w ⊩ A ⊃ B} → Eq f f′ → 𝒰 f → 𝒰 f′ →
                                   {a a′ : w′ ⊩ A} → Eq a a′ → 𝒰 a → 𝒰 a′ →
                   Eq (f ⟦∙⟧⟨ c ⟩ a) (f′ ⟦∙⟧⟨ c ⟩ a′)
  congEq⟦∙⟧⟨ c ⟩ (eq⊃ h) (𝓊⊃ h₀ h₁ h₂) (𝓊⊃ h₀′ h₁′ h₂′) e u u′ = transEq (h₁ c e u u′) (h c u′)

  congEq↑⟨_⟩ : ∀ {A w w′} →
                 (c : w′ ⊒ w) → {a a′ : w ⊩ A} → Eq a a′ →
                 Eq (↑⟨ c ⟩ a) (↑⟨ c ⟩ a′)
  congEq↑⟨ c ⟩ (eq• h) = eq• (λ c′   → h (c ◇ c′))
  congEq↑⟨ c ⟩ (eq⊃ h) = eq⊃ (λ c′ u → h (c ◇ c′) u)

  cong𝒰↑⟨_⟩ : ∀ {A w w′} →
                (c : w′ ⊒ w) → {a : w ⊩ A} → 𝒰 a →
                𝒰 (↑⟨ c ⟩ a)
  cong𝒰↑⟨ c ⟩ 𝓊•            = 𝓊•
  cong𝒰↑⟨ c ⟩ (𝓊⊃ h₀ h₁ h₂) = 𝓊⊃ (λ c′ u       → h₀ (c ◇ c′) u)
                                 (λ c′ e u u′  → h₁ (c ◇ c′) e u u′)
                                 (λ c′ c″ c‴ u → h₂ (c ◇ c′) c″ (c ◇ c‴) u)

-- We also need to prove the following properties about `Eq` and `𝒰` which are used in the proofs of
-- soundness and completeness below.

module _ {{_ : Model}} where
  aux₄₁₁⟨_⟩ : ∀ {A w} →
                (c : w ⊒ w) → {a : w ⊩ A} → 𝒰 a →
                Eq (↑⟨ c ⟩ a) a
  aux₄₁₁⟨ c ⟩ {f} 𝓊•            = eq• (λ c′       → cong (f ⟦g⟧⟨_⟩)
                                                       (id◇₁ c c′))
  aux₄₁₁⟨ c ⟩ {f} (𝓊⊃ h₀ h₁ h₂) = eq⊃ (λ c′ {a} u → ≡→Eq (h₀ (c ◇ c′) u)
                                                       (cong (f ⟦∙⟧⟨_⟩ a)
                                                         (id◇₁ c c′)))

  aux₄₁₂ : ∀ {A w w′ w″} →
             (c : w′ ⊒ w) (c′ : w″ ⊒ w′) (c″ : w″ ⊒ w) → {a : w ⊩ A} → 𝒰 a →
             Eq (↑⟨ c′ ⟩ (↑⟨ c ⟩ a)) (↑⟨ c″ ⟩ a)
  aux₄₁₂ c c′ c″ {f} 𝓊•            = eq• (λ c‴       → cong (f ⟦g⟧⟨_⟩)
                                                          (trans (assoc◇ c c′ c‴)
                                                                 (comp◇ (c ◇ c′) c‴ (c″ ◇ c‴))))
  aux₄₁₂ c c′ c″ {f} (𝓊⊃ h₀ h₁ h₂) = eq⊃ (λ c‴ {a} u → ≡→Eq (h₀ (c ◇ (c′ ◇ c‴)) u)
                                                          (cong (f ⟦∙⟧⟨_⟩ a)
                                                            (trans (assoc◇ c c′ c‴)
                                                                   (comp◇ (c ◇ c′) c‴ (c″ ◇ c‴)))))
  aux₄₁₃ : ∀ {A B w w′} →
             (c : w′ ⊒ w) (c′ : w′ ⊒ w′) → {f : w ⊩ A ⊃ B} → 𝒰 f → {a : w′ ⊩ A} → 𝒰 a →
             Eq (f ⟦∙⟧⟨ c ⟩ a) (↑⟨ c ⟩ f ⟦∙⟧⟨ c′ ⟩ a)
  aux₄₁₃ c c′ {f} (𝓊⊃ h₀ h₁ h₂) {a} u = ≡→Eq (h₀ c u)
                                          (cong (f ⟦∙⟧⟨_⟩ a)
                                            (sym (id◇₂ c c′)))


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
  ↓⟨ weak {x = x} c i ⟩⊩⋆ ρ = [ ↓⟨ c ⟩⊩⋆ ρ , x ≔ lookup ρ i ]

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

-- TODO: Attempting to refine the first cases below results in the following error:
--       An internal error has occurred. Please report this as a bug.
--       Location of the error: src/full/Agda/TypeChecking/Substitute.hs:90

module _ {{_ : Model}} where
  reflEq⋆ : ∀ {Γ w} {ρ : w ⊩⋆ Γ} → 𝒰⋆ ρ → Eq⋆ ρ ρ
  reflEq⋆ 𝓊⋆[]       = eq⋆[]
  reflEq⋆ (𝓊⋆≔ u⋆ u) = eq⋆≔ (reflEq⋆ u⋆) (reflEq u)

  symEq⋆ : ∀ {Γ w} {ρ ρ′ : w ⊩⋆ Γ} → Eq⋆ ρ ρ′ → Eq⋆ ρ′ ρ
  symEq⋆ eq⋆[]       = eq⋆[]
  symEq⋆ (eq⋆≔ e⋆ e) = eq⋆≔ (symEq⋆ e⋆) (symEq e)

  transEq⋆ : ∀ {Γ w} {ρ ρ′ ρ″ : w ⊩⋆ Γ} → Eq⋆ ρ ρ′ → Eq⋆ ρ′ ρ″ → Eq⋆ ρ ρ″
  transEq⋆ eq⋆[]       eq⋆[]         = eq⋆[]
  transEq⋆ (eq⋆≔ e⋆ e) (eq⋆≔ e⋆′ e′) = eq⋆≔ (transEq⋆ e⋆ e⋆′) (transEq e e′)

module _ {{_ : Model}} where
  ≡→Eq⋆ : ∀ {Γ w} {ρ ρ′ : w ⊩⋆ Γ} → 𝒰⋆ ρ → ρ ≡ ρ′ → Eq⋆ ρ ρ′
  ≡→Eq⋆ u⋆ refl = reflEq⋆ u⋆

  module Eq⋆Reasoning where
    infix 1 begin_
    begin_ : ∀ {Γ w} {ρ ρ′ : w ⊩⋆ Γ} → Eq⋆ ρ ρ′ → Eq⋆ ρ ρ′
    begin e⋆ = e⋆

    infixr 2 _Eq⟨⟩_
    _Eq⟨⟩_ : ∀ {Γ w} (ρ {ρ′} : w ⊩⋆ Γ) → Eq⋆ ρ ρ′ → Eq⋆ ρ ρ′
    ρ Eq⟨⟩ e⋆ = e⋆

    infixr 2 _Eq⟨_⟩_
    _Eq⟨_⟩_ : ∀ {Γ w} (ρ {ρ′ ρ″} : w ⊩⋆ Γ) → Eq⋆ ρ ρ′ → Eq⋆ ρ′ ρ″ → Eq⋆ ρ ρ″
    ρ Eq⟨ e⋆ ⟩ e⋆′ = transEq⋆ e⋆ e⋆′

    infixr 2 _≡⟨⟩_
    _≡⟨⟩_ : ∀ {Γ w} (ρ {ρ′} : w ⊩⋆ Γ) → Eq⋆ ρ ρ′ → Eq⋆ ρ ρ′
    ρ ≡⟨⟩ e⋆ = e⋆

    infixr 2 _/_≡⟨_⟩_
    _/_≡⟨_⟩_ : ∀ {Γ w} (ρ {ρ′ ρ″} : w ⊩⋆ Γ) → 𝒰⋆ ρ → ρ ≡ ρ′ → Eq⋆ ρ′ ρ″ → Eq⋆ ρ ρ″
    ρ / u⋆ ≡⟨ e⋆ ⟩ e⋆′ = transEq⋆ (≡→Eq⋆ u⋆ e⋆) e⋆′

    infix 3 _/_∎
    _/_∎ : ∀ {Γ w} (ρ : w ⊩⋆ Γ) → 𝒰⋆ ρ → Eq⋆ ρ ρ
    ρ / u⋆ ∎ = reflEq⋆ u⋆

-- We can substitute equal semantic environments in `lookup`, `↑⟨_⟩`, `↓⟨_⟩`
-- and the result of applying these functions to uniform environments is also uniform.

module _ {{_ : Model}} where
  congEq⋆lookup : ∀ {Γ A w x} →
                    {ρ ρ′ : w ⊩⋆ Γ} → Eq⋆ ρ ρ′ → (i : Γ ∋ x ∷ A) →
                    Eq (lookup ρ i) (lookup ρ′ i)
  congEq⋆lookup eq⋆[]       ()
  congEq⋆lookup (eq⋆≔ e⋆ e) zero    = e
  congEq⋆lookup (eq⋆≔ e⋆ e) (suc i) = congEq⋆lookup e⋆ i

  congEq⋆↑⟨_⟩ : ∀ {Γ w w′} →
                  (c : w′ ⊒ w) → {ρ ρ′ : w ⊩⋆ Γ} → Eq⋆ ρ ρ′ →
                  Eq⋆ (↑⟨ c ⟩ ρ) (↑⟨ c ⟩ ρ′)
  congEq⋆↑⟨ c ⟩ eq⋆[]       = eq⋆[]
  congEq⋆↑⟨ c ⟩ (eq⋆≔ e⋆ e) = eq⋆≔ (congEq⋆↑⟨ c ⟩ e⋆) (congEq↑⟨ c ⟩ e)

  congEq⋆↓⟨_⟩ : ∀ {Γ Δ w} →
                  (c : Γ ⊇ Δ) → {ρ ρ′ : w ⊩⋆ Γ} → Eq⋆ ρ ρ′ →
                  Eq⋆ (↓⟨ c ⟩ ρ) (↓⟨ c ⟩ ρ′)
  congEq⋆↓⟨ done ⟩     e⋆ = eq⋆[]
  congEq⋆↓⟨ weak c i ⟩ e⋆ = eq⋆≔ (congEq⋆↓⟨ c ⟩ e⋆) (congEq⋆lookup e⋆ i)

  cong𝒰⋆lookup : ∀ {Γ A w x} →
                   {ρ : w ⊩⋆ Γ} → 𝒰⋆ ρ → (i : Γ ∋ x ∷ A) →
                   𝒰 (lookup ρ i)
  cong𝒰⋆lookup 𝓊⋆[]       ()
  cong𝒰⋆lookup (𝓊⋆≔ u⋆ u) zero    = u
  cong𝒰⋆lookup (𝓊⋆≔ u⋆ u) (suc i) = cong𝒰⋆lookup u⋆ i

  cong𝒰⋆↑⟨_⟩ : ∀ {Γ w w′} →
                 (c : w′ ⊒ w) → {ρ : w ⊩⋆ Γ} → 𝒰⋆ ρ →
                 𝒰⋆ (↑⟨ c ⟩ ρ)
  cong𝒰⋆↑⟨ c ⟩ 𝓊⋆[]       = 𝓊⋆[]
  cong𝒰⋆↑⟨ c ⟩ (𝓊⋆≔ u⋆ u) = 𝓊⋆≔ (cong𝒰⋆↑⟨ c ⟩ u⋆) (cong𝒰↑⟨ c ⟩ u)

  cong𝒰⋆↓⟨_⟩ : ∀ {Γ Δ w} →
                 (c : Γ ⊇ Δ) → {ρ : w ⊩⋆ Γ} → 𝒰⋆ ρ →
                 𝒰⋆ (↓⟨ c ⟩ ρ)
  cong𝒰⋆↓⟨ done ⟩     u⋆ = 𝓊⋆[]
  cong𝒰⋆↓⟨ weak c i ⟩ u⋆ = 𝓊⋆≔ (cong𝒰⋆↓⟨ c ⟩ u⋆) (cong𝒰⋆lookup u⋆ i)

-- We also
-- need to prove the following properties about `Eq⋆` for semantic environments which basically
-- say that it doesn’t matter in which order we lift and project the substitution:

module _ {{_ : Model}} where
  postulate
    aux₄₂₁⟨_⟩ : ∀ {Γ Δ A w x} →
                  (c : Γ ⊇ Δ) → {ρ : w ⊩⋆ Γ} → 𝒰⋆ ρ → (i : Γ ∋ x ∷ A) (j : Δ ∋ x ∷ A) →
                  Eq (lookup ρ i) (lookup (↓⟨ c ⟩ ρ) j)

  postulate
    aux₄₂₂⟨_⟩ : ∀ {Γ A w w′ x} →
                  (c : w′ ⊒ w) → {ρ : w ⊩⋆ Γ} → 𝒰⋆ ρ → (i : Γ ∋ x ∷ A) →
                  Eq (↑⟨ c ⟩ (lookup ρ i)) (lookup (↑⟨ c ⟩ ρ) i)

  postulate
    aux₄₂₃ : ∀ {Γ Δ A w x} {{_ : T (fresh x Γ)}} {{_ : T (fresh x Δ)}} →
               (c : Γ ⊇ Δ) (c′ : [ Γ , x ∷ A ] ⊇ Δ) → {ρ : w ⊩⋆ Γ} → 𝒰⋆ ρ → {a : w ⊩ A} →
               Eq⋆ (↓⟨ c′ ⟩ [ ρ , x ≔ a ]) (↓⟨ c ⟩ ρ)

  postulate
    aux₄₂₄⟨_⟩ : ∀ {Γ w} →
                  (c : Γ ⊇ Γ) → {ρ : w ⊩⋆ Γ} → 𝒰⋆ ρ →
                  Eq⋆ (↓⟨ c ⟩ ρ) ρ

  aux₄₂₅⟨_⟩ : ∀ {Γ w} →
                (c : w ⊒ w) → {ρ : w ⊩⋆ Γ} → 𝒰⋆ ρ →
                Eq⋆ (↑⟨ c ⟩ ρ) ρ
  aux₄₂₅⟨ c ⟩ 𝓊⋆[]       = eq⋆[]
  aux₄₂₅⟨ c ⟩ (𝓊⋆≔ u⋆ u) = eq⋆≔ (aux₄₂₅⟨ c ⟩ u⋆) (aux₄₁₁⟨ c ⟩ u)

  postulate
    aux₄₂₆ : ∀ {Γ Δ Θ w} →
               (c : Δ ⊇ Γ) (c′ : Θ ⊇ Δ) (c″ : Θ ⊇ Γ) → {ρ : w ⊩⋆ Θ} → 𝒰⋆ ρ →
               Eq⋆ (↓⟨ c ⟩ (↓⟨ c′ ⟩ ρ)) (↓⟨ c″ ⟩ ρ)

  aux₄₂₇ : ∀ {Γ w w′ w″} →
             (c : w′ ⊒ w) (c′ : w″ ⊒ w′) (c″ : w″ ⊒ w) → {ρ : w ⊩⋆ Γ} → 𝒰⋆ ρ →
             Eq⋆ (↑⟨ c′ ⟩ (↑⟨ c ⟩ ρ)) (↑⟨ c″ ⟩ ρ)
  aux₄₂₇ c c′ c″ 𝓊⋆[]       = eq⋆[]
  aux₄₂₇ c c′ c″ (𝓊⋆≔ u⋆ u) = eq⋆≔ (aux₄₂₇ c c′ c″ u⋆) (aux₄₁₂ c c′ c″ u)

  postulate
    aux₄₂₈ : ∀ {Γ Δ w w′} →
               (c : Δ ⊇ Γ) (c′ : w′ ⊒ w) → {ρ : w ⊩⋆ Δ} → 𝒰⋆ ρ →
               Eq⋆ (↑⟨ c′ ⟩ (↓⟨ c ⟩ ρ)) (↓⟨ c ⟩ (↑⟨ c′ ⟩ ρ))

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


-- 4.4. The inversion function
-- ---------------------------
--
-- It is possible to go from the semantics back to the proof trees by an inversion function, `reify`
-- that, given a semantic object in a particular Kripke model, returns a proof tree.  The particular
-- Kripke model that we choose has contexts as possible worlds, the order on contexts as the
-- order on worlds, and `_⊢ •` as `𝒢`.  (…)

instance
  canon : Model
  canon = record
    { 𝒲      = 𝒞
    ; _⊒_    = _⊇_
    ; refl⊒ = refl⊇
    ; _◇_    = _○_
    ; uniq⊒ = uniq⊇
    ; 𝒢      = _⊢ •
    }

-- In order to define the inversion function we need to be able to choose a unique fresh
-- name given a context.  We suppose a function `gensym : 𝒞 → Name` and a proof of
-- `T (fresh (gensym Γ) Γ)` which proves that `gensym` returns a fresh variable.  Note that `gensym`
-- is a function taking a context as an argument and it hence always returns the same variable
-- for a given context.

-- TODO: Can we do better than this?
postulate
  gensym : (Γ : 𝒞) → Σ Name (λ x → T (fresh x Γ))

-- The function `reify` is quite intricate.  (…)
--
-- The function `reify` is mutually defined with `val`, which given a function from a context
-- extension to a proof tree returns a semantic object as result.
--
-- We define an abbreviation for the semantic object corresponding to a variable, `val-ν`.
--
-- The functions `reify` and `val` are both defined by induction on the type:

mutual
  reify : ∀ {A Γ} → Γ ⊩ A → Γ ⊢ A
  reify {•}     {Γ} f = f ⟦g⟧⟨ refl⊇ ⟩
  reify {A ⊃ B} {Γ} f = let x , φ = gensym Γ in
                        let instance _ = φ in
                        ƛ x (reify (f ⟦∙⟧⟨ weak⊇ ⟩ val-ν zero))

  val : ∀ {A Γ} → (∀ {Δ} → Δ ⊇ Γ → Δ ⊢ A) → Γ ⊩ A
  val {•}     f = ⟦𝒢⟧ f
  val {A ⊃ B} f = ⟦ƛ⟧ (λ c a → val (λ c′ → f (c ○ c′) ∙ reify (↑⟨ c′ ⟩ a)))

  val-ν : ∀ {x Γ A} → Γ ∋ x ∷ A → Γ ⊩ A
  val-ν {x} i = val (λ c → ν x (↑⟨ c ⟩ i))

-- We also have that if two semantic objects in a Kripke model are extensionally equal, then
-- the result of applying the inversion function to them is intensionally equal.  To prove this
-- we first have to show the following two lemmas:

aux₄₄₁ : ∀ {A Γ} → (f f′ : ∀ {Δ} → Δ ⊇ Γ → Δ ⊢ A) → (∀ {Δ} → (c : Δ ⊇ Γ) → f c ≡ f′ c) →
           Eq (val f) (val f′)
aux₄₄₁ {•}     f f′ h = eq• (λ c       → h c)
aux₄₄₁ {A ⊃ B} f f′ h = eq⊃ (λ c {a} u → aux₄₄₁ (λ c′ → f (c ○ c′) ∙ reify (↑⟨ c′ ⟩ a))
                                                 (λ c′ → f′ (c ○ c′) ∙ reify (↑⟨ c′ ⟩ a))
                                                 (λ c′ → cong (_∙ reify (↑⟨ c′ ⟩ a))
                                                            (h (c ○ c′))))

aux₄₄₂⟨_⟩ : ∀ {A Γ Δ} → (c : Δ ⊇ Γ) (f : (∀ {Δ} → Δ ⊇ Γ → Δ ⊢ A)) →
              Eq (↑⟨ c ⟩ (val f)) (val (λ c′ → f (c ○ c′)))
aux₄₄₂⟨_⟩ {•}     c f = eq• (λ c′       → cong f refl)
aux₄₄₂⟨_⟩ {A ⊃ B} c f = eq⊃ (λ c′ {a} u → aux₄₄₁ (λ c″ → f ((c ○ c′) ○ c″) ∙ reify (↑⟨ c″ ⟩ a))
                                                  (λ c″ → f (c ○ (c′ ○ c″)) ∙ reify (↑⟨ c″ ⟩ a))
                                                  (λ c″ → cong (_∙ reify (↑⟨ c″ ⟩ a))
                                                             (cong f
                                                               (sym (assoc○ c c′ c″)))))

-- Both lemmas are proved by induction on the type and they are used in order to prove the
-- following theorem,
-- which is shown mutually with a lemma
-- which states that `val` returns a uniform semantic object.  Both the theorem and the lemma
-- are proved by induction on the type.

-- Theorem 1.
mutual
  thm₁ : ∀ {Γ A} {a a′ : Γ ⊩ A} → Eq a a′ → reify a ≡ reify a′
  thm₁ {Γ} (eq• h) = h refl⊇
  thm₁ {Γ} (eq⊃ h) = let x , φ = gensym Γ in
                     let instance _ = φ in
                     cong (ƛ x)
                       (thm₁ (h weak⊇ (aux₄₄₃-ν zero)))

  aux₄₄₃-ν : ∀ {x Γ A} → (i : Γ ∋ x ∷ A) → 𝒰 (val-ν i)
  aux₄₄₃-ν {x} i = aux₄₄₃ (λ c → ν x (↑⟨ c ⟩ i))

  aux₄₄₃ : ∀ {A Γ} → (f : ∀ {Δ} → Δ ⊇ Γ → Δ ⊢ A) → 𝒰 (val f)
  aux₄₄₃ {•}     f = 𝓊•
  aux₄₄₃ {A ⊃ B} f =
    𝓊⊃ (λ c {a} u           → aux₄₄₃ (λ c′ → f (c ○ c′) ∙ reify (↑⟨ c′ ⟩ a)))
       (λ c {a} {a′} e u u′ → aux₄₄₁ (λ c′ → f (c ○ c′) ∙ reify (↑⟨ c′ ⟩ a))
                                      (λ c′ → f (c ○ c′) ∙ reify (↑⟨ c′ ⟩ a′))
                                      (λ c′ → cong (f (c ○ c′) ∙_)
                                                 (thm₁ (congEq↑⟨ c′ ⟩ e))))
       (λ c c′ c″ {a} u     → transEq (aux₄₄₂⟨ c′ ⟩ (λ c‴ → f (c ○ c‴) ∙ reify (↑⟨ c‴ ⟩ a)))
                                       (aux₄₄₁ (λ c‴ → f (c ○ (c′ ○ c‴)) ∙ reify (↑⟨ c′ ○ c‴ ⟩ a))
                                               (λ c‴ → f (c″ ○ c‴) ∙ reify (↑⟨ c‴ ⟩ (↑⟨ c′ ⟩ a)))
                                               (λ c‴ → cong² _∙_
                                                          (cong f
                                                            (trans (assoc○ c c′ c‴)
                                                                   (comp○ (c ○ c′) c‴ (c″ ○ c‴))))
                                                          (thm₁ (symEq (aux₄₁₂ c′ c‴ (c′ ○ c‴) u))))))

-- We are now ready to define the function that given a proof tree computes its normal form.
-- For this we define the identity environment `proj⟨_⟩⊩⋆` which to each variable
-- in the context `Γ` associates the corresponding value of the variable in `Δ` (`val-ν` gives the
-- value of this variable).  The normalisation function, `nf`, is defined as the composition of the
-- evaluation function and `reify`.  This function is similar to the normalisation algorithm given
-- by Berger [3]; one difference is our use of Kripke models to deal with reduction under `λ`.
-- One other difference is that, since we use explicit contexts, we can use the context to find
-- the fresh names in the `reify` function.

proj⟨_⟩⊩⋆ : ∀ {Γ Δ} → Δ ⊇ Γ → Δ ⊩⋆ Γ
proj⟨ done ⟩⊩⋆             = []
proj⟨ weak {x = x} c i ⟩⊩⋆ = [ proj⟨ c ⟩⊩⋆ , x ≔ val-ν i ]

refl⊩⋆ : ∀ {Γ} → Γ ⊩⋆ Γ
refl⊩⋆ = proj⟨ refl⊇ ⟩⊩⋆

-- The computation of the normal form is done by computing the semantics of the proof
-- tree in the identity environment and then inverting the result:

nf : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ A
nf M = reify (⟦ M ⟧ refl⊩⋆)

-- We know by Theorem 1 that `nf` returns the same result when applied to two proof trees
-- having the same semantics:

-- Corollary 1.
cor₁ : ∀ {Γ A} → (M M′ : Γ ⊢ A) → Eq (⟦ M ⟧ refl⊩⋆) (⟦ M′ ⟧ refl⊩⋆) →
         nf M ≡ nf M′
cor₁ M M′ = thm₁


-- 4.5. Soundness and completeness of proof trees
-- ----------------------------------------------
--
-- We have in fact already shown soundness and completeness of the calculus of proof trees.
--
-- The evaluation function, `⟦_⟧`, for proof trees corresponds via the Curry-Howard isomorphism
-- to a proof of the soundness theorem of minimal logic with respect to Kripke models.
-- The function is defined by pattern matching which corresponds to a proof by case analysis
-- of the proof trees.
--
-- The inversion function `reify` is, again via the Curry-Howard isomorphism, a proof of the
-- completeness theorem of minimal logic with respect to a particular Kripke model where
-- the worlds are contexts.


-- 4.6. Completeness of the conversion rules for proof trees
-- ---------------------------------------------------------
--
-- In order to prove that the set of conversion rules is complete, i.e.,
-- `Eq (⟦ M ⟧ refl⊩⋆) (⟦ M′ ⟧ refl⊩⋆)` implies `M ≅ M′`, we must first prove Theorem 2: `M ≅ nf M`.
--
-- To prove the theorem we define a Kripke logical relation [15, 18]
-- which corresponds to Tait’s computability predicate.
--
-- A proof tree of base type is intuitively `CV`-related to a semantic object of base type if
-- they are convertible with each other.  (…)
--
-- A proof tree of function type, `A ⊃ B`, is intuitively `CV`-related to a semantic object of the
-- same type if they send `CV`-related proof trees and objects of type `A` to `CV`-related proof
-- trees and objects of type `B`.  (…)

data CV : ∀ {Γ A} → Γ ⊢ A → Γ ⊩ A → Set where
  cv• : ∀ {Γ} {M : Γ ⊢ •} {f : Γ ⊩ •} →
          (∀ {Δ} → (c : Δ ⊇ Γ) → M ▶ π⟨ c ⟩ ≅ f ⟦g⟧⟨ c ⟩) →
          CV M f
  cv⊃ : ∀ {Γ A B} {M : Γ ⊢ A ⊃ B} {f : Γ ⊩ A ⊃ B} →
          (∀ {Δ N a} → (c : Δ ⊇ Γ) → CV N a → CV ((M ▶ π⟨ c ⟩) ∙ N) (f ⟦∙⟧⟨ c ⟩ a)) →
          CV M f

-- The idea of this predicate is that we can show that if `CV M a` then `M ≅ reify a`, hence
-- if we show that `CV M (⟦ M ⟧ refl⊩⋆)`, we have a proof of Theorem 2.
--
-- Correspondingly for the environment we define:  (…)

data CV⋆ : ∀ {Γ Δ} → Δ ⋙ Γ → Δ ⊩⋆ Γ → Set where
  cv[] : ∀ {Γ} →
           {γ : Γ ⋙ []} →
           CV⋆ γ []
  cv≔  : ∀ {Γ Δ A x} {{_ : T (fresh x Γ)}}
           {γ : Δ ⋙ [ Γ , x ∷ A ]} {c : [ Γ , x ∷ A ] ⊇ Γ} {ρ : Δ ⊩⋆ Γ} {a : Δ ⊩ A} →
           CV⋆ (π⟨ c ⟩ ● γ) ρ → CV (ν x zero ▶ γ) a →
           CV⋆ γ [ ρ , x ≔ a ]

-- In order to prove Lemma 8 below we need to prove the following properties about `CV`:

aux₄₆₁ : ∀ {Γ A} {M M′ : Γ ⊢ A} {a : Γ ⊩ A} →
           M ≅ M′ → CV M′ a →
           CV M a
aux₄₆₁ M≅M′ (cv• h) = cv• (λ c     → trans≅ (cong≅▶ M≅M′ refl≅ₛ) (h c))
aux₄₆₁ M≅M′ (cv⊃ h) = cv⊃ (λ c cv′ → aux₄₆₁ (cong≅∙ (cong≅▶ M≅M′ refl≅ₛ) refl≅) (h c cv′))

aux₄₆₂ : ∀ {Γ Δ} {γ γ′ : Δ ⋙ Γ} {ρ : Δ ⊩⋆ Γ} →
           γ ≅ₛ γ′ → CV⋆ γ′ ρ →
           CV⋆ γ ρ
aux₄₆₂ γ≅ₛγ′ cv[]         = cv[]
aux₄₆₂ γ≅ₛγ′ (cv≔ cv⋆ cv) = cv≔ (aux₄₆₂ (cong≅ₛ● refl≅ₛ γ≅ₛγ′) cv⋆) (aux₄₆₁ (cong≅▶ refl≅ γ≅ₛγ′) cv)

aux₄₆₃⟨_⟩ : ∀ {Γ Δ A} {M : Γ ⊢ A} {a : Γ ⊩ A} →
              (c : Δ ⊇ Γ) → CV M a →
              CV (M ▶ π⟨ c ⟩) (↑⟨ c ⟩ a)
aux₄₆₃⟨ c ⟩ (cv• h) = cv• (λ c′     → trans≅ (trans≅ (conv≅₇ _ _ _)
                                                      (cong≅▶ refl≅ (conv≅ₛ₄ _ _ _)))
                                              (h (c ○ c′)))
aux₄₆₃⟨ c ⟩ (cv⊃ h) = cv⊃ (λ c′ cv′ → aux₄₆₁ (cong≅∙ (trans≅ (conv≅₇ _ _ _)
                                                              (cong≅▶ refl≅ (conv≅ₛ₄ _ _ _)))
                                                      refl≅)
                                              (h (c ○ c′) cv′))

aux₄₆₄ : ∀ {Γ Δ A x} {γ : Δ ⋙ Γ} {ρ : Δ ⊩⋆ Γ} →
           CV⋆ γ ρ → (i : Γ ∋ x ∷ A) →
           CV (ν x i ▶ γ) (lookup ρ i)
aux₄₆₄ cv[]         ()
aux₄₆₄ (cv≔ cv⋆ cv) zero    = cv
aux₄₆₄ (cv≔ cv⋆ cv) (suc i) = aux₄₆₁ (trans≅ (cong≅▶ (sym≅ (conv≅₄ _ _ _)) refl≅ₛ)
                                             (conv≅₇ _ _ _))
                                     (aux₄₆₄ cv⋆ i)

aux₄₆₅⟨_⟩ : ∀ {Γ Δ Θ} {γ : Δ ⋙ Γ} {ρ : Δ ⊩⋆ Γ} →
              (c : Θ ⊇ Δ) → CV⋆ γ ρ →
              CV⋆ (γ ● π⟨ c ⟩) (↑⟨ c ⟩ ρ)
aux₄₆₅⟨ c ⟩ cv[]         = cv[]
aux₄₆₅⟨ c ⟩ (cv≔ cv⋆ cv) = cv≔ (aux₄₆₂ (sym≅ₛ (conv≅ₛ₁ _ _ _)) (aux₄₆₅⟨ c ⟩ cv⋆))
                               (aux₄₆₁ (sym≅ (conv≅₇ _ _ _)) (aux₄₆₃⟨ c ⟩ cv))

aux₄₆₆⟨_⟩ : ∀ {Γ Δ Θ} {γ : Δ ⋙ Γ} {ρ : Δ ⊩⋆ Γ} →
              (c : Γ ⊇ Θ) → CV⋆ γ ρ →
              CV⋆ (π⟨ c ⟩ ● γ) (↓⟨ c ⟩ ρ)
aux₄₆₆⟨ done ⟩     cv⋆ = cv[]
aux₄₆₆⟨ weak c i ⟩ cv⋆ = cv≔ {c = weak⊇}
                             (aux₄₆₂ (trans≅ₛ (sym≅ₛ (conv≅ₛ₁ _ _ _))
                                              (cong≅ₛ● (conv≅ₛ₄ _ _ _) refl≅ₛ))
                                     (aux₄₆₆⟨ c ⟩ cv⋆))
                             (aux₄₆₁ (trans≅ (sym≅ (conv≅₇ _ _ _))
                                             (cong≅▶ (conv≅₄ _ _ _) refl≅ₛ))
                                     (aux₄₆₄ cv⋆ i))

-- Now we are ready to prove that if `γ` and `ρ` are `CV`-related, then `M ▶ γ` and `⟦ M ⟧ ρ` are
-- `CV`-related.  This lemma corresponds to Tait’s lemma saying that each term is computable
-- under substitution.  We prove the lemma
-- mutually with a corresponding lemma for substitutions.

-- Lemma 8.
mutual
  postulate
    lem₈ : ∀ {Γ Δ A} {γ : Δ ⋙ Γ} {ρ : Δ ⊩⋆ Γ} →
             (M : Γ ⊢ A) → CV⋆ γ ρ →
             CV (M ▶ γ) (⟦ M ⟧ ρ)

  postulate
    aux₄₆₇ : ∀ {Γ Δ Θ} {γ′ : Θ ⋙ Δ} {ρ : Θ ⊩⋆ Δ} →
               (γ : Δ ⋙ Γ) → CV⋆ γ′ ρ →
               CV⋆ (γ ● γ′) (⟦ γ ⟧ₛ ρ)

-- Both lemmas are proved by induction on the proof trees using the lemmas above.
--
-- Lemma 9 is shown mutually with a corresponding lemma for `val`:

-- Lemma 9.
mutual
  postulate
    lem₉ : ∀ {Γ A} {M : Γ ⊢ A} {a : Γ ⊩ A} →
             CV M a →
             M ≅ reify a

  postulate
    aux₄₆₈⟨_⟩ : ∀ {Γ Δ A} {M : Γ ⊢ A} {f : ∀ {Δ} → Δ ⊇ Γ → Δ ⊢ A} →
                  (c : Δ ⊇ Γ) → M ▶ π⟨ c ⟩ ≅ f c →
                  CV M (val f)

-- In order to prove Theorem 2 we also prove that `CV π⟨ c ⟩ val-ρ⟨ c ⟩`; then by this, Lemma 8
-- and Lemma 9 we get that `M ▶ π⟨ c ⟩ ≅ nf M`, where `c : Γ ⊇ Γ`.  Using the conversion rule
-- `M ≅ M ▶ π⟨ c ⟩` for `c : Γ ⊇ Γ` we get by transitivity of conversion of `_≅_` that `M ≅ nf M`.

postulate
  proj⟨_⟩CV⋆ : ∀ {Γ Δ} → (c : Δ ⊇ Γ) → CV⋆ π⟨ c ⟩ proj⟨ c ⟩⊩⋆

reflCV⋆ : ∀ {Γ} → CV⋆ π⟨ refl⊇ ⟩ (refl⊩⋆ {Γ})
reflCV⋆ = proj⟨ refl⊇ ⟩CV⋆

postulate
  aux₄₆₉⟨_⟩ : ∀ {Γ A} →
                (c : Γ ⊇ Γ) (M : Γ ⊢ A) →
                M ▶ π⟨ c ⟩ ≅ nf M

-- Theorem 2.
postulate
  thm₂ : ∀ {Γ A} → (M : Γ ⊢ A) →
           M ≅ nf M

-- It is now easy to prove the completeness theorem:

-- Theorem 3.
postulate
  thm₃ : ∀ {Γ A} → (M M′ : Γ ⊢ A) → Eq (⟦ M ⟧ refl⊩⋆) (⟦ M′ ⟧ refl⊩⋆) →
           M ≅ M′


-- 4.7. Completeness of the conversion rules for substitutions
-- -----------------------------------------------------------
--
-- The proof of completeness above does not imply that the set of conversion rules for substitutions
-- is complete.  In order to prove the completeness of conversion rules for the substitutions
-- we define an inversion function for semantic environments:  (…)

reify⋆ : ∀ {Γ Δ} → Δ ⊩⋆ Γ → Δ ⋙ Γ
reify⋆ []            = π⟨ done ⟩
reify⋆ [ ρ , x ≔ a ] = [ reify⋆ ρ , x ≔ reify a ]

-- The normalisation function on substitutions is defined as the inversion of the semantics
-- of the substitution in the identity environment.

nf⋆ : ∀ {Δ Γ} → Δ ⋙ Γ → Δ ⋙ Γ
nf⋆ γ = reify⋆ (⟦ γ ⟧ₛ refl⊩⋆)

-- The completeness result for substitutions follows in the same way as for proof trees, i.e.,
-- we must prove that `γ ≅ₛ nf γ`.

postulate
  thm₂ₛ : ∀ {Γ Δ} → (γ : Δ ⋙ Γ) →
            γ ≅ₛ nf⋆ γ

postulate
  thm₃ₛ : ∀ {Γ Δ} → (γ γ′ : Δ ⋙ Γ) → Eq⋆ (⟦ γ ⟧ₛ refl⊩⋆) (⟦ γ′ ⟧ₛ refl⊩⋆) →
            γ ≅ₛ γ′


-- 4.8. Soundness of the conversion rules
-- --------------------------------------
--
-- In order to prove the soundness of the conversion rules we first have to show:

postulate
  aux₄₈₁ : ∀ {Γ Δ A} →
             (M : Γ ⊢ A) → {ρ : Δ ⊩⋆ Γ} → 𝒰⋆ ρ →
             𝒰 (⟦ M ⟧ ρ)

postulate
  aux₄₈₂ : ∀ {Γ Δ} →
             (γ : Γ ⋙ Δ) → {ρ : Δ ⊩⋆ Γ} → 𝒰⋆ ρ →
             𝒰⋆ (⟦ γ ⟧ₛ ρ)

postulate
  aux₄₈₃ : ∀ {Γ Δ A} →
             {M : Γ ⊢ A} → {ρ ρ′ : Δ ⊩⋆ Γ} → Eq⋆ ρ ρ′ →
             Eq (⟦ M ⟧ ρ) (⟦ M ⟧ ρ′)

postulate
  aux₄₈₄ : ∀ {Γ Δ} →
             {γ : Γ ⋙ Δ} → {ρ ρ′ : Δ ⊩⋆ Γ} → Eq⋆ ρ ρ′ →
             Eq⋆ (⟦ γ ⟧ₛ ρ) (⟦ γ ⟧ₛ ρ′)

postulate
  aux₄₈₅⟨_⟩ : ∀ {Γ Δ Θ A} →
                (c : Θ ⊇ Δ) (M : Γ ⊢ A) (ρ : Δ ⊩⋆ Γ) →
                Eq (↑⟨ c ⟩ (⟦ M ⟧ ρ)) (⟦ M ⟧ (↑⟨ c ⟩ ρ))

postulate
  aux₄₈₆⟨_⟩ : ∀ {Γ Δ Θ} →
                (c : Θ ⊇ Δ) (γ : Γ ⋙ Δ) (ρ : Δ ⊩⋆ Γ) →
                Eq⋆ (↑⟨ c ⟩ (⟦ γ ⟧ₛ ρ)) (⟦ γ ⟧ₛ (↑⟨ c ⟩ ρ))

-- The soundness theorem is shown mutually with a corresponding lemma for substitutions:

-- Theorem 4.
mutual
  postulate
    thm₄ : ∀ {Γ A w} {M M′ : Γ ⊢ A} → M ≅ M′ → (ρ : w ⊩⋆ Γ) →
             Eq (⟦ M ⟧ ρ) (⟦ M′ ⟧ ρ)

  postulate
    thm₄ₛ : ∀ {Γ Δ w} {γ γ′ : Γ ⋙ Δ} → γ ≅ₛ γ′ → (ρ : w ⊩⋆ Γ) →
              Eq⋆ (⟦ γ ⟧ₛ ρ) (⟦ γ′ ⟧ₛ ρ)

-- They are both shown by induction on the rules of conversion.  Notice that the soundness
-- result holds in any Kripke model.


-- 4.9. Decision algorithm for conversion
-- --------------------------------------
--
-- We now have a decision algorithm for testing convertibility between proof trees: compute
-- the normal form and check if they are exactly the same.  This decision algorithm is correct,
-- since by Theorem 2 we have `M ≅ nf M` and `M′ ≅ nf M′` and, by hypothesis, `nf M ≡ nf M′`,
-- we get by transitivity of `_≅_`, that `M ≅ M′`.

-- Theorem 5.
thm₅ : ∀ {Γ A} → (M M′ : Γ ⊢ A) → nf M ≡ nf M′ → M ≅ M′
thm₅ M M′ p =
  begin
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

-- The decision algorithm is also complete since by Theorem 4 and the hypothesis, `M ≅ M′`, we get
-- `Eq (⟦ M ⟧ refl⊩⋆) (⟦ N ⟧ refl⊩⋆)` and by Corollary 1 we get `nf M ≡ nf N`.

-- Theorem 6.
thm₆ : ∀ {Γ A} → (M M′ : Γ ⊢ A) → M ≅ M′ → nf M ≡ nf M′
thm₆ M M′ p = cor₁ M M′ (thm₄ p refl⊩⋆)
