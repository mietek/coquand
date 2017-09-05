module Section3 where

open import Section1 public


-- 3. The calculus of proof trees
-- ==============================
--
-- We define the set of proof trees of implicational logic in the ordinary style à la Church,
-- except that we use explicit substitutions.


-- 3.1. Definition of types
-- ------------------------
--
-- The types we have are base type and function types.  The set of types `𝒯 : Set` is introduced
-- by:

infixr 7 _⊃_
data 𝒯 : Set where
  •   : 𝒯
  _⊃_ : 𝒯 → 𝒯 → 𝒯

-- Types are denoted by `A`, `B`.  (…)
--
-- We write `•` for the base type and `A ⊃ B` for the function type.

module _ where
  inj⊃₁ : ∀ {A A′ B B′} → A ⊃ B ≡ A′ ⊃ B′ → A ≡ A′
  inj⊃₁ refl = refl

  inj⊃₂ : ∀ {A A′ B B′} → A ⊃ B ≡ A′ ⊃ B′ → B ≡ B′
  inj⊃₂ refl = refl

  _≟𝒯_ : (A A′ : 𝒯) → Dec (A ≡ A′)
  •       ≟𝒯 •         = yes refl
  •       ≟𝒯 (A′ ⊃ B′) = no λ ()
  (A ⊃ B) ≟𝒯 •         = no λ ()
  (A ⊃ B) ≟𝒯 (A′ ⊃ B′) with A ≟𝒯 A′ | B ≟𝒯 B′
  …                   | yes refl | yes refl = yes refl
  …                   | no A≢A′  | _        = no (λ A → inj⊃₁ A ↯ A≢A′)
  …                   | _        | no B≢B′  = no (λ B → inj⊃₂ B ↯ B≢B′)


-- 3.2. Definition of contexts
-- ---------------------------
--
-- Suppose a countably infinite set, `Name`, with names together with a decidable equality on it.
-- The set of contexts `𝒞` is mutually defined with a boolean-valued function `fresh` which describes
-- when a name is fresh in a context.  (…)
--
-- Ordinarily, the freshness condition is written as a side-condition, but since we are to
-- formalise the proof trees, this information must be represented, too.
--
-- We write `[]` for the empty context and `[ Γ , x ∷ A ]` for adding an element to a context,
-- hence when we write `[ Γ , x ∷ A ]`
-- it is implicit that we also have a proof that `x` is fresh in `Γ` (when `[ Γ , x ∷ A ]` occurs in the
-- conclusion of a statement, then it is implicit that `T (fresh x Γ)` is an assumption.)  The
-- function `fresh` is defined by induction on the context as:

mutual
  data 𝒞 : Set where
    []      : 𝒞
    [_,_∷_] : (Γ : 𝒞) (x : Name) {{_ : T (fresh x Γ)}} → 𝒯 → 𝒞

  fresh : Name → 𝒞 → Bool
  fresh x []            = true
  fresh x [ Γ , y ∷ A ] = and (x ≠ y) (fresh x Γ)

-- We use `Γ`, `Δ` and `Θ` for contexts.
--
-- The predicate `Γ ∋ x ∷ A` is true when a name with its type occurs in a context.
--
-- The introduction rules are:

data _∋_∷_ : 𝒞 → Name → 𝒯 → Set where
  zero : ∀ {Γ A x} {{_ : T (fresh x Γ)}} →
           [ Γ , x ∷ A ] ∋ x ∷ A
  suc  : ∀ {Γ A B x y} {{_ : T (fresh y Γ)}} →
           Γ ∋ x ∷ A →
           [ Γ , y ∷ B ] ∋ x ∷ A

module _ where
  _∌_∷_ : 𝒞 → Name → 𝒯 → Set
  Γ ∌ x ∷ A = ¬ (Γ ∋ x ∷ A)

  fresh→∌ : ∀ {x Γ A} {{_ : T (fresh x Γ)}} → Γ ∌ x ∷ A
  fresh→∌ {x} {{p}}  zero             with x ≟ x
  fresh→∌ {x} {{()}} zero             | yes refl
  fresh→∌ {x} {{p}}  zero             | no x≢x   = refl ↯ x≢x
  fresh→∌ {x} {{p}}  (suc {y = y}  i) with x ≟ y
  fresh→∌ {x} {{()}} (suc {y = .x} i) | yes refl
  fresh→∌ {x} {{p}}  (suc {y = y}  i) | no x≢y   = i ↯ fresh→∌

-- We also define the relation that describes when a context contains another.
--
-- We use the notational convention `Γ ⊇ Δ` for `Γ` being greater than `Δ`.
-- The set `_⊇_` has the constructors:

infix 3 _⊇_
data _⊇_ : 𝒞 → 𝒞 → Set where
  done : ∀ {Γ} →
           Γ ⊇ []
  weak : ∀ {Γ Δ A x} {{_ : T (fresh x Δ)}} →
           Γ ⊇ Δ → Γ ∋ x ∷ A →
           Γ ⊇ [ Δ , x ∷ A ]

-- The following lemmas are easy to prove:

-- Lemma 1.
ext⊇ : ∀ {Δ Γ} → (∀ {A x} → Δ ∋ x ∷ A → Γ ∋ x ∷ A) → Γ ⊇ Δ
ext⊇ {[]}            f = done
ext⊇ {[ Δ , x ∷ A ]} f = weak (ext⊇ (λ i → f (suc i))) (f zero)

-- Lemma 2.
module _ where
  ↑⟨_⟩∋ : ∀ {Γ Δ A x} → Δ ⊇ Γ → Γ ∋ x ∷ A → Δ ∋ x ∷ A
  ↑⟨ done ⟩∋     ()
  ↑⟨ weak c i ⟩∋ zero    = i
  ↑⟨ weak c i ⟩∋ (suc j) = ↑⟨ c ⟩∋ j

  instance
    raise∋ : ∀ {A x} → Raiseable (_∋ x ∷ A)
    raise∋ = record { ↑⟨_⟩ = ↑⟨_⟩∋ }

-- Lemma 3.
refl⊇ : ∀ {Γ} → Γ ⊇ Γ
refl⊇ = ext⊇ id

-- Lemma 4.
module _ where
  _○_ : ∀ {Γ Δ Θ} → Γ ⊇ Δ → Θ ⊇ Γ → Θ ⊇ Δ
  c ○ c′ = ext⊇ (λ i → ↑⟨ c′ ⟩ (↑⟨ c ⟩ i))

  trans⊇ : ∀ {Γ Δ Θ} → Θ ⊇ Γ → Γ ⊇ Δ → Θ ⊇ Δ
  trans⊇ = flip _○_

-- Lemma 5.
weak⊇ : ∀ {Γ A x} {{_ : T (fresh x Γ)}} → [ Γ , x ∷ A ] ⊇ Γ
weak⊇ = ext⊇ suc

-- Lemma 6.
uniq∋ : ∀ {Γ A x} → (i i′ : Γ ∋ x ∷ A) → i ≡ i′
uniq∋ zero    zero     = refl
uniq∋ zero    (suc i′) = i′ ↯ fresh→∌
uniq∋ (suc i) zero     = i ↯ fresh→∌
uniq∋ (suc i) (suc i′) = cong suc (uniq∋ i i′)

-- Lemma 7.
uniq⊇ : ∀ {Γ Δ} → (c c′ : Γ ⊇ Δ) → c ≡ c′
uniq⊇ done       done         = refl
uniq⊇ (weak c i) (weak c′ i′) = cong² weak (uniq⊇ c c′) (uniq∋ i i′)

-- `ext⊇`, `↑⟨_⟩∋` and `uniq⊇` are proven by induction on `Δ` and `uniq∋` is proven by
-- induction on `Γ`.  `refl⊇` and `weak⊇` are direct consequences of `ext⊇` and for `trans⊇`
-- we also use `↑⟨_⟩∋`.  (…)
--
-- The last two lemmas may seem slightly strange: they are used for guaranteeing independence
-- of the proofs of `_∋_∷_` and `_⊇_`.  For example, `uniq∋` says that if it can be shown that
-- `x ∷ A` occurs in a context `Γ`, then there is a unique proof of this fact.  The need to prove
-- independence of proofs might point to a problem in using type theory for formalising proofs.  On
-- the other hand, as we shall see, proof objects can also be useful: the present formalisation
-- heavily uses the possibilities to perform case analysis on proof objects, which reduces the
-- number of cases to consider.

module _ where
  id○₁ : ∀ {Γ Δ} → (c : Γ ⊇ Γ) (c′ : Δ ⊇ Γ) → c ○ c′ ≡ c′
  id○₁ c c′ = uniq⊇ (c ○ c′) c′

  id○₂ : ∀ {Γ Δ} → (c : Δ ⊇ Γ) (c′ : Δ ⊇ Δ) → c ○ c′ ≡ c
  id○₂ c c′ = uniq⊇ (c ○ c′) c

  assoc○ : ∀ {Γ Δ Θ Ω} → (c : Δ ⊇ Γ) (c′ : Θ ⊇ Δ) (c″ : Ω ⊇ Θ) →
             c ○ (c′ ○ c″) ≡ (c ○ c′) ○ c″
  assoc○ c c′ c″ = uniq⊇ (c ○ (c′ ○ c″)) ((c ○ c′) ○ c″)

  comp○ : ∀ {Γ Δ Θ} → (c : Δ ⊇ Γ) (c′ : Θ ⊇ Δ) (c″ : Θ ⊇ Γ) →
            c ○ c′ ≡ c″
  comp○ c c′ c″ = uniq⊇ (c ○ c′) c″


-- 3.3. Definition of proof trees
-- ------------------------------
--
-- Proof trees and substitutions are mutually inductively defined.  (…)
--
-- We use the notational convention `Γ ⊢ A` and `Δ ⋙ Γ` for a proof of `A` in context `Γ` and
-- a substitution of `Γ` by `Δ`, respectively.
--
-- A substitution of type `Δ ⋙ Γ` intuitively is a list that associates to each `x ∷ A` in `Γ` a unique
-- proof tree of type `Δ ⊢ A`.
--
-- The proof trees are defined by the following rules.
--
-- We recall that hidden assumptions in the definition above are implicitly universally defined
-- and that the notation `[ Γ , x ∷ A ]` implies that `x` is fresh in `Γ`.  (…)
--
-- In the definition of variables we can see that a proof of occurrence is part of the proof
-- tree.  The advantage is that we can do case-analysis on this proof to find out where in the
-- context `x ∷ A` occurs.  The disadvantage is that we need to prove that two variables are the
-- same even if they have two possibly different proofs of occurrence of `x ∷ A` (by Lemma 6 we
-- know that the proofs are the same).

mutual
  infix 3 _⊢_
  data _⊢_ : 𝒞 → 𝒯 → Set where
    ν   : ∀ {Γ A} →
            (x : Name) → Γ ∋ x ∷ A →
            Γ ⊢ A
    ƛ   : ∀ {Γ A B} →
            (x : Name) {{_ : T (fresh x Γ)}} → [ Γ , x ∷ A ] ⊢ B →
            Γ ⊢ A ⊃ B
    _∙_ : ∀ {Γ A B} →
            Γ ⊢ A ⊃ B → Γ ⊢ A →
            Γ ⊢ B
    _▶_ : ∀ {Γ Δ A} →
            Γ ⊢ A → Δ ⋙ Γ →
            Δ ⊢ A

  infix 3 _⋙_
  data _⋙_ : 𝒞 → 𝒞 → Set where
    π⟨_⟩    : ∀ {Γ Δ} →
                Δ ⊇ Γ →
                Δ ⋙ Γ
    _●_     : ∀ {Γ Δ Θ} →
                Γ ⋙ Δ → Θ ⋙ Γ →
                Θ ⋙ Δ
    [_,_≔_] : ∀ {Γ Δ A} →
                Δ ⋙ Γ → (x : Name) {{_ : T (fresh x Γ)}} → Δ ⊢ A →
                Δ ⋙ [ Γ , x ∷ A ]

-- Explicit substitutions are built from a projection map, update and composition (see below
-- for a discussion on the projection map).
--
-- We use the following notational conventions:
--
-- -   `ν x`           for referencing the occurrence `x`, where `x : Γ ∋ x ∷ A`
-- -   `M ▶ γ`         for applying the substitution `γ` to the term `M`
-- -   `ƛ x M`         for abstracting the occurrence `x` from the term `M`, where `M : [ Γ , x ∷ A ] ⊢ B`
-- -   `M ∙ N`         for applying the term `M` to the term `N`
-- -   `π⟨ c ⟩`        for projecting the inclusion `c` as a substitution
-- -   `[ γ , x ≔ M ]` for updating the substitution `γ` with the term `M` for the occurrence `x`
-- -   `γ ● δ`         for composing the substitution `δ` with the substitution `γ`
--
-- Proof trees and substitutions are named `M, N` and `γ, δ, θ` respectively.
--
-- The substitution `π⟨_⟩` is not a standard primitive for explicit substitutions.  Often one rather
-- has an identity substitution (in `Γ ⋙ Γ`) [1, 13] or the empty substitution (in `Γ ⋙ []`) [5].
-- Instead we have taken `π⟨_⟩` as primitive.  If `c : Γ ⊇ Γ`, then `π⟨ c ⟩` is the identity substitution and
-- if `c : Γ ⊇ []`, then `π⟨ c ⟩` is the empty substitution.  Abadi et al. [1] use a substitution `↑` that
-- corresponds to a shift on substitutions; the same substitution is here defined as `π⟨ c ⟩` where
-- `c : [ Γ , x ∷ A ] ⊇ Γ`.  In Martin-Löf’s substitution calculus [13, 20] we have as primitives also
-- thinning rules (i.e., if a term is well-typed in a given context, then it is also well-typed in a
-- larger context and likewise for substitutions.)  Here, thinning is achieved using `π⟨_⟩`, since if,
-- for example, `M : Γ ⊢ A` and `c : Δ ⊇ Γ`, then `M ▶ π⟨ c ⟩ : Δ ⊢ A`.
--
-- The first version of our work used combinators for the thinning rules, since we wanted it to
-- be a start for a complete mechanical analysis of Martin-Löf’s substitution calculus [13, 20].
-- The set of conversion rules we obtained using these combinators suggested the use of `π⟨_⟩`,
-- which gives fewer conversion rules.  There might be other advantages in using `π⟨_⟩`: if a proof
-- tree is of the form `M ▶ π⟨_⟩` we know which are the possible free variables of the term `M`,
-- information that might be used in a computation.

module _ where
  ↑⟨_⟩⊢ : ∀ {Γ Δ A} → Δ ⊇ Γ → Γ ⊢ A → Δ ⊢ A
  ↑⟨ c ⟩⊢ M = M ▶ π⟨ c ⟩

  ↑⟨_⟩⋙ : ∀ {Γ Δ Θ} → Δ ⊇ Γ → Γ ⋙ Θ → Δ ⋙ Θ
  ↑⟨ c ⟩⋙ δ = δ ● π⟨ c ⟩

  ↓⟨_⟩⋙ : ∀ {Γ Δ Θ} → Δ ⊇ Γ → Θ ⋙ Δ → Θ ⋙ Γ
  ↓⟨ c ⟩⋙ δ = π⟨ c ⟩ ● δ

  refl⋙ : ∀ {Γ} → Γ ⋙ Γ
  refl⋙ = π⟨ refl⊇ ⟩

  trans⋙ : ∀ {Γ Δ Θ} → Θ ⋙ Γ → Γ ⋙ Δ → Θ ⋙ Δ
  trans⋙ = flip _●_

  weak⋙ : ∀ {Γ A x} {{_ : T (fresh x Γ)}} → [ Γ , x ∷ A ] ⋙ Γ
  weak⋙ = π⟨ weak⊇ ⟩

  instance
    raise⊢ : ∀ {A} → Raiseable (_⊢ A)
    raise⊢ = record { ↑⟨_⟩ = ↑⟨_⟩⊢ }

    raise⋙ : ∀ {Γ} → Raiseable (_⋙ Γ)
    raise⋙ = record { ↑⟨_⟩ = ↑⟨_⟩⋙ }

    lower⋙ : ∀ {Δ} → Lowerable (Δ ⋙_)
    lower⋙ = record { ↓⟨_⟩ = ↓⟨_⟩⋙ }


-- 3.4. Convertibility of proof trees
-- ----------------------------------
--
-- The rules for conversion between proof trees and substitutions are inductively defined.
--
-- We use the notational convention `M ≅ N` and `γ ≅ₛ δ` for convertibility on proof trees and
-- on substitutions respectively.  (…)
--
-- The conversion rules for proof trees are the reflexivity, symmetry, transitivity, congruence
-- rules and the following rules:

mutual
  infix 3 _≅_
  data _≅_ : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ A → Set where
    refl≅  : ∀ {Γ A} {M : Γ ⊢ A} →
               M ≅ M
    sym≅   : ∀ {Γ A} {M M′ : Γ ⊢ A} →
               M ≅ M′ →
               M′ ≅ M
    trans≅ : ∀ {Γ A} {M M′ M″ : Γ ⊢ A} →
               M ≅ M′ → M′ ≅ M″ →
               M ≅ M″

    cong≅ƛ : ∀ {Γ A B x} {{_ : T (fresh x Γ)}} {M M′ : [ Γ , x ∷ A ] ⊢ B} →
               M ≅ M′ →
               ƛ x M ≅ ƛ x M′
    cong≅∙ : ∀ {Γ A B} {M M′ : Γ ⊢ A ⊃ B} {N N′ : Γ ⊢ A} →
               M ≅ M′ → N ≅ N′ →
               M ∙ N ≅ M′ ∙ N′
    cong≅▶ : ∀ {Γ Δ A} {M M′ : Γ ⊢ A} {γ γ′ : Δ ⋙ Γ} →
               M ≅ M′ → γ ≅ₛ γ′ →
               M ▶ γ ≅ M′ ▶ γ′

    conv≅₁ : ∀ {Γ Δ A B x} {{_ : T (fresh x Γ)}} →
               (M : [ Γ , x ∷ A ] ⊢ B) (γ : Δ ⋙ Γ) (N : Δ ⊢ A) →
               (ƛ x M ▶ γ) ∙ N ≅ M ▶ [ γ , x ≔ N ]
    conv≅₂ : ∀ {Γ A B x} {{_ : T (fresh x Γ)}} →
               (M : Γ ⊢ A ⊃ B) (c : [ Γ , x ∷ A ] ⊇ Γ) →
               M ≅ ƛ x ((M ▶ π⟨ c ⟩) ∙ ν x zero)
    conv≅₃ : ∀ {Γ Δ A x} {{_ : T (fresh x Γ)}} →
               (γ : Δ ⋙ Γ) (M : Δ ⊢ A) →
               ν x zero ▶ [ γ , x ≔ M ] ≅ M
    conv≅₄ : ∀ {Γ Δ A x} →
               (i : Γ ∋ x ∷ A) (c : Δ ⊇ Γ) (j : Δ ∋ x ∷ A) →
               ν x i ▶ π⟨ c ⟩ ≅ ν x j
    conv≅₅ : ∀ {Γ A} →
               (M : Γ ⊢ A) (c : Γ ⊇ Γ) →
               M ▶ π⟨ c ⟩ ≅ M
    conv≅₆ : ∀ {Γ Δ A B} →
               (M : Γ ⊢ A ⊃ B) (N : Γ ⊢ A) (γ : Δ ⋙ Γ) →
               (M ∙ N) ▶ γ ≅ (M ▶ γ) ∙ (N ▶ γ)
    conv≅₇ : ∀ {Γ Δ Θ A} →
               (M : Γ ⊢ A) (γ : Δ ⋙ Γ) (δ : Θ ⋙ Δ) →
               (M ▶ γ) ▶ δ ≅ M ▶ (γ ● δ)

  infix 3 _≅ₛ_
  data _≅ₛ_ : ∀ {Γ Δ} → Δ ⋙ Γ → Δ ⋙ Γ → Set where
    refl≅ₛ  : ∀ {Γ Δ} {γ : Δ ⋙ Γ} →
                γ ≅ₛ γ
    sym≅ₛ   : ∀ {Γ Δ} {γ γ′ : Δ ⋙ Γ} →
                γ ≅ₛ γ′ →
                γ′ ≅ₛ γ
    trans≅ₛ : ∀ {Γ Δ} {γ γ′ γ″ : Δ ⋙ Γ} →
                γ ≅ₛ γ′ → γ′ ≅ₛ γ″ →
                γ ≅ₛ γ″

    cong≅ₛ● : ∀ {Γ Δ Θ} {γ γ′ : Δ ⋙ Γ} {δ δ′ : Θ ⋙ Δ} →
                γ ≅ₛ γ′ → δ ≅ₛ δ′ →
                γ ● δ ≅ₛ γ′ ● δ′
    cong≅ₛ≔ : ∀ {Γ Δ A x} {{_ : T (fresh x Γ)}} {γ γ′ : Δ ⋙ Γ} {M M′ : Δ ⊢ A} →
                γ ≅ₛ γ′ → M ≅ M′ →
                [ γ , x ≔ M ] ≅ₛ [ γ′ , x ≔ M′ ]

    conv≅ₛ₁ : ∀ {Γ Δ Θ Ω} →
                (γ : Δ ⋙ Γ) (δ : Θ ⋙ Δ) (θ : Ω ⋙ Θ) →
                (γ ● δ) ● θ ≅ₛ γ ● (δ ● θ)
    conv≅ₛ₂ : ∀ {Γ Δ Θ A x} {{_ : T (fresh x Γ)}} →
                (γ : Δ ⋙ Γ) (M : Δ ⊢ A) (δ : Θ ⋙ Δ) →
                [ γ , x ≔ M ] ● δ ≅ₛ [ γ ● δ , x ≔ M ▶ δ ]
    conv≅ₛ₃ : ∀ {Γ Δ A x} {{_ : T (fresh x Γ)}} →
                (c : [ Γ , x ∷ A ] ⊇ Γ) (γ : Δ ⋙ Γ) (M : Δ ⊢ A) →
                π⟨ c ⟩ ● [ γ , x ≔ M ] ≅ₛ γ
    conv≅ₛ₄ : ∀ {Γ Δ Θ} →
                (c : Θ ⊇ Γ) (c′ : Δ ⊇ Γ) (c″ : Θ ⊇ Δ) →
                π⟨ c′ ⟩ ● π⟨ c″ ⟩ ≅ₛ π⟨ c ⟩
    conv≅ₛ₅ : ∀ {Γ Δ} →
                (γ : Δ ⋙ Γ) (c : Δ ⊇ Δ) →
                γ ● π⟨ c ⟩ ≅ₛ γ
    conv≅ₛ₆ : ∀ {Γ} →
                (γ : Γ ⋙ []) (c : Γ ⊇ []) →
                γ ≅ₛ π⟨ c ⟩
    conv≅ₛ₇ : ∀ {Γ Δ A x} {{_ : T (fresh x Γ)}} →
                (γ : Δ ⋙ [ Γ , x ∷ A ]) (c : [ Γ , x ∷ A ] ⊇ Γ) (i : [ Γ , x ∷ A ] ∋ x ∷ A) →
                γ ≅ₛ [ π⟨ c ⟩ ● γ , x ≔ ν x i ▶ γ ]

-- The first two `conv≅` rules correspond to the ordinary β- and η-rules, the next three define the effect
-- of substitutions and the last two rules can be seen as the correspondence of the η-rule for
-- substitutions.  The remaining `conv≅ₛ` rules define how the substitutions distribute.

module _ where
  ≡→≅ : ∀ {Γ A} {M M′ : Γ ⊢ A} → M ≡ M′ → M ≅ M′
  ≡→≅ refl = refl≅

  module ≅-Reasoning where
    infix 1 begin_
    begin_ : ∀ {Γ A} {M M′ : Γ ⊢ A} → M ≅ M′ → M ≅ M′
    begin p = p

    infixr 2 _≅⟨⟩_
    _≅⟨⟩_ : ∀ {Γ A} (M {M′} : Γ ⊢ A) → M ≅ M′ → M ≅ M′
    M ≅⟨⟩ p = p

    infixr 2 _≅⟨_⟩_
    _≅⟨_⟩_ : ∀ {Γ A} (M {M′ M″} : Γ ⊢ A) → M ≅ M′ → M′ ≅ M″ → M ≅ M″
    M ≅⟨ p ⟩ p′ = trans≅ p p′

    infixr 2 _≡⟨⟩_
    _≡⟨⟩_ : ∀ {Γ A} (M {M′} : Γ ⊢ A) → M ≅ M′ → M ≅ M′
    M ≡⟨⟩ p = p

    infixr 2 _≡⟨_⟩_
    _≡⟨_⟩_ : ∀ {Γ A} (M {M′ M″} : Γ ⊢ A) → M ≡ M′ → M′ ≅ M″ → M ≅ M″
    M ≡⟨ p ⟩ p′ = trans≅ (≡→≅ p) p′

    infix 3 _∎
    _∎ : ∀ {Γ A} (M : Γ ⊢ A) → M ≅ M
    M ∎ = refl≅

  ≡→≅ₛ : ∀ {Γ Δ} {γ γ′ : Δ ⋙ Γ} → γ ≡ γ′ → γ ≅ₛ γ′
  ≡→≅ₛ refl = refl≅ₛ

  module ≅ₛ-Reasoning where
    infix 1 begin_
    begin_ : ∀ {Γ Δ} {γ γ′ : Δ ⋙ Γ} → γ ≅ₛ γ′ → γ ≅ₛ γ′
    begin p = p

    infixr 2 _≅ₛ⟨⟩_
    _≅ₛ⟨⟩_ : ∀ {Γ Δ} (γ {γ′} : Δ ⋙ Γ) → γ ≅ₛ γ′ → γ ≅ₛ γ′
    γ ≅ₛ⟨⟩ p = p

    infixr 2 _≅ₛ⟨_⟩_
    _≅ₛ⟨_⟩_ : ∀ {Γ Δ} (γ {γ′ γ″} : Δ ⋙ Γ) → γ ≅ₛ γ′ → γ′ ≅ₛ γ″ → γ ≅ₛ γ″
    γ ≅ₛ⟨ p ⟩ p′ = trans≅ₛ p p′

    infixr 2 _≡⟨⟩_
    _≡⟨⟩_ : ∀ {Γ Δ} (γ {γ′} : Δ ⋙ Γ) → γ ≅ₛ γ′ → γ ≅ₛ γ′
    γ ≡⟨⟩ p = p

    infixr 2 _≡⟨_⟩_
    _≡⟨_⟩_ : ∀ {Γ Δ} (γ {γ′ γ″} : Δ ⋙ Γ) → γ ≡ γ′ → γ′ ≅ₛ γ″ → γ ≅ₛ γ″
    γ ≡⟨ p ⟩ p′ = trans≅ₛ (≡→≅ₛ p) p′

    infix 3 _∎
    _∎ : ∀ {Γ Δ} (γ : Δ ⋙ Γ) → γ ≅ₛ γ
    γ ∎ = refl≅ₛ
