module Syntax where

open import Prelude public
  renaming (∙ to tt)
  hiding (_∘_ ; subst)


-- 3.1. Definitions of types

infixr 7 _⇒_
data 𝒯 : Set where
  o    : 𝒯
  _⇒_ : 𝒯 → 𝒯 → 𝒯


-- 3.2. Definition of contexts

abstract
  Name : Set
  Name = Nat

  _≟Name_ : (x x′ : Name) → Dec (x ≡ x′)
  _≟Name_ = _≟Nat_

mutual
  data 𝒞 : Set where
    []      : 𝒞
    [_,_∷_] : (Γ : 𝒞) (x : Name) {{_ : fresh x Γ}} → 𝒯 → 𝒞

  fresh : Name → 𝒞 → Set
  fresh x []            = ⊤
  fresh x [ Γ , y ∷ A ] = x ≢ y ∧ fresh x Γ

data Occur (x : Name) (A : 𝒯) : 𝒞 → Set where
  occ₁ : ∀ {Γ}     {{_ : fresh x Γ}} → Occur x A [ Γ , x ∷ A ]
  occ₂ : ∀ {y B Γ} {{_ : fresh y Γ}} → Occur x A Γ → Occur x A [ Γ , y ∷ B ]

fresh→¬Occur : ∀ {x A Γ} {{_ : fresh x Γ}} → ¬ (Occur x A Γ)
fresh→¬Occur {{x≢x , _}} occ₁     = refl ↯ x≢x
fresh→¬Occur {{_   , φ}} (occ₂ i) = i ↯ fresh→¬Occur {{φ}}

infix 3 _⊇_
data _⊇_ : 𝒞 → 𝒞 → Set where
  gt₁ : ∀ {Γ}                         → Γ ⊇ []
  gt₂ : ∀ {x A Δ Γ} {{_ : fresh x Δ}} → Γ ⊇ Δ → Occur x A Γ → Γ ⊇ [ Δ , x ∷ A ]


-- Lemmas.

Lemma₁ : ∀ {Δ Γ} → (∀ {x A} → Occur x A Δ → Occur x A Γ) → Γ ⊇ Δ
Lemma₁ {[]}            f = gt₁
Lemma₁ {[ Γ , x ∷ A ]} f = gt₂ (Lemma₁ (λ i → f (occ₂ i))) (f occ₁)

ext⊇ = Lemma₁

Lemma₂ : ∀ {x A Δ Γ} → Occur x A Δ → Γ ⊇ Δ → Occur x A Γ
Lemma₂ ()       gt₁
Lemma₂ occ₁     (gt₂ c i) = i
Lemma₂ (occ₂ i) (gt₂ c j) = Lemma₂ i c

mono∈ = Lemma₂

Lemma₃ : ∀ {Γ} → Γ ⊇ Γ
Lemma₃ = Lemma₁ id

refl⊇ = Lemma₃

Lemma₄ : ∀ {Θ Δ Γ} → Θ ⊇ Γ → Γ ⊇ Δ → Θ ⊇ Δ
Lemma₄ c₁ c₂ = Lemma₁ (λ i → Lemma₂ (Lemma₂ i c₂) c₁)

trans⊇ = Lemma₄

Lemma₅ : ∀ {x A Γ} {{_ : fresh x Γ}} → [ Γ , x ∷ A ] ⊇ Γ
Lemma₅ = Lemma₁ occ₂

weak⊇ = Lemma₅

Lemma₆ : ∀ {Γ x A} → (i i′ : Occur x A Γ) → i ≡ i′
Lemma₆ occ₁     occ₁      = refl
Lemma₆ occ₁     (occ₂ i′) = i′ ↯ fresh→¬Occur
Lemma₆ (occ₂ i) occ₁      = i ↯ fresh→¬Occur
Lemma₆ (occ₂ i) (occ₂ i′) = cong occ₂ (Lemma₆ i i′)

uniq∈ = Lemma₆

Lemma₇ : ∀ {Δ Γ} → (c c′ : Γ ⊇ Δ) → c ≡ c′
Lemma₇ gt₁       gt₁         = refl
Lemma₇ (gt₂ l i) (gt₂ l′ i′) = cong² gt₂ (Lemma₇ l l′) (Lemma₆ i i′)

uniq⊇ = Lemma₇


-- Lemmas.

-- idtrans⊆₁ : ∀ {Γ Γ′} → (l : Γ ⊆ Γ′) (l′ : Γ′ ⊆ Γ′) → Lemma₄ l l′ ≡ l
-- idtrans⊆₁ l l′ = uniq⊆ (Lemma₄ l l′) l
--
-- idtrans⊆₂ : ∀ {Γ Γ′} → (l : Γ ⊆ Γ) (l′ : Γ ⊆ Γ′) → Lemma₄ l l′ ≡ l′
-- idtrans⊆₂ l l′ = uniq⊆ (Lemma₄ l l′) l′
--
-- assoctrans⊆ : ∀ {Γ Γ′ Γ″ Γ‴} → (l : Γ ⊆ Γ′) (l′ : Γ′ ⊆ Γ″) (l″ : Γ″ ⊆ Γ‴) →
--               Lemma₄ l (Lemma₄ l′ l″) ≡ Lemma₄ (Lemma₄ l l′) l″
-- assoctrans⊆ l l′ l″ = uniq⊆ (Lemma₄ l (Lemma₄ l′ l″)) (Lemma₄ (Lemma₄ l l′) l″)
--
-- comptrans⊆ : ∀ {Γ Γ′ Γ″} → (l : Γ ⊆ Γ′) (l′ : Γ′ ⊆ Γ″) (l″ : Γ ⊆ Γ″) →
--              Lemma₄ l l′ ≡ l″
-- comptrans⊆ l l′ l″ = uniq⊆ (Lemma₄ l l′) l″


-- 3.3. Definition of proof trees

mutual
  infix 3 _⊢_
  data _⊢_ : 𝒞 → 𝒯 → Set where
    var    : ∀ {x A Γ}                     → (i : Occur x A Γ) → Γ ⊢ A
    subst  : ∀ {A Δ Γ}                     → (M : Γ ⊢ A) → (γ : Δ ⇛ Γ) → Δ ⊢ A
    lambda : ∀ {x A B Γ} {{_ : fresh x Γ}} → (M : [ Γ , x ∷ A ] ⊢ B) → Γ ⊢ A ⇒ B
    apply  : ∀ {A B Γ}                     → (M : Γ ⊢ A ⇒ B) → (N : Γ ⊢ A) → Γ ⊢ B

  infix 3 _⇛_
  data _⇛_ : 𝒞 → 𝒞 → Set where
    proj   : ∀ {Δ Γ}                       → (c : Δ ⊇ Γ) → Δ ⇛ Γ
    comp   : ∀ {Θ Δ Γ}                     → (δ : Γ ⇛ Δ) → (γ : Θ ⇛ Γ) → Θ ⇛ Δ
    update : ∀ {x A Δ Γ} {{_ : fresh x Γ}} → (γ : Δ ⇛ Γ) → (M : Δ ⊢ A) → Δ ⇛ [ Γ , x ∷ A ]

apply′ : ∀ {A B Γ} → Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
apply′ = apply

infixl 7 subst
infixl 6 apply apply′
infixl 5 comp
syntax var {x} {A} i     = v[ x ∷ A ] i
syntax subst M γ         = M ▸ γ
syntax lambda {x} {A} M  = λ[ x ∷ A ] M
syntax apply {A} {B} M N = M ∙⟨ A , B ⟩ N
syntax apply′ M N        = M ∙ N
syntax proj c            = π c
syntax comp δ γ          = δ ∘ γ
syntax update {x} γ M    = [ γ , x ≔ M ]
