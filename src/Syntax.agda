module Syntax where

open import Prelude public


-- Names.

Name : Set
Name = Nat


-- Types.

infixr 7 _⇒_
data Type : Set where
  ○    : Type
  _⇒_ : Type → Type → Type


-- Contexts and freshness.

mutual
  infixl 5 _,_∷_
  data Context : Set where
    ∅     : Context
    _,_∷_ : (Γ : Context) (x : Name) {{_ : x ∥ Γ}} → Type → Context

  infix 4 _∥_
  _∥_ : Name → Context → Set
  x ∥ ∅         = ⊤
  x ∥ Γ , y ∷ A = x ≢ y ∧ x ∥ Γ

infix 4 _∦_
_∦_ : Name → Context → Set
x ∦ Γ = ¬ (x ∥ Γ)


-- Occurrences of names in contexts.

infix 3 _∷_∈_
data _∷_∈_ (x : Name) (A : Type) : Context → Set where
  top : ∀ {Γ}     {{_ : x ∥ Γ}} → x ∷ A ∈ Γ , x ∷ A
  pop : ∀ {y B Γ} {{_ : y ∥ Γ}} → x ∷ A ∈ Γ → x ∷ A ∈ Γ , y ∷ B

_∷_∉_ : Name → Type → Context → Set
x ∷ A ∉ Γ = ¬ (x ∷ A ∈ Γ)

∥→∉ : ∀ {x A Γ} {{_ : x ∥ Γ}} → x ∷ A ∉ Γ
∥→∉ {{x≢x , _}} top     = refl ↯ x≢x
∥→∉ {{_ , x∥Γ}} (pop i) = i ↯ ∥→∉ {{x∥Γ}}


-- Context inclusion.

infix 3 _⊆_
data _⊆_ : Context → Context → Set where
  bot  : ∀ {Γ}                      → ∅ ⊆ Γ
  push : ∀ {x A Γ Γ′} {{_ : x ∥ Γ}} → Γ ⊆ Γ′ → x ∷ A ∈ Γ′ → Γ , x ∷ A ⊆ Γ′

infix 3 _⊈_
_⊈_ : Context → Context → Set
Γ ⊈ Γ′ = ¬ (Γ ⊆ Γ′)


-- Lemmas.

ext⊆ : ∀ {Γ Γ′} → (∀ {x A} → x ∷ A ∈ Γ → x ∷ A ∈ Γ′) → Γ ⊆ Γ′
ext⊆ {∅}           f = bot
ext⊆ {(Γ , x ∷ A)} f = push (ext⊆ (f ∘ pop)) (f top)

mono⊆∈ : ∀ {x A Γ Γ′} → Γ ⊆ Γ′ → x ∷ A ∈ Γ → x ∷ A ∈ Γ′
mono⊆∈ bot        ()
mono⊆∈ (push l i) top     = i
mono⊆∈ (push l i) (pop j) = mono⊆∈ l j

refl⊆ : ∀ {Γ} → Γ ⊆ Γ
refl⊆ = ext⊆ id

trans⊆ : ∀ {Γ Γ′ Γ″} → Γ ⊆ Γ′ → Γ′ ⊆ Γ″ → Γ ⊆ Γ″
trans⊆ l l′ = ext⊆ (mono⊆∈ l′ ∘ mono⊆∈ l)

weak⊆ : ∀ {x A Γ} {{_ : x ∥ Γ}} → Γ ⊆ Γ , x ∷ A
weak⊆ = ext⊆ pop

uniq∈ : ∀ {Γ x A} → (i i′ : x ∷ A ∈ Γ) → i ≡ i′
uniq∈ top     top      = refl
uniq∈ top     (pop i′) = i′ ↯ ∥→∉
uniq∈ (pop i) top      = i ↯ ∥→∉
uniq∈ (pop i) (pop i′) = cong pop (uniq∈ i i′)

uniq⊆ : ∀ {Γ Γ′} → (l l′ : Γ ⊆ Γ′) → l ≡ l′
uniq⊆ bot        bot          = refl
uniq⊆ (push l i) (push l′ i′) = cong² push (uniq⊆ l l′) (uniq∈ i i′)

lem₁ = ext⊆
lem₂ = mono⊆∈
lem₃ = refl⊆
lem₄ = trans⊆
lem₅ = weak⊆
lem₆ = uniq∈
lem₇ = uniq⊆


-- Lemmas.

idtrans⊆₁ : ∀ {Γ Γ′} → (l : Γ ⊆ Γ′) (l′ : Γ′ ⊆ Γ′) → trans⊆ l l′ ≡ l
idtrans⊆₁ l l′ = uniq⊆ (trans⊆ l l′) l

idtrans⊆₂ : ∀ {Γ Γ′} → (l : Γ ⊆ Γ) (l′ : Γ ⊆ Γ′) → trans⊆ l l′ ≡ l′
idtrans⊆₂ l l′ = uniq⊆ (trans⊆ l l′) l′

assoctrans⊆ : ∀ {Γ Γ′ Γ″ Γ‴} → (l : Γ ⊆ Γ′) (l′ : Γ′ ⊆ Γ″) (l″ : Γ″ ⊆ Γ‴) →
              trans⊆ l (trans⊆ l′ l″) ≡ trans⊆ (trans⊆ l l′) l″
assoctrans⊆ l l′ l″ = uniq⊆ (trans⊆ l (trans⊆ l′ l″)) (trans⊆ (trans⊆ l l′) l″)

comptrans⊆ : ∀ {Γ Γ′ Γ″} → (l : Γ ⊆ Γ′) (l′ : Γ′ ⊆ Γ″) (l″ : Γ ⊆ Γ″) →
             trans⊆ l l′ ≡ l″
comptrans⊆ l l′ l″ = uniq⊆ (trans⊆ l l′) l″


-- Derivations and substitutions.

mutual
  infix 3 _⊢_
  infixl 5 _◂_
  data _⊢_ : Context → Type → Set where
    var : ∀ x {A Γ}                 → x ∷ A ∈ Γ → Γ ⊢ A
    lam : ∀ x {A B Γ} {{_ : x ∥ Γ}} → Γ , x ∷ A ⊢ B → Γ ⊢ A ⇒ B
    app : ∀ {A B Γ}                 → Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
    _◂_ : ∀ {A Γ Γ′}                → Γ ⊢ A → Γ ⋘ Γ′ → Γ′ ⊢ A

  infix 3 _⋘_
  infixl 6 _•_
  data _⋘_ : Context → Context → Set where
    sub    : ∀ {Γ Γ′}                   → Γ ⊆ Γ′ → Γ ⋘ Γ′
    _•_    : ∀ {Γ Γ′ Γ″}                → Γ ⋘ Γ′ → Γ′ ⋘ Γ″ → Γ ⋘ Γ″
    [_≔_]_ : ∀ x {A Γ Γ′} {{_ : x ∥ Γ}} → Γ′ ⊢ A → Γ ⋘ Γ′ → Γ , x ∷ A ⋘ Γ′
