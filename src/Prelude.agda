module Prelude where

open import Agda.Primitive public
  using (_⊔_)
  renaming (lsuc to ↑_)


-- Built-in implication.

id : ∀ {ℓ} {X : Set ℓ} → X → X
id x = x

const : ∀ {ℓ ℓ′} {X : Set ℓ} {Y : Set ℓ′} → X → Y → X
const x y = x

flip : ∀ {ℓ ℓ′ ℓ″} {X : Set ℓ} {Y : Set ℓ′} {Z : Set ℓ″} →
       (X → Y → Z) → Y → X → Z
flip P y x = P x y

ap : ∀ {ℓ ℓ′ ℓ″} {X : Set ℓ} {Y : Set ℓ′} {Z : Set ℓ″} →
     (X → Y → Z) → (X → Y) → X → Z
ap f g x = f x (g x)

infixr 9 _∘_
_∘_ : ∀ {ℓ ℓ′ ℓ″} {X : Set ℓ} {Y : Set ℓ′} {Z : Set ℓ″} →
      (Y → Z) → (X → Y) → X → Z
f ∘ g = λ x → f (g x)

refl→ : ∀ {ℓ} {X : Set ℓ} → X → X
refl→ = id

trans→ : ∀ {ℓ ℓ′ ℓ″} {X : Set ℓ} {Y : Set ℓ′} {Z : Set ℓ″} →
          (X → Y) → (Y → Z) → X → Z
trans→ = flip _∘_


-- Built-in verum.

open import Agda.Builtin.Unit public
  using (⊤)
  renaming (tt to ∙)


-- Falsum.

data ⊥ : Set where

{-# HASKELL data AgdaEmpty #-}
{-# COMPILED_DATA ⊥ MAlonzo.Code.Data.Empty.AgdaEmpty #-}

elim⊥ : ∀ {ℓ} {X : Set ℓ} → ⊥ → X
elim⊥ ()


-- Negation.

infix 3 ¬_
¬_ : ∀ {ℓ} → Set ℓ → Set ℓ
¬ X = X → ⊥

_↯_ : ∀ {ℓ ℓ′} {X : Set ℓ} {Y : Set ℓ′} → X → ¬ X → Y
p ↯ ¬p = elim⊥ (¬p p)


-- Built-in equality.

open import Agda.Builtin.Equality public
  using (_≡_ ; refl)

infix 4 _≢_
_≢_ : ∀ {ℓ} {X : Set ℓ} → X → X → Set ℓ
x ≢ x′ = ¬ (x ≡ x′)

trans : ∀ {ℓ} {X : Set ℓ} {x x′ x″ : X} → x ≡ x′ → x′ ≡ x″ → x ≡ x″
trans refl refl = refl

sym : ∀ {ℓ} {X : Set ℓ} {x x′ : X} → x ≡ x′ → x′ ≡ x
sym refl = refl

subst : ∀ {ℓ ℓ′} {X : Set ℓ} → (P : X → Set ℓ′) →
        ∀ {x x′} → x ≡ x′ → P x → P x′
subst P refl p = p

cong : ∀ {ℓ ℓ′} {X : Set ℓ} {Y : Set ℓ′} → (f : X → Y) →
       ∀ {x x′} → x ≡ x′ → f x ≡ f x′
cong f refl = refl

cong² : ∀ {ℓ ℓ′ ℓ″} {X : Set ℓ} {Y : Set ℓ′} {Z : Set ℓ″} → (f : X → Y → Z) →
        ∀ {x x′ y y′} → x ≡ x′ → y ≡ y′ → f x y ≡ f x′ y′
cong² f refl refl = refl

cong³ : ∀ {ℓ ℓ′ ℓ″ ℓ‴} {X : Set ℓ} {Y : Set ℓ′} {Z : Set ℓ″} {A : Set ℓ‴} →
        (f : X → Y → Z → A) →
        ∀ {x x′ y y′ z z′} → x ≡ x′ → y ≡ y′ → z ≡ z′ → f x y z ≡ f x′ y′ z′
cong³ f refl refl refl = refl


-- Equational reasoning with built-in equality.

module _ {ℓ} {X : Set ℓ} where
  infix 1 proof_
  proof_ : ∀ {x x′ : X} → x ≡ x′ → x ≡ x′
  proof p = p

  infixr 2 _≡⟨⟩_
  _≡⟨⟩_ : ∀ (x {x′} : X) → x ≡ x′ → x ≡ x′
  x ≡⟨⟩ p = p

  infixr 2 _≡⟨_⟩_
  _≡⟨_⟩_ : ∀ (x {x′ x″} : X) → x ≡ x′ → x′ ≡ x″ → x ≡ x″
  x ≡⟨ p ⟩ q = trans p q

  infix 3 _∎
  _∎ : ∀ (x : X) → x ≡ x
  x ∎ = refl


-- Constructive existence.

infixl 5 _,_
record Σ {ℓ ℓ′} (X : Set ℓ) (Y : X → Set ℓ′) : Set (ℓ ⊔ ℓ′) where
  constructor _,_
  field
    π₁ : X
    π₂ : Y π₁

open Σ public


-- Conjunction.

infixr 2 _∧_
_∧_ : ∀ {ℓ ℓ′} → Set ℓ → Set ℓ′ → Set (ℓ ⊔ ℓ′)
X ∧ Y = Σ X (λ x → Y)


-- Disjunction.

infixr 1 _∨_
data _∨_ {ℓ ℓ′} (X : Set ℓ) (Y : Set ℓ′) : Set (ℓ ⊔ ℓ′) where
  ι₁ : X → X ∨ Y
  ι₂ : Y → X ∨ Y

{-# HASKELL type AgdaEither _ _ x y = Either x y #-}
{-# COMPILED_DATA _∨_ MAlonzo.Code.Data.Sum.AgdaEither Left Right #-}

elim∨ : ∀ {ℓ ℓ′ ℓ″} {X : Set ℓ} {Y : Set ℓ′} {Z : Set ℓ″} →
        X ∨ Y → (X → Z) → (Y → Z) → Z
elim∨ (ι₁ x) f g = f x
elim∨ (ι₂ y) f g = g y


-- Equivalence.

infix 3 _↔_
_↔_ : ∀ {ℓ ℓ′} → (X : Set ℓ) (Y : Set ℓ′) → Set (ℓ ⊔ ℓ′)
X ↔ Y = (X → Y) ∧ (Y → X)

infix 3 _↮_
_↮_ : ∀ {ℓ ℓ′} → (X : Set ℓ) (Y : Set ℓ′) → Set (ℓ ⊔ ℓ′)
X ↮ Y = ¬ (X ↔ Y)

refl↔ : ∀ {ℓ} {X : Set ℓ} → X ↔ X
refl↔ = refl→ , refl→

trans↔ : ∀ {ℓ ℓ′ ℓ″} {X : Set ℓ} {Y : Set ℓ′} {Z : Set ℓ″} →
          X ↔ Y → Y ↔ Z → X ↔ Z
trans↔ (P , Q) (P′ , Q′) = trans→ P P′ , trans→ Q′ Q

sym↔ : ∀ {ℓ ℓ′} {X : Set ℓ} {Y : Set ℓ′} → X ↔ Y → Y ↔ X
sym↔ (P , Q) = Q , P

antisym→ : ∀ {ℓ ℓ′} {X : Set ℓ} {Y : Set ℓ′} →
            ((X → Y) ∧ (Y → X)) ≡ (X ↔ Y)
antisym→ = refl

≡→↔ : ∀ {ℓ} {X Y : Set ℓ} → X ≡ Y → X ↔ Y
≡→↔ refl = refl↔


-- Equational reasoning with equivalence.

infix 1 proof↔_
proof↔_ : ∀ {ℓ ℓ′} {X : Set ℓ} {Y : Set ℓ′} → X ↔ Y → X ↔ Y
proof↔ P = P

infixr 2 _≡→↔⟨_⟩_
_≡→↔⟨_⟩_ : ∀ {ℓ ℓ′} (X {Y} : Set ℓ) {Z : Set ℓ′} →
             X ≡ Y → Y ↔ Z → X ↔ Z
X ≡→↔⟨ P ⟩ Q = trans↔ (≡→↔ P) Q

infixr 2 _↔⟨⟩_
_↔⟨⟩_ : ∀ {ℓ ℓ′} (X : Set ℓ) {Y : Set ℓ′} → X ↔ Y → X ↔ Y
X ↔⟨⟩ P = P

infixr 2 _↔⟨_⟩_
_↔⟨_⟩_ : ∀ {ℓ ℓ′ ℓ″} (X : Set ℓ) {Y : Set ℓ′} {Z : Set ℓ″} →
          X ↔ Y → Y ↔ Z → X ↔ Z
X ↔⟨ P ⟩ Q = trans↔ P Q

infix 3 _∎↔
_∎↔ : ∀ {ℓ} → (X : Set ℓ) → X ↔ X
X ∎↔ = refl↔


-- Decidability.

data Dec {ℓ} (X : Set ℓ) : Set ℓ where
  yes : X → Dec X
  no  : ¬ X → Dec X

mapDec : ∀ {ℓ ℓ′} {X : Set ℓ} {Y : Set ℓ′} →
         (X → Y) → (Y → X) → Dec X → Dec Y
mapDec f g (yes x) = yes (f x)
mapDec f g (no ¬x) = no (λ y → g y ↯ ¬x)


-- Booleans.

open import Agda.Builtin.Bool public
  using (Bool ; false ; true)

elimBool : ∀ {ℓ} {X : Set ℓ} → Bool → X → X → X
elimBool false z s = z
elimBool true  z s = s

_≟Bool_ : ∀ (b b′ : Bool) → Dec (b ≡ b′)
false ≟Bool false = yes refl
false ≟Bool true  = no (λ ())
true  ≟Bool false = no (λ ())
true  ≟Bool true  = yes refl

⌊_⌋Dec : ∀ {ℓ} {X : Set ℓ} → Dec X → Bool
⌊ yes x ⌋Dec = true
⌊ no ¬x ⌋Dec = false


-- Conditionals.

data Maybe {ℓ} (X : Set ℓ) : Set ℓ where
  nothing : Maybe X
  just    : X → Maybe X

{-# HASKELL type AgdaMaybe _ x = Maybe x #-}
{-# COMPILED_DATA Maybe MAlonzo.Code.Data.Maybe.Base.AgdaMaybe Just Nothing #-}

elimMaybe : ∀ {ℓ ℓ′} {X : Set ℓ} {Y : Set ℓ′} → Maybe X → Y → (X → Y) → Y
elimMaybe nothing  z f = z
elimMaybe (just x) z f = f x


-- Naturals.

open import Agda.Builtin.Nat public
  using (Nat ; zero ; suc)

elimNat : ∀ {ℓ} {X : Set ℓ} → Nat → X → (Nat → X → X) → X
elimNat zero    z f = z
elimNat (suc n) z f = f n (elimNat n z f)

_≟Nat_ : ∀ (n n′ : Nat) → Dec (n ≡ n′)
zero  ≟Nat zero   = yes refl
zero  ≟Nat suc n′ = no (λ ())
suc n ≟Nat zero   = no (λ ())
suc n ≟Nat suc n′ with n ≟Nat n′
suc n ≟Nat suc .n | yes refl = yes refl
suc n ≟Nat suc n′ | no  n≢n′ = no (λ { refl → refl ↯ n≢n′ })
