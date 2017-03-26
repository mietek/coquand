module Convertibility where

open import Syntax public


-- Convertibility of derivations.

mutual
  infix 4 _≅⊦_
  data _≅⊦_ : ∀ {A Γ} → Γ ⊢ A → Γ ⊢ A → Set where
    refl≅⊦  : ∀ {A Γ} {d : Γ ⊢ A} → d ≅⊦ d

    trans≅⊦ : ∀ {A Γ} {d d′ d″ : Γ ⊢ A} → d ≅⊦ d′ → d′ ≅⊦ d″ → d ≅⊦ d″

    sym≅⊦   : ∀ {A Γ} {d d′ : Γ ⊢ A} → d ≅⊦ d′ → d′ ≅⊦ d


    -- Congruences.

    conglam : ∀ {x A B Γ} {{_ : x ∥ Γ}} {d d′ : Γ , x ∷ A ⊢ B} →
              d ≅⊦ d′ → lam x d ≅⊦ lam x d′

    congapp : ∀ {A B Γ} {d d′ : Γ ⊢ A ⇒ B} {e e′ : Γ ⊢ A} →
              d ≅⊦ d′ → e ≅⊦ e′ → app d e ≅⊦ app d′ e′

    cong◂   : ∀ {A Γ Γ′} {d d′ : Γ ⊢ A} {s s′ : Γ ⋘ Γ′} →
              d ≅⊦ d′ → s ≅« s′ → d ◂ s ≅⊦ d′ ◂ s′


    -- Conversions.

    reduce⇒   : ∀ {x A B Γ Γ′} {{_ : x ∥ Γ}} → (d : Γ , x ∷ A ⊢ B) (e : Γ′ ⊢ A) (s : Γ ⋘ Γ′) →
                 app (lam x d ◂ s) e ≅⊦ d ◂ [ x ≔ e ] s

    expand⇒   : ∀ {x A B Γ} {{_ : x ∥ Γ}} → (d : Γ ⊢ A ⇒ B) (l : Γ ⊆ Γ , x ∷ A) →
                 d ≅⊦ lam x (app (d ◂ sub l) (var x top))

    convert≅⊦₁ : ∀ {x A Γ Γ′} {{_ : x ∥ Γ}} → (d : Γ′ ⊢ A) (s : Γ ⋘ Γ′) →
                 var x top ◂ [ x ≔ d ] s ≅⊦ d

    convert≅⊦₂ : ∀ {x A Γ Γ′} → (i : x ∷ A ∈ Γ) (i′ : x ∷ A ∈ Γ′) (l : Γ ⊆ Γ′) →
                 var x i ◂ sub l ≅⊦ var x i′

    convert≅⊦₃ : ∀ {A Γ} → (d : Γ ⊢ A) (l : Γ ⊆ Γ) →
                 d ◂ sub l ≅⊦ d

    convert≅⊦₄ : ∀ {A B Γ Γ′} → (d : Γ ⊢ A ⇒ B) (e : Γ ⊢ A) (s : Γ ⋘ Γ′) →
                 app d e ◂ s ≅⊦ app (d ◂ s) (e ◂ s)

    convert≅⊦₅ : ∀ {A Γ Γ′ Γ″} → (d : Γ ⊢ A) (l : Γ ⋘ Γ′) (l′ : Γ′ ⋘ Γ″) →
                 (d ◂ l) ◂ l′ ≅⊦ d ◂ (l • l′)


-- Convertibility of substitutions.

  infix 4 _≅«_
  data _≅«_ : ∀ {Γ Γ′} → Γ ⋘ Γ′ → Γ ⋘ Γ′ → Set where
    refl≅«  : ∀ {Γ Γ′} {s : Γ ⋘ Γ′} → s ≅« s

    trans≅« : ∀ {Γ Γ′} {s s′ s″ : Γ ⋘ Γ′} → s ≅« s′ → s′ ≅« s″ → s ≅« s″

    sym≅«   : ∀ {Γ Γ′} {s s′ : Γ ⋘ Γ′} → s ≅« s′ → s′ ≅« s


    -- Congruences.

    congsub : ∀ {Γ Γ′} {l l′ : Γ ⊆ Γ′} →
              l ≡ l′ → sub l ≅« sub l′

    cong•   : ∀ {Γ Γ′ Γ″} {s s′ : Γ ⋘ Γ′} {t t′ : Γ′ ⋘ Γ″} →
              s ≅« s′ → t ≅« t′ → s • t ≅« s′ • t′

    cong≔   : ∀ {x A Γ Γ′} {{_ : x ∥ Γ}} {d d′ : Γ′ ⊢ A} {s s′ : Γ ⋘ Γ′} →
              d ≅⊦ d′ → s ≅« s′ → [ x ≔ d ] s ≅« [ x ≔ d′ ] s′


    -- Conversions.

    convert≅«₁ : ∀ {Γ Γ′ Γ″ Γ‴} → (s : Γ ⋘ Γ′) (s′ : Γ′ ⋘ Γ″) (s″ : Γ″ ⋘ Γ‴) →
                 (s • s′) • s″ ≅« s • (s′ • s″)

    convert≅«₂ : ∀ {x A Γ Γ′ Γ″} {{_ : x ∥ Γ}} → (d : Γ′ ⊢ A) (s : Γ ⋘ Γ′) (s′ : Γ′ ⋘ Γ″) →
                 [ x ≔ d ] s • s′ ≅« [ x ≔ d ◂ s′ ] (s • s′)

    convert≅«₃ : ∀ {x A Γ Γ′} {{_ : x ∥ Γ}} → (l : Γ ⊆ Γ , x ∷ A) (d : Γ′ ⊢ A) (s : Γ ⋘ Γ′) →
                 sub l • [ x ≔ d ] s ≅« s

    convert≅«₄ : ∀ {Γ Γ′ Γ″} → (l : Γ ⊆ Γ′) (l′ : Γ′ ⊆ Γ″) (l″ : Γ ⊆ Γ″) →
                 sub l • sub l′ ≅« sub l″

    convert≅«₅ : ∀ {Γ Γ′} → (s : Γ ⋘ Γ′) (l : Γ′ ⊆ Γ′) →
                 s • sub l ≅« s

    convert≅«₆ : ∀ {Γ} → (s : ∅ ⋘ Γ) (l : ∅ ⊆ Γ) →
                 s ≅« sub l

    convert≅«₇ : ∀ {x A Γ Γ′} {{_ : x ∥ Γ}} → (i : x ∷ A ∈ Γ , x ∷ A) (s : Γ , x ∷ A ⋘ Γ′) (l : Γ ⊆ Γ , x ∷ A) →
                 s ≅« [ x ≔ var x i ◂ s ] (sub l • s)


-- Lemmas.

≡→≅⊦ : ∀ {A Γ} {d d′ : Γ ⊢ A} → d ≡ d′ → d ≅⊦ d′
≡→≅⊦ refl = refl≅⊦

≡→≅« : ∀ {Γ Γ′} {s s′ : Γ ⋘ Γ′} → s ≡ s′ → s ≅« s′
≡→≅« refl = refl≅«


-- Equational reasoning with convertibility of derivations.

infix 1 proof≅⊦_
proof≅⊦_ : ∀ {A Γ} {d d′ : Γ ⊢ A} → d ≅⊦ d′ → d ≅⊦ d′
proof≅⊦_ p = p

infixr 2 _≡→≅⊦⟨_⟩_
_≡→≅⊦⟨_⟩_ : ∀ {A Γ} (d {d′ d″} : Γ ⊢ A) → d ≡ d′ → d′ ≅⊦ d″ → d ≅⊦ d″
d ≡→≅⊦⟨ p ⟩ p′ = trans≅⊦ (≡→≅⊦ p) p′

infixr 2 _≅⊦⟨⟩_
_≅⊦⟨⟩_ : ∀ {A Γ} (d {d′} : Γ ⊢ A) → d ≅⊦ d′ → d ≅⊦ d′
d ≅⊦⟨⟩ p = p

infixr 2 _≅⊦⟨_⟩_
_≅⊦⟨_⟩_ : ∀ {A Γ} (d {d′ d″} : Γ ⊢ A) → d ≅⊦ d′ → d′ ≅⊦ d″ → d ≅⊦ d″
d ≅⊦⟨ p ⟩ p′ = trans≅⊦ p p′

infix 3 _∎≅⊦
_∎≅⊦ : ∀ {A Γ} (d : Γ ⊢ A) → d ≅⊦ d
d ∎≅⊦ = refl≅⊦


-- Equational reasoning with convertibility of substitutions.

infix 1 proof≅«_
proof≅«_ : ∀ {Γ Γ′} {s s′ : Γ ⋘ Γ′} → s ≅« s′ → s ≅« s′
proof≅«_ p = p

infixr 2 _≡→≅«⟨_⟩_
_≡→≅«⟨_⟩_ : ∀ {Γ Γ′} (s {s′ s″} : Γ ⋘ Γ′) → s ≡ s′ → s′ ≅« s″ → s ≅« s″
s ≡→≅«⟨ p ⟩ p′ = trans≅« (≡→≅« p) p′

infixr 2 _≅«⟨⟩_
_≅«⟨⟩_ : ∀ {Γ Γ′} (s {s′} : Γ ⋘ Γ′) → s ≅« s′ → s ≅« s′
s ≅«⟨⟩ p = p

infixr 2 _≅«⟨_⟩_
_≅«⟨_⟩_ : ∀ {Γ Γ′} (s {s′ s″} : Γ ⋘ Γ′) → s ≅« s′ → s′ ≅« s″ → s ≅« s″
s ≅«⟨ p ⟩ p′ = trans≅« p p′

infix 3 _∎≅«
_∎≅« : ∀ {Γ Γ′} (s : Γ ⋘ Γ′) → s ≅« s
s ∎≅« = refl≅«
