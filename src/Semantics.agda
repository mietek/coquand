module Semantics where

open import Syntax public


-- Kripke models.

record Model : Set₁ where
  infix 3 _⊩ₒ
  field
    World  : Set
    _≤_    : World → World → Set
    refl≤  : ∀ {w} → w ≤ w
    trans≤ : ∀ {w w′ w″} → w ≤ w′ → w′ ≤ w″ → w ≤ w″
    uniq≤  : ∀ {w w′} → (l l′ : w ≤ w′) → l ≡ l′
    _⊩ₒ   : World → Set

open Model {{…}} public


-- Lemmas.

module _ {{_ : Model}} where
  idtrans≤₁ : ∀ {w w′} → (l : w ≤ w′) (l′ : w′ ≤ w′) → trans≤ l l′ ≡ l
  idtrans≤₁ l l′ = uniq≤ (trans≤ l l′) l

  idtrans≤₂ : ∀ {w w′} → (l : w ≤ w) (l′ : w ≤ w′) → trans≤ l l′ ≡ l′
  idtrans≤₂ l l′ = uniq≤ (trans≤ l l′) l′

  assoctrans≤ : ∀ {w w′ w″ w‴} → (l : w ≤ w′) (l′ : w′ ≤ w″) (l″ : w″ ≤ w‴) →
                trans≤ l (trans≤ l′ l″) ≡ trans≤ (trans≤ l l′) l″
  assoctrans≤ l l′ l″ = uniq≤ (trans≤ l (trans≤ l′ l″)) (trans≤ (trans≤ l l′) l″)

  comptrans≤ : ∀ {w w′ w″} → (l : w ≤ w′) (l′ : w′ ≤ w″) (l″ : w ≤ w″) →
               trans≤ l l′ ≡ l″
  comptrans≤ l l′ l″ = uniq≤ (trans≤ l l′) l″


-- Forcing.

module _ {{_ : Model}} where
  mutual
    infix 3 _⊩_
    _⊩_ : World → Type → Set
    w ⊩ ○      = w ⟦○⟧
    w ⊩ A ⇒ B = w ⟦ A ⇒ B ⟧

    _⟦○⟧ : World → Set
    w ⟦○⟧ = ∀ {w′} → w ≤ w′ → w′ ⊩ₒ

    _⟦_⇒_⟧ : World → Type → Type → Set
    w ⟦ A ⇒ B ⟧ = ∀ {w′} → w ≤ w′ → w′ ⊩ A → w′ ⊩ B

  ⟦pac⟧ : ∀ {w} → w ⊩ ○ → w ⟦○⟧
  ⟦pac⟧ f l = f l

  ⟦app⟧⟪_,_⟫ : ∀ A B {w} → w ⊩ A ⇒ B → w ⟦ A ⇒ B ⟧
  ⟦app⟧⟪ A , B ⟫ f l a = f l a


-- Lemmas.

module _ {{_ : Model}} where
  mono≤⊩⟪_⟫ : ∀ A {w w′} → w ≤ w′ → w ⊩ A → w′ ⊩ A
  mono≤⊩⟪ ○ ⟫      l a = a ∘ trans≤ l
  mono≤⊩⟪ A ⇒ B ⟫ l a = a ∘ trans≤ l


-- Extensional equality and uniformity of semantic objects.

module _ {{_ : Model}} where
  mutual
    infix 4 ⟦=⟧
    syntax ⟦=⟧ {A} f f′ = f ⟦=⟧⟪ A ⟫ f′

    ⟦=⟧ : ∀ {A w} → w ⊩ A → w ⊩ A → Set
    ⟦=⟧ {○}      {w} f f′ = ∀ {w′} → (l : w ≤ w′) → ⟦pac⟧ f l ≡ ⟦pac⟧ f′ l
    ⟦=⟧ {A ⇒ B} {w} f f′ = ∀ {w′} {a : w′ ⊩ A} → (l : w ≤ w′) → ⟦♯⟧⟪ A ⟫ a →
                            ⟦app⟧⟪ A , B ⟫ f l a ⟦=⟧⟪ B ⟫ ⟦app⟧⟪ A , B ⟫ f′ l a

    ⟦♯⟧⟪_⟫ : ∀ A {w} → w ⊩ A → Set
    ⟦♯⟧⟪ ○ ⟫      {w} f = ⊤
    ⟦♯⟧⟪ A ⇒ B ⟫ {w} f = ((∀ {w′} {a : w′ ⊩ A} → (l : w ≤ w′) → ⟦♯⟧⟪ A ⟫ a →
                           ⟦♯⟧⟪ B ⟫ (⟦app⟧⟪ A , B ⟫ f l a)) ∧
                          (∀ {w′} {a a′ : w′ ⊩ A} → (l : w ≤ w′) → ⟦♯⟧⟪ A ⟫ a → ⟦♯⟧⟪ A ⟫ a′ → a ⟦=⟧⟪ A ⟫ a′ →
                           ⟦app⟧⟪ A , B ⟫ f l a ⟦=⟧⟪ B ⟫ ⟦app⟧⟪ A , B ⟫ f l a′)) ∧
                          (∀ {w′ w″} {a : w′ ⊩ A} → (l : w ≤ w′) (l′ : w′ ≤ w″) (l″ : w ≤ w″) → ⟦♯⟧⟪ A ⟫ a →
                           mono≤⊩⟪ B ⟫ l′ (⟦app⟧⟪ A , B ⟫ f l a) ⟦=⟧⟪ B ⟫ ⟦app⟧⟪ A , B ⟫ f l″ (mono≤⊩⟪ A ⟫ l′ a))


-- Lemmas.

module _ {{_ : Model}} where
  refl⟦=⟧⟪_⟫ : ∀ A {w} {a : w ⊩ A} → a ⟦=⟧⟪ A ⟫ a
  refl⟦=⟧⟪ ○ ⟫      = λ l → refl
  refl⟦=⟧⟪ A ⇒ B ⟫ = λ l u → refl⟦=⟧⟪ B ⟫

  trans⟦=⟧⟪_⟫ : ∀ A {w} {a a′ a″ : w ⊩ A} → a ⟦=⟧⟪ A ⟫ a′ → a′ ⟦=⟧⟪ A ⟫ a″ → a ⟦=⟧⟪ A ⟫ a″
  trans⟦=⟧⟪ ○ ⟫      e e′ = λ l → trans (e l) (e′ l)
  trans⟦=⟧⟪ A ⇒ B ⟫ e e′ = λ l u → trans⟦=⟧⟪ B ⟫ (e l u) (e′ l u)

  sym⟦=⟧⟪_⟫ : ∀ A {w} {a a′ : w ⊩ A} → a ⟦=⟧⟪ A ⟫ a′ → a′ ⟦=⟧⟪ A ⟫ a
  sym⟦=⟧⟪ ○ ⟫      e = λ l → sym (e l)
  sym⟦=⟧⟪ A ⇒ B ⟫ e = λ l u → sym⟦=⟧⟪ B ⟫ (e l u)

  cong⟦app⟧⟪_,_⟫ : ∀ A B {w w′} {f f′ : w ⊩ A ⇒ B} {a a′ : w′ ⊩ A} → (l : w ≤ w′) →
                   ⟦♯⟧⟪ A ⇒ B ⟫ f → ⟦♯⟧⟪ A ⇒ B ⟫ f′ → ⟦♯⟧⟪ A ⟫ a → ⟦♯⟧⟪ A ⟫ a′ → f ⟦=⟧⟪ A ⇒ B ⟫ f′ → a ⟦=⟧⟪ A ⟫ a′ →
                   ⟦app⟧⟪ A , B ⟫ f l a ⟦=⟧⟪ B ⟫ ⟦app⟧⟪ A , B ⟫ f′ l a′
  cong⟦app⟧⟪ A , B ⟫ l (h , h′ , h″) u′ v v′ e e′ = trans⟦=⟧⟪ B ⟫ (h′ l v v′ e′) (e l v′)

  mono≤⟦=⟧⟪_⟫ : ∀ A {w w′} {a a′ : w ⊩ A} → (l : w ≤ w′) → a ⟦=⟧⟪ A ⟫ a′ →
                mono≤⊩⟪ A ⟫ l a ⟦=⟧⟪ A ⟫ mono≤⊩⟪ A ⟫ l a′
  mono≤⟦=⟧⟪ ○ ⟫      l e = λ l′ → e (trans≤ l l′)
  mono≤⟦=⟧⟪ A ⇒ B ⟫ l e = λ l′ → e (trans≤ l l′)

  mono≤⟦♯⟧⟪_⟫ : ∀ A {w w′} {a : w ⊩ A} → (l : w ≤ w′) → ⟦♯⟧⟪ A ⟫ a →
                ⟦♯⟧⟪ A ⟫ (mono≤⊩⟪ A ⟫ l a)
  mono≤⟦♯⟧⟪ ○ ⟫      l ∙             = ∙
  mono≤⟦♯⟧⟪ A ⇒ B ⟫ l (h , h′ , h″) = (λ l′ → h (trans≤ l l′)) ,
                                       (λ l′ → h′ (trans≤ l l′)) ,
                                       (λ l′ l″ l‴ → h″ (trans≤ l l′) l″ (trans≤ l l‴))

  ≡→⟦=⟧⟪_⟫ : ∀ A {w} {a a′ : w ⊩ A} → a ≡ a′ → a ⟦=⟧⟪ A ⟫ a′
  ≡→⟦=⟧⟪ A ⟫ refl = refl⟦=⟧⟪ A ⟫


-- Equational reasoning with extensional equality of semantic objects.

module _ {{_ : Model}} where
  infix 1 proof⟦=⟧
  syntax proof⟦=⟧ {A} e = proof⟦=⟧⟪ A ⟫ e

  proof⟦=⟧ : ∀ {A Γ} {a a′ : Γ ⊩ A} → a ⟦=⟧⟪ A ⟫ a′ → a ⟦=⟧⟪ A ⟫ a′
  proof⟦=⟧ {A} e = e

  infixr 2 ≡→⟦=⟧⟨…⟩
  syntax ≡→⟦=⟧⟨…⟩ {A} a e e′ = a ≡→⟦=⟧⟪ A ⟫⟨ e ⟩ e′

  ≡→⟦=⟧⟨…⟩ : ∀ {A Γ} (a {a′ a″} : Γ ⊩ A) → a ≡ a′ → a′ ⟦=⟧⟪ A ⟫ a″ → a ⟦=⟧⟪ A ⟫ a″
  ≡→⟦=⟧⟨…⟩ {A} a e e′ = trans⟦=⟧⟪ A ⟫ (≡→⟦=⟧⟪ A ⟫ e) e′

  infixr 2 ⟦=⟧⟨⟩
  syntax ⟦=⟧⟨⟩ {A} a e = a ⟦=⟧⟪ A ⟫⟨⟩ e

  ⟦=⟧⟨⟩ : ∀ {A Γ} (a {a′} : Γ ⊩ A) → a ⟦=⟧⟪ A ⟫ a′ → a ⟦=⟧⟪ A ⟫ a′
  ⟦=⟧⟨⟩ {A} a e = e

  infixr 2 ⟦=⟧⟨…⟩
  syntax ⟦=⟧⟨…⟩ {A} a e e′ = a ⟦=⟧⟪ A ⟫⟨ e ⟩ e′

  ⟦=⟧⟨…⟩ : ∀ {A Γ} (a {a′ a″} : Γ ⊩ A) → a ⟦=⟧⟪ A ⟫ a′ → a′ ⟦=⟧⟪ A ⟫ a″ → a ⟦=⟧⟪ A ⟫ a″
  ⟦=⟧⟨…⟩ {A} a e e′ = trans⟦=⟧⟪ A ⟫ e e′

  infix 3 ∎⟦=⟧
  syntax ∎⟦=⟧ {A} a = a ∎⟦=⟧⟪ A ⟫

  ∎⟦=⟧ : ∀ {A Γ} (a : Γ ⊩ A) → a ⟦=⟧⟪ A ⟫ a
  ∎⟦=⟧ {A} a = refl⟦=⟧⟪ A ⟫


-- Lemmas.

module _ {{_ : Model}} where
  idmono≤⊩⟪_⟫ : ∀ A {w} {a : w ⊩ A} → (l : w ≤ w) →  mono≤⊩⟪ A ⟫ l a ⟦=⟧⟪ A ⟫ a
  idmono≤⊩⟪ ○ ⟫      {a = f} l = λ l′ → cong f (idtrans≤₂ l l′)
  idmono≤⊩⟪ A ⇒ B ⟫ {a = f} l = λ l′ u → ≡→⟦=⟧⟪ B ⟫ (cong² f (idtrans≤₂ l l′) refl)

  assocmono≤⊩⟪_⟫ : ∀ A {w w′ w″} {a : w ⊩ A} → (l : w ≤ w′) (l′ : w′ ≤ w″) (l″ : w ≤ w″) →
                    mono≤⊩⟪ A ⟫ l′ (mono≤⊩⟪ A ⟫ l a) ⟦=⟧⟪ A ⟫ mono≤⊩⟪ A ⟫ l″ a
  assocmono≤⊩⟪ ○ ⟫      {a = f} l l′ l″         = λ l‴ →
    proof
      f (trans≤ l (trans≤ l′ l‴))
    ≡⟨ cong f (assoctrans≤ l l′ l‴) ⟩
      f (trans≤ (trans≤ l l′) l‴)
    ≡⟨ cong f (cong² trans≤ (comptrans≤ l l′ l″) refl) ⟩
      f (trans≤ l″ l‴)
    ∎
  assocmono≤⊩⟪ A ⇒ B ⟫ {a = f} l l′ l″ {a = a} = λ l‴ u →
    proof⟦=⟧⟪ B ⟫
      f (trans≤ l (trans≤ l′ l‴)) a
    ≡→⟦=⟧⟪ B ⟫⟨ cong² f (assoctrans≤ l l′ l‴) refl ⟩
      f (trans≤ (trans≤ l l′) l‴) a
    ≡→⟦=⟧⟪ B ⟫⟨ cong² f (cong² trans≤ (comptrans≤ l l′ l″) refl) refl ⟩
      f (trans≤ l″ l‴) a
    ∎⟦=⟧⟪ B ⟫

  fnord⟦app⟧⟪_,_⟫ : ∀ A B {w w′} {f : w ⊩ A ⇒ B} {a : w′ ⊩ A} → (l : w ≤ w′) (l′ : w′ ≤ w′) →
                  ⟦app⟧⟪ A , B ⟫ f l a ⟦=⟧⟪ B ⟫ ⟦app⟧⟪ A , B ⟫ (mono≤⊩⟪ A ⇒ B ⟫ l f) l′ a
  fnord⟦app⟧⟪ A , B ⟫ {f = f} {a} l l′ =
    proof⟦=⟧⟪ B ⟫
      ⟦app⟧⟪ A , B ⟫ f l a
    ≡→⟦=⟧⟪ B ⟫⟨ cong² f (sym (idtrans≤₁ l l′)) refl ⟩
      ⟦app⟧⟪ A , B ⟫ (mono≤⊩⟪ A ⇒ B ⟫ l f) l′ a
    ∎⟦=⟧⟪ B ⟫


-- Semantic environments.

module _ {{_ : Model}} where
  infix 3 _⊩⋆_
  _⊩⋆_ : World → Context → Set
  w ⊩⋆ ∅         = ⊤
  w ⊩⋆ Γ , x ∷ A = w ⊩⋆ Γ ∧ w ⊩ A

  lookup : ∀ {Γ x A w} → w ⊩⋆ Γ → x ∷ A ∈ Γ → w ⊩ A
  lookup {∅}         ∙       ()
  lookup {Γ , x ∷ A} (γ , a) top     = a
  lookup {Γ , y ∷ B} (γ , b) (pop i) = lookup γ i

  mono≤⊩⋆ : ∀ {Γ w w′} → w ≤ w′ → w ⊩⋆ Γ → w′ ⊩⋆ Γ
  mono≤⊩⋆ {∅}         l ∙       = ∙
  mono≤⊩⋆ {Γ , x ∷ A} l (γ , a) = mono≤⊩⋆ l γ , mono≤⊩⟪ A ⟫ l a

  mono⊆⊩⋆ : ∀ {Γ Γ′ w} → Γ ⊆ Γ′ → w ⊩⋆ Γ′ → w ⊩⋆ Γ
  mono⊆⊩⋆ bot        γ = ∙
  mono⊆⊩⋆ (push l i) γ = mono⊆⊩⋆ l γ , lookup γ i


-- Extensional equality and uniformity of semantic environments.

module _ {{_ : Model}} where
  infix 4 _⟦=⟧⋆_
  _⟦=⟧⋆_ : ∀ {Γ w} → w ⊩⋆ Γ → w ⊩⋆ Γ → Set
  _⟦=⟧⋆_ {∅}         ∙       ∙         = ⊤
  _⟦=⟧⋆_ {Γ , x ∷ A} (γ , a) (γ′ , a′) = γ ⟦=⟧⋆ γ′ ∧ a ⟦=⟧⟪ A ⟫ a′

  ⟦♯⟧⋆ : ∀ {Γ w} → w ⊩⋆ Γ → Set
  ⟦♯⟧⋆ {∅}         ∙       = ⊤
  ⟦♯⟧⋆ {Γ , x ∷ A} (γ , a) = ⟦♯⟧⋆ γ ∧ ⟦♯⟧⟪ A ⟫ a


-- Lemmas.

module _ {{_ : Model}} where
  refl⟦=⟧⋆ : ∀ {Γ w} {γ : w ⊩⋆ Γ} → γ ⟦=⟧⋆ γ
  refl⟦=⟧⋆ {∅}         = ∙
  refl⟦=⟧⋆ {Γ , x ∷ A} = refl⟦=⟧⋆ , refl⟦=⟧⟪ A ⟫

  trans⟦=⟧⋆ : ∀ {Γ w} {γ γ′ γ″ : w ⊩⋆ Γ} → γ ⟦=⟧⋆ γ′ → γ′ ⟦=⟧⋆ γ″ → γ ⟦=⟧⋆ γ″
  trans⟦=⟧⋆ {∅}         ∙       ∙         = ∙
  trans⟦=⟧⋆ {Γ , x ∷ A} (ε , e) (ε′ , e′) = trans⟦=⟧⋆ ε ε′ , trans⟦=⟧⟪ A ⟫ e e′

  sym⟦=⟧⋆ : ∀ {Γ w} {γ γ′ : w ⊩⋆ Γ} → γ ⟦=⟧⋆ γ′ → γ′ ⟦=⟧⋆ γ
  sym⟦=⟧⋆ {∅}         ∙       = ∙
  sym⟦=⟧⋆ {Γ , x ∷ A} (ε , e) = sym⟦=⟧⋆ ε , sym⟦=⟧⟪ A ⟫ e

--  prop₁ : ∀ {x A Γ Γ′ w} {γ : w ⊩⋆ Γ′} {i : x ∷ A ∈ Γ} {i′ : x ∷ A ∈ Γ′} → (l : Γ ⊆ Γ′) →
--          lookup γ i′ ⟦=⟧⟪ A ⟫ lookup (mono⊆⊩⋆ l γ) i
--  prop₁ l = {!!}
--
--  prop₂ : ∀ {x A Γ w w′} {γ : w ⊩⋆ Γ} {i : x ∷ A ∈ Γ} → (l : w ≤ w′) →
--          mono≤⊩⟪ A ⟫ l (lookup γ i) ⟦=⟧⟪ A ⟫ lookup (mono≤⊩⋆ l γ) i
--  prop₂ l = {!!}
