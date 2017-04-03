module Convertibility where

open import Syntax public


-- 3.4. Convertibility of proof trees

mutual
  infix 4 _≅_
  data _≅_ : ∀ {A Γ} → Γ ⊢ A → Γ ⊢ A → Set where
    refl≅  : ∀ {A Γ} {M : Γ ⊢ A} → M ≅ M

    trans≅ : ∀ {A Γ} {M M′ M″ : Γ ⊢ A} → M ≅ M′ → M′ ≅ M″ → M ≅ M″

    sym≅   : ∀ {A Γ} {M M′ : Γ ⊢ A} → M ≅ M′ → M′ ≅ M

    cong▸  : ∀ {A Δ Γ} {M M′ : Γ ⊢ A} {γ γ′ : Δ ⇛ Γ} →
             M ≅ M′ → γ ≅ₛ γ′ → M ▸ γ ≅ M′ ▸ γ′

    congλ  : ∀ {x A B Γ} {{_ : fresh x Γ}} {M M′ : [ Γ , x ∷ A ] ⊢ B} →
             M ≅ M′ → λ[ x ∷ A ] M ≅ λ[ x ∷ A ] M′

    cong∙  : ∀ {A B Γ} {M M′ : Γ ⊢ A ⇒ B} {N N′ : Γ ⊢ A} →
             M ≅ M′ → N ≅ N′ → M ∙ N ≅ M′ ∙ N′

    conv≅₁ : ∀ {x A B Δ Γ} {{_ : fresh x Γ}} → (M : [ Γ , x ∷ A ] ⊢ B) (N : Δ ⊢ A) (γ : Δ ⇛ Γ) →
             λ[ x ∷ A ] M ▸ γ ∙ N ≅ M ▸ [ γ , x ≔ N ]

    conv≅₂ : ∀ {x A B Γ} {{_ : fresh x Γ}} → (M : Γ ⊢ A ⇒ B) (c : [ Γ , x ∷ A ] ⊇ Γ) →
             M ≅ λ[ x ∷ A ] (M ▸ π c ∙ v[ x ∷ A ] occ₁)

    conv≅₃ : ∀ {x A Δ Γ} {{_ : fresh x Γ}} → (M : Δ ⊢ A) (γ : Δ ⇛ Γ) →
             v[ x ∷ A ] occ₁ ▸ [ γ , x ≔ M ] ≅ M

    conv≅₄ : ∀ {x A Δ Γ} → (i : Occur x A Γ) (j : Occur x A Δ) (c : Δ ⊇ Γ) →
             v[ x ∷ A ] i ▸ π c ≅ v[ x ∷ A ] j

    conv≅₅ : ∀ {A Γ} → (M : Γ ⊢ A) (c : Γ ⊇ Γ) →
             M ▸ π c ≅ M

    conv≅₆ : ∀ {A B Δ Γ} → (M : Γ ⊢ A ⇒ B) (N : Γ ⊢ A) (γ : Δ ⇛ Γ) →
             (M ∙ N) ▸ γ ≅ (M ▸ γ) ∙ (N ▸ γ)

    conv≅₇ : ∀ {A Θ Δ Γ} → (M : Γ ⊢ A) (δ : Δ ⇛ Θ) (γ : Θ ⇛ Γ) →
             (M ▸ γ) ▸ δ ≅ M ▸ (γ ∘ δ)

  infix 4 _≅ₛ_
  data _≅ₛ_ : ∀ {Δ Γ} → Δ ⇛ Γ → Δ ⇛ Γ → Set where
     refl≅ₛ  : ∀ {Δ Γ} {γ : Δ ⇛ Γ} → γ ≅ₛ γ

     trans≅ₛ : ∀ {Δ Γ} {γ γ′ γ″ : Δ ⇛ Γ} → γ ≅ₛ γ′ → γ′ ≅ₛ γ″ → γ ≅ₛ γ″

     sym≅ₛ   : ∀ {Δ Γ} {γ γ′ : Δ ⇛ Γ} → γ ≅ₛ γ′ → γ′ ≅ₛ γ

     congπ   : ∀ {Δ Γ} {c c′ : Δ ⊇ Γ} →
               c ≡ c′ → π c ≅ₛ π c′

     cong∘   : ∀ {Θ Δ Γ} {δ δ′ : Δ ⇛ Θ} {γ γ′ : Θ ⇛ Γ} →
               δ ≅ₛ δ′ → γ ≅ₛ γ′ → γ ∘ δ ≅ₛ γ′ ∘ δ′

     cong≔   : ∀ {x A Δ Γ} {{_ : fresh x Γ}} {M M′ : Δ ⊢ A} {γ γ′ : Δ ⇛ Γ} →
               M ≅ M′ → γ ≅ₛ γ′ → [ γ , x ≔ M ] ≅ₛ [ γ′ , x ≔ M′ ]

     conv≅ₛ₁ : ∀ {Ω Θ Δ Γ} → (θ : Ω ⇛ Δ) (δ : Δ ⇛ Θ) (γ : Θ ⇛ Γ) →
               (γ ∘ δ) ∘ θ ≅ₛ γ ∘ (δ ∘ θ)

     conv≅ₛ₂ : ∀ {x A Θ Δ Γ} {{_ : fresh x Γ}} → (M : Θ ⊢ A) (δ : Δ ⇛ Θ) (γ : Θ ⇛ Γ) →
               [ γ , x ≔ M ] ∘ δ ≅ₛ [ γ ∘ δ , x ≔ M ▸ δ ]

     conv≅ₛ₃ : ∀ {x A Δ Γ} {{_ : fresh x Γ}} → (M : Δ ⊢ A) (γ : Δ ⇛ Γ) (c : [ Γ , x ∷ A ] ⊇ Γ) →
               π c ∘ [ γ , x ≔ M ] ≅ₛ γ

     conv≅s₄ : ∀ {Θ Δ Γ} → (c₁ : Δ ⊇ Γ) (c₂ : Θ ⊇ Δ) (c₃ : Θ ⊇ Γ) →
               π c₁ ∘ π c₂ ≅ₛ π c₃

     conv≅ₛ₅ : ∀ {Δ Γ} → (γ : Γ ⇛ Δ) (c : Γ ⊇ Γ) →
               γ ∘ π c ≅ₛ γ

     conv≅ₛ₆ : ∀ {Γ} → (γ : Γ ⇛ []) (c : Γ ⊇ []) →
               γ ≅ₛ π c

     conv≅ₛ₇ : ∀ {x A Δ Γ} {{_ : fresh x Γ}} → (i : Occur x A Δ) (γ : Δ ⇛ [ Γ , x ∷ A ]) (c : [ Γ , x ∷ A ] ⊇ Γ) →
               γ ≅ₛ [ π c ∘ γ , x ≔ v[ x ∷ A ] i ]


-- Lemmas

≡→≅ : ∀ {A Γ} {M M′ : Γ ⊢ A} → M ≡ M′ → M ≅ M′
≡→≅ refl = refl≅

≡→≅ₛ : ∀ {Δ Γ} {γ γ′ : Δ ⇛ Γ} → γ ≡ γ′ → γ ≅ₛ γ′
≡→≅ₛ refl = refl≅ₛ


-- Equational reasoning

infix 1 proof≅_
proof≅_ : ∀ {A Γ} {M M′ : Γ ⊢ A} → M ≅ M′ → M ≅ M′
proof≅_ p = p

infixr 2 _≡→≅⟨_⟩_
_≡→≅⟨_⟩_ : ∀ {A Γ} (M {M′ M″} : Γ ⊢ A) → M ≡ M′ → M′ ≅ M″ → M ≅ M″
M ≡→≅⟨ p ⟩ p′ = trans≅ (≡→≅ p) p′

infixr 2 _≅⟨⟩_
_≅⟨⟩_ : ∀ {A Γ} (M {M′} : Γ ⊢ A) → M ≅ M′ → M ≅ M′
M ≅⟨⟩ p = p

infixr 2 _≅⟨_⟩_
_≅⟨_⟩_ : ∀ {A Γ} (M {M′ M″} : Γ ⊢ A) → M ≅ M′ → M′ ≅ M″ → M ≅ M″
M ≅⟨ p ⟩ p′ = trans≅ p p′

infix 3 _∎≅
_∎≅ : ∀ {A Γ} (M : Γ ⊢ A) → M ≅ M
M ∎≅ = refl≅


-- Equational reasoning for substitutions

infix 1 proof≅ₛ_
proof≅ₛ_ : ∀ {Δ Γ} {γ γ′ : Δ ⇛ Γ} → γ ≅ₛ γ′ → γ ≅ₛ γ′
proof≅ₛ_ p = p

infixr 2 _≡→≅ₛ⟨_⟩_
_≡→≅ₛ⟨_⟩_ : ∀ {Δ Γ} (γ {γ′ γ″} : Δ ⇛ Γ) → γ ≡ γ′ → γ′ ≅ₛ γ″ → γ ≅ₛ γ″
γ ≡→≅ₛ⟨ p ⟩ p′ = trans≅ₛ (≡→≅ₛ p) p′

infixr 2 _≅ₛ⟨⟩_
_≅ₛ⟨⟩_ : ∀ {Δ Γ} (γ {γ′} : Δ ⇛ Γ) → γ ≅ₛ γ′ → γ ≅ₛ γ′
γ ≅ₛ⟨⟩ p = p

infixr 2 _≅ₛ⟨_⟩_
_≅ₛ⟨_⟩_ : ∀ {Δ Γ} (γ {γ′ γ″} : Δ ⇛ Γ) → γ ≅ₛ γ′ → γ′ ≅ₛ γ″ → γ ≅ₛ γ″
γ ≅ₛ⟨ p ⟩ p′ = trans≅ₛ p p′

infix 3 _∎≅ₛ
_∎≅ₛ : ∀ {Δ Γ} (γ : Δ ⇛ Γ) → γ ≅ₛ γ
γ ∎≅ₛ = refl≅ₛ
