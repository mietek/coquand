module Semantics where

open import Syntax public


-- 4. The semantic model

record Model : Set₁ where
  field
    𝒲      : Set
    𝒢      : 𝒲 → Set
    _≥_    : 𝒲 → 𝒲 → Set
    refl≥  : ∀ {w} → w ≥ w
    trans≥ : ∀ {w w′ w″} → w″ ≥ w′ → w′ ≥ w → w″ ≥ w
    uniq≥  : ∀ {w w′} → (c₁ c₂ : w′ ≥ w) → c₁ ≡ c₂


module _ {{𝔪 : Model}} where
  open Model 𝔪

  idtrans≥₁ : ∀ {w w′} → (c : w′ ≥ w) (c′ : w′ ≥ w′) → trans≥ c′ c ≡ c
  idtrans≥₁ c c′ = uniq≥ (trans≥ c′ c) c

  idtrans≥₂ : ∀ {w w′} → (c : w ≥ w) (c′ : w′ ≥ w) → trans≥ c′ c ≡ c′
  idtrans≥₂ c c′ = uniq≥ (trans≥ c′ c) c′

  assoctrans≥ : ∀ {w w′ w″ w‴} → (c : w′ ≥ w) (c′ : w″ ≥ w′) (c″ : w‴ ≥ w″) →
                trans≥ (trans≥ c″ c′) c ≡ trans≥ c″ (trans≥ c′ c)
  assoctrans≥ c c′ c″ = uniq≥ (trans≥ (trans≥ c″ c′) c) (trans≥ c″ (trans≥ c′ c))

  comptrans≥ : ∀ {w w′ w″} → (c : w′ ≥ w) (c′ : w″ ≥ w′) (c″ : w″ ≥ w) →
               trans≥ c′ c ≡ c″
  comptrans≥ c c′ c″ = uniq≥ (trans≥ c′ c) c″


-- 4.1. Semantic objects

module _ {{𝔪 : Model}} where
  open Model 𝔪

  infix 3 _⊩_
  _⊩_ : 𝒲 → 𝒯 → Set
  w ⊩ o      = ∀ {w′} → w′ ≥ w → 𝒢 w′
  w ⊩ A ⇒ B = ∀ {w′} → w′ ≥ w → w′ ⊩ A → w′ ⊩ B

  Ground : ∀ {w} → (∀ {w′} → w′ ≥ w → 𝒢 w′) → w ⊩ o
  Ground = id

  Lambda : ∀ {A B w} → (∀ {w′} → w′ ≥ w → w′ ⊩ A → w′ ⊩ B) → w ⊩ A ⇒ B
  Lambda = id

  syntax Lambda {A} {B} = Λ⟨ A , B ⟩

  ground : ∀ {w w′} → w ⊩ o → w′ ≥ w → 𝒢 w′
  ground f c = f c

  app : ∀ {A B w w′} → w′ ≥ w → w ⊩ A ⇒ B → w′ ⊩ A → w′ ⊩ B
  app c f u = f c u

  syntax app {A} {B} = app⟨ A , B ⟩

  ↑⟨_⟩ : ∀ A {w w′} → w′ ≥ w → w ⊩ A → w′ ⊩ A
  ↑⟨ o ⟩      c u = λ c′ → u (trans≥ c′ c)
  ↑⟨ A ⇒ B ⟩ c u = λ c′ → u (trans≥ c′ c)

  mutual
    Eq⟨_⟩ : ∀ A {w} → w ⊩ A → w ⊩ A → Set
    Eq⟨ o ⟩      {w} u  v  = ∀ {w′} → (c : w′ ≥ w) →
                             ground u c ≡ ground v c
    Eq⟨ A ⇒ B ⟩ {w} u₁ u₂ = ∀ {w′} {v : w′ ⊩ A} → (c : w′ ≥ w) → 𝒰⟨ A ⟩ v →
                             Eq⟨ B ⟩ (app⟨ A , B ⟩ c u₁ v) (app⟨ A , B ⟩ c u₂ v)

    𝒰⟨_⟩ : ∀ A {w} → w ⊩ A → Set
    𝒰⟨ o ⟩      {w} u = ⊤
    𝒰⟨ A ⇒ B ⟩ {w} u = ((∀ {w′} {v : w′ ⊩ A} → (c : w′ ≥ w) → 𝒰⟨ A ⟩ v →
                         𝒰⟨ B ⟩ (app⟨ A , B ⟩ c u v)) ∧
                         (∀ {w′} {v₁ v₂ : w′ ⊩ A} → (c : w′ ≥ w) → 𝒰⟨ A ⟩ v₁ → 𝒰⟨ A ⟩ v₂ → Eq⟨ A ⟩ v₁ v₂ →
                         Eq⟨ B ⟩ (app⟨ A , B ⟩ c u v₁) (app⟨ A , B ⟩ c u v₂))) ∧
                         (∀ {w′ w″} {v : w′ ⊩ A} → (c₁ : w″ ≥ w′) (c₂ : w′ ≥ w) (c₃ : w″ ≥ w) → 𝒰⟨ A ⟩ v →
                         Eq⟨ B ⟩ (↑⟨ B ⟩ c₁ (app⟨ A , B ⟩ c₂ u v)) (app⟨ A , B ⟩ c₃ u (↑⟨ A ⟩ c₁ v)))

  reflEq⟨_⟩ : ∀ A {w} {u : w ⊩ A} → Eq⟨ A ⟩ u u
  reflEq⟨ o ⟩      = λ c → refl
  reflEq⟨ A ⇒ B ⟩ = λ c q → reflEq⟨ B ⟩

  transEq⟨_⟩ : ∀ A {w} {u u′ u″ : w ⊩ A} → Eq⟨ A ⟩ u u′ → Eq⟨ A ⟩ u′ u″ → Eq⟨ A ⟩ u u″
  transEq⟨ o ⟩      p p′ = λ c → trans (p c) (p′ c)
  transEq⟨ A ⇒ B ⟩ p p′ = λ c q → transEq⟨ B ⟩ (p c q) (p′ c q)

  symEq⟨_⟩ : ∀ A {w} {u u′ : w ⊩ A} → Eq⟨ A ⟩ u u′ → Eq⟨ A ⟩ u′ u
  symEq⟨ o ⟩      p = λ c → sym (p c)
  symEq⟨ A ⇒ B ⟩ p = λ c q → symEq⟨ B ⟩ (p c q)

  congEq⟨_,_⟩ : ∀ A B {w w′} {u₁ u₂ : w ⊩ A ⇒ B} {v₁ v₂ : w′ ⊩ A} → (c : w′ ≥ w) →
                𝒰⟨ A ⇒ B ⟩ u₁ → 𝒰⟨ A ⇒ B ⟩ u₂ → 𝒰⟨ A ⟩ v₁ → 𝒰⟨ A ⟩ v₂ → Eq⟨ A ⇒ B ⟩ u₁ u₂ → Eq⟨ A ⟩ v₁ v₂ →
                Eq⟨ B ⟩ (app⟨ A , B ⟩ c u₁ v₁) (app⟨ A , B ⟩ c u₂ v₂)
  congEq⟨ A , B ⟩ c (q₁ , q₁′ , q₁″) q₂ r₁ r₂ p p′ = transEq⟨ B ⟩ (q₁′ c r₁ r₂ p′) (p c r₂)

  Property₁⟨_⟩ : ∀ A {w w′} {u₁ u₂ : w ⊩ A} → (c : w′ ≥ w) → Eq⟨ A ⟩ u₁ u₂ →
                 Eq⟨ A ⟩ (↑⟨ A ⟩ c u₁) (↑⟨ A ⟩ c u₂)
  Property₁⟨ o ⟩      c p = λ c′ → p (trans≥ c′ c)
  Property₁⟨ A ⇒ B ⟩ c p = λ c′ → p (trans≥ c′ c)

  Property₂⟨_⟩ : ∀ A {w w′} {u : w ⊩ A} → (c : w′ ≥ w) → 𝒰⟨ A ⟩ u →
                 𝒰⟨ A ⟩ (↑⟨ A ⟩ c u)
  Property₂⟨ o ⟩      c tt            = tt
  Property₂⟨ A ⇒ B ⟩ c (q , q′ , q″) = (λ c′ → q (trans≥ c′ c)) ,
                                        (λ c′ → q′ (trans≥ c′ c)) ,
                                        (λ c′ c″ c‴ → q″ c′ (trans≥ c″ c) (trans≥ c‴ c))

  Property₃⟨_⟩ : ∀ A {w} {u : w ⊩ A} → 𝒰⟨ A ⟩ u → (c : w ≥ w) →
                 Eq⟨ A ⟩ (↑⟨ A ⟩ c u) u
  Property₃⟨ o ⟩      {u = u} q c = λ c′ → cong u (idtrans≥₂ c c′)
  Property₃⟨ A ⇒ B ⟩ {u = u} q c = λ c′ q′ → {! !}

  Property₄⟨_⟩ : ∀ A {w w′ w″} {u : w ⊩ A} → 𝒰⟨ A ⟩ u → (c₁ : w″ ≥ w′) (c₂ : w′ ≥ w) (c₃ : w″ ≥ w) →
                 Eq⟨ A ⟩ (↑⟨ A ⟩ c₁ (↑⟨ A ⟩ c₂ u)) (↑⟨ A ⟩ c₃ u)
  Property₄⟨ o ⟩      {u = u} q c₁ c₂ c₃ = λ c′ →
    proof
      u (trans≥ (trans≥ c′ c₁) c₂)
    ≡⟨ cong u (assoctrans≥ c₂ c₁ c′) ⟩
      u (trans≥ c′ (trans≥ c₁ c₂))
    ≡⟨ cong u (cong² trans≥ refl (comptrans≥ c₂ c₁ c₃)) ⟩
      u (trans≥ c′ c₃)
    ∎
  Property₄⟨ A ⇒ B ⟩ {u = u} q c₁ c₂ c₃ = {!!}

  Property₅⟨_,_⟩ : ∀ A B {w w′} {u : w ⊩ A ⇒ B} {v : w′ ⊩ A} → (c : w′ ≥ w) → 𝒰⟨ A ⟩ v →
                   Eq⟨ B ⟩ (app⟨ A , B ⟩ c u v) (app⟨ A , B ⟩ refl≥ (↑⟨ A ⇒ B ⟩ c u) v )
  Property₅⟨ A , B ⟩ c q = {!!}


-- Equational reasoning for extensional equality of semantic objects

module _ {{_ : Model}} where
  infix 1 proofEq
  syntax proofEq {A} p = proofEq⟨ A ⟩ p
  proofEq : ∀ {A Γ} {u u′ : Γ ⊩ A} → Eq⟨ A ⟩ u u′ → Eq⟨ A ⟩ u u′
  proofEq {A} p = p

  ≡→Eq⟨_⟩ : ∀ A {w} {u u′ : w ⊩ A} → u ≡ u′ → Eq⟨ A ⟩ u u′
  ≡→Eq⟨ A ⟩ refl = reflEq⟨ A ⟩

  infixr 2 ≡→Eq⟨…⟩
  syntax ≡→Eq⟨…⟩ {A} u p p′ = u ≡→Eq⟨ A ⟩⟨ p ⟩ p′
  ≡→Eq⟨…⟩ : ∀ {A Γ} (u {u′ u″} : Γ ⊩ A) → u ≡ u′ → Eq⟨ A ⟩ u′ u″ → Eq⟨ A ⟩ u u″
  ≡→Eq⟨…⟩ {A} u p p′ = transEq⟨ A ⟩ (≡→Eq⟨ A ⟩ p) p′

  infixr 2 Eq⟨⟩
  syntax Eq⟨⟩ {A} u p = u Eq⟨ A ⟩⟨⟩ p
  Eq⟨⟩ : ∀ {A Γ} (u {u′} : Γ ⊩ A) → Eq⟨ A ⟩ u u′ → Eq⟨ A ⟩ u u′
  Eq⟨⟩ {A} u p = p

  infixr 2 Eq⟨…⟩
  syntax Eq⟨…⟩ {A} u p p′ = u Eq⟨ A ⟩⟨ p ⟩ p′
  Eq⟨…⟩ : ∀ {A Γ} (u {u′ u″} : Γ ⊩ A) → Eq⟨ A ⟩ u u′ → Eq⟨ A ⟩ u′ u″ → Eq⟨ A ⟩ u u″
  Eq⟨…⟩ {A} u e e′ = transEq⟨ A ⟩ e e′

  infix 3 ∎Eq
  syntax ∎Eq {A} u = u ∎Eq⟨ A ⟩
  ∎Eq : ∀ {A Γ} (u : Γ ⊩ A) → Eq⟨ A ⟩ u u
  ∎Eq {A} u = reflEq⟨ A ⟩


-- -- Lemmas.
--
-- module _ {{_ : Model}} where
--   idmono≤⊩⟪_⟫ : ∀ A {w} {a : w ⊩ A} → (l : w ≤ w) →  mono≤⊩⟪ A ⟫ l a ⟦=⟧⟪ A ⟫ a
--   idmono≤⊩⟪ o ⟫      {a = f} l = λ l′ → cong f (idtrans≤₂ l l′)
--   idmono≤⊩⟪ A ⇒ B ⟫ {a = f} l = λ l′ u → ≡→⟦=⟧⟪ B ⟫ (cong² f (idtrans≤₂ l l′) refl)
--
--   assocmono≤⊩⟪_⟫ : ∀ A {w w′ w″} {a : w ⊩ A} → (l : w ≤ w′) (l′ : w′ ≤ w″) (l″ : w ≤ w″) →
--                     mono≤⊩⟪ A ⟫ l′ (mono≤⊩⟪ A ⟫ l a) ⟦=⟧⟪ A ⟫ mono≤⊩⟪ A ⟫ l″ a
--   assocmono≤⊩⟪ o ⟫      {a = f} l l′ l″         = λ l‴ →
--     proof
--       f (trans≤ l (trans≤ l′ l‴))
--     ≡⟨ cong f (assoctrans≤ l l′ l‴) ⟩
--       f (trans≤ (trans≤ l l′) l‴)
--     ≡⟨ cong f (cong² trans≤ (comptrans≤ l l′ l″) refl) ⟩
--       f (trans≤ l″ l‴)
--     ∎
--   assocmono≤⊩⟪ A ⇒ B ⟫ {a = f} l l′ l″ {a = a} = λ l‴ u →
--     proof⟦=⟧⟪ B ⟫
--       f (trans≤ l (trans≤ l′ l‴)) a
--     ≡→⟦=⟧⟪ B ⟫⟨ cong² f (assoctrans≤ l l′ l‴) refl ⟩
--       f (trans≤ (trans≤ l l′) l‴) a
--     ≡→⟦=⟧⟪ B ⟫⟨ cong² f (cong² trans≤ (comptrans≤ l l′ l″) refl) refl ⟩
--       f (trans≤ l″ l‴) a
--     ∎⟦=⟧⟪ B ⟫
--
--   fnord⟦app⟧⟪_,_⟫ : ∀ A B {w w′} {f : w ⊩ A ⇒ B} {a : w′ ⊩ A} → (l : w ≤ w′) (l′ : w′ ≤ w′) →
--                   ⟦app⟧⟪ A , B ⟫ f l a ⟦=⟧⟪ B ⟫ ⟦app⟧⟪ A , B ⟫ (mono≤⊩⟪ A ⇒ B ⟫ l f) l′ a
--   fnord⟦app⟧⟪ A , B ⟫ {f = f} {a} l l′ =
--     proof⟦=⟧⟪ B ⟫
--       ⟦app⟧⟪ A , B ⟫ f l a
--     ≡→⟦=⟧⟪ B ⟫⟨ cong² f (sym (idtrans≤₁ l l′)) refl ⟩
--       ⟦app⟧⟪ A , B ⟫ (mono≤⊩⟪ A ⇒ B ⟫ l f) l′ a
--     ∎⟦=⟧⟪ B ⟫


-- 4.2. Semantic environments

module _ {{𝔪 : Model}} where
  open Model 𝔪

  infix 3 _⊩ₑ_
  data _⊩ₑ_ : 𝒲 → 𝒞 → Set where
    ⟨⟩      : ∀ {w} → w ⊩ₑ []
    ⟨_,_≔_⟩ : ∀ {Γ w} → w ⊩ₑ Γ → ∀ x {A} {{_ : fresh x Γ}} → w ⊩ A → w ⊩ₑ [ Γ , x ∷ A ]

  lookup : ∀ {Γ x A w} → w ⊩ₑ Γ → Occur x A Γ → w ⊩ A
  lookup ⟨⟩            ()
  lookup ⟨ ρ , x ≔ u ⟩ occ₁     = u
  lookup ⟨ ρ , x ≔ u ⟩ (occ₂ i) = lookup ρ i

  ↑ₑ : ∀ {Γ w w′} → w′ ≥ w → w ⊩ₑ Γ → w′ ⊩ₑ Γ
  ↑ₑ {[]}            c ⟨⟩             = ⟨⟩
  ↑ₑ {[ Γ , x ∷ A ]} c ⟨ ρ , .x ≔ u ⟩ = ⟨ ↑ₑ c ρ , x ≔ ↑⟨ A ⟩ c u ⟩

  ↓ₑ : ∀ {Δ Γ w} → Γ ⊇ Δ → w ⊩ₑ Γ → w ⊩ₑ Δ
  ↓ₑ {[]} gt₁        ρ = ⟨⟩
  ↓ₑ {[ Δ , x ∷ A ]} (gt₂ c i) ρ = ⟨ ↓ₑ c ρ , x ≔ lookup ρ i ⟩

  Eqₑ : ∀ {Γ w} → w ⊩ₑ Γ → w ⊩ₑ Γ → Set
  Eqₑ {[]}            ⟨⟩             ⟨⟩               = ⊤
  Eqₑ {[ Γ , x ∷ A ]} ⟨ ρ , .x ≔ u ⟩ ⟨ ρ′ , .x ≔ u′ ⟩ = Eqₑ ρ ρ′ ∧ Eq⟨ A ⟩ u u′

  𝒰ₑ : ∀ {Γ w} → w ⊩ₑ Γ → Set
  𝒰ₑ {[]}            ⟨⟩             = ⊤
  𝒰ₑ {[ Γ , x ∷ A ]} ⟨ ρ , .x ≔ u ⟩ = 𝒰ₑ ρ ∧ 𝒰⟨ A ⟩ u

  reflEqₑ : ∀ {Γ w} {ρ : w ⊩ₑ Γ} → Eqₑ ρ ρ
  reflEqₑ {[]}            {ρ = ⟨⟩}            = tt
  reflEqₑ {[ Γ , x ∷ A ]} {ρ = ⟨ ρ , .x ≔ u ⟩} = reflEqₑ , reflEq⟨ A ⟩

  transEqₑ : ∀ {Γ w} {ρ ρ′ ρ″ : w ⊩ₑ Γ} → Eqₑ ρ ρ′ → Eqₑ ρ′ ρ″ → Eqₑ ρ ρ″
  transEqₑ {[]}            {ρ = ⟨⟩}             {⟨⟩}              {⟨⟩}              tt tt             = tt
  transEqₑ {[ Γ , x ∷ A ]} {ρ = ⟨ ρ , .x ≔ _ ⟩} {⟨ ρ′ , .x ≔ _ ⟩} {⟨ ρ″ , .x ≔ _ ⟩} (ψ , p) (ψ′ , p′) = transEqₑ ψ ψ′ , transEq⟨ A ⟩ p p′

  symEqₑ : ∀ {Γ w} {ρ ρ′ : w ⊩ₑ Γ} → Eqₑ ρ ρ′ → Eqₑ ρ′ ρ
  symEqₑ {[]}            {ρ = ⟨⟩}             {⟨⟩}              tt      = tt
  symEqₑ {[ Γ , x ∷ A ]} {ρ = ⟨ ρ , .x ≔ _ ⟩} {⟨ ρ′ , .x ≔ _ ⟩} (ψ , p) = symEqₑ ψ , symEq⟨ A ⟩ p

  -- TODO:
  -- We can substitute equal semantic environments in lookup, ↑ₑ, ↓ₑ, and the result of applying
  -- these functions to uniform environments is also uniform
  -- We also need to prove the following properties about Eq for semantic environments which basically
  -- say that it doesn't matter in whcih order we lift and project the substitution

-- --  prop₁ : ∀ {x A Γ Γ′ w} {γ : w ⊩ₑ Γ′} {i : x ∷ A ∈ Γ} {i′ : x ∷ A ∈ Γ′} → (l : Γ ⊆ Γ′) → ⟦♯⟧ₑ γ →
-- --          lookup γ i′ ⟦=⟧⟪ A ⟫ lookup (mono⊆⊩ₑ l γ) i
-- --  prop₁ l υ = {!!}
-- --
-- --  prop₂ : ∀ {x A Γ w w′} {γ : w ⊩ₑ Γ} {i : x ∷ A ∈ Γ} → (l : w ≤ w′) → ⟦♯⟧ₑ γ →
-- --          mono≤⊩⟪ A ⟫ l (lookup γ i) ⟦=⟧⟪ A ⟫ lookup (mono≤⊩ₑ l γ) i
-- --  prop₂ l υ = {!!}


-- 4.3. The semantics of the λ-calculus

module _ {{𝔪 : Model}} where
  open Model 𝔪

  mutual
    ⟦_⟧ : ∀ {A Γ w} → Γ ⊢ A → w ⊩ₑ Γ → w ⊩ A
    ⟦ v[ x ∷ A ] i ⟧         ρ = lookup ρ i
    ⟦ λ[ x ∷ A′ ] M ⟧        ρ = λ c u → ⟦ M ⟧ ⟨ ↑ₑ c ρ , x ≔ u ⟩
    ⟦ M ∙⟨ A , B ⟩ N ⟧       ρ = app⟨ A , B ⟩ refl≥ (⟦ M ⟧ ρ) (⟦ N ⟧ ρ) -- ⟦app⟧⟪ A , B ⟫ (⟦ d ⟧ γ) refl≤ (⟦ e ⟧ γ)
    ⟦ M ▸ γ ⟧                ρ = ⟦ M ⟧ (⟦ γ ⟧ₛ ρ)

    ⟦_⟧ₛ : ∀ {Δ Γ w} → Δ ⇛ Γ → w ⊩ₑ Δ → w ⊩ₑ Γ
    ⟦ [ γ , x ≔ M ] ⟧ₛ       ρ = ⟨ ⟦ γ ⟧ₛ ρ , x ≔ ⟦ M ⟧ ρ ⟩
    ⟦ γ₁ ∘ γ₂ ⟧ₛ             ρ = ⟦ γ₁ ⟧ₛ (⟦ γ₂ ⟧ₛ ρ)
    ⟦ π c ⟧ₛ                 ρ = ↓ₑ c ρ


-- 4.4. The inversion function

instance
  𝔪 : Model
  𝔪 = record
    { 𝒲      = 𝒞
    ; 𝒢      = _⊢ o
    ; _≥_    = _⊇_
    ; refl≥  = Lemma₃
    ; trans≥ = Lemma₄
    ; uniq≥  = Lemma₇
    }

open Model 𝔪

postulate
  gensym : 𝒞 → Name
  instance
    fresh-gensym : (Γ : 𝒞) → fresh (gensym Γ) Γ

mutual
  reify : ∀ {A Γ} → Γ ⊩ A → Γ ⊢ A
  reify {o}      {Γ} u = ground u (Lemma₃ {Γ})
  reify {A ⇒ B} {Γ} u = λ[ z ∷ A ] (reify (app⟨ A , B ⟩ Lemma₅ u (vv[ z ∷ A ] occ₁)))
    where
      z = gensym Γ

  val : ∀ {A Γ} → (∀ {Δ} → Δ ⊇ Γ → Δ ⊢ A) → Γ ⊩ A
  val {o}      f = Ground f
  val {A ⇒ B} f = Λ⟨ A , B ⟩ (λ c₁ v → val (λ c₂ → f (Lemma₄ c₂ c₁) ∙ reify (↑⟨ A ⟩ c₂ v)))

  var-val : ∀ {x A Γ} → Occur x A Γ → Γ ⊩ A
  var-val {x} {A} i = val⟨ A ⟩ (λ c → v[ x ∷ A ] Lemma₂ i c)

  syntax reify {A} u       = reify⟨ A ⟩ u
  syntax val {A} f         = val⟨ A ⟩ f
  syntax var-val {x} {A} i = vv[ x ∷ A ] i

Lemma₄₄₁ : ∀ {A Γ} {f₁ f₂ : ∀ {Δ} → Δ ⊇ Γ → Δ ⊢ A} →
           (∀ {Δ} → (c : Δ ⊇ Γ) → f₁ c ≡ f₂ c) → Eq⟨ A ⟩ (val f₁) (val f₂)
Lemma₄₄₁ {o}      h = λ c → h c
Lemma₄₄₁ {A ⇒ B} h = λ c q → {!!}

postulate
  Lemma₄₄₂ : ∀ {A Δ Γ} {f : ∀ {Δ} → Δ ⊇ Γ → Δ ⊢ A} →
             (c : Δ ⊇ Γ) → Eq⟨ A ⟩ (↑⟨ A ⟩ c (val f)) (val (λ c′ → f (Lemma₄ c′ c)))
-- Lemma₄₄₂ {o}      c = λ c′ → refl
-- Lemma₄₄₂ {A ⇒ B} c = λ c′ q → {!!}

mutual
  postulate
    Theorem₁ : ∀ {A Γ} {u v : Γ ⊩ A} → Eq⟨ A ⟩ u v → reify⟨ A ⟩ u ≡ reify⟨ A ⟩ v
  -- Theorem₁ {o}      p = p refl≥
  -- Theorem₁ {A ⇒ B} p = {!!}

  postulate
    Lemma₄₄₃ : ∀ {A Γ} → (f : ∀ {Δ} → Δ ⊇ Γ → Δ ⊢ A) → 𝒰⟨ A ⟩ (val f)
  -- Lemma₄₄₃ {o}      f = tt
  -- Lemma₄₄₃ {A ⇒ B} f = {!!} , {!!} , {!!}

valₑ : ∀ {Δ Γ} → Δ ⊇ Γ → Δ ⊩ₑ Γ
valₑ gt₁               = ⟨⟩
valₑ (gt₂ {x} {A} c i) = ⟨ valₑ c , x ≔ vv[ x ∷ A ] i ⟩

idₑ : ∀ {Γ} → Γ ⊩ₑ Γ
idₑ = valₑ refl≥

nf : ∀ {A Γ} → Γ ⊢ A → Γ ⊢ A
nf d = reify (⟦ d ⟧ idₑ)

Corollary₁ : ∀ {A Γ} → (M N : Γ ⊢ A) → Eq⟨ A ⟩ (⟦ M ⟧ idₑ) (⟦ N ⟧ idₑ) → nf M ≡ nf N
Corollary₁ M N = Theorem₁


-- 4.5. Soundness and completeness of proof trees

-- (blank)


-- 4.5. Completeness of the conversion rules for proof trees

open import Convertibility public

CV : ∀ {A Γ} → Γ ⊢ A → Γ ⊩ A → Set
CV {o}      {Γ} M u = ∀ {Δ} → (c : Δ ⊇ Γ) → M ▸ π c ≅ ground u c
CV {A ⇒ B} {Γ} M u = ∀ {Δ N v} → (c : Δ ⊇ Γ) → CV N v → CV ((M ▸ π c) ∙ N) (app⟨ A , B ⟩ c u v)

CVₑ : ∀ {Δ Γ} → Δ ⇛ Γ → Δ ⊩ₑ Γ → Set
CVₑ {Δ} {[]}            γ ⟨⟩             = ⊤
CVₑ {Δ} {[ Γ , x ∷ A ]} γ ⟨ ρ , .x ≔ u ⟩ = CVₑ (π Lemma₅ ∘ γ) ρ ∧ CV (v[ x ∷ A ] occ₁ ▸ γ) u

postulate
  Lemma₄₅₁ : ∀ {A Γ} {M N : Γ ⊢ A} {u : Γ ⊩ A} →
             M ≅ N → CV N u → CV M u

  Lemma₄₅₂ : ∀ {Δ Γ} {δ γ : Δ ⇛ Γ} {ρ : Δ ⊩ₑ Γ} →
             γ ≅ₛ δ → CVₑ δ ρ → CVₑ γ ρ

  Lemma₄₅₃ : ∀ {A Δ Γ} {M : Γ ⊢ A} {u : Γ ⊩ A} →
             (c : Δ ⊇ Γ) → CV M u → CV (M ▸ π c) (↑⟨ A ⟩ c u)

  Lemma₄₅₄ : ∀ {x A Δ Γ} {γ : Δ ⇛ Γ} {ρ : Δ ⊩ₑ Γ} {i : Occur x A Γ} →
             CVₑ γ ρ → CV (v[ x ∷ A ] i ▸ γ) (lookup ρ i)

  Lemma₄₅₅ : ∀ {Θ Δ Γ} {γ : Δ ⇛ Γ} {ρ : Δ ⊩ₑ Γ} →
             CVₑ γ ρ → (c : Θ ⊇ Δ) → CVₑ (γ ∘ π c) (↑ₑ c ρ)

  Lemma₄₅₆ : ∀ {Θ Δ Γ} {γ : Δ ⇛ Γ} {ρ : Δ ⊩ₑ Γ} →
             CVₑ γ ρ → (c : Γ ⊇ Θ) → CVₑ (π c ∘ γ) (↓ₑ c ρ)

mutual
  Lemma₈ : ∀ {A Δ Γ} {γ : Δ ⇛ Γ} {ρ : Δ ⊩ₑ Γ} →
           (M : Γ ⊢ A) → CVₑ γ ρ → CV (M ▸ γ) (⟦ M ⟧ ρ)
  Lemma₈ M χ = {!!}

  Lemma₈ₛ : ∀ {Θ Δ Γ} {δ : Θ ⇛ Δ} {ρ : Θ ⊩ₑ Δ} →
            (γ : Δ ⇛ Γ) → CVₑ δ ρ → CVₑ (γ ∘ δ) (⟦ γ ⟧ₛ ρ)
  Lemma₈ₛ γ χ = {!!}

mutual
  Lemma₉ : ∀ {A Γ} {M : Γ ⊢ A} {u : Γ ⊩ A} →
           CV M u → M ≅ reify u
  Lemma₉ h = {!!}

  Lemma₉ᵥ : ∀ {A Δ Γ} {M : Γ ⊢ A} {f : ∀ {Δ} → Δ ⊇ Γ → Δ ⊢ A} →
            (c : Δ ⊇ Γ) → M ▸ π c ≅ f c → CV M (val f)
  Lemma₉ᵥ = {!!}

valCVₑ : ∀ {Δ Γ} → (c : Δ ⊇ Γ) → CVₑ (π c) (valₑ c)
valCVₑ c = {!!}

idCVₑ : ∀ {Γ} → CVₑ (π refl≥) (idₑ {Γ})
idCVₑ = valCVₑ refl≥

postulate
  Lemma₄₅₇ : ∀ {A Γ} {M : Γ ⊢ A} {c : Γ ⊇ Γ} →
             M ▸ π c ≅ nf M

postulate
  Theorem₂ : ∀ {A Γ} → (M : Γ ⊢ A) → M ≅ nf M
-- Theorem₂ = {!!}

Theorem₃ : ∀ {A Γ} → (M N : Γ ⊢ A) → Eq⟨ A ⟩ (⟦ M ⟧ idₑ) (⟦ N ⟧ idₑ) → M ≅ N
Theorem₃ M N p = {!!}


-- 4.7. Completeness of the conversion rules for substitutions

reifyₑ : ∀ {Δ Γ} → Δ ⊩ₑ Γ → Δ ⇛ Γ
reifyₑ ⟨⟩            = π gt₁
reifyₑ ⟨ ρ , x ≔ v ⟩ = [ reifyₑ ρ , x ≔ reify v ]

nfₛ : ∀ {Δ Γ} → Δ ⇛ Γ → Δ ⇛ Γ
nfₛ γ = reifyₑ (⟦ γ ⟧ₛ idₑ)

postulate
  Theorem₂ₛ : ∀ {Δ Γ} → (γ : Δ ⇛ Γ) → γ ≅ₛ nfₛ γ


-- 4.8. Soundness of the conversion rules

postulate
  Lemma₄₈₁ : ∀ {A Δ Γ} {M : Γ ⊢ A} {ρ : Δ ⊩ₑ Γ} →
             𝒰ₑ ρ → 𝒰⟨ A ⟩ (⟦ M ⟧ ρ)

  Lemma₄₈₂ : ∀ {Δ Γ} {γ : Γ ⇛ Δ} {ρ : Δ ⊩ₑ Γ} →
             𝒰ₑ ρ → 𝒰ₑ (⟦ γ ⟧ₛ ρ)

  Lemma₄₈₃⟨_⟩ : ∀ A {Δ Γ} {M : Γ ⊢ A} {ρ₁ ρ₂ : Δ ⊩ₑ Γ} →
                Eqₑ ρ₁ ρ₂ → Eq⟨ A ⟩ (⟦ M ⟧ ρ₁) (⟦ M ⟧ ρ₂)

  Lemma₄₈₄ : ∀ {Δ Γ} {γ : Γ ⇛ Δ} {ρ₁ ρ₂ : Δ ⊩ₑ Γ} →
             Eqₑ ρ₁ ρ₂ → Eqₑ (⟦ γ ⟧ₛ ρ₁) (⟦ γ ⟧ₛ ρ₂)

  Lemma₄₈₅ : ∀ {A Θ Δ Γ} {M : Γ ⊢ A} {ρ : Δ ⊩ₑ Γ} {c : Θ ⊇ Δ} →
             Eq⟨ A ⟩ (↑⟨ A ⟩ c (⟦ M ⟧ ρ)) (⟦ M ⟧ (↑ₑ c ρ))

  Lemma₄₈₆ : ∀ {Θ Δ Γ} {γ : Γ ⇛ Δ} {ρ : Δ ⊩ₑ Γ} {c : Θ ⊇ Δ} →
             Eqₑ (↑ₑ c (⟦ γ ⟧ₛ ρ)) (⟦ γ ⟧ₛ (↑ₑ c ρ))


--     ⟦_⟧ₛ : ∀ {Δ Γ w} → Δ ⇛ Γ → w ⊩ₑ Δ → w ⊩ₑ Γ

mutual
  Theorem₄ : ∀ {A Γ w} {M N : Γ ⊢ A} → M ≅ N → (ρ : w ⊩ₑ Γ) →
             Eq⟨ A ⟩ (⟦ M ⟧ ρ) (⟦ N ⟧ ρ)
  Theorem₄ (refl≅ {A})       ρ = reflEq⟨ A ⟩
  Theorem₄ (trans≅ {A} p p′) ρ = transEq⟨ A ⟩ (Theorem₄ p ρ) (Theorem₄ p′ ρ)
  Theorem₄ (sym≅ {A} p)      ρ = symEq⟨ A ⟩ (Theorem₄ p ρ)

  Theorem₄ {A} {Γ} (cong▸ {M = M} {M′} {γ} {γ′} p q) ρ =
    proofEq⟨ A ⟩
      ⟦ M ⟧ (⟦ γ ⟧ₛ ρ)
    Eq⟨ A ⟩⟨ Lemma₄₈₃⟨ A ⟩ {M = M} (Theorem₄ₛ q ρ) ⟩
      ⟦ M ⟧ (⟦ γ′ ⟧ₛ ρ)
    Eq⟨ A ⟩⟨ Theorem₄ p (⟦ γ′ ⟧ₛ ρ) ⟩
      ⟦ M′ ⟧ (⟦ γ′ ⟧ₛ ρ)
    ∎Eq⟨ A ⟩

  Theorem₄ (congλ {x = x} {B = B} {M = M} {M′} p) ρ {v = v} = λ c q →
    proofEq⟨ B ⟩
      ⟦ M ⟧ ⟨ ↑ₑ c ρ , x ≔ v ⟩
    Eq⟨ B ⟩⟨ Theorem₄ p ⟨ ↑ₑ c ρ , x ≔ v ⟩ ⟩
      ⟦ M′ ⟧ ⟨ ↑ₑ c ρ , x ≔ v ⟩
    ∎Eq⟨ B ⟩

  Theorem₄ {B} (cong∙ {A} {M = M} {M′} {N} {N′} p p′) ρ =
    proofEq⟨ B ⟩
      ⟦ M ⟧ ρ refl⊇ (⟦ N ⟧ ρ)
    Eq⟨ B ⟩⟨ {!Theorem₄ p ρ refl⊇ ?!} ⟩
      ⟦ M ⟧ ρ refl⊇ (⟦ N′ ⟧ ρ)
    Eq⟨ B ⟩⟨ congEq⟨ A , B ⟩ refl⊇ {!!} {!!} {!!} {!!} {!!} {!!} ⟩
      ⟦ M′ ⟧ ρ refl⊇ (⟦ N′ ⟧ ρ)
    ∎Eq⟨ B ⟩
  Theorem₄ (conv≅₁ M N γ) ρ = {!!}
  Theorem₄ (conv≅₂ M c)   ρ = {!!}
  Theorem₄ (conv≅₃ M γ)   ρ = {!!}
  Theorem₄ (conv≅₄ i j c) ρ = {!!}
  Theorem₄ (conv≅₅ M c)   ρ = {!!}
  Theorem₄ (conv≅₆ M N γ) ρ = {!!}
  Theorem₄ (conv≅₇ M δ γ) ρ = {!!}

  postulate
    Theorem₄ₛ : ∀ {Δ Γ w} {γ γ′ : Γ ⇛ Δ} → γ ≅ₛ γ′ → (ρ : w ⊩ₑ Γ) →
                Eqₑ (⟦ γ ⟧ₛ ρ) (⟦ γ′ ⟧ₛ ρ)
  -- Theorem₄ₛ p ρ = {!!}


-- 4.9. Decision algorithm for conversion

Theorem₅ : ∀ {A Γ} → (M N : Γ ⊢ A) → nf M ≡ nf N → M ≅ N
Theorem₅ M N p =
  proof≅
    M
  ≅⟨ Theorem₂ M ⟩
    nf M
  ≡→≅⟨ p ⟩
    nf N
  ≅⟨ sym≅ (Theorem₂ N) ⟩
    N
  ∎≅

Theorem₆ : ∀ {A Γ} → (M N : Γ ⊢ A) → M ≅ N → nf M ≡ nf N
Theorem₆ {A} M N p = Corollary₁ M N (Theorem₄ p idₑ)
