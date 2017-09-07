{-# OPTIONS --no-positivity-check #-}

module Section5 where

open import Section4 public


-- 5. Normal form
-- ==============
--
-- As we have seen above it is not necessary to know that `nf` actually gives a proof tree in
-- η-normal form for the results above.  This is however the case.  We can mutually inductively
-- define when a proof tree is in long η-normal form, `enf`, and in applicative normal form, `anf`.  (…)

mutual
  data enf : ∀ {Γ A} → Γ ⊢ A → Set where
    ƛ : ∀ {Γ A B}
          (x : Name) {{_ : T (fresh x Γ)}} → {M : [ Γ , x ∷ A ] ⊢ B} → enf M →
          enf (ƛ x M)
    α : ∀ {Γ} →
          {M : Γ ⊢ •} → anf M →
          enf M

  data anf : ∀ {Γ A} → Γ ⊢ A → Set where
    ν   : ∀ {Γ A} →
            (x : Name) (i : Γ ∋ x ∷ A) →
            anf (ν x i)
    _∙_ : ∀ {Γ A B} →
            {M : Γ ⊢ A ⊃ B} → anf M → {N : Γ ⊢ A} → enf N →
            anf (M ∙ N)

-- We prove that `nf M` is in long η-normal form.  For this we define a Kripke logical
-- predicate, `𝒩`, such that `𝒩 ⟦ M ⟧` and if `𝒩 a`, then `enf (reify a)`.

data 𝒩 : ∀ {Γ A} → Γ ⊩ A → Set where
  𝓃• : ∀ {Γ} →
         (f : Γ ⊩ •) → (∀ {Δ} → (c : Δ ⊇ Γ) → anf (f ⟦g⟧⟨ c ⟩)) →
         𝒩 f
  𝓃⊃ : ∀ {Γ A B} →
         (f : Γ ⊩ A ⊃ B) → (∀ {Δ} → (c : Δ ⊇ Γ) → {a : Δ ⊩ A} → 𝒩 a → 𝒩 (f ⟦∙⟧⟨ c ⟩ a)) →
         𝒩 f

-- For base type we intuitively define `𝒩 f` to hold if `anf f`.
--
-- If `f : Γ ⊩ A ⊃ B`, then `𝒩 f` is defined to hold if `𝒩 (f ∙ a)` holds for all `a : Γ ⊩ A`
-- such that `𝒩 a`.
--
-- We also define `𝒩⋆ ρ`, `ρ : Γ ⊩⋆ Δ`, to hold if every value, `a`, in `ρ` has the property `𝒩 a`.

data 𝒩⋆ : ∀ {Γ Δ} → Δ ⊩⋆ Γ → Set where
  𝓃⋆[] : ∀ {Δ} →
           𝒩⋆ ([] {w = Δ})
  𝓃⋆≔  : ∀ {Γ Δ A x} {{_ : T (fresh x Γ)}} →
           {ρ : Δ ⊩⋆ Γ} → 𝒩⋆ ρ → {a : Δ ⊩ A} → 𝒩 a →
           𝒩⋆ [ ρ , x ≔ a ]

-- We prove the following lemmas which are used to prove Lemma 10.

postulate
  aux₅₀₁⟨_⟩ : ∀ {Γ Δ A} →
                (c : Δ ⊇ Γ) → {a : Γ ⊩ A} → 𝒩 a →
                𝒩 (↑⟨ c ⟩ a)

postulate
  aux₅₀₂ : ∀ {Γ Δ A x} →
             {ρ : Δ ⊩⋆ Γ} → 𝒩⋆ ρ → (i : Γ ∋ x ∷ A) →
             𝒩 (lookup ρ i)

postulate
  aux₅₀₃⟨_⟩ : ∀ {Γ Δ Θ} →
                (c : Θ ⊇ Δ) → {ρ : Δ ⊩⋆ Γ} → 𝒩⋆ ρ →
                𝒩⋆ (↑⟨ c ⟩ ρ)

postulate
  aux₅₀₄⟨_⟩ : ∀ {Γ Δ Θ} →
                (c : Γ ⊇ Θ) → {ρ : Δ ⊩⋆ Γ} → 𝒩⋆ ρ →
                𝒩⋆ (↓⟨ c ⟩ ρ)

-- The lemma is proved together with a corresponding lemma for substitutions:

-- Lemma 10.
mutual
  postulate
    lem₁₀ : ∀ {Γ Δ A} →
              (M : Γ ⊢ A) → {ρ : Δ ⊩⋆ Γ} → 𝒩⋆ ρ →
              𝒩 (⟦ M ⟧ ρ)

  postulate
    lem₁₀ₛ : ∀ {Γ Δ Θ} →
               (γ : Γ ⋙ Θ) → {ρ : Δ ⊩⋆ Γ} → 𝒩⋆ ρ →
               𝒩⋆ (⟦ γ ⟧ₛ ρ)

-- The main lemma is that for all values, `a`, such that `𝒩 a`, `reify a` returns a proof tree in
-- η-normal form, which is intuitively proved together with a proof that for all proof trees in
-- applicative normal form we can find a value, `a`, such that `𝒩 a`.  (…)

-- Lemma 11.
mutual
  postulate
    lem₁₁ : ∀ {Γ A} →
              {a : Γ ⊩ A} → 𝒩 a →
              enf (reify a)

  postulate
    lem₁₁ₛ : ∀ {Γ A} →
               (f : ∀ {Δ} → Δ ⊇ Γ → Δ ⊢ A) → (h : ∀ {Δ} → (c : Δ ⊇ Γ) → anf (f c)) →
               𝒩 (val f)

-- The proofs are by induction on the types.
--
-- It is straightforward to prove that `𝒩⋆ proj⟨ c ⟩⊩⋆` and then by Lemma 11 and Lemma 10 we get
-- that `nf M` is in long η-normal form. (…)

𝒩-ν : ∀ {x A Γ} → (i : Γ ∋ x ∷ A) → 𝒩 (val-ν i)
𝒩-ν {x} i = lem₁₁ₛ (λ c → ν x (↑⟨ c ⟩ i))
                   (λ c → ν x (↑⟨ c ⟩ i))

proj⟨_⟩𝒩⋆ : ∀ {Γ Δ} → (c : Δ ⊇ Γ) → 𝒩⋆ proj⟨ c ⟩⊩⋆
proj⟨ done ⟩𝒩⋆     = 𝓃⋆[]
proj⟨ weak c i ⟩𝒩⋆ = 𝓃⋆≔ proj⟨ c ⟩𝒩⋆ (𝒩-ν i)

refl𝒩⋆ : ∀ {Γ} → 𝒩⋆ (refl⊩⋆ {Γ})
refl𝒩⋆ = proj⟨ refl⊇ ⟩𝒩⋆

-- Theorem 7.
thm₇ : ∀ {Γ A} → (M : Γ ⊢ A) → enf (nf M)
thm₇ M = lem₁₁ (lem₁₀ M refl𝒩⋆)

-- Hence a proof tree is convertible with its normal form.
--
-- We can also use the results above to prove that if `ƛ(x : A).M ≅ ƛ(y : A).N`, then
-- `M(x = z) ≅ N(y = z)` where `z` is a fresh variable.  Hence we have that `ƛ` is one-to-one up to
-- α-conversion.

-- TODO: What to do about the above paragraph?
