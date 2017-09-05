{-# OPTIONS --no-positivity-check #-}

module Section5 where

open import Section4 public


-- 5. Normal form
-- ==============

mutual
  data ENF : ∀ {Γ A} → Γ ⊢ A → Set where
    enf-ƛ : ∀ {Γ A B x} {{_ : T (fresh x Γ)}} →
              (M : [ Γ , x ∷ A ] ⊢ B) → ENF M →
              ENF (ƛ x M)
    enf-a : ∀ {Γ} →
              (M : Γ ⊢ •) → ANF M →
              ENF M

  data ANF : ∀ {Γ A} → Γ ⊢ A → Set where
    anf-ν : ∀ {Γ A x} →
              (i : Γ ∋ x ∷ A) →
              ANF (ν x i)
    anf-∙ : ∀ {Γ A B} →
              (M : Γ ⊢ A ⊃ B) → ANF M → (N : Γ ⊢ A) → ENF N →
              ANF (M ∙ N)

data NF : ∀ {Γ A} → Γ ⊩ A → Set where
  nf-• : ∀ {Γ} →
           (s : Γ ⊩ •) → (∀ {Δ} → (c : Δ ⊇ Γ) → ANF (s ⟦g⟧⟨ c ⟩)) →
           NF s
  nf-⊃ : ∀ {Γ A B} →
           (s : Γ ⊩ A ⊃ B) → (∀ {Δ} → (c : Δ ⊇ Γ) (t : Δ ⊩ A) → NF t → NF (s ⟦∙⟧⟨ c ⟩ t)) →
           NF s

-- TODO: Remove
-- NF : ∀ {A Γ} → Γ ⊩ A → Set
-- NF {•}     {Γ} s = ∀ {Δ} → (c : Δ ⊇ Γ) → anf (⟦ung⟧ s c)
-- NF {A ⊃ B} {Γ} s = ∀ {Δ} → (c : Δ ⊇ Γ) (t : Δ ⊩ A) → NF t → NF (⟦app⟧ s c t)

NF⋆ : ∀ {Δ Γ} → Δ ⊩⋆ Γ → Set
NF⋆ []            = ⊤
NF⋆ [ ρ , x ≔ s ] = NF⋆ ρ × NF s

postulate
  aux₅₀₁ : ∀ {Γ Δ A} → (c : Δ ⊇ Γ) (s : Γ ⊩ A) → NF s →
             NF (↑⟨ c ⟩ s)

postulate
  aux₅₀₂ : ∀ {Γ Δ A x} → (ρ : Δ ⊩⋆ Γ) → NF⋆ ρ → (i : Γ ∋ x ∷ A) →
             NF (lookup ρ i)

postulate
  aux₅₀₃ : ∀ {Γ Δ Θ} → (c : Θ ⊇ Δ) (ρ : Δ ⊩⋆ Γ) → NF⋆ ρ →
             NF⋆ (↑⟨ c ⟩ ρ)

postulate
  aux₅₀₄ : ∀ {Γ Δ Θ} → (c : Δ ⊇ Γ) (ρ : Θ ⊩⋆ Δ) → NF⋆ ρ →
             NF⋆ (↓⟨ c ⟩ ρ)

-- Lemma 10.
mutual
  postulate
    lem₁₀ : ∀ {Γ Δ A} → (M : Γ ⊢ A) (ρ : Δ ⊩⋆ Γ) → NF⋆ ρ →
              NF (⟦ M ⟧ ρ)

  postulate
    lem₁₀⋆ : ∀ {Γ Δ Θ} → (γ : Δ ⋙ Γ) (ρ : Θ ⊩⋆ Δ) → NF⋆ ρ →
               NF⋆ (⟦ γ ⟧ₛ ρ)

-- Lemma 11.
mutual
  postulate
    lem₁₁ : ∀ {Γ A} → (s : Γ ⊩ A) → NF s →
              ENF (reify s)

  postulate
    lem₁₁⋆ : ∀ {Γ A} → (f : ∀ {Δ} → Δ ⊇ Γ → Δ ⊢ A) →
               (h : ∀ {Δ} → (c : Δ ⊇ Γ) → ANF (f c)) →
               NF (val f)

NF-ν : ∀ {x A Γ} → (i : Γ ∋ x ∷ A) → NF (val-ν i)
NF-ν {x} i = lem₁₁⋆ (λ c → ν x (↑⟨ c ⟩ i))
                    (λ c → anf-ν (↑⟨ c ⟩ i))

projNF⋆⟨_⟩ : ∀ {Γ Δ} → (c : Δ ⊇ Γ) → NF⋆ proj⟨ c ⟩⊩⋆
projNF⋆⟨ done ⟩     = tt
projNF⋆⟨ weak c i ⟩ = projNF⋆⟨ c ⟩ , NF-ν i

reflNF⋆ : ∀ {Γ} → NF⋆ (refl⊩⋆ {Γ})
reflNF⋆ = projNF⋆⟨ refl⊇ ⟩

-- Theorem 7.
thm₇ : ∀ {Γ A} → (M : Γ ⊢ A) → ENF (nf M)
thm₇ M = lem₁₁ (⟦ M ⟧ refl⊩⋆) (lem₁₀ M refl⊩⋆ reflNF⋆)

-- TODO:
-- “We can also use the results above to prove that if λ(x : A).M ≅ λ(y : A).N, then
-- M(x = z) ≅ N(y = z) where z is a fresh variable.  Hence we have that λ is one-to-one up to
-- α-conversion.”
