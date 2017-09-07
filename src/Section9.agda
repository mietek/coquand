module Section9 where

open import Section8 public


-- 9. A decision algorithm for terms
-- =================================
--
-- The reduction defined above can be used for deciding if two well-typed terms are convertible
-- with each other or not: reduce the terms and check if the results are equal.  This algorithm
-- is implicit in Martin-Löf’s notes [13].
--
-- The decision algorithm is complete:

-- Theorem 11.
postulate
  thm₁₁ : ∀ {Γ A t₀ t₁} →
            Γ ⊢ t₀ ≊ t₁ ∷ A →
            Σ 𝕋 (λ t → Γ ⊢ t₀ ⇓ t ∷ A × Γ ⊢ t₁ ⇓ t ∷ A)

-- Proof:  By Lemma 14 and Lemma 12 we know that there exist proof trees `M, N` such
-- that `t₀` is equal to `M ⁻` and `t₁` is equal to `N ⁻`.  By Theorem 9 we get that `M ≅ N`.  We can
-- choose `nf M ⁻` for `t` since, by Lemma 8, `Γ ⊢ M ⁻ ⇓ nf M ⁻ ∷ A`, `Γ ⊢ N ⁻ ⇓ nf N ⁻ ∷ A`
-- and by Theorem 6 we have `nf M ≡ nf N` and hence that `nf M ⁻` and `nf N ⁻` are the
-- same.
--
-- This decision algorithm is correct, i.e.,

-- Theorem 12.
postulate
  thm₁₂ : ∀ {Γ A t} →
            (M N : Γ ⊢ A) → Γ ⊢ M ⁻ ⇓ t ∷ A → Γ ⊢ N ⁻ ⇓ t ∷ A →
            M ≅ N

-- Proof:  We have `nf M ⁻ ≡ nf N ⁻` since, by Lemma 8, `Γ ⊢ M ⁻ ⇓ nf M ⁻ ∷ A`
-- and `Γ ⊢ N ⁻ ⇓ nf N ⁻ ∷ A` and the reduction is deterministic.  By Corollary 2 we get
-- `M ≅ N`.
