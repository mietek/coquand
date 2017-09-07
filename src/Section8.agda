module Section8 where

open import Section7 public


-- 8. Correctness of conversion between terms
-- ==========================================
--
-- The conversion rules for terms are sound:

-- Theorem 9.
postulate
  thm₉ : ∀ {Γ A t₀ t₁} →
           (M N : Γ ⊢ A) → t₀ 𝒟 M → t₁ 𝒟 N → Γ ⊢ t₀ ≊ t₁ ∷ A →
           M ≅ N

-- Proof: The proof is by induction on the proof of `Γ ⊢ t₀ ≊ t₁ ∷ A`.  We illustrate the proof
-- with the reflexivity case.  In this case we have that `t₀` and `t₁` are the same, hence by Corollary 3
-- we get `M ≅ N`.
--
-- To prove that the conversion rules are complete
-- is straightforward by induction on the proof of `M ≅ N`.

-- Theorem 10.
postulate
  thm₁₀ : ∀ {Γ A} →
            (M N : Γ ⊢ A) → M ≅ N →
            Γ ⊢ M ⁻ ≊ N ⁻ ∷ A
