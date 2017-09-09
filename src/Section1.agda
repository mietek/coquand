module Section1 where


-- 1. Introduction
-- ===============
--
-- 1.1. Outline of the formalisation
-- ---------------------------------
--
-- -   We formalize terms-in-context, `Γ ⊢ t ∷ A`, as a calculus of proof trees, `Γ ⊢ A`, for
--     implicational logic, i.e., term `t` is seen as a proof tree that derives `A` from the assumptions
--     contained in `Γ`.  A notion of equivalence of terms-in-context (including, e.g., β-reduction
--     and η-conversion) is then defined with a conversion relation `_≅_` on these proof trees.
--
-- -   We give a Kripke model with an ordered set of worlds and define when a proposition `A` is
--     true for a world `w` in the model, `w ⊩ A`.  We also define an extensional equality between
--     objects in the model.
--
-- -   We define an interpreter `⟦_⟧` that maps a proof tree in the theory to its semantics in the
--     Kripke model.  According to the Curry-Howard correspondence of programs to proofs
--     and types to propositions, the type of the interpreter expresses soundness of the theory of
--     proof trees with respect to the Kripke model.  Consequently, the interpreter can be seen
--     as a constructive soundness proof.
--
-- -   We also define an inversion function, `reify`, which returns a proof tre corresponding to
--     a given semantic object, yielding—again by the Curry-Howard isomorphism—a
--     completeness proof.
--
--     The inversion function is based on the principle of normalization by evaluation [3].
--     Obviously, for proof trees `M` and `N` with the same semantics, inversion yields the same proof
--     tree `reify ⟦ M ⟧ = reify ⟦ N ⟧`.  Consequently, we define a normalization function, `nf`, as
--     the composition of the interpreter and the inversion function.  We prove that if `M` is a proof
--     tree, then `M ≅ nf M`; together with the soundness result, this yields a decision algorithm
--     for convertibility.  We further show that `nf` returns a proof term in long η-normal form.
--
-- -   We prove that the convertibility relation on proof trees is sound and complete.  The proof
--     of soundness, i.e., convertible proof trees have the same semantics, is straightforward by
--     induction on the structure of the trees.  The completeness proof, i.e., if `⟦ M ⟧` and `⟦ N ⟧` are
--     equal, then `M` and `N` are convertible, uses the fact that `reify ⟦ M ⟧` is exactly the same as
--     `reify ⟦ N ⟧`, and since `M ≅ nf M ≡ reify ⟦ M ⟧` and vice versa for `N`, we get that `M ≅ N`.
--
-- -   We define a calculus of simply typed ƛterms, a typed convertibility relation on the terms,
--     and a deterministic reduction, `_⇓_`.  We also define an erasure function on proof trees that
--     maps a proof tree `M` into a well-typed term `M ⁻`.  For every well-typed term there is at
--     least one proof tree that erases to this term; for defining the semantics of well-typed terms
--     through that of proof trees, it suffices to show that all proof trees that erase to the same
--     well-typed term have the same semantics.
--
-- -   Because we know that convertible proof trees have the same semantics, it remains to
--     show that all proof trees that erase to a given well-typed term are convertible.  We use an
--     argument due to Streicher [19]: we first prove that if `nf M ⁻` and `nf N ⁻` are the same,
--     then `M ≅ N`.  Secondly, we prove that if a proof tree `M` erases to a well-typed term `t`,
--     then `t ⇓ nf M ⁻`.  Now, if two proof trees `M` and `N` erase to the same well-typed term
--     `t`, then `t ⇓ nf M ⁻` and `t ⇓ nf N ⁻`.  Since the reduction is deterministic we have that
--     `nf M ⁻` and `nf N ⁻` are the same, and hence `M ≅ N`.
--
-- -   We prove that the convertibility relation on proof trees is sound and complete, and give
--     a decision algorithm for checking convertibility of two well-typed terms.
--
-- (…)


open import Agda.Builtin.FromString public
  using (IsString ; fromString)

open import Data.Bool public
  using (Bool ; T ; true ; false ; not)
  renaming (_∧_ to and)

open import Data.Product public
  using (Σ ; _,_ ; _×_)

open import Data.Unit public
  using (⊤ ; tt)

import Data.String as Str
open Str
  using (String)

open import Function public
  using (_∘_ ; case_of_ ; flip ; id)

open import Relation.Binary.PropositionalEquality public
  using (_≡_ ; _≢_ ; refl ; cong ; subst ; sym ; trans)
  renaming (cong₂ to cong²)

open import Relation.Nullary public
  using (¬_ ; Dec ; yes ; no)

import Relation.Nullary.Decidable as Decidable
open Decidable using (⌊_⌋) public

open import Relation.Nullary.Negation public
  renaming (contradiction to _↯_)


module _ where
  data Name : Set where
    name : String → Name

  module _ where
    inj-name : ∀ {s s′} → name s ≡ name s′ → s ≡ s′
    inj-name refl = refl

    _≟_ : (x x′ : Name) → Dec (x ≡ x′)
    name s ≟ name s′ = Decidable.map′ (cong name) inj-name (s Str.≟ s′)

    _≠_ : Name → Name → Bool
    x ≠ x′ = not ⌊ x ≟ x′ ⌋

  instance
    str-Name : IsString Name
    str-Name = record
      { Constraint = λ s → ⊤
      ; fromString = λ s → name s
      }


module _ where
  record Raiseable
      {World : Set}
      (_⊩◌  : World → Set)
      {_⊒_   : World → World → Set} : Set₁ where
    field
      ↑⟨_⟩  : ∀ {w w′} → w′ ⊒ w → w ⊩◌ → w′ ⊩◌
  open Raiseable {{…}} public

  record Lowerable
      {World : Set}
      (◌⊩_  : World → Set)
      {_⊒_   : World → World → Set} : Set₁ where
    field
      ↓⟨_⟩  : ∀ {w w′} → w′ ⊒ w → ◌⊩ w′ → ◌⊩ w
  open Lowerable {{…}} public
