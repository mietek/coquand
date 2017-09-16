{-# OPTIONS --no-positivity-check #-}

module Section4b where

open import Section4a public


-- 4.4. The inversion function
-- ---------------------------
--
-- It is possible to go from the semantics back to the proof trees by an inversion function, `reify`
-- that, given a semantic object in a particular Kripke model, returns a proof tree.  The particular
-- Kripke model that we choose has contexts as possible worlds, the order on contexts as the
-- order on worlds, and `_⊢ •` as `𝒢`.  (…)

instance
  canon : Model
  canon = record
    { 𝒲      = 𝒞
    ; _⊒_    = _⊇_
    ; refl⊒ = refl⊇
    ; _◇_    = _○_
    ; uniq⊒ = uniq⊇
    ; 𝒢      = _⊢ •
    }

-- In order to define the inversion function we need to be able to choose a unique fresh
-- name given a context.  We suppose a function `gensym : 𝒞 → Name` and a proof of
-- `T (fresh (gensym Γ) Γ)` which proves that `gensym` returns a fresh variable.  Note that `gensym`
-- is a function taking a context as an argument and it hence always returns the same variable
-- for a given context.

-- TODO: Can we do better than this?
postulate
  gensym : (Γ : 𝒞) → Σ Name (λ x → T (fresh x Γ))

-- The function `reify` is quite intricate.  (…)
--
-- The function `reify` is mutually defined with `val`, which given a function from a context
-- extension to a proof tree returns a semantic object as result.
--
-- We define an abbreviation for the semantic object corresponding to a variable, `⟦ν⟧`.
--
-- The functions `reify` and `val` are both defined by induction on the type:

mutual
  reify : ∀ {A Γ} → Γ ⊩ A → Γ ⊢ A
  reify {•}     {Γ} f = f ⟦g⟧⟨ refl⊇ ⟩
  reify {A ⊃ B} {Γ} f = let x , φ = gensym Γ in
                        let instance _ = φ in
                        ƛ x (reify (f ⟦∙⟧⟨ weak⊇ ⟩ ⟦ν⟧ zero))

  val : ∀ {A Γ} → (∀ {Δ} → Δ ⊇ Γ → Δ ⊢ A) → Γ ⊩ A
  val {•}     f = ⟦𝒢⟧ f
  val {A ⊃ B} f = ⟦ƛ⟧ (λ c a → val (λ c′ → f (c ○ c′) ∙ reify (↑⟨ c′ ⟩ a)))

  ⟦ν⟧ : ∀ {x Γ A} → Γ ∋ x ∷ A → Γ ⊩ A
  ⟦ν⟧ {x} i = val (λ c → ν x (↑⟨ c ⟩ i))

-- We also have that if two semantic objects in a Kripke model are extensionally equal, then
-- the result of applying the inversion function to them is intensionally equal.  To prove this
-- we first have to show the following two lemmas:

aux₄₄₁ : ∀ {A Γ} →
           (f f′ : ∀ {Δ} → Δ ⊇ Γ → Δ ⊢ A) → (∀ {Δ} → (c : Δ ⊇ Γ) → f c ≡ f′ c) →
           Eq (val f) (val f′)
aux₄₄₁ {•}     f f′ h = eq• (λ c        → h c)
aux₄₄₁ {A ⊃ B} f f′ h = eq⊃ (λ c {a} uₐ → aux₄₄₁ (λ c′ → f (c ○ c′) ∙ reify (↑⟨ c′ ⟩ a))
                            (λ c′       → f′ (c ○ c′) ∙ reify (↑⟨ c′ ⟩ a))
                            (λ c′       → cong (_∙ reify (↑⟨ c′ ⟩ a))
                                             (h (c ○ c′))))

aux₄₄₂⟨_⟩ : ∀ {A Γ Δ} →
              (c : Δ ⊇ Γ) (f : (∀ {Δ} → Δ ⊇ Γ → Δ ⊢ A)) →
              Eq (↑⟨ c ⟩ (val f)) (val (λ c′ → f (c ○ c′)))
aux₄₄₂⟨_⟩ {•}     c f = eq• (λ c′        → cong f refl)
aux₄₄₂⟨_⟩ {A ⊃ B} c f = eq⊃ (λ c′ {a} uₐ → aux₄₄₁ (λ c″ → f ((c ○ c′) ○ c″) ∙ reify (↑⟨ c″ ⟩ a))
                            (λ c″        → f (c ○ (c′ ○ c″)) ∙ reify (↑⟨ c″ ⟩ a))
                            (λ c″        → cong (_∙ reify (↑⟨ c″ ⟩ a))
                                              (cong f
                                                (sym (assoc○ c c′ c″)))))

-- Both lemmas are proved by induction on the type and they are used in order to prove the
-- following theorem,
-- which is shown mutually with a lemma
-- which states that `val` returns a uniform semantic object.  Both the theorem and the lemma
-- are proved by induction on the type.

-- Theorem 1.
mutual
  thm₁ : ∀ {Γ A} {a a′ : Γ ⊩ A} → Eq a a′ → reify a ≡ reify a′
  thm₁ {Γ} (eq• h) = h refl⊇
  thm₁ {Γ} (eq⊃ h) = let x , φ = gensym Γ in
                     let instance _ = φ in
                     cong (ƛ x)
                       (thm₁ (h weak⊇ (⟦ν⟧𝒰 zero)))

  ⟦ν⟧𝒰 : ∀ {x Γ A} → (i : Γ ∋ x ∷ A) → 𝒰 (⟦ν⟧ i)
  ⟦ν⟧𝒰 {x} i = aux₄₄₃ (λ c → ν x (↑⟨ c ⟩ i))

  aux₄₄₃ : ∀ {A Γ} → (f : ∀ {Δ} → Δ ⊇ Γ → Δ ⊢ A) → 𝒰 (val f)
  aux₄₄₃ {•}     f = 𝓊•
  aux₄₄₃ {A ⊃ B} f =
    𝓊⊃ (λ c {a} uₐ              → aux₄₄₃ (λ c′ → f (c ○ c′) ∙ reify (↑⟨ c′ ⟩ a)))
       (λ c {a} {a′} eqₐ uₐ uₐ′ → aux₄₄₁ (λ c′ → f (c ○ c′) ∙ reify (↑⟨ c′ ⟩ a))
                                          (λ c′ → f (c ○ c′) ∙ reify (↑⟨ c′ ⟩ a′))
                                          (λ c′ → cong (f (c ○ c′) ∙_)
                                                     (thm₁ (cong↑⟨ c′ ⟩Eq eqₐ))))
       (λ c c′ c″ {a} uₐ        →
         transEq (aux₄₄₂⟨ c′ ⟩ (λ c‴ → f (c ○ c‴) ∙ reify (↑⟨ c‴ ⟩ a)))
                 (aux₄₄₁ (λ c‴ → f (c ○ (c′ ○ c‴)) ∙ reify (↑⟨ c′ ○ c‴ ⟩ a))
                         (λ c‴ → f (c″ ○ c‴) ∙ reify (↑⟨ c‴ ⟩ (↑⟨ c′ ⟩ a)))
                         (λ c‴ → cong² _∙_
                                    (cong f
                                      (trans (assoc○ c c′ c‴)
                                             (comp○ (c ○ c′) c‴ (c″ ○ c‴))))
                                    (thm₁ (symEq (aux₄₁₂ c′ c‴ (c′ ○ c‴) uₐ))))))

-- We are now ready to define the function that given a proof tree computes its normal form.
-- For this we define the identity environment `proj⟨_⟩⊩⋆` which to each variable
-- in the context `Γ` associates the corresponding value of the variable in `Δ` (`⟦ν⟧` gives the
-- value of this variable).  The normalisation function, `nf`, is defined as the composition of the
-- evaluation function and `reify`.  This function is similar to the normalisation algorithm given
-- by Berger [3]; one difference is our use of Kripke models to deal with reduction under `λ`.
-- One other difference is that, since we use explicit contexts, we can use the context to find
-- the fresh names in the `reify` function.

proj⟨_⟩⊩⋆ : ∀ {Γ Δ} → Δ ⊇ Γ → Δ ⊩⋆ Γ
proj⟨ done ⟩⊩⋆             = []
proj⟨ step {x = x} c i ⟩⊩⋆ = [ proj⟨ c ⟩⊩⋆ , x ≔ ⟦ν⟧ i ]

refl⊩⋆ : ∀ {Γ} → Γ ⊩⋆ Γ
refl⊩⋆ = proj⟨ refl⊇ ⟩⊩⋆

-- The computation of the normal form is done by computing the semantics of the proof
-- tree in the identity environment and then inverting the result:

nf : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ A
nf M = reify (⟦ M ⟧ refl⊩⋆)

-- We know by Theorem 1 that `nf` returns the same result when applied to two proof trees
-- having the same semantics:

-- Corollary 1.
cor₁ : ∀ {Γ A} → (M M′ : Γ ⊢ A) → Eq (⟦ M ⟧ refl⊩⋆) (⟦ M′ ⟧ refl⊩⋆) →
         nf M ≡ nf M′
cor₁ M M′ = thm₁


-- 4.5. Soundness and completeness of proof trees
-- ----------------------------------------------
--
-- We have in fact already shown soundness and completeness of the calculus of proof trees.
--
-- The evaluation function, `⟦_⟧`, for proof trees corresponds via the Curry-Howard isomorphism
-- to a proof of the soundness theorem of minimal logic with respect to Kripke models.
-- The function is defined by pattern matching which corresponds to a proof by case analysis
-- of the proof trees.
--
-- The inversion function `reify` is, again via the Curry-Howard isomorphism, a proof of the
-- completeness theorem of minimal logic with respect to a particular Kripke model where
-- the worlds are contexts.


-- 4.6. Completeness of the conversion rules for proof trees
-- ---------------------------------------------------------
--
-- In order to prove that the set of conversion rules is complete, i.e.,
-- `Eq (⟦ M ⟧ refl⊩⋆) (⟦ M′ ⟧ refl⊩⋆)` implies `M ≅ M′`, we must first prove Theorem 2: `M ≅ nf M`.
--
-- To prove the theorem we define a Kripke logical relation [15, 18]
-- which corresponds to Tait’s computability predicate.
--
-- A proof tree of base type is intuitively `CV`-related to a semantic object of base type if
-- they are convertible with each other.  (…)
--
-- A proof tree of function type, `A ⊃ B`, is intuitively `CV`-related to a semantic object of the
-- same type if they send `CV`-related proof trees and objects of type `A` to `CV`-related proof
-- trees and objects of type `B`.  (…)

data CV : ∀ {Γ A} → Γ ⊢ A → Γ ⊩ A → Set where
  cv• : ∀ {Γ} {M : Γ ⊢ •} {f : Γ ⊩ •} →
          (∀ {Δ} → (c : Δ ⊇ Γ) → M ▶ π⟨ c ⟩ ≅ f ⟦g⟧⟨ c ⟩) →
          CV M f
  cv⊃ : ∀ {Γ A B} {M : Γ ⊢ A ⊃ B} {f : Γ ⊩ A ⊃ B} →
          (∀ {Δ N a} → (c : Δ ⊇ Γ) → CV N a → CV ((M ▶ π⟨ c ⟩) ∙ N) (f ⟦∙⟧⟨ c ⟩ a)) →
          CV M f

-- The idea of this predicate is that we can show that if `CV M a` then `M ≅ reify a`, hence
-- if we show that `CV M (⟦ M ⟧ refl⊩⋆)`, we have a proof of Theorem 2.
--
-- Correspondingly for the environment we define:  (…)

data CV⋆ : ∀ {Γ Δ} → Δ ⋙ Γ → Δ ⊩⋆ Γ → Set where
  cv⋆[] : ∀ {Γ} →
            {γ : Γ ⋙ []} →
            CV⋆ γ []
  cv⋆≔  : ∀ {Γ Δ A x} {{_ : T (fresh x Γ)}}
            {γ : Δ ⋙ [ Γ , x ∷ A ]} {c : [ Γ , x ∷ A ] ⊇ Γ} {ρ : Δ ⊩⋆ Γ} {a : Δ ⊩ A} →
            CV⋆ (π⟨ c ⟩ ● γ) ρ → CV (ν x zero ▶ γ) a →
            CV⋆ γ [ ρ , x ≔ a ]

-- In order to prove Lemma 8 below we need to prove the following properties about `CV`:

cong≅CV : ∀ {Γ A} {M M′ : Γ ⊢ A} {a : Γ ⊩ A} →
            M ≅ M′ → CV M′ a →
            CV M a
cong≅CV p (cv• h) = cv• (λ c     → trans≅ (cong▶≅ p refl≅ₛ)
                                           (h c))
cong≅CV p (cv⊃ h) = cv⊃ (λ c cvₐ → cong≅CV (cong∙≅ (cong▶≅ p refl≅ₛ) refl≅)
                                            (h c cvₐ))

cong≅ₛCV⋆ : ∀ {Γ Δ} {γ γ′ : Δ ⋙ Γ} {ρ : Δ ⊩⋆ Γ} →
              γ ≅ₛ γ′ → CV⋆ γ′ ρ →
              CV⋆ γ ρ
cong≅ₛCV⋆ p cv⋆[]         = cv⋆[]
cong≅ₛCV⋆ p (cv⋆≔ cv⋆ cv) = cv⋆≔ (cong≅ₛCV⋆ (cong●≅ₛ refl≅ₛ p) cv⋆)
                                 (cong≅CV (cong▶≅ refl≅ p) cv)

cong↑⟨_⟩CV : ∀ {Γ Δ A} {M : Γ ⊢ A} {a : Γ ⊩ A} →
               (c : Δ ⊇ Γ) → CV M a →
               CV (M ▶ π⟨ c ⟩) (↑⟨ c ⟩ a)
cong↑⟨ c ⟩CV (cv• h) = cv• (λ c′     → trans≅ (trans≅ (conv₇≅ _ _ _)
                                                       (cong▶≅ refl≅ (conv₄≅ₛ _ _ _)))
                                               (h (c ○ c′)))
cong↑⟨ c ⟩CV (cv⊃ h) = cv⊃ (λ c′ cvₐ → cong≅CV (cong∙≅ (trans≅ (conv₇≅ _ _ _)
                                                                (cong▶≅ refl≅ (conv₄≅ₛ _ _ _)))
                                                        refl≅)
                                                (h (c ○ c′) cvₐ))

conglookupCV : ∀ {Γ Δ A x} {γ : Δ ⋙ Γ} {ρ : Δ ⊩⋆ Γ} →
                 CV⋆ γ ρ → (i : Γ ∋ x ∷ A) →
                 CV (ν x i ▶ γ) (lookup ρ i)
conglookupCV cv⋆[]         ()
conglookupCV (cv⋆≔ cv⋆ cv) zero    = cv
conglookupCV (cv⋆≔ cv⋆ cv) (suc i) = cong≅CV (trans≅ (cong▶≅ (sym≅ (conv₄≅ _ _ _)) refl≅ₛ)
                                                     (conv₇≅ _ _ _))
                                             (conglookupCV cv⋆ i)

cong↑⟨_⟩CV⋆ : ∀ {Γ Δ Θ} {γ : Δ ⋙ Γ} {ρ : Δ ⊩⋆ Γ} →
                (c : Θ ⊇ Δ) → CV⋆ γ ρ →
                CV⋆ (γ ● π⟨ c ⟩) (↑⟨ c ⟩ ρ)
cong↑⟨ c ⟩CV⋆ cv⋆[]         = cv⋆[]
cong↑⟨ c ⟩CV⋆ (cv⋆≔ cv⋆ cv) = cv⋆≔ (cong≅ₛCV⋆ (sym≅ₛ (conv₁≅ₛ _ _ _)) (cong↑⟨ c ⟩CV⋆ cv⋆))
                                   (cong≅CV (sym≅ (conv₇≅ _ _ _)) (cong↑⟨ c ⟩CV cv))

cong↓⟨_⟩CV⋆ : ∀ {Γ Δ Θ} {γ : Δ ⋙ Γ} {ρ : Δ ⊩⋆ Γ} →
                (c : Γ ⊇ Θ) → CV⋆ γ ρ →
                CV⋆ (π⟨ c ⟩ ● γ) (↓⟨ c ⟩ ρ)
cong↓⟨ done ⟩CV⋆     cv⋆ = cv⋆[]
cong↓⟨ step c i ⟩CV⋆ cv⋆ = cv⋆≔ {c = weak⊇}
                                (cong≅ₛCV⋆ (trans≅ₛ (sym≅ₛ (conv₁≅ₛ _ _ _))
                                                    (cong●≅ₛ (conv₄≅ₛ _ _ _) refl≅ₛ))
                                           (cong↓⟨ c ⟩CV⋆ cv⋆))
                                (cong≅CV (trans≅ (sym≅ (conv₇≅ _ _ _))
                                                 (cong▶≅ (conv₄≅ _ _ _) refl≅ₛ))
                                         (conglookupCV cv⋆ i))

-- Now we are ready to prove that if `γ` and `ρ` are `CV`-related, then `M ▶ γ` and `⟦ M ⟧ ρ` are
-- `CV`-related.  This lemma corresponds to Tait’s lemma saying that each term is computable
-- under substitution.  We prove the lemma
-- mutually with a corresponding lemma for substitutions.

-- Lemma 8.
mutual
  CV⟦_⟧ : ∀ {Γ Δ A} {γ : Δ ⋙ Γ} {ρ : Δ ⊩⋆ Γ} →
            (M : Γ ⊢ A) → CV⋆ γ ρ →
            CV (M ▶ γ) (⟦ M ⟧ ρ)
  CV⟦ ν x i ⟧ cv⋆ = conglookupCV cv⋆ i
  CV⟦ ƛ x M ⟧ cv⋆ = cv⊃ (λ c cvₐ → cong≅CV (trans≅ (cong∙≅ (conv₇≅ _ _ _) refl≅)
                                                    (conv₁≅ _ _ _))
                                            (CV⟦ M ⟧ (cv⋆≔ {c = weak⊇}
                                                           (cong≅ₛCV⋆ (conv₃≅ₛ _ _ _)
                                                                      (cong↑⟨ c ⟩CV⋆ cv⋆))
                                                           (cong≅CV (conv₃≅ _ _) cvₐ))))
  CV⟦ M ∙ N ⟧ cv⋆ with CV⟦ M ⟧ cv⋆
  CV⟦ M ∙ N ⟧ cv⋆ | (cv⊃ h) = cong≅CV (trans≅ (conv₆≅ _ _ _)
                                              (cong∙≅ (sym≅ (conv₅≅ _ _)) refl≅))
                                      (h refl⊇ (CV⟦ N ⟧ cv⋆))
  CV⟦ M ▶ γ ⟧ cv⋆ = cong≅CV (conv₇≅ _ _ _)
                            (CV⟦ M ⟧ (CV⋆⟦ γ ⟧ₛ cv⋆))

  CV⋆⟦_⟧ₛ : ∀ {Γ Δ Θ} {δ : Θ ⋙ Δ} {ρ : Θ ⊩⋆ Δ} →
              (γ : Δ ⋙ Γ) → CV⋆ δ ρ →
              CV⋆ (γ ● δ) (⟦ γ ⟧ₛ ρ)
  CV⋆⟦ π⟨ c ⟩ ⟧ₛ        cv⋆ = cong↓⟨ c ⟩CV⋆ cv⋆
  CV⋆⟦ γ ● γ′ ⟧ₛ        cv⋆ = cong≅ₛCV⋆ (conv₁≅ₛ _ _ _)
                                        (CV⋆⟦ γ ⟧ₛ (CV⋆⟦ γ′ ⟧ₛ cv⋆))
  CV⋆⟦ [ γ , x ≔ M ] ⟧ₛ cv⋆ = cv⋆≔ {c = weak⊇}
                                   (cong≅ₛCV⋆ (trans≅ₛ (sym≅ₛ (conv₁≅ₛ _ _ _))
                                                       (cong●≅ₛ (conv₃≅ₛ _ _ _) refl≅ₛ))
                                              (CV⋆⟦ γ ⟧ₛ cv⋆))
                                   (cong≅CV (trans≅ (sym≅ (conv₇≅ _ _ _))
                                                    (cong▶≅ (conv₃≅ _ _) refl≅ₛ))
                                            (CV⟦ M ⟧ cv⋆))

-- Both lemmas are proved by induction on the proof trees using the lemmas above.
--
-- Lemma 9 is shown mutually with a corresponding lemma for `val`:

-- Lemma 9.
mutual
  lem₉ : ∀ {Γ A} {M : Γ ⊢ A} {a : Γ ⊩ A} →
           CV M a →
           M ≅ reify a
  lem₉ (cv• h) = trans≅ (sym≅ (conv₅≅ _ _))
                        (h refl⊇)
  lem₉ (cv⊃ h) = trans≅ (conv₂≅ _ _)
                        (congƛ≅ (lem₉ (h weak⊇ (aux₄₆₈ (λ c → conv₄≅ _ _ _)))))

  aux₄₆₈ : ∀ {A Γ} {M : Γ ⊢ A} {f : ∀ {Δ} → Δ ⊇ Γ → Δ ⊢ A} →
             (∀ {Δ} → (c : Δ ⊇ Γ) → M ▶ π⟨ c ⟩ ≅ f c) →
             CV M (val f)
  aux₄₆₈ {•}                 h = cv• (λ c → h c)
  aux₄₆₈ {A ⊃ B} {M = M} {f} h = cv⊃ (λ {_} {N} {a} c cvₐ →
                                       aux₄₆₈ (λ {Δ′} c′ →
                                         begin
                                           ((M ▶ π⟨ c ⟩) ∙ N) ▶ π⟨ c′ ⟩
                                         ≅⟨ conv₆≅ _ _ _ ⟩
                                           ((M ▶ π⟨ c ⟩) ▶ π⟨ c′ ⟩) ∙ (N ▶ π⟨ c′ ⟩)
                                         ≅⟨ cong∙≅ (conv₇≅ _ _ _) refl≅ ⟩
                                           (M ▶ (π⟨ c ⟩ ● π⟨ c′ ⟩)) ∙ (N ▶ π⟨ c′ ⟩)
                                         ≅⟨ cong∙≅ (cong▶≅ refl≅ (conv₄≅ₛ _ _ _)) refl≅ ⟩
                                           (M ▶ π⟨ c ○ c′ ⟩) ∙ (N ▶ π⟨ c′ ⟩)
                                         ≅⟨ cong∙≅ (h (c ○ c′)) refl≅ ⟩
                                           f (c ○ c′) ∙ (N ▶ π⟨ c′ ⟩)
                                         ≅⟨ cong∙≅ refl≅ (lem₉ (cong↑⟨ c′ ⟩CV cvₐ)) ⟩
                                           f (c ○ c′) ∙ reify (↑⟨ c′ ⟩ a)
                                         ∎))
                                         where
                                           open ≅-Reasoning

-- In order to prove Theorem 2 we also prove that `CV⋆ π⟨ c ⟩ proj⟨ c ⟩⊩⋆`; then by this, Lemma 8
-- and Lemma 9 we get that `M ▶ π⟨ c ⟩ ≅ nf M`, where `c : Γ ⊇ Γ`.  Using the conversion rule
-- `M ≅ M ▶ π⟨ c ⟩` for `c : Γ ⊇ Γ` we get by transitivity of conversion of `_≅_` that `M ≅ nf M`.

proj⟨_⟩CV⋆ : ∀ {Γ Δ} →
               (c : Δ ⊇ Γ) →
               CV⋆ π⟨ c ⟩ proj⟨ c ⟩⊩⋆
proj⟨ done ⟩CV⋆             = cv⋆[]
proj⟨ step {x = x} c i ⟩CV⋆ = cv⋆≔ {c = weak⊇}
                                   (cong≅ₛCV⋆ (conv₄≅ₛ _ _ _) (proj⟨ c ⟩CV⋆))
                                   (aux₄₆₈ (λ c′ →
                                     begin
                                       (ν x zero ▶ π⟨ step c i ⟩) ▶ π⟨ c′ ⟩
                                     ≅⟨ cong▶≅ (conv₄≅ _ _ _) refl≅ₛ ⟩
                                       ν x i ▶ π⟨ c′ ⟩
                                     ≅⟨ conv₄≅ _ _ _ ⟩
                                       ν x (↑⟨ c′ ⟩ i)
                                     ∎))
                                     where
                                       open ≅-Reasoning

reflCV⋆ : ∀ {Γ} → CV⋆ π⟨ refl⊇ ⟩ (refl⊩⋆ {Γ})
reflCV⋆ = proj⟨ refl⊇ ⟩CV⋆

aux₄₆₉⟨_⟩ : ∀ {Γ A} →
              (c : Γ ⊇ Γ) (M : Γ ⊢ A) →
              M ▶ π⟨ c ⟩ ≅ nf M
aux₄₆₉⟨ c ⟩ M rewrite uniq⊇ refl⊇ c
              = lem₉ (CV⟦ M ⟧ proj⟨ c ⟩CV⋆)

-- Theorem 2.
thm₂ : ∀ {Γ A} → (M : Γ ⊢ A) →
         M ≅ nf M
thm₂ M = trans≅ (sym≅ (conv₅≅ _ _))
                (aux₄₆₉⟨ refl⊇ ⟩ M)

-- It is now easy to prove the completeness theorem:

-- Theorem 3.
thm₃ : ∀ {Γ A} → (M M′ : Γ ⊢ A) → Eq (⟦ M ⟧ refl⊩⋆) (⟦ M′ ⟧ refl⊩⋆) →
         M ≅ M′
thm₃ M M′ eq = begin
                 M
               ≅⟨ thm₂ M ⟩
                 nf M
               ≡⟨ cor₁ M M′ eq ⟩
                 nf M′
               ≅⟨ sym≅ (thm₂ M′) ⟩
                 M′
               ∎
               where
                 open ≅-Reasoning


-- 4.7. Completeness of the conversion rules for substitutions
-- -----------------------------------------------------------
--
-- The proof of completeness above does not imply that the set of conversion rules for substitutions
-- is complete.  In order to prove the completeness of conversion rules for the substitutions
-- we define an inversion function for semantic environments:  (…)

reify⋆ : ∀ {Γ Δ} → Δ ⊩⋆ Γ → Δ ⋙ Γ
reify⋆ []            = π⟨ done ⟩
reify⋆ [ ρ , x ≔ a ] = [ reify⋆ ρ , x ≔ reify a ]

-- The normalisation function on substitutions is defined as the inversion of the semantics
-- of the substitution in the identity environment.

nf⋆ : ∀ {Δ Γ} → Δ ⋙ Γ → Δ ⋙ Γ
nf⋆ γ = reify⋆ (⟦ γ ⟧ₛ refl⊩⋆)

-- The completeness result for substitutions follows in the same way as for proof trees, i.e.,
-- we must prove that `γ ≅ₛ nf⋆ γ`.

thm₁ₛ : ∀ {Γ Δ} {ρ ρ′ : Δ ⊩⋆ Γ} → Eq⋆ ρ ρ′ → reify⋆ ρ ≡ reify⋆ ρ′
thm₁ₛ eq⋆[]         = refl
thm₁ₛ (eq⋆≔ eq⋆ eq) = cong² (λ γ M → [ γ , _ ≔ M ]) (thm₁ₛ eq⋆) (thm₁ eq)

cor₁ₛ : ∀ {Γ Δ} → (γ γ′ : Δ ⋙ Γ) → Eq⋆ (⟦ γ ⟧ₛ refl⊩⋆) (⟦ γ′ ⟧ₛ refl⊩⋆) →
          nf⋆ γ ≡ nf⋆ γ′
cor₁ₛ γ γ′ = thm₁ₛ

lem₉ₛ : ∀ {Γ Δ} {γ : Δ ⋙ Γ} {ρ : Δ ⊩⋆ Γ} →
          CV⋆ γ ρ →
          γ ≅ₛ reify⋆ ρ
lem₉ₛ cv⋆[]         = conv₆≅ₛ _ _
lem₉ₛ (cv⋆≔ cv⋆ cv) = trans≅ₛ (conv₇≅ₛ _ _ _)
                              (cong≔≅ₛ (lem₉ₛ cv⋆) (lem₉ cv))

aux₄₆₉ₛ⟨_⟩ : ∀ {Γ Δ} →
               (c : Δ ⊇ Δ) (γ : Δ ⋙ Γ) →
               γ ● π⟨ c ⟩ ≅ₛ nf⋆ γ
aux₄₆₉ₛ⟨ c ⟩ γ rewrite uniq⊇ refl⊇ c
               = lem₉ₛ (CV⋆⟦ γ ⟧ₛ proj⟨ c ⟩CV⋆)

thm₂ₛ : ∀ {Γ Δ} → (γ : Δ ⋙ Γ) →
          γ ≅ₛ nf⋆ γ
thm₂ₛ γ = trans≅ₛ (sym≅ₛ (conv₅≅ₛ _ _))
                  (aux₄₆₉ₛ⟨ refl⊇ ⟩ γ)

thm₃ₛ : ∀ {Γ Δ} → (γ γ′ : Δ ⋙ Γ) → Eq⋆ (⟦ γ ⟧ₛ refl⊩⋆) (⟦ γ′ ⟧ₛ refl⊩⋆) →
          γ ≅ₛ γ′
thm₃ₛ γ γ′ eq⋆ = begin
                   γ
                 ≅ₛ⟨ thm₂ₛ γ ⟩
                   nf⋆ γ
                 ≡⟨ cor₁ₛ γ γ′ eq⋆ ⟩
                   nf⋆ γ′
                 ≅ₛ⟨ sym≅ₛ (thm₂ₛ γ′) ⟩
                   γ′
                 ∎
                 where
                   open ≅ₛ-Reasoning


-- 4.8. Soundness of the conversion rules
-- --------------------------------------
--
-- In order to prove the soundness of the conversion rules we first have to show:

-- NOTE: Added missing uniformity assumptions.
mutual
  𝒰⟦_⟧ : ∀ {A Γ Δ} {ρ : Δ ⊩⋆ Γ} →
           (M : Γ ⊢ A) → 𝒰⋆ ρ →
           𝒰 (⟦ M ⟧ ρ)
  𝒰⟦ ν x i ⟧ u⋆ = conglookup𝒰 u⋆ i
  𝒰⟦ ƛ x M ⟧ u⋆ = 𝓊⊃ (λ c uₐ         → 𝒰⟦ M ⟧ (𝓊⋆≔ (cong↑⟨ c ⟩𝒰⋆ u⋆) uₐ))
                     (λ c eqₐ uₐ uₐ′ → Eq⟦ M ⟧ (eq⋆≔ (cong↑⟨ c ⟩Eq⋆ (reflEq⋆ u⋆)) eqₐ)
                                                (𝓊⋆≔ (cong↑⟨ c ⟩𝒰⋆ u⋆) uₐ)
                                                (𝓊⋆≔ (cong↑⟨ c ⟩𝒰⋆ u⋆) uₐ′))
                     (λ c c′ c″ uₐ   → transEq (↑⟨ c′ ⟩Eq⟦ M ⟧ (𝓊⋆≔ (cong↑⟨ c ⟩𝒰⋆ u⋆) uₐ))
                                                (Eq⟦ M ⟧ (eq⋆≔ (aux₄₂₇ c c′ c″ u⋆)
                                                               (reflEq (cong↑⟨ c′ ⟩𝒰 uₐ)))
                                                         (𝓊⋆≔ (cong↑⟨ c′ ⟩𝒰⋆ (cong↑⟨ c ⟩𝒰⋆ u⋆))
                                                              (cong↑⟨ c′ ⟩𝒰 uₐ))
                                                         (𝓊⋆≔ (cong↑⟨ c″ ⟩𝒰⋆ u⋆)
                                                              (cong↑⟨ c′ ⟩𝒰 uₐ))))
  𝒰⟦ M ∙ N ⟧ u⋆ with 𝒰⟦ M ⟧ u⋆
  𝒰⟦ M ∙ N ⟧ u⋆ | (𝓊⊃ h₀ h₁ h₂) = h₀ refl⊇ (𝒰⟦ N ⟧ u⋆)
  𝒰⟦ M ▶ γ ⟧ u⋆ = 𝒰⟦ M ⟧ (𝒰⋆⟦ γ ⟧ₛ u⋆)

  𝒰⋆⟦_⟧ₛ : ∀ {Γ Δ Θ} {ρ : Θ ⊩⋆ Δ} →
             (γ : Δ ⋙ Γ) → 𝒰⋆ ρ →
             𝒰⋆ (⟦ γ ⟧ₛ ρ)
  𝒰⋆⟦ π⟨ c ⟩ ⟧ₛ        u⋆ = cong↓⟨ c ⟩𝒰⋆ u⋆
  𝒰⋆⟦ γ ● γ′ ⟧ₛ        u⋆ = 𝒰⋆⟦ γ ⟧ₛ (𝒰⋆⟦ γ′ ⟧ₛ u⋆)
  𝒰⋆⟦ [ γ , x ≔ M ] ⟧ₛ u⋆ = 𝓊⋆≔ (𝒰⋆⟦ γ ⟧ₛ u⋆) (𝒰⟦ M ⟧ u⋆)

  Eq⟦_⟧ : ∀ {Γ Δ A} {ρ ρ′ : Δ ⊩⋆ Γ} →
            (M : Γ ⊢ A) → Eq⋆ ρ ρ′ → 𝒰⋆ ρ → 𝒰⋆ ρ′ →
            Eq (⟦ M ⟧ ρ) (⟦ M ⟧ ρ′)
  Eq⟦ ν x i ⟧ eq⋆ u⋆ u⋆′ = conglookupEq eq⋆ i
  Eq⟦ ƛ x M ⟧ eq⋆ u⋆ u⋆′ = eq⊃ (λ c uₐ → Eq⟦ M ⟧ (eq⋆≔ (cong↑⟨ c ⟩Eq⋆ eq⋆) (reflEq uₐ))
                                                  (𝓊⋆≔ (cong↑⟨ c ⟩𝒰⋆ u⋆) uₐ)
                                                  (𝓊⋆≔ (cong↑⟨ c ⟩𝒰⋆ u⋆′) uₐ))
  Eq⟦ M ∙ N ⟧ eq⋆ u⋆ u⋆′ = cong⟦∙⟧⟨ refl⊇ ⟩Eq (Eq⟦ M ⟧ eq⋆ u⋆ u⋆′) (𝒰⟦ M ⟧ u⋆) (𝒰⟦ M ⟧ u⋆′)
                                              (Eq⟦ N ⟧ eq⋆ u⋆ u⋆′) (𝒰⟦ N ⟧ u⋆) (𝒰⟦ N ⟧ u⋆′)
  Eq⟦ M ▶ γ ⟧ eq⋆ u⋆ u⋆′ = Eq⟦ M ⟧ (Eq⋆⟦ γ ⟧ₛ eq⋆ u⋆ u⋆′) (𝒰⋆⟦ γ ⟧ₛ u⋆) (𝒰⋆⟦ γ ⟧ₛ u⋆′)

  Eq⋆⟦_⟧ₛ : ∀ {Γ Δ Θ} {ρ ρ′ : Θ ⊩⋆ Δ} →
              (γ : Δ ⋙ Γ) → Eq⋆ ρ ρ′ → 𝒰⋆ ρ → 𝒰⋆ ρ′ →
              Eq⋆ (⟦ γ ⟧ₛ ρ) (⟦ γ ⟧ₛ ρ′)
  Eq⋆⟦ π⟨ c ⟩ ⟧ₛ        eq⋆ u⋆ u⋆′ = cong↓⟨ c ⟩Eq⋆ eq⋆
  Eq⋆⟦ γ ● γ′ ⟧ₛ        eq⋆ u⋆ u⋆′ = Eq⋆⟦ γ ⟧ₛ (Eq⋆⟦ γ′ ⟧ₛ eq⋆ u⋆ u⋆′) (𝒰⋆⟦ γ′ ⟧ₛ u⋆) (𝒰⋆⟦ γ′ ⟧ₛ u⋆′)
  Eq⋆⟦ [ γ , x ≔ M ] ⟧ₛ eq⋆ u⋆ u⋆′ = eq⋆≔ (Eq⋆⟦ γ ⟧ₛ eq⋆ u⋆ u⋆′)
                                          (Eq⟦ M ⟧ eq⋆ u⋆ u⋆′)

  ↑⟨_⟩Eq⟦_⟧ : ∀ {Γ Δ Θ A} {ρ : Δ ⊩⋆ Γ} →
                (c : Θ ⊇ Δ) (M : Γ ⊢ A) → 𝒰⋆ ρ →
                Eq (↑⟨ c ⟩ (⟦ M ⟧ ρ)) (⟦ M ⟧ (↑⟨ c ⟩ ρ))
  ↑⟨ c ⟩Eq⟦ ν x i ⟧ u⋆ = conglookup↑⟨ c ⟩Eq u⋆ i
  ↑⟨ c ⟩Eq⟦ ƛ x M ⟧ u⋆ = eq⊃ (λ c′ uₐ → Eq⟦ M ⟧ (eq⋆≔ (symEq⋆ (aux₄₂₇ c c′ (c ○ c′) u⋆)) (reflEq uₐ))
                                                 (𝓊⋆≔ (cong↑⟨ c ○ c′ ⟩𝒰⋆ u⋆) uₐ)
                                                 (𝓊⋆≔ (cong↑⟨ c′ ⟩𝒰⋆ (cong↑⟨ c ⟩𝒰⋆ u⋆)) uₐ))
  ↑⟨ c ⟩Eq⟦ M ∙ N ⟧ u⋆ with 𝒰⟦ M ⟧ u⋆
  ↑⟨ c ⟩Eq⟦ M ∙ N ⟧ u⋆ | (𝓊⊃ h₀ h₁ h₂) = transEq (h₂ refl⊇ c c (𝒰⟦ N ⟧ u⋆))
                                                 (transEq (aux₄₁₃ c refl⊇ (𝒰⟦ M ⟧ u⋆) (cong↑⟨ c ⟩𝒰 (𝒰⟦ N ⟧ u⋆)))
                                                          (cong⟦∙⟧⟨ refl⊇ ⟩Eq (↑⟨ c ⟩Eq⟦ M ⟧ u⋆)
                                                                              (cong↑⟨ c ⟩𝒰 (𝒰⟦ M ⟧ u⋆))
                                                                              (𝒰⟦ M ⟧ (cong↑⟨ c ⟩𝒰⋆ u⋆))
                                                                              (↑⟨ c ⟩Eq⟦ N ⟧ u⋆)
                                                                              (cong↑⟨ c ⟩𝒰 (𝒰⟦ N ⟧ u⋆))
                                                                              (𝒰⟦ N ⟧ (cong↑⟨ c ⟩𝒰⋆ u⋆))))
  ↑⟨ c ⟩Eq⟦ M ▶ γ ⟧ u⋆ = transEq (↑⟨ c ⟩Eq⟦ M ⟧ (𝒰⋆⟦ γ ⟧ₛ u⋆))
                                 (Eq⟦ M ⟧ (↑⟨ c ⟩Eq⋆⟦ γ ⟧ₛ u⋆)
                                          (cong↑⟨ c ⟩𝒰⋆ (𝒰⋆⟦ γ ⟧ₛ u⋆))
                                          (𝒰⋆⟦ γ ⟧ₛ (cong↑⟨ c ⟩𝒰⋆ u⋆)))

  ↑⟨_⟩Eq⋆⟦_⟧ₛ : ∀ {Γ Δ Θ Ω} {ρ : Θ ⊩⋆ Δ} →
                  (c : Ω ⊇ Θ) (γ : Δ ⋙ Γ) → 𝒰⋆ ρ →
                  Eq⋆ (↑⟨ c ⟩ (⟦ γ ⟧ₛ ρ)) (⟦ γ ⟧ₛ (↑⟨ c ⟩ ρ))
  ↑⟨ c ⟩Eq⋆⟦ π⟨ c′ ⟩ ⟧ₛ       u⋆ = aux₄₂₈ c′ c u⋆
  ↑⟨ c ⟩Eq⋆⟦ γ ● γ′ ⟧ₛ        u⋆ = transEq⋆ (↑⟨ c ⟩Eq⋆⟦ γ ⟧ₛ (𝒰⋆⟦ γ′ ⟧ₛ u⋆))
                                            (Eq⋆⟦ γ ⟧ₛ (↑⟨ c ⟩Eq⋆⟦ γ′ ⟧ₛ u⋆)
                                                      (cong↑⟨ c ⟩𝒰⋆ (𝒰⋆⟦ γ′ ⟧ₛ u⋆))
                                                      (𝒰⋆⟦ γ′ ⟧ₛ (cong↑⟨ c ⟩𝒰⋆ u⋆)))
  ↑⟨ c ⟩Eq⋆⟦ [ γ , x ≔ M ] ⟧ₛ u⋆ = eq⋆≔ (↑⟨ c ⟩Eq⋆⟦ γ ⟧ₛ u⋆) (↑⟨ c ⟩Eq⟦ M ⟧ u⋆)


-- NOTE: Added missing lemmas.
module _ where
  aux₄₈₁⟨_⟩ : ∀ {Γ Δ A x} {{_ : T (fresh x Γ)}} {ρ : Δ ⊩⋆ Γ} {a : Δ ⊩ A} →
                (c : [ Γ , x ∷ A ] ⊇ Γ) → 𝒰⋆ ρ →
                Eq⋆ (↓⟨ c ⟩ [ ρ , x ≔ a ]) ρ
  aux₄₈₁⟨ c ⟩ u⋆ = transEq⋆ (aux₄₂₃ refl⊇ c u⋆) (aux₄₂₄⟨ refl⊇ ⟩ u⋆)

  aux₄₈₂⟨_⟩ : ∀ {Γ Δ} {ρ : Δ ⊩⋆ Γ} →
                (c : Γ ⊇ []) → 𝒰⋆ ρ →
                ↓⟨ c ⟩ ρ ≡ []
  aux₄₈₂⟨ done ⟩ u⋆ = refl

  aux₄₈₃ : ∀ {Γ Δ} {ρ : Δ ⊩⋆ Γ} →
             (γ : Γ ⋙ []) → 𝒰⋆ ρ →
             Eq⋆ (⟦ γ ⟧ₛ ρ) []
  aux₄₈₃ π⟨ c ⟩   u⋆ rewrite aux₄₈₂⟨ c ⟩ u⋆ = reflEq⋆ 𝓊⋆[]
  aux₄₈₃ (γ ● γ′) u⋆ = aux₄₈₃ γ (𝒰⋆⟦ γ′ ⟧ₛ u⋆)

  aux₄₈₄ : ∀ {Γ Δ A x} {{_ : T (fresh x Γ)}} {ρ : Δ ⊩⋆ Γ} {a : Δ ⊩ A} →
             (i : [ Γ , x ∷ A ] ∋ x ∷ A) → 𝒰 a →
             Eq (lookup [ ρ , x ≔ a ] i) a
  aux₄₈₄ i uₐ rewrite uniq∋ i zero = reflEq uₐ

  conv₆Eq⋆⟨_⟩ : ∀ {Γ Δ} {ρ : Δ ⊩⋆ Γ} →
                  (c : Γ ⊇ []) (γ : Γ ⋙ []) → 𝒰⋆ ρ →
                  Eq⋆ (⟦ γ ⟧ₛ ρ) (↓⟨ c ⟩⊩⋆ ρ)
  conv₆Eq⋆⟨ c ⟩ γ u⋆ rewrite aux₄₈₂⟨ c ⟩ u⋆ = aux₄₈₃ γ u⋆

  conv₇Eq⋆⟨_⟩ : ∀ {Γ Δ Θ A x} {{_ : T (fresh x Γ)}} {ρ : Θ ⊩⋆ Δ} →
                  (c : [ Γ , x ∷ A ] ⊇ Γ) (γ : Δ ⋙ [ Γ , x ∷ A ]) (i : [ Γ , x ∷ A ] ∋ x ∷ A) → 𝒰⋆ ρ →
                  Eq⋆ (⟦ γ ⟧ₛ ρ) [ ↓⟨ c ⟩ (⟦ γ ⟧ₛ ρ) , x ≔ lookup (⟦ γ ⟧ₛ ρ) i ]
  conv₇Eq⋆⟨_⟩ {x = x} {ρ = ρ} c γ i u⋆ with ⟦ γ ⟧ₛ ρ | 𝒰⋆⟦ γ ⟧ₛ u⋆
  conv₇Eq⋆⟨_⟩ {x = x} {ρ = ρ} c γ i u⋆ | [ ρ′ , .x ≔ a ] | 𝓊⋆≔ u⋆′ uₐ =
    begin
      [ ρ′ , x ≔ a ]
    Eq⋆⟨ eq⋆≔ (symEq⋆ (aux₄₈₁⟨ c ⟩ u⋆′)) (symEq (aux₄₈₄ i uₐ)) ⟩
      [ ↓⟨ c ⟩⊩⋆ [ ρ′ , x ≔ a ] , x ≔ lookup [ ρ′ , x ≔ a ] i ]
    ∎⟨ 𝓊⋆≔ (cong↓⟨ c ⟩𝒰⋆ (𝓊⋆≔ u⋆′ uₐ)) (conglookup𝒰 (𝓊⋆≔ u⋆′ uₐ) i) ⟩
   where
     open Eq⋆Reasoning


-- The soundness theorem is shown mutually with a corresponding lemma for substitutions:

-- Theorem 4.
-- NOTE: Added missing uniformity assumptions.
module _ {{_ : Model}} where
  mutual
    Eq⟦_⟧≅ : ∀ {Γ A w} {M M′ : Γ ⊢ A} {ρ : w ⊩⋆ Γ} →
               M ≅ M′ → 𝒰⋆ ρ →
               Eq (⟦ M ⟧ ρ) (⟦ M′ ⟧ ρ)
    Eq⟦ refl≅ {M = M} ⟧≅                     u⋆ = reflEq (𝒰⟦ M ⟧ u⋆)
    Eq⟦ sym≅ p ⟧≅                            u⋆ = symEq (Eq⟦ p ⟧≅ u⋆)
    Eq⟦ trans≅ p p′ ⟧≅                       u⋆ = transEq (Eq⟦ p ⟧≅ u⋆) (Eq⟦ p′ ⟧≅ u⋆)
    Eq⟦ congƛ≅ {M = M} {M′} p ⟧≅             u⋆ = eq⊃ (λ c uₐ → Eq⟦ p ⟧≅ (𝓊⋆≔ (cong↑⟨ c ⟩𝒰⋆ u⋆) uₐ))
    Eq⟦ cong∙≅ {M = M} {M′} {N} {N′} p p′ ⟧≅ u⋆ = cong⟦∙⟧⟨ refl⊇ ⟩Eq (Eq⟦ p ⟧≅ u⋆)
                                                                     (𝒰⟦ M ⟧ u⋆)
                                                                     (𝒰⟦ M′ ⟧ u⋆)
                                                                     (Eq⟦ p′ ⟧≅ u⋆)
                                                                     (𝒰⟦ N ⟧ u⋆)
                                                                     (𝒰⟦ N′ ⟧ u⋆)
    Eq⟦ cong▶≅ {M = M} {M′} {γ} {γ′} p pₛ ⟧≅ u⋆ = transEq (Eq⟦ M ⟧ (Eq⋆⟦ pₛ ⟧≅ₛ u⋆) (𝒰⋆⟦ γ ⟧ₛ u⋆) (𝒰⋆⟦ γ′ ⟧ₛ u⋆))
                                                          (transEq (Eq⟦ p ⟧≅ (𝒰⋆⟦ γ′ ⟧ₛ u⋆))
                                                                   (reflEq (𝒰⟦ M′ ⟧ (𝒰⋆⟦ γ′ ⟧ₛ u⋆))))
    Eq⟦ conv₁≅ M N γ ⟧≅                      u⋆ = Eq⟦ M ⟧ (eq⋆≔ (aux₄₂₅⟨ refl⊇ ⟩ (𝒰⋆⟦ γ ⟧ₛ u⋆))
                                                                (reflEq (𝒰⟦ N ⟧ u⋆)))
                                                          (𝓊⋆≔ (cong↑⟨ refl⊇ ⟩𝒰⋆ (𝒰⋆⟦ γ ⟧ₛ u⋆))
                                                               (𝒰⟦ N ⟧ u⋆))
                                                          (𝓊⋆≔ (𝒰⋆⟦ γ ⟧ₛ u⋆)
                                                               (𝒰⟦ N ⟧ u⋆))
    Eq⟦_⟧≅ {ρ = ρ} (conv₂≅ {x = x} c M) u⋆ =
      eq⊃ (λ c′ {a} uₐ →
        begin
          ⟦ M ⟧ ρ ⟦∙⟧⟨ c′ ⟩ a
        Eq⟨ aux₄₁₃ c′ refl⊇ (𝒰⟦ M ⟧ u⋆) uₐ ⟩
          (↑⟨ c′ ⟩ (⟦ M ⟧ ρ) ⟦∙⟧⟨ refl⊇ ⟩ a)
        Eq⟨ cong⟦∙⟧⟨ refl⊇ ⟩Eq (↑⟨ c′ ⟩Eq⟦ M ⟧ u⋆)
                               (cong↑⟨ c′ ⟩𝒰 (𝒰⟦ M ⟧ u⋆))
                               (𝒰⟦ M ⟧ (cong↑⟨ c′ ⟩𝒰⋆ u⋆))
                               (reflEq uₐ) uₐ uₐ ⟩
          ⟦ M ⟧ (↑⟨ c′ ⟩ ρ) ⟦∙⟧⟨ refl⊇ ⟩ a
        Eq⟨ cong⟦∙⟧⟨ refl⊇ ⟩Eq (Eq⟦ M ⟧ (symEq⋆ (aux₄₈₁⟨ c ⟩ (cong↑⟨ c′ ⟩𝒰⋆ u⋆)))
                                        (cong↑⟨ c′ ⟩𝒰⋆ u⋆)
                                        (cong↓⟨ c ⟩𝒰⋆ (𝓊⋆≔ (cong↑⟨ c′ ⟩𝒰⋆ u⋆) uₐ)))
                               (𝒰⟦ M ⟧ (cong↑⟨ c′ ⟩𝒰⋆ u⋆))
                               (𝒰⟦ M ⟧ (cong↓⟨ c ⟩𝒰⋆ (𝓊⋆≔ (cong↑⟨ c′ ⟩𝒰⋆ u⋆) uₐ)))
                               (reflEq uₐ) uₐ uₐ ⟩
          ⟦ M ⟧ (↓⟨ c ⟩ [ ↑⟨ c′ ⟩ ρ , x ≔ a ]) ⟦∙⟧⟨ refl⊇ ⟩ a
        ∎⟨ case (𝒰⟦ M ⟧ (cong↓⟨ c ⟩𝒰⋆ (𝓊⋆≔ (cong↑⟨ c′ ⟩𝒰⋆ u⋆) uₐ))) of
             (λ { (𝓊⊃ h₀ h₁ h₂) → h₀ refl⊇ uₐ }) ⟩)
        where
          open EqReasoning
    Eq⟦ conv₃≅ M γ ⟧≅                        u⋆ = reflEq (𝒰⟦ M ⟧ u⋆)
    Eq⟦ conv₄≅ c i j ⟧≅                      u⋆ = symEq (aux₄₂₁⟨ c ⟩ u⋆ j i)
    Eq⟦ conv₅≅ c M ⟧≅                        u⋆ = Eq⟦ M ⟧ (aux₄₂₄⟨ c ⟩ u⋆) (cong↓⟨ c ⟩𝒰⋆ u⋆) u⋆
    Eq⟦ conv₆≅ M N γ ⟧≅                      u⋆ = cong⟦∙⟧⟨ refl⊇ ⟩Eq (reflEq (𝒰⟦ M ⟧ (𝒰⋆⟦ γ ⟧ₛ u⋆)))
                                                                     (𝒰⟦ M ⟧ (𝒰⋆⟦ γ ⟧ₛ u⋆))
                                                                     (𝒰⟦ M ⟧ (𝒰⋆⟦ γ ⟧ₛ u⋆))
                                                                     (reflEq (𝒰⟦ N ⟧ (𝒰⋆⟦ γ ⟧ₛ u⋆)))
                                                                     (𝒰⟦ N ⟧ (𝒰⋆⟦ γ ⟧ₛ u⋆))
                                                                     (𝒰⟦ N ⟧ (𝒰⋆⟦ γ ⟧ₛ u⋆))
    Eq⟦ conv₇≅ M γ δ ⟧≅                      u⋆ = reflEq (𝒰⟦ M ⟧ (𝒰⋆⟦ γ ⟧ₛ (𝒰⋆⟦ δ ⟧ₛ u⋆)))

    Eq⋆⟦_⟧≅ₛ : ∀ {Γ Δ w} {γ γ′ : Γ ⋙ Δ} {ρ : w ⊩⋆ Γ} →
                 γ ≅ₛ γ′ → 𝒰⋆ ρ →
                 Eq⋆ (⟦ γ ⟧ₛ ρ) (⟦ γ′ ⟧ₛ ρ)
    Eq⋆⟦ refl≅ₛ {γ = γ} ⟧≅ₛ                    u⋆ = reflEq⋆ (𝒰⋆⟦ γ ⟧ₛ u⋆)
    Eq⋆⟦ sym≅ₛ pₛ ⟧≅ₛ                          u⋆ = symEq⋆ (Eq⋆⟦ pₛ ⟧≅ₛ u⋆)
    Eq⋆⟦ trans≅ₛ pₛ pₛ′ ⟧≅ₛ                    u⋆ = transEq⋆ (Eq⋆⟦ pₛ ⟧≅ₛ u⋆) (Eq⋆⟦ pₛ′ ⟧≅ₛ u⋆)
    Eq⋆⟦ cong●≅ₛ {γ′ = γ′} {δ} {δ′} pₛ pₛ′ ⟧≅ₛ u⋆ = transEq⋆ (Eq⋆⟦ pₛ ⟧≅ₛ (𝒰⋆⟦ δ ⟧ₛ u⋆))
                                                             (Eq⋆⟦ γ′ ⟧ₛ (Eq⋆⟦ pₛ′ ⟧≅ₛ u⋆)
                                                                         (𝒰⋆⟦ δ ⟧ₛ u⋆)
                                                                         (𝒰⋆⟦ δ′ ⟧ₛ u⋆))
    Eq⋆⟦ cong≔≅ₛ pₛ p ⟧≅ₛ                      u⋆ = eq⋆≔ (Eq⋆⟦ pₛ ⟧≅ₛ u⋆) (Eq⟦ p ⟧≅ u⋆)
    Eq⋆⟦ conv₁≅ₛ γ δ θ ⟧≅ₛ                     u⋆ = reflEq⋆ (𝒰⋆⟦ γ ⟧ₛ (𝒰⋆⟦ δ ⟧ₛ (𝒰⋆⟦ θ ⟧ₛ u⋆)))
    Eq⋆⟦ conv₂≅ₛ M γ δ ⟧≅ₛ                     u⋆ = reflEq⋆ (𝓊⋆≔ (𝒰⋆⟦ γ ⟧ₛ (𝒰⋆⟦ δ ⟧ₛ u⋆))
                                                                 (𝒰⟦ M ⟧ (𝒰⋆⟦ δ ⟧ₛ u⋆)))
    Eq⋆⟦ conv₃≅ₛ c M γ ⟧≅ₛ                     u⋆ = transEq⋆ (aux₄₂₃ refl⊇ c (𝒰⋆⟦ γ ⟧ₛ u⋆))
                                                             (aux₄₂₄⟨ refl⊇ ⟩ (𝒰⋆⟦ γ ⟧ₛ u⋆))
    Eq⋆⟦ conv₄≅ₛ c c′ c″ ⟧≅ₛ                   u⋆ = aux₄₂₆ c′ c″ c u⋆
    Eq⋆⟦ conv₅≅ₛ c γ ⟧≅ₛ                       u⋆ = Eq⋆⟦ γ ⟧ₛ (aux₄₂₄⟨ c ⟩ u⋆) (cong↓⟨ c ⟩𝒰⋆ u⋆) u⋆
    Eq⋆⟦ conv₆≅ₛ c γ ⟧≅ₛ                       u⋆ = conv₆Eq⋆⟨ c ⟩ γ u⋆
    Eq⋆⟦ conv₇≅ₛ c γ i ⟧≅ₛ                     u⋆ = conv₇Eq⋆⟨ c ⟩ γ i u⋆

-- They are both shown by induction on the rules of conversion.  Notice that the soundness
-- result holds in any Kripke model.


-- 4.9. Decision algorithm for conversion
-- --------------------------------------
--
-- We now have a decision algorithm for testing convertibility between proof trees: compute
-- the normal form and check if they are exactly the same.  This decision algorithm is correct,
-- since by Theorem 2 we have `M ≅ nf M` and `M′ ≅ nf M′` and, by hypothesis, `nf M ≡ nf M′`,
-- we get by transitivity of `_≅_`, that `M ≅ M′`.

-- Theorem 5.
thm₅ : ∀ {Γ A} → (M M′ : Γ ⊢ A) → nf M ≡ nf M′ → M ≅ M′
thm₅ M M′ p = begin
                M
              ≅⟨ thm₂ M ⟩
                nf M
              ≡⟨ p ⟩
                nf M′
              ≅⟨ sym≅ (thm₂ M′) ⟩
                M′
              ∎
              where
                open ≅-Reasoning

-- The decision algorithm is also complete since by Theorem 4 and the hypothesis, `M ≅ M′`, we get
-- `Eq (⟦ M ⟧ refl⊩⋆) (⟦ N ⟧ refl⊩⋆)` and by Corollary 1 we get `nf M ≡ nf N`.

-- NOTE: Added missing lemmas.
module _ where
  proj⟨_⟩𝒰⋆ : ∀ {Γ Δ} →
                (c : Δ ⊇ Γ) →
                𝒰⋆ proj⟨ c ⟩⊩⋆
  proj⟨ done ⟩𝒰⋆     = 𝓊⋆[]
  proj⟨ step c i ⟩𝒰⋆ = 𝓊⋆≔ proj⟨ c ⟩𝒰⋆ (⟦ν⟧𝒰 i)

  refl𝒰⋆ : ∀ {Γ} → 𝒰⋆ (refl⊩⋆ {Γ})
  refl𝒰⋆ = proj⟨ refl⊇ ⟩𝒰⋆

-- Theorem 6.
thm₆ : ∀ {Γ A} → (M M′ : Γ ⊢ A) → M ≅ M′ → nf M ≡ nf M′
thm₆ M M′ p = cor₁ M M′ (Eq⟦ p ⟧≅ refl𝒰⋆)
