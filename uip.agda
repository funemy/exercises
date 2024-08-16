{-- ice1000 has a relevant blog post: https://ice1000.org/2020/08-15-AxiomK.html --}
module UIP where

open import Agda.Primitive

module HeteroEq where
  private
    variable
      ℓa ℓb : Level

  data _≡_ {A : Set ℓa} (a : A) : {B : Set ℓb} → B -> Set ℓa where
    refl : a ≡ a

  J : {A : Set ℓa} → {B : Set ℓb} → {a : A} → {b : B}
      → (target : a ≡ b)
      → (motive : {ℓx : Level} → {X : Set ℓx} → {x : X} → a ≡ x → Set ℓa)
      → (base : motive refl)
      → motive target
  J refl motive base = base

  uip' : {A : Set ℓa} → {B : Set ℓb} → {a : A} → {b : B}
         → (g : a ≡ b) → (h : a ≡ b) → g ≡ h
  uip' refl refl = refl

  uip : {A : Set ℓa} → {B : Set ℓb} → {a : A} → {b : B}
        → (g : a ≡ b) → (h : a ≡ b) → g ≡ h
  uip g h = J h (λ a≡x → g ≡ a≡x) (J g (λ a≡x → a≡x ≡ refl) refl)

module HomoEq where
  private
    variable
      ℓ : Level

  data _≡_ {A : Set ℓ} (a : A) : A -> Set ℓ where
    refl : a ≡ a

  -- An intuition of the J rule:
  -- First, we want to understand what `motive` is doing. `motive` returns a Set/Type,
  -- therefore `motive` is a function that *constructs* a proposition,
  -- or in logic term, `motive` is a predicate.
  --
  -- Second, the signature of `motive` may look weird at the first place, since it's
  -- universally quantifying over all `x` of type A.
  -- However, notice that _≡_ is not defined recursively, therefore, we will only
  -- generate two propositions using motive.
  --
  -- The first one is `motive refl` (the type of base).
  -- The type of `refl` here is `a ≡ a`.
  -- Therefore, this is a proposition that mentions (or depends on) `a` and the proof
  -- of `a ≡ a` (i.e., refl).
  -- Let's denote it as P(a, pf : a ≡ a)
  --
  -- Similarly, the second application of `motive`, i.e., `motive target` (the return type),
  -- gives us a proposition P(b, pf' : a ≡ b)
  --
  -- Now, the type of J rule can be simplified to
  -- J : a ≡ b → P(a, pf : a ≡ a) → P(b, pf' : a ≡ b)
  -- Now this type can be intuitively translate to natural language:
  -- Given a proof of a ≡ b, and a proof of P which depends on a and the proof of a ≡ a,
  -- We can conclude that the proposition P', which substitute a to b and the proof of a ≡ a
  -- to the proof of a ≡ b, also holds.
  --
  -- Now it's also easy to justify why the J rule make sense.
  -- Since we already proved a ≡ b, of course we can substitute a to b.
  -- Since we already proved a ≡ b, and in fact, the only way to prove a ≡ b is when
  -- b can be normalized to a, therefore the proof should be identical to a ≡ a, then
  -- of course it's safe to substitute pf to pf'
  --
  -- The reasoning above is precisely reflected on the implementation of J
  -- Since a and b are identical, the proofs of a ≡ a and a ≡ b are also identical,
  -- there is no need for actual substitution, and instead, we can just return `base`,
  -- i.e., the proof of "P(a, pf : a ≡ a)"
  --
  -- This definition of J rule is called based path induction in HoTT
  -- (https://www.pls-lab.org/en/Path_induction)
  J : {A : Set ℓ} → {a b : A}
      → (target : a ≡ b)
      → (motive : {x : A} → a ≡ x → Set ℓ)
      → (base : motive refl)
      → motive target
  J refl motive base = base

  -- Axiom K, presented in a way that's easy to compare with the J above
  K : {A : Set ℓ} {a : A}
      → (target : a ≡ a)
      → (motive : a ≡ a → Set ℓ)
      → (base : motive refl)
      → motive target
  K refl motive base = base

  -- This is a directly comparison between J rule and subst.
  -- We can see from the implementation, J and subst are
  -- computationally the same.
  -- The difference is between the types of P and motive.
  -- P has one less parameter then motive, therefore it's
  -- less expressive on the predicate we can write here.
  subst : {A : Set ℓ} → {a b : A}
        → a ≡ b
        → (P : A → Set ℓ)
        → P a
        → P b
  subst refl _ Pa = Pa

  -- This shows you can implement subst using J
  subst' : {A : Set ℓ} → {a b : A}
        → a ≡ b
        → (P : A → Set ℓ)
        → P a
        → P b
  subst' a≡b P Pa = J a≡b (λ {a} x → P a) Pa

  -- You can still prove uip of homogeneous ≡ using dependent pattern matching
  uip' : {A : Set ℓ} {a b : A} →
         (g : a ≡ b) → (h : a ≡ b) → g ≡ h
  uip' refl refl = refl

  -- uip : {A : Set ℓ} → {a b : A} →
  --       (g : a ≡ b) → (h : a ≡ b) → g ≡ h
  -- -- we cannot put `g ≡ a≡x` in the first hole anymore
  -- uip g h = J h (λ a≡x → {!!}) {!!}

  -- Since we also defined K, let's try prove UIP using K (and inevitably J)
  -- We first prove reflexivity proofs are unique
  uip-refl : {A : Set ℓ} {a : A} →
             (g : a ≡ a) → (h : a ≡ a) → g ≡ h
  uip-refl g h = K g (λ p → p ≡ h) (K h (λ p' → refl ≡ p') refl)

  -- Now we can prove UIP by generalizing uip-refl
  uip'' : {A : Set ℓ} {a b : A} →
          (g : a ≡ b) → (h : a ≡ b) → g ≡ h
  uip'' {_} {A} {a} {b} g = J g (λ {x} p → (q : a ≡ x) → p ≡ q) (λ q → uip-refl refl q)


module ML-≡ where
  -- MLTT's original I
  -- Comparing to HomoEq define above, both sides of the equality
  -- are encoded as indices rather than parameters.
  data _≡_ {A : Set} : A → A -> Set where
    refl : (a : A) → a ≡ a

  -- TODO: define J rule on this version
  J : {ℓ : Level} → {A : Set} → {from to : A} →
      (target : from ≡ to) →
      (motive : {from to : A} → from ≡ to → Set ℓ) →
      (base : motive (refl from)) →
      motive target
  -- TODO: define replace on this version of J


