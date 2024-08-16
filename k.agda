-- {-# OPTIONS --without-K #-}
module K where

open import Agda.Primitive
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

private
  variable
    ℓ : Level

J : {A : Set ℓ}→ {a b : A}
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
-- This implementation wouldn't type check if --without-K was enabled
K refl motive base = base

-- I found this stackoverflow post informative
-- https://stackoverflow.com/a/47243610
