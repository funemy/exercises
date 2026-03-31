-- An example of W-type and indexed W-type cooked by Reed
-- from cofree chat :).

-- This technique will introduce a huge amount of syntactic noise but it only requires you to implement a handful of things
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Level using (Lift; lift)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)

-- A polynomial functor
-- Intuitition:
--  This can be viewed as a tree, where you have `P .Pos` kinds of branches,
--   each with a branching factor of `P .Dir`.
--  So `.Pos` describes constructors and non-recursive arguments,
--  and `Dir` describes the recursive arguments for each constructor.
record Poly (o ℓ : Level) : Set (lsuc o ⊔ lsuc ℓ) where
  no-eta-equality
  field
    Pos : Set o
    Dir : Pos → Set ℓ

open Poly

-- W-type, a fixpoint of a polynomial functor
data Mu {o ℓ} (P : Poly o ℓ) : Set (o ⊔ ℓ) where
  roll : (p : P .Pos) → (P .Dir p → Mu P) → Mu P

data Nat-tag : Set where
  `zero : Nat-tag
  `suc  : Nat-tag

NatP : Poly lzero lzero
NatP .Pos = Nat-tag
NatP .Dir `zero = ⊥
NatP .Dir `suc = ⊤

suc : Mu NatP → Mu NatP
suc x = roll `suc (λ tt → x)

zero : Mu NatP
zero = roll `zero λ ()

record IxPoly {ℓi ℓj} (I : Set ℓi) (J : Set ℓj) (o ℓ : Level) : Set (ℓi ⊔ ℓj ⊔ lsuc o ⊔ lsuc ℓ) where
  no-eta-equality
  field
    Pos : J → Set o
    Dir : ∀ (j : J) → Pos j → Set ℓ
    idx  : ∀ (j : J) (p : Pos j) → Dir j p → I

open IxPoly

-- Same idea as the non-indexed Mu above:
-- The `.Pos` cases describe the constructors at each index and their non-recursive arguments.
-- The `.Dir` case tells you the recursive arguments.
-- The difference is that we also get to pick the index of each recursive argument as well
data IMu {ℓi o ℓ} {I : Set ℓi} (P : IxPoly I I o ℓ) : I → Set (ℓi ⊔ o ⊔ ℓ) where
  roll : ∀ {i : I} → (p : P .Pos i) → ((d : P .Dir i p) → IMu P (P .idx i p d)) → IMu P i

Nat : Set
Nat = Mu NatP

VecP : ∀ {ℓ} (A : Set ℓ) → IxPoly Nat Nat ℓ lzero
-- VecP A .Pos zero = Lift _ ⊤
-- VecP A .Pos (suc n) = A
-- VecP A .Dir zero _ = ⊥
-- VecP A .Dir (suc n) x = ⊤
-- VecP A .idx (suc n) t x = n
VecP A .Pos (roll `zero _) = Lift _ ⊤
VecP A .Pos (roll `suc n) = A
VecP A .Dir (roll `zero _) _ = ⊥
VecP A .Dir (roll `suc n) x = ⊤
VecP A .idx (roll `suc n) t x = n tt

nil : ∀ {ℓ} {A : Set ℓ} → IMu (VecP A) zero
nil = roll (lift tt) λ ()

cons : ∀ {ℓ} {A : Set ℓ} {n} → A → IMu (VecP A) n → IMu (VecP A) (suc n)
cons x xs = roll x λ _ → xs

-- Indexed coinductive types can be encoded using the same schema;
record Nu {ℓi o ℓ} {I : Set ℓi} (P : IxPoly I I o ℓ) (i : I) : Set (ℓi ⊔ o ⊔ ℓ) where
  coinductive
  field
    pos : P .Pos i
    step : (d : P .Dir i pos) → Nu P (P .idx i pos d)
