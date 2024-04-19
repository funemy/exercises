open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data Bool : Set where
  T : Bool
  F : Bool

goal : ∀ (f : Bool → Bool) (b : Bool) → f (f (f b)) ≡ f b
goal f T with f T in eq1
goal f T | T rewrite eq1 = eq1
goal f T | F with f F in eq2
goal f T | F | T = eq1
goal f T | F | F = eq2
goal f F with f F in eq3
goal f F | T with f T in eq4
goal f F | T | T = eq4
goal f F | T | F = eq3
goal f F | F rewrite eq3 = eq3

