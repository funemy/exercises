open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Data.Nat using (ℕ; _+_; zero; suc)
open import Function using (_∘_)

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

b1011 : Bin
b1011 = ⟨⟩ I O I I

b011 : Bin
b011 = ⟨⟩ O I I

b11 : Bin
b11 = ⟨⟩ I I

postulate
  -- 1. Two representations of zeros are equal.
  -- 2. Binaries that only differ in their leading zeros are equal.
  ⟨⟩O≡⟨⟩ : ⟨⟩ O ≡ ⟨⟩

b11≡b011 : b11 ≡ b011
b11≡b011 rewrite ⟨⟩O≡⟨⟩ = refl

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (b O) = b I
inc (b I) = (inc b) O

_ : inc (⟨⟩ I O I I) ≡ ⟨⟩ I I O O
_ = refl

_+b_ : Bin → Bin → Bin
⟨⟩ +b b2 = b2
b1 +b ⟨⟩ = b1
(b1 O) +b (b2 O) = (b1 +b b2) O
(b1 O) +b (b2 I) = (b1 +b b2) I
(b1 I) +b (b2 O) = (b1 +b b2) I
(b1 I) +b (b2 I) = inc (b1 +b b2) O


b+b≡bO : ∀ b → b +b b ≡ b O
b+b≡bO ⟨⟩ rewrite ⟨⟩O≡⟨⟩ = refl
b+b≡bO (b O) rewrite b+b≡bO b = refl
b+b≡bO (b I) rewrite b+b≡bO b = refl

from : Bin → ℕ
from ⟨⟩ = 0
from (b O) = from b + from b
from (b I) = suc (from b + from b)

_ : from b11 ≡ 3
_ = refl

_ : from b1011 ≡ 11
_ = refl

to : ℕ → Bin
to zero = ⟨⟩
to (suc n) = inc (to n)

from∘inc≡suc∘from : ∀ b → from (inc b) ≡ suc (from b)
from∘inc≡suc∘from ⟨⟩ = refl
from∘inc≡suc∘from (b O) = refl
from∘inc≡suc∘from (b I) rewrite from∘inc≡suc∘from b = cong suc (lemma1 (from b) (from b))
  where
  lemma1 : ∀ a b → a + suc b ≡ suc (a + b)
  lemma1 zero b = refl
  lemma1 (suc a) b = cong suc (lemma1 a b)

from∘to : ∀ n → from (to n) ≡ n
from∘to zero = refl
from∘to (suc n) rewrite from∘inc≡suc∘from (to n) = cong suc (from∘to n)

inc-+-comm : ∀ x y → (inc x) +b y ≡ inc (x +b y)
inc-+-comm ⟨⟩ ⟨⟩ = refl
inc-+-comm ⟨⟩ (y O) = refl
inc-+-comm ⟨⟩ (y I) = refl
inc-+-comm (x O) ⟨⟩ = refl
inc-+-comm (x O) (y O) = refl
inc-+-comm (x O) (y I) = refl
inc-+-comm (x I) ⟨⟩ = refl
inc-+-comm (x I) (y O) = cong _O (inc-+-comm x y)
inc-+-comm (x I) (y I) = cong _I (inc-+-comm x y)

to-dist : ∀ x y → to (x + y) ≡ (to x) +b (to y)
to-dist zero y = refl
to-dist (suc x) y rewrite inc-+-comm (to x) (to y) = cong inc (to-dist x y)

to∘from : ∀ b → to (from b) ≡ b
to∘from ⟨⟩ = refl
to∘from (b O)
  rewrite to-dist (from b) (from b)
  rewrite to∘from b
  = b+b≡bO b
to∘from (b I)
  rewrite to-dist (from b) (from b)
  rewrite to∘from b
  rewrite b+b≡bO b
  = refl

