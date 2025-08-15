open import Data.Nat
open import Data.Integer as I
open import Data.String renaming (_==_ to strEq)
open import Data.Bool
open import Data.Empty
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable.Core using (isYes)
open import Data.Maybe as M using (Maybe; just) renaming (nothing to exn)

Num : Set
Num = ℤ

Loc : Set
Loc = ℕ

data Symbol (T : Set) : Set where
    sym : T → Symbol T

-- Symbols represented by Strings
SSymbol : Set
SSymbol = Symbol String

infix 4 _==_
_==_ : SSymbol → SSymbol → Bool
(sym s1) == (sym s2) = strEq s1 s2

data Aexp : Set where
    num : Num → Aexp
    var : SSymbol → Aexp
    plus : Aexp → Aexp → Aexp
    mul : Aexp → Aexp → Aexp
    sub : Aexp → Aexp → Aexp

data Bexp : Set where
    tt : Bexp
    ff : Bexp
    eq : Aexp → Aexp → Bexp
    leq : Aexp → Aexp → Bexp
    lneg : Bexp → Bexp
    land : Bexp → Bexp → Bexp

data Stm : Set where
    assign : SSymbol → Aexp → Stm
    skip : Stm
    seq : Stm → Stm → Stm
    ite : Bexp → Stm → Stm → Stm
    whiledo : Bexp → Stm → Stm

WHILE_DO_ : Bexp → Stm → Stm
WHILE b DO s = whiledo b s

IF_THEN_ELSE_ : Bexp → Stm → Stm → Stm
IF b THEN s1 ELSE s2 = ite b s1 s2

-- well, I would like to use semicolon, but it's special in Agda.
_,_ : Stm → Stm → Stm
s1 , s2 = seq s1 s2

Value : Set
Value = Num

-- Value extended with a special case (i.e., `exn`) to denote exceptions.
Value⊥ : Set
Value⊥ = Maybe Num

Bool⊥ : Set
Bool⊥ = Maybe Bool

vplus : Value⊥ → Value⊥ → Value⊥
vplus (just x1) (just x2) = just (x1 I.+ x2)
vplus _ _ = exn

vmul : Value⊥ → Value⊥ → Value⊥
vmul (just x1) (just x2) = just (x1 I.* x2)
vmul _ _ = exn

vsub : Value⊥ → Value⊥ → Value⊥
vsub (just x1) (just x2) = just (x1 I.- x2)
vsub _ _ = exn

veq : Value⊥ → Value⊥ → Maybe Bool
veq (just x1) (just x2) = just (isYes (x1 I.≟ x2))
veq _ _ = exn

vleq : Value⊥ → Value⊥ → Maybe Bool
vleq (just x1) (just x2) = just (isYes (x1 I.≤? x2))
vleq _ _ = exn

vand : Maybe Bool → Maybe Bool → Maybe Bool
vand (just b1) (just b2) = just (b1 ∧ b2)
vand _ _ = exn

-- vleq : Value → Value → Bool
-- vleq (V x1) →

V' : ℕ → Value
V' n = (+ n)

Heap : Set
Heap = SSymbol → Value⊥

-- heap update
_[_:=_] : Heap → SSymbol → Num → Heap
h [ s := v ] = λ x → if (s == x) then just v else h x
-- heap access
_[_] : Heap → SSymbol → Value⊥
h [ s ] = h s

emptyHeap : Heap
emptyHeap = λ x → exn

X : SSymbol
X = sym "X"

Y : SSymbol
Y = sym "Y"

testHeap1 : Heap
testHeap1 = emptyHeap [ X := (V' 42) ]

test1 : emptyHeap [ X ] ≡ exn
test1 = refl

test2 : testHeap1 [ X ] ≡ just (V' 42)
test2 = refl

-- denotational semantics for Arithmetic expressions (Aexp)
A⟦_⟧_ : Aexp → Heap → Value⊥
A⟦ num x ⟧ s = just x
A⟦ var x ⟧ s = s x
A⟦ plus a₁ a₂ ⟧ s = vplus (A⟦ a₁ ⟧ s) (A⟦ a₂ ⟧ s)
A⟦ mul a₁ a₂ ⟧ s = vmul (A⟦ a₁ ⟧ s) (A⟦ a₂ ⟧ s)
A⟦ sub a₁ a₂ ⟧ s = vsub (A⟦ a₁ ⟧ s) (A⟦ a₂ ⟧ s)

-- denotational semantics for Boolean expressions (Bexp)
B⟦_⟧_ : Bexp → Heap → Bool⊥
B⟦ tt ⟧ s = just true
B⟦ ff ⟧ s = just false
B⟦ eq a₁ a₂ ⟧ s = veq (A⟦ a₁ ⟧ s) (A⟦ a₂ ⟧ s)
B⟦ leq a₁ a₂ ⟧ s = vleq (A⟦ a₁ ⟧ s) (A⟦ a₂ ⟧ s)
B⟦ lneg b ⟧ s = M.map not (B⟦ b ⟧ s)
B⟦ land b₁ b₂ ⟧ s = vand (B⟦ b₁ ⟧ s) (B⟦ b₂ ⟧ s)

-- big-step semantics for Statement (Stm)
--  assign : SSymbol → Aexp → Stm
--  skip : Stm
--  seq : Stm → Stm → Stm
--  ite : Bexp → Stm → Stm → Stm
--  whiledo : Bexp → Stm → Stm
data [_,_]⇓_ : (s : Stm) → (σ : Heap) → (σ' : Maybe Heap) → Set where
    s-assign :
        { s : Heap } →
        { x : SSymbol } →
        { aexp : Aexp } →
        let s' = M.map (λ v → s [ x := v ]) (A⟦ aexp ⟧ s) in
    ----------------------------------------------------------
        [ assign x aexp , s ]⇓ s'

    s-skip :
        { s : Heap } →
    ----------------------------------------------------------
        [ skip , s ]⇓ just s

    s-seq :
        { stm1 stm2 : Stm} →
        { s s'' : Heap } →
        { s' : Maybe Heap} →
        [ stm1 , s ]⇓ just s'' →
        [ stm2 , s'' ]⇓ s' →
    ----------------------------------------------------------
        [ seq stm1 stm2 , s ]⇓ s'

    s-seq-⊥ :
        { stm1 stm2 : Stm} →
        { s s' s'' : Heap } →
        [ stm1 , s ]⇓ exn →
    ----------------------------------------------------------
        [ seq stm1 stm2 , s ]⇓ exn

    s-ite-tt :
        { b : Bexp } →
        { stm1 stm2 : Stm } →
        { s : Heap } →
        { s' : Maybe Heap } →
        B⟦ b ⟧ s ≡ just true →
        [ stm1 , s ]⇓ s' →
    ----------------------------------------------------------
        [ ite b stm1 stm2 , s ]⇓ s'

    s-ite-ff :
        { b : Bexp } →
        { stm1 stm2 : Stm } →
        { s : Heap } →
        { s' : Maybe Heap } →
        B⟦ b ⟧ s ≡ just false →
        [ stm2 , s ]⇓ s' →
    ----------------------------------------------------------
        [ ite b stm1 stm2 , s ]⇓ s'

    s-whiledo-true :
        { b : Bexp } →
        { stm : Stm } →
        { s s'' : Heap } →
        { s' : Maybe Heap } →
        B⟦ b ⟧ s ≡ just true →
        [ stm , s ]⇓ just s'' →
        [ whiledo b stm , s'' ]⇓ s' →
    ----------------------------------------------------------
        [ whiledo b stm , s ]⇓ s'

    s-whiledo-false :
        { b : Bexp } →
        { stm : Stm } →
        { s : Heap } →
        B⟦ b ⟧ s ≡ just false →
    ----------------------------------------------------------
        [ whiledo b stm , s ]⇓ just s

    s-whiledo-⊥₁ :
        { b : Bexp } →
        { stm : Stm } →
        { s : Heap } →
        B⟦ b ⟧ s ≡ exn →
    ----------------------------------------------------------
        [ whiledo b stm , s ]⇓ exn

    s-whiledo-⊥₂ :
        { b : Bexp } →
        { stm : Stm } →
        { s s'' : Heap } →
        { s' : Maybe Heap } →
        B⟦ b ⟧ s ≡ just true →
        [ stm , s ]⇓ exn →
    ----------------------------------------------------------
        [ whiledo b stm , s ]⇓ exn