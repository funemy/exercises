-- For infinite derivation sequences
{-# OPTIONS --guardedness #-}

open import Agda.Builtin.Sigma using (_,_)
open import Data.Nat using (ℕ)
open import Data.Integer as I using (ℤ; +_; -_)
open import Data.String using (String) renaming (_==_ to strEq)
open import Data.Bool using (Bool; true; false; _∧_; if_then_else_; not)
open import Data.Empty
open import Data.Maybe as M using (Maybe; just) renaming (nothing to exn)
open import Data.Sum as S using (_⊎_; inj₁; inj₂)
open import Data.Product as P using (_×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable.Core using (isYes)

Num : Set
Num = ℤ

data Symbol (T : Set) : Set where
    sym : T → Symbol T

-- Symbols represented by Strings
SSymbol : Set
SSymbol = Symbol String

-- Decidable equality of symbols is the decidable equality of their underlying representation
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

-- Below is some syntactic sugar for the language defined above
N : ℕ → Aexp
N n = num (+ n)

-N : ℕ → Aexp
-N n = num (- (+ n))

infix 1 WHILE_DO_
WHILE_DO_ : Bexp → Stm → Stm
WHILE b DO s = whiledo b s

IF_THEN_ELSE_ : Bexp → Stm → Stm → Stm
IF b THEN s1 ELSE s2 = ite b s1 s2

_←_ : SSymbol → Aexp → Stm
x ← e = assign x e

_≟_ : Aexp → Aexp → Bexp
a ≟ b = eq a b

_≤?_ : Aexp → Aexp → Bexp
a ≤? b = leq a b

-- Sugar for sequencing.
-- I would like to use semicolon, but it's special in Agda.
infixr 0  _⨾_
_⨾_ : Stm → Stm → Stm
s1 ⨾ s2 = seq s1 s2

-- Value is represented as numbers (i.e., integers)
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

-- Heap is represented as a function from symbols to values
Heap : Set
Heap = SSymbol → Value⊥

-- heap update
_[_:=_] : Heap → SSymbol → Num → Heap
h [ s := v ] = λ x → if (s == x) then just v else h x

-- heap access
_[_] : Heap → SSymbol → Value⊥
h [ s ] = h s

-- an initial (i.e., empty) heap, where any access will leads to exceptions
σ₀ : Heap
σ₀ = λ x → exn

-- define symbols and variables X, Y, Z to make it easier to construct examples
X : SSymbol
X = sym "X"

`X : Aexp
`X = var X

Y : SSymbol
Y = sym "Y"

`Y : Aexp
`Y = var Y

Z : SSymbol
Z = sym "Z"

`Z : Aexp
`Z = var Z

testHeap1 : Heap
testHeap1 = σ₀ [ X := (+ 42) ]

_ : σ₀ [ X ] ≡ exn
_ = refl

_ : testHeap1 [ X ] ≡ just (+ 42)
_ = refl

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
data [_,_]⇓_ : (s : Stm) → (σ : Heap) → (σ' : Maybe Heap) → Set where
    b-assign :
        { x : SSymbol } →
        { aexp : Aexp } →
        { σ : Heap } →
        { v : Value } →
        A⟦ aexp ⟧ σ ≡ just v →
    ----------------------------------------------------------
        [ assign x aexp , σ ]⇓ just (σ [ x := v ])

    b-assign-⊥ :
        { x : SSymbol } →
        { aexp : Aexp } →
        { σ : Heap } →
        A⟦ aexp ⟧ σ ≡ exn →
    ----------------------------------------------------------
        [ assign x aexp , σ ]⇓ exn

    b-skip :
        { σ : Heap } →
    ----------------------------------------------------------
        [ skip , σ ]⇓ just σ

    b-seq :
        { stm1 stm2 : Stm} →
        { σ σ'' : Heap } →
        { σ'⊥ : Maybe Heap} →
        [ stm1 , σ ]⇓ just σ'' →
        [ stm2 , σ'' ]⇓ σ'⊥ →
    ----------------------------------------------------------
        [ seq stm1 stm2 , σ ]⇓ σ'⊥

    b-seq-⊥ :
        { stm1 stm2 : Stm} →
        { σ : Heap } →
        [ stm1 , σ ]⇓ exn →
    ----------------------------------------------------------
        [ seq stm1 stm2 , σ ]⇓ exn

    b-ite-tt :
        { b : Bexp } →
        { stm1 stm2 : Stm } →
        { σ : Heap } →
        { σ'⊥ : Maybe Heap } →
        B⟦ b ⟧ σ ≡ just true →
        [ stm1 , σ ]⇓ σ'⊥ →
    ----------------------------------------------------------
        [ ite b stm1 stm2 , σ ]⇓ σ'⊥

    b-ite-ff :
        { b : Bexp } →
        { stm1 stm2 : Stm } →
        { σ : Heap } →
        { σ'⊥ : Maybe Heap } →
        B⟦ b ⟧ σ ≡ just false →
        [ stm2 , σ ]⇓ σ'⊥ →
    ----------------------------------------------------------
        [ ite b stm1 stm2 , σ ]⇓ σ'⊥

    b-ite-⊥ :
        { b : Bexp } →
        { stm1 stm2 : Stm } →
        { σ : Heap } →
        B⟦ b ⟧ σ ≡ exn →
    ----------------------------------------------------------
        [ ite b stm1 stm2 , σ ]⇓ exn

    b-whiledo-tt :
        { b : Bexp } →
        { stm : Stm } →
        { σ σ'' : Heap } →
        { σ'⊥ : Maybe Heap } →
        B⟦ b ⟧ σ ≡ just true →
        [ stm , σ ]⇓ just σ'' →
        [ whiledo b stm , σ'' ]⇓ σ'⊥ →
    ----------------------------------------------------------
        [ whiledo b stm , σ ]⇓ σ'⊥

    b-whiledo-ff :
        { b : Bexp } →
        { stm : Stm } →
        { σ : Heap } →
        B⟦ b ⟧ σ ≡ just false →
    ----------------------------------------------------------
        [ whiledo b stm , σ ]⇓ just σ

    b-whiledo-⊥₁ :
        { b : Bexp } →
        { stm : Stm } →
        { σ : Heap } →
        B⟦ b ⟧ σ ≡ exn →
    ----------------------------------------------------------
        [ whiledo b stm , σ ]⇓ exn

    b-whiledo-⊥₂ :
        { b : Bexp } →
        { stm : Stm } →
        { σ : Heap } →
        B⟦ b ⟧ σ ≡ just true →
        [ stm , σ ]⇓ exn →
    ----------------------------------------------------------
        [ whiledo b stm , σ ]⇓ exn

StepRes : Set
StepRes = Heap ⊎ (Stm × Heap)

-- small-step semantics
-- The small-step semantics can either step into a new heap (state) for statements
-- like assign or skip, or step into a pair of next statement and a new state.
-- This is defined as the type `StepRes` above, additionally, we wrap it in `Maybe`
-- to model exceptions due to state-lookup.
data [_,_]⟶_ : (stm : Stm) → (σ : Heap) → (γ : Maybe StepRes) → Set where
    s-assign :
        { x : SSymbol } →
        { aexp : Aexp } →
        { s : Heap } →
        { v : Value } →
        A⟦ aexp ⟧ s ≡ just v →
    -----------------------------------------------------------------
        [ assign x aexp , s ]⟶ just (inj₁ (s [ x := v ]))

    s-assign-⊥ :
        { x : SSymbol } →
        { aexp : Aexp } →
        { s : Heap } →
        { v : Value } →
        A⟦ aexp ⟧ s ≡ exn →
    -----------------------------------------------------------------
        [ assign x aexp , s ]⟶ exn

    s-skip :
        { s : Heap } →
    -----------------------------------------------------------------
        [ skip , s ]⟶ just (inj₁ s)

    s-seq-1 :
        { s1 s2 s1' : Stm } →
        { s s' : Heap } →
        [ s1 , s ]⟶ just (inj₂ (s1' , s' )) →
    -----------------------------------------------------------------
        [ seq s1 s2 , s ]⟶ just (inj₂ (seq s1' s2 , s'))

    s-seq-2 :
        { s1 s2 : Stm } →
        { s s' : Heap } →
        [ s1 , s ]⟶ just (inj₁ s') →
    -----------------------------------------------------------------
        [ seq s1 s2 , s ]⟶ just (inj₂ ( s2 , s' ))

    s-seq-⊥ :
        { s1 s2 : Stm } →
        { s : Heap } →
        [ s1 , s ]⟶ exn →
    -----------------------------------------------------------------
        [ seq s1 s2 , s ]⟶ exn

    s-ite-tt :
        { b : Bexp } →
        { s1 s2 : Stm } →
        { s : Heap } →
        B⟦ b ⟧ s ≡ just true →
    -----------------------------------------------------------------
        [ ite b s1 s2 , s ]⟶ just (inj₂ (s1 , s))

    s-ite-ff :
        { b : Bexp } →
        { s1 s2 : Stm } →
        { s : Heap } →
        B⟦ b ⟧ s ≡ just false →
    -----------------------------------------------------------------
        [ ite b s1 s2 , s ]⟶ just (inj₂ (s2 , s))

    s-ite-⊥ :
        { b : Bexp } →
        { s1 s2 : Stm } →
        { s : Heap } →
        B⟦ b ⟧ s ≡ exn →
    -----------------------------------------------------------------
        [ ite b s1 s2 , s ]⟶ exn

    s-while-tt :
        { b : Bexp } →
        { stm : Stm } →
        { s : Heap } →
        B⟦ b ⟧ s ≡ just true →
    ---------------------------------------------------------------------
        [ whiledo b stm , s ]⟶ just (inj₂ (seq stm (whiledo b stm) , s))

    s-while-ff :
        { b : Bexp } →
        { stm : Stm } →
        { s : Heap } →
        B⟦ b ⟧ s ≡ just false →
    ---------------------------------------------------------------------
        [ whiledo b stm , s ]⟶ just (inj₂ (skip , s))

    s-while-⊥ :
        { b : Bexp } →
        { stm : Stm } →
        { s : Heap } →
        B⟦ b ⟧ s ≡ exn →
    -----------------------------------------------------------------
        [ whiledo b stm , s ]⟶ exn

-- derivation sequence (finite)
data [_,_]⟶*_ : (stm : Stm) → (σ : Heap) → (σ' : Heap) → Set where
    dseq-id :
        { stm : Stm } →
        { σ σ' : Heap } →
        [ stm , σ ]⟶ just (inj₁ σ') →
    -----------------------------------------------------------------
        [ stm , σ ]⟶* σ'

    dseq-cons :
        { stm stm' : Stm } →
        { σ σ' σ'' : Heap } →
        [ stm , σ ]⟶ just (inj₂ (stm' , σ'' )) →
        [ stm' , σ'' ]⟶* σ' →
    -----------------------------------------------------------------
        [ stm , σ ]⟶* σ'

-- some sugar for composing the derivation sequence
infixr -20 _::⟶⟨_⟩_
_::⟶⟨_⟩_ :
    { stm stm' : Stm } →
    ( σ : Heap ) →
    { σ'' σ' : Heap } →
    ( step : [ stm , σ ]⟶ just (inj₂ (stm' , σ'' )) ) →
    ( rest : [ stm' , σ'' ]⟶* σ' ) →
    [ stm , σ ]⟶* σ'
(_::⟶⟨_⟩_) {stm} σ {σ''} {σ'} step rest = dseq-cons step rest

helper-dseq-id :
    { stm : Stm } →
    ( σ : Heap ) →
    ( σ' : Heap ) →
    ( step : [ stm , σ ]⟶ just (inj₁ σ') ) →
    [ stm , σ ]⟶* σ'
helper-dseq-id {stm} σ σ' step = dseq-id step

infix -19 helper-dseq-id
syntax helper-dseq-id σ σ' step = σ ::⟶⟨ step ⟩∎ σ'

-- composing two derivation sequences
dseq∘ :
    { stm1 stm2 : Stm } →
    { σ σ' σ'' : Heap } →
    (deriv1 : [ stm1 , σ ]⟶* σ') →
    (deriv2 : [ stm2 , σ' ]⟶* σ'') →
    [ stm1 ⨾ stm2 , σ ]⟶* σ''
dseq∘ (dseq-id step) deriv2 = dseq-cons (s-seq-2 step) deriv2
dseq∘ (dseq-cons step deriv1) deriv2 =
    let tail = dseq∘ deriv1 deriv2 in
    dseq-cons (s-seq-1 step) tail

_ : [ skip , σ₀ ]⟶* σ₀
_ = σ₀ ::⟶⟨ s-skip ⟩∎ σ₀

_ : [ skip ⨾ skip , σ₀ ]⟶* σ₀
_ = σ₀ ::⟶⟨ s-seq-2 s-skip ⟩
    σ₀ ::⟶⟨ s-skip ⟩∎
    σ₀

-- an example program
prog1 : Stm
prog1 =
    X ← N 0 ⨾
    WHILE `X ≤? N 1 DO
        X ← (plus `X (N 1))

-- the expected final program state when prog1 terminates
σ-prog1 : Heap
σ-prog1 = σ₀ [ X := (+ 0) ] [ X := (+ 1) ] [ X := (+ 2) ]

-- execution of prog1 using big-step semantics
exec-prog1 : [ prog1 , σ₀ ]⇓ just σ-prog1
exec-prog1 = b-seq
                (b-assign refl)
                (b-whiledo-tt
                    refl
                    (b-assign refl)
                    (b-whiledo-tt
                        refl
                        (b-assign refl)
                        (b-whiledo-ff refl)))

-- this is a completely non-sugared version
dseq-prog1 : [ prog1 , σ₀ ]⟶* σ-prog1
dseq-prog1 = dseq-cons
                (s-seq-2 (s-assign refl))
                (dseq-cons
                    (s-while-tt refl)
                    (dseq-cons
                        (s-seq-2 (s-assign refl))
                        (dseq-cons
                            (s-while-tt refl)
                            (dseq-cons
                                (s-seq-2 (s-assign refl))
                                (dseq-cons
                                    (s-while-ff refl)
                                    (dseq-id s-skip))))))

-- describing the derivation sequence of prog1's small-step intepretation using the syntactic sugar defined above
dseq-sugared-prog1 : [ prog1 , σ₀ ]⟶* σ-prog1
dseq-sugared-prog1 =
    σ₀ ::⟶⟨ s-seq-2 (s-assign refl) ⟩
    σ₀ [ X := (+ 0) ] ::⟶⟨ s-while-tt refl ⟩
    σ₀ [ X := (+ 0) ] ::⟶⟨ s-seq-2 (s-assign refl) ⟩
    σ₀ [ X := (+ 0) ] [ X := (+ 1) ] ::⟶⟨ s-while-tt refl ⟩
    σ₀ [ X := (+ 0) ] [ X := (+ 1) ] ::⟶⟨ s-seq-2 (s-assign refl) ⟩
    σ₀ [ X := (+ 0) ] [ X := (+ 1) ] [ X := (+ 2) ] ::⟶⟨ s-while-ff refl ⟩
    σ₀ [ X := (+ 0) ] [ X := (+ 1) ] [ X := (+ 2) ] ::⟶⟨ s-skip ⟩∎
    σ₀ [ X := (+ 0) ] [ X := (+ 1) ] [ X := (+ 2) ]

-- For any big-step intepretation that doesn't raise exceptions,
-- there is a corresponding small-step derivation sequence.
-- Proof sketch:
--    1. first case-splitting on statements (Stm) of IMP
--    2. then doing induction on big-step derivation
-- In pen-and-paper proof, I suppose the order is more commonly flipped,
-- as in you first apply the induction principle of derivation tree, then
-- case-splitting on statements.
[∙,∙]⇓∙-implies-[∙,∙]⟶*∙ :
    ∀ (stm : Stm) (σ σ' : Heap) →
    [ stm , σ ]⇓ just σ' →
    [ stm , σ ]⟶* σ'
[∙,∙]⇓∙-implies-[∙,∙]⟶*∙ (assign x aexp) σ σ' (b-assign x₁) = dseq-id (s-assign x₁)
[∙,∙]⇓∙-implies-[∙,∙]⟶*∙ skip σ σ' b-skip = dseq-id s-skip
[∙,∙]⇓∙-implies-[∙,∙]⟶*∙ (seq stm1 stm2) σ σ' (b-seq {σ'' = σ''} deriv1 deriv2) =
    let sub-dseq1 = [∙,∙]⇓∙-implies-[∙,∙]⟶*∙ stm1 σ σ'' deriv1 in
    let sub-dseq2 = [∙,∙]⇓∙-implies-[∙,∙]⟶*∙ stm2 σ'' σ' deriv2 in
    dseq∘ sub-dseq1 sub-dseq2
[∙,∙]⇓∙-implies-[∙,∙]⟶*∙ (ite x stm1 stm2) σ σ' (b-ite-tt b deriv) =
    let sub-dseq = [∙,∙]⇓∙-implies-[∙,∙]⟶*∙ stm1 σ σ' deriv in
    dseq-cons (s-ite-tt b) sub-dseq
[∙,∙]⇓∙-implies-[∙,∙]⟶*∙ (ite x stm1 stm2) σ σ' (b-ite-ff b deriv) =
    let sub-dseq = [∙,∙]⇓∙-implies-[∙,∙]⟶*∙ stm2 σ σ' deriv in
    dseq-cons (s-ite-ff b) sub-dseq
[∙,∙]⇓∙-implies-[∙,∙]⟶*∙ (whiledo pred stm) σ σ' (b-whiledo-tt {σ'' = σ''} pred/tt deriv/stm deriv/while) =
    let sub-dseq/stm = [∙,∙]⇓∙-implies-[∙,∙]⟶*∙ stm σ σ'' deriv/stm in
    let sub-dseq/while = [∙,∙]⇓∙-implies-[∙,∙]⟶*∙ (whiledo pred stm) σ'' σ' deriv/while in
    dseq-cons (s-while-tt pred/tt) (dseq∘ sub-dseq/stm sub-dseq/while)
[∙,∙]⇓∙-implies-[∙,∙]⟶*∙ (whiledo pred stm) σ σ' (b-whiledo-ff pred/ff) = dseq-cons (s-while-ff pred/ff) (dseq-id s-skip)

-- record [_,_]⟶_ (stm : Stm) (σᵢ : Heap) (σ : Heap) : Set where
--     coinductive
--     field
--         trace :