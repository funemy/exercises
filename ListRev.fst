// This file proves a simple property about list reversal in an intentionally non-idiomatic style in FStar.
// The goal is to see if we can reduce the smt queries (doesn't seem possible to make fstar independent of
// z3) and finish a proof in an ordinary dependently-typed way.
module ListRev

noeq
type list (a: Type) =
  | Nil
  | Cons: a -> list a -> list a

let rec append (#a: Type) (l1: list a) (l2: list a): list a =
  match l1 with
  | Nil -> l2
  | Cons h t -> Cons h (append t l2)

let singleton (#a: Type) (x: a): list a = Cons x Nil

let snoc (#a: Type) (l: list a) (x: a): list a = append l (singleton x)

let rec rev (#a: Type) (l: list a): list a =
  match l with
  | Nil -> Nil
  | Cons h t -> snoc (rev t) h

// In most dependent type based proof assistant, this proof does not goes through.
// F* internally looks into the constructors of `equals` type (i.e., performing an implicit dependent pattern matching),
// hence it can figure out `equal a c` holds.
// This also implies UIP (uniqueness of identity proofs) is trivial in F*.
let trans (#t: Type) (#a: t) (#b: t) (#c: t)
    (pf1: equals a b)
    (pf2: equals b c)
    : equals a c
  = Refl

// Congruence
let cong (#t: Type) (#u: Type) (#a: t) (#b: t) (pf: equals a b) (f: t -> u): equals (f a) (f b) = Refl

// Symmetry
let sym (#t: Type) (#a: t) (#b: t) (pf: equals a b): equals b a = Refl

let rec lemma_rev_snoc
        (#a: Type)
        (h: a)
        (l: list a)
        : equals (Cons h (rev l)) (rev (snoc l h))
  = match l with
    | Nil -> Refl
    | Cons hd tl ->
      let ih: equals (rev (snoc tl h)) (Cons h (rev tl)) = lemma_rev_snoc h tl in
      Refl

let rec rev_rev_id (#a: Type) (l: list a): equals l (rev (rev l)) =
  match l with
  | Nil -> Refl
  | Cons h t ->
    // IH: t == rev (rev t)
    let ih: equals t (rev (rev t)) = rev_rev_id t in
    // step1: h :: t == h :: (rev (rev t))
    // This is proven by applying congruence on IH
    // But surprisingly, using Refl can also prove this (try the commented line below):
    //   let step1: equals (Cons h t) (Cons h (reverse (reverse t))) = Refl in
    let step1: equals (Cons h t) (Cons h (rev (rev t))) = cong ih (Cons h) in
    // step2: h :: (rev (rev t)) == rev ((rev t) @@ [h])
    // This is proven apply the lemma `lemma_rev_snoc` on `h` and `reverse t`
    let step2: equals (Cons h (rev (rev t))) (rev (snoc (rev t) h)) = lemma_rev_snoc h (rev t) in
    // step3: rev ((rev t) @@ [h]) = rev (rev (h :: t))
    // This is proven by unpacking the definition of `rev`
    let step3: equals (rev (snoc (rev t) h)) (rev (rev (Cons h t))) = Refl in
    // Notice that the LHS of step1 and the RHS of step3 form our proof goal
    // Hence we proved the theorem by applying transitivity twice.
    trans step1 (trans step2 step3)

open FStar.Squash

// squashing the proven theorem `rev_rev_id` into a proof-irrelevant one
let rev_rev_id' (#a: Type) (l: list a): (l == (rev (rev l))) = return_squash (rev_rev_id l)

// `Lemma (l == (rev (rev l)))` is a sugar for `Lemma (ensures (l == (rev (rev l))))`
let rev_rev_id'' (#a: Type) (l: list a): Lemma (l == (rev (rev l))) =
  give_proof (rev_rev_id' l)
  // or simply:
  // rev_rev_id' l

let rev_rev_id''' (#a: Type) (l: list a): Lemma (equals l (rev (rev l))) =
  give_proof (rev_rev_id' l)
  // or simply:
  // rev_rev_id' l
