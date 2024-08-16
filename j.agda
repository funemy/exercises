open import Agda.Primitive

module J where
  private
    variable
      ℓ : Level

  data _≡_ {A : Set ℓ} (a : A) : A -> Set ℓ where
    refl : a ≡ a

  -- This is called based path induction
  J-based : {A : Set ℓ} → {a : A} → {b : A}
      → (target : a ≡ b)
      → (motive : (x : A) → a ≡ x → Set ℓ)
      → (base : motive a refl)
      → motive b target
  J-based refl motive base = base

  -- This is the J (or path induction) rule defined by Martin-Löf
  J : {A : Set ℓ} → {a : A} → {b : A}
      → (target : a ≡ b)
      → (motive : (x y : A) → x ≡ y → Set ℓ)
      → (base : (z : A) → motive z z refl)
      → motive a b target
  J {_} {_} {a} {b} refl motive base = base a


  JBasedSort : Setω
  JBasedSort = {ℓj ℓm : Level} → {A : Set ℓj} → {a : A} → {b : A}
      → (target : a ≡ b)
      → (motive : (x : A) → a ≡ x → Set ℓm)
      → (base : motive a refl)
      → motive b target


  JSort : Setω
  JSort = {ℓj ℓm : Level} → {A : Set ℓj} → {a : A} → {b : A}
         → (target : a ≡ b)
         → (motive : (x y : A) → x ≡ y → Set ℓm)
         → (base : (z : A) → motive z z refl)
         → motive a b target


  -- Can we prove the two J rule definitions are equivalent?
  JB⇒J : JBasedSort → JSort
  JB⇒J JB {_} {_} {_} {a} {_} = λ target motive base → JB target (motive a) (base a)

  -- Amazing!!!!
  -- Following the HoTT book
  J⇒JB : JSort → JBasedSort
  J⇒JB J {ℓj} {ℓm} {A} {a} {b} = f a b
    where
       D : (x y : A) → x ≡ y → Set (ℓj ⊔ (lsuc ℓm))
       D x y x≡y = (C : (z : A) → x ≡ z → Set ℓm) → C x refl → C y x≡y

       d : (x : A) → D x x refl
       d x m c = c

       f : (x y : A) → (p : x ≡ y) → D x y p
       f x y p = J p D d
