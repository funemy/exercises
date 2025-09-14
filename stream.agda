{-# OPTIONS --guardedness #-}

-- This code is written under Agda 2.8.0
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)

-- A standard definition of stream (infinite list)
record Stream (A : Set) : Set where
  coinductive
  field
    head : A
    tail : Stream A

open Stream

-- The function below fails agda's termination checker
{-# TERMINATING #-}
fromList : List ℕ → Stream ℕ
fromList [] = fromList (1 ∷ 2 ∷ 3 ∷ [])
fromList (h ∷ t) .head = h
fromList (h ∷ t) .tail = fromList t

-- BUT this works
fromList' : List ℕ → Stream ℕ
fromList' [] .head = 1
fromList' [] .tail = fromList' (2 ∷ 3 ∷ [])
fromList' (h ∷ t) .head = h
fromList' (h ∷ t) .tail = fromList' t

s : Stream ℕ
s = fromList (1 ∷ 2 ∷ 3 ∷ [])