{-# OPTIONS_GHC -W #-}
module Cata where

-- This definition can be found in Data.Fix package
-- The difference between Fix and Mu is that
-- Mu encode a inductive type directly as its fold
-- Therefore it only represents the least fixed-point.
--
-- Whereas in Haskell, due to Laziness, Fix actually contains both least and greatest fixed-points
newtype Mu f = In { unIn :: forall a . (f a -> a) -> a }

data ListF a b = NilF | ConsF a b

instance Functor (ListF a) where
  fmap :: (b -> c) -> ListF a b -> ListF a c
  fmap _ NilF = NilF
  fmap f (ConsF a b) = ConsF a (f b)

type List a = Mu (ListF a)

test0 :: List Int
test0 = In (\alg -> alg NilF)

-- see, now we don't need to implement cata, since it's already in our encoding
test1 :: List Int
test1 = In (\alg -> alg (ConsF 2 (alg (ConsF 1 (alg NilF)))))

-- more generally
nil :: List a
nil = In (\alg -> alg NilF)

cons :: a -> List a -> List a
cons a l = In (\alg -> alg (ConsF a (unIn l alg)))

sumAlg :: ListF Int Int -> Int
sumAlg NilF = 0
sumAlg (ConsF a r) = a + r

sum1 :: Int
sum1 = unIn test1 sumAlg

test2 :: List Int
test2 = cons 6 (cons 5 (cons 4 (cons 3 (cons 2 (cons 1 nil)))))

sum2 :: Int
sum2 = unIn test2 sumAlg

