-- Selective Applicative Functor
-- https://dl.acm.org/doi/abs/10.1145/3341694
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -W #-}

module SelectiveFunctor where

import Data.Bool (bool)
import Data.Function ((&))
import Prelude hiding (Applicative (..), Either (..), Functor (..), Monad, either, (<$>), (>>=))

data Either a b
    = Left a
    | Right b

instance Functor (Either a) where
    fmap f = \case
        Left a -> Left a
        Right b -> Right (f b)

instance Functor ((->) a) where
    fmap = (.)

either :: (a -> c) -> (b -> c) -> Either a b -> c
either f g = \case
    Left a -> f a
    Right b -> g b

class Functor f where
    fmap :: (a -> b) -> f a -> f b

(<$>) :: (Functor f) => (a -> b) -> f a -> f b
(<$>) = fmap

class (Functor f) => Applicative f where
    pure :: a -> f a
    (<*>) :: f (a -> b) -> f a -> f b

class (Applicative f) => Selective f where
    select :: f (Either a b) -> f (a -> b) -> f b

(<*?) :: (Selective f) => f (Either a b) -> f (a -> b) -> f b
(<*?) = select

class (Selective f) => Monad f where
    return :: a -> f a
    (>>=) :: f a -> (a -> f b) -> f b

-- Note that `ap` has the below specific impl, which restricts the order of effects to be executed
-- (i.e., m1 first, then m2)
ap :: (Monad f) => f (a -> b) -> f a -> f b
ap m1 m2 =
    m1 >>= \f ->
        m2 >>= \a ->
            pure (f a)

selectM :: (Monad f) => f (Either a b) -> f (a -> b) -> f b
selectM m f =
    m >>= \case
        -- ($ a) is \g -> g a
        Left a -> ($ a) <$> f
        Right b -> pure b

-- Note that this implementation is different from selectM,
-- as the effect of the second argument (i.e., f), will always be triggered.
-- While in selectM, the effect of the second argument may not be triggered
-- if the inner content of the first argument is `Right b`
selectA :: (Applicative f) => f (Either a b) -> f (a -> b) -> f b
selectA m f = (\e g -> either g id e) <$> m <*> f

-- According to the paper:
-- - selectM is good for conditional execution of effects
-- - selectA is good for static analysis
-- see section 3 for more details

-- The paper gives this impl for apS
apS :: (Selective f) => f (a -> b) -> f a -> f b
apS f m = select (Left <$> f) ((&) <$> m)

-- FIXME: this impl is WRONG
-- You might wonder why the impl below is not used.
-- The problem is -- the effects are executed in the opposite order!
apS' :: (Selective f) => f (a -> b) -> f a -> f b
apS' f m = select (Left <$> m) f

-- The lesson here is, the order of the execution of effects matters.
-- In fact, the power of selective applicative functor is indeed a finer grained control of effects,
-- which makes it sit in betweeen <*> and >>= (as can also be seen from the typeclass hierachy).

-- Combinators
--
-- The actual meaning of whenS depends the on impl of select
-- If select is implemented as selectM, then the effect will be executed when the bool is True.
whenS :: (Selective f) => f Bool -> f () -> f ()
whenS x y = selector <*? effect
  where
    -- if we flip the order of Right and Left, we get unlessS
    selector = bool (Right ()) (Left ()) <$> x
    effect = const <$> y

branch :: (Selective f) => f (Either a b) -> f (a -> c) -> f (b -> c) -> f c
branch x l r = fmap (fmap Left) x <*? fmap (fmap Right) l <*? r

-- FIXME: another WRONG impl:
-- It's easy to notice the impl here doesn't use the select operator (i.e., <*?).
-- Really the difference here is the difference between <*> and <*? -- <*> always executes effects while <*? conditionally executes effects.
-- The distinction between branch and branch' therefore is a bit like selectM and selectA.
-- As a result, this wrong impl will execute both effects (i.e., the effects of l and r) unconditionally,
-- on the other hand, branch will only trigger one effect based on the value of Either a b.
--
-- NOTE:
-- BTW, ideally there is a GHC flag to warn the fact that <*? is not used,
-- therefore the class contraint can be simplify to "Applicative f"
branch' :: (Selective f) => f (Either a b) -> f (a -> c) -> f (b -> c) -> f c
branch' x l r = (\e f g -> either f g e) <$> x <*> l <*> r

-- Below is an example showing the difference between branch and branch'
-- test2 shows that the effect of [plus1, plus1] (here we are using the list monad, so the effect is essentially duplication) happened
-- on both Right and Left (both 0 and 3 are duplicated), while in test1, the effect is only happened on Left values.
instance Functor [] where
    fmap = map

instance Applicative [] where
    pure x = [x]
    [] <*> _ = []
    _ <*> [] = []
    fs <*> xs = foldr (\f l -> l ++ fmap f xs) [] fs

instance Monad [] where
    return = pure
    (>>=) = flip concatMap

instance Selective [] where
    select = selectM

plus1 :: Int -> Int
plus1 x = x + 1

minus1 :: Int -> Int
minus1 x = x - 1

-- NOTE:
-- In this example, [plus1, plus1] has the effect of doubling the number of elements in the list, while
-- [minus1] has no effect.
-- We can see from the return value that only Lefts are duplicated
test1 :: [Int]
test1 = branch [Right 1, Left 2] [plus1, plus1] [minus1]

-- fmap (fmap Left) [Right 1, Left 2] <*? fmap (fmap Right) [plus1, plus1] <*? [minus1]
-- [fmap Left (Right 1), fmap Left (Left 2)] <*? fmap (fmap Right) [plus1, plus1] <*? [minus1]
-- [Right (Left 1), Left 2] <*? fmap (fmap Right) [plus1, plus1] <*? [minus1]
-- [Right (Left 1), Left 2] <*? [\x -> Right (x + 1), \x -> Right (x + 1)] <*? [minus1]
-- [Left 1, Right 3, Right 3] <*? [minus1]
-- [0, 3 3]

-- NOTE:
-- In contrast, here both Right and Left values are duplicated, so the effect is executed unconditionally.
test2 :: [Int]
test2 = branch' [Right 1, Left 2] [plus1, plus1] [minus1]

-- [\f g -> either f g Right 1, \f g -> either f g Left 2] <*> [plus1, plus1] <*> [minus1]
-- [\g -> either plus1 g Right 1, \g -> either plus1 g Right 1, \g -> either plus1 g Left 2, \g -> either plus1 g Left 2] <*> [minus1]
-- [either plus1 minus1 Right 1, \g -> either plus1 minus1 Right 1, \g -> either plus1 minus1 Left 2, \g -> either plus1 minus1 Left 2]
-- [0, 0, 3, 3]
--

newtype Const m a = Const {getConst :: m}

instance Functor (Const m) where
    fmap _ (Const x) = Const x

instance Monoid m => Applicative (Const m) where
    pure _ = Const mempty
    Const x <*> Const y = Const $ x <> y

data Validation e a = Failure e | Success a

-- instance Monad (Validation e) where
--   return = Success
--   (Failure e) >>= _ = Failure e
--   (Success a) >>= f = f a

