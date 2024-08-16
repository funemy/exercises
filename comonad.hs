module Comonad where

class (Functor w) => Comonad w where
    extract :: w a -> a
    duplicate :: w a -> w (w a)

    extend :: (w a -> b) -> w a -> w b
    extend f wa = fmap f (duplicate wa)

data Store s a = Store
    { here :: s
    , view :: s -> a
    }

instance Functor (Store s) where
  fmap :: (a -> b) -> Store s a -> Store s b
  fmap f (Store s v) = Store s (f . v)

-- a comonad represents a (lazy) unfolding of all possible future states (?)
instance Comonad (Store s) where
  extract :: Store s a -> a
  extract (Store s v) = v s
  duplicate :: Store s a -> Store s (Store s a)
  duplicate (Store s v) = Store s (\next -> Store next v)

move :: s -> Store s a -> Store s a
move s store = view (duplicate store) s

-- Ed Kmett's Co
newtype Co w a = Co {runCo :: forall r . w (a -> r) -> r}

instance (Functor w) => Functor (Co w) where
  fmap :: Functor w => (a -> b) -> Co w a -> Co w b
  fmap f (Co w) = Co (w . fmap (. f))

instance (Comonad w) => Applicative (Co w) where
  pure :: Comonad w => a -> Co w a
  pure a = Co (flip extract a)
  (<*>) :: Comonad w => Co w (a -> b) -> Co w a -> Co w b
  cwf <*> cwa = _

instance (Comonad w) => Monad (Co w) where
  (>>=) :: Comonad w => Co w a -> (a -> Co w b) -> Co w b
  (Co k) >>= f = Co (k . extend (\wbr a -> runCo (f a) wbr))
