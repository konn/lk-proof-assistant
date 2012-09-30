{-# LANGUAGE ConstraintKinds, DataKinds, GADTs, PolyKinds, Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables, TypeFamilies, TypeOperators         #-}
module NAry where
import Control.Applicative
import GHC.Exts (Constraint)

data NAry (as :: [*]) a where
  Value :: a -> NAry '[] a
  Arg   :: (b -> NAry xs a) -> NAry (b ': xs) a

instance Show a => Show (NAry xs a) where
  showsPrec d (Value a) = showParen (d > 10) $ showString "Value " . showsPrec d a
  showsPrec d (Arg _)   = showParen (d > 10) $ showString "#Argument#"

data NAry' (as :: [*]) a = (as ~ '[]) => Value' a
                         | forall b xs . (as ~ (b ': xs))
                           => Arg' (b -> NAry' xs a)
type family (xs :: [*]) :~> a :: *

type instance '[] :~> a = a
type instance (x ': xs) :~> a = x -> xs :~> a

infixr :~>

fromNAry :: NAry xs a -> xs :~> a
fromNAry (Value a) = a
fromNAry (Arg f)   = fromNAry . f

data SList (as :: [*]) where
  SNil  :: SList '[]
  SCons :: a -> SList xs -> SList (a ': xs)

class SingList k where
  slist :: SList k

instance SingList '[] where
  slist = SNil

instance SingList xs => SingList (x ': xs) where
  slist = SCons undefined slist

toNAry' :: SList xs -> (xs :~> a) -> NAry xs a
toNAry' SNil a = Value a
toNAry' (SCons _ ts) f = Arg $ toNAry' ts . f

toNAry :: forall xs a. SingList xs => (xs :~> a) -> NAry xs a
toNAry = toNAry' (slist :: SList xs)

type family   All (cxt :: * -> Constraint) (xs :: [*]) :: Constraint
type instance All cxt '[]        = ()
type instance All cxt (x ': xs)  = (cxt x, All cxt xs)

applyStringList :: All k as
          => Proxy k
          -> (forall b. k b => String -> Maybe b)
          -> NAry as a
          -> [String]
          -> Maybe a
applyStringList Proxy _ (Value a) []     = Just a
applyStringList proxy r (Arg f)   (x:xs) =
  case f <$> r x of
    Nothing -> Nothing
    Just f' -> applyStringList proxy r f' xs
applyStringList _ _ _ _ = Nothing

data Proxy a = Proxy

data Nat = Z | S Nat

class ToInt (a :: Nat) where
  toInt :: Proxy a -> Int

instance ToInt 'Z where
  toInt _ = 0

instance ToInt n => ToInt ('S n) where
  toInt Proxy = toInt (Proxy :: Proxy n) + 1

