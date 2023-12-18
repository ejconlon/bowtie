{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}

module Knots
  ( Base1
  , Recursive1 (..)
  , Corecursive1 (..)
  , cata1
  , cata1M
  , Fix (..)
  , mkFix
  , unMkFix
  , Knot (..)
  , mkKnot
  , unMkKnot
  , Anno (..)
  , MemoF (..)
  , Memo (..)
  , pattern MemoP
  , mkMemo
  , unMkMemo
  , memoKey
  , memoVal
  , memoCata
  , memoCataM
  ) where

import Control.Comonad (Comonad (..))
import Control.Monad ((>=>))
import Control.Monad.Reader (Reader, ReaderT (..), runReader)
import Data.Bifunctor (Bifunctor (..))
import Data.Bifoldable (Bifoldable (..))
import Data.Bitraversable (Bitraversable (..))
import Data.Bifunctor.TH (deriveBifoldable, deriveBifunctor, deriveBitraversable)
import Data.Functor.Apply (Apply (..))
import Data.Functor.Foldable (Base, Corecursive (..), Recursive (..))
import Data.Kind (Type)
import Prettyprinter (Pretty)
import Data.String (IsString)

type family Base1 (f :: Type -> Type) :: Type -> Type -> Type

class (Bifunctor (Base1 f), Functor f) => Recursive1 f where
  project1 :: f a -> Base1 f a (f a)

class (Bifunctor (Base1 f), Functor f) => Corecursive1 f where
  embed1 :: Base1 f a (f a) -> f a

cata1 :: (Recursive1 f, Base1 f ~ g) => (g a b -> b) -> f a -> b
cata1 f = go where go = f . second go . project1

cata1M :: (Monad m, Recursive1 f, Base1 f ~ g, Bitraversable g) => (g a b -> m b) -> f a -> m b
cata1M f = go where go = bitraverse pure go . project1 >=> f

fmapViaBi :: (Recursive1 f, Corecursive1 f, Base1 f ~ g) => (a -> b) -> f a -> f b
fmapViaBi f = go where go = embed1 . bimap f go . project1

foldrViaBi :: (Recursive1 f, Base1 f ~ g, Bifoldable g) => (a -> b -> b) -> b -> f a -> b
foldrViaBi f = flip go where go fa b = bifoldr f go b (project1 fa)

traverseViaBi :: (Recursive1 f, Corecursive1 f, Base1 f ~ g, Bitraversable g, Applicative m) => (a -> m b) -> f a -> m (f b)
traverseViaBi f = go where go = fmap embed1 . bitraverse f go . project1

type Fix :: (Type -> Type) -> Type
newtype Fix f = Fix {unFix :: f (Fix f)}

deriving newtype instance (Eq (f (Fix f))) => Eq (Fix f)

deriving newtype instance (Ord (f (Fix f))) => Ord (Fix f)

deriving stock instance (Show (f (Fix f))) => Show (Fix f)

deriving newtype instance (Pretty (f (Fix f))) => Pretty (Fix f)

deriving newtype instance (IsString (f (Fix f))) => IsString (Fix f)

type instance Base (Fix f) = f

instance (Functor f) => Recursive (Fix f) where project = unFix

instance (Functor f) => Corecursive (Fix f) where embed = Fix

mkFix :: (Recursive t, Base t ~ f) => t -> Fix f
mkFix = cata Fix

unMkFix :: (Corecursive t, Base t ~ f) => Fix f -> t
unMkFix = cata embed

type Knot :: (Type -> Type -> Type) -> Type -> Type
newtype Knot g a = Knot {unKnot :: g a (Knot g a)}

deriving newtype instance (Eq (g a (Knot g a))) => Eq (Knot g a)

deriving newtype instance (Ord (g a (Knot g a))) => Ord (Knot g a)

deriving stock instance (Show (g a (Knot g a))) => Show (Knot g a)

deriving newtype instance (Pretty (g a (Knot g a))) => Pretty (Knot g a)

deriving newtype instance (IsString (g a (Knot g a))) => IsString (Knot g a)

type instance Base1 (Knot g) = g

instance (Bifunctor g) => Recursive1 (Knot g) where project1 = unKnot

instance (Bifunctor g) => Corecursive1 (Knot g) where embed1 = Knot

instance (Bifunctor g) => Functor (Knot g) where fmap = fmapViaBi

instance (Bifunctor g, Bifoldable g) => Foldable (Knot g) where foldr = foldrViaBi

instance (Bitraversable g) => Traversable (Knot g) where traverse = traverseViaBi

mkKnot :: (Recursive1 f, Base1 f ~ g) => f a -> Knot g a
mkKnot = cata1 Knot

unMkKnot :: (Corecursive1 f, Base1 f ~ g) => Knot g a -> f a
unMkKnot = cata1 embed1

type Anno :: Type -> Type -> Type
data Anno b a = Anno {annoKey :: !b, annoVal :: a}
  deriving stock (Eq, Ord, Show, Functor, Foldable, Traversable)

deriveBifunctor ''Anno
deriveBifoldable ''Anno
deriveBitraversable ''Anno

instance (Semigroup b) => Apply (Anno b) where
  liftF2 f (Anno b1 a1) (Anno b2 a2) = Anno (b1 <> b2) (f a1 a2)

instance (Monoid b) => Applicative (Anno b) where
  pure = Anno mempty
  liftA2 = liftF2

instance Comonad (Anno b) where
  extract (Anno _ a) = a
  extend f anno@(Anno b _) = Anno b (f anno)

newtype MemoF f b r = MemoF { unMemoF :: Anno b (f r) }
  deriving stock (Show, Functor)
  deriving newtype (Eq, Ord)

instance (Apply f, Semigroup b) => Apply (MemoF f b) where
  liftF2 f (MemoF (Anno b1 f1)) (MemoF (Anno b2 f2)) = MemoF (Anno (b1 <> b2) (liftF2 f f1 f2))

instance (Applicative f, Monoid b) => Applicative (MemoF f b) where
  pure = MemoF . Anno mempty . pure
  liftA2 f (MemoF (Anno b1 f1)) (MemoF (Anno b2 f2)) = MemoF (Anno (b1 <> b2) (liftA2 f f1 f2))

type Memo :: (Type -> Type) -> Type -> Type
newtype Memo f b = Memo {unMemo :: Anno b (f (Memo f b))}

pattern MemoP :: b -> f (Memo f b) -> Memo f b
pattern MemoP b fm = Memo (Anno b fm)
{-# COMPLETE MemoP #-}

deriving stock instance (Eq b, Eq (f (Memo f b))) => Eq (Memo f b)

deriving stock instance (Ord b, Ord (f (Memo f b))) => Ord (Memo f b)

deriving stock instance (Show b, Show (f (Memo f b))) => Show (Memo f b)

instance (Functor f) => Functor (Memo f) where
  fmap f = go where go (MemoP k v) = MemoP (f k) (fmap go v)

instance (Foldable f) => Foldable (Memo f) where
  foldr f = flip go where go (MemoP k v) z = foldr go (f k z) v

instance (Traversable f) => Traversable (Memo f) where
  traverse f = go where go (MemoP k v) = liftA2 MemoP (f k) (traverse go v)

mkMemo :: (Recursive t, Base t ~ f) => (f b -> b) -> t -> Memo f b
mkMemo f = cata (\gm -> MemoP (f (fmap memoKey gm)) gm)

unMkMemo :: (Corecursive t, Base t ~ f) => Memo f b -> t
unMkMemo (MemoP _ gm) = embed (fmap unMkMemo gm)

memoKey :: Memo f b -> b
memoKey = annoKey . unMemo

memoVal :: Memo f b -> f (Memo f b)
memoVal = annoVal . unMemo

memoCata :: (Functor f) => (f x -> Reader b x) -> Memo f b -> x
memoCata f = go
 where
  go (MemoP b gm) = runReader (f (fmap go gm)) b

memoCataM :: (Monad m, Traversable f) => (f x -> ReaderT b m x) -> Memo f b -> m x
memoCataM f = go
 where
  go (MemoP b gm) = traverse go gm >>= \gx -> runReaderT (f gx) b

