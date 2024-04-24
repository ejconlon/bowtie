{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

module Bowtie.Member
  ( Val
  , Member
  , Inserted
  , Deleted
  , SM
  , emptySM
  , singletonSM
  , indexSM
  , insertSM
  , deleteSM
  )
where

import Data.Dependent.Map (DMap)
import Data.Dependent.Map qualified as DMap
import Data.Functor.Identity (Identity (..))
import Data.GADT.Compare (GCompare (..), GEq (..), GOrdering (..), defaultCompare, defaultEq)
import Data.Kind (Type)
import Data.Proxy (Proxy (..))
import Data.Type.Equality ((:~:) (..))
import GHC.TypeLits (CmpSymbol, KnownSymbol, OrderingI (..), Symbol, cmpSymbol, sameSymbol)

type family Val (d :: Type) (s :: Symbol) :: Type

data Key (d :: Type) (v :: Type) where
  Key
    :: (KnownSymbol s, v ~ Val d s)
    => Proxy s
    -> Proxy v
    -> Key d v

instance GEq (Key d) where
  geq (Key ps1 _) (Key ps2 _) =
    fmap (\Refl -> Refl) (sameSymbol ps1 ps2)

instance Eq (Key d v) where
  (==) = defaultEq

instance GCompare (Key d) where
  gcompare (Key ps1 _) (Key ps2 _) =
    case cmpSymbol ps1 ps2 of
      LTI -> GLT
      EQI -> GEQ
      GTI -> GGT

instance Ord (Key d v) where
  compare = defaultCompare

key :: (KnownSymbol s, v ~ Val d s) => Proxy s -> Key d v
key = flip Key Proxy

type DM (d :: Type) = DMap (Key d) Identity

emptyDM :: DM d
emptyDM = DMap.empty

singletonDM :: (KnownSymbol s) => Proxy s -> Val d s -> DM d
singletonDM ps v = DMap.singleton (key ps) (Identity v)

lookupDM :: (KnownSymbol s) => Proxy s -> DM d -> Maybe (Val d s)
lookupDM ps m = fmap runIdentity (DMap.lookup (key ps) m)

indexDM :: (KnownSymbol s) => Proxy s -> DM d -> Val d s
indexDM ps m = runIdentity (m DMap.! key ps)

insertDM :: (KnownSymbol s) => Proxy s -> Val d s -> DM d -> DM d
insertDM ps v = DMap.insert (key ps) (Identity v)

deleteDM :: (KnownSymbol s) => Proxy s -> DM d -> DM d
deleteDM ps = DMap.delete (key ps)

class Member (x :: Symbol) (xs :: [Symbol])

instance Member x (x : xs)

instance {-# OVERLAPS #-} (CmpSymbol x y ~ GT, Member x xs) => Member x (y : xs)

class Inserted (x :: Symbol) (xs :: [Symbol]) (zs :: [Symbol]) | x xs -> zs

instance Inserted x '[] (x : '[])

instance Inserted x (x : xs) (x : xs)

instance {-# OVERLAPS #-} (CmpSymbol x y ~ GT, Inserted x xs zs) => Inserted x (y ': xs) (y ': zs)

class Deleted (x :: Symbol) (xs :: [Symbol]) (zs :: [Symbol]) | x xs -> zs

instance Deleted x '[] '[]

instance Deleted x (x : xs) xs

instance {-# OVERLAPS #-} (CmpSymbol x y ~ GT, Deleted x xs zs) => Deleted x (y ': xs) (y ': zs)

newtype SM (d :: Type) (xs :: [Symbol]) = SM (DM d)

emptySM :: SM d '[]
emptySM = SM emptyDM

singletonSM :: (KnownSymbol s) => Proxy s -> Val d s -> SM d '[s]
singletonSM ps v = SM (singletonDM ps v)

indexSM :: (KnownSymbol s, Member s xs) => Proxy s -> SM d xs -> Val d s
indexSM ps (SM m) = indexDM ps m

insertSM :: (KnownSymbol s, Inserted s xs zs) => Proxy s -> Val d s -> SM d xs -> SM d zs
insertSM ps v (SM m) = SM (insertDM ps v m)

deleteSM :: (KnownSymbol s, Deleted s xs zs) => Proxy s -> SM d xs -> SM d zs
deleteSM ps (SM m) = SM (deleteDM ps m)
