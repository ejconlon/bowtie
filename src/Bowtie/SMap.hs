{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

-- | 'SMap' is a "symbol map": Given a domain 'd' and symbol 's', an 'SMap d'
-- maps 's' to a value 'Val d s'.
--
-- Why is this useful? Consider the following scenario: you have some DAG of
-- transformations that read and write annotations on some datatype, for example,
-- in a compiler. Then you can type these transformations according to the
-- what they read and write. These transormations can be grouped into a
-- domain 'd', and each annotation can be identified by a key symbol 's' and
-- a value type 'Val d s'.
module Bowtie.SMap
  ( Val
  , Member
  , Inserted
  , Deleted
  , SMap
  , emptySMap
  , singletonSMap
  , indexSMap
  , updateSMap
  , insertSMap
  , deleteSMap
  )
where

import Data.Dependent.Map (DMap)
import Data.Dependent.Map qualified as DMap
import Data.Functor.Identity (Identity (..))
import Data.GADT.Compare (GCompare (..), GEq (..), GOrdering (..), defaultCompare, defaultEq)
import Data.Kind (Type)
import Data.Proxy (Proxy (..))
import Data.Type.Equality ((:~:) (..))
import GHC.TypeLits (KnownSymbol, OrderingI (..), Symbol, cmpSymbol, sameSymbol)

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

type family SymEq (a :: Symbol) (b :: Symbol) where
  SymEq a a = True
  SymEq a b = False

-- | x is a member of xs
class Member (x :: Symbol) (xs :: [Symbol])

instance {-# OVERLAPS #-} Member x (x : xs)

instance {-# OVERLAPS #-} (SymEq x y ~ False, Member x xs) => Member x (y : xs)

-- | x is NOT a member of xs
class NonMember (x :: Symbol) (xs :: [Symbol])

instance NonMember x '[]

instance (SymEq x y ~ False, NonMember x xs) => NonMember x (y : xs)

-- | x inserted into xs is zs (and x is not already member of xs, so xs /= zs)
class (NonMember x xs, Member x zs) => Inserted (x :: Symbol) (xs :: [Symbol]) (zs :: [Symbol]) | x xs -> zs, xs zs -> x

instance {-# OVERLAPS #-} Inserted x '[] (x : '[])

instance {-# OVERLAPS #-} (SymEq x y ~ False, Inserted x xs zs) => Inserted x (y ': xs) (y ': zs)

-- | x removed from xs is zs (and x is member of xs, so xs /= zs)
class
  (Member x xs, NonMember x zs) =>
  Deleted (x :: Symbol) (xs :: [Symbol]) (zs :: [Symbol])
    | x xs -> zs
    , xs zs -> x
    , x zs -> xs

instance {-# OVERLAPS #-} (NonMember x xs) => Deleted x (x : xs) xs

instance {-# OVERLAPS #-} (SymEq x y ~ False, Deleted x xs zs) => Deleted x (y ': xs) (y ': zs)

newtype SMap (d :: Type) (xs :: [Symbol]) = SMap (DM d)

emptySMap :: SMap d '[]
emptySMap = SMap emptyDM

singletonSMap :: (KnownSymbol s) => Proxy s -> Val d s -> SMap d '[s]
singletonSMap ps v = SMap (singletonDM ps v)

indexSMap :: (KnownSymbol s, Member s xs) => Proxy s -> SMap d xs -> Val d s
indexSMap ps (SMap m) = indexDM ps m

updateSMap :: (KnownSymbol s, Member s xs) => Proxy s -> Val d s -> SMap d xs -> SMap d xs
updateSMap ps v (SMap m) = SMap (insertDM ps v m)

insertSMap :: (KnownSymbol s, Inserted s xs zs) => Proxy s -> Val d s -> SMap d xs -> SMap d zs
insertSMap ps v (SMap m) = SMap (insertDM ps v m)

deleteSMap :: (KnownSymbol s, Deleted s xs zs) => Proxy s -> SMap d xs -> SMap d zs
deleteSMap ps (SMap m) = SMap (deleteDM ps m)
