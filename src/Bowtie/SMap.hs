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
  , NonMember
  , Inserted
  , Deleted
  , Reordered
  , SMap
  , emptySMap
  , singletonSMap
  , indexSMap
  , updateSMap
  , insertSMap
  , deleteSMap
  , reorderSMap
  )
where

import Data.Coerce (coerce)
import Data.Dependent.Map (DMap)
import Data.Dependent.Map qualified as DMap
import Data.Functor.Identity (Identity (..))
import Data.GADT.Compare (GCompare (..), GEq (..), GOrdering (..), defaultCompare, defaultEq)
import Data.Kind (Type)
import Data.Proxy (Proxy (..))
import Data.Type.Bool (type (||))
import Data.Type.Equality ((:~:) (..), type (==))
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

-- type family BoolEqF (x :: Symbol) (y :: Symbol) :: Bool where
--   BoolEqF x x = True
--   BoolEqF x y = False
--
-- castBoolEq :: (BoolEqF x y == True) => x :~: y
-- castBoolEq = undefined

type family MemberF (x :: Symbol) (xs :: [Symbol]) :: Bool where
  MemberF x '[] = False
  MemberF x (x : zs) = True
  MemberF x (y : zs) = MemberF x zs

class Member (x :: Symbol) (xs :: [Symbol])

instance (MemberF x (y : zs) ~ True, (x == y || MemberF x zs) ~ True) => Member x (y : zs)

class NonMember (x :: Symbol) (xs :: [Symbol])

instance NonMember x '[]

instance (MemberF x (y : zs) ~ False, (x == y || MemberF x zs) ~ False) => NonMember x (y : zs)

type family InsertedF (x :: Symbol) (xs :: [Symbol]) :: [Symbol] where
  InsertedF x '[] = '[x]
  InsertedF x (x : zs) = x : zs
  InsertedF x (y : zs) = y : InsertedF x zs

class (Member x zs) => Inserted (x :: Symbol) (xs :: [Symbol]) (zs :: [Symbol]) | x xs -> zs

instance (zs ~ InsertedF x '[], Member x zs) => Inserted x '[] zs

instance (zs ~ InsertedF x (y : ys), Member x zs) => Inserted x (y : ys) zs

type family DeletedF (x :: Symbol) (xs :: [Symbol]) :: [Symbol] where
  DeletedF x '[] = '[]
  DeletedF x (x : zs) = zs
  DeletedF x (y : zs) = y : DeletedF x zs

class (NonMember x zs) => Deleted (x :: Symbol) (xs :: [Symbol]) (zs :: [Symbol]) | x xs -> zs

instance (zs ~ DeletedF x '[]) => Deleted x '[] zs

instance (zs ~ DeletedF x (y : ys), NonMember x zs) => Deleted x (y : ys) zs

class Reordered (xs :: [Symbol]) (zs :: [Symbol])

instance Reordered '[] '[]

instance (Reordered xs (DeletedF x zs)) => Reordered (x : xs) zs

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

reorderSMap :: (Reordered xs zs) => SMap d xs -> SMap d zs
reorderSMap = coerce
