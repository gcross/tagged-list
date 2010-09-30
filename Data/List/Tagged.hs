-- @+leo-ver=4-thin
-- @+node:gcross.20100917213812.1278:@thin Data/List/Tagged.hs
-- @@language Haskell
-- @<< Language extensions >>
-- @+node:gcross.20100918210837.1285:<< Language extensions >>
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UnicodeSyntax #-}
-- @-node:gcross.20100918210837.1285:<< Language extensions >>
-- @nl

module Data.List.Tagged where

-- @<< Import needed modules >>
-- @+node:gcross.20100918210837.1286:<< Import needed modules >>
import Prelude hiding (tail,foldl,foldr,map,mapM,mapM_,length)

import Control.Applicative
import Control.Monad.Trans.Abort

import Data.Binary
import Data.Foldable hiding (toList,mapM_)
import Data.Monoid
import Data.Traversable (Traversable(..))
import Data.Typeable

import TypeLevel.NaturalNumber hiding (NaturalNumber)
import TypeLevel.NaturalNumber.Induction
import TypeLevel.NaturalNumber.Operations

import Data.NaturalNumber
-- @-node:gcross.20100918210837.1286:<< Import needed modules >>
-- @nl

-- @+others
-- @+node:gcross.20100918210837.1287:Types
-- @+node:gcross.20100928114649.1285:TL
newtype TL α n = TL { unwrapTL :: TaggedList n α }
-- @-node:gcross.20100928114649.1285:TL
-- @+node:gcross.20100928151321.1296:ATL
newtype ATL t α n = ATL { unwrapATL :: t (TaggedList n α) }
-- @-node:gcross.20100928151321.1296:ATL
-- @+node:gcross.20100918210837.1288:TaggedList
data TaggedList n α where
    E :: TaggedList Zero α
    (:.) :: α → TaggedList n α → TaggedList (SuccessorTo n) α
  deriving Typeable

infixr :.
-- @-node:gcross.20100918210837.1288:TaggedList
-- @+node:gcross.20100918210837.1289:UntaggedList
data UntaggedList α = ∀ n. UntaggedList (TaggedList n α) deriving Typeable
-- @-node:gcross.20100918210837.1289:UntaggedList
-- @-node:gcross.20100918210837.1287:Types
-- @+node:gcross.20100918210837.1290:Instances
-- @+node:gcross.20100918210837.1291:Binary TaggedList
instance (NaturalNumber n, Binary α) ⇒ Binary (TaggedList n α) where
    get = fmap fromList get
    put = put . toList
-- @nonl
-- @-node:gcross.20100918210837.1291:Binary TaggedList
-- @+node:gcross.20100918210837.1292:Binary UntaggedList
instance Binary α ⇒ Binary (UntaggedList α) where
    get = fmap fromListAsUntagged get
    put (UntaggedList l) = put (toList l)
-- @nonl
-- @-node:gcross.20100918210837.1292:Binary UntaggedList
-- @+node:gcross.20100918210837.1295:Eq TaggedList
instance (NaturalNumber n, Eq α) ⇒ Eq (TaggedList n α) where
    x == y = runAbort (deduction2M () (\_ _ _ → return True) step (TL x) (TL y))
      where
        step :: Eq α ⇒ TL α (SuccessorTo n) → TL α (SuccessorTo n) → () → Abort Bool (TL α n,TL α n,())
        step (TL (x :. xs)) (TL (y :. ys)) b
          | x /= y    = abort False
          | otherwise = return (TL xs,TL ys,())
-- @nonl
-- @-node:gcross.20100918210837.1295:Eq TaggedList
-- @+node:gcross.20100918210837.1294:Foldable TaggedList
instance NaturalNumber n ⇒ Foldable (TaggedList n) where
    foldMap f l = deduction mempty (const id) (step f) (TL l)
      where
        step :: Monoid m ⇒ (α → m) → TL α (SuccessorTo n) → m → (TL α n,m)
        step f (TL (x :. xs)) a = (TL xs,a `mappend` f x)
-- @nonl
-- @-node:gcross.20100918210837.1294:Foldable TaggedList
-- @+node:gcross.20100918210837.1293:Functor TaggedList
instance NaturalNumber n ⇒ Functor (TaggedList n) where
    fmap f = withTL (transform (const (TL E)) (step f))
      where
        step :: ∀ α β n. (α → β) → (TL α n → TL β n) → TL α (SuccessorTo n) → TL β (SuccessorTo n) 
        step f recurse (TL (x :. xs)) = TL (f x :. withTL recurse xs)
-- @nonl
-- @-node:gcross.20100918210837.1293:Functor TaggedList
-- @+node:gcross.20100928151321.1295:Traversable TaggedList
instance NaturalNumber n ⇒ Traversable (TaggedList n) where
    traverse f = unwrapATL . transform (const . ATL . pure $ E) (step f) . TL
      where
        step :: ∀ α β t n. Applicative t ⇒ (α → t β) → (TL α n → ATL t β n) → TL α (SuccessorTo n) → ATL t β (SuccessorTo n) 
        step f recurse (TL (x :. xs)) = ATL (liftA2 (:.) (f x) (unwrapATL . recurse . TL $ xs))
-- @-node:gcross.20100928151321.1295:Traversable TaggedList
-- @-node:gcross.20100918210837.1290:Instances
-- @+node:gcross.20100918210837.1296:Functions
-- @+node:gcross.20100918210837.1300:append
append :: TaggedList m α → TaggedList n α → TaggedList (Plus m n) α
append E = id
append (x :. xs) = (x :.) . append xs
-- @-node:gcross.20100918210837.1300:append
-- @+node:gcross.20100918210837.1308:eqLists
eqLists :: Eq α ⇒ TaggedList m α → TaggedList n α → Bool
eqLists E E = True
eqLists E _ = False
eqLists _ E = False
eqLists (x:.xs) (y:.ys) = (x == y) && eqLists xs ys
-- @nonl
-- @-node:gcross.20100918210837.1308:eqLists
-- @+node:gcross.20100928114649.1287:fromList
fromList :: NaturalNumber n ⇒ [α] → TaggedList n α
fromList = unwrapTL . snd . induction z i
  where
    z [] = (undefined,TL E)
    z _ = error "List is too long to convert into a tagged list of the given length."
    i (x:xs) (TL l) = (xs,TL (x :. l))
    i [] _ = error "List is too short to convert into a tagged list of the given length."
-- @nonl
-- @-node:gcross.20100928114649.1287:fromList
-- @+node:gcross.20100918210837.1306:fromListAsUntagged
fromListAsUntagged :: [α] → UntaggedList α
fromListAsUntagged [] = UntaggedList E
fromListAsUntagged (x:rest) =
    case fromListAsUntagged rest of
        UntaggedList xs → UntaggedList (x :. xs)
-- @-node:gcross.20100918210837.1306:fromListAsUntagged
-- @+node:gcross.20100918210837.1298:head
head :: TaggedList (SuccessorTo n) α → α
head (x :. _) = x
-- @-node:gcross.20100918210837.1298:head
-- @+node:gcross.20100918210837.1301:join
join :: TaggedList m α → TaggedList n α → (TaggedList (Plus m n) α,TaggedList (Plus m n) β → (TaggedList m β,TaggedList n β))
join E v = (v,\z → (E,z))
join (x :. xs) v =
    let (vv,split) = join xs v 
    in (x :. vv
       ,(\(y :. ys) → let (a,b) = split ys in (y :. a,b))
       )
-- @-node:gcross.20100918210837.1301:join
-- @+node:gcross.20100918210837.1297:length
length :: NaturalNumber n ⇒ TaggedList n α → N n
length _ = asN
-- @nonl
-- @-node:gcross.20100918210837.1297:length
-- @+node:gcross.20100918210837.1304:map
map :: (α → β) → TaggedList n α → TaggedList n β
map f E = E
map f (x :. xs) = f x :. map f xs
-- @-node:gcross.20100918210837.1304:map
-- @+node:gcross.20100918210837.1310:mapM_
mapM_ :: Monad m ⇒ (α → m β) → TaggedList n α → m ()
mapM_ f E = return ()
mapM_ f (x :. xs) = f x >> mapM_ f xs
-- @nonl
-- @-node:gcross.20100918210837.1310:mapM_
-- @+node:gcross.20100918210837.1302:replace
replace :: [α] → TaggedList n β → TaggedList n α
replace [] E = E
replace [] _ = error "There are not enough elements in the list to replace all elements of the tagged list."
replace (x:xs) (_:.ys) = x :. replace xs ys
replace (x:xs) E = error "There are too many elements in the list to replace all elements of the tagged list."
-- @-node:gcross.20100918210837.1302:replace
-- @+node:gcross.20100918210837.1299:tail
tail :: TaggedList (SuccessorTo n) α → TaggedList n α
tail (_ :. xs) = xs
-- @-node:gcross.20100918210837.1299:tail
-- @+node:gcross.20100918210837.1305:toList
toList :: TaggedList n α → [α]
toList E = []
toList (x :. xs) = x : toList xs
-- @-node:gcross.20100918210837.1305:toList
-- @+node:gcross.20100918210837.1303:unwrapRights
unwrapRights :: TaggedList n (Either α β) → Either [α] (TaggedList n β)
unwrapRights E = Right E
unwrapRights (Left x :. rest) =  
    case unwrapRights rest of
        Left xs → Left (x:xs)
        Right _ → Left [x]
unwrapRights (Right x :. rest) =  
    case unwrapRights rest of
        Left es → Left es
        Right xs → Right (x:.xs)
-- @-node:gcross.20100918210837.1303:unwrapRights
-- @+node:gcross.20100928114649.1288:withTL
withTL f = unwrapTL . f . TL
-- @-node:gcross.20100928114649.1288:withTL
-- @+node:gcross.20100918210837.1311:zipf
zipf :: TaggedList n (α → β) → TaggedList n α → TaggedList n β
zipf E E = E
zipf (f :. fs) (x :. xs) = f x :. zipf fs xs
-- @-node:gcross.20100918210837.1311:zipf
-- @-node:gcross.20100918210837.1296:Functions
-- @+node:gcross.20100929163524.1296:Tuple conversions
type family TupleOf n α
type instance TupleOf N0  α = ()
type instance TupleOf N1  α = (α)
type instance TupleOf N2  α = (α,α)
type instance TupleOf N3  α = (α,α,α)
type instance TupleOf N4  α = (α,α,α,α)
type instance TupleOf N5  α = (α,α,α,α,α)
type instance TupleOf N6  α = (α,α,α,α,α,α)
type instance TupleOf N7  α = (α,α,α,α,α,α,α)
type instance TupleOf N8  α = (α,α,α,α,α,α,α,α)
type instance TupleOf N9  α = (α,α,α,α,α,α,α,α,α)
type instance TupleOf N10 α = (α,α,α,α,α,α,α,α,α,α)
type instance TupleOf N11 α = (α,α,α,α,α,α,α,α,α,α,α)
type instance TupleOf N12 α = (α,α,α,α,α,α,α,α,α,α,α,α)
type instance TupleOf N13 α = (α,α,α,α,α,α,α,α,α,α,α,α,α)
type instance TupleOf N14 α = (α,α,α,α,α,α,α,α,α,α,α,α,α,α)
type instance TupleOf N15 α = (α,α,α,α,α,α,α,α,α,α,α,α,α,α,α)

class TupleConvertable n where
    fromT :: TupleOf n α → TaggedList n α
    toT :: TaggedList n α → TupleOf n α

instance TupleConvertable N0 where
    fromT _ = E
    toT _ = ()    
instance TupleConvertable N1 where
    fromT (x1) = x1:.E
    toT (x1:.E) = (x1)
instance TupleConvertable N2 where
    fromT (x1,x2) = x1:.x2:.E
    toT (x1:.x2:.E) = (x1,x2)
instance TupleConvertable N3 where
    fromT (x1,x2,x3) = x1:.x2:.x3:.E
    toT (x1:.x2:.x3:.E) = (x1,x2,x3)
instance TupleConvertable N4 where
    fromT (x1,x2,x3,x4) = x1:.x2:.x3:.x4:.E
    toT (x1:.x2:.x3:.x4:.E) = (x1,x2,x3,x4)
instance TupleConvertable N5 where
    fromT (x1,x2,x3,x4,x5) = x1:.x2:.x3:.x4:.x5:.E
    toT (x1:.x2:.x3:.x4:.x5:.E) = (x1,x2,x3,x4,x5)
instance TupleConvertable N6 where
    fromT (x1,x2,x3,x4,x5,x6) = x1:.x2:.x3:.x4:.x5:.x6:.E
    toT (x1:.x2:.x3:.x4:.x5:.x6:.E) = (x1,x2,x3,x4,x5,x6)
instance TupleConvertable N7 where
    fromT (x1,x2,x3,x4,x5,x6,x7) = x1:.x2:.x3:.x4:.x5:.x6:.x7:.E
    toT (x1:.x2:.x3:.x4:.x5:.x6:.x7:.E) = (x1,x2,x3,x4,x5,x6,x7)
instance TupleConvertable N8 where
    fromT (x1,x2,x3,x4,x5,x6,x7,x8) = x1:.x2:.x3:.x4:.x5:.x6:.x7:.x8:.E
    toT (x1:.x2:.x3:.x4:.x5:.x6:.x7:.x8:.E) = (x1,x2,x3,x4,x5,x6,x7,x8)
instance TupleConvertable N9 where
    fromT (x1,x2,x3,x4,x5,x6,x7,x8,x9) = x1:.x2:.x3:.x4:.x5:.x6:.x7:.x8:.x9:.E
    toT (x1:.x2:.x3:.x4:.x5:.x6:.x7:.x8:.x9:.E) = (x1,x2,x3,x4,x5,x6,x7,x8,x9)
instance TupleConvertable N10 where
    fromT (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10) = x1:.x2:.x3:.x4:.x5:.x6:.x7:.x8:.x9:.x10:.E
    toT (x1:.x2:.x3:.x4:.x5:.x6:.x7:.x8:.x9:.x10:.E) = (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10)
instance TupleConvertable N11 where
    fromT (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11) = x1:.x2:.x3:.x4:.x5:.x6:.x7:.x8:.x9:.x10:.x11:.E
    toT (x1:.x2:.x3:.x4:.x5:.x6:.x7:.x8:.x9:.x10:.x11:.E) = (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11)
instance TupleConvertable N12 where
    fromT (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12) = x1:.x2:.x3:.x4:.x5:.x6:.x7:.x8:.x9:.x10:.x11:.x12:.E
    toT (x1:.x2:.x3:.x4:.x5:.x6:.x7:.x8:.x9:.x10:.x11:.x12:.E) = (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12)
instance TupleConvertable N13 where
    fromT (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13) = x1:.x2:.x3:.x4:.x5:.x6:.x7:.x8:.x9:.x10:.x11:.x12:.x13:.E
    toT (x1:.x2:.x3:.x4:.x5:.x6:.x7:.x8:.x9:.x10:.x11:.x12:.x13:.E) = (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13)
instance TupleConvertable N14 where
    fromT (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14) = x1:.x2:.x3:.x4:.x5:.x6:.x7:.x8:.x9:.x10:.x11:.x12:.x13:.x14:.E
    toT (x1:.x2:.x3:.x4:.x5:.x6:.x7:.x8:.x9:.x10:.x11:.x12:.x13:.x14:.E) = (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14)
instance TupleConvertable N15 where
    fromT (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15) = x1:.x2:.x3:.x4:.x5:.x6:.x7:.x8:.x9:.x10:.x11:.x12:.x13:.x14:.x15:.E
    toT (x1:.x2:.x3:.x4:.x5:.x6:.x7:.x8:.x9:.x10:.x11:.x12:.x13:.x14:.x15:.E) = (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15)
-- @nonl
-- @-node:gcross.20100929163524.1296:Tuple conversions
-- @-others
-- @-node:gcross.20100917213812.1278:@thin Data/List/Tagged.hs
-- @-leo
