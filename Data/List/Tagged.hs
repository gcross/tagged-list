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
{-# LANGUAGE UnicodeSyntax #-}
-- @-node:gcross.20100918210837.1285:<< Language extensions >>
-- @nl

module Data.List.Tagged where

-- @<< Import needed modules >>
-- @+node:gcross.20100918210837.1286:<< Import needed modules >>
import Prelude hiding (tail,foldl,foldr,map,mapM,mapM_,length)

import Control.Monad.Trans.Abort

import Data.Binary
import Data.Foldable hiding (toList,mapM_)
import Data.Monoid
import Data.Typeable

import TypeLevel.NaturalNumber hiding (NaturalNumber)
import TypeLevel.NaturalNumber.Induction
import TypeLevel.NaturalNumber.Operations

import Data.NaturalNumber
-- @-node:gcross.20100918210837.1286:<< Import needed modules >>
-- @nl

-- @+others
-- @+node:gcross.20100918210837.1287:Types
-- @+node:gcross.20100928114649.1285:FlipTaggedList
newtype TL α n = TL { unwrapTL :: TaggedList n α }
-- @-node:gcross.20100928114649.1285:FlipTaggedList
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
-- @+node:gcross.20100918210837.1309:mapM
mapM :: Monad m ⇒ (α → m β) → TaggedList n α → m (TaggedList n β)
mapM f E = return E
mapM f (x :. xs) = do
    y ← f x
    ys ← mapM f xs
    return (y :. ys)
-- @nonl
-- @-node:gcross.20100918210837.1309:mapM
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
-- @-others
-- @-node:gcross.20100917213812.1278:@thin Data/List/Tagged.hs
-- @-leo
