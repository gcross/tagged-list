-- @+leo-ver=4-thin
-- @+node:gcross.20100918210837.1284:@thin Data/List/Tagged.hs
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
newtype TL a n = TL { unwrapTL :: TaggedList n a }
-- @-node:gcross.20100928114649.1285:FlipTaggedList
-- @+node:gcross.20100918210837.1288:TaggedList
data TaggedList n a where
    E :: TaggedList Zero a
    (:.) :: a → TaggedList n a → TaggedList (SuccessorTo n) a
  deriving Typeable

infixr :.
-- @-node:gcross.20100918210837.1288:TaggedList
-- @+node:gcross.20100918210837.1289:UntaggedList
data UntaggedList a = ∀ n. UntaggedList (TaggedList n a) deriving Typeable
-- @-node:gcross.20100918210837.1289:UntaggedList
-- @-node:gcross.20100918210837.1287:Types
-- @+node:gcross.20100918210837.1290:Instances
-- @+node:gcross.20100918210837.1291:Binary TaggedList
instance (NaturalNumber n, Binary a) => Binary (TaggedList n a) where
    get = fmap fromList get
    put = put . toList
-- @-node:gcross.20100918210837.1291:Binary TaggedList
-- @+node:gcross.20100918210837.1292:Binary UntaggedList
instance Binary a => Binary (UntaggedList a) where
    get = fmap fromListAsUntagged get
    put (UntaggedList l) = put (toList l)
-- @-node:gcross.20100918210837.1292:Binary UntaggedList
-- @+node:gcross.20100918210837.1295:Eq TaggedList
instance (NaturalNumber n, Eq a) => Eq (TaggedList n a) where
    x == y = runAbort (deduction2M () (\_ _ _ → return True) step (TL x) (TL y))
      where
        step :: Eq a => TL a (SuccessorTo n) → TL a (SuccessorTo n) → () → Abort Bool (TL a n,TL a n,())
        step (TL (x :. xs)) (TL (y :. ys)) b
          | x /= y    = abort False
          | otherwise = return (TL xs,TL ys,())
-- @-node:gcross.20100918210837.1295:Eq TaggedList
-- @+node:gcross.20100918210837.1294:Foldable TaggedList
instance NaturalNumber n => Foldable (TaggedList n) where
    foldMap f l = deduction mempty (const id) (step f) (TL l)
      where
        step :: Monoid m ⇒ (α → m) → TL α (SuccessorTo n) → m -> (TL α n,m)
        step f (TL (x :. xs)) a = (TL xs,a `mappend` f x)
-- @-node:gcross.20100918210837.1294:Foldable TaggedList
-- @+node:gcross.20100918210837.1293:Functor TaggedList
instance NaturalNumber n => Functor (TaggedList n) where
    fmap f = withTL (transform (const (TL E)) (step f))
      where
        step :: ∀ α β n. (α → β) → (TL α n → TL β n) → TL α (SuccessorTo n) → TL β (SuccessorTo n) 
        step f recurse (TL (x :. xs)) = TL (f x :. withTL recurse xs)
-- @-node:gcross.20100918210837.1293:Functor TaggedList
-- @-node:gcross.20100918210837.1290:Instances
-- @+node:gcross.20100918210837.1296:Functions
-- @+node:gcross.20100918210837.1300:append
append :: TaggedList m a → TaggedList n a → TaggedList (Plus m n) a
append E = id
append (x :. xs) = (x :.) . append xs
-- @-node:gcross.20100918210837.1300:append
-- @+node:gcross.20100918210837.1308:eqLists
eqLists :: Eq a => TaggedList m a → TaggedList n a → Bool
eqLists E E = True
eqLists E _ = False
eqLists _ E = False
eqLists (x:.xs) (y:.ys) = (x == y) && eqLists xs ys
-- @-node:gcross.20100918210837.1308:eqLists
-- @+node:gcross.20100928114649.1287:fromList
fromList :: NaturalNumber n => [a] → TaggedList n a
fromList = unwrapTL . snd . induction z i
  where
    z [] = (undefined,TL E)
    z _ = error "List is too long to convert into a tagged list of the given length."
    i (x:xs) (TL l) = (xs,TL (x :. l))
    i [] _ = error "List is too short to convert into a tagged list of the given length."
-- @-node:gcross.20100928114649.1287:fromList
-- @+node:gcross.20100918210837.1306:fromListAsUntagged
fromListAsUntagged :: [a] → UntaggedList a
fromListAsUntagged [] = UntaggedList E
fromListAsUntagged (x:rest) =
    case fromListAsUntagged rest of
        UntaggedList xs → UntaggedList (x :. xs)
-- @-node:gcross.20100918210837.1306:fromListAsUntagged
-- @+node:gcross.20100918210837.1298:head
head :: TaggedList (SuccessorTo n) a → a
head (x :. _) = x
-- @-node:gcross.20100918210837.1298:head
-- @+node:gcross.20100918210837.1301:join
join :: TaggedList m a → TaggedList n a → (TaggedList (Plus m n) a,TaggedList (Plus m n) b → (TaggedList m b,TaggedList n b))
join E v = (v,\z → (E,z))
join (x :. xs) v =
    let (vv,split) = join xs v 
    in (x :. vv
       ,(\(y :. ys) → let (a,b) = split ys in (y :. a,b))
       )
-- @-node:gcross.20100918210837.1301:join
-- @+node:gcross.20100918210837.1297:length
length :: NaturalNumber n => TaggedList n a → N n
length _ = asN
-- @-node:gcross.20100918210837.1297:length
-- @+node:gcross.20100918210837.1304:map
map :: (a → b) → TaggedList n a → TaggedList n b
map f E = E
map f (x :. xs) = f x :. map f xs
-- @-node:gcross.20100918210837.1304:map
-- @+node:gcross.20100918210837.1309:mapM
mapM :: Monad m => (a → m b) → TaggedList n a → m (TaggedList n b)
mapM f E = return E
mapM f (x :. xs) = do
    y ← f x
    ys ← mapM f xs
    return (y :. ys)
-- @-node:gcross.20100918210837.1309:mapM
-- @+node:gcross.20100918210837.1310:mapM_
mapM_ :: Monad m => (a → m b) → TaggedList n a → m ()
mapM_ f E = return ()
mapM_ f (x :. xs) = f x >> mapM_ f xs
-- @-node:gcross.20100918210837.1310:mapM_
-- @+node:gcross.20100918210837.1302:replace
replace :: [a] → TaggedList n b → TaggedList n a
replace [] E = E
replace [] _ = error "There are not enough elements in the list to replace all elements of the tagged list."
replace (x:xs) (_:.ys) = x :. replace xs ys
replace (x:xs) E = error "There are too many elements in the list to replace all elements of the tagged list."
-- @-node:gcross.20100918210837.1302:replace
-- @+node:gcross.20100918210837.1299:tail
tail :: TaggedList (SuccessorTo n) a → TaggedList n a
tail (_ :. xs) = xs
-- @-node:gcross.20100918210837.1299:tail
-- @+node:gcross.20100918210837.1305:toList
toList :: TaggedList n a → [a]
toList E = []
toList (x :. xs) = x : toList xs
-- @-node:gcross.20100918210837.1305:toList
-- @+node:gcross.20100918210837.1303:unwrapRights
unwrapRights :: TaggedList n (Either a b) → Either [a] (TaggedList n b)
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
zipf :: TaggedList n (a → b) → TaggedList n a → TaggedList n b
zipf E E = E
zipf (f :. fs) (x :. xs) = f x :. zipf fs xs
-- @-node:gcross.20100918210837.1311:zipf
-- @-node:gcross.20100918210837.1296:Functions
-- @-others
-- @-node:gcross.20100918210837.1284:@thin Data/List/Tagged.hs
-- @-leo
