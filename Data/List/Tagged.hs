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

module Data.List.Tagged (
    -- * Tagged lists
    TaggedList(..),
    UntaggedList(..),
    TL(..),
    ATL(..),
    -- * Utility functions
    append,
    eqLists,
    extractRightsOrLefts,
    fromList,
    fromListAsUntagged,
    head,
    join,
    length,
    map,
    mapM_,
    replace,
    tail,
    toList,
    withTL,
    zipf,
    -- * Tuple conversion
    TupleOf(..),
    TupleConvertable(..),
) where

-- @<< Import needed modules >>
-- @+node:gcross.20100918210837.1286:<< Import needed modules >>
import Prelude
            (Bool(..)
            ,Either(..)
            ,Eq(..)
            ,Functor
            ,Monad(..)
            ,const
            ,error
            ,fmap
            ,id
            ,otherwise
            ,snd
            ,undefined
            ,($)
            ,(.)
            ,(&&)
            )

import Control.Applicative (Applicative,liftA2,pure)
import Control.Monad.Trans.Abort (Abort,abort,runAbort)

import Data.Binary (Binary,get,put)
import Data.Foldable (Foldable,foldMap)
import Data.Monoid (Monoid,mappend,mempty)
import Data.Traversable (Traversable,traverse)
import Data.Typeable (Typeable)

import TypeLevel.NaturalNumber
            (N0,N1,N2,N3,N4,N5,N6,N7,N8,N9,N10,N11,N12,N13,N14,N15
            ,Zero
            ,SuccessorTo
            )
import TypeLevel.NaturalNumber.Induction (Induction(deduction2M),induction,deduction,transform)
import TypeLevel.NaturalNumber.Operations (Plus)

import Data.NaturalNumber (NaturalNumber,N,asN)
-- @-node:gcross.20100918210837.1286:<< Import needed modules >>
-- @nl

-- @+others
-- @+node:gcross.20100918210837.1287:Types
-- @+node:gcross.20100928114649.1285:TL
-- | 'TL' is a newtype wrapper around a 'TaggedList' which flips the two type arguments;  this type was introduced to make it easier to define inductive operations on TaggedLists.
newtype TL α n = TL { unwrapTL :: TaggedList n α }
-- @-node:gcross.20100928114649.1285:TL
-- @+node:gcross.20100928151321.1296:ATL
-- | 'ATL' is a newtype wrapper around some functor of 'TaggedList' which flips the two type arguments;  this type was introduced to make it easier to define inductive operations on functors of TaggedLists.
newtype ATL t α n = ATL { unwrapATL :: t (TaggedList n α) }
-- @-node:gcross.20100928151321.1296:ATL
-- @+node:gcross.20100918210837.1288:TaggedList
-- | 'TaggedList' is a data structure that represents a linked-list tagged with a phantom type-level natural number representing the length of the list.
data TaggedList n α where
    E :: TaggedList Zero α
    (:.) :: α → TaggedList n α → TaggedList (SuccessorTo n) α
  deriving Typeable

infixr :.
-- @-node:gcross.20100918210837.1288:TaggedList
-- @+node:gcross.20100918210837.1289:UntaggedList
-- | 'UntaggedList' is a wrapper around TaggedList that lets you hide the length tag;  the purpose of this is to allow for situations in which you have a tagged list with an unknown length.
data UntaggedList α = ∀ n. NaturalNumber n ⇒ UntaggedList (TaggedList n α) deriving Typeable
-- @-node:gcross.20100918210837.1289:UntaggedList
-- @-node:gcross.20100918210837.1287:Types
-- @+node:gcross.20100918210837.1290:Instances
-- @+node:gcross.20100918210837.1291:Binary TaggedList
instance (Induction n, Binary α) ⇒ Binary (TaggedList n α) where
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
instance (Induction n, Eq α) ⇒ Eq (TaggedList n α) where
    x == y = runAbort (deduction2M () (\_ _ _ → return True) step (TL x) (TL y))
      where
        step ::
            forall n α.
            Eq α ⇒
            TL α (SuccessorTo n) →
            TL α (SuccessorTo n) →
            () →
            Abort Bool (TL α n,TL α n,())
        step (TL (x :. xs)) (TL (y :. ys)) b
          | x /= y    = abort False
          | otherwise = return (TL xs,TL ys,())
-- @nonl
-- @-node:gcross.20100918210837.1295:Eq TaggedList
-- @+node:gcross.20100918210837.1294:Foldable TaggedList
instance Induction n ⇒ Foldable (TaggedList n) where
    foldMap f l = deduction mempty (const id) (step f) (TL l)
      where
        step ::
            forall α n m.
            Monoid m ⇒
            (α → m) →
            TL α (SuccessorTo n) →
            m →
            (TL α n,m)
        step f (TL (x :. xs)) a = (TL xs,a `mappend` f x)
-- @nonl
-- @-node:gcross.20100918210837.1294:Foldable TaggedList
-- @+node:gcross.20100918210837.1293:Functor TaggedList
instance Induction n ⇒ Functor (TaggedList n) where
    fmap f = withTL (transform (const (TL E)) (step f))
      where
        step :: ∀ α β n. (α → β) → (TL α n → TL β n) → TL α (SuccessorTo n) → TL β (SuccessorTo n) 
        step f recurse (TL (x :. xs)) = TL (f x :. withTL recurse xs)
-- @nonl
-- @-node:gcross.20100918210837.1293:Functor TaggedList
-- @+node:gcross.20100928151321.1295:Traversable TaggedList
instance Induction n ⇒ Traversable (TaggedList n) where
    traverse f = unwrapATL . transform (const . ATL . pure $ E) (step f) . TL
      where
        step :: ∀ α β t n. Applicative t ⇒ (α → t β) → (TL α n → ATL t β n) → TL α (SuccessorTo n) → ATL t β (SuccessorTo n) 
        step f recurse (TL (x :. xs)) = ATL (liftA2 (:.) (f x) (unwrapATL . recurse . TL $ xs))
-- @-node:gcross.20100928151321.1295:Traversable TaggedList
-- @-node:gcross.20100918210837.1290:Instances
-- @+node:gcross.20100918210837.1296:Functions
-- @+node:gcross.20100918210837.1300:append
-- | Appends two tagged lists.
--
-- (Note: The order of the arguments to Plus is important since append is defined recursively over its *first* argument.)
append :: TaggedList m α → TaggedList n α → TaggedList (Plus m n) α
append E = id
append (x :. xs) = (x :.) . append xs
-- @-node:gcross.20100918210837.1300:append
-- @+node:gcross.20100918210837.1308:eqLists
-- | Compares two lists, which may be of different sizes;  'False' is returned if the lists do not have the same size.
eqLists :: Eq α ⇒ TaggedList m α → TaggedList n α → Bool
eqLists E E = True
eqLists E _ = False
eqLists _ E = False
eqLists (x:.xs) (y:.ys) = (x == y) && eqLists xs ys
-- @nonl
-- @-node:gcross.20100918210837.1308:eqLists
-- @+node:gcross.20100918210837.1303:extractRightsOrLefts
-- | If the input list of 'Either' values has only 'Rights', then this function returns a tagged list of the same length with the values contained in each 'Right'.  Otherwise, this function returns an ordinary list with the values contained in each 'Left'.
extractRightsOrLefts :: TaggedList n (Either α β) → Either [α] (TaggedList n β)
extractRightsOrLefts E = Right E
extractRightsOrLefts (Left x :. rest) =  
    case extractRightsOrLefts rest of
        Left xs → Left (x:xs)
        Right _ → Left [x]
extractRightsOrLefts (Right x :. rest) =  
    case extractRightsOrLefts rest of
        Left es → Left es
        Right xs → Right (x:.xs)
-- @-node:gcross.20100918210837.1303:extractRightsOrLefts
-- @+node:gcross.20100928114649.1287:fromList
-- | Converts a list to a 'TaggedList', returning _|_ if the length of the list does not match the length tag of the return type.
fromList :: Induction n ⇒ [α] → TaggedList n α
fromList = unwrapTL . snd . induction z i
  where
    z [] = (undefined,TL E)
    z _ = error "List is too long to convert into a tagged list of the given length."
    i (x:xs) (TL l) = (xs,TL (x :. l))
    i [] _ = error "List is too short to convert into a tagged list of the given length."
-- @nonl
-- @-node:gcross.20100928114649.1287:fromList
-- @+node:gcross.20100918210837.1306:fromListAsUntagged
-- | Converts an arbitrary list to an 'UntaggedList'.
fromListAsUntagged :: [α] → UntaggedList α
fromListAsUntagged [] = UntaggedList E
fromListAsUntagged (x:rest) =
    case fromListAsUntagged rest of
        UntaggedList xs → UntaggedList (x :. xs)
-- @-node:gcross.20100918210837.1306:fromListAsUntagged
-- @+node:gcross.20100918210837.1298:head
-- | Returns the head of a tagged list.
--
-- Note that unlike its List counterpart, this function never returns _|_ since the existence of at least one element is guaranteed by the type system.
head :: TaggedList (SuccessorTo n) α → α
head (x :. _) = x
-- @-node:gcross.20100918210837.1298:head
-- @+node:gcross.20100918210837.1301:join
-- | Appends two lists together, and returns both the result and a splitter function that allows you to take another list of the same size as the result (though possible of a different type) and split it back into two lists of the sizes of the arguments to this function.
join :: TaggedList m α → TaggedList n α → (TaggedList (Plus m n) α,TaggedList (Plus m n) β → (TaggedList m β,TaggedList n β))
join E v = (v,\z → (E,z))
join (x :. xs) v =
    let (vv,split) = join xs v 
    in (x :. vv
       ,(\(y :. ys) → let (a,b) = split ys in (y :. a,b))
       )
-- @-node:gcross.20100918210837.1301:join
-- @+node:gcross.20100918210837.1297:length
-- | Returns the length of the list as a value-level natural number.
length :: NaturalNumber n ⇒ TaggedList n α → N n
length _ = asN
-- @nonl
-- @-node:gcross.20100918210837.1297:length
-- @+node:gcross.20100918210837.1304:map
-- | Applies a function to every element of the list.
map :: (α → β) → TaggedList n α → TaggedList n β
map f E = E
map f (x :. xs) = f x :. map f xs
-- @-node:gcross.20100918210837.1304:map
-- @+node:gcross.20100918210837.1310:mapM_
-- | Performs an action for every element in the list and returns ().
mapM_ :: Monad m ⇒ (α → m β) → TaggedList n α → m ()
mapM_ f E = return ()
mapM_ f (x :. xs) = f x >> mapM_ f xs
-- @nonl
-- @-node:gcross.20100918210837.1310:mapM_
-- @+node:gcross.20100918210837.1302:replace
-- | Replaces all of the elements in a given tagged list with the members of an ordinary list, returning _|_ if the length of the list does not match the length tag.
replace :: [α] → TaggedList n β → TaggedList n α
replace [] E = E
replace [] _ = error "There are not enough elements in the list to replace all elements of the tagged list."
replace (x:xs) (_:.ys) = x :. replace xs ys
replace (x:xs) E = error "There are too many elements in the list to replace all elements of the tagged list."
-- @-node:gcross.20100918210837.1302:replace
-- @+node:gcross.20100918210837.1299:tail
-- | Returns the tail of a tagged list.
--
-- Note that unlike its List counterpart, this function never returns _|_ since the existence of at least one element is guaranteed by the type system.
tail :: TaggedList (SuccessorTo n) α → TaggedList n α
tail (_ :. xs) = xs
-- @-node:gcross.20100918210837.1299:tail
-- @+node:gcross.20100918210837.1305:toList
-- | Converts a tagged list to an ordinary list.
toList :: TaggedList n α → [α]
toList E = []
toList (x :. xs) = x : toList xs
-- @-node:gcross.20100918210837.1305:toList
-- @+node:gcross.20100928114649.1288:withTL
-- | This is a convenience function for lifting a function on 'TL' to a function on 'TaggedList'.
--
-- (Note:  'TL' is just a newtype wrapper around 'TaggedList' that swaps the two type arguments to make it easier to perform inductive operations.)
withTL :: (TL α n → TL β n) → TaggedList n α → TaggedList n β
withTL f = unwrapTL . f . TL
-- @-node:gcross.20100928114649.1288:withTL
-- @+node:gcross.20100918210837.1311:zipf
-- | Applies a list of functions to a list of inputs.
zipf :: TaggedList n (α → β) → TaggedList n α → TaggedList n β
zipf E E = E
zipf (f :. fs) (x :. xs) = f x :. zipf fs xs
-- @-node:gcross.20100918210837.1311:zipf
-- @-node:gcross.20100918210837.1296:Functions
-- @+node:gcross.20100929163524.1296:Tuple conversions
-- | TupleOf is a type family that maps type-level natural numbers (from N0 to N15) to tuples with the corresponding number of entries.
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

-- | The class TupleConvertable provides methods for converting tagged lists to and from tuples.
class TupleConvertable n where
    fromTuple :: TupleOf n α → TaggedList n α
    toTuple :: TaggedList n α → TupleOf n α

instance TupleConvertable N0 where
    fromTuple _ = E
    toTuple _ = ()
instance TupleConvertable N1 where
    fromTuple (x1) = x1:.E
    toTuple (x1:.E) = (x1)
instance TupleConvertable N2 where
    fromTuple (x1,x2) = x1:.x2:.E
    toTuple (x1:.x2:.E) = (x1,x2)
instance TupleConvertable N3 where
    fromTuple (x1,x2,x3) = x1:.x2:.x3:.E
    toTuple (x1:.x2:.x3:.E) = (x1,x2,x3)
instance TupleConvertable N4 where
    fromTuple (x1,x2,x3,x4) = x1:.x2:.x3:.x4:.E
    toTuple (x1:.x2:.x3:.x4:.E) = (x1,x2,x3,x4)
instance TupleConvertable N5 where
    fromTuple (x1,x2,x3,x4,x5) = x1:.x2:.x3:.x4:.x5:.E
    toTuple (x1:.x2:.x3:.x4:.x5:.E) = (x1,x2,x3,x4,x5)
instance TupleConvertable N6 where
    fromTuple (x1,x2,x3,x4,x5,x6) = x1:.x2:.x3:.x4:.x5:.x6:.E
    toTuple (x1:.x2:.x3:.x4:.x5:.x6:.E) = (x1,x2,x3,x4,x5,x6)
instance TupleConvertable N7 where
    fromTuple (x1,x2,x3,x4,x5,x6,x7) = x1:.x2:.x3:.x4:.x5:.x6:.x7:.E
    toTuple (x1:.x2:.x3:.x4:.x5:.x6:.x7:.E) = (x1,x2,x3,x4,x5,x6,x7)
instance TupleConvertable N8 where
    fromTuple (x1,x2,x3,x4,x5,x6,x7,x8) = x1:.x2:.x3:.x4:.x5:.x6:.x7:.x8:.E
    toTuple (x1:.x2:.x3:.x4:.x5:.x6:.x7:.x8:.E) = (x1,x2,x3,x4,x5,x6,x7,x8)
instance TupleConvertable N9 where
    fromTuple (x1,x2,x3,x4,x5,x6,x7,x8,x9) = x1:.x2:.x3:.x4:.x5:.x6:.x7:.x8:.x9:.E
    toTuple (x1:.x2:.x3:.x4:.x5:.x6:.x7:.x8:.x9:.E) = (x1,x2,x3,x4,x5,x6,x7,x8,x9)
instance TupleConvertable N10 where
    fromTuple (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10) = x1:.x2:.x3:.x4:.x5:.x6:.x7:.x8:.x9:.x10:.E
    toTuple (x1:.x2:.x3:.x4:.x5:.x6:.x7:.x8:.x9:.x10:.E) = (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10)
instance TupleConvertable N11 where
    fromTuple (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11) = x1:.x2:.x3:.x4:.x5:.x6:.x7:.x8:.x9:.x10:.x11:.E
    toTuple (x1:.x2:.x3:.x4:.x5:.x6:.x7:.x8:.x9:.x10:.x11:.E) = (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11)
instance TupleConvertable N12 where
    fromTuple (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12) = x1:.x2:.x3:.x4:.x5:.x6:.x7:.x8:.x9:.x10:.x11:.x12:.E
    toTuple (x1:.x2:.x3:.x4:.x5:.x6:.x7:.x8:.x9:.x10:.x11:.x12:.E) = (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12)
instance TupleConvertable N13 where
    fromTuple (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13) = x1:.x2:.x3:.x4:.x5:.x6:.x7:.x8:.x9:.x10:.x11:.x12:.x13:.E
    toTuple (x1:.x2:.x3:.x4:.x5:.x6:.x7:.x8:.x9:.x10:.x11:.x12:.x13:.E) = (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13)
instance TupleConvertable N14 where
    fromTuple (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14) = x1:.x2:.x3:.x4:.x5:.x6:.x7:.x8:.x9:.x10:.x11:.x12:.x13:.x14:.E
    toTuple (x1:.x2:.x3:.x4:.x5:.x6:.x7:.x8:.x9:.x10:.x11:.x12:.x13:.x14:.E) = (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14)
instance TupleConvertable N15 where
    fromTuple (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15) = x1:.x2:.x3:.x4:.x5:.x6:.x7:.x8:.x9:.x10:.x11:.x12:.x13:.x14:.x15:.E
    toTuple (x1:.x2:.x3:.x4:.x5:.x6:.x7:.x8:.x9:.x10:.x11:.x12:.x13:.x14:.x15:.E) = (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15)
-- @nonl
-- @-node:gcross.20100929163524.1296:Tuple conversions
-- @-others
-- @-node:gcross.20100917213812.1278:@thin Data/List/Tagged.hs
-- @-leo
