{-# LANGUAGE TypeSynonymInstances #-}
module ListSemigroup where

{-@ type NonEmptyList a = {l:[a] | len l > 0} @-}
type NonEmptyList a = [a]

class MySemigroup a where
  myMappend :: a -> a -> a

-- We want to be able to write something like this:
-- {-@ instance MySemigroup (NonEmptyList a) @-}
instance MySemigroup (NonEmptyList a) where
  myMappend = (++)

{-@ mySconcat :: MySemigroup a => NonEmptyList a -> a @-}
mySconcat :: MySemigroup a => NonEmptyList a -> a
mySconcat [x] = x
mySconcat (x:xs) = x `myMappend` mySconcat xs

-- This is currently rejected by Liquid Haskell. We would like it to
-- be accepted.
{-@ myFlatten :: NonEmptyList (NonEmptyList a) -> NonEmptyList a @-}
myFlatten :: NonEmptyList (NonEmptyList a) -> NonEmptyList a
myFlatten = mySconcat

-- This is accepted, despite being the same as the above function.
{-@ myFlatten' :: NonEmptyList (NonEmptyList a) -> NonEmptyList a @-}
myFlatten' :: NonEmptyList (NonEmptyList a) -> NonEmptyList a
myFlatten' [x] = x
myFlatten' (x:xs) = x ++ myFlatten' xs
