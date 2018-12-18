module Ordinals where

-- Will this be in the generated code? Probably not?
data NumD a = NumD
  { (+) :: a -> a -> a
  , (-) :: a -> a -> a
  , (*) :: a -> a -> a
  , negate :: a -> a
  , abs :: a -> a
  , signum :: a -> a -> a
  , fromInteger :: Integer -> a
  }

{-@ numOrdinal :: NumD NFOrd @-}
numOrdinal :: NumD Ordinal
numOrdinal = NumD add' ?? ?? ?? ??

{-@ add' :: NFOrd -> NFOrd -> NFOrd @-}
add' :: Ordinal -> Ordinal -> Ordinal
add' = ??

-- This is doubly complicated by the fact that (-) is a partial
-- function on ordinals.
{-@ negate :: NFOrd -> NFOrd @-}
negate x = (fromInteger 0) - x
