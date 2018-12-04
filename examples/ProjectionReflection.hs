{-@ LIQUID "--reflection" @-}

module ProjectionReflection where

{-@ reflect projL @-}
projL :: (Int, Int) -> Int
projL (x, _) = x

{-@ reflect zeroOne @-}
zeroOne :: (Int, Int)
zeroOne = (0, 1)

{-@ foo :: {v:Int | v == 0} @-}
foo :: Int
foo = projL zeroOne
