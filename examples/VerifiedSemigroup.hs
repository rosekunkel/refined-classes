module VerifiedSemigroup where

class VSemigroup a where
  {-@ reflect vsappend @-}
  vsappend :: a -> a -> a
  {-@ vsappendAssoc :: x:a -> y:a -> z:a -> {vsappend x (vsappend y z) == vsappend (vsappend x y) z} @-}
  vsappendAssoc :: a -> a -> a -> ()

instance VSemigroup [a] where
  vsappend [] ys = ys
  vsappend (x:xs) ys = x:vsappend xs ys

  {-@ ple vsappendAssoc @-}
  vsappendAssoc [] _ _ = ()
  vsappendAssoc (x:xs) ys zs = vsappendAssoc xs ys zs

{-@ foo :: xs:[a] -> ys:[a] -> {vsappend xs (vsappend ys []) == vsappend (vsappend xs ys) []} @-}
foo :: [a] -> [a] -> ()
foo xs ys = vsappendAssoc xs ys []
