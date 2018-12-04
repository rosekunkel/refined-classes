{-@ LIQUID "--reflection" @-}

-- Problems:
--   - Can't reflect a function-valued projection at all
--   - Reflecting projection isn't enough

module VerifiedSemigroup where

data VSemigroup a = VSemigroup (a -> a -> a) (a -> a -> a -> ())

{-@ reflect vsappend @-}
vsappend :: VSemigroup a -> a -> a -> a
vsappend (VSemigroup f _) = f

{-@ reflect vsappendAssoc @-}
vsappendAssoc :: VSemigroup a -> a -> a -> a -> ()
vsappendAssoc (VSemigroup _ f) = f

{-@ reflect list_VSemigroup @-}
list_VSemigroup :: VSemigroup [a]
list_VSemigroup = VSemigroup list_vsappend list_vsappendAssoc

{-@ reflect list_vsappend @-}
list_vsappend :: [a] -> [a] -> [a]
list_vsappend [] ys = ys
list_vsappend (x:xs) ys = x:vsappend list_VSemigroup xs ys

{-@ list_vsappendAssoc :: x:[a] -> y:[a] -> z:[a] -> {vsappend list_VSemigroup x (vsappend list_VSemigroup y z) == vsappend list_VSemigroup (vsappend list_VSemigroup x y) z} @-}
{-@ ple list_vsappendAssoc @-}
list_vsappendAssoc :: [a] -> [a] -> [a] -> ()
list_vsappendAssoc [] _ _ = ()
list_vsappendAssoc (x:xs) ys zs = vsappendAssoc list_VSemigroup xs ys zs

{-@ foo :: xs:[a] -> ys:[a] -> {vsappend list_VSemigroup xs (vsappend list_VSemigroup ys []) == vsappend list_VSemigroup (vsappend list_VSemigroup xs ys) []} @-}
foo :: [a] -> [a] -> ()
foo xs ys = vsappendAssoc list_VSemigroup xs ys []
