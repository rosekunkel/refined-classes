-- From Alexander Varga
{-@ LIQUID "--reflection" @-}

module Ordinals where

import NewProofCombinators

-- Num typeclass definition from Preulude:
--
-- class Num a where
--   (+) :: a -> a -> a
--   (-) :: a -> a -> a
--   (*) :: a -> a -> a
--   negate :: a -> a
--   abs :: a -> a
--   signum :: a -> a -> a
--   fromInteger :: Integer -> a
--
-- We need to be able to deal with default implementations:
--   x - y = x + negate y
--   negate x = 0 - x

-- Ord typeclass definition from Prelude:
--
-- class Eq a => Ord a where
--   compare :: a -> a -> Ordering
--   (<) :: a -> a -> Bool
--   (<=) :: a -> a -> Bool
--   (>) :: a -> a -> Bool
--   (>=) :: a -> a -> Bool
--   max :: a -> a -> a
--   min :: a -> a -> a
--
--   Ord should have a bunch of default implementations, but it seems to be
--   magic/compiler-internal? I can't find the source for Ord.


-- Can we refer to *, +, etc in refinement types?
class Num a => VerifiedNum a where
  -- Should we be allowed to reflect here? Probably not, but we do need a way to
  -- reflect standard lib functions.
  {-@ reflect abs, signum, (*) @-}

  -- This is the only law that the Num documentation includes.
  {-@ absSignumDecompose :: x:a -> {abs x * signum x == x} @-}
  absSignumDecompose :: a -> Proof

----------------------------------------------------------------

-- This definition is definitely missing some omegas in it:
-- (Ord a n b) = a^n + b
-- require Cantor Normal Form and use the measure "size" to check termination
-- see: https://en.wikipedia.org/wiki/Ordinal_arithmetic#Cantor_normal_form
{-@ data Ordinal [size] @-}
data Ordinal = Ord Ordinal Int Ordinal
             | Zero
             -- How does deriving work with this translation? Hopefully it "just
             -- works".
             deriving (Eq)

{-@ measure size @-}
{-@ size :: Ordinal -> Nat @-}
size :: Ordinal -> Int
size Zero = 0
size (Ord a n b) = 1 + (size a) + n*n + (size b)

{-@ type NFOrd = {v:Ordinal | normal v} @-}

{-@ reflect normal @-}
normal :: Ordinal -> Bool
normal Zero = True
normal (Ord a n b) = (normal a) && (n > 0) && (normal b) && (case b of
    Zero -> True
    (Ord c _ _) -> (comp c a == LT))

-- Declaring an instance for a refined type.
{-@ instance Ord NFOrd where compare :: NFOrd -> NFOrd -> Ordering @-}
instance Ord Ordinal where compare = comp

-- We should probably allow this to just be
-- {-@ instance num NFOrd @-}
{-@ 
instance Num NFOrd where 
    (+) :: NFOrd -> NFOrd -> NFOrd
    (-) :: NFOrd -> NFOrd -> NFOrd
    (*) :: NFOrd -> NFOrd -> NFOrd
    abs :: NFOrd -> NFOrd
    signum :: NFOrd -> NFOrd
    fromInteger :: Integer -> NFOrd
@-}
instance Num Ordinal where
    -- Not sure why this is defined for the primed versions (without proofs attached).
    (+) = add'
    (-) = sub'
    (*) = mul'
    abs = id
    signum = const one
    fromInteger = n2o' . abs' . fromIntegral

instance VerifiedNum Ordinal where
  absSignumDecompose x =
    -- A proof goes here, it should be easy

---- INSTANCE ORD ----

{-@ reflect compInt @-}
compInt :: Int -> Int -> Ordering
compInt x y = if x < y then LT else if x == y then EQ else GT

{-@ reflect comp @-}
comp :: Ordinal -> Ordinal -> Ordering
comp Zero Zero = EQ
comp Zero (Ord a n b) = LT
comp (Ord a n b) Zero = GT
comp (Ord a0 n0 b0) (Ord a1 n1 b1) =
    case (a0 `comp` a1) of
        LT -> LT
        GT -> GT
        EQ -> case (n0 `compInt` n1) of
            LT -> LT
            GT -> GT
            EQ -> (b0 `comp` b1)

{-@ reflect maxOrd @-}
maxOrd :: Ordinal -> Ordinal -> Ordinal
maxOrd a b = case (a `comp` b) of
    LT -> b
    GT -> a
    EQ -> a

{-@ reflect op @-}
op :: Ordering -> Ordering
op LT = GT
op GT = LT
op EQ = EQ

{-@ eq_is_eq :: x:Ordinal -> y:Ordinal -> {(comp x y == EQ) <=> (x == y)} @-}
eq_is_eq :: Ordinal -> Ordinal -> ()
eq_is_eq x@Zero y@Zero = (x `comp` y == EQ) *** QED
eq_is_eq x@Zero y@(Ord a1 n1 b1) = ((x `comp` y == EQ) == False) *** QED
eq_is_eq x@(Ord a0 n0 b0) y@Zero = ((x `comp` y == EQ) == False) *** QED
eq_is_eq x@(Ord a0 n0 b0) y@(Ord a1 n1 b1) = ((x `comp` y == EQ) == (x == y))
    === (case (a0 `comp` a1) of
            LT -> (False == (x == y))
            GT -> (False == (x == y))
            EQ -> case (n0 `compInt` n1) of
                LT -> (False == (x == y))
                GT -> (False == (x == y))
                EQ -> ((x `comp` y == EQ) == (x == y)))
    ==? True ? (eq_is_eq a0 a1 &&& eq_is_eq b0 b1) *** QED

{-@ op_op :: x:Ordering -> {op (op x) == x} @-}
op_op x = op (op x) == x *** QED

{-@ op_compInt :: x:Int -> y:Int -> {compInt x y == op (compInt y x)} @-}
op_compInt x y = compInt x y == op (compInt y x) *** QED

{-@ op_comp :: x:Ordinal -> y:Ordinal -> {comp x y == op (comp y x)} @-}
op_comp x@Zero y = (x `comp` y == op (y `comp` x)) *** QED
op_comp x y@Zero = (x `comp` y == op (y `comp` x)) *** QED
op_comp x@(Ord a0 n0 b0) y@(Ord a1 n1 b1) = (x `comp` y == op (y `comp` x)) 
    === (case (a0 `comp` a1 ==? op (a1 `comp` a0) ? op_comp a0 a1) of
            LT -> (LT == op GT)
            GT -> (GT == op LT)
            EQ -> case (n0 `compInt` n1 ==? op (n1 `compInt` n0) ? op_compInt n0 n1) of
                LT -> (LT == op GT)
                GT -> (GT == op LT)
                EQ -> (x `comp` y == op (y `comp` x)))
    ==? True ? (op_comp b0 b1) *** QED

----------------------------------------------------------------

---- INSTANCE NUM ----

-- The structure of this is very similar to the LiquidAgda stuff.
{-@ reflect n2o' @-}
n2o' 0 = Zero
n2o' p = Ord Zero p Zero
{-@ normal_nat :: n:Nat -> {normal (n2o' n)} @-}
normal_nat :: Int -> ()
normal_nat p = normal (n2o' p) === normal Zero *** QED
{-@ n2o :: Nat -> NFOrd @-}
n2o n = (n2o' n) `withProof` (normal_nat n)
{-@ abs' :: Int -> Nat @-}
abs' :: Int -> Int
abs' n
  | 0 < n     = n
  | otherwise = 0 - n


{-@ zero :: NFOrd @-}
zero    = n2o 0
{-@ one :: NFOrd @-}
one     = n2o 1
{-@ w :: NFOrd @-}
w       = let w = (Ord one 1 Zero) in w `withProof` [normal Zero, normal w]
{-@ omega :: NFOrd @-}
omega       = w

----

{-@ reflect add' @-}
add' :: Ordinal -> Ordinal -> Ordinal
add' x Zero = x
add' Zero y = y
add' x@(Ord a0 n0 b0) y@(Ord a1 n1 b1) = case (a1 `comp` a0) of
    GT -> y
    LT -> (Ord a0 n0 (add' b0 y))
    EQ -> (Ord a0 (n0+n1) (add' b0 b1))
{-@ normal_add :: x:NFOrd -> y:NFOrd -> {normal (add' x y)} @-}
normal_add :: Ordinal -> Ordinal -> ()
normal_add x y@Zero = normal (add' x y) *** QED
normal_add x@Zero y = normal (add' x y) *** QED
normal_add x@(Ord a0 n0 b0) y@(Ord a1 n1 b1) = normal (add' x y) 
    === (case (a1 `comp` a0) of
            GT -> (normal y)
            LT -> (normal (Ord a0 n0 (add' b0 y)))
            EQ -> (normal (Ord a0 (n0+n1) (add' b0 b1))))
    ==? True ? ((normal x *** QED)
                 &&& (normal y *** QED)
                 &&& eq_is_eq a1 a0
                 &&& normal_add b0 b1
                 &&& normal_add b0 y) *** QED
{-@ add :: NFOrd -> NFOrd -> NFOrd @-}
add x y = (add' x y) `withProof` (normal_add x y)

----

{-@ reflect sub' @-}
sub' :: Ordinal -> Ordinal -> Ordinal
sub' x Zero = x
sub' Zero y = Zero
sub' x@(Ord a0 n0 b0) y@(Ord a1 n1 b1) = case (a0 `comp` a1) of
    LT -> Zero
    GT -> x
    EQ -> case (n0 `compInt` n1) of
        LT -> Zero
        GT -> (Ord a0 (n0-n1) b0)
        EQ -> (sub' b0 b1)
{-@ normal_sub :: x:NFOrd -> y:NFOrd -> {normal (sub' x y)} @-}
normal_sub :: Ordinal -> Ordinal -> ()
normal_sub x y@Zero = normal (sub' x y) *** QED
normal_sub x@Zero y = normal (sub' x y) *** QED
normal_sub x@(Ord a0 n0 b0) y@(Ord a1 n1 b1) = normal (sub' x y) 
    === (case (a0 `comp` a1) of
            LT -> normal Zero
            GT -> normal x
            EQ -> case (n0 `compInt` n1) of
                LT -> normal Zero
                GT -> normal (Ord a0 (n0-n1) b0)
                EQ -> normal (sub' b0 b1))
    ==? True ? ((normal x *** QED)
                 &&& (normal y *** QED)
                 &&& normal_sub b0 b1) *** QED
{-@ sub :: NFOrd -> NFOrd -> NFOrd @-}
sub x y = (sub' x y) `withProof` (normal_sub x y)

----

{-@ reflect mul' @-}
{-@ mul' :: x:_ -> y:_ -> _ / [(size x), (size y)] @-}
mul' :: Ordinal -> Ordinal -> Ordinal
mul' x Zero = Zero
mul' Zero x = Zero
mul' (Ord a0 n0 b0) (Ord Zero n1 Zero) = (Ord a0 (n0*n1) b0)
mul' (Ord a0 n0 b0) (Ord a1 n1 Zero) = (Ord (add' a0 a1) n1 Zero)
mul' x (Ord a1 n1 b1) = (add' (mul' x (Ord a1 n1 Zero)) (mul' x b1))
{-@ normal_mul :: x:NFOrd -> y:NFOrd -> {normal (mul' x y)} / [(size x), (size y)] @-}
normal_mul :: Ordinal -> Ordinal -> ()
normal_mul x y@Zero = normal (mul' x y) *** QED
normal_mul x@Zero y = normal (mul' x y) *** QED
normal_mul x@(Ord a0 n0 b0) y@(Ord Zero n1 Zero) = normal (mul' x y) 
    === normal (Ord a0 (n0*n1) b0)
    ==? True ? ((normal x *** QED) &&& (normal y *** QED)) *** QED
normal_mul x@(Ord a0 n0 b0) y@(Ord a1 n1 Zero) = normal (mul' x y) 
    === normal (Ord (add' a0 a1) n1 Zero)
    ==? True ? ((normal x *** QED) &&& (normal y *** QED) &&& normal_add a0 a1) 
    *** QED 
normal_mul x y@(Ord a1 n1 b1) = normal (mul' x y) 
    === normal (add' (mul' x (Ord a1 n1 Zero)) (mul' x b1))
    ==? True ? ((normal x *** QED) 
            &&& (normal y *** QED)
            &&& (normal Zero *** QED)
            &&& (normal (Ord a1 n1 Zero) *** QED)
            &&& normal_mul x (Ord a1 n1 Zero)
            &&& normal_mul x b1
            &&& normal_add (mul' x (Ord a1 n1 Zero)) (mul' x b1))
    *** QED
{-@ mul :: NFOrd -> NFOrd -> NFOrd @-}
mul x y = (mul' x y) `withProof` (normal_mul x y)
