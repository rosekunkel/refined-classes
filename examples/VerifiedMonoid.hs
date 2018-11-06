{-@
  class VerifiedMonoid a where
    vmempty :: a
    vmappend :: a -> a -> a

    vmappendAssoc :: x:a -> y:a -> z:a -> { vmappend x (vmappend y z) = vmappend (vmappend x y) z }
    vmappendLeftId :: x:a -> { vmappend vmempty x = x }
    vmappendRightId :: x:a -> { vmappend x vmempty = x }
@-}
class VerifiedMonoid a where
  vmempty :: a
  vmappend :: a -> a -> a

  vmappendAssoc :: a -> a -> a -> Proof
  vmappendLeftId :: a -> Proof
  vmappendRightId :: a -> Proof

instance VerifiedMonoid [a] where
  vmempty = []

  vmappend [] ys = ys
  vmappend (x:xs) ys = x:vmappend xs ys

  vmappendAssoc [] ys zs = trivial
  vmappendAssoc (x:xs) ys zs = vmappendAssoc xs ys zs

  vmappendLeftId _ = trivial

  vmappendRightId [] = trivial
  vmappendRightId (x:xs) = vmappendRightId xs

{-@ reflect myReverse @-}
myReverse :: [a] -> [a]
myReverse [] = []
myReverse (x:xs) = vmappend (myReverse xs) [x]

{-@ myReverseAntiHom :: xs:[a] -> ys:[a] -> { myReverse (vmappend xs ys) = vmappend (myReverse ys) (myReverse xs) } @-}
myReverseAntiHom :: [a] -> [a] -> Proof
myReverseAntiHom [] ys = myReverse (vmappend [] ys)
  === myReverse ys
  === vmappend (myReverse ys) [] ? vmappendRightId (myReverse ys)
  === vmappend (myReverse ys) (myReverse [])
  *** QED
myReverseAntiHom (x:xs) ys = myReverse (vmappend (x:xs) ys)
  === myReverse (x:vmappend xs ys)
  === vmappend (myReverse (vmappend xs ys)) [x]
  === vmappend (vmappend (myReverse ys) (myReverse xs)) [x] ? myReverseAntiHom xs ys
  === vmappend (myReverse ys) (vmappend (myReverse xs) [x]) ? vmappendAssoc (myReverse ys) (myReverse xs) [x]
  === vmappend (myReverse ys) (myReverse (x:xs))
  *** QED
