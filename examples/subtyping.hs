{-@
  class Foo a where
    foo :: {v : a | False} -> a
@-}
class Foo a where
  foo :: a -> a

{-@
  instance Foo Int where
    foo :: {v : Int | True} -> Int
@-}
instance Foo Int where
  foo x = x

-- This should be rejected, even though 5 satisfies {v : Int | True} and
-- {v : Int | True} -> Int is a subtype of {v : a | False} -> a
shouldReject = foo 5
