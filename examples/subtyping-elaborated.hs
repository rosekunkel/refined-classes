-- This is the elaboration of subtyping.hs, which is correctly rejected.

{-@ data FooDict a = FooDict ({v : a | False} -> a) @-}
data FooDict a = FooDict (a -> a)

{-@ fooIntImpl :: {v : Int | True} -> Int @-}
fooIntImpl :: Int -> Int
fooIntImpl x = x

fooIntDict :: FooDict Int
fooIntDict = FooDict fooIntImpl

-- If we didn't propogate the refinement on the class method here, the program
-- would be rejected here, rather than at shouldReject.
{-@ foo :: FooDict a -> {v : a | False} -> a @-}
foo :: FooDict a -> a -> a
foo (FooDict f) x = f x

-- This is where the program is rejected.
shouldReject = foo fooIntDict 5
