module Effective

class Effective res (e : Type -> Type) (m : Type -> Type) where
     runEffect : res -> e t -> (res -> t -> m a) -> m a

using (xs, ys : List a)
  data SubList : List a -> List a -> Type where
       SubNil : SubList {a} [] []
       Keep   : SubList xs ys -> SubList (x :: xs) (x :: ys)
       Drop   : SubList xs ys -> SubList xs (x :: ys)

  subListId : SubList xs xs
  subListId {xs = Nil} = SubNil
  subListId {xs = x :: xs} = Keep subListId

