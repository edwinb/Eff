module Effective

Effect : Type
Effect = Type -> Type -> Type -> Type

data EFF : Type where
     MkEff : Type -> Effect -> EFF

class Effective (e : Effect) (m : Type -> Type) where
     runEffect : res -> (eff : e res res' t) -> (res' -> t -> m a) -> m a

class Catchable (m : Type -> Type) t where
    catch : m a -> (t -> m a) -> m a













---------------------

using (xs : Vect a m, ys : Vect a n)
  data SubList : Vect a m -> Vect a n -> Type where
       SubNil : SubList {a} [] []
       Keep   : SubList xs ys -> SubList (x :: xs) (x :: ys)
       Drop   : SubList xs ys -> SubList xs (x :: ys)

  subListId : SubList xs xs
  subListId {xs = Nil} = SubNil
  subListId {xs = x :: xs} = Keep subListId

effType : EFF -> Type
effType (MkEff t _) = t

using (m : Type -> Type, 
       xs : Vect EFF n, xs' : Vect EFF n, xs'' : Vect EFF n,
       ys : Vect EFF p)

  data Env  : (m : Type -> Type) -> Vect EFF n -> Type where
       Nil  : Env m Nil
       (::) : Effective eff m => a -> Env m xs -> Env m (MkEff a eff :: xs)

  data EffElem : (Type -> Type -> Type -> Type) -> Type ->
                 Vect EFF n -> Type where
       Here : EffElem x a (MkEff a x :: xs)
       There : EffElem x a xs -> EffElem x a (y :: xs)

  -- make an environment corresponding to a sub-list
  dropEnv : Env m ys -> SubList xs ys -> Env m xs
  dropEnv [] SubNil = []
  dropEnv (v :: vs) (Keep rest) = v :: dropEnv vs rest
  dropEnv (v :: vs) (Drop rest) = dropEnv vs rest

  updateWith : {ys : Vect a p} ->
               (ys' : Vect a p) -> (xs : Vect a n) ->
               SubList ys xs -> Vect a n
  updateWith (y :: ys) (x :: xs) (Keep rest) = y :: updateWith ys xs rest
  updateWith ys        (x :: xs) (Drop rest) = x :: updateWith ys xs rest
  updateWith []        []        SubNil      = []

  -- put things back, replacing old with new in the sub-environment
  rebuildEnv : {ys' : Vect _ p} ->
               Env m ys' -> (prf : SubList ys xs) -> 
               Env m xs -> Env m (updateWith ys' xs prf) 
  rebuildEnv []        SubNil      env = env
  rebuildEnv (x :: xs) (Keep rest) (y :: env) = x :: rebuildEnv xs rest env
  rebuildEnv xs        (Drop rest) (y :: env) = y :: rebuildEnv xs rest env
--   rebuildEnv (x :: xs) SubNil      env impossible

