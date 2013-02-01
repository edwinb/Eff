module Effective

class Effective (e : Type -> Type -> Type -> Type) 
                (m : Type -> Type) where
     runEffect : res -> (eff : e res res' t) -> (res' -> t -> m a) -> m a

using (xs : Vect a m, ys : Vect a n)
  data SubList : Vect a m -> Vect a n -> Type where
       SubNil : SubList {a} [] []
       Keep   : SubList xs ys -> SubList (x :: xs) (x :: ys)
       Drop   : SubList xs ys -> SubList xs (x :: ys)

  subListId : SubList xs xs
  subListId {xs = Nil} = SubNil
  subListId {xs = x :: xs} = Keep subListId

data EFF : (Type -> Type) -> Type where
     MkEff : Type ->
             (eff : Type -> Type -> Type -> Type) ->
             Effective eff f -> EFF f

using (m : Type -> Type, 
       xs : Vect (EFF m) n, xs' : Vect (EFF m) n, xs'' : Vect (EFF m) n,
       ys : Vect (EFF m) p)

  data Env  : Vect (EFF m) n -> Type where
       Nil  : Env {m} Nil
       (::) : a -> Env {m} xs -> Env (MkEff a eff i :: xs)

  data EffElem : (Type -> Type -> Type -> Type) -> Type ->
                 Vect (EFF m) n -> Type where
       Here : EffElem x a (MkEff a x i :: xs)
       There : EffElem x a xs -> EffElem x a (y :: xs)

  -- make an environment corresponding to a sub-list
  dropEnv : Env ys -> SubList xs ys -> Env xs
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
               Env ys' -> (prf : SubList ys xs) -> 
               Env xs -> Env (updateWith ys' xs prf) 
  rebuildEnv [] SubNil env = env
  rebuildEnv (x :: xs) (Keep rest) (y :: env) =  x :: rebuildEnv xs rest env
  rebuildEnv xs (Drop rest) (y :: env) = y :: rebuildEnv xs rest env

