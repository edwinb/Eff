module Eff

import Language.Reflection

{- TODO:

* Make effect/lift/call etc functions to lose interpreter overhead
* Try to find nice notation
* Allow adding effects/handlers in the middle of a program (e.g. adding
  exception handlers)
* More examples: concurrency, finer grained IO, nondeterminism, partiality. 
* Are dependent resources possible (e.g. tracking file open state)?

-}

class Effective res (e : Type -> Type) (m : Type -> Type) where
     runEffect : res -> e t -> (res -> t -> m a) -> m a

using (xs, ys : List a)
  data SubList : List a -> List a -> Type where
       SubNil : SubList {a} [] []
       Keep   : SubList xs ys -> SubList (x :: xs) (x :: ys)
       Drop   : SubList xs ys -> SubList xs (x :: ys)

---- The Effect EDSL itself ----

data EFF : (Type -> Type) -> Type where
     MkEff : (eff : Type -> Type) -> 
             Effective a eff f -> EFF f

using (m : Type -> Type, xs : List (EFF m), ys : List (EFF m))

  data Env  : List (EFF m) -> Type where
       Nil  : Env {m} Nil
       (::) : a -> Env {m} g -> Env (MkEff {a} eff i :: g)

  -- make an environment corresponding to a sub-list
  dropEnv : Env ys -> SubList xs ys -> Env xs
  dropEnv [] SubNil = []
  dropEnv (v :: vs) (Keep rest) = v :: dropEnv vs rest
  dropEnv (v :: vs) (Drop rest) = dropEnv vs rest

  -- put things back, replacing old with new in the sub-environment
  rebuildEnv : Env xs -> SubList xs ys -> Env ys -> Env ys
  rebuildEnv [] _ env = env
  rebuildEnv (x :: xs) (Keep rest) (y :: env) =  x :: rebuildEnv xs rest env
  rebuildEnv xs (Drop rest) (y :: env) = y :: rebuildEnv xs rest env

  data EffElem : (Type -> Type) -> List (EFF m) -> Type where
       Here : EffElem x (MkEff {a} x i :: xs)
       There : EffElem x xs -> EffElem x (y :: xs)


  data Eff : List (EFF m) -> Type -> Type where
       return : a -> Eff xs a
       (>>=)  : Eff xs a -> (a -> Eff xs b) -> Eff xs b
       effect : {e : Type -> Type} -> 
                e t -> EffElem e xs -> Eff xs t
       call   : Eff ys t -> SubList ys xs -> Eff xs t
       lift   : m a -> Eff xs a

  infixl 2 <$>

  pure : a -> Eff xs a
  pure = return

  (<$>) : Eff xs (a -> b) -> Eff xs a -> Eff xs b
  (<$>) prog v = do fn <- prog
                    arg <- v
                    return (fn arg)

  execEff : Monad m => Env xs -> EffElem e xs -> e a ->
                       (Env xs -> a -> m t) -> m t
  execEff (val :: env) Here eff k 
      = runEffect val eff (\res, v => k (res :: env) v)
  execEff (val :: env) (There p) eff k 
      = execEff env p eff (\env', v => k (val :: env') v)

  eff : Monad m => Env xs -> Eff xs a -> (Env xs -> a -> m b) -> m b
  eff env (return x)   k = k env x
  eff env (prog >>= c) k 
     = eff env prog (\env', p' => eff env' (c p') k)
  eff env (effect effP prf) k = execEff env prf effP k
  eff env (call effP prf) k 
     = let env' = dropEnv env prf in 
           eff env' effP (\envk, p' => k (rebuildEnv envk prf env) p')
  eff env (lift act) k = do x <- act
                            k env x

  run : Monad m => Env xs -> Eff xs a -> m a
  run env prog = eff env prog (\env, r => return r)

findEffElem : Nat -> Tactic -- Nat is maximum search depth
findEffElem O = Refine "Here" `Seq` Solve 
findEffElem (S n) = Try (Refine "Here" `Seq` Solve)
                        (Refine "There" `Seq` (Solve `Seq` findEffElem n))
 
findSubList : Nat -> Tactic
findSubList O = Refine "SubNil" `Seq` Solve
findSubList (S n) 
   = Try (Refine "SubNil" `Seq` Solve)
         ((Try (Refine "Keep" `Seq` Solve)
               (Refine "Drop" `Seq` Solve)) `Seq` findSubList n)

findSubList' : Nat -> Tactic
findSubList' O = Refine "SubNil"
findSubList' (S n) 
   = Try ((Try (Refine "Keep")
               (Refine "Drop")) `Seq` (findSubList' n))
         (Refine "SubNil")

syntax Effect [x] = effect x (tactics { reflect findEffElem 10; solve; })
syntax Call [x] = call x (tactics { reflect findSubList 10; solve; })

