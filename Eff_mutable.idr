module Eff_mutable

import Language.Reflection
import Effective

{- TODO:

* Make effect/lift/call etc functions to lose interpreter overhead
* Try to find nice notation
* Allow adding effects/handlers in the middle of a program (e.g. adding
  exception handlers)
* More examples: concurrency, finer grained IO, nondeterminism, partiality. 
* Are dependent resources possible (e.g. tracking file open state)?

-}

---- The Effect EDSL itself ----

data EFF : (Type -> Type) -> Type where
     MkEff : (eff : Type -> Type) -> 
             Effective a eff f -> EFF f

using (m : Type -> Type, 
       xs : List (EFF m), xs' : List (EFF m), xs'' : List (EFF m),
       ys : List (EFF m))

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

  -- some proof automation
  findEffElem : Nat -> Tactic -- Nat is maximum search depth
  findEffElem O = Refine "Here" `Seq` Solve 
  findEffElem (S n) = GoalType "EffElem" 
            (Try (Refine "Here" `Seq` Solve)
                 (Refine "There" `Seq` (Solve `Seq` findEffElem n)))
 
  findSubList : Nat -> Tactic
  findSubList O = Refine "SubNil" `Seq` Solve
  findSubList (S n) 
     = GoalType "SubList" 
           (Try (Try (Refine "SubNil" `Seq` Solve)
                     (Refine "subListId" `Seq` Solve))
           ((Try (Refine "Keep" `Seq` Solve)
                 (Refine "Drop" `Seq` Solve)) `Seq` findSubList n))

  -- the language of Effects

  data MEff : List (EFF m) -> List (EFF m) -> Type -> Type where
       value  : a -> MEff xs xs a
       ebind  : MEff xs xs' a -> (a -> MEff xs' xs'' b) -> MEff xs xs'' b
       effect : {e : Type -> Type} -> 
                {default tactics { reflect findEffElem 10; solve; } 
                   p : EffElem e xs} -> 
                e t -> MEff xs xs t
       call   : {default tactics { reflect findSubList 10; solve; }
                   p : SubList ys xs} ->
                MEff ys ys t -> MEff xs xs t
       lift   : m a -> MEff xs xs a

--   Eff : List (EFF m) -> Type -> Type

  -- for 'do' notation

  return : a -> MEff xs xs a
  return = value

  (>>=) : MEff xs xs' a -> (a -> MEff xs' xs'' b) -> MEff xs xs'' b
  (>>=) = ebind

  -- for idiom brackets

  infixl 2 <$>

  pure : a -> MEff xs xs a
  pure = value

  (<$>) : MEff xs xs (a -> b) -> MEff xs xs a -> MEff xs xs b
  (<$>) prog v = do fn <- prog
                    arg <- v
                    return (fn arg)

  -- an interpreter

  execEff : Monad m => Env xs -> EffElem e xs -> e a ->
                       (Env xs -> a -> m t) -> m t
  execEff (val :: env) Here eff k 
      = runEffect val eff (\res, v => k (res :: env) v)
  execEff (val :: env) (There p) eff k 
      = execEff env p eff (\env', v => k (val :: env') v)

  eff : Monad m => Env xs -> MEff xs xs' a -> (Env xs' -> a -> m b) -> m b
  eff env (value x) k = k env x
  eff env (prog `ebind` c) k 
     = eff env prog (\env', p' => eff env' (c p') k)
  eff env (effect {p=prf} effP) k = execEff env prf effP k
  eff env (call {p=prf} effP) k 
     = let env' = dropEnv env prf in 
           eff env' effP (\envk, p' => k (rebuildEnv envk prf env) p')
  eff env (lift act) k = do x <- act
                            k env x

  run : Monad m => Env xs -> MEff xs xs' a -> m a
  run env prog = eff env prog (\env, r => return r)

syntax Eff [xs] [t] = MEff xs xs t
syntax GenEff [xs] [a] = Monad m => MEff xs xs {m} a 

-- some higher order things

mapE : Monad m => (a -> MEff xs xs {m} b) -> List a -> MEff xs xs {m} (List b)
mapE f []        = pure [] 
mapE f (x :: xs) = [| f x :: mapE f xs |]

when : Monad m => Bool -> MEff xs xs {m} () -> MEff xs xs {m} ()
when True  e = e
when False e = return ()

