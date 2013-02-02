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

using (m : Type -> Type, 
       xs : Vect (EFF m) n, xs' : Vect (EFF m) n, xs'' : Vect (EFF m) n,
       ys : Vect (EFF m) p, ys' : Vect (EFF m) p)

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
           (Try (Refine "subListId" `Seq` Solve)
           ((Try (Refine "Keep" `Seq` Solve)
                 (Refine "Drop" `Seq` Solve)) `Seq` findSubList n))

  updateResTy : (xs : Vect (EFF m) n) -> EffElem e a xs -> e a b t -> 
                Vect (EFF m) n
  updateResTy {b} (MkEff a e i :: xs) Here n = (MkEff b e i) :: xs
  updateResTy (x :: xs) (There p) n = x :: updateResTy xs p n


  -- the language of Effects

  data MEff : Vect (EFF m) n -> Vect (EFF m) n -> Type -> Type where
       value  : a -> MEff xs xs a
       ebind  : MEff xs xs' a -> (a -> MEff xs' xs'' b) -> MEff xs xs'' b
       effect : {a, b: _} -> {e : Effect} ->
                {default tactics { reflect findEffElem 10; solve; } 
                  prf : EffElem e a xs} -> 
                  (eff : e a b t) -> 
                MEff xs (updateResTy xs prf eff) t
       call   : {default tactics { reflect findSubList 10; solve; }
                   prf : SubList ys xs} ->
                MEff ys ys' t -> MEff xs (updateWith ys' xs prf) t
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

  execEff : Monad m => {e : Effect} -> {t : Type} ->
                       Env xs -> (p : EffElem e res xs) -> 
                       (eff : e res b a) ->
                       (Env (updateResTy xs p eff) -> a -> m t) -> m t
  execEff (val :: env) Here eff' k 
      = runEffect val eff' (\res, v => k (res :: env) v)
  execEff (val :: env) (There p) eff k 
      = execEff env p eff (\env', v => k (val :: env') v)

  eff : Monad m => Env xs -> MEff xs xs' a -> (Env xs' -> a -> m b) -> m b
  eff env (value x) k = k env x
  eff env (prog `ebind` c) k 
     = eff env prog (\env', p' => eff env' (c p') k)
  eff env (effect {prf} effP) k = execEff env prf effP k
  eff env (call {prf} effP) k 
     = let env' = dropEnv env prf in 
           eff env' effP (\envk, p' => k (rebuildEnv envk prf env) p')
  eff env (lift act) k = do x <- act
                            k env x

  run : Monad m => Env xs -> MEff xs xs' a -> m a
  run env prog = eff env prog (\env, r => return r)

syntax Eff [xs] [t] = MEff xs xs t
syntax GenEff [xs] [a] = Monad m => MEff xs xs {m} a 

-- some higher order things

mapE : Monad m => {xs : Vect (EFF m) n} -> 
       (a -> MEff xs xs {m} b) -> List a -> MEff xs xs {m} (List b)
mapE f []        = pure [] 
mapE f (x :: xs) = [| f x :: mapE f xs |]

when : Monad m => {xs : Vect (EFF m) n} ->
       Bool -> MEff xs xs {m} () -> MEff xs xs {m} ()
when True  e = e
when False e = return ()

