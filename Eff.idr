module Eff

import Language.Reflection
import Control.Monad.Identity
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
       xs : Vect EFF n, xs' : Vect EFF n, xs'' : Vect EFF n,
       ys : Vect EFF p, ys' : Vect EFF p)

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

  updateResTy : (xs : Vect EFF n) -> EffElem e a xs -> e a b t -> 
                Vect EFF n
  updateResTy {b} (MkEff a e :: xs) Here n = (MkEff b e) :: xs
  updateResTy (x :: xs) (There p) n = x :: updateResTy xs p n

  infix 5 :::, :-, :=

  data LRes : lbl -> Type -> Type where
       (:=) : (x : lbl) -> res -> LRes x res

  (:::) : lbl -> EFF -> EFF 
  (:::) {lbl} x (MkEff r eff) = MkEff (LRes x r) eff

  unlabel : {l : ty} -> Env m [l ::: x] -> Env m [x]
  unlabel {m} {x = MkEff a eff} [l := v] = [v]

  relabel : (l : ty) -> Env m [x] -> Env m [l ::: x]
  relabel {x = MkEff a eff} l [v] = [l := v]

  -- the language of Effects

  data EffM : (m : Type -> Type) ->
              Vect EFF n -> Vect EFF n -> Type -> Type where
       value   : a -> EffM m xs xs a
       ebind   : EffM m xs xs' a -> (a -> EffM m xs' xs'' b) -> EffM m xs xs'' b
       effect  : {a, b: _} -> {e : Effect} ->
                 (prf : EffElem e a xs) -> 
                 (eff : e a b t) -> 
                 EffM m xs (updateResTy xs prf eff) t
       lift    : (prf : SubList ys xs) ->
                 EffM m ys ys' t -> EffM m xs (updateWith ys' xs prf) t
       new     : Effective e m =>
                 res -> EffM m (MkEff res e :: xs) (MkEff res' e :: xs') a ->
                 EffM m xs xs' a
       catch   : Catchable m err =>
                 EffM m xs xs' a -> (err -> EffM m xs xs' a) ->
                 EffM m xs xs' a
       (:-)    : (l : ty) -> EffM m [x] [y] t -> EffM m [l ::: x] [l ::: y] t

--   Eff : List (EFF m) -> Type -> Type

  implicit
  lift' : {default tactics { reflect findSubList 10; solve; }
             prf : SubList ys xs} ->
          EffM m ys ys' t -> EffM m xs (updateWith ys' xs prf) t
  lift' {prf} e = lift prf e

  implicit
  effect' : {a, b: _} -> {e : Effect} ->
            {default tactics { reflect findEffElem 10; solve; } 
               prf : EffElem e a xs} -> 
            (eff : e a b t) -> 
           EffM m xs (updateResTy xs prf eff) t
  effect' {prf} e = effect prf e


  -- for 'do' notation

  return : a -> EffM m xs xs a
  return x = value x

  (>>=) : EffM m xs xs' a -> (a -> EffM m xs' xs'' b) -> EffM m xs xs'' b
  (>>=) = ebind

  -- for idiom brackets

  infixl 2 <$>

  pure : a -> EffM m xs xs a
  pure = value

  (<$>) : EffM m xs xs (a -> b) -> EffM m xs xs a -> EffM m xs xs b
  (<$>) prog v = do fn <- prog
                    arg <- v
                    return (fn arg)

  -- an interpreter

  execEff : Env m xs -> (p : EffElem e res xs) -> 
            (eff : e res b a) ->
            (Env m (updateResTy xs p eff) -> a -> m t) -> m t
  execEff (val :: env) Here eff' k 
      = runEffect val eff' (\res, v => k (res :: env) v)
  execEff (val :: env) (There p) eff k 
      = execEff env p eff (\env', v => k (val :: env') v)

  eff : Env m xs -> EffM m xs xs' a -> (Env m xs' -> a -> m b) -> m b
  eff env (value x) k = k env x
  eff env (prog `ebind` c) k 
     = eff env prog (\env', p' => eff env' (c p') k)
  eff env (effect prf effP) k = execEff env prf effP k
  eff env (lift prf effP) k 
     = let env' = dropEnv env prf in 
           eff env' effP (\envk, p' => k (rebuildEnv envk prf env) p')
  eff env (new r prog) k
     = let env' = r :: env in 
           eff env' prog (\(v :: envk), p' => k envk p')
  eff env (catch prog handler) k
     = catch (eff env prog k)
             (\e => eff env (handler e) k)
  eff {xs = [l ::: x]} env (l :- prog) k
     = let env' = unlabel {l} env in
           eff env' prog (\envk, p' => k (relabel l envk) p')

  run : Applicative m => Env m xs -> EffM m xs xs' a -> m a
  run env prog = eff env prog (\env, r => pure r)

  runEnv : Applicative m => Env m xs -> EffM m xs xs' a -> m (Env m xs', a)
  runEnv env prog = eff env prog (\env, r => pure (env, r))

  runPure : Env Identity xs -> EffM Identity xs xs' a -> a
  runPure env prog = case eff env prog (\env, r => return r) of
                          Id v => v

syntax Eff [xs] [a] = Monad m => EffM m xs xs a 
syntax EffT [m] [xs] [t] = EffM m xs xs t

-- some higher order things

mapE : Monad m => {xs : Vect EFF n} -> 
       (a -> EffM m xs xs b) -> List a -> EffM m xs xs (List b)
mapE f []        = pure [] 
mapE f (x :: xs) = [| f x :: mapE f xs |]

when : Monad m => {xs : Vect EFF n} ->
       Bool -> EffM m xs xs () -> EffM m xs xs ()
when True  e = e
when False e = return ()

