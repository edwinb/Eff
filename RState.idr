module Main

import Control.Monad.Identity
import System

{- TODO:

* Make proofs of EffElem and SubList automatic
* Make return/lift/call etc functions to lose interpreter overhead
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
       lift   : EffElem e xs -> e t -> Eff xs t
       call   : SubList ys xs -> Eff ys t -> Eff xs t

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
  eff env (lift prf effP) k = execEff env prf effP k
  eff env (call prf effP) k 
     = let env' = dropEnv env prf in 
           eff env' effP (\envk, p' => k (rebuildEnv envk prf env) p')
 
  run : Monad m => Env xs -> Eff xs a -> m a
  run env prog = eff env prog (\env, r => return r)

  -- This is a horrible way of automating a proof of list membership
  -- statically. Do it better!

  syntax eqHack = (| Here, 
                     There Here, 
                     There (There Here),
                     There (There (There Here)),
                     There (There (There (There Here))),
                     There (There (There (There (There Here)))) |)
  syntax Lift [x] = lift eqHack x

---- Some algebraic resource/effect types ----

data State : Type -> Type -> Type where
     Get :      State a a
     Put : a -> State a ()

data Exception : Type -> Type -> Type where
     Raise : a -> Exception a b 

data Channel : Type -> Type where
     InCh : Channel Char
     OutCh : Char -> Channel ()
     OutInt : Int -> Channel ()

using (f : Type -> Type) -- not sure why it can't get this itself!
  instance Effective a (State a) f where
     runEffect st Get       k = k st st
     runEffect st (Put new) k = k new ()

instance Effective () (Exception a) Maybe where
     runEffect _ (Raise e) k = Nothing

instance Effective () (Exception a) IO where
     runEffect _ (Raise e) k = do putStrLn "FAIL!"
                                  believe_me (exit 1)

instance Effective () Channel IO where
     runEffect _ InCh k = do x <- getChar
                             k () x 
     runEffect _ (OutCh v) k = do putStr (show v)
                                  k () ()
     runEffect _ (OutInt v) k = do putStr (show v)
                                   k () ()

STATE : {m : Type -> Type} -> Type -> EFF m
STATE t = MkEff (State t) %instance

CHANNEL : EFF IO
CHANNEL = MkEff Channel %instance

EXCEPTION : Type -> EFF Maybe
EXCEPTION t = MkEff (Exception t) %instance

IO_EXCEPTION : Type -> EFF IO
IO_EXCEPTION t = MkEff (Exception t) %instance


---- A simple example ----

data Tree = Leaf | Node Tree Int Tree

testTree : Tree
testTree = Node (Node (Node Leaf 5 (Node Leaf 1 Leaf)) 3 (Node Leaf 1 Leaf))
                2
                (Node Leaf 1 Leaf)

countOnes : Tree -> Eff [CHANNEL, STATE Int, IO_EXCEPTION String] ()
countOnes Leaf = return ()
countOnes (Node l v r) = do if v == 1
                               then do n <- Lift Get
                                       Lift (Put (n + 1))
                               else return ()
                            countOnes l
                            countOnes r

countOnes' : Tree -> Eff [STATE Int] {m} ()
countOnes' Leaf = return ()
countOnes' (Node l v r) = do if v == 1
                               then do n <- Lift Get
                                       Lift (Put (n + 1))
                               else return ()
                             countOnes' l
                             countOnes' r

testProg : Eff [CHANNEL, STATE Int, IO_EXCEPTION String] ()
testProg = do val <- Lift Get
              Lift (OutCh '?')
              c <- Lift InCh
              if (c == 'x') then Lift (Raise "NO!")
                            else return ()
              let tot = cast c + val
              Lift (OutCh (cast tot))
              call (Drop (Keep (Drop SubNil))) (countOnes' testTree)
              nodes <- Lift Get
              Lift (OutInt nodes)
              return ()

main : IO ()
main = run [(), 0, ()] testProg

