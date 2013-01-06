module Main

import Eff
import System

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

