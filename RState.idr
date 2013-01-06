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

instance Monad m => Effective a (State a) m where
     runEffect st Get       k = k st st
     runEffect st (Put new) k = k new ()

instance Effective () (Exception a) Maybe where
     runEffect _ (Raise e) k = Nothing

instance Show a => Effective () (Exception a) IO where
     runEffect _ (Raise e) k = do putStrLn (show e)
                                  believe_me (exit 1)

instance Effective () Channel IO where
     runEffect _ InCh k = do x <- getChar
                             k () x 
     runEffect _ (OutCh v) k = do putStr (show v)
                                  k () ()
     runEffect _ (OutInt v) k = do putStr (show v)
                                   k () ()

STATE : Monad m => Type -> EFF m
STATE t = MkEff (State t) %instance

get : Monad m => Eff [STATE x] {m} x
get = effect Get

put : Monad m => x -> Eff [STATE x] {m} ()
put x = effect (Put x)

CHANNEL : EFF IO
CHANNEL = MkEff Channel %instance

EXCEPTION : Type -> EFF Maybe
EXCEPTION t = MkEff (Exception t) %instance

IO_EXCEPTION : EFF IO
IO_EXCEPTION = MkEff (Exception String) %instance


---- A simple example ----

data Tree = Leaf | Node Tree Int Tree

testTree : Tree
testTree = Node (Node (Node Leaf 5 (Node Leaf 1 Leaf)) 3 (Node Leaf 1 Leaf))
                2
                (Node Leaf 1 Leaf)

write : Eff [STATE Int] ()
write = call (put 42)

countOnes : Monad m => Tree -> Eff [STATE Int] {m} ()
countOnes Leaf = return ()
countOnes (Node l v r) = do if v == 1
                               then do n <- call get
                                       call (put (n + 1))
                               else return ()
                            call $ countOnes l
                            call $ countOnes r

testProg : Eff [CHANNEL, STATE Int, IO_EXCEPTION] Int
testProg = do val <- call get
              effect $ OutCh '?'
              c <- effect InCh
              if (c == 'x') then effect $ Raise "NO!"
                            else return ()
              let tot = cast c + val
              effect $ OutCh (cast tot) 
              call $ countOnes testTree
              nodes <- call get
              effect $ OutInt nodes
              lift $ putStr "DONE!\n"
              call get

main : IO ()
main = do n <- run [(), 0, ()] testProg
          print n

