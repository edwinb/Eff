module Main

import Eff_mutable
import System
import State
import Exception

---- IO as an effect ----

data Channel : Type -> Type where
     InCh : Channel Char
     OutCh : Char -> Channel ()
     OutInt : Int -> Channel ()

instance Effective () Channel IO where
     runEffect _ InCh k = do x <- getChar
                             k () x 
     runEffect _ (OutCh v) k = do putStr (show v)
                                  k () ()
     runEffect _ (OutInt v) k = do putStr (show v)
                                   k () ()

CHANNEL : EFF IO
CHANNEL = MkEff Channel %instance



---- A simple example ----

data Tree = Leaf | Node Tree Int Tree

testTree : Tree
testTree = Node (Node (Node Leaf 5 (Node Leaf 1 Leaf)) 3 (Node Leaf 1 Leaf))
                2
                (Node Leaf 1 Leaf)

write : Eff [STATE Int] ()
write = call (put 42)

countOnes : Tree -> GenEff [STATE Int] ()
countOnes Leaf = return ()
countOnes (Node l v r) = do if v == 1
                               then do n <- call get
                                       call (put (n + 1))
                               else return ()
                            call (countOnes l)
                            call (countOnes r)

testProg : Eff [IO_EXCEPTION, CHANNEL, STATE Int] ()
testProg = do val <- call get
              effect (OutCh '?')
              c <- effect InCh
              when (c == 'x') $ effect (Raise "NO!")
              let tot = cast c + val
              effect (OutCh (cast tot))
              call (countOnes testTree)
              nodes <- call get
              effect (OutInt nodes)
              lift (putStr "DONE!\n")
              call get

main : IO ()
main = do n <- run [(), (), 0] testProg
          print n

