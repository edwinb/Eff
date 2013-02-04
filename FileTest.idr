module Main 

import File
import State
import Eff_mutable

data FName = Count | NotCount

readFile : EffT IO [FILE_IO (Handle Read), Count ::: STATE Int] (List String)
readFile = readAcc [] where
    readAcc : List String -> Eff IO [FILE_IO (Handle Read), Count ::: STATE Int] (List String)
    readAcc acc = do e <- call eof
                     if (not e) 
                        then do str <- call readLine
                                ls <- call (Count :- get)
                                call (Count :- put (ls + 1))
                                readAcc (str :: acc)
                        else return (reverse acc)

testFile : EffT IO [FILE_IO (), Count ::: STATE Int] ()
testFile = do call (open "testFile" Read)
              str <- readFile
              lift $ print str
              ls <- call (Count :- get)
              lift $ print ls
              call close

main : IO ()
main = run [(), Count := 0] testFile
