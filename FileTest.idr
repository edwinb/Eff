module Main 

import File
import State
import Eff_mutable

data FName = Count | NotCount

readFile : Eff [FILE_IO (Handle Read), Count ::: STATE Int] (List String)
readFile = readAcc [] where
    readAcc : List String -> Eff [FILE_IO (Handle Read), Count ::: STATE Int] (List String)
    readAcc acc = do e <- call eof
                     if (not e) 
                        then do str <- call readLine
                                ls <- call (getFrom Count)
                                call (putTo Count (ls + 1))
                                readAcc (str :: acc)
                        else return (reverse acc)

testFile : Eff [FILE_IO (), Count ::: STATE Int] ()
testFile = do call (open "testFile" Read)
              str <- readFile
              lift $ print str
              ls <- call (getFrom Count)
              lift $ print ls
              call close

main : IO ()
main = run [(), 0] testFile
