module Main 

import File
import State
import Eff_mutable

readFile : Eff [FILE_IO (Handle Read), STATE Int] (List String)
readFile = readAcc [] where
    readAcc : List String -> Eff [FILE_IO (Handle Read), STATE Int] (List String)
    readAcc acc = do e <- call eof
                     if (not e) 
                        then do str <- call readLine
                                ls <- call get
                                call (put (ls + 1))
                                readAcc (str :: acc)
                        else return (reverse acc)

testFile : Eff [FILE_IO (), STATE Int] ()
testFile = do call (open "testFile" Read)
              str <- call readFile
              lift $ print str
              ls <- call get
              lift $ print ls
              call close

main : IO ()
main = run [(), 0] testFile
