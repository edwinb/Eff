module Main 

import File
import State
import StdIO
import Eff

data FName = Count | NotCount

FileIO : Type -> Type -> Type
FileIO st t 
   = EffT (IOExcept String) [FILE_IO st, STDIO, Count ::: STATE Int] t

readFile : FileIO (Handle Read) (List String)
readFile = readAcc [] where
    readAcc : List String -> FileIO (Handle Read) (List String) 
    readAcc acc = do e <- lift eof
                     if (not e) 
                        then do str <- lift readLine
                                ls <- lift (Count :- get)
                                lift (Count :- put (ls + 1))
                                readAcc (str :: acc)
                        else return (reverse acc)

testFile : FileIO () () 
testFile = catch (do lift (open "testFile" Read)
                     str <- readFile
                     lift (putStrLn (show str))
                     ls <- lift (Count :- get)
                     lift (putStrLn (show ls))
                     lift close)
                 (\err => lift (putStrLn ("Handled: " ++ show err)))

main : IO ()
main = do ioe_run (run [(), (), Count := 0] testFile)
                  (\err => print err) (\ok => return ())


