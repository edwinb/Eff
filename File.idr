module File

import Eff
import Exception

data Handle : Mode -> Type where
     FH : File -> Handle m

data FileIO : Effect where
     Open  : String -> (m : Mode) -> FileIO () (Handle m) ()
     Close :                         FileIO (Handle m) () ()

     ReadLine  :           FileIO (Handle Read)  (Handle Read) String
     WriteLine : String -> FileIO (Handle Write) (Handle Write) ()
     EOF       :           FileIO (Handle Read)  (Handle Read) Bool

instance Effective FileIO IO where
    runEffect () (Open fname m) k = do h <- openFile fname m
                                       k (FH h) ()
    runEffect (FH h) Close      k = do closeFile h
                                       k () ()
    runEffect (FH h) ReadLine        k = do str <- fread h
                                            k (FH h) str
    runEffect (FH h) (WriteLine str) k = do fwrite h str
                                            k (FH h) ()
    runEffect (FH h) EOF             k = do e <- feof h
                                            k (FH h) e

instance Effective FileIO (IOExcept String) where
    runEffect () (Open fname m) k 
       = do h <- ioe_lift (openFile fname m)
            valid <- ioe_lift (validFile h)
            if valid then k (FH h) ()
                     else ioe_fail "File open failed"
    runEffect (FH h) Close           k = do ioe_lift (closeFile h); k () ()
    runEffect (FH h) ReadLine        k = do str <- ioe_lift (fread h)
                                            k (FH h) str
    runEffect (FH h) (WriteLine str) k = do ioe_lift (fwrite h str)
                                            k (FH h) ()
    runEffect (FH h) EOF             k = do e <- ioe_lift (feof h)
                                            k (FH h) e

FILE_IO : Type -> EFF
FILE_IO t = MkEff t FileIO 

open : Effective FileIO e =>
       String -> (m : Mode) -> EffM e [FILE_IO ()] [FILE_IO (Handle m)] ()
open f m = effect (Open f m)

close : Effective FileIO e =>
        EffM e [FILE_IO (Handle m)] [FILE_IO ()] ()
close = effect Close

readLine : Effective FileIO e => EffT e [FILE_IO (Handle Read)] String
readLine = effect ReadLine

writeLine : Effective FileIO e => String -> EffT e [FILE_IO (Handle Write)] ()
writeLine str = effect (WriteLine str)

eof : Effective FileIO e => EffT e [FILE_IO (Handle Read)] Bool
eof = effect EOF




