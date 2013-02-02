module File

import Eff_mutable
import Exception

data Handle : Mode -> Type where
     FH : File -> Handle m

data FileIO : Effect where
     Open  : String -> (m : Mode) -> FileIO () (Handle m) ()
     Close : FileIO (Handle m) () ()

     ReadLine  : FileIO (Handle Read) (Handle Read) String
     WriteLine : String -> FileIO (Handle Write) (Handle Write) ()
     EOF       : FileIO (Handle Read) (Handle Read) Bool

instance Effective FileIO IO where
    runEffect () (Open fname m) k = do h <- openFile fname m; k (FH h) ()
    runEffect (FH h) Close      k = do closeFile h; k () ()
    runEffect (FH h) ReadLine        k = do str <- fread h; k (FH h) str
    runEffect (FH h) (WriteLine str) k = do fwrite h str; k (FH h) ()
    runEffect (FH h) EOF             k = do e <- feof h; k (FH h) e

FILE_IO : Type -> EFF IO
FILE_IO t = MkEff t FileIO %instance

open : String -> (m : Mode) -> MEff [FILE_IO ()] [FILE_IO (Handle m)] ()
open f m = effect (Open f m)

close : MEff [FILE_IO (Handle m)] [FILE_IO ()] ()
close = effect Close

readLine : Eff [FILE_IO (Handle Read)] String
readLine = effect ReadLine

writeLine : String -> Eff [FILE_IO (Handle Write)] ()
writeLine str = effect (WriteLine str)

eof : Eff [FILE_IO (Handle Read)] Bool
eof = effect EOF




