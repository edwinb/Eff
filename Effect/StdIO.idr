module Effect.StdIO

import Effects
import Control.IOExcept

data StdIO : Effect where
     PutStr : String -> StdIO () () ()
     GetStr : StdIO () () String

instance Effective StdIO IO where
    runEffect () (PutStr s) k = do putStr s; k () ()
    runEffect () GetStr     k = do x <- getLine; k () x 

instance Effective StdIO (IOExcept a) where
    runEffect () (PutStr s) k = do ioe_lift (putStr s); k () ()
    runEffect () GetStr     k = do x <- ioe_lift getLine; k () x 

STDIO : EFF
STDIO = MkEff () StdIO

putStr : Effective StdIO e => String -> EffT e [STDIO] ()
putStr s = PutStr s

putStrLn : Effective StdIO e => String -> EffT e [STDIO] ()
putStrLn s = putStr (s ++ "\n")

getStr : Effective StdIO e => EffT e [STDIO] String
getStr = GetStr

