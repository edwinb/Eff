module Exception

import Eff
import System

data Exception : Type -> Type -> Type where
     Raise : a -> Exception a b 

instance Effective () (Exception a) Maybe where
     runEffect _ (Raise e) k = Nothing

instance Show a => Effective () (Exception a) IO where
     runEffect _ (Raise e) k = do putStrLn (show e)
                                  believe_me (exit 1)

namespace Maybe_Exception
  EXCEPTION : Type -> EFF Maybe
  EXCEPTION t = MkEff (Exception t) %instance

  raise : a -> Eff [EXCEPTION a] b
  raise err = effect $ Raise err

namespace IO_Exception
  IO_EXCEPTION : EFF IO
  IO_EXCEPTION = MkEff (Exception String) %instance

  io_raise : Show a => a -> Eff [IO_EXCEPTION] b
  io_raise err = effect (Raise (show err))

