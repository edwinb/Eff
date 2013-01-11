module Exception

import Eff_mutable
import System

%access public

data Exception : Type -> Type -> Type where
     Raise : a -> Exception a b 

instance Effective () (Exception a) Maybe where
     runEffect _ (Raise e) k = Nothing

data IOExcept : Type -> Type where
     ioM : IO (Maybe a) -> IOExcept a

instance Functor IOExcept where
     fmap f (ioM fn) = ioM (fmap (fmap f) fn)

instance Applicative IOExcept where
     pure x = ioM (pure (pure x))
     (ioM f) <$> (ioM a) = ioM (do f' <- f; a' <- a
                                   return (f' <$> a'))

instance Monad IOExcept where
     return = pure
     (ioM x) >>= k = ioM (do x' <- x;
                             case x' of
                                  Just a => let (ioM ka) = k a in
                                                ka
                                  Nothing => return Nothing)
     
instance Effective () (Exception a) IOExcept where
     runEffect _ (Raise e) k = ioM (return Nothing)

instance Show a => Effective () (Exception a) IO where
     runEffect _ (Raise e) k = do print e
                                  believe_me (exit 1)

namespace Maybe_Exception
  EXCEPTION : Type -> EFF Maybe
  EXCEPTION t = MkEff (Exception t) %instance

  raise : a -> Eff [EXCEPTION a] b
  raise err = effect (Raise err)

namespace IO_Exception
  IO_EXCEPTION : EFF IO
  IO_EXCEPTION = MkEff (Exception String) %instance

  io_raise : Show a => a -> Eff [IO_EXCEPTION] b
  io_raise err = effect (Raise (show err))

