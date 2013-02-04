module Exception

import Eff_mutable
import System

%access public

data Exception : Type -> Type -> Type -> Type -> Type where
     Raise : a -> Exception a () () b 

instance Effective (Exception a) Maybe where
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
     
instance Effective (Exception a) IOExcept where
     runEffect _ (Raise e) k = ioM (return Nothing)

instance Show a => Effective (Exception a) IO where
     runEffect _ (Raise e) k = do print e
                                  believe_me (exit 1)

EXCEPTION : Type -> EFF 
EXCEPTION t = MkEff () (Exception t) 

raise : a -> Eff m [EXCEPTION a] b
raise err = effect (Raise err)

