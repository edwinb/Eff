module Exception

import Eff
import System
import IOExcept

data Exception : Type -> Type -> Type -> Type -> Type where
     Raise : a -> Exception a () () b 

instance Effective (Exception a) Maybe where
     runEffect _ (Raise e) k = Nothing

instance Show a => Effective (Exception a) IO where
     runEffect _ (Raise e) k = do print e
                                  believe_me (exit 1)

instance Effective (Exception a) (IOExcept a) where
     runEffect _ (Raise e) k = ioM (return (Left e))

EXCEPTION : Type -> EFF 
EXCEPTION t = MkEff () (Exception t) 

raise : a -> Eff [EXCEPTION a] b
raise err = effect (Raise err)

instance Catchable Maybe () where
    catch Nothing  h = h ()
    catch (Just x) h = Just x

instance Catchable (Either a) a where
    catch (Left err) h = h err
    catch (Right x)  h = (Right x)

instance Catchable (IOExcept err) err where
    catch (ioM prog) h = ioM (do p' <- prog
                                 case p' of
                                      Left e => let ioM he = h e in he
                                      Right val => return (Right val))









-- TODO: Catching exceptions mid program?
-- probably need to invoke a new interpreter

-- possibly add a 'handle' to the Eff language so that an alternative
-- handler can be introduced mid interpretation?

