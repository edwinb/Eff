module State

import Eff

data State : Type -> Type -> Type where
     Get :      State a a
     Put : a -> State a ()

instance Monad m => Effective a (State a) m where
     runEffect st Get       k = k st st
     runEffect st (Put new) k = k new ()

STATE : Monad m => Type -> EFF m
STATE t = MkEff (State t) %instance

get : GenEff [STATE x] x
get = effect Get

put : x -> GenEff [STATE x] ()
put x = effect (Put x)
