module State

import Eff_mutable
import Label

%access public

data State : Type -> Effect where
     Get :      State a a a a
     Put : a -> State a a a ()

instance Monad m => Effective (State a) m where
     runEffect st Get       k = k st st
     runEffect st (Put new) k = k new ()

STATE : Monad m => Type -> EFF m
STATE t = MkEff t (State t) %instance

get : GenEff [STATE x] x
get = effect Get 

put : Monad m => x -> MEff [STATE x] [STATE x] {m} ()
put x = effect (Put x)

getFrom : (l : a) -> GenEff [l ::: STATE x] x
getFrom l = effect (Labelled l Get)

putTo : (l : a) -> x -> GenEff [l ::: STATE x] ()
putTo l x = effect (Labelled l (Put x))

-- Following leads to neater code, but can't be used in a HOF:

-- syntax get = effect Get
-- syntax put [x] = effect (Put x)
