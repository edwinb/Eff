module State

import Eff

%access public

data State : Type -> Effect where
     Get :      State a a a a
     Put : a -> State a a a ()

instance Monad m => Effective (State a) m where
     runEffect st Get       k = k st st
     runEffect st (Put new) k = k new ()

STATE : Type -> EFF
STATE t = MkEff t (State t)

get : Eff [STATE x] x
get = effect Get 

put : Monad m => x -> EffM m [STATE x] [STATE x] ()
put x = effect (Put x)

-- Following leads to neater code, but can't be used in a HOF:

-- syntax get = effect Get
-- syntax put [x] = effect (Put x)
