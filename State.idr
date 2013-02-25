module State

import Eff

%access public

data State : Type -> Effect where
     Get :      State a a a a
     Put : a -> State a a a ()

using (m : Type -> Type)
  instance Effective (State a) m where
     runEffect st Get     k = k st st
     runEffect st (Put n) k = k n ()

STATE : Type -> EFF
STATE t = MkEff t (State t)

get : Eff [STATE x] x
get = Get 

put : x -> EffM m [STATE x] [STATE x] ()
put x = Put x

update : (x -> x) -> Eff [STATE x] ()
update f = do val <- get
              put (f val) 

-- Following leads to neater code, but can't be used in a HOF:

-- syntax get = effect Get
-- syntax put [x] = effect (Put x)
