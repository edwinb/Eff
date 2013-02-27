module Effect.State

import Effects

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

get : Eff m [STATE x] x
get = Get 

put : x -> Eff m [STATE x] ()
put x = Put x

update : (x -> x) -> Eff m [STATE x] ()
update f = do val <- get
              put (f val) 

