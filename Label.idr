module Label

import Effective
import Eff_mutable

infix 5 :::, :-

data Label : a -> Effect -> Effect where
     Labelled :  (x : a) -> e res res' b -> Label x e res res' b

using (ty : Type, l : ty) 
  instance Effective e m => Effective (Label l e) m where
       runEffect res (Labelled _ eff) k = runEffect res eff k

(:::) : Monad m => a -> EFF m -> EFF m
(:::) x (MkEff r eff c) = MkEff r (Label x eff) %instance

-- (:-) : (l : ty) -> MEff [a] [b] t -> MEff [l ::: a] [l ::: b] t
-- (:-) {a = MkEff res e i} {b = MkEff res' e i}
--      l (effect {prf = Here} {xs = [MkEff res e i]} eff) 
--      = effect {prf = Here} {xs = [MkEff res (Label _ (MkEff res e i))]} 
--           (Labelled _ eff)
     


