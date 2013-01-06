module Random

import Eff

data Random : Type -> Type where
     RNDInt : Int -> Int -> Random Int

instance Monad m => Effective Int Random m where
     runEffect seed (RNDInt lower upper) k
              = let seed' = 1664525 * seed + 1013904223 in
                    k seed' (seed' `mod` (upper - lower) + lower)

RND : Monad m => EFF m
RND = MkEff Random %instance

rndInt : Monad m => Int -> Int -> Eff [RND] {m} Int
rndInt lower upper = effect $ RNDInt lower upper


