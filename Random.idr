module Random

import Eff

data Random : Type -> Type where
     getRandom : Random Int

instance Monad m => Effective Int Random m where
     runEffect seed getRandom k
              = let seed' = 1664525 * seed + 1013904223 in
                    k seed' seed'
                    
RND : Monad m => EFF m
RND = MkEff Random %instance

rndInt : Int -> Int -> GenEff [RND] Int
rndInt lower upper = do v <- effect $ getRandom 
                        return (v `mod` (upper - lower) + lower)


