module Random

import Eff_mutable

%access public

data Random : Type -> Type -> Type -> Type where
     getRandom : Random Int Int Int

instance Monad m => Effective Random m where
     runEffect seed getRandom k
              = let seed' = 1664525 * seed + 1013904223 in
                    k seed' seed'
                    
RND : Monad m => EFF m
RND = MkEff Int Random %instance

rndInt : Int -> Int -> GenEff [RND] Int
rndInt lower upper = do v <- effect getRandom 
                        return (v `mod` (upper - lower) + lower)


