module Random

import Eff

data Random : Type -> Type -> Type -> Type where
     getRandom : Random Int Int Int

instance Monad m => Effective Random m where
     runEffect seed getRandom k
              = let seed' = 1664525 * seed + 1013904223 in
                    k seed' seed'
                    
RND : EFF
RND = MkEff Int Random

rndInt : Int -> Int -> Eff [RND] Int
rndInt lower upper = do v <- effect getRandom 
                        return (v `mod` (upper - lower) + lower)


