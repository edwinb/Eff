module Effect.Random

import Effects

data Random : Type -> Type -> Type -> Type where
     getRandom : Random Int Int Int

using (m : Type -> Type)
  instance Effective Random m where
     runEffect seed getRandom k
              = let seed' = 1664525 * seed + 1013904223 in
                    k seed' seed'
                    
RND : EFF
RND = MkEff Int Random

rndInt : Int -> Int -> Eff [RND] Int
rndInt lower upper = do v <- getRandom 
                        return (v `mod` (upper - lower) + lower)


