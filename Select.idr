module Select

import Exception

data Selection : Effect where
     Select : List a -> Selection () () a

instance Effective Selection Maybe where
     runEffect _ (Select xs) k = tryAll xs where
         tryAll [] = Nothing
         tryAll (x :: xs) = case k () x of
                                 Nothing => tryAll xs
                                 Just v => Just v

instance Effective Selection List where
     runEffect r (Select xs) k = concatMap (k r) xs
     
SELECT : EFF
SELECT = MkEff () Selection

select : List a -> Eff [SELECT] a
select xs = effect (Select xs)

