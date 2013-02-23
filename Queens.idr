module Main

import Eff
import Select

no_attack : (Int, Int) -> (Int, Int) -> Bool
no_attack (x, y) (x', y') 
   = x /= x' && y /= y' && abs (x - x') /= abs (y - y')

rowsIn : Int -> List (Int, Int) -> List Int
rowsIn col qs = [ x | x <- [1..8], all (no_attack (x, col)) qs ]

addQueens : Int -> List (Int, Int) -> Eff [SELECT] (List (Int, Int)) 
addQueens 0   qs = return qs
addQueens col qs = do row <- lift (select (rowsIn col qs))
                      addQueens (col - 1) ((row, col) :: qs)

getQueens : Maybe (List (Int, Int))
getQueens = run [()] (addQueens 8 [])

main : IO ()
main = case getQueens of
            Nothing => putStrLn "No solution"
            Just qs => putStrLn ("Solution: " ++ show qs)
