module Main

import State
import Exception
import Random

data Expr = Var String
          | Val Int
          | Add Expr Expr
          | Random Int

eval : Expr -> Eff [EXCEPTION String, RND, STATE (List (String, Int))] Int
eval (Var x) = do vs <- call get
                  case lookup x vs of
                       Nothing => call (raise ("No such variable " ++ x))
                       Just val => return val
eval (Val x) = return x
eval (Add l r) = [| eval l + eval r |]
eval (Random upper) = do val <- call (rndInt 0 upper)
                         return val

runEval : List (String, Int) -> Expr -> Maybe Int
runEval args expr = run [(), 123456, args] (eval expr)
