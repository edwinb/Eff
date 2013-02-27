module Main

import Effect.State
import Effect.Exception
import Effect.Random
import Effect.StdIO

data Expr = Var String
          | Val Int
          | Add Expr Expr
          | Random Int

Evaluator : Type -> Type
Evaluator t 
   = Eff IO [EXCEPTION String, RND, STATE (List (String, Int)), STDIO] t

test : Evaluator Int
test = do vs <- get
          return 0

eval : Expr -> Evaluator Int
eval (Var x) = do vs <- get
                  case lookup x vs of
                        Nothing => raise ("No such variable " ++ x)
                        Just val => return val
eval (Val x) = return x
eval (Add l r) = [| eval l + eval r |]
eval (Random upper) = do val <- rndInt 0 upper
                         putStrLn (show val)
                         return val

testExpr : Expr
testExpr = Add (Add (Var "foo") (Val 42)) (Random 100)

runEval : List (String, Int) -> Expr -> IO Int
runEval args expr = run [(), 123456, args, ()] (eval expr)

main : IO ()
main = do putStr "Number: "
          x <- getLine
          val <- runEval [("foo", cast x)] testExpr
          putStrLn $ "Answer: " ++ show val


