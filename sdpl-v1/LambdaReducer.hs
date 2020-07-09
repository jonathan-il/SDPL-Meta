module LambdaReducer where 

data Lam a = 
    Var a 
    | Abst (Lam a -> Lam a)
    | App (Lam a) (Lam a) 

{-
Code golfing a very small lambda calculus beta reducer by hacking the lambda calculus type.
-}

-- Beta reductions towards weak head normal form.
-- It's weak because there may be reductions possible under a lambda, but we don't
-- Consider them.
findAndFireRedex :: Lam a -> (Bool,Lam a)
findAndFireRedex t = case t of 
    Var x -> (False,Var x)
    (App (Abst h) m) -> (True,h m)
    -- i think this rule allows for 
    (App m n) -> 
        let
            (b1,m') = findAndFireRedex m 
            (b2,n') = findAndFireRedex n 
        in 
            (b1 || b2,App m' n')
    (Abst k) -> (False,Abst k)

reduceToWHNF :: Lam a -> Lam a 
reduceToWHNF t = case findAndFireRedex t of 
    (True,m) -> reduceToWHNF m 
    (False,n) -> n


{-
From Martin Erwig
-}
deugly :: String -> String
deugly s@[c]                     = s
deugly ('"':s)  | last s == '"'  = init s
            | otherwise      = s
deugly ('\'':s) | last s == '\'' = init s
            | otherwise      = s
deugly s                         = s