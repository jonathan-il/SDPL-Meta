module LambdaReducer where 

import qualified Data.ByteString as B
import qualified Data.Set as S
import qualified Data.Sequence as Seq

data Lam a = 
    Var a 
    | Abst a (Lam a)
    | App (Lam a) (Lam a) 

fv :: (Ord a) => Lam a -> S.Set a 
fv (Var x) = S.singleton  x 
fv (Abst x m) = S.delete x (fv m)
fv (App m n) = S.union (fv m) (fv n)

type DS = Seq.Seq Direction
data Direction = No | Left | Right | Straight | Both

data LamDirector a = 
    DVar a 
    | DBvar 
    | DAbst (LamDirector a) DS
    | DApp (LamDirector a) (LamDirector a) DS

compile :: (Ord a) => Lam a -> LamDirector a 
compile m = let freem = fv m in compileWith m freem (Seq.fromList (S.toList freem))

compileWith :: (Ord a) => Lam a -> S.Set a -> Seq.Seq a -> LamDirector a 
compileWith m freem boundlist = case m of 
    Var x -> if S.member x freem then DVar x else DBvar 
    App m n -> 
        let