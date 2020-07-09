module VarsAndSubs where 

import Control.Monad 
import Control.Monad.Identity
import Control.Monad.Trans.State.Strict 
import qualified Data.Set as S 
import qualified Data.Map as M 
import qualified Data.Sequence as Seq 
import SDPLTerms 
import SyntaxStructure ()

type ST s m a = StateT s m a
type St s a = StateT s Identity a

-- sub m x n == n[m/x]  
unsafeSubTrace :: (Eq v) => Tracev a v -> v -> Tracev a v -> Tracev a v
unsafeSubTrace a t b = case b of 
    TVar z -> if z == t then a else TVar z 
    m@(TConst m') -> m
    TZero  -> TZero
    (TSum m n) -> TSum (unsafeSubTrace a t m) (unsafeSubTrace a t n)
    (TOp f arg) -> TOp f (unsafeSubTrace a t arg)
    (TLet r m n) -> TLet r  (unsafeSubTrace a t m) (unsafeSubTrace a t n)
    TNil -> TNil 
    TPair   m n -> TPair   (unsafeSubTrace a t m) (unsafeSubTrace a t n)
    TFst   m -> TFst   (unsafeSubTrace a t m)
    TSnd   m -> TSnd   (unsafeSubTrace a t m)

freevars :: Ord v => Rawv a v -> S.Set v 
freevars t = case t of 
    Var x -> S.singleton x
    Const a -> S.empty 
    Zero -> S.empty 
    m :+ n -> (freevars m) `S.union` (freevars n)
    Op f m -> freevars m 
    Let x m n -> (freevars m) `S.union` ((freevars n) S.\\ (S.singleton x))
    Nil -> S.empty  
    Pair m n -> (freevars m) `S.union` (freevars n)
    Fst m -> freevars m 
    Snd m -> freevars m 
    If b m n -> (freevarsb b) `S.union` (freevars m) `S.union` (freevars n)
    -- We actually know by typing that x is the unique freevariable in x and m 
    -- But we are going to relax this in future versions
    While x b m -> (S.singleton x) `S.union` (freevarsb b) `S.union` (freevars m)
    RD x m a v -> ((freevars m) S.\\ (S.singleton  x)) `S.union` (freevars a) `S.union` (freevars v)
    Call f m -> freevars m

freevarsb :: Ord v => BRawv a v -> S.Set v  
freevarsb t = case t of 
    RTrue -> S.empty
    RFalse -> S.empty 
    P p m -> freevars m



data CountMap = CM {counter :: Int, varmap :: M.Map String Int}

-- This program will convert all variable names to integers in a way that matches the original declaration structure exactly. 
-- For example x + x ~~> 1 + 1.  This will even work across the program: f(x)=x   g(x)=x ~~> f(1)=1 g(1)=1.  While we do this, 
-- we will also build up our list of freevariables with the new variable names to avoid requiring a second call.
brawStringToInt ::  (Monad m) => BRaw a -> ST CountMap m (BRawI a,S.Set Int)
brawStringToInt t = case t of 
    RTrue -> return (RTrue,S.empty )
    RFalse -> return (RFalse,S.empty)
    P p m -> do 
        (m',free) <- rawStringToInt m 
        return (P p m',free)

{-
The purpose of this function is to abstract a common operation:
  1) check to see if a name is in the varmap 
  2) If not add it, update the counter and varmap, and return the translated name
  3) If so return the name 
-}
addName :: (Monad m) => String -> ST CountMap m Int
addName name = do 
    names <- gets varmap  
    case M.lookup name names of 
        Just translatedName -> return translatedName 
        Nothing -> do 
            -- if the name isn't there, get a freshvariable for the new name, store the translation, update the counter, return the name 
            newname <- gets counter 
            modify $ \s -> s {counter = succ newname}
            modify $ \s -> s {varmap = M.insert name newname  names}
            return newname

{-# INLINABLE addName #-}

-- I think it may be wise for efficiency reasons to have a rawStringToInt like the original one, and a special one used just by the interpreter. 
-- We don't need to compute the freevariables of the term, or anything else, as long as we're not inferring types.  For now we're being inefficient.

rawStringToInt :: (Monad m) => Raw a -> ST CountMap m (RawI a,S.Set Int)
rawStringToInt trem = case trem of 
    Var v -> do 
        v' <- addName v 
        return (Var v',S.singleton v')
    Const a -> return (Const a,S.empty )
    Zero -> return (Zero,S.empty)
    m :+ n -> do 
        (m',freem) <- rawStringToInt m 
        (n',freen) <- rawStringToInt n 
        return (m' :+ n', freem `S.union` freen)
    Op f m -> do 
        (m',freem) <- rawStringToInt m 
        return (Op f m',freem)
    Let v m n -> do 
        v' <- addName v 
        (m',freem) <- rawStringToInt m 
        (n',freen) <- rawStringToInt n 
        return (Let v' m' n',freem `S.union` (freen S.\\ S.singleton v'))
    Nil -> return (Nil,S.empty )
    Pair m n -> do 
        (m',freem) <- rawStringToInt m
        (n',freen) <- rawStringToInt n
        return (Pair m' n',freem `S.union` freen)
    Fst m -> rawStringToInt m
    Snd m -> rawStringToInt m
    If b m n -> do 
        (b',freeb) <- brawStringToInt b 
        (m',freem) <- rawStringToInt m 
        (n',freen) <- rawStringToInt n 
        return (If b' m' n', freeb `S.union` freem `S.union` freen)
    While x b m -> do 
        x' <- addName x 
        (b',freeb) <- brawStringToInt b 
        (m',freem) <- rawStringToInt m 
        return (While x' b' m',(S.singleton x') `S.union` freeb `S.union` freem)
    RD x m a v -> do 
        x' <- addName x 
        (m',freem) <- rawStringToInt m 
        (a',freea) <- rawStringToInt a 
        (v',freev) <- rawStringToInt v 
        return (RD x' m' a' v',(freem S.\\ S.singleton x') `S.union` freea `S.union` freev)
    Call f m -> do 
        (m',freem) <- rawStringToInt m 
        return (Call f m',freem) 

-- rawToStringTotal converts a rawterm to an integer raw term, tells you what its freevariables are 
-- and tells you what the next freshvariable would have been 
rawStringToIntTotal :: Raw a -> (RawI a,S.Set Int,Int)
rawStringToIntTotal trem = 
    let ((trem',freetrem),fresh) = runIdentity (runStateT (rawStringToInt trem) CM {counter =0, varmap = M.empty}) in 
    (trem',freetrem,counter fresh)


rawStringToIntTotalWithFresh :: Raw a -> Int -> (RawI a,S.Set Int,Int)
rawStringToIntTotalWithFresh trem seed = 
    let ((trem',freetrem),fresh) = runIdentity (runStateT (rawStringToInt trem) CM {counter =seed, varmap = M.empty}) in 
    (trem',freetrem,counter fresh)

-- In order to create a ProgI, we will, at parse time, convert the functions 
-- before creating function closures around them.  This will ensure that 
-- rather than closing the term, and then later releasing the variable, and closing it again,
-- we close it only once.  Before continuing with typer inference, we will rework our interpreter 
-- to make use of the int terms.  As well as the parser.
-- One thing to get a little nervous about now though is that ints are a bounded type.  So if we do 2^32-1 = 4,294,967,295 freshVar calls, we could roll over.  
-- That might seem like a lot, but it really might not be.  May need to switch to integer instead.
rawFuncStringInt :: (Monad m) => (String,String,Raw a) -> ST CountMap m (FuncIClosure a)
rawFuncStringInt (fname,farg,fbody) = do 
    farg' <- addName farg 
    (fbody',_) <- rawStringToInt fbody 
    return $ (makeClosed fbody' farg') 

-- functions definitions cannot have freevariables.
rawFuncsStringInt :: (Monad m) => [(String,String,Raw a)] -> ST CountMap m (ProgI a)
rawFuncsStringInt [] = return M.empty
rawFuncsStringInt (f@(fname,_,_):funs) = do 
    f' <- rawFuncStringInt f
    funs' <- rawFuncsStringInt funs 
    return $ M.insert fname f' funs'

-- here we return the translated program and the next freshvariable 
rawFuncsStringIntTotal :: [(String,String,Raw a)] -> (ProgI a,Int)
rawFuncsStringIntTotal funs = 
    let (prog,fresh) = runIdentity (runStateT (rawFuncsStringInt funs) (CM {counter = 0, varmap = M.empty}) ) in 
    (prog,counter fresh)
-- return $ (funName,makeClosed body formalArg)

makeClosed :: Eq v => Rawv a v -> v -> (v -> Rawv a v)
makeClosed trem closingvar formalarg = case trem of -- purposefully misspelled to prevent clash 
    Var v -> if closingvar == v then Var formalarg else Var v
    Const a -> Const a 
    Zero -> Zero
    m :+ n -> (makeClosed m closingvar formalarg) :+ (makeClosed n closingvar formalarg)
    Op f m -> Op f (makeClosed m closingvar formalarg)
    {-
    By our typing rules we have a variable condition.  In any term Let y = m in n, we have that y is not free in m.  Thus if closingvar == y, then there is nothing to change in m.  
    Also, since y is bound in n, if closingvar == y there is nothing to change in n.  Thus if y==closingvar, the term is left unmodified.  Otherwise, we need to close the closingvars 
        in both m and n.
    -}
    Let y  m n -> case closingvar == y of 
        True -> Let y  m n 
        False -> Let y  (makeClosed m closingvar formalarg) (makeClosed n closingvar formalarg)
    Nil -> Nil
    Pair   m n -> Pair   (makeClosed m closingvar formalarg) (makeClosed n closingvar formalarg)
    Fst   m -> Fst   (makeClosed m closingvar formalarg)
    Snd   m -> Snd   (makeClosed m closingvar formalarg)
    If b m n -> If (makeClosedB b closingvar formalarg) (makeClosed m closingvar formalarg) (makeClosed n closingvar formalarg)
    -- x:A \proves f:A x:A \proves b ==> x:A \proves while x A b f : A has x free.  However, x tells us the variable we are closing. 
    -- Then we have two possibilities
    -- 1)  f(x) = (...) while x A b do f ~~> in which case we're using the function to evaluate the whileloop 
    -- 2)  f(x) = (...) let z = b in (...) while z B[x] do f [x]
    -- I actually claim that in the latter case we may skip over.  This is because SDPL is so strict about while-loops, a while-loop 
    -- can only be formed with respect to a unique freevariable. 
    -- To do something like f(n) = let i=0 in while (i < n) do m, we would actually have to 
    -- do something much more verbose like f(n) = let iAndN = (0,n) in while iAndN (fst(iAndN) < snd(iAndN)) do m[fst(iAndN)/i,snd(iAndN)/n]
    -- In a future release we will relax this language to allow functions to be called with lists of arguments, and we will allow forming 
    -- while-loops in simple slices.  That is, we will allow specifying variables that will be iteratedover in a while-loop.  This will 
    -- require a bit more care.
    -- At any rate, our typing rules will not allow us to form a while x. b do f expression where b and f have variables that are not x. 
    While cont  b f -> case cont == closingvar of 
        False -> While cont  b f  
        True -> While formalarg  (makeClosedB b closingvar formalarg) (makeClosed f closingvar formalarg)
    {-
    Similarly to let expressions, any formation rd(y.m)(a)*v has the assumption that y is not in a or v.  Thus if closingvar == y 
    there is nothing to do because closing var is in neither of those terms.  Also, y is bound in m, thus there is nothing to change in m in this case either.
    Otherwise, all 3 terms need to be changed.
    -}
    RD x   m a v -> case x == closingvar of 
        True -> RD x   m a v 
        False -> RD x   (makeClosed m closingvar formalarg) (makeClosed a closingvar formalarg) (makeClosed v closingvar formalarg)
    Call f m -> Call f (makeClosed m closingvar formalarg)

makeClosedB :: Eq v => BRawv a v -> v -> (v -> BRawv a v)
makeClosedB trem closingvar formalarg = case trem of 
    RTrue -> RTrue 
    RFalse -> RFalse 
    P p m -> P p (makeClosed m closingvar formalarg)

getFresh :: (Enum s,Monad m) => ST s m s 
getFresh = do 
    s <- get
    modify succ 
    return s

bvRenameTerm :: (Enum v,Eq v) => Rawv a v -> St v (Rawv a v)
bvRenameTerm t = case t of 
    Var x -> return $ Var x 
    Const a -> return $ Const a 
    Zero -> return Zero 
    m :+ n -> do 
        m' <- bvRenameTerm m 
        n' <- bvRenameTerm n 
        return $ m' :+ n' 
    Op f m -> do 
        m' <- bvRenameTerm m 
        return $ Op f m' 
    Let x m n -> do 
        x' <- getFresh 
        m' <- bvRenameTerm m
        -- makeClosed term x is often used to close a variable in a term.  But 
        -- makeClosed term x y is nothing more than replacing all the free x in term with y
        let n' = makeClosed n x x' 
        n'' <- bvRenameTerm n' 
        return $ Let x' m' n''
    Nil -> return Nil 
    Pair m n -> do 
        m' <- bvRenameTerm m 
        n' <- bvRenameTerm n 
        return $ Pair m' n'  
    Fst m -> do 
        m' <- bvRenameTerm m 
        return $ Fst m' 
    Snd m -> do 
        m' <- bvRenameTerm m 
        return $ Snd m'
    If b m n -> do 
        b' <- bvRenameBTerm b 
        m' <- bvRenameTerm m 
        n' <- bvRenameTerm n 
        return $ If b' m' n' 
    While x b m -> do 
        -- we must assume that this is run with the largest freevariable seed or this will fail here 
        b' <- bvRenameBTerm b 
        m' <- bvRenameTerm m 
        return $ While x b' m' 
    RD x m a v -> do 
        x' <- getFresh 
        a' <- bvRenameTerm a 
        v' <- bvRenameTerm v 
        let m' = makeClosed m x x' 
        m'' <- bvRenameTerm m' 
        return $ RD x' m'' a' v'
    Call f m -> do 
        m' <- bvRenameTerm m 
        return $ Call f m'

bvRenameBTerm ::  (Enum v,Eq v) => BRawv a v -> St v (BRawv a v)
bvRenameBTerm trem = case trem of 
    RTrue -> return  RTrue 
    RFalse -> return RFalse
    P p m -> do 
        m' <- bvRenameTerm m 
        return $ P p m' 

-- bvRenameFuncClosure :: (Enum v,Eq v) => FuncGenericClosure a v -> St v (FuncGenericClosure a v)
-- to prepare a program for type checking we assign all functional arguments with fresh variable names.
prepareTInferFun :: (Enum v,Eq v) => String -> FuncGenericClosure a v -> St v (String,v,Rawv a v)
prepareTInferFun fname f = do 
    arg <- getFresh
    -- note that in body the arg variable is assumed to be fresh by construction
    let body = f arg 
    body' <- bvRenameTerm body 
    return (fname,arg,body')

prepareTInferProg :: (Enum v,Eq v) => ProgGeneric a v -> St v [(String,v,Rawv a v)]
prepareTInferProg prog = mapM (uncurry prepareTInferFun) $ M.toList prog
    
--  All that is left to do is write the actual type inferencing code.

-- data Rawv a v = 
--     Var v 
--     | Const a 
--     | Zero 
--     | (Rawv a v) :+ (Rawv a v)
--     | Op Sigma (Rawv a v)
--     | Let v (Rawv a v) (Rawv  a v) 
--     | Nil 
--     | Pair (Rawv a v)  (Rawv a v) 
--     | Fst (Rawv a v)
--     | Snd (Rawv a v)
--     | If (BRawv a v) (Rawv a v) (Rawv a v)
--     | While v (BRawv a v) (Rawv a v)
--     | RD v (Rawv a v) (Rawv a v) (Rawv a v)
--     | Call v (Rawv a v)


-- data BRawv a v =
--     RTrue 
--     | RFalse 
--     | P Pred (Rawv a v)

    -- data Tracev a v = 
    -- TVar v
    -- | TConst !a 
    -- | TZero 
    -- | TSum !(Tracev a v) !(Tracev a v)
    -- | TOp Sigma !(Tracev a v)
    -- | TLet v !(Tracev a v) !(Tracev a v)
    -- | TNil 
    -- | TPair !(Tracev a v) !(Tracev a v)
    -- | TFst !(Tracev a v) !(Tracev a v)
    -- | TSnd !(Tracev a v) !(Tracev a v) 

safeSubTrace = undefined

-- effective freevars (these are freevariables that can witnessed differentiated with respect to)
-- e.g. d(fst(x,y)/dy) will be 0 and y is not an effective freevar in fst(x,y)