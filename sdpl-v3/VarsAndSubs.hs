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

{-
When substituting a for t in b, the free variable t in b will be gone.  However, any variable that is 
free in a will now be free wherever x was free.  Thus we must update all director strings.
-}
unsafeSubTraceD :: (Ord v,Eq v) => Tracevd a v (S.Set v) -> v -> S.Set v -> Tracevd a v (S.Set v) -> Tracevd a v (S.Set v)
unsafeSubTraceD a t freea b = case b of 
    DTVar z -> if z == t then a else DTVar z 
    m@(DTConst _) -> m 
    DTZero  -> DTZero 
    DTSum (m,freem) (n,freen) -> DTSum (unsafeSubTraceD a t freea m,updateVars freem t freea) (unsafeSubTraceD a t freea n,updateVars freen t freea)
    DTOp f (arg,freearg) -> DTOp f (unsafeSubTraceD a t freea arg,updateVars freearg t freea)
    DTLet r (m,freem) (n,freen) -> DTLet r (unsafeSubTraceD a t freea m,updateVars freem t freea) (unsafeSubTraceD a t freea n,updateVars freen t freea)
    DTNil -> DTNil 
    DTPair (m,freem) (n,freen) -> DTPair (unsafeSubTraceD a t freea m,updateVars freem t freea) (unsafeSubTraceD a t freea n,updateVars freen t freea) 
    DTFst (m,freem) -> DTFst (unsafeSubTraceD a t freea m,updateVars freem t freea)
    DTSnd (m,freem) -> DTSnd (unsafeSubTraceD a t freea m,updateVars freem t freea)


-- We use this above.  If s constains t then join in a, removing t, else it's just s. 
updateVars s t a = if S.member t s then (S.delete t s) `S.union` a else s

-- This function is only sound when used as a check to see if x is differentiably free in a term m. 
-- That means that we can disregard if it occurs in boolean terms. 
isFreeInDTerm :: (Ord v) => v ->  (Rawvd a v) (S.Set v) -> Bool
isFreeInDTerm searchv trem = case trem of 
    DVar x -> searchv == x 
    DConst _ -> False 
    DZero -> False 
    DSum (_,freem) (_,freen) -> (S.member searchv freem) || (S.member searchv freen)
    DOp f (_,freem) -> S.member searchv freem
    -- by construction, then if I'm searching for x, it's not free because x \not\in freem and it's bound in freen.  
    -- We should be renaming our bound variables then.  Though.
    DLet x (_,freem) (_,freen) -> if x == searchv then False else (S.member searchv freem) || (S.member searchv freen)
    DNil -> False 
    DPair (_,freem) (_,freen) -> (S.member searchv freem) || (S.member searchv freen)
    DFst (_,freem) -> S.member searchv freem
    DSnd (_,freem) -> S.member searchv freem
    -- This 
    DIf b (_,freem) (_,freen) -> (S.member searchv freem) || (S.member searchv freen)
    -- We actually know by typing that x is the unique freevariable in x and m 
    -- But we are going to relax this in future versions
    DWhile x b (_,freem) -> if x == searchv then True else S.member searchv freem 
    -- again we need to rename our bound variables as a preprocess step.
    DRD x (_,freem) (_,freea) (_,freev) -> if x == searchv then False else (S.member searchv freem) || (S.member searchv freea) || (S.member searchv freev)
    DCall f (_,freem) -> S.member searchv freem

isFreeInDTrace :: (Ord v) => v -> (Tracevd a v (S.Set v)) -> Bool 
isFreeInDTrace searchv trem = case trem of 
    DTVar x -> searchv == x 
    DTConst _ -> False 
    DTZero -> False 
    DTSum (_,freem) (_,freen) -> (S.member searchv freem) || (S.member searchv freen)
    DTOp f (_,freem) -> S.member searchv freem 
    DTLet x (_,freem) (_,freen) -> if x == searchv then False else (S.member searchv freem) || (S.member searchv freen)
    DTNil -> False 
    DTPair (_,freem) (_,freen) -> (S.member searchv freem) || (S.member searchv freen)
    DTFst (_,freem) -> S.member searchv freem
    DTSnd (_,freem) -> S.member searchv freem




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

freetrace :: Ord v => Tracev a v -> S.Set v 
freetrace trem = case trem of 
    TVar x -> S.singleton x
    TConst a -> S.empty 
    TZero -> S.empty 
    TSum m  n -> (freetrace m) `S.union` (freetrace n)
    TOp f m -> freetrace m 
    TLet x m n -> (freetrace m) `S.union` ((freetrace n) S.\\ (S.singleton x))
    TNil -> S.empty  
    TPair m n -> (freetrace m) `S.union` (freetrace n)
    TFst m -> freetrace m 
    TSnd m -> freetrace m 
    

freevarsb :: Ord v => BRawv a v -> S.Set v  
freevarsb t = case t of 
    RTrue -> S.empty
    RFalse -> S.empty 
    P p m -> freevars m

-- make sure we add pragmas to make everything aggressively specialize
-- create directory terms
convertTermToDTerm :: Ord v => Rawv a v -> RawvDir a v 
convertTermToDTerm = fst . convertTermToDTermFree

convertTermToDTermFree :: Ord v => Rawv a v -> (RawvDir a v,S.Set v)
convertTermToDTermFree trem = case trem of 
    Var x -> (DVar x,S.singleton x)
    Const a -> (DConst a,S.empty)
    Zero -> (DZero,S.empty)
    m :+ n -> case (convertTermToDTermFree m,convertTermToDTermFree n) of 
        (mcon@(m',mfree),ncon@(n',nfree)) -> (DSum mcon ncon,mfree `S.union` nfree)
    Op f m -> let (m',mfree) = convertTermToDTermFree m in (DOp f (m',mfree),mfree)
    Let v m n -> let ((m',mfree),(n',nfree)) = (convertTermToDTermFree m,convertTermToDTermFree n) in (DLet v (m',mfree) (n',nfree),mfree `S.union` (nfree S.\\ S.singleton v))
    Nil -> (DNil,S.empty)
    Pair m n -> let (mcon@(m',mfree),ncon@(n',nfree)) = (convertTermToDTermFree m,convertTermToDTermFree n) in (DPair mcon ncon,S.union mfree nfree)
    -- I think in future versions, we may way to go with a sort of effective freeness.  effective_free fst(m,n) = effective_free m e.g. But this requires more 
    -- runtime substatial, because I don't before things get assembled at runtime into values, terms under fst can get pretty gnarly.  I really do think 
    -- a much better data structure that is updated at runtime is a much better way to go in a more real version. 
    Fst m -> let (m',mfree) = convertTermToDTermFree m in (DFst (m',mfree),mfree)
    Snd m -> let (m',mfree) = convertTermToDTermFree m in (DSnd (m',mfree),mfree)
    If b m n -> let (mconv@(m',mfree),nconv@(n',nfree)) = (convertTermToDTermFree m,convertTermToDTermFree n) in (DIf (convertBTermToDBTerm b) mconv nconv, S.union mfree nfree) 
    While x b m -> let (m',mfree) = convertTermToDTermFree m in (DWhile x (convertBTermToDBTerm b) (m',mfree),S.union mfree (S.singleton x)) 
    RD x m a v -> 
        let (mconv@(_,mfree),aconv@(_,afree),vconv@(_,vfree)) = (convertTermToDTermFree m,convertTermToDTermFree a,convertTermToDTermFree v)
        in (DRD x mconv aconv vconv, (mfree S.\\ (S.singleton x)) `S.union` afree `S.union` vfree)
    Call f m -> let (m',mfree) = convertTermToDTermFree m in (DCall f (m',mfree),mfree)


convertBTermToDBTerm :: BRawv a v -> BRawvd a v (S.Set v)
convertBTermToDBTerm t = case t of 
    RTrue -> DTrue 
    RFalse -> DFalse 
    P p m -> DPred p (oneify m)

-- Put one in boolean terms because free variables don't matter. 
oneify :: Rawv a v -> Rawvd a v (S.Set v)
oneify t = case t of 
    Var x -> DVar x
    Const a -> DConst a 
    Zero -> DZero 
    m :+ n -> DSum (oneify m,S.empty) (oneify n,S.empty)
    Op f m -> DOp f (oneify m,S.empty)
    Let v m n -> DLet v (oneify m,S.empty) (oneify n,S.empty)
    Nil -> DNil 
    Pair m n -> DPair (oneify m ,S.empty) (oneify n,S.empty)
    Fst m -> DFst (oneify m,S.empty)
    Snd m -> DSnd (oneify m,S.empty)
    If b m n -> DIf (convertBTermToDBTerm b) (oneify m,S.empty) (oneify n,S.empty)
    While x b m -> DWhile x (convertBTermToDBTerm b) (oneify m ,S.empty)
    RD x m a v -> DRD x (oneify m, S.empty) (oneify a,S.empty) (oneify v,S.empty)
    Call f m -> DCall f (oneify m,S.empty)



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

-- type RawvDir a v = Rawvd a v (S.Set v)
makeClosedDir :: (Ord v,Eq v) => Rawv a v -> v ->  (v -> RawvDir a v)
makeClosedDir trem closingvar formalarg = fst (makeClosedDirFree trem closingvar formalarg)



makeClosedDirFree :: (Ord v, Eq v) => Rawv a v -> v -> (v -> (RawvDir a v,S.Set v))
makeClosedDirFree trem closingvar formalarg = case trem of 
    Var v -> if closingvar == v then (DVar formalarg,S.singleton v) else (DVar v,S.singleton v)
    Const a -> (DConst a,S.empty)
    Zero -> (DZero,S.empty)
    m :+ n -> let (m'@(_,freem),n'@(_,freen)) = (makeClosedDirFree m closingvar formalarg,makeClosedDirFree n closingvar formalarg) in (DSum m' n',S.union freem freen)
    Op f m -> let m'@(_,freem) = makeClosedDirFree m closingvar formalarg in (DOp f m',freem)
    Let y m n -> case closingvar == y of -- to see why this works see original makeClosed below
        True -> let (m'@(_,freem),n'@(_,freen)) = (convertTermToDTermFree m,convertTermToDTermFree n) in (DLet y m' n', freem `S.union` (freen S.\\ S.singleton y))
        False -> let (m'@(_,freem),n'@(_,freen)) = (makeClosedDirFree m closingvar formalarg,makeClosedDirFree n closingvar formalarg) in (DLet y m' n',freem `S.union` (freen S.\\ S.singleton y))
    Nil -> (DNil,S.empty)
    Pair m n -> let (m'@(_,freem),n'@(_,freen)) = (makeClosedDirFree m closingvar formalarg,makeClosedDirFree n closingvar formalarg) in (DPair m' n',freem `S.union` freen)
    Fst m -> let m'@(_,freem) = makeClosedDirFree m closingvar formalarg in (DFst m',freem)
    Snd m -> let m'@(_,freem) = makeClosedDirFree m closingvar formalarg in (DSnd m',freem)
    If b m n -> let (m'@(_,freem),n'@(_,freen)) = (makeClosedDirFree m closingvar formalarg,makeClosedDirFree n closingvar formalarg) in (DIf (makeClosedBDir b closingvar formalarg) m' n', S.union freem freen)
    While cont b m -> case cont == closingvar of -- to see why this works see original makeClosed below
        False -> let m'@(_,freem) = convertTermToDTermFree m in (DWhile cont (convertBTermToDBTerm b) m',S.union freem (S.singleton cont))
        True -> let m'@(_,freem) = makeClosedDirFree m closingvar formalarg in (DWhile formalarg (makeClosedBDir b closingvar formalarg) m',S.union freem (S.singleton cont))
    RD x m a v -> case x == closingvar of -- to see why this works see original makeClosed below 
        True -> 
            let (mconv@(_,mfree),aconv@(_,afree),vconv@(_,vfree)) = (convertTermToDTermFree m,convertTermToDTermFree a,convertTermToDTermFree v)
            in (DRD x mconv aconv vconv, (mfree S.\\ (S.singleton x)) `S.union` afree `S.union` vfree)
        False -> 
            let (mconv@(_,mfree),aconv@(_,afree),vconv@(_,vfree)) = (makeClosedDirFree m closingvar formalarg,makeClosedDirFree a closingvar formalarg,makeClosedDirFree v closingvar formalarg)
            in (DRD x mconv aconv vconv, (mfree S.\\ (S.singleton x)) `S.union` afree `S.union` vfree)
    Call f m -> let m'@(_,freem) = makeClosedDirFree m closingvar formalarg in (DCall f m',freem)
    
-- This function is for use in the repl.  It totally prepares a term and 
-- makes sure you get a directory term over ints and a new freshvariable name
prepTermStringToDirITotalWithFresh :: Raw a -> Int -> (RawDir a,Int)
prepTermStringToDirITotalWithFresh term seed = 
    let (translated,_,newseed) = rawStringToIntTotalWithFresh term seed 
    in (convertTermToDTerm translated,newseed)

-- This function is for use in the parser.  It totally prepares a list of 
-- (String,String,Raw a) representing (fname,farg,fbody) and converts them all to 
-- (String,Int,RawI a) and then converts them to  ProgDirI a = M.Map String (Int -> RawDir a)
-- rawFuncsStringInt :: (Monad m) => [(String,String,Raw a)] -> ST CountMap m (ProgI a)
rawFuncStringDir :: (Monad m) => (String,String,Raw a) -> ST CountMap m (String,Int,RawI a)
rawFuncStringDir (fname,farg,fbody) = do 
    farg' <- addName farg 
    (fbody',_) <- rawStringToInt fbody 
    return $ (fname,farg',fbody')

-- ProgDirI a
rawFuncsStringDir :: (Monad m) => [(String,String,Raw a)] -> ST CountMap m (ProgDirI a)
rawFuncsStringDir [] = return M.empty 
rawFuncsStringDir (f@(fname,_,_):funs) = do 
    (f',farg',fbody') <- rawFuncStringDir f 
    funs' <- rawFuncsStringDir funs 
    return $ M.insert f' (makeClosedDir fbody' farg') funs'
    -- (makeClosed fbody' farg') 
-- rawFuncsStringInt (f@(fname,_,_):funs) = do 
--     f' <- rawFuncStringInt f
--     funs' <- rawFuncsStringInt funs 
--     return $ M.insert fname f' funs'

{-
Functions have no free variables, so we don't need to supply a seed to this one.  But we still return the next fresh name, 
so that we can prepare terms at the repl easily.

This function is for use in the parser.  It projects a total version of the above and reminds you what the next fresh variable name is.
-}
rawFuncsStringDirTotal :: [(String,String,Raw a)] -> (ProgDirI a,Int)
rawFuncsStringDirTotal funs = 
    let (prog,exit_state) = runIdentity (runStateT (rawFuncsStringDir funs) (CM {counter = 0,varmap = M.empty}) ) 
    in (prog,counter exit_state)
    

-- I think all the variable and substitution stuff has now been threaded through.

makeClosedBDir :: (Eq v) => BRawv a v -> v -> (v -> BRawvd a v (S.Set v))
makeClosedBDir trem closingvar formalarg = case trem of 
    RFalse -> DFalse 
    RTrue -> DTrue 
    P p m -> DPred p (closeone m closingvar formalarg)

closeone :: (Eq v) => Rawv a v -> v -> (v -> Rawvd a v (S.Set v))
closeone trem closingvar formalarg = case trem of 
    Var v -> if closingvar == v then DVar formalarg else DVar v 
    Const a -> DConst a 
    Zero -> DZero 
    m :+ n -> DSum (closeone trem closingvar formalarg,S.empty) (closeone trem closingvar formalarg,S.empty)
    Op f m -> DOp f (closeone trem closingvar formalarg,S.empty)
    Let y m n -> case closingvar == y of -- to see why this works see original makeClosed below
        True -> DLet y (oneify m,S.empty) (oneify n,S.empty) 
        False -> DLet y (closeone m closingvar formalarg,S.empty) (closeone n closingvar formalarg,S.empty)
    Nil -> DNil
    Pair m n -> DPair (closeone m closingvar formalarg,S.empty) (closeone n closingvar formalarg,S.empty)
    Fst m -> DFst (closeone m closingvar formalarg,S.empty)
    Snd m -> DSnd (closeone m closingvar formalarg,S.empty)
    If b m n -> DIf (makeClosedBDir b closingvar formalarg) (closeone m closingvar formalarg,S.empty) (closeone n closingvar formalarg,S.empty)
    While cont b f -> case cont == closingvar of -- to see why this works see original makeClosed below
        False -> DWhile cont (convertBTermToDBTerm b) (oneify f,S.empty)
        True -> DWhile formalarg (makeClosedBDir b closingvar formalarg) (closeone f closingvar formalarg,S.empty)
    RD x m a v -> case x == closingvar of -- to see why this works see original makeClosed below 
        True -> DRD x (oneify m,S.empty) (oneify a,S.empty) (oneify v,S.empty)
        False -> DRD x (closeone m closingvar formalarg,S.empty) (closeone a closingvar formalarg,S.empty) (closeone v closingvar formalarg,S.empty) 
    Call f m -> DCall f (closeone m closingvar formalarg,S.empty)

    





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

-- Should do things like rename bound variables before converting to directory terms.
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