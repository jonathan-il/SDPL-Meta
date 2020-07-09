module Parser where

-- If time ever permits, rewrite this using BNFC.  It's just more flexible and the result will be loads faster.  For example, there is a 
-- between windows and unix systems, where a file cannot start with a certain whitespace character.

import SDPLTerms
import R1Signature -- just for testing
import SyntaxStructure
import NotationalSums (makeZeroVal)

-- Parsec imports
import System.IO
import Control.Monad
import Text.ParserCombinators.Parsec 
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token





-- Standard containers
import qualified Data.Map as M


-- One piece of shorthand that would be really nice to to have would be a piece of shorthand for something like array dereferncing
-- e.g. x : [4] then x[1] is shorthand for let x13 = fst(x),x4=snd(x),x12=fst(x13),x3=snd(x13),x1=fst(x12),x2=snd(x12) in x1. 
-- Realistically, we should use array/vector inputs where we can input shape parameters.  Then we won't have to do all this 
-- long sequences of let expressions.  But to make everything workout, we would still allow contexts to have multiple variables 
-- so that are input space isn't regarded as a single contiguous block.  We just allow for vector variables 
-- with a shape parameter: commas are the higher precedence, and semicolons indicate bilinearity or "tensoring" (but we don't really)
-- tensor types, just a bilinearity requirement.  So e.g. f : [1,2,2;4,1] says f has type R x R^2 x (R^2 ; R^4) x R where R^2 ; R^4 
-- is interpreted either as a tensor or as the requirement that f be bilinear in that argument.


-- Add the parsing out of comments.  This isn't done here it's just lexed.


languageDef = 
    emptyDef 
        {
            Token.commentStart = "/*",
            Token.commentEnd  = "*/",
            Token.commentLine = "//",
            Token.identStart = letter,
            Token.identLetter = alphaNum,
            Token.reservedNames =
                [
                    "if",
                    "then",
                    "else",
                    "while",
                    "do",
                    "let",
                    "in",
                    "fst",
                    "snd",
                    "rd",
                    "true",
                    "false",
                    "real",
                    "1",
                    "fun",
                    ":=", -- for function body definitions
                    "=", -- for let bindings 
                    "<-" -- for special syntactic sugar of "array update syntax"
                ],
            Token.reservedOpNames =
                [
                    -- we only really have a single binary operator
                    -- everything else is assumed to come from \Sigma.
                    "+",
                    ":", -- we don't really think of : as an operator, but sometimes it's nicer to write x:real instead of x : real.  I.e. you don't need space with operators.  (check) 
                    "*",  -- similarly to :.  However, this one gets a bit odd, because we also use this symbol for unit, which is not being used as an operator.  Maybe we should have a different symbol 
                          -- for either the unit element or the application of the reverse derivative in a direction? (check)
                    "."  -- this operator is used in while loops (check)
                ]
        }

-- create a lexer
lexer = Token.makeTokenParser languageDef

-- Now we extract some useful components from the lexer 
ident = Token.identifier lexer 
reserved = Token.reserved lexer
reservedOp = Token.reservedOp lexer
parens = Token.parens lexer 
braces = Token.braces lexer
brackets = Token.brackets lexer
int = Token.integer lexer 
-- In this language, numbers will have to be input in .0 format. e.g. 1.0 not 1.
double = Token.float lexer
semi = Token.semi lexer 
comma = Token.comma lexer 
whiteSpace = Token.whiteSpace lexer
 


parserType :: Parser LType 
parserType = 
    do
        -- a list of numbers as above 
        xs <- numlist 
        return $ makePowers xs
    <|> 
    do
        real <- reserved "real"
        return Real 
    <|> 
    do 
        unit <- reserved "1" 
        return Unit
    <|> parens twoTypes



-- twoTypes :: Parser LType 
twoTypes = do 
    ty1 <- parserType 
    comma 
    ty2 <- parserType 
    return $ Prod ty1 ty2 

-- numlist :: Parser [Integer]
numlist = brackets nums 
-- nums :: Parser [Integer]
nums = int `sepBy` comma
makePowers :: [Integer] -> LType
makePowers [] = Unit 
makePowers [x] = makePower x 
makePowers (x:xs) = makePowersAcc (makePower x) xs
makePowersAcc :: LType -> [Integer] -> LType 
makePowersAcc acc [] = acc 
makePowersAcc acc (x:xs)  = 
    let acc' = Prod acc (makePower x)
    in seq acc' $ makePowersAcc acc' xs 
makePower n 
    | n < 0 = undefined 
    | n == 0 = Unit 
    | n == 1 = Real 
    | n > 1 = Prod (makePower (n-1)) Real
    


-- type Prog s p a = M.Map String (FuncClosure s p a)
-- Recall that we are parsing over signatures sigma and predicates pred.
-- To properly parse, we require a syntax structure be passed in.  We will 
-- require that constants can be made from doubles.  This doesn't limit us 
-- to using doubles in our implementation, internally, it just requires 
-- that we have the ability to create constants from doubles.
-- In the future we may even want to change this.  We may want to parse 
-- from say tropical reals or GF2.
parserProg :: (Monoid a) => SyntaxStructure s p a -> Parser (Prog s p a)
parserProg s = do 
    whiteSpace
    funcs <- many (parserFunc s)
    whiteSpace
    let v = foldr (\f@(name,_,_,_) m -> M.insert name f m) M.empty funcs 
    return v



-- type FuncClosure s p a = (String,LType,LType, String -> Raw s p a)
-- we are going for fun f (x : real) : real := body 
parserFunc :: (Monoid a) => SyntaxStructure s p a -> Parser (FuncClosure s p a)
parserFunc s = do 
    reserved "fun"
    funName <- ident 
    (formalArg,intty) <- parens parseArg 
    reservedOp ":" 
    outty <- parserType 
    reserved ":="
    body <- (parserTerm s)
    return $ (funName,intty,outty,makeClosed body formalArg)



parseArg :: Parser (String,LType)
parseArg = do 
    varName <- ident 
    reservedOp ":" 
    ty <- parserType 
    return (varName,ty)



    



makeClosed :: Raw s p a -> String -> (String -> Raw s p a)
makeClosed trem closingvar formalarg = case trem of -- purposefully misspelled to prevent clash 
    Var v -> if closingvar == v then Var formalarg else Var v
    Const a -> Const a 
    m :+ n -> (makeClosed m closingvar formalarg) :+ (makeClosed n closingvar formalarg)
    Op f m -> Op f (makeClosed m closingvar formalarg)
    {-
    By our typing rules we have a variable condition.  In any term Let y = m in n, we have that y is not free in m.  Thus if closingvar == y, then there is nothing to change in m.  
    Also, since y is bound in n, if closingvar == y there is nothing to change in n.  Thus if y==closingvar, the term is left unmodified.  Otherwise, we need to close the closingvars 
        in both m and n.
    -}
    Let y yty m n -> case closingvar == y of 
        True -> Let y yty m n 
        False -> Let y yty (makeClosed m closingvar formalarg) (makeClosed n closingvar formalarg)
    Nil -> Nil
    Pair tym tyn m n -> Pair tym tyn (makeClosed m closingvar formalarg) (makeClosed n closingvar formalarg)
    Fst ty1 ty2 m -> Fst ty1 ty2 (makeClosed m closingvar formalarg)
    Snd ty1 ty2 m -> Snd ty1 ty2 (makeClosed m closingvar formalarg)
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
    While cont contty b f -> case cont == closingvar of 
        False -> While cont contty b f  
        True -> While formalarg contty (makeClosedB b closingvar formalarg) (makeClosed f closingvar formalarg)
    {-
    Similarly to let expressions, any formation rd(y.m)(a)*v has the assumption that y is not in a or v.  Thus if closingvar == y 
    there is nothing to do because closing var is in neither of those terms.  Also, y is bound in m, thus there is nothing to change in m in this case either.
    Otherwise, all 3 terms need to be changed.
    -}
    RD x xty mty m a v -> case x == closingvar of 
        True -> RD x xty mty m a v 
        False -> RD x xty mty (makeClosed m closingvar formalarg) (makeClosed a closingvar formalarg) (makeClosed v closingvar formalarg)
    Call f m -> Call f (makeClosed m closingvar formalarg)

makeClosedB :: BRaw s p a -> String -> (String -> BRaw s p a)
makeClosedB trem closingvar formalarg = case trem of 
    RTrue -> RTrue 
    RFalse -> RFalse 
    Pred p m -> Pred p (makeClosed m closingvar formalarg)
    





parserBTerm :: (Monoid a) => SyntaxStructure s p a -> Parser (BRaw s p a)
parserBTerm s = 
    do 
        reserved "true"
        return RTrue 
    <|> 
    do 
        reserved "false"
        return RFalse 
    <|>
    do 
        predname <- ident 
        m <- parens (parserTerm s)
        case lookupPredName s predname of 
            -- I wonder if there's an exploit avaible for bypassing a parser made with parsec 
            -- that can pass typechecking too.  Because fail doesn't necessarily 
            -- fail hard.  We should redo and replace this with ParsecT String () Err a
            Nothing -> fail $ "The predicate symbol: " ++ predname ++ " is not defined"
            Just prednameActual -> return $ Pred prednameActual m



-- our approach to parsing is to look for assignments, ifthenelse, while and rd
-- as the top of the tree i.e. highest precedence.   so e.g. let x = m in n + t will be parsed as (let x=m in n) + t
-- these are all guaranteed to consume input to try to match, so there is no direct left recursion.
parserTerm :: (Monoid a) => SyntaxStructure s p a -> Parser (Raw s p a)
parserTerm s = 
    letcall s 
    <|> ifThenElse s 
    <|> while s 
    <|> rd s 
    <|> expr s


infixOp :: String -> (a -> a -> a) -> Parser (a -> a -> a)
infixOp x f = reservedOp x >> return f 

-- then an expression is some number of additions of of primary terms.
expr :: (Monoid a) => SyntaxStructure s p a -> Parser (Raw s p a)
expr = addition 

addOp = infixOp "+" (:+)
addition :: (Monoid a) => SyntaxStructure s p a -> Parser (Raw s p a)
addition s = (primary s) `chainl1` addOp

-- a primary term is a number, a parenthetized expression, a braced expression, 
-- a function or operation call or a variable.  variables can get shadowed by 
-- function calls, so we try function call first, and if it fails hand the unconsumed 
-- string to the variable catcher
primary :: (Monoid a) => SyntaxStructure s p a -> Parser (Raw s p a)
primary s = constant s <|> value s <|> first s <|> second s <|> (try (opcall s) <|> var)
-- <|> first s <|> second s -- I think these class with call.

value :: (Monoid a) => SyntaxStructure s p a -> Parser (Raw s p a)
value s = nil <|> (try (pair s) <|> parens (parserTerm s)) <|> braces (parserTerm s)

var :: (Monoid a) => Parser (Raw s p a)
var = 
    (
        try scriptvar 
        <|>
        do 
            x <- ident 
            return $ Var x 
    )
     


{-
We now allow the following syntax 
  x[n,i]
Which is merely syntactic sugar that our parser disregards and replaces with 
the ith element of the n-tuple x.  There is no formal term formation rule, but there is an 
admissable term formation rule 
  x : R^n   
  -------------
  x[n,i] : R 

It is defined as follows:
  x[n,i] := *  if n <= 0 (this says n is dimension 0, and we take negative dimensions to all be 0)
  x[n,i] := 0_R  if i <= 0 (this says get the 0th element, but we are assuming counting from 1 so we just set this to be 0)
  x[1,i] := x  (by the hypothesis, actually i has to be 1 so this is equivalently x[1,1] = x)
  x[n+1,i] := snd(x) if i=n+1    and (fst(x))[n,i] otherwise 

We will also soon allow slices 
  x[n, i:k] : R{k-i}
And again, this is mere syntactic sugar -- these do not have corresponding language counterparts. 
Though they can in future iterations.
-}
scriptvar :: (Monoid a) => Parser (Raw s p a)
scriptvar = try scriptvarset <|> scriptvarget 

scriptvarget :: (Monoid a) => Parser (Raw s p a)
scriptvarget = do 
    x <- ident 
    (n,i) <- brackets twoNums 
    return $ makeIndexed (Var x) n i 

twoNums = do 
    n <- int
    comma 
    i <- int 
    return (n,i)

makeIndexed x n i 
    | n <= 0 = Nil 
    | i <= 0 = Const mempty
    | n == 1 =  x -- here by assumption 0 < i <= n and n == 1 so i == 1 is forced  
    | n > 1 && i > 0 = case i == n of 
        True -> Snd (makePower (n-1)) Real x
        False -> makeIndexed (Fst (makePower (n-1)) Real x) (n-1) i


{-
We also allow special syntax for setting scriptvariables.  
  x[n,i] <- b  
We have an admissable rule:
  x : R^n   b : R 
  -----------------
  x[n,i] <- b : R^n 

The idea is that this is the ith entry of x updated with b otherwise everything else is the same.
Note here that b must be a variable.  The common case would be 
  let b = nasty in 
  x[n,i] <- b : R^n
In the future we may allow arbitrary terms, but this is just for my use right now, in order to 
test out the language.

We require that i <= n and then 
This is given inductively by 
  x[n,i] <- b   = *   if n <= 0 
  x[n,i] <- b   = x   if i <= 0 -- here we aren't updating a relevant component of x 
  x[1,1] <- b   = b   again this is the same as x[1,i]
  x[n+1,i] <- b = 
      if n+1 == i then (fst(x),b)
      else   (fst(x)[n,i] <- b,snd(x))

-}
scriptvarset :: (Monoid a) => Parser (Raw s p a)
scriptvarset = do 
    x <- ident 
    (n,i) <- brackets twoNums 
    reserved "<-"
    t <- ident
    return $ makeIndexedSet (Var x) n i (Var t) 

makeIndexedSet x n i b
    | n <= 0 = Nil 
    | i <= 0 = x 
    | n == 1 = b 
    | n > 1 && i > 0 = case i == n of 
        True -> Pair (makePower (n-1)) Real (Fst (makePower (n-1)) Real x) (b)
        False -> Pair (makePower (n-1)) Real (makeIndexedSet (Fst (makePower (n-1)) Real x) (n-1) i b) (Snd (makePower (n-1)) Real x)



constant s = do 
    a <- double 
    return $ Const $ makeConstant s a




opcall s = do 
    f <- ident 
    m <- parens (parserTerm s)
    -- we could actually do a preprocess step, pull all the function names out of the file 
    -- and check to see that f is defined entirely.
    case lookupFunName s f of 
        Nothing -> return $ Call f m 
        Just opnameActual -> return $ Op opnameActual m 



-- I know, we could use whitespace.  But getting that right takes time. 
-- We're looking for let x : A = m in n.
-- We've also made braces optional.
letcall s = do 
    reserved "let" 
    x <- ident 
    reservedOp ":" 
    a <- parserType 
    reserved "=" 
    m <- parserTerm s
    reserved "in" 
    -- n <- braces (parserTerm s)
    n <- parserTerm s
    return $ Let x a m n 


nil = do 
    reservedOp "*" 
    return Nil 



-- This will look like (m,n){a,b}
pair s = do 
    (m,n) <- parens (commaterms s)
    (ty1,ty2) <- braces commatypes
    return $ Pair ty1 ty2 m n



commaterms s = do 
    m <- parserTerm s 
    comma 
    n <- parserTerm s 
    return (m, n)

commatypes = do 
    ty1 <- parserType 
    comma 
    ty2 <- parserType 
    return (ty1,ty2)

-- this will look like fst {a,b} (m)
first s = do 
    reserved "fst"
    (ty1,ty2) <- braces commatypes 
    m <- parserTerm s
    return $ Fst ty1 ty2 m
second s = do 
    reserved "snd" 
    (ty1,ty2) <- braces commatypes 
    m <- parserTerm s
    return $ Snd ty1 ty2 m


-- we're looking for if b then m else n 
-- we'll try it without braces at first 
ifThenElse s = do 
    reserved "if" 
    b <- parserBTerm s <|> parens (parserBTerm s)
    reserved "then" 
    m <- parserTerm s
    reserved "else" 
    n <- parserTerm s 
    return $ If b m n 



-- we're looking for while (x:A) . b do f
-- we'll try without braces at first
while s = do 
    reserved "while"
    (x,xty) <- parens parseArg
    reservedOp "."
    b <- parserBTerm s 
    reserved "do" 
    f <- parserTerm s 
    return $ While x xty b f 

-- fun w (x : real) : real := while (x : real) . (less ((x, 1.4){real,real})) do times ( (x,x) {real,real})
-- fun activationExample (z : [2]) : real :=
--     fst{real,real}(z)

-- we're looking for 
-- rd (x:t.m:b) (a)*v 
rd s = do 
    reserved "rd" 
    (x,t,m,b) <- parens (diffarg s)
    a <- parens (parserTerm s)
    reservedOp "*" 
    v <- parserTerm s 
    return $ RD x t b m a v



diffarg s = do 
    x <- ident 
    reservedOp ":" 
    t <- parserType 
    reservedOp "." 
    m <- parserTerm s 
    reservedOp ":" 
    b <- parserType  
    return (x,t,m,b)


-- ******************************
-- TESTS 
-- ******************************
allTests :: [Bool]
allTests = 
    typeTests
    ++ termTests
    ++ btermTests
    ++ functionTests 
    ++ programTests

allTestsPassed :: Bool 
allTestsPassed = and allTests

typeTests :: [Bool]
typeTests = 
    [
        ttestr,
        ttestu,
        ttestbrackets,
        ttestprodrr,
        ttestprodrbrackets,
        ttestprodbracketsinvolved,
        ttestmultibrackets
    ]
termTests :: [Bool]
termTests = 
    [
        rdTest1,
        whileTest,
        ifThenElseTest1,
        ifThenElseTest2,
        firstTest,
        firstTest2 ,
        secondTest,
        pairTest,
        nilTest,
        letsTest,
        opTest,
        callTest,
        callTest2,
        sumTest,
        contestTerm,
        vtestTerm,
        scriptVarTest,
        scriptVarSetTest1,
        scriptVarSetTest2,
        scriptVarSetTest3
    ]

btermTests :: [Bool]
btermTests =
    [
        trueTest,
        falseTest,
        predTest,
        predTest2 
    ]

functionTests :: [Bool]
functionTests = 
    [
        functionTest
    ]

programTests :: [Bool]
programTests = 
    [
        progTest
    ]
ttestr = case parse parserType "" "real" of 
    Left error -> False
    Right Real -> True 
    Right _ -> False

ttestu = case parse parserType "" "1" of 
    Right Unit -> True 
    _ -> False
ttestbrackets = case parse parserType "" "[5]" of 
    Right (Prod (Prod (Prod (Prod Real Real) Real) Real) Real) -> True 
    _ -> False
ttestprodrr = case parse parserType "" "(real,real)" of 
    Right (Prod Real Real) -> True 
    _ -> False 
ttestprodrbrackets = case parse parserType "" "(real,[3])" of 
    Right (Prod Real (Prod (Prod Real Real)Real)) -> True 
    _ -> False
ttestmultibrackets = case parse parserType "" "[2,2,2]" of 
    Right (Prod  (Prod (Prod Real Real) (Prod Real Real) ) (Prod Real Real)   ) -> True 
    _ -> False
ttestprodbracketsinvolved = case parse parserType "" "((1,[2,0]),([2],([],real)))" of 
    Right (Prod (Prod (Unit) (Prod (Prod Real Real) Unit)) (Prod (Prod Real Real) (Prod Unit Real))) -> True 
    _ -> False

rdTest1 = case parse (parserTerm instanceSSR1 ) "" "rd (x : real . x : real) (y) * z" of 
    Right (RD "x" Real Real (Var "x") (Var "y") (Var "z")) -> True
    _ -> False

whileTest = case parse (parserTerm instanceSSR1 ) "" "while (x : real) . true do x+x" of
    Right (While "x" Real RTrue ((Var "x") :+ (Var "x"))) -> True
    _ -> False

ifThenElseTest1 = case parse (parserTerm instanceSSR1 ) "" "if (less(x)) then y else z" of 
    Right (If (Pred LessThan (Var "x")) (Var "y") (Var "z")) -> True 
    _ -> False

ifThenElseTest2 = case  parse (parserTerm instanceSSR1 ) "" "if less(x) then y else z" of
    Right (If (Pred LessThan (Var "x")) (Var "y") (Var "z")) -> True 
    _ -> False

firstTest = case parse (parserTerm instanceSSR1 ) "" "fst {real,real} (x,y) {real,real}" of 
    Right _ -> True
    _ -> False 

firstTest2 = case parse (parserTerm instanceSSR1 ) "" "fst {real,real} ((x,y) {real,real})" of 
    Right _ -> True
    _ -> False 

secondTest = case parse (parserTerm instanceSSR1 ) "" "snd {real,real} (x,y) {real,real}" of 
    Right _ -> True 
    _ -> False

pairTest = case parse (parserTerm instanceSSR1 ) "" "(x,y){real,real}" of 
    Right (Pair Real Real (Var "x") (Var "y")) -> True
    _ -> False

nilTest = case parse (parserTerm instanceSSR1 ) "" "*" of
    Right Nil -> True 
    _ -> False

letsTest = case parse (parserTerm instanceSSR1) "" "let x : real = z in w" of 
    Right (Let "x" Real (Var "z") (Var "w")) -> True
    _ -> False

opTest = case parse (parserTerm instanceSSR1 ) "" "sin(x)" of 
    Right (Op (Orig Sin Real Real) (Var "x") ) -> True
    _ -> False

callTest = case parse (parserTerm instanceSSR1 ) "" "f(x)" of 
    Right (Call "f" (Var "x")) -> True 
    _ -> False 

-- cannot use builtin names 
callTest2 = case parse (parserTerm instanceSSR1 ) "" "fst(x)" of 
    Left _ -> True 
    _ -> False 

sumTest = case parse (parserTerm instanceSSR1) "" "x + y" of 
    Right ((Var "x") :+ (Var "y")) -> True
    _ -> False

-- script variables e.g. x[3,1]
scriptVarTest = case (parse (parserTerm instanceSSR1 ) "" "x[3,1]", parse (parserTerm instanceSSR1) "" "x[3,2]") of 
    (Right (Fst Real Real (Fst (Prod Real Real) Real (Var "x"))) , Right (Snd Real Real (Fst (Prod Real Real) Real (Var "x")))) -> True 
    _ -> False 

-- script variable setting e.g. x[3,1] <- y
scriptVarSetTest1 = case parse (parserTerm instanceSSR1) "" "x[3,1] <- y" of 
    Right (Pair (Prod Real Real) Real (  Pair Real Real (Var "y") (Snd Real Real (Fst (Prod Real Real) Real (Var "x")))  ) (Snd (Prod Real Real) Real (Var "x"))) -> True 
    _ -> False

scriptVarSetTest2 = case parse (parserTerm instanceSSR1) "" "x[3,2] <- y" of 
    Right (Pair (Prod Real Real) Real (  Pair Real Real  (Fst Real Real (Fst (Prod Real Real) Real (Var "x")))   (Var "y")   ) (Snd (Prod Real Real) Real (Var "x"))) -> True  
    _ -> False

scriptVarSetTest3 = case parse (parserTerm instanceSSR1 ) "" "x[3,3] <- y" of 
    Right (Pair (Prod Real Real) Real (Fst (Prod Real Real) Real (Var "x")) (Var "y")) -> True 
    _ -> False

contestTerm = case parse (parserTerm instanceSSR1) "" "3.0" of 
    Right (Const (R1 3.0)) -> True
    _ -> False 

vtestTerm = case parse (parserTerm instanceSSR1) "" "x" of 
    Right (Var "x") -> True 
    _ -> False 

trueTest = case parse (parserBTerm instanceSSR1) "" "true" of 
    Right RTrue -> True 
    _ -> False

falseTest = case parse (parserBTerm instanceSSR1 ) "" "false" of 
    Right RFalse -> True 
    _ -> False

predTest = case parse (parserBTerm instanceSSR1 ) "" "less(x)" of 
    Right (Pred LessThan (Var "x")) -> True 
    _ -> False

predTest2 = case parse (parserBTerm instanceSSR1 ) "" "lesser(x)" of 
    Left _ -> True 
    _ -> False 

functionTest = case parse (parserFunc instanceSSR1 ) "" "fun f (x : real) : real := x" of 
    Right (f,inty,outty,body) -> case body "w" of 
        Var "w" -> True 
        _ -> False 
    _ -> False

progTest = case parse (parserProg instanceSSR1 ) "" "fun f (x : real) : real := x  fun g (y : real) : real := y + y" of 
    Left _ -> False 
    Right map -> case (M.lookup "f" map,M.lookup "g" map) of 
        (Just (a,b,c,d),Just (a',b',c',d')) -> case (d "w",d' "w")  of 
            (Var "w",(Var "w") :+ (Var "w")) -> True 
            _ -> False
        _ -> False