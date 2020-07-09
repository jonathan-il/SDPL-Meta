module Parser where 

import SDPLTerms 
import SyntaxStructure (lookupPredName,lookupFunName)
import VarsAndSubs (rawFuncsStringIntTotal,makeClosed,rawFuncsStringDirTotal)

-- Parsec imports 
import System.IO
import Control.Monad
import Text.ParserCombinators.Parsec 
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token





-- Standard containers
import qualified Data.Map as M



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
                    "0",
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
                    -- ":", -- we don't really think of : as an operator, but sometimes it's nicer to write x:real instead of x : real.  I.e. you don't need space with operators.  (check) 
                    -- Later, we might add type annotations in for documentation.  But our types are all inferred.
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



-- type Prog s p a = M.Map String (FuncClosure s p a)
-- Recall that we are parsing over signatures sigma and predicates pred.
-- To properly parse, we require a syntax structure be passed in.  We will 
-- require that constants can be made from doubles.  This doesn't limit us 
-- to using doubles in our implementation, internally, it just requires 
-- that we have the ability to create constants from doubles.
-- In the future we may even want to change this.  We may want to parse 
-- from say tropical reals or GF2.



-- parserProg :: Parser (Prog A)
parserProg = do 
    whiteSpace
    funcs <- many parserFunc
    whiteSpace
    let v = foldr (\f@(name,_) m -> M.insert name f m) M.empty funcs 
    return v

-- this parses the program and converts it to int variables
-- this parser returns the program together with the largest variable used in renaming.
parserProgI = do 
    whiteSpace 
    funcs <- many parserFuncRaw
    whiteSpace
    return $ rawFuncsStringIntTotal funcs 

parserProgDir = do 
    whiteSpace 
    funcs <- many parserFuncRaw 
    whiteSpace 
    return $ rawFuncsStringDirTotal funcs

-- Need a directory prog parser.  This parses all the functions and returns them in a raw (formal closure)
-- format with the largest variable used directory terms
    -- processFuncIs funcs 

-- 
-- processFuncIs [] n = return M.empty 
-- processFuncIs ((fname,formalArg,fbody):funs) n = do 
--     let fbody 

parserFuncRaw =  do 
    reserved "fun" 
    funName <- ident 
    formalArg <- parens ident 
    reserved ":=" 
    body <- parserTerm 
    return (funName,formalArg,body)

parserFunc = do 
    reserved "fun"
    funName <- ident 
    formalArg <- parens ident  -- if we add type annotations this would be replaced by a type annotation
    reserved ":="
    body <- parserTerm 
    return $ (funName,makeClosed body formalArg)



    
-- parserBTerm :: Parser (BRaw)
-- remember 0.0 will be parsed as a double.  0 will not.  But we need to 
-- still do some additional testing.  Maybe one will shadow the other incorrectly
parserBTerm  = 
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
        m <- parens parserTerm
        case lookupPredName predname of 
            -- I wonder if there's an exploit avaible for bypassing a parser made with parsec 
            -- that can pass typechecking too.  Because fail doesn't necessarily 
            -- fail hard.  We should redo and replace this with ParsecT String () Err a
            Nothing -> fail $ "The predicate symbol: " ++ predname ++ " is not defined"
            Just prednameActual -> return $ P prednameActual m

parserTerm = 
    letcall 
    <|> ifThenElse
    <|> while 
    <|> rd 
    <|> expr 

infixOp :: String -> (a -> a -> a) -> Parser (a -> a -> a)
infixOp x f = reservedOp x >> return f 

-- then an expression is some number of additions of of primary terms.
expr = addition 

addOp = infixOp "+" (:+)
addition = primary  `chainl1` addOp

primary  = constant  <|> value  <|> first  <|> second  <|> (try (opcall ) <|> var)


value  = nil <|> (try (pair ) <|> parens (parserTerm )) <|> braces (parserTerm )


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
scriptvar = try scriptvarset <|> scriptvarget 

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
    | i <= 0 = Const 0
    | n == 1 =  x -- here by assumption 0 < i <= n and n == 1 so i == 1 is forced  
    | n > 1 && i > 0 = case i == n of 
        True -> Snd x
        False -> makeIndexed (Fst x) (n-1) i

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
        True -> Pair (Fst x) b
        False -> Pair (makeIndexedSet (Fst  x) (n-1) i b) (Snd  x)

constant = try rawConstant <|> zero 

rawConstant = do 
    a <- double 
    return $ Const a 

zero = do 
    reserved "0" 
    return Zero
-- requires some hard testing


opcall = do 
    f <- ident 
    m <- parens parserTerm
    -- we could actually do a preprocess step, pull all the function names out of the file 
    -- and check to see that f is defined entirely.
    case lookupFunName f of 
        Nothing -> return $ Call f m 
        Just opnameActual -> return $ Op opnameActual m 

letcall = do 
    reserved "let" 
    x <- ident 
    reserved "=" 
    m <- parserTerm
    reserved "in" 
    -- n <- braces (parserTerm s)
    n <- parserTerm
    return $ Let x m n 


nil = do 
    reservedOp "*" 
    return Nil 



-- This will look like (m,n)
pair = do 
    (m,n) <- parens commaterms
    return $ Pair m n


commaterms = do 
    m <- parserTerm 
    comma 
    n <- parserTerm  
    return (m, n)


-- this will look like fst (m)
first = do 
    reserved "fst"
    m <- parserTerm 
    return $ Fst  m
second  = do 
    reserved "snd" 
    m <- parserTerm
    return $ Snd m

ifThenElse  = do 
    reserved "if" 
    b <- parserBTerm  <|> parens (parserBTerm )
    reserved "then" 
    m <- parserTerm 
    reserved "else"
    n <- parserTerm 
    return $ If b m n

-- while x . b do f 
while = do 
    reserved "while"
    x <- ident 
    reservedOp "."
    b <- parserBTerm 
    reserved "do" 
    f <- parserTerm 
    return $ While x b f 

-- rd (x.m) (a)*v 
rd = do 
    reserved "rd" 
    (x,m) <- parens (diffarg)
    a <- parens (parserTerm )
    reservedOp "*" 
    v <- parserTerm 
    return $ RD x m a v

diffarg = do 
    x <- ident 
    reservedOp "." 
    m <- parserTerm 
    return (x,m)


{-

fun idx (z) := 
    let y = 3.1 in 
    let x = z[3,2] <- y in 
    let y2 = x[3,1] + 1.1 in 
    x[3,1] <- y2
fun idxExample (z) := 
    let y = 3.1 in 
    let x = z[3,2] <- y in 
    let y2 = x[3,1] + 1.1 in 
    x[3,1] <- y2

fun idxExample (z) := let y = 3.1 in let x = z[3,2] <- y in let y2 = x[3,1] + 1.1 in x[3,1] <- y2
-}