module Main where 

{-
Practical changes to make:
  1. Switch to megaparsec.  Since this is a reference, I don't see a need to switch to alex/happy for the speed improvements.
  2. Switch to bytestring processing 
  3. Change to using the industrial strenth ST instead of our homebrewed one.  The real one is much more tuned.  Similarly for the Err monad we used. 
  4. Allow for array indexing syntax to make operations smoother.  E.g. x,y : [n] then we can do things like x[1] + y[1] and eventually x[1..k] + y[1..k]. 
  5. Implement some of the optimizations that follow from restriction differentiation.
-}

-- system imports
import System.IO         (readFile)
import Control.Exception (catch, IOException)
import System.Exit (die) -- such a morbid name
import Control.Monad (when)
import System.Environment (getArgs)

-- my imports
import qualified SDPLInterpreter as Interpreter 
import qualified Parser as Parser 
import qualified SDPLTerms as Terms 
import qualified R1Signature as R1
import qualified SyntaxStructure as SS 
import qualified Err as Err
import qualified OperationalStructure as OS

-- parsec
import qualified Text.ParserCombinators.Parsec as Parsec

-- standard containers 
import qualified Data.Map as M

safeLoadFile :: FilePath -> IO (Maybe String)
safeLoadFile p = (Just <$> readFile p) `catch` handler
   where
   handler :: IOException -> IO (Maybe String)
   handler _ = return Nothing

type CanonicalTerm = Terms.Raw (Terms.ROP R1.SigmaR1) R1.Pred1 R1.R1 
type CanonicalProgram = Terms.Prog (Terms.ROP R1.SigmaR1) R1.Pred1 R1.R1

loadProg :: String -> IO (Maybe CanonicalProgram)
loadProg filename = do 
    x <- safeLoadFile filename
    case x of 
        Nothing -> do 
            putStrLn $ "Filename: " ++ filename ++ " not found"
            return Nothing 
        Just contents -> case Parsec.parse (Parser.parserProg SS.instanceSSR1) "" contents of 
            Left e -> do 
                putStrLn $ "Program failed to parse with message: " ++ (show e )
                return Nothing
            Right m -> return $ Just m


evalTermInProg :: CanonicalTerm -> CanonicalProgram -> Err.Err (Terms.ClosedVal R1.R1)
evalTermInProg = Interpreter.fullEvaluationTermInProgStrict OS.instanceOperationalStruct  "hfree"

repl :: CanonicalProgram -> IO () 
repl prog = do 
    putStrLn "Enter term to evaluate or :q to exit:"
    x <- getLine 
    when (x == ":q") (die "Bye")
    case Parsec.parse ((Parser.parserTerm SS.instanceSSR1) <* Parsec.eof) "" x of 
        Left e -> do 
            putStrLn $ "Invalid term: " ++ (show e)
            repl prog
        Right term -> case evalTermInProg term prog of 
            Err.Fail msg -> do 
                putStrLn $ "Computation failed because: " ++ msg 
                repl prog 
            Err.Ok val -> do 
                print val 
                repl prog

-- I compile with ghc --make -O2 Main
-- I run with ./Main Examples.sdpl
-- Other options include adding 
-- -ffun-to-thunk
-- -fno-state-hack -- we need to switch to using the real ST instead of our own for this
-- -funbox-strict-fields

-- Try for example taking the derivative of the while loop used by h in Examples.sdpl.
-- rd (x : real . h(x) : real)(1.001) * (1.001)
-- It should return ~ 854.1 instantly.

-- Also, be careful in the interpreter: you have to always type a decimal.  So 1.0 not 1.  
-- Also, I made a choice to make a < b undefined when a == b.  You can change this an recompile.
main :: IO ()
main = do 
    args <- getArgs
    case args of 
        [] -> do 
            putStrLn "No program entered, you can still evaluate terms including derivatives.  You can write while-loops, call builtins etc, you just won't have access to functions you wrote.\n"
            putStrLn "Entering read-eval-print-loop.  Enter a term you want to evaluate.  Note this is a simple repl, and there is no history or back.  If you make a mistake just hit enter and type the term again.\n"
            repl M.empty 
        [x] -> do 
            putStrLn $ "Attempting to load program contained in: " ++ x
            prog <- loadProg x
            case prog of 
                Nothing -> putStrLn "At this time your program cannot be run.  Please make necessary changes, or if this is a bug, file a bug report."
                Just realProgram -> repl realProgram
        _ -> putStrLn "At this time, we only support loading a single file."

    

