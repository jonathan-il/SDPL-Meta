-- Import this module as qualified
module SyntaxStructure where 

import SDPLTerms 
import R1Signature



-- A syntax structure contains the ingredients required to canonicalize a source tree (for example turn it into an ROP tree)
-- We use it during parsing to differentiate for an arbitrary sigma between user defined functions and builtin operations.
data SyntaxStructure s p a = SS {
    makeConstant :: Double -> a,
    lookupFunName :: String -> Maybe s,
    lookupPredName :: String -> Maybe p
}

{-
     getty :: s -> (LType,LType)
     gettypred :: p -> LType
-}
-- *********************************************
-- Syntax structure for (ROP Sigma) Pred1 R1
-- We should really pull this and the 
-- operational structs out into an example 
-- language definition file.  
-- And then share functions.
-- *********************************************


instanceSSR1 = SS {
    makeConstant = (\z -> R1 z) ,
    lookupFunName = 
        (
            \z -> case z of 
                "sin" -> Just $ Orig Sin Real Real 
                "cos" -> Just $ Orig Cos Real Real 
                "times" -> Just $  Orig Times (Prod Real Real) Real
                "neg" -> Just $ Orig Neg Real Real
                _ -> Nothing
        ),
    lookupPredName =
        (
            \z -> case z of 
                "less" -> Just LessThan 
                _ -> Nothing
        )
}

