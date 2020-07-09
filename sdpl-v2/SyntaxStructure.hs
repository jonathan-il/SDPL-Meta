module SyntaxStructure where 

import SDPLTerms 

-- We won't carry around the make constant bit.  If we want to change our implementation 
-- to take on something more precise than doubles, then we'll do that later. 

lookupFunName z = case z of 
    "sin" -> Just Sin 
    "cos" -> Just Cos 
    "times" -> Just Times 
    "neg" -> Just Neg 
    _ -> Nothing 

{-# INLINABLE lookupFunName #-}

lookupPredName z = case z of 
    "less" -> Just LessThan 
    _ -> Nothing 

{-# INLINABLE lookupPredName #-}


-- We should also keep type lookup information for operation symbols in here.