module R1Signature where 

{-
This is our canonical signature module.  To obtain how our programming language works, we only need to add 
new symbols here, and then extend our preoperational structure and our syntax structure definitions. 
Everything else is already tied together.
-}

-- this should be moved off into it's own file.
data SigmaR1 = Sin | Cos | Times | Neg
data Pred1 = LessThan
data R1 = R1 Double

instance Show SigmaR1 where 
    show Sin = "sin"
    show Cos = "cos"
    show Times = "times"
    show Neg = "neg"

instance Show Pred1 where
    show LessThan = "lessthan"

instance Show R1 where 
    show (R1 d) = show d

instance Semigroup R1 where
    (R1 a) <> (R1 b) = R1 (a+b)

instance Monoid R1 where
    mempty = R1 0