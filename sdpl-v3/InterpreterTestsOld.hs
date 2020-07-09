module InterpreterTestsOld where 

import SDPLTerms 
import qualified Data.Map as M
import SDPLInterpreterOld

dOfWhileSquare = 
  let 
    guard = P LessThan (Pair (Var 0) (Const 1.4))
    body = Op Times (Pair (Var 0) (Var 0))
    w = While 0 guard body 
    rdwhole = RD (0::Int) w (Const 1.000001) (Const 1.000001)
  in 
    fullEvaluationTermTotal 10 rdwhole 

recdOfWhileSquare = 
  let 
    hbody z = If (P LessThan (Pair (Var z) (Const 1.4)) ) (Call "h" (Op Times (Pair (Var z) (Var z)))) (Var z)
    hprog = M.insert "h" hbody M.empty 
    callhonx = Call "h" (Var 0)
    rdh = RD (0::Int) callhonx (Const 1.000001) (Const 1.000001)
  in 
    fullEvaluationTermInProgTotal 1 rdh hprog
  -- fun h (z) := if less ((z,1.4)) then h (times ((z,z))) else z 

  -- fullEvaluationTermInProgTotal