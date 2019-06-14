
 -- Amalgamated projection of Ring Election, error appear in fact "traces" 
 -- on "or" expression

module chapter6/ringElection

open util/ordering [Time] 
open util/ordering [Process] 

private abstract sig _Feature_{}
private one sig _F1,_F2 extends _Feature_{}
private sig _Product_ in _Feature_{}

sig Time{}
sig Process{
        succ: lone Process,
        succDyn: (Process -> Time),
        toSend: (Process -> Time),
        elected: set  Time
        }
fact {
         _F1 in _Product_  implies succ in Process -> one Process else no succ
        }
fact {
         _F2 in _Product_  implies succDyn in Process ->(Process -> Time) else no succDyn
        }

fact FM{
        (((( _F1 in _Product_ and _F2 in _Product_ ) implies  some none)) and
        ((( _F1 not in _Product_ and _F2 not in _Product_ ) implies  some none)) ) 
        }
 
fact ring{
        ((( _F1 in _Product_  implies {all  p :  one Process | (Process in  p . ^(succ ))})) and
        (( _F2 in _Product_  implies {all  t :  one Time, p :  one Process | (Process in  p . ^(succDyn . t ))})) ) 
        }
 
fact defineElected {
        no (elected.first) and  
        (all t :one  (Time - first) | (elected.t = ({p :one  Process | (p in (p.toSend.t - p.toSend.(t.prev)))})))
        }

 
fact traces{
        (init[first]) 

        all  t :  Time - last | let  t' = t .next | 
		all  p :   Process | (step[ t , t' , p ]) 
				   or (skip[ t , t' , p ]) 	
        				   or ( _F1 in _Product_  implies step[ t , t' ,succ . p ]) 
				//Error !     with "or" 
				// F2 not selected, should have no counterexample !!!!
				// but if comment this line,  there will be no counterexample 
       				  or ( _F2 in _Product_  implies step[ t , t' ,succDyn . t . p ]) 
        }
 
pred init [ t : Time]{
        {all  p :  one Process | ( p .toSend . t  =  p )}
        }

pred step [ t , t' : Time, p : Process]{
        (( _F1 in _Product_  implies (let  from = p .toSend  | (let  to = p .succ .toSend  | {some  id :  one  from . t  | ((( from . t'  = ( from . t  -  id ))) and
        (( to . t'  = ( to . t  + ( id  - prevs[ p .succ ])))) )}))) and
        ( _F2 in _Product_  implies (let  from = p .toSend  | (let  to = p .succDyn . t .toSend  | {some  id :  one  from . t  | ((( from . t'  = ( from . t  -  id ))) and
        (( to . t'  = ( to . t  + ( id  - prevs[ p .succDyn . t ])))) )}))) )
        }

pred skip [ t , t' : Time, p : Process]{
        ( p .toSend . t  =  p .toSend . t' )
        }

pred progress {
        {all  t :  one (Time - last) | ( some Process.toSend . t  => {some  p :  one Process |  ! skip[ t ,( t .next), p ]})}
        }

pred show {
         some elected 
        }


assert AtMostOneElected{
         lone elected .Time
        }

assert AtLeastOneElected{
        (progress =>  some elected .Time)
        }

check AtMostOneElected for 4  but 3 Process,3 Time 

fact selectedFeatures {
        _F1 in _Product_  &&_F2 not in _Product_ 
        }
