/**
* ➀  Add "RViz", "Map_server",  "Location_perfect_Match" sensor node and 1 a "Node Agrob_Planner" node
* ➁  Add safe control (add "Node Safety_controller_Filter" node)
*/
module octo
open meta
fact FM{
	➁➀some none➀➁
}

------  Values	------
abstract sig VL extends Value{}
sig PL, GL, RL, LL, Zero in VL{}	-- Linear Velocities

fact VL_constraints {
	VL in (PL + GL + RL + LL + Zero)
	no Zero & (PL + GL + RL + LL)	
	GL in PL						
	LL in GL
	LL in RL
	RL in LL
	lone Zero						
	}

abstract sig JC extends Value{}	
sig RB, LB, GLB, WB in JC{}-- Joystick Control Buttons

fact JC_constraints {
	JC in (RB + LB + GLB + WB) -- dealing with abstract hierarchy problem
	no RB & (LB + GLB + WB)			
	no LB & (RB + GLB + WB)
	no GLB & (RB + LB  + WB)
	no WB & (RB + LB + GLB)
								
	lone RB						
	lone LB
	lone GLB
	lone WB
	}

abstract sig LS extends Value{}
sig SR, DR in LS {}	-- Laser Scan Values		

fact LS_constraints {
	LS in (SR + DR)
	no SR & DR					
	}

abstract sig S extends Value{}
sig IS, WS, GLS in S {}				-- State Values

fact S_constraints {
	S in (IS + WS + GLS)
	no IS & (WS + GLS)
	no WS & (IS + GLS)
	no GLS & (IS + WS)
	lone IS
	lone WS
	lone GLS
	}	
--for feature ➀ or ➁
abstract sig Pose extends Value{}		-- Pose Values
--for feature ➀ or ➁
abstract sig OG extends Value {}		-- Occupancy Grid Values
sig Unknown, SC, UC in OG {}			-- Unknown, Safe Cell, Unsafe Cell
--for feature ➀ or ➁
fact OG_constraints {
	OG in (Unknown + SC + UC)
	no Unknown & (SC + UC)
	no SC & (Unknown + UC)
	no UC & (Unknown + SC)
	lone Unknown
	lone SC
	lone UC
	}

------ Topic List ------
one sig  	Horizontal_PointCloud ,		 	      
		Vertical_PointCloud,
		Joystick_Commands,
		Current_State,
		Joystick_Vel_Linear,
		Supervisor_Vel_Linear, 
		Max_Vel_Linear , 
		Husky_Vel_Linear
extends Topic {}
--for feature ➀ or ➁
one sig Goal_Pose, 
		Map,
		Current_Pose,
		External_Vel_Linear
extends Topic{}

➁one sig 	Joystick_Commands_Filtered extends Topic{}➁

-- Topic message type constraints
fact topic_predicates {	 
	all m: topic.Horizontal_PointCloud | m.value in(➋➊ LS➊➋+➀DR➀+➁DR➁) 

	all m: topic.Vertical_PointCloud | m.value in (➋➊LS➊➋+➀DR➀+➁DR➁)
	all m: topic.Joystick_Commands | m.value in JC or m.value in PL
	all m: topic.Joystick_Vel_Linear | m.value in (➋➊VL➊➋+➀JC➀+➁JC➁)
	--for feature ➀ or ➁
	all m: topic.Goal_Pose | m.value in Pose
	all m: topic.Map | m.value in OG
	all m: topic.Current_Pose | m.value in Pose

	➁all m: topic.Joystick_Commands_Filtered | m.value in (JC + PL)➁
	all m: topic.Current_State | m.value in S
	all m: topic.Supervisor_Vel_Linear | m.value in VL
	all m: topic.Max_Vel_Linear| m.value in VL
	all m: topic.Husky_Vel_Linear | m.value in VL
	}

------ Node List ------
one sig Horizontal_Laser extends  Sensor {}{		
	advertises = Horizontal_PointCloud
	}
one sig Vertical_Laser extends  Sensor {}{
	advertises = Vertical_PointCloud
	}
one sig Controller extends  Sensor {}{
	advertises = Joystick_Commands 
	}
one sig Rviz extends Sensor {}{-- Map only	
	advertises = Goal_Pose	
	}

one sig Map_Server extends Sensor {}{-- Map only
	advertises = Map	
	}

one sig Localization_Perfect_Match extends Sensor {}{	-- Map only (abstracted to a sensor)
	advertises = Current_Pose
	}

one sig Agrob_Planner extends Node {}{-- Map only
	subscribes = Goal_Pose + Map + Current_Pose + Vertical_PointCloud 
	advertises = External_Vel_Linear
	}

➁one sig Safety_Controller_Filter extends Node {}{ 
	subscribes = Joystick_Commands
	advertises = Joystick_Commands_Filtered
	}➁
one sig Translator extends Node {}{
	subscribes = Joystick_Commands
	advertises = Joystick_Vel_Linear
	}
one sig Supervisor extends Node {} {
	subscribes = Horizontal_PointCloud + Vertical_PointCloud + ➋Joystick_Commands➋+➁Joystick_Commands_Filtered➁
	advertises = Supervisor_Vel_Linear + Max_Vel_Linear + Current_State
	}
one sig Multiplexer extends Node {} {
	subscribes = Supervisor_Vel_Linear + Max_Vel_Linear + Joystick_Vel_Linear+➀External_Vel_Linear➀
	advertises = Husky_Vel_Linear
	}
one sig Supervisor_GUI extends Actuator {}{
	subscribes = Current_State
	}
one sig Husky_Base extends Actuator{}{
	subscribes = Husky_Vel_Linear
	}


fact Translator_Behaviour {
	all t: Time-first, m1: Translator.outbox.t & topic.Joystick_Vel_Linear | some t': t.prevs {
			(some m0: Translator.inbox.t' & topic.Joystick_Commands |  m0.value in VL and m0.value = m1.value)}
	
	all t: Time-last,  m0 : Translator.inbox.t & topic.Joystick_Commands | some t': t.nexts| { m0.value in VL 
				implies (some m1: Translator.outbox.t' & topic.Joystick_Vel_Linear| m0.value = m1.value ) }
	}


➀fact Agrob_Planner_Behaviour {	
	
	all t: Time | lone (Agrob_Planner.inbox.t & topic.Goal_Pose)	--1 queue size for Goal_Pose, Current_Pose topic
	all t: Time | lone (Agrob_Planner.inbox.t & topic.Current_Pose)
	
	all t: Time-first|  some t': t.prevs | {(some Agrob_Planner.outbox.t)
			implies (some goal: (Agrob_Planner.inbox.t' & topic.Goal_Pose), c_pose : (Agrob_Planner.inbox.t' & topic.Current_Pose) | goal.value != c_pose.value)}
		
	all t: Time-last |some t': t.nexts| 
			 {(some goal: (Agrob_Planner.inbox.t & topic.Goal_Pose), c_pose : (Agrob_Planner.inbox.t & topic.Current_Pose) |goal.value != c_pose.value)
				implies  some Agrob_Planner.outbox.t'}
	
		
	all t: Time-first|some  t': t.prevs |{ (some m: Agrob_Planner.outbox.t| m.value in Zero)
			implies (some m: Agrob_Planner.inbox.t' & (topic.Vertical_PointCloud + topic.Map) | m.value in (DR + UC + Unknown))}
	
	all t: Time-last |some t': t.nexts|{ (some m: Agrob_Planner.inbox.t & (topic.Vertical_PointCloud + topic.Map)  | 
			 m.value in (DR + UC + Unknown))
			implies  (some m: Agrob_Planner.outbox.t' | m.value in Zero)}
		
	all t: Time-first| some  t': t.prevs| {(some m: Agrob_Planner.outbox.t | m.value in (VL - Zero) )
			implies ( (some m: Agrob_Planner.inbox.t' & topic.Vertical_PointCloud | m.value in SR) and 
								(some m: Agrob_Planner.inbox.t' & topic.Map | m.value in SC) )}

}➀

➁fact Safety_Controller_Filter_Behaviour_Control_Buttons { ----
	
	all t: Time-first, m1: Safety_Controller_Filter.outbox.t & topic.Joystick_Commands_Filtered |some t': t.prevs| {
		m1.value in (LB + RB) 
			implies ( (some m0: Safety_Controller_Filter.inbox.t' & topic.Joystick_Commands | m0.value = m1.value ) and preconditions_side_buttons_filter)	}
									
	all t: Time-first, m1: Safety_Controller_Filter.outbox.t & topic.Joystick_Commands_Filtered | some t': t.prevs|{
		 not (m1.value in (LB + RB) )
			implies (some m0 : Safety_Controller_Filter.inbox.t' & topic.Joystick_Commands | m0.value = m1.value) }	
	
	all t: Time-last, m0 : Safety_Controller_Filter.inbox.t & topic.Joystick_Commands| some t':t.nexts |{ 
		(m0.value in (LB + RB)  and preconditions_side_buttons_filter)
			implies  (some m1: Safety_Controller_Filter.outbox.t' & topic.Joystick_Commands_Filtered | m0.value = m1.value)}
		
	all t: Time-last, m0 : Safety_Controller_Filter.inbox.t & topic.Joystick_Commands | some t': t.nexts|{
		 not (m0.value in (LB + RB)) 
			implies  (some m1: Safety_Controller_Filter.outbox.t' & topic.Joystick_Commands_Filtered | m0.value = m1.value)}
	}➁
-- Controller Filter aux preds
➁pred preconditions_side_buttons_filter {---
	some t: Time-first-last| one t':Time | t' in t.prevs and  joy_wall_button_filter_pred[t']
	and (not joy_goline_button_filter_pred[t'.nexts]) 
	}➁
➁pred joy_goline_button_filter_pred[t: Time]{----
	(some m0: Safety_Controller_Filter.inbox.t & topic.Joystick_Commands | m0.value in GLB)
	}➁
➁pred joy_wall_button_filter_pred [  t: Time]{----
	(some m0: Safety_Controller_Filter.inbox.t & topic.Joystick_Commands | m0.value in WB)
	}➁


fact Supervisor_Behaviour {	
		
	all t: Time-first | some t':t.prevs| {(some m1: (Supervisor.outbox.t & topic.Supervisor_Vel_Linear) | m1.value in PL)
			implies (some m0:Supervisor.inbox.t' & topic.(➋Joystick_Commands➋+ ➁Joystick_Commands_Filtered➁) | m0.value in (RB + LB + GLB))}
	
	
	all t: Time-first|some t' :t.prevs|{ (  some m1: (Supervisor.outbox.t & topic.Supervisor_Vel_Linear)|  m1.value in GL and m1.value not in (RL + LL))
			 implies (some m0:Supervisor.inbox.t' & topic.(➋Joystick_Commands➋+ ➁Joystick_Commands_Filtered➁)  | m0.value in GLB) }
	
	all t: Time-first| some t': t.prevs| {(some m1: (Supervisor.outbox.t & topic.Supervisor_Vel_Linear) | m1.value in (RL + LL) )
			implies (some m0:Supervisor.inbox.t' & topic.(➋Joystick_Commands➋+ ➁Joystick_Commands_Filtered➁)  | m0.value in GLB or m0.value in (RB + LB))}
	
	all t: Time-last | some t': t.next| {( some m0:Supervisor.inbox.t & topic.(➋Joystick_Commands➋+ ➁Joystick_Commands_Filtered➁)  | m0.value in GLB)
			 implies  some m1: (Supervisor.outbox.t' & topic.Supervisor_Vel_Linear) | m1.value in GL}

	all t: Time -last |some t': t.next| { (some m0:Supervisor.inbox.t & topic.(➋Joystick_Commands➋+ ➁Joystick_Commands_Filtered➁) |  m0.value in (RB + LB)  )
			implies  some m1: (Supervisor.outbox.t' & topic.Supervisor_Vel_Linear) | m1.value in (RL + LL)}	

		

	all t: Time-first |some t':t.prevs |{ (some m1: Supervisor.outbox.t & topic.Current_State | m1.value in GLS)
			implies  (some m0: (Supervisor.inbox.t' & topic.(➋Joystick_Commands➋+ ➁Joystick_Commands_Filtered➁) ) | m0.value in GLB)}

	all t: Time-first|some t':t.prevs| {( some m1: Supervisor.outbox.t & topic.Current_State | m1.value in WS  )
			implies  (some m0: (Supervisor.inbox.t' & topic.(➋Joystick_Commands➋+ ➁Joystick_Commands_Filtered➁) ) | m0.value in WB)}

	all t: Time-first|some t':t.prevs | {(some m1: Supervisor.outbox.t & topic.Current_State |m1.value in IS)
			implies some m0: (Supervisor.inbox.t' & topic.(➋Joystick_Commands➋+ ➁Joystick_Commands_Filtered➁) ) | (m0.value not in GLB) and  (m0.value not in WB) and (m0.value in (VL + JC))}

		
	all t: Time -last|some t': t.nexts| {( some m0: (Supervisor.inbox.t & topic.(➋Joystick_Commands➋+ ➁Joystick_Commands_Filtered➁) )  | m0.value in GLB)
			implies  (some m1: Supervisor.outbox.t' & topic.Current_State | m1.value in GLS)  }	
		
	all t: Time -last|some t': t.nexts |{(some m0: (Supervisor.inbox.t & topic.(➋Joystick_Commands➋+ ➁Joystick_Commands_Filtered➁) )  | m0.value in WB)
		 	implies  some m1: Supervisor.outbox.t' & topic.Current_State | m1.value in WS}
		
	all t: Time -last|some t': t.nexts| {(some m0: (Supervisor.inbox.t & topic.(➋Joystick_Commands➋+ ➁Joystick_Commands_Filtered➁) ) | (m0.value not in (GLB + WB)) and (m0.value in (VL + JC)))
			implies  (some m1: Supervisor.outbox.t' & topic.Current_State | m1.value in IS)}				
	
	
	all t: Time-first|some t': t.prevs|{ (some m1: (Supervisor.outbox.t & (topic.Max_Vel_Linear + topic.Supervisor_Vel_Linear)) | ( m1.value in Zero)) 
			implies (some m0:Supervisor.inbox.t' & (topic.Vertical_PointCloud + topic.Horizontal_PointCloud) | m0.value in DR) }	
	
	all t: Time -last| some t': t.nexts| {(some m0:Supervisor.inbox.t & (topic.Vertical_PointCloud + topic.Horizontal_PointCloud)| m0.value in DR )
			implies  ( (some m1: (Supervisor.outbox.t' & topic.Max_Vel_Linear) | m1.value in Zero) and
							 (some m2: (Supervisor.outbox.t'& topic.Supervisor_Vel_Linear) | m2.value in Zero)) }		
	-- Refactored
	-- Extra property. Constraints the publication on Max_Vel_Linear topic to Zero value only.
		all t: Time, m1: (Supervisor.outbox.t & topic.Max_Vel_Linear) | m1.value in (Zero + PL) 
	
	}

fact Multiplexer_Behaviour_Map {	
	--1 queue size for Max_Vel_Linear topic
	all t: Time|   lone (Multiplexer.inbox.t & topic.Max_Vel_Linear) 
		-- For non-Zero values
	all t:Time-first| some t': t.prevs| { all m1: (Multiplexer.outbox.t & topic.Husky_Vel_Linear) | {➋(m1.value not in Zero)  implies 
			  (all max : (Multiplexer.inbox.t' & topic.Max_Vel_Linear) | max.value != Zero)➋ and ➁(all max : (Multiplexer.inbox.t' & topic.Max_Vel_Linear) | max.value != Zero)➁ and
			  (some (Multiplexer.inbox.t' & (topic.Supervisor_Vel_Linear+➀ topic.External_Vel_Linear➀))
							 implies (some m0: (Multiplexer.inbox.t' & topic.Supervisor_Vel_Linear) | m0.value = m1.value)
							else (some m0 : (Multiplexer.inbox.t' & topic.Joystick_Vel_Linear) | m0.value = m1.value)) }}

	all t:Time-last,m0: (Multiplexer.inbox.t & (topic.Supervisor_Vel_Linear  +topic. Joystick_Vel_Linear+➀topic.External_Vel_Linear➀)) | some t': t.nexts|
			{ (Zero not in (Multiplexer.inbox.t & topic.Max_Vel_Linear).value)
				 implies (some m1: Multiplexer.outbox.t' & topic.Husky_Vel_Linear | m1.value = m0.value)}
																										 	
		-- For Zero values
	all t: Time-first |some t':t.prevs| {( some m1: (Multiplexer.outbox.t & topic.Husky_Vel_Linear)| (m1.value in Zero))
			implies (some m0: (Multiplexer.inbox.t' & (➊topic.Max_Vel_Linear➊+topic.Supervisor_Vel_Linear +➀topic.External_Vel_Linear➀+ topic.Joystick_Vel_Linear)) | m0.value in Zero)}
			-- Required additional condition ( Refactored_map)

	
	all t: Time-last |some t': t.nexts | {( some m0: (Multiplexer.inbox.t & topic.Max_Vel_Linear)|  m0.value in Zero)
						implies  some m1: (Multiplexer.outbox.t' & topic.Husky_Vel_Linear) | (m1.value in Zero)} 
	
	}


-- Assumptions
pred limited_control_assumption {
	all t: Time,  m: Controller.outbox.t | m.value in JC 
	}

-- Properties
pred goline_state_safe{	
	all t: Time-first| some t': t.prevs |{(some m1: Supervisor_GUI.inbox.t | m1.value in GLS)
		 	implies (some m0: Controller.outbox.t' | m0.value in GLB) 
		    }
	}

pred wall_state_safe{	
	all t: Time-first| some t':t.prevs| (some m1: Supervisor_GUI.inbox.t | m1.value in WS)
			 implies  (some m0: Controller.outbox.t' | m0.value in WB) 
	
	}

pred idle_state_safe{
	all t: Time-first| some t': t.prevs |{
		(some m0: Supervisor_GUI.inbox.t | m0.value in IS)
			implies (some m1: Controller.outbox.t' | m1.value not in (GLB + WB))
	}
	}

pred danger_range_safe{
	all t: Time-first| some t': t.prevs |{
		(some m1: Husky_Base.inbox.t | m1.value in Zero) 
			implies (some m0: (Horizontal_Laser + Vertical_Laser).outbox.t' | m0.value in DR)	
		}
	}


pred base_linear_safe{
	all t: Time-first| some t': t.prevs |{
		(some m1: Husky_Base.inbox.t | m1.value in PL)
			implies (some m0: Controller.outbox.t' | m0.value in (WB + GLB + PL))
		}
	}

pred base_linear_safe2 {
	all t: Time| one t': Time| { t' in t.prevs and
		(some m: Husky_Base.inbox.t' | m.value in (GL - RL - LL)) 
			implies (  (some m: Controller.outbox.t' | m.value in GLB) and 
				 ((not (some m: Controller.outbox.(t.nexts) | m.value in (RB + LB) )) ) )
	}
	}

pred actuators_safe{
	all t: Time-last| some t': t.nexts|( some m1: Husky_Base.inbox.t' | m1.value in PL) 
			implies (all t: Time-last| some t': t.nexts| 
					some m2: Supervisor_GUI.inbox.t' | m2.value in (WS + GLS))
	}

pred danger_range_liveness{
	some t: Time |{(some m0: (Horizontal_Laser + Vertical_Laser).outbox.t | m0.value in DR) 
		implies  (some m1: Husky_Base.inbox.(t.nexts) | m1.value in Zero) }
	}



-- Verification
assert prop1_octo { 
	goline_state_safe
	} 

check prop1_octo  for 15 Value, 10 Message, 10 Time
check prop1_octo with exactly ➊,➋ for 15 Value, 10 Message, 10 Time
check prop1_octo with  ➊,➋ for 15 Value, 10 Message, 10 Time
check prop1_octo with exactly ➀,➋ for 15 Value, 10 Message, 10 Time
check prop1_octo with  ➀,➋ for 15 Value, 10 Message, 10 Time
check prop1_octo with exactly ➊,➁ for 15 Value, 10 Message, 10 Time
check prop1_octo with  ➊,➁ for 15 Value, 10 Message, 10 Time
check prop1_octo with exactly ➀,➁ for 15 Value, 10 Message, 10 Time
check prop1_octo with  ➀,➁ for 15 Value, 10 Message, 10 Time

check prop1_octo with exactly ➀ for 11 Value, 10 Message, 10 Time
-- No counterexample found
-- time : 581543 ms
-- time after refactoring : 76547 ms

assert prop2_octo {
	wall_state_safe
}

 check prop2_octo for 11 Value, 10 Message, 10 Time
-- No counterexample found
-- time : 568742 ms
-- time after refactoring : 77536 ms

assert  prop3_octo {
	 idle_state_safe
}

check  prop3_octo for 11 Value, 10 Message, 10 Time
check  prop3_octo with exactly ➊ for 11 Value, 10 Message, 10 Time
check  prop3_octo with exactly ➀ for 11 Value, 10 Message, 10 Time


assert prop4_octo{
	danger_range_safe
	}

check prop4_octo for 15 Value, 10 Message, 10 Time
check prop4_octo with exactly ➊,➋ for 15 Value, 10 Message, 10 Time
check prop4_octo with  ➊,➋ for 15 Value, 10 Message, 10 Time
check prop4_octo with exactly ➀,➋ for 15 Value, 10 Message, 10 Time
check prop4_octo with  ➀,➋ for 15 Value, 10 Message, 10 Time
check prop4_octo with exactly ➊,➁ for 15 Value, 10 Message, 10 Time
check prop4_octo with  ➊,➁ for 15 Value, 10 Message, 10 Time
check prop4_octo with exactly ➀,➁ for 15 Value, 10 Message, 10 Time
check prop4_octo with  ➀,➁ for 15 Value, 10 Message, 10 Time


check prop5_octo {							
	base_linear_safe
} for 11 Value, 10 Message, 10 Time


check prop6_octo{									-- this property is badly expressed due to the intervals abstraction	
	limited_control_assumption implies base_linear_safe2
} for 12 Value, 10 Message, 10 Time						

assert  prop7_octo{
	 limited_control_assumption and ➁(no Rviz)➁ implies actuators_safe	
	} 

check  prop7_octo for 15 Value, 10 Message, 10 Time
-- Counterexample was found
check  prop7_octo with exactly ➊,➋ for 15 Value, 10 Message, 10 Time
check  prop7_octo with  ➊,➋ for 15 Value, 10 Message, 10 Time
-- Counterexample was found
check  prop7_octo with exactly ➀ for 15 Value, 10 Message, 10 Time
check  prop7_octo with  ➀,➋ for 15 Value, 10 Message, 10 Time
--no counterexample found
check  prop7_octo with exactly ➁ for 15 Value, 10 Message, 10 Time
check  prop7_octo with  ➊,➁ for 15 Value, 10 Message, 10 Time

check  prop7_octo with exactly ➀,➁ for 15 Value, 10 Message, 10 Time
check  prop7_octo with exactly ➀,➁ for 15 Value, 10 Message, 10 Time

assert  prop8_octo{
	 danger_range_liveness
	} 

check  prop8_octo for 15 Value, 10 Message, 10 Time-- counterexample
check  prop8_octo  with exactly ➊,➋ for 15 Value, 10 Message, 10 Time  -- counterexample
check  prop8_octo  with  ➊,➋ for 15 Value, 10 Message, 10 Time
check  prop8_octo  with exactly ➀ for 15 Value, 10 Message, 10 Time-- counterexample
check  prop8_octo  with  ➀,➋ for 15 Value, 10 Message, 10 Time
check  prop8_octo  with exactly ➁ for 15 Value, 10 Message, 10 Time-- counterexample
check  prop8_octo  with  ➊,➁ for 15 Value, 10 Message, 10 Time
check  prop8_octo  with exactly ➀,➁ for 15 Value, 10 Message, 10 Time -- no  counterexample
check  prop8_octo  with  ➀,➁ for 15 Value, 10 Message, 10 Time--no -- counterexample

pred testInstance {	
	some t: Time-last |  some Husky_Base.inbox.(t.nexts)
}

run testInstance  for 8 Value, 8 Message, 7 Time


