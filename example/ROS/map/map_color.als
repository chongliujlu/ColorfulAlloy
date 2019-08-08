module Map
open meta
/**
* ➀:  Add "RViz", "Map_server",  "Location_perfect_Match" sensor node and a "Node Agrob_Planner" node
* ➁:  Add safe control (add "Node Safety_controller_Filter" node)
* ➂:  Represent the cases that either feature ➀ or feature ➁ is selected
*/

fact FM{
	➀➁ some none ➁➀
	//feature ➂ is the disjunction of ➀ and ➁
	➀➌some none➌➀
	➁➌ some none➌➁
	➂➊➋some none➋➊➂
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
-- Joystick Control Buttons
sig RB, LB, GLB, WB in JC{}

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
-- Laser Scan Values	
sig SR, DR in LS {} 	

fact LS_constraints {
	LS in (SR + DR)
	no SR & DR					
	}

abstract sig S extends Value{}
-- State Values
sig IS, WS, GLS in S {}

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
➂abstract sig Pose extends Value{}➂ -- Pose Values
--for feature ➀ or ➁
➂abstract sig OG extends Value {}➂ -- Occupancy Grid Values
➂sig Unknown, SC, UC in OG {}➂	-- Unknown, Safe Cell, Unsafe Cell
--for feature ➀ or ➁
➂fact OG_constraints {
	OG in (Unknown + SC + UC)
	no Unknown & (SC + UC)
	no SC & (Unknown + UC)
	no UC & (Unknown + SC)
	lone Unknown
	lone SC
	lone UC
	}➂

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
➂one sig Goal_Pose, 
		Map,
		Current_Pose,
		External_Vel_Linear
extends Topic{}➂

➁one sig Joystick_Commands_Filtered extends Topic{}➁

-- Topic message type constraints
fact topic_predicates {	 
	all m: topic.Horizontal_PointCloud | m.value in(➌ LS➌+➂DR➂) 

	all m: topic.Vertical_PointCloud | m.value in (➌LS➌+➂DR➂)
	all m: topic.Joystick_Commands | m.value in (JC + PL)
	all m: topic.Joystick_Vel_Linear | m.value in (➌VL➌+➂DR➂)
	--for feature ➀ or ➁
	➂all m: topic.Goal_Pose | m.value in Pose➂
	➂all m: topic.Map | m.value in OG➂
	➂all m: topic.Current_Pose | m.value in Pose➂

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
-- Map only, ➀ or ➁
➂one sig Rviz extends Sensor {}{	
	advertises = Goal_Pose	
	}➂
-- Map only,➀ or ➁
➂one sig Map_Server extends Sensor {}{
	advertises = Map	
	}➂
-- Map only (abstracted to a sensor), ➀ or ➁
➂one sig Localization_Perfect_Match extends Sensor {}{	
	advertises = Current_Pose
	}➂
-- Map only
➂one sig Agrob_Planner extends Node {}{
	subscribes = Goal_Pose + Map + Current_Pose + Vertical_PointCloud 
	advertises = External_Vel_Linear
	}➂

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
	subscribes = Supervisor_Vel_Linear + Max_Vel_Linear + Joystick_Vel_Linear+➂➀External_Vel_Linear➀➂
	advertises = Husky_Vel_Linear
	}
one sig Supervisor_GUI extends Actuator {}{
	subscribes = Current_State
	}
one sig Husky_Base extends Actuator{}{
	subscribes = Husky_Vel_Linear
	}


fact Translator_Behaviour {
	all t: Time-first, m1: Translator.outbox.t & topic.Joystick_Vel_Linear | 
		some t': t.prevs, m0: Translator.inbox.t' & topic.Joystick_Commands |  m0.value in VL and m0.value = m1.value
	
	all t: Time-last,  m0 : Translator.inbox.t & topic.Joystick_Commands | { m0.value in VL 
				implies (some t': t.nexts, m1: Translator.outbox.t' & topic.Joystick_Vel_Linear| m0.value = m1.value ) }
	}


➂fact Agrob_Planner_Behaviour {	
	--1 queue size for Goal_Pose, Current_Pose topic
	all t: Time | lone (Agrob_Planner.inbox.t & topic.Goal_Pose)	
	all t: Time | lone (Agrob_Planner.inbox.t & topic.Current_Pose)
	
	all t: Time-first| {(some Agrob_Planner.outbox.t)
			implies (some t': t.prevs, goal: (Agrob_Planner.inbox.t' & topic.Goal_Pose), 
					c_pose : (Agrob_Planner.inbox.t' & topic.Current_Pose) | goal.value != c_pose.value)}
		
	all t: Time-last | (some goal: (Agrob_Planner.inbox.t & topic.Goal_Pose), c_pose : (Agrob_Planner.inbox.t & topic.Current_Pose) |goal.value != c_pose.value)
				implies (some t': t.nexts|some Agrob_Planner.outbox.t')
	
		
	all t: Time-first| (some m: Agrob_Planner.outbox.t| m.value in Zero)
			implies (some t': t.prevs, m: Agrob_Planner.inbox.t' & (topic.Vertical_PointCloud + topic.Map) | m.value in (DR + UC + Unknown))
	
	all t: Time-last | (some m: Agrob_Planner.inbox.t & (topic.Vertical_PointCloud + topic.Map)  |  m.value in (DR + UC + Unknown))
			implies  ( some t': t.nexts, m: Agrob_Planner.outbox.t' | m.value in Zero)
		
	all t: Time-first| (some m: Agrob_Planner.outbox.t | m.value in (VL - Zero) )
			implies ( some t': t.prevs| {(some m: Agrob_Planner.inbox.t' & topic.Vertical_PointCloud | m.value in SR) and 
								(some m: Agrob_Planner.inbox.t' & topic.Map | m.value in SC) })
	}➂


➁fact Safety_Controller_Filter_Behaviour_Control_Buttons { 
	
	all t: Time-first, m1: Safety_Controller_Filter.outbox.t & topic.Joystick_Commands_Filtered |{
		m1.value in (LB + RB) 
			implies ( (some  t': t.prevs, m0: Safety_Controller_Filter.inbox.t' & topic.Joystick_Commands | m0.value = m1.value ) and preconditions_side_buttons_filter)	}
									
	all t: Time-first, m1: Safety_Controller_Filter.outbox.t & topic.Joystick_Commands_Filtered |
		 not (m1.value in (LB + RB) )
			implies (some t': t.prevs, m0 : Safety_Controller_Filter.inbox.t' & topic.Joystick_Commands | m0.value = m1.value) 	
	
	all t: Time-last, m0 : Safety_Controller_Filter.inbox.t & topic.Joystick_Commands|
		(m0.value in (LB + RB)  and preconditions_side_buttons_filter)
			implies  (some  t':t.nexts,  m1: Safety_Controller_Filter.outbox.t' & topic.Joystick_Commands_Filtered | m0.value = m1.value)
		
	all t: Time-last, m0 : Safety_Controller_Filter.inbox.t & topic.Joystick_Commands | 
		 not (m0.value in (LB + RB)) 
			implies  (some t': t.nexts, m1: Safety_Controller_Filter.outbox.t' & topic.Joystick_Commands_Filtered | m0.value = m1.value)
	}➁
-- Controller Filter aux preds
➁pred preconditions_side_buttons_filter {
	some t: Time-first-last| one t':Time | t' in t.prevs and  joy_wall_button_filter_pred[t']
	and (not joy_goline_button_filter_pred[t'.nexts]) 
	}➁
➁pred joy_goline_button_filter_pred[t: Time]{
	(some m0: Safety_Controller_Filter.inbox.t & topic.Joystick_Commands | m0.value in GLB)
	}➁
➁pred joy_wall_button_filter_pred [  t: Time]{
	(some m0: Safety_Controller_Filter.inbox.t & topic.Joystick_Commands | m0.value in WB)
	}➁


fact Supervisor_Behaviour {	
		
	all t: Time-first | (some m1: (Supervisor.outbox.t & topic.Supervisor_Vel_Linear) | m1.value in PL)
			implies (some t':t.prevs, m0:Supervisor.inbox.t' & topic.(➋Joystick_Commands➋+ ➁Joystick_Commands_Filtered➁) | m0.value in (RB + LB + GLB))
	
	all t: Time-first| (  some m1: (Supervisor.outbox.t & topic.Supervisor_Vel_Linear)|  m1.value in GL and m1.value not in (RL + LL))
			 implies (some t' :t.prevs, m0:Supervisor.inbox.t' & topic.(➋Joystick_Commands➋+ ➁Joystick_Commands_Filtered➁)  | m0.value in GLB) 
	
	all t: Time-first| (some m1: (Supervisor.outbox.t & topic.Supervisor_Vel_Linear) | m1.value in (RL + LL) )
			implies (some  t': t.prevs, m0:Supervisor.inbox.t' & topic.(➋Joystick_Commands➋+ ➁Joystick_Commands_Filtered➁)  | m0.value in GLB or m0.value in (RB + LB))
	
	all t: Time-last | ( some m0:Supervisor.inbox.t & topic.(➋Joystick_Commands➋+ ➁Joystick_Commands_Filtered➁)  | m0.value in GLB)
			 implies  some  t': t.next, m1: (Supervisor.outbox.t' & topic.Supervisor_Vel_Linear) | m1.value in GL

	all t: Time -last | (some m0:Supervisor.inbox.t & topic.(➋Joystick_Commands➋+ ➁Joystick_Commands_Filtered➁) |  m0.value in (RB + LB)  )
			implies  some t': t.next, m1: (Supervisor.outbox.t' & topic.Supervisor_Vel_Linear) | m1.value in (RL + LL)	

		

	all t: Time-first | (some m1: Supervisor.outbox.t & topic.Current_State | m1.value in GLS)
			implies  (some t':t.prevs , m0: (Supervisor.inbox.t' & topic.(➋Joystick_Commands➋+ ➁Joystick_Commands_Filtered➁) ) | m0.value in GLB)

	all t: Time-first| ( some m1: Supervisor.outbox.t & topic.Current_State | m1.value in WS  )
			implies  (some t':t.prevs, m0: (Supervisor.inbox.t' & topic.(➋Joystick_Commands➋+ ➁Joystick_Commands_Filtered➁) ) | m0.value in WB)

	all t: Time-first|(some m1: Supervisor.outbox.t & topic.Current_State |m1.value in IS)
			implies some t':t.prevs , m0: (Supervisor.inbox.t' & topic.(➋Joystick_Commands➋+ ➁Joystick_Commands_Filtered➁) ) | (m0.value not in GLB) and  (m0.value not in WB) and (m0.value in (VL + JC))

		
	all t: Time -last|( some m0: (Supervisor.inbox.t & topic.(➋Joystick_Commands➋+ ➁Joystick_Commands_Filtered➁) )  | m0.value in GLB)
			implies  (some t': t.nexts, m1: Supervisor.outbox.t' & topic.Current_State | m1.value in GLS)  
		
	all t: Time -last|(some m0: (Supervisor.inbox.t & topic.(➋Joystick_Commands➋+ ➁Joystick_Commands_Filtered➁) )  | m0.value in WB)
		 	implies  some t': t.nexts, m1: Supervisor.outbox.t' & topic.Current_State | m1.value in WS
		
	all t: Time -last|some t': t.nexts| {(some m0: (Supervisor.inbox.t & topic.(➋Joystick_Commands➋+ ➁Joystick_Commands_Filtered➁) ) | (m0.value not in (GLB + WB)) and (m0.value in (VL + JC)))
			implies  (some m1: Supervisor.outbox.t' & topic.Current_State | m1.value in IS)}				
	
	
	all t: Time-first|(some m1: (Supervisor.outbox.t & (topic.Max_Vel_Linear + topic.Supervisor_Vel_Linear)) | ( m1.value in Zero)) 
			implies (some t': t.prevs, m0:Supervisor.inbox.t' & (topic.Vertical_PointCloud + topic.Horizontal_PointCloud) | m0.value in DR) 	
	
	all t: Time -last| (some m0:Supervisor.inbox.t & (topic.Vertical_PointCloud + topic.Horizontal_PointCloud)| m0.value in DR )
			implies  (some t': t.nexts| {(some m1: (Supervisor.outbox.t' & topic.Max_Vel_Linear) | m1.value in Zero) and
							 (some m2: (Supervisor.outbox.t'& topic.Supervisor_Vel_Linear) | m2.value in Zero)} ) 	
	-- Refactored
	-- Extra property. Constraints the publication on Max_Vel_Linear topic to Zero value only.
		all t: Time, m1: (Supervisor.outbox.t & topic.Max_Vel_Linear) | m1.value in (Zero + PL) 
	
	}

fact Multiplexer_Behaviour {	
	--1 queue size for Max_Vel_Linear topic
	all t: Time|   lone (Multiplexer.inbox.t & topic.Max_Vel_Linear) 
		-- For non-Zero values
	all t:Time-first| some t': t.prevs| { all m1: (Multiplexer.outbox.t & topic.Husky_Vel_Linear) | {
		➋((m1.value not in Zero)  implies (all max : (Multiplexer.inbox.t' & topic.Max_Vel_Linear) | max.value != Zero))➋ 
		and ➁(all max : (Multiplexer.inbox.t' & topic.Max_Vel_Linear) | max.value != Zero)➁ 		
		and (some (Multiplexer.inbox.t' & topic.(Supervisor_Vel_Linear+➂➀External_Vel_Linear➀➂))
			implies (some m0: (Multiplexer.inbox.t' & topic.(Supervisor_Vel_Linear+ ➂➀External_Vel_Linear➀➂)) | m0.value = m1.value)
			else (some m0 : (Multiplexer.inbox.t' & topic.Joystick_Vel_Linear) | m0.value = m1.value)) }}

	all t:Time-last,m0: (Multiplexer.inbox.t & topic.(Supervisor_Vel_Linear  +Joystick_Vel_Linear+➂➀External_Vel_Linear➀➂)) |
		{ (Zero not in (Multiplexer.inbox.t & topic.Max_Vel_Linear).value)
			implies (some t': t.nexts, m1: Multiplexer.outbox.t' & topic.Husky_Vel_Linear | m1.value = m0.value)}
																										 	
		-- For Zero values
	all t: Time-first | ( some m1: (Multiplexer.outbox.t & topic.Husky_Vel_Linear)| (m1.value in Zero))
		implies (some t':t.prevs, m0: (Multiplexer.inbox.t' & topic.(➊Max_Vel_Linear➊+Supervisor_Vel_Linear +➂➀External_Vel_Linear➀➂+ Joystick_Vel_Linear)) | m0.value in Zero)
			-- Required additional condition ( Refactored_map)

	
	all t: Time-last | ( some m0: (Multiplexer.inbox.t & topic.Max_Vel_Linear)|  m0.value in Zero)
					implies  some t': t.nexts, m1: (Multiplexer.outbox.t' & topic.Husky_Vel_Linear) | (m1.value in Zero)
	
	}


-- Assumptions
pred limited_control_assumption {
	all t: Time,  m: Controller.outbox.t | m.value in JC 
	}

-- Properties
pred goline_state_safe{	
	all t: Time-first |{(some m1: Supervisor_GUI.inbox.t | m1.value in GLS)
		 	implies ( some t': t.prevs, m0: Controller.outbox.t' | m0.value in GLB) 
		    }
	}

pred wall_state_safe{	
	all t: Time-first| (some m1: Supervisor_GUI.inbox.t | m1.value in WS)
			 implies  (some t':t.prevs, m0: Controller.outbox.t' | m0.value in WB) 
	
	}

pred idle_state_safe{
	all t: Time-first |{
		(some m0: Supervisor_GUI.inbox.t | m0.value in IS)
			implies (some t': t.prevs, m1: Controller.outbox.t' | m1.value not in (GLB + WB))
	}
	}

pred danger_range_safe{
	all t: Time-first |
		(some m1: Husky_Base.inbox.t | m1.value in Zero) 
			implies ( some t': t.prevs, m0: (Horizontal_Laser + Vertical_Laser).outbox.t' | m0.value in DR)	
	}


pred base_linear_safe{
	all t: Time-first|{
		(some m1: Husky_Base.inbox.t | m1.value in PL)
			implies (some t': t.prevs,  m0: Controller.outbox.t' | m0.value in (WB + GLB + PL))
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
	all t: Time-last| ( some t': t.nexts, m1: Husky_Base.inbox.t' | m1.value in PL) 
			implies (all t'': Time-last| 
					some  t''': t''.nexts, m2: Supervisor_GUI.inbox.t''' | m2.value in (WS + GLS))
	}

pred danger_range_liveness{
	some t: Time |{(some m0: (Horizontal_Laser + Vertical_Laser).outbox.t | m0.value in DR) 
		implies  (some m1: Husky_Base.inbox.(t.nexts) | m1.value in Zero) }
	}


-- Verification
assert prop1 { 
	goline_state_safe
	} 
-- No counterexample found
check prop1  for 15 Value, 10 Message, 10 Time
check prop1 with exactly ➊,➋,➌ for 15 Value, 10 Message, 10 Time
check prop1 with  ➊,➋,➌ for 15 Value, 10 Message, 10 Time
check prop1 with exactly ➀,➋,➌ for 15 Value, 10 Message, 10 Time
check prop1 with  ➀,➋,➌ for 15 Value, 10 Message, 10 Time
check prop1 with exactly ➊,➁,➌ for 15 Value, 10 Message, 10 Time
check prop1 with  ➊,➁,➌ for 15 Value, 10 Message, 10 Time
check prop1 with exactly ➊,➋,➂ for 15 Value, 10 Message, 10 Time
check prop1 with  ➊,➋,➂ for 15 Value, 10 Message, 10 Time
check prop1 with exactly ➀,➁,➌ for 15 Value, 10 Message, 10 Time
check prop1 with  ➀,➁,➌ for 15 Value, 10 Message, 10 Time
check prop1 with exactly ➀,➋,➂ for 15 Value, 10 Message, 10 Time
check prop1 with  ➀,➋,➂ for 15 Value, 10 Message, 10 Time
check prop1 with exactly ➊,➁,➂ for 15 Value, 10 Message, 10 Time
check prop1 with  ➊,➁,➂ for 15 Value, 10 Message, 10 Time
check prop1 with exactly ➀,➁,➂ for 15 Value, 10 Message, 10 Time
check prop1 with  ➀,➁,➂ for 15 Value, 10 Message, 10 Time



assert prop2 {
	wall_state_safe
}
-- No counterexample found
check prop2  for 15 Value, 10 Message, 10 Time
check prop2 with exactly ➊,➋,➌ for 15 Value, 10 Message, 10 Time
check prop2 with  ➊,➋,➌ for 15 Value, 10 Message, 10 Time
check prop2 with exactly ➀,➋,➌ for 15 Value, 10 Message, 10 Time
check prop2 with  ➀,➋,➌ for 15 Value, 10 Message, 10 Time
check prop2 with exactly ➊,➁,➌ for 15 Value, 10 Message, 10 Time
check prop2 with  ➊,➁,➌ for 15 Value, 10 Message, 10 Time
check prop2 with exactly ➊,➋,➂ for 15 Value, 10 Message, 10 Time
check prop2 with  ➊,➋,➂ for 15 Value, 10 Message, 10 Time
check prop2 with exactly ➀,➁,➌ for 15 Value, 10 Message, 10 Time
check prop2 with  ➀,➁,➌ for 15 Value, 10 Message, 10 Time
check prop2 with exactly ➀,➋,➂ for 15 Value, 10 Message, 10 Time
check prop2 with  ➀,➋,➂ for 15 Value, 10 Message, 10 Time
check prop2 with exactly ➊,➁,➂ for 15 Value, 10 Message, 10 Time
check prop2 with  ➊,➁,➂ for 15 Value, 10 Message, 10 Time
check prop2 with exactly ➀,➁,➂ for 15 Value, 10 Message, 10 Time
check prop2 with  ➀,➁,➂ for 15 Value, 10 Message, 10 Time



assert  prop3 {
	 idle_state_safe
}
-- No counterexample found
check prop3  for 15 Value, 10 Message, 10 Time
check prop3 with exactly ➊,➋,➌ for 15 Value, 10 Message, 10 Time
check prop3 with  ➊,➋,➌ for 15 Value, 10 Message, 10 Time
check prop3 with exactly ➀,➋,➌ for 15 Value, 10 Message, 10 Time
check prop3 with  ➀,➋,➌ for 15 Value, 10 Message, 10 Time
check prop3 with exactly ➊,➁,➌ for 15 Value, 10 Message, 10 Time
check prop3 with  ➊,➁,➌ for 15 Value, 10 Message, 10 Time
check prop3 with exactly ➊,➋,➂ for 15 Value, 10 Message, 10 Time
check prop3 with  ➊,➋,➂ for 15 Value, 10 Message, 10 Time
check prop3 with exactly ➀,➁,➌ for 15 Value, 10 Message, 10 Time
check prop3 with  ➀,➁,➌ for 15 Value, 10 Message, 10 Time
check prop3 with exactly ➀,➋,➂ for 15 Value, 10 Message, 10 Time
check prop3 with  ➀,➋,➂ for 15 Value, 10 Message, 10 Time
check prop3 with exactly ➊,➁,➂ for 15 Value, 10 Message, 10 Time
check prop3 with  ➊,➁,➂ for 15 Value, 10 Message, 10 Time
check prop3 with exactly ➀,➁,➂ for 15 Value, 10 Message, 10 Time
check prop3 with  ➀,➁,➂ for 15 Value, 10 Message, 10 Time


assert prop4{
	danger_range_safe
	}

check prop4  for 15 Value, 10 Message, 10 Time	--  counterexample 
check prop4 with exactly ➊,➋,➌ for 15 Value, 10 Message, 10 Time
check prop4 with  ➊,➋,➌ for 15 Value, 10 Message, 10 Time
check prop4 with exactly ➀,➋,➌ for 15 Value, 10 Message, 10 Time
check prop4 with  ➀,➋,➌ for 15 Value, 10 Message, 10 Time
check prop4 with exactly ➊,➁,➌ for 15 Value, 10 Message, 10 Time
check prop4 with  ➊,➁,➌ for 15 Value, 10 Message, 10 Time
check prop4 with exactly ➊,➋,➂ for 15 Value, 10 Message, 10 Time
check prop4 with  ➊,➋,➂ for 15 Value, 10 Message, 10 Time
check prop4 with exactly ➀,➁,➌ for 15 Value, 10 Message, 10 Time
check prop4 with  ➀,➁,➌ for 15 Value, 10 Message, 10 Time
check prop4 with exactly ➀,➋,➂ for 15 Value, 10 Message, 10 Time --  counterexample 
check prop4 with  ➀,➋,➂ for 15 Value, 10 Message, 10 Time	        --  counterexample 
check prop4 with exactly ➊,➁,➂ for 15 Value, 10 Message, 10 Time
check prop4 with  ➊,➁,➂ for 15 Value, 10 Message, 10 Time
check prop4 with exactly ➀,➁,➂ for 15 Value, 10 Message, 10 Time
check prop4 with  ➀,➁,➂ for 15 Value, 10 Message, 10 Time


check prop5_octo {							
	base_linear_safe
} for 11 Value, 10 Message, 10 Time

assert prop5 {							
	base_linear_safe
	} 
// thoses products with no counterexample are forbidden by Feature Model
check prop5  for 15 Value, 10 Message, 10 Time			--counterexample	 
check prop5 with exactly ➊,➋,➌ for 15 Value, 10 Message, 10 Time 	--counterexample
check prop5 with  ➊,➋,➌ for 15 Value, 10 Message, 10 Time		--counterexample
check prop5 with exactly ➀,➋,➌ for 15 Value, 10 Message, 10 Time
check prop5 with  ➀,➋,➌ for 15 Value, 10 Message, 10 Time
check prop5 with exactly ➊,➁,➌ for 15 Value, 10 Message, 10 Time
check prop5 with  ➊,➁,➌ for 15 Value, 10 Message, 10 Time
check prop5 with exactly ➊,➋,➂ for 15 Value, 10 Message, 10 Time
check prop5 with  ➊,➋,➂ for 15 Value, 10 Message, 10 Time
check prop5 with exactly ➀,➁,➌ for 15 Value, 10 Message, 10 Time
check prop5 with  ➀,➁,➌ for 15 Value, 10 Message, 10 Time
check prop5 with exactly ➀,➋,➂ for 15 Value, 10 Message, 10 Time	 --counterexample
check prop5 with  ➀,➋,➂ for 15 Value, 10 Message, 10 Time		 --counterexample
check prop5 with exactly ➊,➁,➂ for 15 Value, 10 Message, 10 Time	
check prop5 with  ➊,➁,➂ for 15 Value, 10 Message, 10 Time		
check prop5 with exactly ➀,➁,➂ for 15 Value, 10 Message, 10 Time
check prop5 with  ➀,➁,➂ for 15 Value, 10 Message, 10 Time


check prop6_octo{-- this property is badly expressed due to the intervals abstraction	
	limited_control_assumption implies base_linear_safe2
} for 12 Value, 10 Message, 10 Time						



assert prop6{-- this property is badly expressed due to the intervals abstraction	
	limited_control_assumption implies base_linear_safe2
	}
// thoses products with no counterexample are forbidden by Feature Model
check prop6  for 15 Value, 10 Message, 10 Time			--counterexample	 
check prop6 with exactly ➊,➋,➌ for 15 Value, 10 Message, 10 Time 	--counterexample
check prop6 with  ➊,➋,➌ for 15 Value, 10 Message, 10 Time		--counterexample
check prop6 with exactly ➀,➋,➌ for 15 Value, 10 Message, 10 Time
check prop6 with  ➀,➋,➌ for 15 Value, 10 Message, 10 Time
check prop6 with exactly ➊,➁,➌ for 15 Value, 10 Message, 10 Time
check prop6 with  ➊,➁,➌ for 15 Value, 10 Message, 10 Time
check prop6 with exactly ➊,➋,➂ for 15 Value, 10 Message, 10 Time
check prop6 with  ➊,➋,➂ for 15 Value, 10 Message, 10 Time
check prop6 with exactly ➀,➁,➌ for 15 Value, 10 Message, 10 Time
check prop6 with  ➀,➁,➌ for 15 Value, 10 Message, 10 Time
check prop6 with exactly ➀,➋,➂ for 15 Value, 10 Message, 10 Time	 --counterexample
check prop6 with  ➀,➋,➂ for 15 Value, 10 Message, 10 Time		 --counterexample
check prop6 with exactly ➊,➁,➂ for 15 Value, 10 Message, 10 Time	--counterexample
check prop6 with  ➊,➁,➂ for 15 Value, 10 Message, 10 Time		--counterexample
check prop6 with exactly ➀,➁,➂ for 15 Value, 10 Message, 10 Time
check prop6 with  ➀,➁,➂ for 15 Value, 10 Message, 10 Time	


assert  prop7{
	 limited_control_assumption and ➂➁(no Rviz)➁➂ implies actuators_safe	
	} 
check prop7  for 15 Value, 10 Message, 10 Time			--counterexample 
check prop7 with exactly ➊,➋,➌ for 15 Value, 10 Message, 10 Time 	--counterexample
check prop7 with  ➊,➋,➌ for 15 Value, 10 Message, 10 Time		--counterexample
check prop7 with exactly ➀,➋,➌ for 15 Value, 10 Message, 10 Time
check prop7 with  ➀,➋,➌ for 15 Value, 10 Message, 10 Time
check prop7 with exactly ➊,➁,➌ for 15 Value, 10 Message, 10 Time
check prop7 with  ➊,➁,➌ for 15 Value, 10 Message, 10 Time
check prop7 with exactly ➊,➋,➂ for 15 Value, 10 Message, 10 Time
check prop7 with  ➊,➋,➂ for 15 Value, 10 Message, 10 Time
check prop7 with exactly ➀,➁,➌ for 15 Value, 10 Message, 10 Time
check prop7 with  ➀,➁,➌ for 15 Value, 10 Message, 10 Time
check prop7 with exactly ➀,➋,➂ for 15 Value, 10 Message, 10 Time	--counterexample 
check prop7 with  ➀,➋,➂ for 15 Value, 10 Message, 10 Time		--counterexample 
check prop7 with exactly ➊,➁,➂ for 15 Value, 10 Message, 10 Time
check prop7 with  ➊,➁,➂ for 15 Value, 10 Message, 10 Time
check prop7 with exactly ➀,➁,➂ for 15 Value, 10 Message, 10 Time
check prop7 with  ➀,➁,➂ for 15 Value, 10 Message, 10 Time


assert  prop8{
	 danger_range_liveness
	} 
check prop8  for 15 Value, 10 Message, 10 Time			 
check prop8 with exactly ➊,➋,➌ for 15 Value, 10 Message, 10 Time 	
check prop8 with  ➊,➋,➌ for 15 Value, 10 Message, 10 Time		
check prop8 with exactly ➀,➋,➌ for 15 Value, 10 Message, 10 Time
check prop8 with  ➀,➋,➌ for 15 Value, 10 Message, 10 Time
check prop8 with exactly ➊,➁,➌ for 15 Value, 10 Message, 10 Time
check prop8 with  ➊,➁,➌ for 15 Value, 10 Message, 10 Time
check prop8 with exactly ➊,➋,➂ for 15 Value, 10 Message, 10 Time
check prop8 with  ➊,➋,➂ for 15 Value, 10 Message, 10 Time
check prop8 with exactly ➀,➁,➌ for 15 Value, 10 Message, 10 Time
check prop8 with  ➀,➁,➌ for 15 Value, 10 Message, 10 Time
check prop8 with exactly ➀,➋,➂ for 15 Value, 10 Message, 10 Time	 
check prop8 with  ➀,➋,➂ for 15 Value, 10 Message, 10 Time		 
check prop8 with exactly ➊,➁,➂ for 15 Value, 10 Message, 10 Time
check prop8 with  ➊,➁,➂ for 15 Value, 10 Message, 10 Time
check prop8 with exactly ➀,➁,➂ for 15 Value, 10 Message, 10 Time
check prop8 with  ➀,➁,➂ for 15 Value, 10 Message, 10 Time

pred testInstance {	
	some t: Time-last |  some Husky_Base.inbox.(t.nexts)
}

run testInstance  for 8 Value, 8 Message, 7 Time


