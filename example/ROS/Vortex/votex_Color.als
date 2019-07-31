module vorteX
open meta

------  Values	--------
abstract sig TS extends Value {} 	-- TwistStamped 
abstract sig PC extends Value {} 	-- PointCloud2
abstract sig SIMU extends Value {} 	-- Sensor_msgs/Imu
abstract sig NF extends Value {} 	-- Nav_Fix
abstract sig Img extends Value {}	-- Sensor/Image

abstract sig IndxTrack extends Value {}
➀abstract sig MA extends Value {}➀ 	-- MultiArray

------ Topic List ------
one sig GPS_Vel, 			
	GPS_Fix,
	PointCloud,
	Image,
	Imu,					
	Ind_GPS_Vel,			
	Ind_GPS_Fix,		
	Ind_PointCloud,
	Ind_Image,
	Ind_Imu,
	Ind_Tracklets,		
	Transf_Tracklets,	
	Transf_PointCloud	     
extends Topic {}

➀one sig Compressed_PointCloud extends Topic{}➀

fact topic_values {
	all m:topic.GPS_Vel | m.value in TS
	all m:topic.GPS_Fix | m.value in NF
	all m:topic.PointCloud | m.value in PC
	all m:topic.Image | m.value in Img
	all m:topic.Imu | m.value in SIMU
	all m:topic.Ind_GPS_Vel | m.value in TS
	all m:topic.Ind_GPS_Fix | m.value in NF
	all m:topic.Ind_PointCloud | m.value in PC
	all m:topic.Ind_Image| m.value in Img
	all m:topic.Ind_Imu | m.value in SIMU
	all m:topic.Ind_Tracklets | m.value in IndxTrack
	all m:topic.Transf_Tracklets | m.value in IndxTrack
	all m:topic.Transf_PointCloud | m.value in PC
	➀all m:topic.Compressed_PointCloud| m.value in MA➀
	}

------ Node List ------
one sig Reader extends Sensor{}{
	advertises = GPS_Vel + GPS_Fix + PointCloud + Image + Imu
	}
one sig Perception_Thrust extends Node {}{
	subscribes = GPS_Vel      + GPS_Fix       + PointCloud      + Image      + Imu
	advertises = Ind_GPS_Vel + Ind_GPS_Fix + Ind_PointCloud + Ind_Image+ Ind_Imu + Ind_Tracklets 
	}
one sig Transform extends Node {}{
	subscribes = Ind_Imu + Ind_PointCloud + Ind_Tracklets
	advertises = Transf_Tracklets + Transf_PointCloud
	}
➀one sig Compressor extends Node{}{
	subscribes = Transf_Tracklets + Transf_PointCloud
	advertises = Compressed_PointCloud
	}➀

one sig Mem_Writter extends Actuator{}{
	subscribes = Ind_Imu + Ind_GPS_Vel + Ind_GPS_Fix + Ind_Image + Transf_Tracklets + ➊Transf_PointCloud➊+➀Compressed_PointCloud➀
	}


------ Behaviour ------
fact Perception_Thrust_Behaviour {
	all t: Time-first | all m1: Perception_Thrust.outbox.t & topic.Ind_Imu | some t': t.prevs| {
			some m0: Perception_Thrust.inbox.t' & topic.Imu | m0.value = m1.value
			}

	all t: Time-last | all m0: Perception_Thrust.inbox.t & topic.Imu | some t': t.nexts| {
			 some m1: Perception_Thrust.outbox.t' & topic.Ind_Imu | m0.value = m1.value
			}
	

	all t: Time-first | all m1: Perception_Thrust.outbox.t & topic.Ind_GPS_Vel |some t': t.prevs {
			 some m0: Perception_Thrust.inbox.t' & topic.GPS_Vel | m0.value = m1.value
			}
	
	all t: Time-last | all m0: Perception_Thrust.inbox.t & topic.GPS_Vel | some t':t.nexts{
			some m1: Perception_Thrust.outbox.t'  & topic.Ind_GPS_Vel | m0.value = m1.value
			}


	all t: Time-first | all m1: Perception_Thrust.outbox.t & topic.Ind_GPS_Fix | some t': t.prevs|{
		 	some m0: Perception_Thrust.inbox.t' & topic.GPS_Fix | m0.value = m1.value }
	
	all t: Time-last | all m0: Perception_Thrust.inbox.t & topic.GPS_Fix | some t': t.nexts|{
			 some m1: Perception_Thrust.outbox.t' & topic.Ind_GPS_Fix | m0.value = m1.value 
			}
	


	all t: Time-first | all m1: Perception_Thrust.outbox.t  & topic.Ind_PointCloud | some t': t.prevs{
			 some m0: Perception_Thrust.inbox.t' & topic.PointCloud | m0.value = m1.value
			}

	all t: Time-last | all m0: Perception_Thrust.inbox.t & topic.PointCloud |some t': t.nexts|{
		 	some m1: Perception_Thrust.outbox.t' & topic.Ind_PointCloud  | m0.value = m1.value 
			}


	
	all t: Time-first | all m0: Perception_Thrust.outbox.t & topic.Ind_Image | some t': t.prevs|{
			some m1: Perception_Thrust.inbox.t' & topic.Image| m0.value = m1.value}

	all t: Time-last | all m0: Perception_Thrust.inbox.t & topic.Image | some t': t.nexts|{
			some m1: Perception_Thrust.outbox.t' & topic.Ind_Image | m0.value = m1.value}
-------------------------------------
	--修改主题	 
	--收到PointCloud 改为 Ind_Tracklets   value 不管
	all t: Time-first |all m1: Perception_Thrust.outbox.t & topic.Ind_Tracklets |  some t': t.prevs|{
		(some m1) implies ( some Perception_Thrust.inbox.t' &  topic.PointCloud )}
						   	  

	all t: Time -last|some t': t.nexts|  all m0: Perception_Thrust.inbox.t & (topic.GPS_Vel +  topic.GPS_Fix + topic.PointCloud + topic.Image + topic.Imu) | 
		{(some m0)  implies (some Perception_Thrust.outbox.t' & topic.Ind_Tracklets)}
  
}


fact Transform_Behaviour{

	all t:Time-first |some t': t.prevs|  all m1:  Transform.outbox.t & topic.Transf_Tracklets | {
		(some m0: Transform.inbox.t' & topic.Ind_Tracklets | m0.value = m1.value)}
	
	all t:Time-last | some t': t.nexts | all m0: Transform.inbox.t & topic.Ind_Tracklets|{
		 (some m1: Transform.outbox.t' & topic.Transf_Tracklets | m0.value = m1.value)}
	

	all t:Time-first | some t': t.prevs | all m1: Transform.outbox.t & topic.Transf_PointCloud | {
		(some  m0: Transform.inbox.t' & topic.Ind_PointCloud | m0.value = m1.value)}

	all t:Time-last | some t': t.nexts |all m0: Transform.inbox.t & topic.Ind_PointCloud |{
		(some m1: Transform.outbox.t' & topic.Transf_PointCloud | m0.value = m1.value)
		}	
}

➀fact Compressor_Behaviour {
	all t: Time-first| some t': t.prevs{
		(some Compressor.outbox.t & topic.Compressed_PointCloud) implies (some Compressor.inbox.t' & topic.Transf_PointCloud)}
	all t: Time-last|some t': t.nexts| {
		(some Compressor.inbox.t & topic.Transf_PointCloud) implies  (some Compressor.outbox.t' & topic.Compressed_PointCloud)
	}
}➀

 assert writter_PC_safety{
	all t: Time-first , m1: Mem_Writter.inbox.t & ➀topic.Compressed_PointCloud ➀ &➊ topic.Transf_PointCloud ➊ | some t': t.prevs|{
			 (some m0 : Reader.outbox.t' & topic.PointCloud| m0.value = m1.value)
	}
} 
//no counterexample
check writter_PC_safety with  exactly ➊ for 7 Value, 10 Message, 15 Time 
//this should generate a counterexample
check writter_PC_safety with  exactly ➀ for 7 Value, 10 Message, 15 Time
