module vorteX
open meta

------  Values	--------
abstract sig TS extends Value {} 	-- TwistStamped 旋转戳？？什么东东？
abstract sig PC extends Value {} 	-- PointCloud2
abstract sig SIMU extends Value {} 	-- Sensor_msgs/Imu
abstract sig NF extends Value {} 	-- Nav_Fix
abstract sig Img extends Value {}	-- Sensor/Image

abstract sig IndxTrack extends Value {}

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
}


------ Node List ------
one sig Reader extends Sensor{}{
	advertises = GPS_Vel + GPS_Fix + PointCloud + Image + Imu
}
one sig Perception_Thrust extends Node {}{
	//广播 比接收的多一类topic，追踪系统
	subscribes = GPS_Vel      + GPS_Fix       + PointCloud      + Image      + Imu
	advertises = Ind_GPS_Vel + Ind_GPS_Fix + Ind_PointCloud + Ind_Image+ Ind_Imu + Ind_Tracklets 
}

one sig Transform extends Node {}{
	//只接受 3个 不收GPS2 和图像1
	subscribes = Ind_Imu + Ind_PointCloud + Ind_Tracklets
	advertises = Transf_Tracklets + Transf_PointCloud
}
//所以  Ind_Imu 消息 可以不被转化，直接从第二个节点过来，也可以经第三个节点转化后接受
one sig Mem_Writter extends Actuator{}{
	subscribes = Ind_Imu + Ind_GPS_Vel + Ind_GPS_Fix + Ind_Image + Transf_Tracklets + Transf_PointCloud
}


------ Behaviour ------

--所有消息都经此节点
fact Perception_Thrust_Behaviour {
   --message value 不变
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


check writter_PC_safety{
	all t:Time-first,  m1: Mem_Writter.inbox.t & topic.Transf_PointCloud | some t': t.prevs {
			 some m0 : Reader.outbox.t' & topic.PointCloud |  m0.value = m1.value
	}
} for 6 Value, 10 Message, 10 Time
