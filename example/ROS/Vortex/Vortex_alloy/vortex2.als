module vorteX
open meta

------  Values	--------
abstract sig TS extends Value {} 	-- TwistStamped
abstract sig PC extends Value {} 	-- PointCloud2
abstract sig SIMU extends Value {} 	-- Sensor_msgs/Imu
abstract sig NF extends Value {} 	-- Nav_Fix
abstract sig Img extends Value {}	-- Sensor/Image

abstract sig IndxTrack extends Value {}
abstract sig MA extends Value {} 	-- MultiArray



------ Topic List ------
---------------------for node Perception_Thrust 
one sig GPS_Vel, 			
	GPS_Fix,
	PointCloud,
	Image,
	Imu,	
------------				
	Ind_GPS_Vel,			
	Ind_GPS_Fix,		
	Ind_PointCloud,
	Ind_Image,
	Ind_Imu,
	Ind_Tracklets,	--Perception_Thrust 发布主题	
	Transf_Tracklets,	
	Transf_PointCloud,
	Compressed_PointCloud		     
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
	all m:topic.Compressed_PointCloud| m.value in MA
}


------ Node List ------
one sig Reader extends Sensor{}{
	advertises = GPS_Vel + GPS_Fix + PointCloud + Image + Imu
}
one sig Perception_Thrust extends Node {}{
	subscribes = GPS_Vel + GPS_Fix + PointCloud + Image + Imu
	advertises = Ind_Imu + Ind_GPS_Fix + Ind_GPS_Vel + Ind_PointCloud + Ind_Image + Ind_Tracklets
}

one sig Transform extends Node {}{
	subscribes = Ind_Imu + Ind_PointCloud + Ind_Tracklets
	advertises = Transf_Tracklets + Transf_PointCloud
}

one sig Compressor extends Node{}{
	subscribes = Transf_Tracklets + Transf_PointCloud
	advertises = Compressed_PointCloud
}

one sig Mem_Writter extends Actuator{}{
	subscribes = Ind_Imu + Ind_GPS_Vel + Ind_GPS_Fix + Ind_Image + Transf_Tracklets + Compressed_PointCloud
}


------ Behaviour ------
fact Perception_Thrust_Behaviour {
 
	all t: Time-first,  m1: Perception_Thrust.outbox.t & topic.Ind_Imu | some t': t.prevs|{
			(some m0: Perception_Thrust.inbox.t' & topic.Imu | m0.value = m1.value)}

	all t: Time-last, m0: Perception_Thrust.inbox.t & topic.Imu | some t': t.nexts|{
			 (some m1: Perception_Thrust.outbox.t' & topic.Ind_Imu | m0.value = m1.value)}
	

	all t: Time -first, m1: Perception_Thrust.outbox.t & topic.Ind_GPS_Vel | some t': t.prevs|{
			 (some m0: Perception_Thrust.inbox.t' & topic.GPS_Vel | m0.value = m1.value)}
	
	all t: Time-last,  m0: Perception_Thrust.inbox.t & topic.GPS_Vel | some t': t.nexts|{
			 (some m1: Perception_Thrust.outbox.t' & topic.Ind_GPS_Vel | m0.value = m1.value)}


	all t: Time-first, m1: Perception_Thrust.outbox.t & topic.Ind_GPS_Fix | some t': t.prevs|{
			 (some m0: Perception_Thrust.inbox.t' & topic.GPS_Fix | m0.value = m1.value)}
	
	all t: Time-last, m0: Perception_Thrust.inbox.t & topic.GPS_Fix | some t': t.nexts|{
			(some m1: Perception_Thrust.outbox.t' & topic.Ind_GPS_Fix | m0.value = m1.value )}
	

	all t: Time-first , m1: Perception_Thrust.outbox.t & topic.Ind_PointCloud |some t': t.prevs|{
			 (some m0: Perception_Thrust.inbox.t' & topic.PointCloud | m0.value = m1.value)}

	all t: Time-last , m0: Perception_Thrust.inbox.t & topic.PointCloud |some t': t.nexts|{
			(some m1: Perception_Thrust.outbox.t' & topic.Ind_PointCloud  | m0.value = m1.value)}


	
	all t: Time -first, m0: Perception_Thrust.outbox.t & topic.Ind_Image |some t': t.prevs|{
			(some m1: Perception_Thrust.inbox.t' & topic.Image| m0.value = m1.value)}

	all t: Time-last, m0: Perception_Thrust.inbox.t & topic.Image |some t': t.nexts {
		 (some m1: Perception_Thrust.outbox.t' & topic.Ind_Image | m0.value = m1.value)}

	all t: Time-first, m1: Perception_Thrust.outbox.t & topic.Ind_Tracklets | some t': t.prevs|{(some m1)
			implies  ( (some Perception_Thrust.inbox.t' &  topic.PointCloud  ))}
						   	  
	//节点收件箱中有 这些topic 的消息时，生成 topic为topic.Ind_Tracklets的消息
	all t: Time-last, m0: Perception_Thrust.inbox.t & (topic.GPS_Vel +  topic.GPS_Fix + topic.PointCloud + topic.Image + topic.Imu) | some t': t.nexts|{
		(some m0)
			implies (some Perception_Thrust.outbox.t' & topic.Ind_Tracklets)}
 
}


fact Transform_Behaviour{
 
	all t: Time-first,  m1:  Transform.outbox.t & topic.Transf_Tracklets |some t':t.prevs|{ 
		 (some m0: Transform.inbox.t' & topic.Ind_Tracklets | m0.value = m1.value)}
	
	all t: Time-last, m0: Transform.inbox.t & topic.Ind_Tracklets| some t': t.nexts|{
		 (some m1: Transform.outbox.t' & topic.Transf_Tracklets | m0.value = m1.value)}
	
	all t: Time-first, m1: Transform.outbox.t & topic.Transf_PointCloud | some t': t.prevs| {
		(some  m0: Transform.inbox.t' & topic.Ind_PointCloud | m0.value = m1.value)}

	all t: Time-last, m0: Transform.inbox.t & topic.Ind_PointCloud | some t': t.nexts|{
		 (some m1: Transform.outbox.t' & topic.Transf_PointCloud | m0.value = m1.value)}
 	
}

fact Compressor_Behaviour {
	all t: Time-first| some t': t.prevs{
		(some Compressor.outbox.t & topic.Compressed_PointCloud) implies (some Compressor.inbox.t' & topic.Transf_PointCloud)}
	all t: Time-last|some t': t.nexts| {
		(some Compressor.inbox.t & topic.Transf_PointCloud) implies  (some Compressor.outbox.t' & topic.Compressed_PointCloud)
	}
}




check writter_PC_safety{
	all t: Time , m1: Mem_Writter.inbox.t & topic.Compressed_PointCloud | some t': t.prevs|{
			 (some m0 : Reader.outbox.t' & topic.PointCloud| m0.value = m1.value)
	}
} for 7 Value, 10 Message, 10 Time
