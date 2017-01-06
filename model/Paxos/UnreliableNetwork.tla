----------------------- MODULE UnreliableNetwork -------------------------
CONSTANT AddressSpace,
         DataSpace,
         None,
         maxNetSize

NonePacketSpace == [data: [foo: {"None"}]]

NonePacket == CHOOSE x \in NonePacketSpace: TRUE

PacketSpace == [receiver: AddressSpace, sender: AddressSpace, data: DataSpace] \union NonePacketSpace

\* NetSpace == SUBSET PacketSpace

TypeInvariant(net) == TRUE \* /\ net \in NetSpace

-------------------------------------------------------------------

Init(net) == /\ TypeInvariant(net)
             /\ net = {}
                                                   
SendPacket(packet, net, net_next) == /\ net_next = net \union { packet }
                                
ReceivePacket(receiverAddress, ret_packet, net, net_next) ==
  IF \E packet \in net: packet.receiver = receiverAddress
      THEN /\ ret_packet = CHOOSE packet \in net: packet.receiver = receiverAddress 
           /\ net_next = net \ { ret_packet }
      ELSE /\ ret_packet = NonePacket
           /\ net_next = net



       

Send(senderAddress, receiverAddress, data, net, net_next) ==
  \E packet \in PacketSpace: \* careful so there is only one
    /\ packet.receiver = receiverAddress 
    /\ packet.sender = senderAddress
    /\ packet.data = data
    /\ SendPacket(packet, net, net_next)        
(*                  
Receive(receiverAddress, ret_data, net, net_next) ==
  \E packet \in (PacketSpace \union {NoData}):
    /\ ReceivePacket(receiverAddress, packet, net, net_next)
    /\ ret_data = IF packet # NoData THEN packet.data ELSE NoData
*)
      
Broadcast(senderAddress, data, net, net_next) == 
  \A addr \in (AddressSpace \ {senderAddress}):
    Send(senderAddress, addr, data, net, net_next)
(*         
Multicast(senderAddress, receiversAddrs, data, net, net_next) == TRUE
*)

-------------------------------------------------------------------

\*Correctness == []((pc[1] = "Done" /\ pc[2] = "Done") => x = 0)

===================================================================
