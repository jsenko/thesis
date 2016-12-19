----------------------- MODULE UnreliableNetwork -------------------------
CONSTANT AddressSpace,
         DataSpace

PacketSpace == [receiver: AddressSpace, sender: AddressSpace, data: DataSpace]

NetSpace == SUBSET PacketSpace

NoData == 10\*CHOOSE x: x \notin PacketSpace

\*InboxSpace == [packets: PacketsSpace (*, enabled: BOOLEAN*)] 

\* Random packet delivery? what if too many packets? random disable?

\*DefaultInbox == [packets |-> {}(*, enabled |-> TRUE*)]

\*NetSpace == [inboxes: [AddressSpace -> InboxSpace]]

\*VARIABLE net

TypeInvariant(net) == \*/\ DefaultInbox \in InboxSpace
                      /\ net \in NetSpace


-------------------------------------------------------------------

NInit(net) == /\ TypeInvariant(net)
             /\ net = {}\*.inboxes = [addr \in AddressSpace |-> DefaultInbox]
                                                   
SendPacket(packet, net, net_next) == /\ net_next = net \union {packet}
                                
ReceivePacket(receiverAddress, ret_packet, net, net_next) ==
  IF \E packet \in net: packet.receiver = receiverAddress
      THEN /\ ret_packet = CHOOSE packet \in net: packet.receiver = receiverAddress 
           /\ net_next = net \ {ret_packet}
      ELSE /\ ret_packet = NoData
           /\ net_next = net
 \* /\ net_next = net \ ret_packet ELSE net
          

Send(senderAddress, receiverAddress, data, net, net_next) ==
  \E packet \in PacketSpace: \* careful so there is only one
    /\ packet.receiver = receiverAddress 
    /\ packet.sender = senderAddress
    /\ packet.data = data
    /\ SendPacket(packet, net, net_next)        
                  
Receive(receiverAddress, ret_data, net, net_next) ==
  \E packet \in (PacketSpace \union {NoData}):
    /\ ReceivePacket(receiverAddress, packet, net, net_next)
    /\ ret_data = IF packet # NoData THEN packet.data ELSE NoData
         
Broadcast(senderAddress, data, net, net_next) == TRUE         
         
Multicast(senderAddress, receiversAddrs, data, net, net_next) == TRUE
  
-------------------------------------------------------------------

\*Correctness == []((pc[1] = "Done" /\ pc[2] = "Done") => x = 0)

===================================================================
