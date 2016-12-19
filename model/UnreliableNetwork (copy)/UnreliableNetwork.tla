----------------------- MODULE UnreliableNetwork -------------------------
\*EXTENDS
CONSTANT AddressSpace, \* Enabled addresses
         DataSpace

NoData == CHOOSE x : x \notin DataSpace

PacketSpace == [receiver: AddressSpace, sender: AddressSpace, data: DataSpace]

InboxSpace == [packets: {PacketSpace}, enabled: BOOLEAN] 
\* Random packet delivery? what if too many packets? random disable?

DefaultInbox == [packets: {}, enabled: TRUE]

NetSpace == [inboxes: [AddressSpace -> InboxSpace]]

\*VARIABLE net

TypeInvariant(net) == /\ DefaultInbox \in InboxSpace
                      /\ net \in NetSpace

(*

*)

-------------------------------------------------------------------

Init(net) == /\ TypeInvariant(net)
             /\ net.inboxes = [addr \in AddressSpace |-> DefaultInbox]

CreatePacket(ret_packet, receiver, sender, data) == /\ ret_packet.receiver = receiver
                                                    /\ ret_packet.receiver = receiver
                                                    

Send(packet, net, net_next) == /\ net_next.inboxes = [net.inboxes EXCEPT ![packet.receiver] = net.inboxes[packet.receiver] \union packet]
                                
Receive(receiver, ret_packet, net, net_next) == /\ ret_packet = CHOOSE packet \in net.inboxes[receiver]: packet
                                                /\ net_next.inboxes = [net.inboxes EXCEPT ![receiver] =  net.inboxes[receiver] \ ret_packet]

-------------------------------------------------------------------

\*Correctness == []((pc[1] = "Done" /\ pc[2] = "Done") => x = 0)

===================================================================
