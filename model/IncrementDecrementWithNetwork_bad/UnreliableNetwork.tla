----------------------- MODULE UnreliableNetwork -------------------------
\*EXTENDS
CONSTANT AddressSpace, \* Enabled addresses
         DataSpace

PacketSpace == [receiver: AddressSpace, sender: AddressSpace, data: DataSpace]

PacketsSpace == SUBSET PacketSpace

NoData == CHOOSE x : x \notin PacketSpace

InboxSpace == [packets: PacketsSpace (*, enabled: BOOLEAN*)] 

\* Random packet delivery? what if too many packets? random disable?

DefaultInbox == [packets |-> {}(*, enabled |-> TRUE*)]

NetSpace == [inboxes: [AddressSpace -> InboxSpace]]

\*VARIABLE net

TypeInvariant(net) == /\ DefaultInbox \in InboxSpace
                      /\ net \in NetSpace


-------------------------------------------------------------------

NInit(net) == /\ TypeInvariant(net)
             /\ net.inboxes = [addr \in AddressSpace |-> DefaultInbox]
                                                   
Send(packet, net, net_next) == /\ net_next.inboxes = [net.inboxes EXCEPT ![packet.receiver] = net.inboxes[packet.receiver] \union packet]
                                
Receive(receiverAddress, ret_packet, net, net_next) ==
  /\ ret_packet = IF net.inboxes[receiverAddress] # {} 
    THEN CHOOSE packet \in net.inboxes[receiverAddress]: packet
    ELSE NoData
  /\ net_next.inboxes = IF net.inboxes[receiverAddress] # {} 
    THEN [net.inboxes EXCEPT ![receiverAddress] = net.inboxes[receiverAddress] \ ret_packet]
    ELSE net.inboxes 

-------------------------------------------------------------------

\*Correctness == []((pc[1] = "Done" /\ pc[2] = "Done") => x = 0)

===================================================================
