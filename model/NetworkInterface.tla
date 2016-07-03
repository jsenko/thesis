------------------ MODULE NetworkInterface ---------------------
EXTENDS Naturals, FiniteSets, Message
(*CONSTANT NetworkCapacity*)
VARIABLES n
---------------------------------------------------------------

NetworkInterfaceSpace == [address: MessageSpace, receivedMessage: MessageSpace]

IsNetworkInterface(ni) == ni \in NetworkInterfaceSpace

---------------------------------------------------------------

InitNI(ni) == IsNetworkInterface(ni) /\ ni.address = noAddress

(*Send(net, msg) == ( /\ IsNetwork(net)
                    /\ net.messages' = net.messages \cup { msg }
                    /\ IsNetwork(net')
                  ) \/ UNCHANGED net (* throw away the message if no capacity available *)
*)
(* Receive(net, msg) ==*) 

===============================================================
