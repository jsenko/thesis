------------------ MODULE Network ---------------------
EXTENDS Naturals, FiniteSets, Message, NetworkInterface

CONSTANTS NetworkCapacity (* # of messages *),
          NetworkSize (* # of nodes (interfaces) *)

VARIABLES network
---------------------------------------------------------------

NetworkSpace == [interfaces: NetworkInterfaceSpace, messages: MessageSpace]

Capacity(net) == Cardinality(net)

IsNetwork(net) == net \in NetworkSpace /\ Capacity(net) <= NetworkCapacity

---------------------------------------------------------------

Init == IsNetwork(network) /\ Capacity(network) = 0

RegisterNetworkInterface(interface) == network.interfaces'
                                         = network.interfaces \cup { interface }

===============================================================
