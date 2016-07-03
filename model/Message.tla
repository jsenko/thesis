------------------ MODULE Message ---------------------
EXTENDS Naturals
CONSTANT  AddressSpaceSize, DataSpace, noAddress, noMessage 

---------------------------------------------------------------

AddressSpace == { addr \in Nat : addr < AddressSpaceSize }
                \cup { noAddress }

broadcastAddress == 0

IsAddress(addr) == addr \in AddressSpace

MessageSpace == [from: AddressSpace, to: AddressSpace, data: DataSpace] 
                \cup { noMessage }


(* |MessageSpace| = |MessageSpace|^2 * |DataSpace| + 1 *)

IsMessage(msg) == msg \in MessageSpace 

===============================================================
