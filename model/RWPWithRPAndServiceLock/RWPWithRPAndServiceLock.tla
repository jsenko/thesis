----------------------- MODULE RWPWithRPAndServiceLock -------------------------
EXTENDS Naturals
CONSTANT ReadersCount,
         WritersCount
         
Readers == 1 .. ReadersCount
Writers == (ReadersCount + 1) .. (ReadersCount + WritersCount)


mutexInstance == INSTANCE FairSemaphore WITH permitCount <- 1
wInstance == INSTANCE FairSemaphore WITH permitCount <- 1

(*
 Each process will read the shared value, or write 
 
--algorithm RWP {

  variables readCount = 0,
            mutex = {}, \* INSTANCE Semaphore WITH permitCount <- 1
            w = {} \* INSTANCE Semaphore WITH permitCount <- 1
            \* service lock
            

  process (Reader \in Readers)
    variable s;
  {   
   startR:   while(TRUE) {
               \* ACQUIRE ACCESS 
               \* service lock   
      s01:     with(x \in BOOLEAN) { s := x; }; \* s := TryWait on mutex
      s02:     if(s) { \* CS on mutex
                 \*service signal
                 \* First reader locks out writers
      s03:       if(readCount = 0) {
      s04:         with(x \in BOOLEAN) { s := x; }; \* s := TryWait on w
      s05:         if(\neg s) {
                       goto s04; \* retry
                   }    
                 };
      s06:       readCount := readCount + 1;
      s07:       skip; \* Signal on mutex
               }
               else {
      s08:       goto s01; \* retry 
               };
               
               \* DO READ
      s09:     skip;
      
               \* RELEASE ACCESS
      s10:     with(x \in BOOLEAN) { s := x; }; \* s := TryWait on mutex
      s11:     if(s) { \* CS on mutex
      s12:       readCount := readCount - 1;
                 \* Last reader unlocks writers
      s13:       if(readCount = 0) {
                   skip; \* Signal on w                       
                 };
      s14:       skip; \* Signal on mutex 
               }
               else {
                 goto s10; \* retry
               }
             }          
  }
  
  process (Writer \in Writers)
    variable s;
  {
   startW:   while(TRUE) {
               \* service lock
               \*ACQUIRE ACCESS 
      s15:     with(x \in BOOLEAN) { s := x; }; \* s := TryWait on w
      s16:     if(s) {
                 \*service signal
                 \* DO WRITE
      s17:       skip;
                 
                 \* RELEASE ACCESS
      s18:       skip; \* Signal on w
               }
               else {
                 goto s15; \* retry
               }
             }          
  }
} \* end algorithm
*)

-------------------------------------------------------------------

\* BEGIN TRANSLATION
\* Process variable s of process Reader at line 24 col 14 changed to s_
CONSTANT defaultInitValue
VARIABLES readCount, mutex, w, pc, s_, s

vars == << readCount, mutex, w, pc, s_, s >>

ProcSet == (Readers) \cup (Writers)

Init == (* Global variables *)
        /\ readCount = 0
        /\ mutexInstance!Init(mutex)
        /\ wInstance!Init(w)
        (* Process Reader *)
        /\ s_ = [self \in Readers |-> defaultInitValue]
        (* Process Writer *)
        /\ s = [self \in Writers |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> CASE self \in Readers -> "startR"
                                        [] self \in Writers -> "startW"]

startR(self) == /\ pc[self] = "startR"
                /\ pc' = [pc EXCEPT ![self] = "s01"]
                /\ UNCHANGED << readCount, mutex, w, s_, s >>

s01(self) == /\ pc[self] = "s01"
             /\ \E x \in BOOLEAN:
                  /\ s_' = [s_ EXCEPT ![self] = x]
                  /\ mutexInstance!TryWait(self, x, mutex, mutex')
             /\ pc' = [pc EXCEPT ![self] = "s02"]
             /\ UNCHANGED << readCount, w, s >>

s02(self) == /\ pc[self] = "s02"
             /\ IF s_[self]
                   THEN /\ pc' = [pc EXCEPT ![self] = "s03"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "s08"]
             /\ UNCHANGED << readCount, mutex, w, s_, s >>

s03(self) == /\ pc[self] = "s03"
             /\ IF readCount = 0
                   THEN /\ pc' = [pc EXCEPT ![self] = "s04"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "s06"]
             /\ UNCHANGED << readCount, mutex, w, s_, s >>

s04(self) == /\ pc[self] = "s04"
             /\ \E x \in BOOLEAN:
                  /\ s_' = [s_ EXCEPT ![self] = x]
                  /\ wInstance!TryWait(self, x, w, w')
             /\ pc' = [pc EXCEPT ![self] = "s05"]
             /\ UNCHANGED << readCount, mutex, s >>

s05(self) == /\ pc[self] = "s05"
             /\ IF \neg s_[self]
                   THEN /\ pc' = [pc EXCEPT ![self] = "s04"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "s06"]
             /\ UNCHANGED << readCount, mutex, w, s_, s >>

s06(self) == /\ pc[self] = "s06"
             /\ readCount' = readCount + 1
             /\ pc' = [pc EXCEPT ![self] = "s07"]
             /\ UNCHANGED << mutex, w, s_, s >>

s07(self) == /\ pc[self] = "s07"
             /\ mutexInstance!Signal(mutex, mutex')
             /\ pc' = [pc EXCEPT ![self] = "s09"]
             /\ UNCHANGED << readCount, w, s_, s >>

s08(self) == /\ pc[self] = "s08"
             /\ pc' = [pc EXCEPT ![self] = "s01"]
             /\ UNCHANGED << readCount, mutex, w, s_, s >>

s09(self) == /\ pc[self] = "s09"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "s10"]
             /\ UNCHANGED << readCount, mutex, w, s_, s >>

s10(self) == /\ pc[self] = "s10"
             /\ \E x \in BOOLEAN:
                  /\ s_' = [s_ EXCEPT ![self] = x]
                  /\ mutexInstance!TryWait(self, x, mutex, mutex')
             /\ pc' = [pc EXCEPT ![self] = "s11"]
             /\ UNCHANGED << readCount, w, s >>

s11(self) == /\ pc[self] = "s11"
             /\ IF s_[self]
                   THEN /\ pc' = [pc EXCEPT ![self] = "s12"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "s10"]
             /\ UNCHANGED << readCount, mutex, w, s_, s >>

s12(self) == /\ pc[self] = "s12"
             /\ readCount' = readCount - 1
             /\ pc' = [pc EXCEPT ![self] = "s13"]
             /\ UNCHANGED << mutex, w, s_, s >>

s13(self) == /\ pc[self] = "s13"
             /\ IF readCount = 0
                   THEN /\ wInstance!Signal(w, w')
                   ELSE /\ w' = w
             /\ pc' = [pc EXCEPT ![self] = "s14"]
             /\ UNCHANGED << readCount, mutex, s_, s >>

s14(self) == /\ pc[self] = "s14"
             /\ mutexInstance!Signal(mutex, mutex')
             /\ pc' = [pc EXCEPT ![self] = "startR"]
             /\ UNCHANGED << readCount, w, s_, s >>

Reader(self) == startR(self) \/ s01(self) \/ s02(self) \/ s03(self)
                   \/ s04(self) \/ s05(self) \/ s06(self) \/ s07(self)
                   \/ s08(self) \/ s09(self) \/ s10(self) \/ s11(self)
                   \/ s12(self) \/ s13(self) \/ s14(self)

startW(self) == /\ pc[self] = "startW"
                /\ pc' = [pc EXCEPT ![self] = "s15"]
                /\ UNCHANGED << readCount, mutex, w, s_, s >>

s15(self) == /\ pc[self] = "s15"
             /\ \E x \in BOOLEAN:
                  /\ s' = [s EXCEPT ![self] = x]
                  /\ wInstance!TryWait(self, x, w, w')
             /\ pc' = [pc EXCEPT ![self] = "s16"]
             /\ UNCHANGED << readCount, mutex, s_ >>

s16(self) == /\ pc[self] = "s16"
             /\ IF s[self]
                   THEN /\ pc' = [pc EXCEPT ![self] = "s17"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "s15"]
             /\ UNCHANGED << readCount, mutex, w, s_, s >>

s17(self) == /\ pc[self] = "s17"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "s18"]
             /\ UNCHANGED << readCount, mutex, w, s_, s >>

s18(self) == /\ pc[self] = "s18"
             /\ wInstance!Signal(w, w')
             /\ pc' = [pc EXCEPT ![self] = "startW"]
             /\ UNCHANGED << readCount, mutex, s_, s >>

Writer(self) == startW(self) \/ s15(self) \/ s16(self) \/ s17(self)
                   \/ s18(self)

Next == (\E self \in Readers: Reader(self))
           \/ (\E self \in Writers: Writer(self))
           
Fairness == /\ \A self \in Readers: WF_vars(Reader(self))
            /\ \A self \in Writers: WF_vars(Writer(self))

Spec == Init /\ [][Next]_vars /\ WF_vars(Next) /\ Fairness (* each process must be able to progress *)
(* TODO WF conjuction rule*)
\* END TRANSLATION

-------------------------------------------------------------------

ReadSection == "s09"

WriteSection == "s17"

StartLabels == {"StartR", "StartL"}

C1 == [](\A wr \in Writers: (pc[wr] = WriteSection) =>
                 /\ (\neg \E wr2 \in Writers \ { wr }: pc[wr2] = WriteSection) 
                 /\ (\neg \E r \in Readers: pc[r] = ReadSection)) 

C2 == [](\E r \in Readers: (pc[r] = ReadSection) =>
                 /\ (\neg \E wr \in Writers: pc[wr] = WriteSection))
                 
C3 == [](wInstance!CorrectnessInvariant(w) /\ mutexInstance!CorrectnessInvariant(mutex))
                  
Correctness == C1 /\ C2 /\ C3

L1 == \A wr \in Writers: []<>(pc[wr] = WriteSection)

L2 == \A r \in Readers: []<>(pc[r] = ReadSection)

Liveness == L1 /\ L2

===================================================================
