--------------------------------- MODULE raft ---------------------------------
\* This is the formal specification for the Raft consensus algorithm.
\* Modified by Ovidiu Marcu. Simplified model and performance invariants added.
\* Modified further for Hovercraft model.
\*
\* Copyright 2014 Diego Ongaro.
\* This work is licensed under the Creative Commons Attribution-4.0
\* International License https://creativecommons.org/licenses/by/4.0/

EXTENDS Naturals, FiniteSets, Sequences, TLC

\* The set of server IDs
CONSTANTS Server
ASSUME Cardinality(Server) > 0 \* Assume non-empty set for CHOOSE

\* The set of requests that can go into the log and their IDs
CONSTANTS Value, RequestId \* Assume simple types (String, Int, ModelValue)

\* Server states.
CONSTANTS Follower, Candidate, Leader

\* To identify the switch (Use a consistent ID)
CONSTANTS SwitchID

\* A reserved value.
CONSTANTS Nil

\* Message types:
CONSTANTS RequestVoteRequest, RequestVoteResponse,
          AppendEntriesRequest, AppendEntriesResponse,
          CRequestViaSwitch \* Type for broadcast messages

\* Model Checking Bounds
CONSTANTS MaxClientRequests
CONSTANTS MaxBecomeLeader
CONSTANTS MaxTerm

----
\* Global variables
VARIABLE messages
VARIABLE maxc
VARIABLE elections \* History
VARIABLE allLogs   \* History
VARIABLE leaderCount
VARIABLE pendingClientRequests \* HOVERCRAFT Buffer

----
\* Per-server variables
VARIABLE currentTerm
VARIABLE state
VARIABLE votedFor
serverVars == <<currentTerm, state, votedFor>>

\* Log entries: Sequence of [term: Nat, value: Value, requestID: RequestId]
VARIABLE log
VARIABLE commitIndex
logVars == <<log, commitIndex>>

\* Candidate state
VARIABLE votesResponded
VARIABLE votesGranted
VARIABLE voterLog \* History
candidateVars == <<votesResponded, votesGranted, voterLog>>

\* Leader state
VARIABLE nextIndex
VARIABLE matchIndex
leaderVars == <<nextIndex, matchIndex, elections>>

----
\* All variables; used for stuttering (asserting state hasn't changed).
\* INCLUDE new variable
vars == <<messages, allLogs, serverVars, candidateVars, leaderVars, logVars,
          maxc, leaderCount, pendingClientRequests>>

----
\* Helpers

Quorum == {i \in SUBSET(Server) : Cardinality(i) * 2 > Cardinality(Server)}

\* Needs to access .term field of the record
LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].term

\* Standard message helpers (unchanged)
WithMessage(m, msgs) ==
    IF m \in DOMAIN msgs THEN
        msgs
       \* [msgs EXCEPT ![m] = IF msgs[m] < 2 THEN msgs[m] + 1 ELSE 2 ]
    ELSE
        msgs @@ (m :> 1)

WithoutMessage(m, msgs) ==
    IF m \in DOMAIN msgs THEN
        [msgs EXCEPT ![m] = IF msgs[m] > 0 THEN msgs[m] - 1 ELSE 0 ]
    ELSE
        msgs

Send(m) == messages' = WithMessage(m, messages)
Discard(m) == messages' = WithoutMessage(m, messages)
Reply(response, request) ==
    messages' = WithoutMessage(request, WithMessage(response, messages))

Min(s) == CHOOSE x \in s : \A y \in s : x <= y
Max(s) == CHOOSE x \in s : \A y \in s : x >= y

\* Recursive helper for broadcasting (as provided by user)
RECURSIVE RecursiveAddToAll(_, _, _)
RecursiveAddToAll(msgs, s, msgTemplate) ==
    IF s = {} THEN
        msgs
    ELSE
        LET server == CHOOSE x \in s : TRUE
            msgToSend == [msgTemplate EXCEPT !.mdest = server]
            updatedMsgs == WithMessage(msgToSend, msgs)
            remainingServers == s \ {server}
        IN RecursiveAddToAll(updatedMsgs, remainingServers, msgTemplate)

----
\* Initialization

InitHistoryVars == /\ elections = {}
                   /\ allLogs   = {}
                   /\ voterLog  = [i \in Server |-> [j \in {} |-> <<>>]]
InitServerVars == /\ currentTerm = [i \in Server |-> 1]
                  /\ state       = [i \in Server |-> Follower]
                  /\ votedFor    = [i \in Server |-> Nil]
InitCandidateVars == /\ votesResponded = [i \in Server |-> {}]
                     /\ votesGranted   = [i \in Server |-> {}]
InitLeaderVars == /\ nextIndex  = [i \in Server |-> [j \in Server |-> 1]]
                  /\ matchIndex = [i \in Server |-> [j \in Server |-> 0]]
InitLogVars == /\ log          = [i \in Server |-> << >>]
               /\ commitIndex  = [i \in Server |-> 0]

\* ADD Initialization for the buffer
InitPendingRequests == /\ pendingClientRequests = [i \in Server |-> {}]

Init == /\ messages = [m \in {} |-> 0]
        /\ InitHistoryVars
        /\ InitServerVars
        /\ InitCandidateVars
        /\ InitLeaderVars
        /\ InitLogVars
        /\ InitPendingRequests \* INCLUDE new var init
        /\ maxc = 0
        /\ leaderCount = [i \in Server |-> 0]

----
\* State transitions

\* Restart(i) - Unchanged
Restart(i) ==
    /\ state'          = [state EXCEPT ![i] = Follower]
    /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]
    /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
    /\ voterLog'       = [voterLog EXCEPT ![i] = [j \in {} |-> <<>>]]
    /\ nextIndex'      = [nextIndex EXCEPT ![i] = [j \in Server |-> 1]]
    /\ matchIndex'     = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
    /\ commitIndex'    = [commitIndex EXCEPT ![i] = 0]
    \* Optionally clear pending requests on restart:
    \* /\ pendingClientRequests' = [pendingClientRequests EXCEPT ![i] = {}]
    /\ UNCHANGED <<messages, currentTerm, votedFor, log, elections, maxc, leaderCount, pendingClientRequests>>

\* Timeout(i) - Unchanged
Timeout(i) == /\ state[i] \in {Follower, Candidate}
              /\ currentTerm[i] < MaxTerm
              /\ state' = [state EXCEPT ![i] = Candidate]
              /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
              /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
              /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]
              /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
              /\ voterLog'       = [voterLog EXCEPT ![i] = [j \in {} |-> <<>>]]
              /\ UNCHANGED <<messages, leaderVars, logVars, maxc, leaderCount, pendingClientRequests>>

RequestVote(i, j) ==
    /\ state[i] = Candidate
    /\ j \notin votesResponded[i]
    /\ Send([mtype |-> RequestVoteRequest, mterm |-> currentTerm[i], mlastLogTerm |-> LastTerm(log[i]), mlastLogIndex |-> Len(log[i]), msource |-> i, mdest |-> j])
    \* OK: messages' determined by Send
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, maxc, leaderCount, pendingClientRequests>>

SwitchBroadcastRequest(v, rid) ==
    /\ maxc < MaxClientRequests
    /\ LET msgTmpl == [ mtype      |-> CRequestViaSwitch,
                        mvalue     |-> v,
                        mrequestID |-> rid,
                        msource    |-> SwitchID,
                        mdest      |-> Nil ]
       IN messages' = RecursiveAddToAll(messages, Server, msgTmpl)
    \* OK: messages' determined by RecursiveAddToAll/WithMessage
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, leaderCount,
                   maxc, pendingClientRequests>>

AppendEntries(i, j) ==
    /\ i /= j
    /\ state[i] = Leader
    /\ LET prevLogIndex == nextIndex[i][j] - 1
           prevLogTerm == IF prevLogIndex > 0 THEN log[i][prevLogIndex].term ELSE 0
           lastLogEntryIndex == Len(log[i])
           entryIndexToSend == nextIndex[i][j]
           lastMetadataIndex == Min({lastLogEntryIndex, entryIndexToSend})
           fullEntriesToProcess == SubSeq(log[i], entryIndexToSend, lastMetadataIndex)
           metadataEntries ==
               [idx \in DOMAIN fullEntriesToProcess |->
                   LET entry == fullEntriesToProcess[idx]
                   IN [term      |-> entry.term,
                       requestID |-> entry.requestID]
               ]
       IN Send([mtype          |-> AppendEntriesRequest,
                mterm          |-> currentTerm[i],
                mprevLogIndex  |-> prevLogIndex,
                mprevLogTerm   |-> prevLogTerm,
                mentries       |-> metadataEntries,
                mcommitIndex   |-> Min({commitIndex[i], lastMetadataIndex}),
                msource        |-> i,
                mdest          |-> j])
    \* OK: messages' determined by Send
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, maxc, leaderCount, pendingClientRequests>>

\* BecomeLeader(i) - Unchanged
BecomeLeader(i) ==
    /\ state[i] = Candidate
    /\ votesGranted[i] \in Quorum
    /\ leaderCount[i] < MaxBecomeLeader
    /\ state'      = [state EXCEPT ![i] = Leader]
    /\ nextIndex'  = [nextIndex EXCEPT ![i] = [j \in Server |-> Len(log[i]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
    /\ elections'  = elections \cup {[eterm |-> currentTerm[i], eleader |-> i, elog |-> log[i], evotes |-> votesGranted[i], evoterLog |-> voterLog[i]]}
    /\ leaderCount' = [leaderCount EXCEPT ![i] = leaderCount[i] + 1]
    /\ UNCHANGED <<messages, currentTerm, votedFor, candidateVars, logVars, maxc, pendingClientRequests>>

\* AdvanceCommitIndex(i) - Unchanged
AdvanceCommitIndex(i) ==
    /\ state[i] = Leader
    /\ LET Agree(idx) == {i} \cup {k \in Server : matchIndex[i][k] >= idx}
           agreeIndexes == {idx \in 1..Len(log[i]) : Agree(idx) \in Quorum}
           newCommitIndex ==
              IF /\ agreeIndexes /= {}
                 /\ log[i][Max(agreeIndexes)].term = currentTerm[i]
              THEN Max(agreeIndexes)
              ELSE commitIndex[i]
       IN commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex]
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, log, maxc, leaderCount, pendingClientRequests>>

----
\* Message handlers

HandleRequestVoteRequest(i, j, m) ==
    LET logOk == \/ m.mlastLogTerm > LastTerm(log[i])
                 \/ /\ m.mlastLogTerm = LastTerm(log[i]) /\ m.mlastLogIndex >= Len(log[i])
        grant == /\ m.mterm = currentTerm[i] /\ logOk /\ votedFor[i] \in {Nil, j}
    IN /\ m.mterm <= currentTerm[i]
       /\ \/ grant /\ votedFor' = [votedFor EXCEPT ![i] = j]
          \/ ~grant /\ UNCHANGED votedFor
       /\ Reply([mtype |-> RequestVoteResponse, mterm |-> currentTerm[i], mvoteGranted |-> grant, mlog |-> log[i], msource |-> i, mdest |-> j], m)
       \* OK: messages' determined by Reply
       /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, logVars, maxc, leaderCount, pendingClientRequests>>

HandleClientRequestViaSwitch(i, m) ==
    LET newRequestRecord == [requestID |-> m.mrequestID, value |-> m.mvalue]
    IN
    \* Always buffer
    /\ pendingClientRequests' = [pendingClientRequests EXCEPT ![i] =
                                    pendingClientRequests[i] \cup {newRequestRecord} ]
    \* If Leader, also try logging
    /\ IF state[i] = Leader THEN
         LET v == m.mvalue
             rid == m.mrequestID
             entryExistsInLog == \E x \in DOMAIN log[i] :
                                   log[i][x].requestID = rid /\ log[i][x].term = currentTerm[i]
             newLogEntry == [term |-> currentTerm[i], value |-> v, requestID |-> rid]
             newLog == IF entryExistsInLog THEN log[i] ELSE Append(log[i], newLogEntry)
         IN /\ log' = [log EXCEPT ![i] = newLog]
            /\ maxc' = IF entryExistsInLog THEN maxc ELSE maxc + 1
            /\ UNCHANGED <<commitIndex>>
       ELSE \* Follower/Candidate only buffer
          UNCHANGED <<logVars, maxc>>
    /\ Discard(m)
    \* <<< FIX: Remove 'messages' >>>
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, leaderCount>>

HandleRequestVoteResponse(i, j, m) ==
    /\ m.mterm = currentTerm[i]
    /\ votesResponded' = [votesResponded EXCEPT ![i] = votesResponded[i] \cup {j}]
    /\ \/ /\ m.mvoteGranted
          /\ votesGranted' = [votesGranted EXCEPT ![i] = votesGranted[i] \cup {j}]
          /\ voterLog' = [voterLog EXCEPT ![i] = voterLog[i] @@ (j :> m.mlog)]
       \/ /\ ~m.mvoteGranted
          /\ UNCHANGED <<votesGranted, voterLog>>
    /\ Discard(m)
    \* OK: messages' determined by Discard
    /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars, maxc, leaderCount, pendingClientRequests>>

HandleAppendEntriesRequest(i, j, m) ==
    LET logOk == \/ m.mprevLogIndex = 0
                 \/ /\ m.mprevLogIndex > 0
                    /\ m.mprevLogIndex <= Len(log[i])
                    /\ m.mprevLogTerm = log[i][m.mprevLogIndex].term
    IN /\ m.mterm <= currentTerm[i]
       /\ \/ /\ \* REJECT request
                \/ m.mterm < currentTerm[i]
                \/ /\ m.mterm = currentTerm[i] /\ state[i] = Follower /\ \lnot logOk
             /\ Reply([mtype |-> AppendEntriesResponse, mterm |-> currentTerm[i], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j], m)
             \* OK: messages' is determined by Reply
             /\ UNCHANGED <<serverVars, logVars, pendingClientRequests>>
          \/ \* Step down if Candidate
             /\ m.mterm = currentTerm[i] /\ state[i] = Candidate
             /\ state' = [state EXCEPT ![i] = Follower]
             \* OK: messages is UNCHANGED here because no Send/Discard/Reply is called
             /\ UNCHANGED <<currentTerm, votedFor, logVars, messages, pendingClientRequests>>
          \/ \* ACCEPT request (Hovercraft logic)
             /\ m.mterm = currentTerm[i] /\ state[i] = Follower /\ logOk
             /\ LET index == m.mprevLogIndex + 1
                    metadataEntry == IF Len(m.mentries) > 0 THEN m.mentries[1] ELSE Nil
                    requestIDToMatch == IF metadataEntry /= Nil THEN metadataEntry.requestID ELSE Nil
                    maybePending == { p \in pendingClientRequests[i] : p.requestID = requestIDToMatch }
                    payloadValue == IF metadataEntry /= Nil /\ maybePending /= {}
                                    THEN (CHOOSE p \in maybePending : TRUE).value
                                    ELSE Nil
                    entryToStore == IF metadataEntry /= Nil /\ payloadValue /= Nil THEN
                                        [term |-> metadataEntry.term, value |-> payloadValue, requestID |-> requestIDToMatch]
                                    ELSE Nil
                IN \/ \* Case 1: Match/Heartbeat
                       /\ \/ metadataEntry = Nil
                          \/ /\ entryToStore /= Nil
                             /\ Len(log[i]) >= index
                             /\ log[i][index].term = entryToStore.term
                             /\ log[i][index].requestID = entryToStore.requestID
                       /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({commitIndex[i], Min({m.mcommitIndex, m.mprevLogIndex + Len(m.mentries)})})]
                       /\ Reply([mtype |-> AppendEntriesResponse, mterm |-> currentTerm[i], msuccess |-> TRUE, mmatchIndex |-> m.mprevLogIndex + Len(m.mentries), msource |-> i, mdest |-> j], m)
                       /\ pendingClientRequests' = [pendingClientRequests EXCEPT ![i] = pendingClientRequests[i] \ maybePending ]
                       \* OK: messages' determined by Reply
                       /\ UNCHANGED <<serverVars, log>>
                   \/ \* Case 2: Conflict
                       /\ entryToStore /= Nil
                       /\ Len(log[i]) >= index
                       /\ \/ log[i][index].term /= entryToStore.term
                          \/ log[i][index].requestID /= entryToStore.requestID
                       /\ LET newLog == SubSeq(log[i], 1, index - 1) IN log' = [log EXCEPT ![i] = newLog]
                       /\ Reply([mtype |-> AppendEntriesResponse, mterm |-> currentTerm[i], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j], m)
                       \* <<< FIX: Remove 'messages' >>>
                       /\ UNCHANGED <<serverVars, commitIndex, pendingClientRequests>>
                   \/ \* Case 3: Append
                       /\ entryToStore /= Nil
                       /\ Len(log[i]) = m.mprevLogIndex
                       /\ maybePending /= {} \* Assert payload found
                       /\ log' = [log EXCEPT ![i] = Append(log[i], entryToStore)]
                       /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({commitIndex[i], Min({m.mcommitIndex, m.mprevLogIndex + Len(m.mentries)})})]
                       /\ Reply([mtype |-> AppendEntriesResponse, mterm |-> currentTerm[i], msuccess |-> TRUE, mmatchIndex |-> m.mprevLogIndex + Len(m.mentries), msource |-> i, mdest |-> j], m)
                       /\ pendingClientRequests' = [pendingClientRequests EXCEPT ![i] = pendingClientRequests[i] \ maybePending ]
                       \* <<< FIX: Remove 'messages' >>>
                       /\ UNCHANGED <<serverVars>>
       /\ UNCHANGED <<candidateVars, leaderVars, maxc, leaderCount>>

HandleAppendEntriesResponse(i, j, m) ==
    /\ m.mterm = currentTerm[i]
    /\ \/ /\ m.msuccess \* successful
          /\ nextIndex'  = [nextIndex  EXCEPT ![i][j] = IF matchIndex[i][j] > m.mmatchIndex THEN matchIndex[i][j] + 1 ELSE m.mmatchIndex + 1]
          /\ matchIndex' = [matchIndex EXCEPT ![i][j] = IF matchIndex[i][j] > m.mmatchIndex THEN matchIndex[i][j] ELSE m.mmatchIndex]
       \/ /\ \lnot m.msuccess \* not successful
          /\ nextIndex' = [nextIndex EXCEPT ![i][j] = Max({nextIndex[i][j] - 1, 1})]
          /\ UNCHANGED <<matchIndex>>
    /\ Discard(m)
    \* OK: messages' determined by Discard
    /\ UNCHANGED <<serverVars, candidateVars, logVars, elections, maxc, leaderCount, pendingClientRequests>>

UpdateTerm(i, j, m) ==
    /\ m.mterm > currentTerm[i]
    /\ m.mterm <= MaxTerm
    /\ currentTerm'    = [currentTerm EXCEPT ![i] = m.mterm]
    /\ state'          = [state       EXCEPT ![i] = Follower]
    /\ votedFor'       = [votedFor    EXCEPT ![i] = Nil]
    \* OK: messages is intentionally UNCHANGED here
    /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, maxc, leaderCount, pendingClientRequests>>

DropStaleResponse(i, j, m) ==
    /\ m.mterm < currentTerm[i]
    /\ Discard(m)
    \* OK: messages' determined by Discard
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, maxc, leaderCount, pendingClientRequests>>

Receive(m) ==
    LET i == m.mdest
        j == m.msource
    IN
    \/ /\ m.mtype \in {RequestVoteRequest, AppendEntriesRequest, RequestVoteResponse, AppendEntriesResponse}
       /\ m.mterm > currentTerm[i]
       /\ UpdateTerm(i, j, m)
    \/ /\ m.mtype = RequestVoteRequest /\ HandleRequestVoteRequest(i, j, m)
    \/ /\ m.mtype = RequestVoteResponse /\ (\/ DropStaleResponse(i, j, m) \/ HandleRequestVoteResponse(i, j, m))
    \/ /\ m.mtype = AppendEntriesRequest /\ HandleAppendEntriesRequest(i, j, m)
    \/ /\ m.mtype = AppendEntriesResponse /\ (\/ DropStaleResponse(i, j, m) \/ HandleAppendEntriesResponse(i, j, m))
    \/ /\ m.mtype = CRequestViaSwitch /\ HandleClientRequestViaSwitch(i, m)

----
\* Network state transitions (Optional)
\* DuplicateMessage(m) == /\ Send(m) /\ UNCHANGED << vars EXCEPT "messages" >>
\* DropMessage(m) == /\ Discard(m) /\ UNCHANGED << vars EXCEPT "messages" >>

----
\* Specification Definition

ValidMessage(msgs) == { m \in DOMAIN messages : messages[m] > 0 }

Next == /\ \/ \E i \in Server : Timeout(i)
\*           \/ \E i \in Server : Restart(i)
           \/ \E i,j \in Server : i /= j /\ RequestVote(i, j)
           \/ \E i \in Server : BecomeLeader(i)
           \/ \E v \in Value, rid \in RequestId : SwitchBroadcastRequest(v, rid)
           \/ \E i \in Server : AdvanceCommitIndex(i)
           \/ \E i,j \in Server : i /= j /\ AppendEntries(i, j)
           \/ \E m \in ValidMessage(messages) : Receive(m)
\*           \/ \E m \in ValidMessage(messages) : DuplicateMessage(m)
\*           \/ \E m \in ValidMessage(messages) : DropMessage(m)
        /\ allLogs' = allLogs \cup {log[i] : i \in Server}
        \* Simplified: Rely on _vars and UNCHANGED clauses for stuttering

Spec == Init /\ [][Next]_vars

----
\* Properties and Invariants

TypeInvariant ==
    /\ \A i \in Server: state[i] \in {Follower, Candidate, Leader}
    /\ \A i \in Server: currentTerm[i] \in Nat
    /\ \A i \in Server: commitIndex[i] \in Nat
    /\ \A i \in Server: pendingClientRequests[i] \subseteq [requestID: RequestId, value: Value]
    \* Add log record type check if needed

Committed(i) == IF commitIndex[i] = 0 THEN << >> ELSE SubSeq(log[i],1,commitIndex[i])

CheckIsPrefix(seq1, seq2) ==
    /\ Len(seq1) <= Len(seq2)
    /\ \A idx \in 1..Len(seq1) : seq1[idx] = seq2[idx]

LogInv == \A i, j \in Server :
              \/ CheckIsPrefix(Committed(i), Committed(j))
              \/ CheckIsPrefix(Committed(j), Committed(i))

LogMatchingInv ==
    \A i, j \in Server : i /= j =>
        \A n \in 1..Min({Len(log[i]), Len(log[j])}) :
            (log[i][n].term = log[j][n].term /\ log[i][n].requestID = log[j][n].requestID) =>
                SubSeq(log[i],1,n) = SubSeq(log[j],1,n)

\* LeaderCompletenessInv (Review might be needed depending on proof approach)
\* CommittedTermPrefix(i, x) == ...
\* LeaderCompletenessInv == ...

MaxCInv == (\E i \in Server : state[i] = Leader) => maxc <= MaxClientRequests
LeaderCountInv == \A i \in Server : leaderCount[i] <= MaxBecomeLeader
MaxTermInv == \A i \in Server : currentTerm[i] <= MaxTerm

LeaderCommitted == \E i \in Server : commitIndex[i] /= 1

THEOREM Spec => [](TypeInvariant /\ LogInv /\ LogMatchingInv /\ MaxCInv /\ LeaderCountInv /\ MaxTermInv)

\* Optional constraints for model checking
MyConstraint == (\A i \in Server: currentTerm[i] <= 2 /\ Len(log[i]) <= 2 ) /\ (\A m \in DOMAIN messages: messages[m] <= 1) /\ LeaderCountInv

\* Symmetry == Permutations(Server)

=============================================================================