--------------------------- MODULE raftModelPerf ---------------------------

EXTENDS raftSpec

\*instrumentation and performance invariants

\* A leader's maxc should remain under MaxClientRequests
MaxCInv == (\E i \in RaftServers(switchIndex) : state[i] = Leader) => maxc <= MaxClientRequests

\* No server can become leader more than MaxBecomeLeader times
LeaderCountInv == \E i \in RaftServers(switchIndex) : (state[i] = Leader => leaderCount[i] <= MaxBecomeLeader)

\* No server can have a term exceeding MaxTerm
MaxTermInv == \A i \in RaftServers(switchIndex) : currentTerm[i] <= MaxTerm

\* Check lower bound for message counts on committed entries ----
\* For any entry that has been marked as committed, verify that either the number
\* of AppendEntries requests sent OR the number of successful acknowledgments received
\* is at least the minimum number of followers required to form a majority.
\* will fail when an entry was sent twice to a follower and no response was acked yet, which is normal
EntryCommitMessageCountInv ==
    LET NumFollowers == Cardinality(Server) - 1
        MinFollowersForMajority == Cardinality(Server) \div 2
    IN \A key \in DOMAIN entryCommitStats :
        LET stats == entryCommitStats[key]
        IN IF stats.committed
           THEN (stats.sentCount >= MinFollowersForMajority /\ stats.sentCount <= NumFollowers) 
                \/ (stats.ackCount >= MinFollowersForMajority /\ stats.ackCount <= NumFollowers)
           ELSE TRUE

\* Check that committed entries received acknowledgments from a majority of followers.
EntryCommitAckQuorumInv ==
    LET NumServers == Cardinality(Server)
        \* Minimum number of *followers* needed (in addition to the leader)
        \* to reach a majority for committing an entry.
        MinFollowerAcksForMajority == NumServers \div 2
    IN \A key \in DOMAIN entryCommitStats :
        LET stats == entryCommitStats[key]
        IN stats.committed => (stats.ackCount >= MinFollowerAcksForMajority)

\* fake inv to obtain a trace
LeaderCommitted ==
    \E i \in RaftServers(switchIndex): commitIndex[i] /= 1 \* it was 2
    
    
AllServersHaveOneUnorderedRequestInv ==

    \E s \in RaftServers(switchIndex) :  Cardinality(unorderedRequests[s]) /= 2
    


=============================================================================
\* Created by Ovidiu-Cristian Marcu
