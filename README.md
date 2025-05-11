*Changes done in TLA class: 07/04/2025*
Just forked the repo and understood the new schema of how requests will be handled now that we need to add the switch (forgot to make that first commit)


*Changes done before TLA class: 23/04/2025*
DONE
1. Read articles and papers to understand raft and hovercraft
2. Analyzed the raft tla code to understand what I need to modify for the hovercraft specification
3. Modified the code:
        - Added switch variable
        - Modified the init to also include the initialization of buffers of each server
        - removed the clientRequest and added the SwitchSendingCRequest
        - added a handler for the requests from switch
        - modified the appendEntries


*Changes done during 24/04/25 - 11/05/25*
1. Modified in the code:
        - Modified my previous code to make switch as server
        - defined myInit for hoverCraft model and mySwitchNext
        - defined SwitchClientRequest(switchIndex, i, v)
        - defined SwitchClientRequestReplicate(switchIndex, i, v)
        - modified the code like actions to also use the new variables for switch