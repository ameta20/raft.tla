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