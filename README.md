
*Changes done before TLA class of 23/04/2025*
DONE
1. Read articles and papers to understand raft and hovercraft
2. Analyzed the raft tla code to understand what I need to modify for the hovercraft specification
3. Modified the code:
        - Added switch variable
        - Modified the init to also include the initialization of buffers of each server
        - removed the clientRequest and added the SwitchSendingCRequest
        - added a handler for the requests from switch
        - modified the appendEntries