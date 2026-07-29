------------------------- MODULE BridgeCompletion -------------------------
(***************************************************************************)
(* Formal TLA+ model of the dYdX v4 x/bridge completion path, hunting for   *)
(* PERMANENT FREEZING / LOSS of bridged-in funds (finding F5).              *)
(*                                                                          *)
(* Ground truth:                                                            *)
(*  protocol/x/bridge/keeper/acknowledge_bridges.go AcknowledgeBridges:     *)
(*    - for each recognized bridge event, schedules a delayed               *)
(*      MsgCompleteBridge `DelayBlocks` in the future via x/delaymsg, AND    *)
(*    - advances AcknowledgedEventInfo.NextId past the event (so it is       *)
(*      NEVER re-acknowledged / re-scheduled).                              *)
(*  protocol/x/bridge/keeper/complete_bridge.go CompleteBridge:             *)
(*    - returns ErrBridgingDisabled if safetyParams.IsDisabled (no coins     *)
(*      transferred).                                                       *)
(*  protocol/x/delaymsg/keeper/dispatch.go DispatchMessagesForBlock:        *)
(*    - executes each scheduled message in a CACHED context (state is        *)
(*      rolled back if the handler errors; the error is only LOGGED), then   *)
(*    - UNCONDITIONALLY DELETES every message scheduled for the block        *)
(*      (no retry, no re-queue).                                            *)
(*                                                                          *)
(* Consequence: if bridging is disabled during the delay window, the        *)
(* delayed MsgCompleteBridge fires, errors, rolls back (no funds sent), and  *)
(* is deleted forever. Since the event was already acknowledged, it is       *)
(* never retried => the user's already-locked (burned on L1) funds are       *)
(* permanently frozen.                                                      *)
(***************************************************************************)
EXTENDS Naturals, TLC

CONSTANTS
    Delay,          \* safetyParams.DelayBlocks between acknowledge and complete
    AllowDisable    \* whether bridging can be disabled during the window (governance)

VARIABLES
    phase,      \* "none" -> "acked" -> "completed" | "dropped"
    delay,      \* blocks remaining until the delayed MsgCompleteBridge fires
    disabled,   \* safetyParams.IsDisabled
    delivered   \* TRUE iff the bridged funds actually reached the user

vars == <<phase, delay, disabled, delivered>>

TypeOK ==
    /\ phase \in {"none", "acked", "completed", "dropped"}
    /\ delay \in 0..Delay
    /\ disabled \in BOOLEAN
    /\ delivered \in BOOLEAN

Init ==
    /\ phase = "none"
    /\ delay = 0
    /\ disabled = FALSE
    /\ delivered = FALSE

(* Recognize + AcknowledgeBridges: only when bridging is enabled; schedules   *)
(* the delayed completion and advances AcknowledgedEventInfo past the event.  *)
Acknowledge ==
    /\ phase = "none"
    /\ ~disabled
    /\ phase' = "acked"
    /\ delay' = Delay
    /\ UNCHANGED <<disabled, delivered>>

(* EndBlock advances one block toward the scheduled completion. *)
Tick ==
    /\ phase = "acked"
    /\ delay > 0
    /\ delay' = delay - 1
    /\ UNCHANGED <<phase, disabled, delivered>>

(* Governance disables / re-enables bridging (MsgUpdateSafetyParams). *)
Disable ==
    /\ AllowDisable
    /\ ~disabled
    /\ disabled' = TRUE
    /\ UNCHANGED <<phase, delay, delivered>>

Enable ==
    /\ AllowDisable
    /\ disabled
    /\ disabled' = FALSE
    /\ UNCHANGED <<phase, delay, delivered>>

(* The delayed MsgCompleteBridge fires. If bridging is disabled at this exact  *)
(* block, CompleteBridge errors, the cached state is rolled back (no funds),   *)
(* and delaymsg deletes the message regardless => permanently dropped.         *)
Fire ==
    /\ phase = "acked"
    /\ delay = 0
    /\ IF disabled
       THEN /\ phase' = "dropped"
            /\ UNCHANGED delivered
       ELSE /\ phase' = "completed"
            /\ delivered' = TRUE
    /\ UNCHANGED <<delay, disabled>>

Next == Acknowledge \/ Tick \/ Disable \/ Enable \/ Fire

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Tick)
    /\ WF_vars(Fire)

------------------------------------------------------------------------------
(*                              PROPERTIES                                   *)

(* SAFETY: an acknowledged bridge is never permanently dropped. HOLDS when    *)
(* bridging is never disabled (baseline); FAILS when bridging can be disabled *)
(* in the delay window => F5 permanent loss of bridged-in funds.              *)
NeverDropped == phase # "dropped"

(* LIVENESS: once acknowledged, the funds are eventually delivered.           *)
EventuallyDelivered == (phase = "acked") ~> delivered

=============================================================================
