----------------------------- MODULE SimplePPKS_attacker -----------------------------
EXTENDS Naturals, Reals
CONSTANTS
        BOp, EOp, Exper,
        Broker, Endpoint, Controller,
        EOpIntention, ExperIntention,
        BOpAllowedEOp, BOpAllowedExper, EOpAllowedExper, EOpAllowedExp,
        BOpOwnedBroker, EOpOwnedEndpoint, ExperOwnedController,
        Channel, Exp, SNI, empty_msg, null_info,
        Attacker, MaxAttackerSeqRange, MaxAttackerTransitionCnt

Everyone ==
    BOp \cup EOp \cup Exper \cup
    Broker \cup Endpoint \cup Controller \cup Attacker

ASSUME
    /\ BOpAllowedEOp \subseteq (BOp \X EOp \X Broker)
    /\ BOpAllowedExper \subseteq (BOp \X Exper)
    /\ BOpOwnedBroker \subseteq (BOp \X Broker)
    /\ EOpIntention \subseteq (EOp \X SUBSET (BOp \X Channel))
    /\ EOpAllowedExper \subseteq (EOp \X Exper)
    /\ EOpAllowedExp \subseteq (EOp \X Exp)
    /\ EOpOwnedEndpoint \subseteq (EOp \X Endpoint)
    /\ ExperIntention \subseteq (Exper \X SUBSET (EOp \X Exp))
    /\ ExperOwnedController \subseteq (Exper \X Controller)
    /\ MaxAttackerSeqRange \in Nat
    /\ MaxAttackerTransitionCnt \in Nat

-----------------------------------------------------------------------------
(***************************************************************************)
(*                     Principal interaction messages                      *)
(***************************************************************************)
RequestSubPrivilegeMsgs(seqType) ==
  [type: {"req_sub_priv"}, seq: seqType, sender: Everyone, receiver: Everyone, channel: Channel]
      \cup
  [type: {"rsp_sub_priv"}, seq: seqType, sender: Everyone, receiver: Everyone, broker: Everyone]
      \cup
  [type: {"rsp_sub_priv_f"}, seq: seqType, sender: Everyone, receiver: Everyone]

RequestPubPrivilegeMsgs(seqType) ==
  [type: {"req_pub_priv"}, seq: seqType, sender: Everyone, receiver: Everyone, broker: Everyone]
      \cup
  [type: {"rsp_pub_priv"}, seq: seqType, sender: Everyone, receiver: Everyone]
      \cup
  [type: {"rsp_pub_priv_f"}, seq: seqType, sender: Everyone, receiver: Everyone]

RequestExpPrivilegeMsgs(seqType) ==
  [type: {"req_exp_priv"}, seq: seqType, sender: Everyone, receiver: Everyone, exp: Exp]
      \cup
  [type: {"rsp_exp_priv"}, seq: seqType, sender: Everyone, receiver: Everyone,
   broker_owner: Everyone, broker: Everyone, channel: Channel, exp_priv: Exp]
      \cup
  [type: {"rsp_exp_priv_f"}, seq: seqType, sender: Everyone, receiver: Everyone]

(***************************************************************************)
(*                       Agent interaction messages                        *)
(***************************************************************************)
RequestSubMsgs(seqType) ==
  [type: {"cmd_sub"}, seq: seqType, sender: Everyone, receiver: Everyone,
   broker: Everyone, channel: Channel]
      \cup
  [type: {"ack_cmd_sub"}, seq: seqType, sender: Everyone, receiver: Everyone]
      \cup
  [type: {"nack_cmd_sub"}, seq: seqType, sender: Everyone, receiver: Everyone]
      \cup
  [type: {"req_sub"}, seq: seqType, sender: Everyone, receiver: Everyone,
   owner: Everyone, channel: Channel]
      \cup
  [type: {"rsp_sub"}, seq: seqType, sender: Everyone, receiver: Everyone]
      \cup
  [type: {"rsp_sub_f"}, seq: seqType, sender: Everyone, receiver: Everyone]
      \cup
  [type: {"auth_sub_req"}, seq: seqType, sender: Everyone, receiver: Everyone,
   origin: Everyone, owner: Everyone, channel: Channel]
      \cup
  [type: {"ack_auth_sub_req"}, seq: seqType, sender: Everyone, receiver: Everyone]
      \cup
  [type: {"nack_auth_sub_req"}, seq: seqType, sender: Everyone, receiver: Everyone]
      \cup
  [type: {"req_auth_sub_agent"}, seq: seqType, sender: Everyone, receiver: Everyone,
   origin: Everyone, target: Everyone, channel: Channel]
      \cup
  [type: {"rsp_auth_sub_agent"}, seq: seqType, sender: Everyone, receiver: Everyone]
      \cup
  [type: {"rsp_auth_sub_agent_f"}, seq: seqType, sender: Everyone, receiver: Everyone]

RequestPubMsgs(seqType) ==
  [type: {"cmd_pub"}, seq: seqType, sender: Everyone, receiver: Everyone,
   exp: Exp, broker: Everyone, channel: Channel, sni: SNI]
      \cup
  [type: {"ack_cmd_pub"}, seq: seqType, sender: Everyone, receiver: Everyone]
      \cup
  [type: {"nack_cmd_sub"}, seq: seqType, sender: Everyone, receiver: Everyone]
      \cup
  [type: {"req_pub"}, seq: seqType, sender: Everyone, receiver: Everyone,
   owner: Everyone, exp: Exp, channel: Channel, sni: SNI]
      \cup
  [type: {"rsp_pub"}, seq: seqType, sender: Everyone, receiver: Everyone]
      \cup
  [type: {"rsp_pub_f"}, seq: seqType, sender: Everyone, receiver: Everyone]
      \cup
  [type: {"auth_pub_req"}, seq: seqType, sender: Everyone, receiver: Everyone,
   origin: Everyone, owner: Everyone, exp: Exp, channel: Channel, sni: SNI]
      \cup
  [type: {"ack_auth_pub_req"}, seq: seqType, sender: Everyone, receiver: Everyone]
      \cup
  [type: {"nack_auth_pub_req"}, seq: seqType, sender: Everyone, receiver: Everyone]
      \cup
  [type: {"req_auth_pub_agent"}, seq: seqType, sender: Everyone, receiver: Everyone,
   origin: Everyone, target: Everyone, channel: Channel, exp: Exp, sni: SNI]
      \cup
  [type: {"rsp_auth_pub_agent"}, seq: seqType, sender: Everyone, receiver: Everyone]
      \cup
  [type: {"rsp_auth_pub_agent_f"}, seq: seqType, sender: Everyone, receiver: Everyone]

NotifyAndRunExpMsgs(seqType) ==
  [type: {"notify_exp"}, seq: seqType, sender: Everyone, receiver: Everyone,
   target: Everyone, exp: Exp, channel: Channel, sni: SNI]
      \cup
  [type: {"auth_notify"}, seq: seqType, sender: Everyone, receiver: Everyone,
   notifier: Everyone, channel: Channel]
      \cup
  [type: {"ack_auth_notify"}, seq: seqType, sender: Everyone, receiver: Everyone]
      \cup
  [type: {"nack_auth_notify"}, seq: seqType, sender: Everyone, receiver: Everyone]
      \cup
  [type: {"connect"}, seq: seqType, sender: Everyone, receiver: Everyone, sni: SNI] \* for mimicing endpoint connection to controller
      \cup
  [type: {"conn_accepted"}, seq: seqType, sender: Everyone, receiver: Everyone]
      \cup
  [type: {"conn_refused"}, seq: seqType, sender: Everyone, receiver: Everyone]
      \cup
  [type: {"auth_sni"}, seq: seqType, sender: Everyone, receiver: Everyone, sni: SNI]
      \cup
  [type: {"ack_sni"}, seq: seqType, sender: Everyone, receiver: Everyone]
      \cup
  [type: {"nack_sni"}, seq: seqType, sender: Everyone, receiver: Everyone]
      \cup
  [type: {"req_run_exp"}, seq: seqType, sender: Everyone, receiver: Everyone,
   owner: Everyone]
      \cup
  [type: {"rsp_run_exp"}, seq: seqType, sender: Everyone, receiver: Everyone]
      \cup
  [type: {"rsp_run_exp_f"}, seq: seqType, sender: Everyone, receiver: Everyone]
      \cup
  [type: {"auth_exp"}, seq: seqType, sender: Everyone, receiver: Everyone,
   origin: Everyone, owner: Everyone, exp: Exp, notifier: Everyone, channel: Channel]
      \cup
  [type: {"ack_auth_exp"}, seq: seqType, sender: Everyone, receiver: Everyone, exp_priv: Exp]
      \cup
  [type: {"nack_auth_exp"}, seq: seqType, sender: Everyone, receiver: Everyone]
      \cup
  [type: {"req_auth_exp_agent"}, seq: seqType, sender: Everyone, receiver: Everyone,
   origin: Everyone, exp: Exp, notifier: Everyone, channel: Channel]
      \cup
  [type: {"rsp_auth_exp_agent"}, seq: seqType, sender: Everyone, receiver: Everyone]
      \cup
  [type: {"rsp_auth_exp_agent_f"}, seq: seqType, sender: Everyone, receiver: Everyone]
      \cup
  [type: {"req_help_exp"}, seq: seqType, sender: Everyone, receiver: Everyone,
   owner: Everyone]
      \cup
  [type: {"rsp_help_exp"}, seq: seqType, sender: Everyone, receiver: Everyone]
      \cup
  [type: {"rsp_help_exp_f"}, seq: seqType, sender: Everyone, receiver: Everyone]
      \cup
  [type: {"auth_help"}, seq: seqType, sender: Everyone, receiver: Everyone,
   owner: Everyone, origin: Everyone]
      \cup
  [type: {"ack_auth_help"}, seq: seqType, sender: Everyone, receiver: Everyone, exp: Exp]
      \cup
  [type: {"nack_auth_help"}, seq: seqType, sender: Everyone, receiver: Everyone]
      \cup
  [type: {"req_auth_help_agent"}, seq: seqType, sender: Everyone, receiver: Everyone,
   helper: Everyone]
      \cup
  [type: {"rsp_auth_help_agent"}, seq: seqType, sender: Everyone, receiver: Everyone]
      \cup
  [type: {"rsp_auth_help_agent_f"}, seq: seqType, sender: Everyone, receiver: Everyone]
      \cup
  [type: {"exec_exp"}, seq: seqType, sender: Everyone, receiver: Everyone, exp: Exp]

Messages ==
  RequestSubPrivilegeMsgs(Nat)
      \cup
  RequestPubPrivilegeMsgs(Nat)
      \cup
  RequestExpPrivilegeMsgs(Nat)
      \cup
  RequestSubMsgs(Nat)
      \cup
  RequestPubMsgs(Nat)
      \cup
  NotifyAndRunExpMsgs(Nat)

subsetNat == 0 .. MaxAttackerSeqRange

AttackerMessages ==
  RequestSubPrivilegeMsgs(subsetNat)
      \cup
  RequestPubPrivilegeMsgs(subsetNat)
      \cup
  RequestExpPrivilegeMsgs(subsetNat)
      \cup
  RequestSubMsgs(subsetNat)
      \cup
  RequestPubMsgs(subsetNat)
      \cup
  NotifyAndRunExpMsgs(subsetNat)

ASSUME AttackerMessages \subseteq Messages
-----------------------------------------------------------------------------
(***************************************************************************)
(*                       Entity state specification                        *)
(***************************************************************************)
VARIABLES
        BOpState,
        EOpState,
        ExperState,
        BrokerState,
        EndpointState,
        ControllerState,
        msgs,
        AttackerTransitionCnt
vars == <<BOpState,
          EOpState,
          ExperState,
          BrokerState,
          EndpointState,
          ControllerState,
          msgs,
          AttackerTransitionCnt>>

TrackSeqSet == SUBSET (Everyone \X SUBSET (Nat))

TypeOK ==
  (*************************************************************************)
  (* The type-correctness invariant.                                       *)
  (*************************************************************************)
  \* Principal types
  /\ BOpState \in [BOp -> [state: {"Idle", "AwaitAuthAgentPub", "AwaitAuthAgentSub"},
                           received_msg: Messages \cup {empty_msg},
                           sent_msg: Messages \cup {empty_msg},
                           sub_priv: SUBSET (Everyone \X Channel \X Everyone),
                           pub_priv: SUBSET (Everyone \X Everyone),
                           counter: Nat, track: TrackSeqSet]]
  /\ EOpState \in [EOp -> [state: {"Idle", "AwaitSubPrivilege", "AwaitSub", "AwaitAuthAgentExp"},
                           received_msg: Messages \cup {empty_msg},
                           sent_msg: Messages \cup {empty_msg},
                           sub_priv: SUBSET (Everyone \X Channel \X Everyone),
                           exp_priv: SUBSET (Everyone \X Channel \X Everyone \X Exp),
                           sub_cmd: SUBSET (Everyone \X Channel \X Everyone),
                           unused_sub_priv: SUBSET (Everyone \X Channel \X Everyone),
                           sub_targets: SUBSET (Everyone \X Channel),
                           counter: Nat, track: TrackSeqSet]]
  /\ ExperState \in [Exper -> [state: {"Idle", "AwaitPubPrivilege", "AwaitExpPrivilege", "AwaitPub", "AwaitAuthAgentHelp"},
                               received_msg: Messages \cup {empty_msg},
                               sent_msg: Messages \cup {empty_msg},
                               pub_priv: SUBSET (Everyone \X Everyone),
                               exp_priv: SUBSET (Everyone \X Channel \X Everyone \X Exp \X Exp),
                               pub_cmd: SUBSET (Everyone \X Exp \X Channel \X Everyone \X SNI),
                               unused_pub_priv: SUBSET (Everyone \X Everyone),
                               unused_exp_priv: SUBSET (Everyone \X Channel \X Everyone \X Exp \X Exp),
                               run_targets: SUBSET (Everyone \X Exp),
                               counter: Nat, track: TrackSeqSet]]
  \* Agent types
  /\ BrokerState \in [Broker -> [state: {"Idle", "AwaitSubAuth", "AwaitPubAuth"},
                                 received_msg: Messages \cup {empty_msg},
                                 sent_msg: Messages \cup {empty_msg},
                                 sub_info: SUBSET (Everyone \X Channel),
                                 pub_info: SUBSET (Everyone \X Exp \X Channel \X SNI),
                                 notified: SUBSET (Everyone \X Everyone \X Exp \X Channel \X SNI),
                                 counter: Nat, track: TrackSeqSet]]
  /\ EndpointState \in [Endpoint -> [state: {"Idle", "AwaitSub", "AwaitNotifyAuth", "AwaitConn", "AwaitRunExp", "AwaitExpAuth", "AwaitHelpExp", "AwaitExp"},
                                     received_msg: Messages \cup {empty_msg},
                                     sent_msg: Messages \cup {empty_msg},
                                     run_info: (Everyone \X Exp) \cup {null_info},
                                     executed_exp: SUBSET (Everyone \X Exp),
                                     counter: Nat, track: TrackSeqSet]]
  /\ ControllerState \in [Controller -> [state: {"Idle", "AwaitPub", "AwaitSNIAuth", "AwaitRunExp", "AwaitHelpExp", "AwaitHelpAuth"},
                                         received_msg: Messages \cup {empty_msg},
                                         sent_msg: Messages \cup {empty_msg},
                                         counter: Nat, track: TrackSeqSet]]
  \* Others
  /\ msgs \subseteq Messages
  \* bounded checking
  /\ AttackerTransitionCnt \in [Attacker -> Nat]

TrackSeqSetInit ==
    {<<bo, {}>>: bo \in BOp} \cup
    {<<eo, {}>>: eo \in EOp} \cup
    {<<ep, {}>>: ep \in Exper} \cup
    {<<b, {}>>: b \in Broker} \cup
    {<<e, {}>>: e \in Endpoint} \cup
    {<<c, {}>>: c \in Controller} \cup
    {<<a, {}>>: a \in Attacker}

Init ==
  (*************************************************************************)
  (* The initial states.                                                   *)
  (*************************************************************************)
  /\ BOpState = [bo \in BOp |-> [state |-> "Idle",
                                 received_msg |-> empty_msg,
                                 sent_msg |-> empty_msg,
                                 sub_priv |-> {},
                                 pub_priv |-> {},
                                 counter |-> 0,
                                 track |-> TrackSeqSetInit]]
  /\ EOpState = [eo \in EOp |-> [state |-> "Idle",
                                 received_msg |-> empty_msg,
                                 sent_msg |-> empty_msg,
                                 sub_priv |-> {},
                                 exp_priv |-> {},
                                 sub_cmd |-> {},
                                 unused_sub_priv |-> {},
                                 sub_targets |-> (CHOOSE tup \in EOpIntention: tup[1] = eo)[2],
                                 counter |-> 0,
                                 track |-> TrackSeqSetInit]]
  /\ ExperState = [ep \in Exper |-> [state |-> "Idle",
                                     received_msg |-> empty_msg,
                                     sent_msg |-> empty_msg,
                                     pub_priv |-> {},
                                     exp_priv |-> {},
                                     pub_cmd |-> {},
                                     unused_pub_priv |-> {},
                                     unused_exp_priv |-> {},
                                     run_targets |-> (CHOOSE tup \in ExperIntention: tup[1] = ep)[2],
                                     counter |-> 0,
                                     track |-> TrackSeqSetInit]]
  /\ BrokerState = [b \in Broker |-> [state |-> "Idle",
                                      received_msg |-> empty_msg,
                                      sent_msg |-> empty_msg,
                                      sub_info |-> {},
                                      pub_info |-> {},
                                      notified |-> {},
                                      counter |-> 0,
                                      track |-> TrackSeqSetInit]]
  /\ EndpointState = [e \in Endpoint |-> [state |-> "Idle",
                                          received_msg |-> empty_msg,
                                          sent_msg |-> empty_msg,
                                          run_info |-> null_info,
                                          executed_exp |-> {},
                                          counter |-> 0,
                                          track |-> TrackSeqSetInit]]
  /\ ControllerState = [c \in Controller |-> [state |-> "Idle",
                                              received_msg |-> empty_msg,
                                              sent_msg |-> empty_msg,
                                              counter |-> 0,
                                              track |-> TrackSeqSetInit]]
  /\ msgs = {}
  /\ AttackerTransitionCnt = [a \in Attacker |-> 0]

-----------------------------------------------------------------------------
(***************************************************************************)
(*                            Useful Definitions                           *)
(***************************************************************************)

UnseenSeq(track, entity, seq) ==
    ~seq \in (CHOOSE tup \in track: tup[1] = entity)[2]

UpdatedTrackSeqSet(orgtrack, entity, seq) ==
    LET record == (CHOOSE tup \in orgtrack: tup[1] = entity)
    IN (orgtrack \ {record}) \cup {<<record[1], record[2] \cup {seq}>>}

(***************************************************************************)
(*                               The actions.                              *)
(***************************************************************************)
(***************************************************************************)
(*                         BOp principal actions.                          *)
(***************************************************************************)

BOpPosRspReqSubPriv(bo) ==
    /\ BOpState[bo].state = "Idle"
    /\ \E m \in msgs :
        /\ m.type = "req_sub_priv"
        /\ m.receiver = bo
        /\ UnseenSeq(BOpState[bo].track, m.sender, m.seq)
        /\ \E target_broker \in Everyone:
            /\ <<bo, m.sender, target_broker>> \in BOpAllowedEOp
            /\ msgs' = msgs \cup
                       {[type |-> "rsp_sub_priv",
                         seq |-> m.seq,
                         sender |-> bo,
                         receiver |-> m.sender,
                         broker |-> target_broker]}
            /\ BOpState' = [BOpState EXCEPT ![bo].sub_priv = BOpState[bo].sub_priv \cup
                                                             {<<m.sender, m.channel, target_broker>>},
                                            ![bo].track = UpdatedTrackSeqSet(BOpState[bo].track, m.sender, m.seq)]
        /\ UNCHANGED <<EOpState, ExperState, BrokerState, EndpointState, ControllerState>>

BOpNegRspReqSubPriv(bo) ==
    /\ BOpState[bo].state = "Idle"
    /\ \E m \in msgs :
        /\ m.type = "req_sub_priv"
        /\ m.receiver = bo
        /\ UnseenSeq(BOpState[bo].track, m.sender, m.seq)
        /\ \A b \in Everyone: ~ <<bo, m.sender, b>> \in BOpAllowedEOp
        /\ msgs' = msgs \cup
                     {[type |-> "rsp_sub_priv_f",
                       seq |-> m.seq,
                       sender |-> bo,
                       receiver |-> m.sender]}
        /\ BOpState' = [BOpState EXCEPT ![bo].track = UpdatedTrackSeqSet(BOpState[bo].track, m.sender, m.seq)]
        /\ UNCHANGED <<EOpState, ExperState, BrokerState, EndpointState, ControllerState>>

BOpPosRspReqPubPriv(bo) ==
    /\ BOpState[bo].state = "Idle"
    /\ \E m \in msgs :
        /\ m.type = "req_pub_priv"
        /\ m.receiver = bo
        /\ UnseenSeq(BOpState[bo].track, m.sender, m.seq)
        /\ <<bo, m.sender>> \in BOpAllowedExper
        /\ <<bo, m.broker>> \in BOpOwnedBroker
        /\ msgs' = msgs \cup
                     {[type |-> "rsp_pub_priv",
                       seq |-> m.seq,
                       sender |-> bo,
                       receiver |-> m.sender]}
        /\ BOpState' = [BOpState EXCEPT ![bo].pub_priv = BOpState[bo].pub_priv \cup {<<m.sender, m.broker>>},
                                        ![bo].track = UpdatedTrackSeqSet(BOpState[bo].track, m.sender, m.seq)]
        /\ UNCHANGED <<EOpState, ExperState, BrokerState, EndpointState, ControllerState>>

BOpNegRspReqPubPriv(bo) ==
    /\ BOpState[bo].state = "Idle"
    /\ \E m \in msgs :
        /\ m.type = "req_pub_priv"
        /\ m.receiver = bo
        /\ UnseenSeq(BOpState[bo].track, m.sender, m.seq)
        /\ \/ ~ <<bo, m.sender>> \in BOpAllowedExper
           \/ ~ <<bo, m.broker>> \in BOpOwnedBroker
        /\ msgs' = msgs \cup
                     {[type |-> "rsp_pub_priv_f",
                       seq |-> m.seq,
                       sender |-> bo,
                       receiver |-> m.sender]}
        /\ BOpState' = [BOpState EXCEPT ![bo].track = UpdatedTrackSeqSet(BOpState[bo].track, m.sender, m.seq)]
        /\ UNCHANGED <<EOpState, ExperState, BrokerState, EndpointState, ControllerState>>
(***************************************************************************)
(*                           BOp agent actions.                            *)
(***************************************************************************)
(***************************************************************************)
(*                          Request sub actions.                           *)
(***************************************************************************)

BOpProcessAuthSub(bo) ==
    /\ BOpState[bo].state = "Idle"
    /\ \E m \in msgs :
        /\ m.type = "auth_sub_req"
        /\ m.receiver = bo
        /\ <<bo, m.sender>> \in BOpOwnedBroker
        /\ UnseenSeq(BOpState[bo].track, m.sender, m.seq)
        /\ \/ /\ ~<<m.owner, m.channel, m.sender>> \in BOpState[bo].sub_priv
              /\ msgs' = msgs \cup {[type |-> "nack_auth_sub_req", seq |-> m.seq, sender |-> bo, receiver |-> m.sender]}
              /\ BOpState' = [BOpState EXCEPT ![bo].track = UpdatedTrackSeqSet(BOpState[bo].track, m.sender, m.seq)]
              /\ UNCHANGED <<EOpState, ExperState, BrokerState, EndpointState, ControllerState>>
           \/ /\ <<m.owner, m.channel, m.sender>> \in BOpState[bo].sub_priv
              /\ LET auth_m == [type |-> "req_auth_sub_agent",
                                seq |-> BOpState[bo].counter,
                                sender |-> bo,
                                receiver |-> m.owner,
                                origin |-> m.origin,
                                target |-> m.sender,
                                channel |-> m.channel]
                 IN /\ BOpState' = [BOpState EXCEPT ![bo].state = "AwaitAuthAgentSub",
                                                    ![bo].counter = BOpState[bo].counter+1,
                                                    ![bo].track = UpdatedTrackSeqSet(BOpState[bo].track, m.sender, m.seq),
                                                    ![bo].received_msg = m,
                                                    ![bo].sent_msg = auth_m]
                    /\ msgs' = msgs \cup {auth_m}
              /\ UNCHANGED <<EOpState, ExperState, BrokerState, EndpointState, ControllerState>>

BOpPosRspAuthSub(bo) ==
    /\ BOpState[bo].state = "AwaitAuthAgentSub"
    /\ \E m \in msgs :
        /\ m.type = "rsp_auth_sub_agent"
        /\ m.receiver = bo
        /\ BOpState[bo].sent_msg.receiver = m.sender
        /\ BOpState[bo].sent_msg.seq = m.seq
        /\ msgs' = msgs \cup {[type |-> "ack_auth_sub_req",
                               seq |-> BOpState[bo].received_msg.seq,
                               sender |-> bo,
                               receiver |-> BOpState[bo].received_msg.sender]}
        /\ BOpState' = [BOpState EXCEPT ![bo].state = "Idle",
                                        ![bo].received_msg = empty_msg,
                                        ![bo].sent_msg = empty_msg]
        /\ UNCHANGED <<EOpState, ExperState, BrokerState, EndpointState, ControllerState>>

BOpNegRspAuthSub(bo) ==
    /\ BOpState[bo].state = "AwaitAuthAgentSub"
    /\ \E m \in msgs :
        /\ m.type = "rsp_auth_sub_agent_f"
        /\ m.receiver = bo
        /\ BOpState[bo].sent_msg.receiver = m.sender
        /\ BOpState[bo].sent_msg.seq = m.seq
        /\ msgs' = msgs \cup {[type |-> "nack_auth_sub_req",
                               seq |-> BOpState[bo].received_msg.seq,
                               sender |-> bo,
                               receiver |-> BOpState[bo].received_msg.sender]}
        /\ BOpState' = [BOpState EXCEPT ![bo].state = "Idle",
                                        ![bo].received_msg = empty_msg,
                                        ![bo].sent_msg = empty_msg]
        /\ UNCHANGED <<EOpState, ExperState, BrokerState, EndpointState, ControllerState>>

(***************************************************************************)
(*                          Request pub actions.                           *)
(***************************************************************************)

BOpProcessAuthPub(bo) ==
    /\ BOpState[bo].state = "Idle"
    /\ \E m \in msgs :
        /\ m.type = "auth_pub_req"
        /\ m.receiver = bo
        /\ <<bo, m.sender>> \in BOpOwnedBroker
        /\ UnseenSeq(BOpState[bo].track, m.sender, m.seq)
        /\ \/ /\ ~<<m.owner, m.sender>> \in BOpState[bo].pub_priv
              /\ msgs' = msgs \cup {[type |-> "nack_auth_pub_req", seq |-> m.seq, sender |-> bo, receiver |-> m.sender]}
              /\ BOpState' = [BOpState EXCEPT ![bo].track = UpdatedTrackSeqSet(BOpState[bo].track, m.sender, m.seq)]
              /\ UNCHANGED <<EOpState, ExperState, BrokerState, EndpointState, ControllerState>>
           \/ /\ <<m.owner, m.sender>> \in BOpState[bo].pub_priv
              /\ LET auth_m == [type |-> "req_auth_pub_agent",
                                seq |-> BOpState[bo].counter,
                                sender |-> bo,
                                receiver |-> m.owner,
                                origin |-> m.origin,
                                target |-> m.sender,
                                channel |-> m.channel,
                                exp |-> m.exp,
                                sni |-> m.sni]
                 IN /\ BOpState' = [BOpState EXCEPT ![bo].state = "AwaitAuthAgentPub",
                                                    ![bo].counter = BOpState[bo].counter+1,
                                                    ![bo].track = UpdatedTrackSeqSet(BOpState[bo].track, m.sender, m.seq),
                                                    ![bo].received_msg = m,
                                                    ![bo].sent_msg = auth_m]
                    /\ msgs' = msgs \cup {auth_m}
              /\ UNCHANGED <<EOpState, ExperState, BrokerState, EndpointState, ControllerState>>

BOpPosRspAuthPub(bo) ==
    /\ BOpState[bo].state = "AwaitAuthAgentPub"
    /\ \E m \in msgs :
        /\ m.type = "rsp_auth_pub_agent"
        /\ m.receiver = bo
        /\ BOpState[bo].sent_msg.receiver = m.sender
        /\ BOpState[bo].sent_msg.seq = m.seq
        /\ msgs' = msgs \cup {[type |-> "ack_auth_pub_req",
                               seq |-> BOpState[bo].received_msg.seq,
                               sender |-> bo,
                               receiver |-> BOpState[bo].received_msg.sender]}
        /\ BOpState' = [BOpState EXCEPT ![bo].state = "Idle",
                                        ![bo].received_msg = empty_msg,
                                        ![bo].sent_msg = empty_msg]
        /\ UNCHANGED <<EOpState, ExperState, BrokerState, EndpointState, ControllerState>>

BOpNegRspAuthPub(bo) ==
    /\ BOpState[bo].state = "AwaitAuthAgentPub"
    /\ \E m \in msgs :
        /\ m.type = "rsp_auth_pub_agent_f"
        /\ m.receiver = bo
        /\ BOpState[bo].sent_msg.receiver = m.sender
        /\ BOpState[bo].sent_msg.seq = m.seq
        /\ msgs' = msgs \cup {[type |-> "nack_auth_pub_req",
                               seq |-> BOpState[bo].received_msg.seq,
                               sender |-> bo,
                               receiver |-> BOpState[bo].received_msg.sender]}
        /\ BOpState' = [BOpState EXCEPT ![bo].state = "Idle",
                                        ![bo].received_msg = empty_msg,
                                        ![bo].sent_msg = empty_msg]
        /\ UNCHANGED <<EOpState, ExperState, BrokerState, EndpointState, ControllerState>>

(***************************************************************************)
(*                             Broker actions.                             *)
(***************************************************************************)
(***************************************************************************)
(*                          Request sub actions.                           *)
(***************************************************************************)

BrokerProcessReqSub(b) ==
    /\ BrokerState[b].state = "Idle"
    /\ \E m \in msgs :
        /\ m.type = "req_sub"
        /\ m.receiver = b
        /\ UnseenSeq(BrokerState[b].track, m.sender, m.seq)
        /\ LET auth_m == [type |-> "auth_sub_req",
                          seq |-> BrokerState[b].counter,
                          sender |-> b,
                          receiver |-> (CHOOSE tup \in BOpOwnedBroker: tup[2] = b)[1],
                          origin |-> m.sender,
                          owner |-> m.owner,
                          channel |-> m.channel]
           IN /\ BrokerState' = [BrokerState EXCEPT ![b].state = "AwaitSubAuth",
                                                    ![b].counter = BrokerState[b].counter+1,
                                                    ![b].track = UpdatedTrackSeqSet(BrokerState[b].track, m.sender, m.seq),
                                                    ![b].received_msg = m,
                                                    ![b].sent_msg = auth_m]
              /\ msgs' = msgs \cup {auth_m}
        /\ UNCHANGED <<EOpState, ExperState, BOpState, EndpointState, ControllerState>>

BrokerPosRspReqSub(b) ==
    /\ BrokerState[b].state = "AwaitSubAuth"
    /\ \E m \in msgs :
        /\ m.type = "ack_auth_sub_req"
        /\ m.receiver = b
        /\ BrokerState[b].sent_msg.receiver = m.sender
        /\ BrokerState[b].sent_msg.seq = m.seq
        /\ msgs' = msgs \cup {[type |-> "rsp_sub",
                               seq |-> BrokerState[b].received_msg.seq,
                               sender |-> b,
                               receiver |-> BrokerState[b].received_msg.sender]}
        /\ BrokerState' = [BrokerState EXCEPT ![b].state = "Idle",
                                              ![b].received_msg = empty_msg,
                                              ![b].sent_msg = empty_msg,
                                              ![b].sub_info =
                                                BrokerState[b].sub_info \cup
                                                {<<BrokerState[b].received_msg.sender,
                                                   BrokerState[b].received_msg.channel>>}]
        /\ UNCHANGED <<EOpState, ExperState, BOpState, EndpointState, ControllerState>>

BrokerNegRspReqSub(b) ==
    /\ BrokerState[b].state = "AwaitSubAuth"
    /\ \E m \in msgs :
        /\ m.type = "nack_auth_sub_req"
        /\ m.receiver = b
        /\ BrokerState[b].sent_msg.receiver = m.sender
        /\ BrokerState[b].sent_msg.seq = m.seq
        /\ msgs' = msgs \cup {[type |-> "rsp_sub_f",
                               seq |-> BrokerState[b].received_msg.seq,
                               sender |-> b,
                               receiver |-> BrokerState[b].received_msg.sender]}
        /\ BrokerState' = [BrokerState EXCEPT ![b].state = "Idle",
                                              ![b].received_msg = empty_msg,
                                              ![b].sent_msg = empty_msg]
        /\ UNCHANGED <<EOpState, ExperState, BOpState, EndpointState, ControllerState>>


(***************************************************************************)
(*                          Request pub actions.                           *)
(***************************************************************************)

BrokerProcessReqPub(b) ==
    /\ BrokerState[b].state = "Idle"
    /\ \E m \in msgs :
        /\ m.type = "req_pub"
        /\ m.receiver = b
        /\ UnseenSeq(BrokerState[b].track, m.sender, m.seq)
        /\ LET auth_m == [type |-> "auth_pub_req",
                          seq |-> BrokerState[b].counter,
                          sender |-> b,
                          receiver |-> (CHOOSE tup \in BOpOwnedBroker: tup[2] = b)[1],
                          origin |-> m.sender,
                          owner |-> m.owner,
                          exp |-> m.exp,
                          channel |-> m.channel,
                          sni |-> m.sni]
           IN /\ BrokerState' = [BrokerState EXCEPT ![b].state = "AwaitPubAuth",
                                                    ![b].counter = BrokerState[b].counter+1,
                                                    ![b].track = UpdatedTrackSeqSet(BrokerState[b].track, m.sender, m.seq),
                                                    ![b].received_msg = m,
                                                    ![b].sent_msg = auth_m]
              /\ msgs' = msgs \cup {auth_m}
        /\ UNCHANGED <<EOpState, ExperState, BOpState, EndpointState, ControllerState>>

BrokerPosRspReqPub(b) ==
    /\ BrokerState[b].state = "AwaitPubAuth"
    /\ \E m \in msgs :
        /\ m.type = "ack_auth_pub_req"
        /\ m.receiver = b
        /\ BrokerState[b].sent_msg.receiver = m.sender
        /\ BrokerState[b].sent_msg.seq = m.seq
        /\ msgs' = msgs \cup {[type |-> "rsp_pub",
                               seq |-> BrokerState[b].received_msg.seq,
                               sender |-> b,
                               receiver |-> BrokerState[b].received_msg.sender]}
        /\ BrokerState' = [BrokerState EXCEPT ![b].state = "Idle",
                                              ![b].received_msg = empty_msg,
                                              ![b].sent_msg = empty_msg,
                                              ![b].pub_info =
                                                BrokerState[b].pub_info \cup
                                                {<< BrokerState[b].received_msg.sender,
                                                    BrokerState[b].received_msg.exp,
                                                    BrokerState[b].received_msg.channel,
                                                    BrokerState[b].received_msg.sni >>}]
        /\ UNCHANGED <<EOpState, ExperState, BOpState, EndpointState, ControllerState>>

BrokerNegRspReqPub(b) ==
    /\ BrokerState[b].state = "AwaitPubAuth"
    /\ \E m \in msgs :
        /\ m.type = "nack_auth_pub_req"
        /\ m.receiver = b
        /\ BrokerState[b].sent_msg.receiver = m.sender
        /\ BrokerState[b].sent_msg.seq = m.seq
        /\ msgs' = msgs \cup {[type |-> "rsp_pub_f",
                               seq |-> BrokerState[b].received_msg.seq,
                               sender |-> b,
                               receiver |-> BrokerState[b].received_msg.sender]}
        /\ BrokerState' = [BrokerState EXCEPT ![b].state = "Idle",
                                              ![b].received_msg = empty_msg,
                                              ![b].sent_msg = empty_msg]
        /\ UNCHANGED <<EOpState, ExperState, BOpState, EndpointState, ControllerState>>

(***************************************************************************)
(*                Notify and run exp endpoint auth actions.                *)
(***************************************************************************)

BrokerNotifyExp(b) ==
    /\ BrokerState[b].state = "Idle"
    /\ \E sub_info \in BrokerState[b].sub_info :
        /\ \E pub_info \in BrokerState[b].pub_info :
            /\ sub_info[2] = pub_info[3]
            /\ ~ <<sub_info[1], pub_info[1], pub_info[2], pub_info[3], pub_info[4]>> \in BrokerState[b].notified
            /\ msgs' = msgs \cup {[type |-> "notify_exp",
                                   seq |-> BrokerState[b].counter,
                                   sender |-> b,
                                   receiver |-> sub_info[1],
                                   target |-> pub_info[1],
                                   exp |-> pub_info[2],
                                   channel |-> pub_info[3],
                                   sni |-> pub_info[4]]}
            /\ BrokerState' = [BrokerState EXCEPT ![b].notified =
                                                     BrokerState[b].notified \cup
                                                     {<<sub_info[1], pub_info[1], pub_info[2], pub_info[3], pub_info[4]>>},
                                                  ![b].counter = BrokerState[b].counter+1]
    /\ UNCHANGED <<EOpState, ExperState, BOpState, EndpointState, ControllerState>>

(***************************************************************************)
(*                         EOp principal actions.                          *)
(***************************************************************************)

EOpReqSubPriv(eo) ==
    /\ EOpState[eo].state = "Idle"
    /\ ~EOpState[eo].sub_targets = {}
    /\ LET target_tup == (CHOOSE cand_tup \in EOpState[eo].sub_targets: TRUE)
           req_m == [type |-> "req_sub_priv",
                     seq |-> EOpState[eo].counter,
                     sender |-> eo,
                     receiver |-> target_tup[1],
                     channel |-> target_tup[2]]
       IN /\ EOpState' = [EOpState EXCEPT ![eo].sub_targets = EOpState[eo].sub_targets \ {target_tup},
                                          ![eo].counter = EOpState[eo].counter+1,
                                          ![eo].state = "AwaitSubPrivilege",
                                          ![eo].sent_msg = req_m]
          /\ msgs' = msgs \cup {req_m}
    /\ UNCHANGED <<BOpState, ExperState, BrokerState, EndpointState, ControllerState>>

EOpPosRspReqSubPriv(eo) ==
    /\ EOpState[eo].state = "AwaitSubPrivilege"
    /\ \E m \in msgs :
        /\ m.type = "rsp_sub_priv"
        /\ m.receiver = eo
        /\ EOpState[eo].sent_msg.receiver = m.sender
        /\ EOpState[eo].sent_msg.seq = m.seq
        /\ EOpState' = [EOpState EXCEPT ![eo].state = "Idle",
                                        ![eo].sent_msg = empty_msg,
                                        ![eo].sub_priv =
                                            EOpState[eo].sub_priv \cup
                                            {<<m.sender, EOpState[eo].sent_msg.channel, m.broker>>},
                                        ![eo].unused_sub_priv =
                                            EOpState[eo].unused_sub_priv \cup
                                            {<<m.sender, EOpState[eo].sent_msg.channel, m.broker>>}]
        /\ UNCHANGED <<BOpState, ExperState, BrokerState, EndpointState, ControllerState, msgs>>

EOpNegRspReqSubPriv(eo) ==
    /\ EOpState[eo].state = "AwaitSubPrivilege"
    /\ \E m \in msgs :
        /\ m.type = "rsp_sub_priv_f"
        /\ m.receiver = eo
        /\ EOpState[eo].sent_msg.receiver = m.sender
        /\ EOpState[eo].sent_msg.seq = m.seq
        /\ EOpState' = [EOpState EXCEPT ![eo].state = "Idle",
                                        ![eo].sent_msg = empty_msg]
        /\ UNCHANGED <<BOpState, ExperState, BrokerState, EndpointState, ControllerState, msgs>>

\* consider remove broker tup non-determinism
EOpPosRspReqExpPriv(eo) ==
    /\ EOpState[eo].state = "Idle"
    /\ \E m \in msgs :
        /\ m.type = "req_exp_priv"
        /\ m.receiver = eo
        /\ UnseenSeq(EOpState[eo].track, m.sender, m.seq)
        /\ <<eo, m.sender>> \in EOpAllowedExper
        /\ <<eo, m.exp>> \in EOpAllowedExp
        /\ ~ EOpState[eo].sub_priv = {} \* reply to exp_priv only after having assigned broker
        /\ LET broker_tup == (CHOOSE tup \in EOpState[eo].sub_priv: TRUE)
               exp_priv_tup == (CHOOSE tup \in EOpAllowedExp: tup[1] = eo)
           IN /\ msgs' = msgs \cup
                     {[type |-> "rsp_exp_priv",
                       seq |-> m.seq,
                       sender |-> eo,
                       receiver |-> m.sender,
                       broker_owner |-> broker_tup[1],
                       broker |-> broker_tup[3],
                       channel |-> broker_tup[2],
                       exp_priv |-> exp_priv_tup[2]]} \* may be a set instead
              /\ EOpState' = [EOpState EXCEPT ![eo].exp_priv = EOpState[eo].exp_priv \cup
                                                               {<<m.sender,
                                                                  broker_tup[2],
                                                                  broker_tup[3],
                                                                  exp_priv_tup[2]>>},
                                              ![eo].track = UpdatedTrackSeqSet(EOpState[eo].track, m.sender, m.seq)]
        /\ UNCHANGED <<BOpState, ExperState, BrokerState, EndpointState, ControllerState>>

EOpNegRspReqExpPriv(eo) ==
    /\ EOpState[eo].state = "Idle"
    /\ \E m \in msgs :
        /\ m.type = "req_exp_priv"
        /\ m.receiver = eo
        /\ UnseenSeq(EOpState[eo].track, m.sender, m.seq)
        /\ \/ ~ <<eo, m.sender>> \in EOpAllowedExper
           \/ ~ <<eo, m.exp>> \in EOpAllowedExp
        /\ msgs' = msgs \cup
                     {[type |-> "rsp_exp_priv_f",
                       seq |-> m.seq,
                       sender |-> eo,
                       receiver |-> m.sender]}
        /\ EOpState' = [EOpState EXCEPT ![eo].track = UpdatedTrackSeqSet(EOpState[eo].track, m.sender, m.seq)]
        /\ UNCHANGED <<BOpState, ExperState, BrokerState, EndpointState, ControllerState>>

(***************************************************************************)
(*                           EOp agent actions.                            *)
(***************************************************************************)
(***************************************************************************)
(*                          Request sub actions.                           *)
(***************************************************************************)

\* triggered only when no sub_targets left
EOpCmdSub(eo) ==
    /\ EOpState[eo].state = "Idle"
    /\ EOpState[eo].sub_targets = {}
    /\ \E sub_priv \in EOpState[eo].unused_sub_priv :
        /\ LET target_agent == (CHOOSE tup \in EOpOwnedEndpoint: tup[1] = eo)[2]
               cmd_m == [type |-> "cmd_sub",
                         seq |-> EOpState[eo].counter,
                         sender |-> eo,
                         receiver |-> target_agent,
                         broker |-> sub_priv[3],
                         channel |-> sub_priv[2]]
           IN /\ EOpState' = [EOpState EXCEPT ![eo].state = "AwaitSub",
                                              ![eo].counter = EOpState[eo].counter+1,
                                              ![eo].sent_msg = cmd_m,
                                              ![eo].sub_cmd =
                                                  EOpState[eo].sub_cmd \cup
                                                  {<<cmd_m.receiver, cmd_m.channel, cmd_m.broker>>},
                                              ![eo].unused_sub_priv = EOpState[eo].unused_sub_priv \ {sub_priv}]
              /\ msgs' = msgs \cup {cmd_m}
    /\ UNCHANGED <<BOpState, ExperState, BrokerState, EndpointState, ControllerState>>

EOpPosRspCmdSub(eo) ==
    /\ EOpState[eo].state = "AwaitSub"
    /\ \E m \in msgs :
        /\ m.type = "ack_cmd_sub"
        /\ m.receiver = eo
        /\ EOpState[eo].sent_msg.receiver = m.sender
        /\ EOpState[eo].sent_msg.seq = m.seq
        /\ EOpState' = [EOpState EXCEPT ![eo].state = "Idle",
                                        ![eo].sent_msg = empty_msg]
        /\ UNCHANGED <<BOpState, ExperState, BrokerState, EndpointState, ControllerState, msgs>>

EOpNegRspCmdSub(eo) ==
    /\ EOpState[eo].state = "AwaitSub"
    /\ \E m \in msgs :
        /\ m.type = "nack_cmd_sub"
        /\ m.receiver = eo
        /\ EOpState[eo].sent_msg.receiver = m.sender
        /\ EOpState[eo].sent_msg.seq = m.seq
        /\ EOpState' = [EOpState EXCEPT ![eo].state = "Idle",
                                        ![eo].sent_msg = empty_msg,
                                        ![eo].sub_cmd =
                                            EOpState[eo].sub_cmd \
                                            {<<EOpState[eo].sent_msg.receiver,
                                               EOpState[eo].sent_msg.channel,
                                               EOpState[eo].sent_msg.broker>>}]
        /\ UNCHANGED <<BOpState, ExperState, BrokerState, EndpointState, ControllerState, msgs>>

EOpProcessReqAuthSubAgent(eo) ==
    /\ EOpState[eo].state = "AwaitSub"
    /\ \E m \in msgs :
        /\ m.type = "req_auth_sub_agent"
        /\ m.receiver = eo
        /\ UnseenSeq(EOpState[eo].track, m.sender, m.seq)
        /\ EOpState' = [EOpState EXCEPT ![eo].track = UpdatedTrackSeqSet(EOpState[eo].track, m.sender, m.seq)]
        /\ LET check1 == \E sub_priv \in EOpState[eo].sub_priv :
                            /\ sub_priv[1] = m.sender
                            /\ sub_priv[2] = m.channel
                            /\ sub_priv[3] = m.target
               check2 == \E sub_cmd \in EOpState[eo].sub_cmd :
                            /\ sub_cmd[1] = m.origin
                            /\ sub_cmd[2] = m.channel
                            /\ sub_cmd[3] = m.target
               pos_m == [type |-> "rsp_auth_sub_agent",
                         seq |-> m.seq,
                         sender |-> eo,
                         receiver |-> m.sender]
               neg_m == [type |-> "rsp_auth_sub_agent_f",
                         seq |-> m.seq,
                         sender |-> eo,
                         receiver |-> m.sender]
           IN \/ /\ check1
                 /\ check2
                 /\ msgs' = msgs \cup {pos_m}
                 /\ UNCHANGED <<BOpState, ExperState, BrokerState, EndpointState, ControllerState>>
              \/ /\ ~check1
                 /\ msgs' = msgs \cup {neg_m}
                 /\ UNCHANGED <<BOpState, ExperState, BrokerState, EndpointState, ControllerState>>
              \/ /\ ~check2
                 /\ msgs' = msgs \cup {neg_m}
                 /\ UNCHANGED <<BOpState, ExperState, BrokerState, EndpointState, ControllerState>>

(***************************************************************************)
(*                Notify and run exp endpoint auth actions.                *)
(***************************************************************************)

EOpProcessAuthNotify(eo) ==
    /\ EOpState[eo].state = "Idle"
    /\ \E m \in msgs :
        /\ m.type = "auth_notify"
        /\ m.receiver = eo
        /\ <<eo, m.sender>> \in EOpOwnedEndpoint
        /\ UnseenSeq(EOpState[eo].track, m.sender, m.seq)
        /\ EOpState' = [EOpState EXCEPT ![eo].track = UpdatedTrackSeqSet(EOpState[eo].track, m.sender, m.seq)]
        /\ LET check == \E sub_cmd \in EOpState[eo].sub_cmd :
                            /\ sub_cmd[1] = m.sender
                            /\ sub_cmd[2] = m.channel
                            /\ sub_cmd[3] = m.notifier
               pos_m == [type |-> "ack_auth_notify",
                         seq |-> m.seq,
                         sender |-> eo,
                         receiver |-> m.sender]
               neg_m == [type |-> "nack_auth_notify",
                         seq |-> m.seq,
                         sender |-> eo,
                         receiver |-> m.sender]
           IN \/ /\ check
                 /\ msgs' = msgs \cup {pos_m}
                 /\ UNCHANGED <<BOpState, ExperState, BrokerState, EndpointState, ControllerState>>
              \/ /\ ~check
                 /\ msgs' = msgs \cup {neg_m}
                 /\ UNCHANGED <<BOpState, ExperState, BrokerState, EndpointState, ControllerState>>

EOpProcessAuthExp(eo) ==
    /\ EOpState[eo].state = "Idle"
    /\ \E m \in msgs :
        /\ m.type = "auth_exp"
        /\ m.receiver = eo
        /\ UnseenSeq(EOpState[eo].track, m.sender, m.seq)
        /\ LET check1 == \E sub_cmd \in EOpState[eo].sub_cmd :
                            /\ sub_cmd[1] = m.sender
                            /\ sub_cmd[2] = m.channel
                            /\ sub_cmd[3] = m.notifier
               check2 == \E exp_priv \in EOpState[eo].exp_priv :
                            /\ exp_priv[1] = m.owner
                            /\ exp_priv[2] = m.channel
                            /\ exp_priv[3] = m.notifier
               further_auth_m == [type |-> "req_auth_exp_agent",
                                  seq |-> EOpState[eo].counter,
                                  sender |-> eo,
                                  receiver |-> m.owner,
                                  origin |-> m.origin,
                                  exp |-> m.exp,
                                  notifier |-> m.notifier,
                                  channel |-> m.channel]
               neg_m == [type |-> "nack_auth_exp",
                         seq |-> m.seq,
                         sender |-> eo,
                         receiver |-> m.sender]
           IN \/ /\ check1
                 /\ check2
                 /\ EOpState' = [EOpState EXCEPT ![eo].state = "AwaitAuthAgentExp",
                                                 ![eo].counter = EOpState[eo].counter+1,
                                                 ![eo].track = UpdatedTrackSeqSet(EOpState[eo].track, m.sender, m.seq),
                                                 ![eo].sent_msg = further_auth_m,
                                                 ![eo].received_msg = m]
                 /\ msgs' = msgs \cup {further_auth_m}
                 /\ UNCHANGED <<BOpState, ExperState, BrokerState, EndpointState, ControllerState>>
              \/ /\ ~check1
                 /\ msgs' = msgs \cup {neg_m}
                 /\ EOpState' = [EOpState EXCEPT ![eo].track = UpdatedTrackSeqSet(EOpState[eo].track, m.sender, m.seq)]
                 /\ UNCHANGED <<BOpState, ExperState, BrokerState, EndpointState, ControllerState>>
              \/ /\ ~check2
                 /\ msgs' = msgs \cup {neg_m}
                 /\ EOpState' = [EOpState EXCEPT ![eo].track = UpdatedTrackSeqSet(EOpState[eo].track, m.sender, m.seq)]
                 /\ UNCHANGED <<BOpState, ExperState, BrokerState, EndpointState, ControllerState>>

EOpPosRspAuthExp(eo) ==
    /\ EOpState[eo].state = "AwaitAuthAgentExp"
    /\ \E m \in msgs :
        /\ m.type = "rsp_auth_exp_agent"
        /\ m.receiver = eo
        /\ EOpState[eo].sent_msg.receiver = m.sender
        /\ EOpState[eo].sent_msg.seq = m.seq
        /\ EOpState' = [EOpState EXCEPT ![eo].state = "Idle",
                                        ![eo].sent_msg = empty_msg,
                                        ![eo].received_msg = empty_msg]
        /\ LET pos_m == [type |-> "ack_auth_exp",
                         seq |-> EOpState[eo].received_msg.seq,
                         sender |-> eo,
                         receiver |-> EOpState[eo].received_msg.sender,
                         exp_priv |-> (CHOOSE tup \in EOpState[eo].exp_priv:
                                            /\ tup[1] = m.sender
                                            /\ tup[2] = EOpState[eo].received_msg.channel
                                            /\ tup[3] = EOpState[eo].received_msg.notifier)[4]]
           IN msgs' = msgs \cup {pos_m}
        /\ UNCHANGED <<BOpState, ExperState, BrokerState, EndpointState, ControllerState>>

EOpNegRspAuthExp(eo) ==
    /\ EOpState[eo].state = "AwaitAuthAgentExp"
    /\ \E m \in msgs :
        /\ m.type = "rsp_auth_exp_agent_f"
        /\ m.receiver = eo
        /\ EOpState[eo].sent_msg.receiver = m.sender
        /\ EOpState[eo].sent_msg.seq = m.seq
        /\ EOpState' = [EOpState EXCEPT ![eo].state = "Idle",
                                        ![eo].sent_msg = empty_msg,
                                        ![eo].received_msg = empty_msg]
        /\ LET neg_m == [type |-> "nack_auth_exp",
                         seq |-> EOpState[eo].received_msg.seq,
                         sender |-> eo,
                         receiver |-> EOpState[eo].received_msg.sender]
           IN msgs' = msgs \cup {neg_m}
        /\ UNCHANGED <<BOpState, ExperState, BrokerState, EndpointState, ControllerState>>

(***************************************************************************)
(*               Notify and run exp controller auth actions.               *)
(***************************************************************************)

EOpProcessReqAuthHelpAgent(eo) ==
    /\ EOpState[eo].state = "Idle"
    /\ \E m \in msgs :
        /\ m.type = "req_auth_help_agent"
        /\ m.receiver = eo
        /\ UnseenSeq(EOpState[eo].track, m.sender, m.seq)
        /\ EOpState' = [EOpState EXCEPT ![eo].track = UpdatedTrackSeqSet(EOpState[eo].track, m.sender, m.seq)]
        /\ LET check == \E exp_priv \in EOpState[eo].exp_priv :
                            /\ exp_priv[1] = m.sender
                            /\ \E sub_cmd \in EOpState[eo].sub_cmd :
                                /\ sub_cmd[1] = m.helper
                                /\ sub_cmd[2] = exp_priv[2]
                                /\ sub_cmd[3] = exp_priv[3]
               pos_m == [type |-> "rsp_auth_help_agent",
                         seq |-> m.seq,
                         sender |-> eo,
                         receiver |-> m.sender]
               neg_m == [type |-> "rsp_auth_help_agent_f",
                         seq |-> m.seq,
                         sender |-> eo,
                         receiver |-> m.sender]
           IN \/ /\ check
                 /\ msgs' = msgs \cup {pos_m}
                 /\ UNCHANGED <<BOpState, ExperState, BrokerState, EndpointState, ControllerState>>
              \/ /\ ~check
                 /\ msgs' = msgs \cup {neg_m}
                 /\ UNCHANGED <<BOpState, ExperState, BrokerState, EndpointState, ControllerState>>

(***************************************************************************)
(*                            Endpoint actions.                            *)
(***************************************************************************)
(***************************************************************************)
(*                          Request sub actions.                           *)
(***************************************************************************)

EndpointProcessCmdSub(e) ==
    /\ EndpointState[e].state = "Idle"
    /\ \E m \in msgs :
        /\ m.type = "cmd_sub"
        /\ m.receiver = e
        /\ <<m.sender, m.receiver>> \in EOpOwnedEndpoint
        /\ UnseenSeq(EndpointState[e].track, m.sender, m.seq)
        /\ LET req_m == [type |-> "req_sub",
                         seq |-> EndpointState[e].counter,
                         sender |-> e,
                         receiver |-> m.broker,
                         owner |-> m.sender,
                         channel |-> m.channel]
           IN /\ EndpointState' = [EndpointState EXCEPT ![e].state = "AwaitSub",
                                                        ![e].counter = EndpointState[e].counter+1,
                                                        ![e].track = UpdatedTrackSeqSet(EndpointState[e].track, m.sender, m.seq),
                                                        ![e].sent_msg = req_m,
                                                        ![e].received_msg = m]
              /\ msgs' = msgs \cup {req_m}
    /\ UNCHANGED <<BOpState, ExperState, EOpState, BrokerState, ControllerState>>

EndpointPosRspCmdSub(e) ==
    /\ EndpointState[e].state = "AwaitSub"
    /\ \E m \in msgs :
        /\ m.type = "rsp_sub"
        /\ m.receiver = e
        /\ EndpointState[e].sent_msg.receiver = m.sender
        /\ EndpointState[e].sent_msg.seq = m.seq
        /\ LET pos_m == [type |-> "ack_cmd_sub",
                         seq |-> EndpointState[e].received_msg.seq,
                         sender |-> e,
                         receiver |-> EndpointState[e].received_msg.sender]
           IN /\ EndpointState' = [EndpointState EXCEPT ![e].state = "Idle",
                                                        ![e].sent_msg = empty_msg,
                                                        ![e].received_msg = empty_msg]
              /\ msgs' = msgs \cup {pos_m}
    /\ UNCHANGED <<BOpState, ExperState, EOpState, BrokerState, ControllerState>>

EndpointNegRspCmdSub(e) ==
    /\ EndpointState[e].state = "AwaitSub"
    /\ \E m \in msgs :
        /\ m.type = "rsp_sub_f"
        /\ m.receiver = e
        /\ EndpointState[e].sent_msg.receiver = m.sender
        /\ EndpointState[e].sent_msg.seq = m.seq
        /\ LET neg_m == [type |-> "nack_cmd_sub",
                         seq |-> EndpointState[e].received_msg.seq,
                         sender |-> e,
                         receiver |-> EndpointState[e].received_msg.sender]
           IN /\ EndpointState' = [EndpointState EXCEPT ![e].state = "Idle",
                                                        ![e].sent_msg = empty_msg,
                                                        ![e].received_msg = empty_msg]
              /\ msgs' = msgs \cup {neg_m}
    /\ UNCHANGED <<BOpState, ExperState, EOpState, BrokerState, ControllerState>>

(***************************************************************************)
(*                Notify and run exp endpoint auth actions.                *)
(***************************************************************************)

EndpointProcessNotifyExp(e) ==
    /\ EndpointState[e].state = "Idle"
    /\ \E m \in msgs :
        /\ m.type = "notify_exp"
        /\ m.receiver = e
        /\ UnseenSeq(EndpointState[e].track, m.sender, m.seq)
        /\ LET auth_m == [type |-> "auth_notify",
                          seq |-> EndpointState[e].counter,
                          sender |-> e,
                          receiver |-> (CHOOSE tup \in EOpOwnedEndpoint: tup[2] = e)[1],
                          notifier |-> m.sender,
                          channel |-> m.channel]
           IN /\ EndpointState' = [EndpointState EXCEPT ![e].state = "AwaitNotifyAuth",
                                                        ![e].counter = EndpointState[e].counter+1,
                                                        ![e].track = UpdatedTrackSeqSet(EndpointState[e].track, m.sender, m.seq),
                                                        ![e].sent_msg = auth_m,
                                                        ![e].received_msg = m]
              /\ msgs' = msgs \cup {auth_m}
    /\ UNCHANGED <<BOpState, ExperState, EOpState, BrokerState, ControllerState>>

EndpointDecideConnect(e) ==
    /\ EndpointState[e].state = "AwaitNotifyAuth"
    /\ \/ \E m \in msgs :
            /\ m.type = "ack_auth_notify"
            /\ m.receiver = e
            /\ EndpointState[e].sent_msg.receiver = m.sender
            /\ EndpointState[e].sent_msg.seq = m.seq
            /\ LET conn_m == [type |-> "connect",
                              seq |-> EndpointState[e].counter,
                              sender |-> e,
                              receiver |-> EndpointState[e].received_msg.target,
                              sni |-> EndpointState[e].received_msg.sni]
               IN /\ EndpointState' = [EndpointState EXCEPT ![e].state = "AwaitConn",
                                                            ![e].counter = EndpointState[e].counter+1,
                                                            ![e].sent_msg = conn_m]
                  /\ msgs' = msgs \cup {conn_m}
            /\ UNCHANGED <<BOpState, ExperState, EOpState, BrokerState, ControllerState>>
       \/ \E m \in msgs :
            /\ m.type = "nack_auth_notify"
            /\ m.receiver = e
            /\ EndpointState[e].sent_msg.receiver = m.sender
            /\ EndpointState[e].sent_msg.seq = m.seq
            /\ EndpointState' = [EndpointState EXCEPT ![e].state = "Idle",
                                                      ![e].sent_msg = empty_msg,
                                                      ![e].received_msg = empty_msg]
            /\ UNCHANGED <<BOpState, ExperState, EOpState, BrokerState, ControllerState, msgs>>

EndpointRspConnect(e) ==
    /\ EndpointState[e].state = "AwaitConn"
    /\ \/ \E m \in msgs :
            /\ m.type = "conn_accepted"
            /\ m.receiver = e
            /\ EndpointState[e].sent_msg.receiver = m.sender
            /\ EndpointState[e].sent_msg.seq = m.seq
            /\ EndpointState' = [EndpointState EXCEPT ![e].state = "AwaitRunExp",
                                                      ![e].sent_msg = empty_msg]
            /\ UNCHANGED <<BOpState, ExperState, EOpState, BrokerState, ControllerState, msgs>>
       \/ \E m \in msgs :
            /\ m.type = "conn_refused"
            /\ m.receiver = e
            /\ EndpointState[e].sent_msg.receiver = m.sender
            /\ EndpointState[e].sent_msg.seq = m.seq
            /\ EndpointState' = [EndpointState EXCEPT ![e].state = "Idle",
                                                      ![e].sent_msg = empty_msg,
                                                      ![e].received_msg = empty_msg]
            /\ UNCHANGED <<BOpState, ExperState, EOpState, BrokerState, ControllerState, msgs>>

EndpointProcessReqRunExp(e) ==
    /\ EndpointState[e].state = "AwaitRunExp"
    /\ \E m \in msgs :
        /\ m.type = "req_run_exp"
        /\ m.receiver = e
        /\ EndpointState[e].received_msg.target = m.sender
        /\ UnseenSeq(EndpointState[e].track, m.sender, m.seq)
        /\ LET auth_m == [type |-> "auth_exp",
                          seq |-> EndpointState[e].counter,
                          sender |-> e,
                          receiver |-> (CHOOSE tup \in EOpOwnedEndpoint: tup[2] = e)[1],
                          origin |-> m.sender,
                          owner |-> m.owner,
                          exp |-> EndpointState[e].received_msg.exp,
                          notifier |-> EndpointState[e].received_msg.sender,
                          channel |-> EndpointState[e].received_msg.channel]
           IN /\ EndpointState' = [EndpointState EXCEPT ![e].state = "AwaitExpAuth",
                                                        ![e].counter = EndpointState[e].counter+1,
                                                        ![e].track = UpdatedTrackSeqSet(EndpointState[e].track, m.sender, m.seq),
                                                        ![e].sent_msg = auth_m,
                                                        ![e].received_msg = m]
              /\ msgs' = msgs \cup {auth_m}
    /\ UNCHANGED <<BOpState, ExperState, EOpState, BrokerState, ControllerState>>

(***************************************************************************)
(*               Notify and run exp controller auth actions.               *)
(***************************************************************************)

EndpointRspReqRunExp(e) ==
    /\ EndpointState[e].state = "AwaitExpAuth"
    /\ \/ \E m \in msgs :
            /\ m.type = "ack_auth_exp"
            /\ m.receiver = e
            /\ EndpointState[e].sent_msg.receiver = m.sender
            /\ EndpointState[e].sent_msg.seq = m.seq
            /\ LET pos_m == [type |-> "rsp_run_exp",
                             seq |-> EndpointState[e].received_msg.seq,
                             sender |-> e,
                             receiver |-> EndpointState[e].sent_msg.origin]
                   req_m == [type |-> "req_help_exp",
                             seq |-> EndpointState[e].counter,
                             sender |-> e,
                             receiver |-> EndpointState[e].sent_msg.origin,
                             owner |-> m.sender]
               IN /\ EndpointState' = [EndpointState EXCEPT ![e].state = "AwaitHelpExp",
                                                            ![e].counter = EndpointState[e].counter+1,
                                                            ![e].sent_msg = req_m,
                                                            ![e].received_msg = empty_msg,
                                                            ![e].run_info = <<EndpointState[e].sent_msg.origin, m.exp_priv>>]
                  /\ msgs' = msgs \cup {pos_m, req_m}
                  /\ UNCHANGED <<BOpState, ExperState, EOpState, BrokerState, ControllerState>>
       \/ \E m \in msgs :
            /\ m.type = "nack_auth_exp"
            /\ m.receiver = e
            /\ EndpointState[e].sent_msg.receiver = m.sender
            /\ EndpointState[e].sent_msg.seq = m.seq
            /\ EndpointState' = [EndpointState EXCEPT ![e].state = "Idle",
                                                      ![e].sent_msg = empty_msg,
                                                      ![e].received_msg = empty_msg]
            /\ LET neg_m == [type |-> "rsp_run_exp_f",
                             seq |-> EndpointState[e].received_msg.seq,
                             sender |-> e,
                             receiver |-> EndpointState[e].sent_msg.origin]
               IN msgs' = msgs \cup {neg_m}
            /\ UNCHANGED <<BOpState, ExperState, EOpState, BrokerState, ControllerState>>

EndpointRspReqHelpExp(e) ==
    /\ EndpointState[e].state = "AwaitHelpExp"
    /\ \/ \E m \in msgs :
            /\ m.type = "rsp_help_exp"
            /\ m.receiver = e
            /\ EndpointState[e].sent_msg.receiver = m.sender
            /\ EndpointState[e].sent_msg.seq = m.seq
            /\ EndpointState' = [EndpointState EXCEPT ![e].state = "AwaitExp",
                                                      ![e].sent_msg = empty_msg,
                                                      ![e].received_msg = empty_msg]
            /\ UNCHANGED <<BOpState, ExperState, EOpState, BrokerState, ControllerState, msgs>>
       \/ \E m \in msgs :
            /\ m.type = "rsp_help_exp_f"
            /\ m.receiver = e
            /\ EndpointState[e].sent_msg.receiver = m.sender
            /\ EndpointState[e].sent_msg.seq = m.seq
            /\ EndpointState' = [EndpointState EXCEPT ![e].state = "Idle",
                                                      ![e].sent_msg = empty_msg,
                                                      ![e].received_msg = empty_msg,
                                                      ![e].run_info = null_info]
            /\ UNCHANGED <<BOpState, ExperState, EOpState, BrokerState, ControllerState, msgs>>

EndpointExecExp(e) ==
    /\ EndpointState[e].state = "AwaitExp"
    /\ \E m \in msgs :
         /\ m.type = "exec_exp"
         /\ m.receiver = e
         /\ UnseenSeq(EndpointState[e].track, m.sender, m.seq)
         /\ EndpointState[e].run_info[1] = m.sender
         /\ \/ /\ EndpointState[e].run_info[2] = m.exp
               /\ EndpointState' = [EndpointState EXCEPT ![e].state = "Idle",
                                                         ![e].track = UpdatedTrackSeqSet(EndpointState[e].track, m.sender, m.seq),
                                                         ![e].executed_exp = EndpointState[e].executed_exp \cup {<<m.sender, m.exp>>},
                                                         ![e].run_info = null_info]
               /\ UNCHANGED <<BOpState, ExperState, EOpState, BrokerState, ControllerState, msgs>>
            \/ /\ ~EndpointState[e].run_info[2] = m.exp
               /\ EndpointState' = [EndpointState EXCEPT ![e].state = "Idle",
                                                         ![e].track = UpdatedTrackSeqSet(EndpointState[e].track, m.sender, m.seq),
                                                         ![e].run_info = null_info]
               /\ UNCHANGED <<BOpState, ExperState, EOpState, BrokerState, ControllerState, msgs>>

(***************************************************************************)
(*                        Exper principal actions.                         *)
(***************************************************************************)

ExperReqExpPriv(ep) ==
    /\ ExperState[ep].state = "Idle"
    /\ ~ ExperState[ep].run_targets = {}
    /\ LET target_tup == (CHOOSE tup \in ExperState[ep].run_targets: TRUE)
           req_m == [type |-> "req_exp_priv", seq |-> ExperState[ep].counter, sender |-> ep, receiver |-> target_tup[1], exp |-> target_tup[2]]
       IN /\ ExperState' = [ExperState EXCEPT ![ep].run_targets = ExperState[ep].run_targets \ {target_tup},
                                              ![ep].state = "AwaitExpPrivilege",
                                              ![ep].counter = ExperState[ep].counter+1,
                                              ![ep].sent_msg = req_m]
          /\ msgs' = msgs \cup {req_m}
    /\ UNCHANGED <<BOpState, EOpState, BrokerState, EndpointState, ControllerState>>

ExperPosRspReqExpPriv(ep) ==
    /\ ExperState[ep].state = "AwaitExpPrivilege"
    /\ \E m \in msgs :
        /\ m.type = "rsp_exp_priv"
        /\ m.receiver = ep
        /\ ExperState[ep].sent_msg.receiver = m.sender
        /\ ExperState[ep].sent_msg.seq = m.seq
        /\ LET req_m == [type |-> "req_pub_priv", seq |-> ExperState[ep].counter, sender |-> ep, receiver |-> m.broker_owner, broker |-> m.broker]
           IN /\ ExperState' = [ExperState EXCEPT ![ep].state = "AwaitPubPrivilege",
                                                  ![ep].counter = ExperState[ep].counter+1,
                                                  ![ep].exp_priv = ExperState[ep].exp_priv \cup
                                                                   {<<m.sender, m.channel, m.broker, m.exp_priv, ExperState[ep].sent_msg.exp>>},
                                                  ![ep].unused_exp_priv = ExperState[ep].unused_exp_priv \cup
                                                                   {<<m.sender, m.channel, m.broker, m.exp_priv, ExperState[ep].sent_msg.exp>>},
                                                  ![ep].sent_msg = req_m]
              /\ msgs' = msgs \cup {req_m}
        /\ UNCHANGED <<BOpState, EOpState, BrokerState, EndpointState, ControllerState>>

ExperNegRspReqExpPriv(ep) ==
    /\ ExperState[ep].state = "AwaitExpPrivilege"
    /\ \E m \in msgs :
        /\ m.type = "rsp_exp_priv_f"
        /\ m.receiver = ep
        /\ ExperState[ep].sent_msg.receiver = m.sender
        /\ ExperState[ep].sent_msg.seq = m.seq
        /\ ExperState' = [ExperState EXCEPT ![ep].state = "Idle",
                                            ![ep].sent_msg = empty_msg]
        /\ UNCHANGED <<BOpState, EOpState, BrokerState, EndpointState, ControllerState, msgs>>

ExperPosRspReqPubPriv(ep) ==
    /\ ExperState[ep].state = "AwaitPubPrivilege"
    /\ \E m \in msgs :
        /\ m.type = "rsp_pub_priv"
        /\ m.receiver = ep
        /\ ExperState[ep].sent_msg.receiver = m.sender
        /\ ExperState[ep].sent_msg.seq = m.seq
        /\ ExperState' = [ExperState EXCEPT ![ep].state = "Idle",
                                            ![ep].pub_priv = ExperState[ep].pub_priv \cup
                                                             {<<m.sender, ExperState[ep].sent_msg.broker>>},
                                            ![ep].unused_pub_priv = ExperState[ep].unused_pub_priv \cup
                                                             {<<m.sender, ExperState[ep].sent_msg.broker>>},
                                            ![ep].sent_msg = empty_msg]
        /\ UNCHANGED <<BOpState, EOpState, BrokerState, EndpointState, ControllerState, msgs>>

ExperNegRspReqPubPriv(ep) ==
    /\ ExperState[ep].state = "AwaitPubPrivilege"
    /\ \E m \in msgs :
        /\ m.type = "rsp_pub_priv_f"
        /\ m.receiver = ep
        /\ ExperState[ep].sent_msg.receiver = m.sender
        /\ ExperState[ep].sent_msg.seq = m.seq
        /\ ExperState' = [ExperState EXCEPT ![ep].state = "Idle",
                                            ![ep].sent_msg = empty_msg]
        /\ UNCHANGED <<BOpState, EOpState, BrokerState, EndpointState, ControllerState, msgs>>

(***************************************************************************)
(*                          Exper agent actions.                           *)
(***************************************************************************)
(***************************************************************************)
(*                          Request pub actions.                           *)
(***************************************************************************)

ExperCmdPub(ep) ==
    /\ ExperState[ep].state = "Idle"
    /\ ExperState[ep].run_targets = {}
    /\ \E pub_priv \in ExperState[ep].unused_pub_priv :
            \E exp_priv \in ExperState[ep].unused_exp_priv :
                /\ pub_priv[2] = exp_priv[3]
                /\ LET target_agent == (CHOOSE tup \in ExperOwnedController: tup[1] = ep)[2]
                       sni == (CHOOSE sni \in SNI: TRUE)
                       cmd_m == [type |-> "cmd_pub",
                                 seq |-> ExperState[ep].counter,
                                 sender |-> ep,
                                 receiver |-> target_agent,
                                 exp |-> exp_priv[5],
                                 broker |-> exp_priv[3],
                                 channel |-> exp_priv[2],
                                 sni |-> sni]
                   IN /\ ExperState' = [ExperState EXCEPT ![ep].state = "AwaitPub",
                                                          ![ep].counter = ExperState[ep].counter+1,
                                                          ![ep].sent_msg = cmd_m,
                                                          ![ep].pub_cmd =
                                                                ExperState[ep].pub_cmd \cup
                                                                {<<target_agent, exp_priv[5], exp_priv[2], exp_priv[3], sni>>},
                                                          ![ep].unused_pub_priv = ExperState[ep].unused_pub_priv \ {pub_priv},
                                                          ![ep].unused_exp_priv = ExperState[ep].unused_exp_priv \ {exp_priv}]
                      /\ msgs' = msgs \cup {cmd_m}
    /\ UNCHANGED <<BOpState, EOpState, BrokerState, EndpointState, ControllerState>>

ExperRspCmdPub(ep) ==
    /\ ExperState[ep].state = "AwaitPub"
    /\ \/ \E m \in msgs :
            /\ m.type = "ack_cmd_pub"
            /\ m.receiver = ep
            /\ ExperState[ep].sent_msg.receiver = m.sender
            /\ ExperState[ep].sent_msg.seq = m.seq
            /\ ExperState' = [ExperState EXCEPT ![ep].state = "Idle",
                                                ![ep].sent_msg = empty_msg]
            /\ UNCHANGED <<BOpState, EOpState, BrokerState, EndpointState, ControllerState, msgs>>
       \/ \E m \in msgs :
            /\ m.type = "nack_cmd_sub"
            /\ m.receiver = ep
            /\ ExperState[ep].sent_msg.receiver = m.sender
            /\ ExperState[ep].sent_msg.seq = m.seq
            /\ ExperState' = [ExperState EXCEPT ![ep].state = "Idle",
                                                ![ep].sent_msg = empty_msg,
                                                ![ep].pub_cmd =
                                                    ExperState[ep].pub_cmd \
                                                    {<<ExperState[ep].sent_msg.receiver,
                                                       ExperState[ep].sent_msg.exp,
                                                       ExperState[ep].sent_msg.channel,
                                                       ExperState[ep].sent_msg.broker,
                                                       ExperState[ep].sent_msg.sni>>}]
            /\ UNCHANGED <<BOpState, EOpState, BrokerState, EndpointState, ControllerState, msgs>>

ExperProcessReqAuthPubAgent(ep) ==
    /\ ExperState[ep].state = "AwaitPub"
    /\ \E m \in msgs :
        /\ m.type = "req_auth_pub_agent"
        /\ m.receiver = ep
        /\ UnseenSeq(ExperState[ep].track, m.sender, m.seq)
        /\ ExperState' = [ExperState EXCEPT ![ep].track = UpdatedTrackSeqSet(ExperState[ep].track, m.sender, m.seq)]
        /\ LET check1 == \E pub_priv \in ExperState[ep].pub_priv :
                            /\ pub_priv[1] = m.sender
                            /\ pub_priv[2] = m.target
               check2 == \E pub_cmd \in ExperState[ep].pub_cmd :
                            /\ pub_cmd[1] = m.origin
                            /\ pub_cmd[2] = m.exp
                            /\ pub_cmd[3] = m.channel
                            /\ pub_cmd[4] = m.target
                            /\ pub_cmd[5] = m.sni
               pos_m == [type |-> "rsp_auth_pub_agent",
                         seq |-> m.seq,
                         sender |-> ep,
                         receiver |-> m.sender]
               neg_m == [type |-> "rsp_auth_pub_agent_f",
                         seq |-> m.seq,
                         sender |-> ep,
                         receiver |-> m.sender]
           IN \/ /\ check1
                 /\ check2
                 /\ msgs' = msgs \cup {pos_m}
                 /\ UNCHANGED <<BOpState, EOpState, BrokerState, EndpointState, ControllerState>>
              \/ /\ ~check1
                 /\ msgs' = msgs \cup {neg_m}
                 /\ UNCHANGED <<BOpState, EOpState, BrokerState, EndpointState, ControllerState>>
              \/ /\ ~check2
                 /\ msgs' = msgs \cup {neg_m}
                 /\ UNCHANGED <<BOpState, EOpState, BrokerState, EndpointState, ControllerState>>

(***************************************************************************)
(*                Notify and run exp endpoint auth actions.                *)
(***************************************************************************)

ExperProcessAuthSNI(ep) ==
    /\ ExperState[ep].state = "Idle"
    /\ \E m \in msgs :
        /\ m.type = "auth_sni"
        /\ m.receiver = ep
        /\ UnseenSeq(ExperState[ep].track, m.sender, m.seq)
        /\ ExperState' = [ExperState EXCEPT ![ep].track = UpdatedTrackSeqSet(ExperState[ep].track, m.sender, m.seq)]
        /\ LET check == \E pub_cmd \in ExperState[ep].pub_cmd :
                            /\ pub_cmd[1] = m.sender
                            /\ pub_cmd[5] = m.sni
               pos_m == [type |-> "ack_sni",
                         seq |-> m.seq,
                         sender |-> ep,
                         receiver |-> m.sender]
               neg_m == [type |-> "nack_sni",
                         seq |-> m.seq,
                         sender |-> ep,
                         receiver |-> m.sender]
           IN \/ /\ check
                 /\ msgs' = msgs \cup {pos_m}
                 /\ UNCHANGED <<BOpState, EOpState, BrokerState, EndpointState, ControllerState>>
              \/ /\ ~check
                 /\ msgs' = msgs \cup {neg_m}
                 /\ UNCHANGED <<BOpState, EOpState, BrokerState, EndpointState, ControllerState>>

ExperProcessReqAuthExpAgent(ep) ==
    /\ ExperState[ep].state = "Idle"
    /\ \E m \in msgs :
        /\ m.type = "req_auth_exp_agent"
        /\ m.receiver = ep
        /\ UnseenSeq(ExperState[ep].track, m.sender, m.seq)
        /\ ExperState' = [ExperState EXCEPT ![ep].track = UpdatedTrackSeqSet(ExperState[ep].track, m.sender, m.seq)]
        /\ LET check1 == \E exp_priv \in ExperState[ep].exp_priv :
                            /\ exp_priv[1] = m.sender
                            /\ exp_priv[2] = m.channel
                            /\ exp_priv[3] = m.notifier
               check2 == \E pub_cmd \in ExperState[ep].pub_cmd :
                            /\ pub_cmd[1] = m.origin
                            /\ pub_cmd[2] = m.exp
                            /\ pub_cmd[3] = m.channel
                            /\ pub_cmd[4] = m.notifier \* note no sni checked
               pos_m == [type |-> "rsp_auth_exp_agent",
                         seq |-> m.seq,
                         sender |-> ep,
                         receiver |-> m.sender]
               neg_m == [type |-> "rsp_auth_exp_agent_f",
                         seq |-> m.seq,
                         sender |-> ep,
                         receiver |-> m.sender]
           IN \/ /\ check1
                 /\ check2
                 /\ msgs' = msgs \cup {pos_m}
                 /\ UNCHANGED <<BOpState, EOpState, BrokerState, EndpointState, ControllerState>>
              \/ /\ ~check1
                 /\ msgs' = msgs \cup {neg_m}
                 /\ UNCHANGED <<BOpState, EOpState, BrokerState, EndpointState, ControllerState>>
              \/ /\ ~check2
                 /\ msgs' = msgs \cup {neg_m}
                 /\ UNCHANGED <<BOpState, EOpState, BrokerState, EndpointState, ControllerState>>

(***************************************************************************)
(*               Notify and run exp controller auth actions.               *)
(***************************************************************************)

ExperProcessAuthHelp(ep) ==
    /\ ExperState[ep].state = "Idle"
    /\ \E m \in msgs :
        /\ m.type = "auth_help"
        /\ m.receiver = ep
        /\ <<ep, m.sender>> \in ExperOwnedController
        /\ UnseenSeq(ExperState[ep].track, m.sender, m.seq)
        /\ LET check == \E pub_cmd \in ExperState[ep].pub_cmd:
                            /\ pub_cmd[1] = m.sender
                            /\ \E exp_priv \in ExperState[ep].exp_priv:
                                    /\ exp_priv[1] = m.owner
                                    /\ exp_priv[2] = pub_cmd[3]
                                    /\ exp_priv[3] = pub_cmd[4]
               req_m == [type |-> "req_auth_help_agent",
                         seq |-> ExperState[ep].counter,
                         sender |-> ep,
                         receiver |-> m.owner,
                         helper |-> m.origin]
               neg_m == [type |-> "nack_auth_help",
                         seq |-> m.seq,
                         sender |-> ep,
                         receiver |-> m.sender]
           IN \/ /\ check
                 /\ ExperState' = [ExperState EXCEPT ![ep].state = "AwaitAuthAgentHelp",
                                                     ![ep].counter = ExperState[ep].counter+1,
                                                     ![ep].track = UpdatedTrackSeqSet(ExperState[ep].track, m.sender, m.seq),
                                                     ![ep].sent_msg = req_m,
                                                     ![ep].received_msg = m]
                 /\ msgs' = msgs \cup {req_m}
                 /\ UNCHANGED <<BOpState, EOpState, BrokerState, EndpointState, ControllerState>>
              \/ /\ ~check
                 /\ msgs' = msgs \cup {neg_m}
                 /\ ExperState' = [ExperState EXCEPT ![ep].track = UpdatedTrackSeqSet(ExperState[ep].track, m.sender, m.seq)]
                 /\ UNCHANGED <<BOpState, EOpState, BrokerState, EndpointState, ControllerState>>

ExperRspAuthHelp(ep) ==
    /\ ExperState[ep].state = "AwaitAuthAgentHelp"
    /\ \/ \E m \in msgs :
            /\ m.type = "rsp_auth_help_agent"
            /\ m.receiver = ep
            /\ ExperState[ep].sent_msg.receiver = m.sender
            /\ ExperState[ep].sent_msg.seq = m.seq
            /\ ExperState' = [ExperState EXCEPT ![ep].state = "Idle",
                                                ![ep].sent_msg = empty_msg,
                                                ![ep].received_msg = empty_msg]
            /\ LET agent == ExperState[ep].received_msg.sender
                   pos_m == [type |-> "ack_auth_help",
                             seq |-> ExperState[ep].received_msg.seq,
                             sender |-> ep,
                             receiver |-> agent,
                             exp |-> (CHOOSE pub_cmd \in ExperState[ep].pub_cmd: pub_cmd[1] = agent)[2]]
               IN /\ msgs' = msgs \cup {pos_m}
                  /\ UNCHANGED <<BOpState, EOpState, BrokerState, EndpointState, ControllerState>>
       \/ \E m \in msgs :
            /\ m.type = "rsp_auth_help_agent_f"
            /\ m.receiver = ep
            /\ ExperState[ep].sent_msg.receiver = m.sender
            /\ ExperState[ep].sent_msg.seq = m.seq
            /\ ExperState' = [ExperState EXCEPT ![ep].state = "Idle",
                                                ![ep].sent_msg = empty_msg,
                                                ![ep].received_msg = empty_msg]
            /\ LET agent == ExperState[ep].received_msg.sender
                   neg_m == [type |-> "nack_auth_help",
                             seq |-> ExperState[ep].received_msg.seq,
                             sender |-> ep,
                             receiver |-> agent]
               IN /\ msgs' = msgs \cup {neg_m}
                  /\ UNCHANGED <<BOpState, EOpState, BrokerState, EndpointState, ControllerState>>

(***************************************************************************)
(*                           Controller actions.                           *)
(***************************************************************************)
(***************************************************************************)
(*                          Request pub actions.                           *)
(***************************************************************************)

ControllerProcessCmdPub(c) ==
    /\ ControllerState[c].state = "Idle"
    /\ \E m \in msgs :
        /\ m.type = "cmd_pub"
        /\ m.receiver = c
        /\ <<m.sender, c>> \in ExperOwnedController
        /\ UnseenSeq(ControllerState[c].track, m.sender, m.seq)
        /\ LET req_m == [type |-> "req_pub",
                         seq |-> ControllerState[c].counter,
                         sender |-> c,
                         receiver |-> m.broker,
                         owner |-> m.sender,
                         exp |-> m.exp,
                         channel |-> m.channel,
                         sni |-> m.sni]
           IN /\ ControllerState' = [ControllerState EXCEPT ![c].state = "AwaitPub",
                                                            ![c].counter = ControllerState[c].counter+1,
                                                            ![c].track = UpdatedTrackSeqSet(ControllerState[c].track, m.sender, m.seq),
                                                            ![c].sent_msg = req_m,
                                                            ![c].received_msg = m]
              /\ msgs' = msgs \cup {req_m}
              /\ UNCHANGED <<BOpState, EOpState, ExperState, BrokerState, EndpointState>>

ControllerRspCmdPub(c) ==
    /\ ControllerState[c].state = "AwaitPub"
    /\ \/ \E m \in msgs :
            /\ m.type = "rsp_pub"
            /\ m.receiver = c
            /\ ControllerState[c].sent_msg.receiver = m.sender
            /\ ControllerState[c].sent_msg.seq = m.seq
            /\ ControllerState' = [ControllerState EXCEPT ![c].state = "Idle",
                                                          ![c].sent_msg = empty_msg,
                                                          ![c].received_msg = empty_msg]
            /\ LET pos_m == [type |-> "ack_cmd_pub",
                             seq |-> ControllerState[c].received_msg.seq,
                             sender |-> c,
                             receiver |-> ControllerState[c].received_msg.sender]
               IN /\ msgs' = msgs \cup {pos_m}
                  /\ UNCHANGED <<BOpState, EOpState, ExperState, BrokerState, EndpointState>>
       \/ \E m \in msgs :
            /\ m.type = "rsp_pub_f"
            /\ m.receiver = c
            /\ ControllerState[c].sent_msg.receiver = m.sender
            /\ ControllerState[c].sent_msg.seq = m.seq
            /\ ControllerState' = [ControllerState EXCEPT ![c].state = "Idle",
                                                          ![c].sent_msg = empty_msg,
                                                          ![c].received_msg = empty_msg]
            /\ LET neg_m == [type |-> "nack_cmd_sub",
                             seq |-> ControllerState[c].received_msg.seq,
                             sender |-> c,
                             receiver |-> ControllerState[c].received_msg.sender]
               IN /\ msgs' = msgs \cup {neg_m}
                  /\ UNCHANGED <<BOpState, EOpState, ExperState, BrokerState, EndpointState>>


(***************************************************************************)
(*                Notify and run exp endpoint auth actions.                *)
(***************************************************************************)

ControllerProcessConnect(c) ==
    /\ ControllerState[c].state = "Idle"
    /\ \E m \in msgs :
        /\ m.type = "connect"
        /\ m.receiver = c
        /\ UnseenSeq(ControllerState[c].track, m.sender, m.seq)
        /\ LET auth_m == [type |-> "auth_sni",
                          seq |-> ControllerState[c].counter,
                          sender |-> c,
                          receiver |-> (CHOOSE tup \in ExperOwnedController: tup[2] = c)[1],
                          sni |-> m.sni]
           IN /\ ControllerState' = [ControllerState EXCEPT ![c].state = "AwaitSNIAuth",
                                                            ![c].counter = ControllerState[c].counter+1,
                                                            ![c].track = UpdatedTrackSeqSet(ControllerState[c].track, m.sender, m.seq),
                                                            ![c].sent_msg = auth_m,
                                                            ![c].received_msg = m]
              /\ msgs' = msgs \cup {auth_m}
              /\ UNCHANGED <<BOpState, EOpState, ExperState, BrokerState, EndpointState>>

ControllerRspConnect(c) ==
    /\ ControllerState[c].state = "AwaitSNIAuth"
    /\ \/ \E m \in msgs :
            /\ m.type = "ack_sni"
            /\ m.receiver = c
            /\ ControllerState[c].sent_msg.receiver = m.sender
            /\ ControllerState[c].sent_msg.seq = m.seq
            /\ LET pos_m == [type |-> "conn_accepted",
                             seq |-> ControllerState[c].received_msg.seq,
                             sender |-> c,
                             receiver |-> ControllerState[c].received_msg.sender]
                   req_m == [type |-> "req_run_exp",
                             seq |-> ControllerState[c].counter,
                             sender |-> c,
                             receiver |-> ControllerState[c].received_msg.sender,
                             owner |-> m.sender]
               IN /\ ControllerState' = [ControllerState EXCEPT ![c].state = "AwaitRunExp",
                                                                ![c].counter = ControllerState[c].counter+1,
                                                                ![c].sent_msg = req_m,
                                                                ![c].received_msg = empty_msg]
                  /\ msgs' = msgs \cup {pos_m, req_m}
                  /\ UNCHANGED <<BOpState, EOpState, ExperState, BrokerState, EndpointState>>
       \/ \E m \in msgs :
            /\ m.type = "nack_sni"
            /\ m.receiver = c
            /\ ControllerState[c].sent_msg.receiver = m.sender
            /\ ControllerState[c].sent_msg.seq = m.seq
            /\ ControllerState' = [ControllerState EXCEPT ![c].state = "Idle",
                                                          ![c].sent_msg = empty_msg,
                                                          ![c].received_msg = empty_msg]
            /\ LET neg_m == [type |-> "conn_refused",
                             seq |-> ControllerState[c].received_msg.seq,
                             sender |-> c,
                             receiver |-> ControllerState[c].received_msg.sender]
               IN /\ msgs' = msgs \cup {neg_m}
                  /\ UNCHANGED <<BOpState, EOpState, ExperState, BrokerState, EndpointState>>

ControllerRspReqRunExp(c) ==
    /\ ControllerState[c].state = "AwaitRunExp"
    /\ \/ \E m \in msgs :
            /\ m.type = "rsp_run_exp"
            /\ m.receiver = c
            /\ ControllerState[c].sent_msg.receiver = m.sender
            /\ ControllerState[c].sent_msg.seq = m.seq
            /\ ControllerState' = [ControllerState EXCEPT ![c].state = "AwaitHelpExp", \* maintain sent_msg
                                                          ![c].received_msg = empty_msg]
            /\ UNCHANGED <<BOpState, EOpState, ExperState, BrokerState, EndpointState, msgs>>
       \/ \E m \in msgs :
            /\ m.type = "rsp_run_exp_f"
            /\ m.receiver = c
            /\ ControllerState[c].sent_msg.receiver = m.sender
            /\ ControllerState[c].sent_msg.seq = m.seq
            /\ ControllerState' = [ControllerState EXCEPT ![c].state = "Idle",
                                                          ![c].sent_msg = empty_msg,
                                                          ![c].received_msg = empty_msg]
            /\ UNCHANGED <<BOpState, EOpState, ExperState, BrokerState, EndpointState, msgs>>

(***************************************************************************)
(*               Notify and run exp controller auth actions.               *)
(***************************************************************************)

ControllerProcessReqHelpExp(c) ==
    /\ ControllerState[c].state = "AwaitHelpExp"
    /\ \E m \in msgs :
        /\ m.type = "req_help_exp"
        /\ m.receiver = c
        /\ ControllerState[c].sent_msg.receiver = m.sender
        /\ UnseenSeq(ControllerState[c].track, m.sender, m.seq)
        /\ LET auth_m == [type |-> "auth_help",
                          seq |-> ControllerState[c].counter,
                          sender |-> c,
                          receiver |-> (CHOOSE tup \in ExperOwnedController: tup[2] = c)[1],
                          owner |-> m.owner,
                          origin |-> m.sender]
           IN /\ ControllerState' = [ControllerState EXCEPT ![c].state = "AwaitHelpAuth",
                                                            ![c].counter = ControllerState[c].counter+1,
                                                            ![c].track = UpdatedTrackSeqSet(ControllerState[c].track, m.sender, m.seq),
                                                            ![c].sent_msg = auth_m,
                                                            ![c].received_msg = m]
              /\ msgs' = msgs \cup {auth_m}
              /\ UNCHANGED <<BOpState, EOpState, ExperState, BrokerState, EndpointState>>

ControllerRspReqHelpExp(c) ==
    /\ ControllerState[c].state = "AwaitHelpAuth"
    /\ \/ \E m \in msgs :
            /\ m.type = "ack_auth_help"
            /\ m.receiver = c
            /\ ControllerState[c].sent_msg.receiver = m.sender
            /\ ControllerState[c].sent_msg.seq = m.seq
            /\ ControllerState' = [ControllerState EXCEPT ![c].state = "Idle",
                                                          ![c].counter = ControllerState[c].counter+1,
                                                          ![c].sent_msg = empty_msg,
                                                          ![c].received_msg = empty_msg]
            /\ LET pos_m == [type |-> "rsp_help_exp",
                             seq |-> ControllerState[c].received_msg.seq,
                             sender |-> c,
                             receiver |-> ControllerState[c].received_msg.sender]
                   exec_m == [type |-> "exec_exp", \* exec exp at the same time
                              seq |-> ControllerState[c].counter,
                              sender |-> c,
                              receiver |-> ControllerState[c].received_msg.sender,
                              exp |-> m.exp]
               IN /\ msgs' = msgs \cup {pos_m, exec_m}
                  /\ UNCHANGED <<BOpState, EOpState, ExperState, BrokerState, EndpointState>>
       \/ \E m \in msgs :
            /\ m.type = "nack_auth_help"
            /\ m.receiver = c
            /\ ControllerState[c].sent_msg.receiver = m.sender
            /\ ControllerState[c].sent_msg.seq = m.seq
            /\ ControllerState' = [ControllerState EXCEPT ![c].state = "Idle",
                                                          ![c].sent_msg = empty_msg,
                                                          ![c].received_msg = empty_msg]
            /\ LET neg_m == [type |-> "rsp_help_exp_f",
                             seq |-> ControllerState[c].received_msg.seq,
                             sender |-> c,
                             receiver |-> ControllerState[c].received_msg.sender]
               IN /\ msgs' = msgs \cup {neg_m}
                  /\ UNCHANGED <<BOpState, EOpState, ExperState, BrokerState, EndpointState>>

(***************************************************************************)
(*                            Attacker Actions                             *)
(***************************************************************************)
(***************************************************************************)
(*                                No spoof                                 *)
(***************************************************************************)
NoSpoofAttackerInsertMsg(a) ==
    \E m \in AttackerMessages:
        /\ m.sender = a
        /\ msgs' = msgs \cup {m}
        /\ AttackerTransitionCnt' = [AttackerTransitionCnt EXCEPT ![a] = AttackerTransitionCnt[a]+1]
        /\ UNCHANGED <<BOpState, EOpState, ExperState, BrokerState, EndpointState, ControllerState>>

(***************************************************************************)
(*                                 Spoof                                   *)
(***************************************************************************)
AttackerInsertMsg(a) ==
    \E m \in AttackerMessages:
        /\ msgs' = msgs \cup {m}
        /\ AttackerTransitionCnt' = [AttackerTransitionCnt EXCEPT ![a] = AttackerTransitionCnt[a]+1]
        /\ UNCHANGED <<BOpState, EOpState, ExperState, BrokerState, EndpointState, ControllerState>>

(***************************************************************************)
(*                             Combined Next.                              *)
(***************************************************************************)
Next ==
    \/ /\ \/ \E bo \in BOp: \/ BOpPosRspReqSubPriv(bo)
                            \/ BOpNegRspReqSubPriv(bo)
                            \/ BOpPosRspReqPubPriv(bo)
                            \/ BOpNegRspReqPubPriv(bo)
                            \/ BOpProcessAuthSub(bo)
                            \/ BOpPosRspAuthSub(bo)
                            \/ BOpNegRspAuthSub(bo)
                            \/ BOpProcessAuthPub(bo)
                            \/ BOpPosRspAuthPub(bo)
                            \/ BOpNegRspAuthPub(bo)
          \/ \E eo \in EOp: \/ EOpReqSubPriv(eo)
                            \/ EOpPosRspReqSubPriv(eo)
                            \/ EOpNegRspReqSubPriv(eo)
                            \/ EOpPosRspReqExpPriv(eo)
                            \/ EOpNegRspReqExpPriv(eo)
                            \/ EOpReqSubPriv(eo)
                            \/ EOpPosRspReqSubPriv(eo)
                            \/ EOpNegRspReqSubPriv(eo)
                            \/ EOpPosRspReqExpPriv(eo)
                            \/ EOpNegRspReqExpPriv(eo)
                            \/ EOpCmdSub(eo)
                            \/ EOpPosRspCmdSub(eo)
                            \/ EOpNegRspCmdSub(eo)
                            \/ EOpProcessReqAuthSubAgent(eo)
                            \/ EOpProcessAuthNotify(eo)
                            \/ EOpProcessAuthExp(eo)
                            \/ EOpPosRspAuthExp(eo)
                            \/ EOpNegRspAuthExp(eo)
                            \/ EOpProcessReqAuthHelpAgent(eo)
          \/ \E ep \in Exper: \/ ExperReqExpPriv(ep)
                              \/ ExperPosRspReqExpPriv(ep)
                              \/ ExperNegRspReqExpPriv(ep)
                              \/ ExperPosRspReqPubPriv(ep)
                              \/ ExperNegRspReqPubPriv(ep)
                              \/ ExperReqExpPriv(ep)
                              \/ ExperPosRspReqExpPriv(ep)
                              \/ ExperNegRspReqExpPriv(ep)
                              \/ ExperPosRspReqPubPriv(ep)
                              \/ ExperNegRspReqPubPriv(ep)
                              \/ ExperCmdPub(ep)
                              \/ ExperRspCmdPub(ep)
                              \/ ExperProcessReqAuthPubAgent(ep)
                              \/ ExperProcessAuthSNI(ep)
                              \/ ExperProcessReqAuthExpAgent(ep)
                              \/ ExperProcessAuthHelp(ep)
                              \/ ExperRspAuthHelp(ep)
          \/ \E b \in Broker: \/ BrokerProcessReqSub(b)
                              \/ BrokerPosRspReqSub(b)
                              \/ BrokerNegRspReqSub(b)
                              \/ BrokerProcessReqPub(b)
                              \/ BrokerPosRspReqPub(b)
                              \/ BrokerNegRspReqPub(b)
                              \/ BrokerNotifyExp(b)
          \/ \E e \in Endpoint: \/ EndpointProcessCmdSub(e)
                                \/ EndpointPosRspCmdSub(e)
                                \/ EndpointNegRspCmdSub(e)
                                \/ EndpointProcessNotifyExp(e)
                                \/ EndpointDecideConnect(e)
                                \/ EndpointRspConnect(e)
                                \/ EndpointProcessReqRunExp(e)
                                \/ EndpointRspReqRunExp(e)
                                \/ EndpointRspReqHelpExp(e)
                                \/ EndpointExecExp(e)
          \/ \E c \in Controller: \/ ControllerProcessCmdPub(c)
                                  \/ ControllerRspCmdPub(c)
                                  \/ ControllerProcessConnect(c)
                                  \/ ControllerRspConnect(c)
                                  \/ ControllerRspReqRunExp(c)
                                  \/ ControllerProcessReqHelpExp(c)
                                  \/ ControllerRspReqHelpExp(c)
       /\ UNCHANGED <<AttackerTransitionCnt>>
    \/ \E a \in Attacker:
        /\ NoSpoofAttackerInsertMsg(a) \*AttackerInsertMsg(a)
        /\ AttackerTransitionCnt[a] < MaxAttackerTransitionCnt

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(***************************************************************************)
(*                               Invariants.                               *)
(***************************************************************************)

ExperExpPrivOnlyIfEOpGranted ==
    \A ep \in Exper, eo \in EOp:
        /\ \E tup \in ExperState[ep].exp_priv: tup[1] = eo
        => <<eo, ep>> \in EOpAllowedExper

ExperPubPrivOnlyIfBOpGranted ==
    \A ep \in Exper, bo \in BOp:
        /\ \E tup \in ExperState[ep].pub_priv: tup[1] = bo
        => <<bo, ep>> \in BOpAllowedExper

ExperNeverHasExpPriv == \* for showing error
    \A ep \in Exper: ExperState[ep].exp_priv = {}

ExperNeverHasPubPriv == \* for showing error
    \A ep \in Exper: ExperState[ep].pub_priv = {}

DebugNoAuthSNI ==
    ~(\E msg \in msgs: msg.type = "auth_sni")

DebugNeverExecute ==
    \A e \in Endpoint: EndpointState[e].executed_exp = {}

\* Actual properties to check
Soundness ==
    \A e \in Endpoint:
        \A exp_tup \in EndpointState[e].executed_exp:
            \E eo \in EOp:
                /\ <<eo, e>> \in EOpOwnedEndpoint                   \* Endpoint ownership
                /\ <<eo, exp_tup[2]>> \in EOpAllowedExp             \* EOp allow specific exp to be run on owned endpoints
                /\ \E ep \in Exper:
                    /\ <<ep, exp_tup[1]>> \in ExperOwnedController  \* Controller ownership
                    /\ <<eo, ep>> \in EOpAllowedExper               \* EOp allow Exper to run stuff on owned endpoints
                    /\ \E experintent \in ExperIntention:
                        /\ experintent[1] = ep
                        /\ <<eo, exp_tup[2]>> \in experintent[2]    \* Exper intention to run exp with endpoints of EOp

Completeness ==
    \A ep \in Exper:
        \A eo \in EOp:
            /\ <<eo, ep>> \in EOpAllowedExper                                               \* EOp allow Exper to run stuff on owned endpoints
            /\ \E experintent \in ExperIntention:
                /\ experintent[1] = ep
                /\ \E intenttup \in experintent[2]:
                    /\ intenttup[1] = eo                                                    \* Exper intention to run some exp with endpoints of EOp
                    /\ <<eo, intenttup[2]>> \in EOpAllowedExp                               \* EOp allow "some" exp to be run on owned endpoints
                    /\ <> \E e \in Endpoint:
                            \E c \in Controller:
                                /\ <<c, intenttup[2]>> \in EndpointState[e].executed_exp    \* Some exp executed
                                /\ <<eo, e>> \in EOpOwnedEndpoint                           \* Endpoint ownership
                                /\ <<ep, c>> \in ExperOwnedController                       \* Controller ownership

=============================================================================
\* Modification History
\* Last modified Sun Dec 05 22:56:09 CST 2021 by User
\* Created Tue Oct 26 10:39:47 CDT 2021 by User
