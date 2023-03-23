(** * Piggybank contract *)
(** Proofs for Piggybank contract defined in [ConCert.Examples.piggybank.piggybank]. *)

From ConCert.Examples.PiggyBank Require Import PiggyBank.
From ConCert.Utils Require Import RecordUpdate.
From ConCert.Utils Require Import Automation.
From ConCert.Utils Require Import Extras.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import ContractCommon.
From ConCert.Execution Require Import Monad.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import ContractCommon.
From Coq Require Import List. Import ListNotations.
From Coq Require Import ZArith.
From Coq Require Import Lia.

(** A few tactics to make the proofs more manageable and more transparent *)
Tactic Notation "contract_simpl" := contract_simpl receive init.

Ltac insert_reduce prev_state ctx := 
  destruct (ctx_amount ctx <=? 0)%Z eqn:Epos; try discriminate; 
  destruct (is_smashed prev_state) eqn:Esmash; try discriminate.

Ltac smash_reduce prev_state ctx := 
  destruct (is_smashed prev_state) eqn:Esmash; try discriminate; 
  destruct (address_neqb ctx.(ctx_from) prev_state.(owner)) eqn:Eowner; try discriminate;
  destruct (negb (ctx_amount ctx =? 0)%Z) eqn:Enonzero; try discriminate.

(** ** Functional properties *)
Section FunctionalProperties.
  Context `{BaseTypes : ChainBase}.
  Open Scope Z.

  (** If insert runs then it inserts the correct amount to the correct account *)
  Lemma insert_inserts_correct (prev_state next_state : State) 
                               (ctx : ContractCallContext) 
                               (acts : list ActionBody) : 
    insert prev_state ctx = Ok (next_state, acts) ->
    acts = [] /\
    Z.add ctx.(ctx_amount) prev_state.(balance) = next_state.(balance).
  Proof.
    intros Hinsert. unfold insert in Hinsert.
    insert_reduce prev_state ctx.
    now inversion Hinsert.
  Qed.

  (** If smash runs successfully the resulting state is smashed and the amount in the PiggyBank 
      is transfered to the owner *)
  Lemma smash_transfers_correctly (prev_state next_state : State) 
                                  (ctx : ContractCallContext) 
                                  (acts : list ActionBody) : 
    smash prev_state ctx = Ok (next_state, acts) ->
    next_state.(piggyState) = Smashed /\
    next_state.(balance) = 0 /\
    acts = [act_transfer prev_state.(owner) prev_state.(balance)].
  Proof. 
    intros Hsmash. unfold smash in Hsmash. smash_reduce prev_state ctx.
    now inversion Hsmash. 
  Qed.

  Lemma receive_is_correct (chain : Chain) 
                           (ctx : ContractCallContext) 
                           (prev_state next_state : State) 
                           (msg : option Msg) 
                           (acts : list ActionBody) : 
    PiggyBank.receive chain ctx prev_state msg = Ok (next_state, acts) ->
    match msg with
      | Some Insert => acts = [] /\ Z.add ctx.(ctx_amount) prev_state.(balance) = next_state.(balance)
      | Some Smash => next_state.(piggyState) = Smashed /\ next_state.(balance) = 0 
                      /\ acts = [act_transfer prev_state.(owner) prev_state.(balance)]
      | None => False
    end.
  Proof. 
    intros Hreceive. unfold PiggyBank.receive in Hreceive. 
    destruct msg; try discriminate. 
    destruct m; 
    [apply insert_inserts_correct | apply smash_transfers_correctly with ctx]; 
    apply Hreceive.
  Qed.
End FunctionalProperties.

(** ** Safety properties *)
Section SafetyProperties.
  Context `{BaseTypes : ChainBase}.
  Open Scope Z.
  
  Open Scope program_scope.

  (** ** Outgoing acts facts *)
  (** If a contract emits self calls then they are for the receive entrypoints (which do not exits) *)
  Lemma only_getter_self_calls bstate caddr :
    reachable bstate ->
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    Forall (fun act_body =>
      match act_body with
      | act_transfer to _ => False
      | act_call to _ msg => to = caddr ->
          (msg = serialize (Insert)) \/
          (msg = serialize (Smash)) 
      | _ => False
      end) (outgoing_acts bstate caddr).
  Proof. Admitted. (*
    contract_induction; intros; auto.
    - now inversion IH.
    - apply Forall_app; split; auto.
      clear IH. simpl in *.
      destruct msg; try discriminate.
      destruct m; unfold PiggyBank.receive in receive_some;
      [unfold insert in receive_some | unfold smash in receive_some]; 
      [insert_reduce prev_state ctx | smash_reduce prev_state ctx];
      inversion receive_some; eauto.
      admit.
      
    - inversion_clear IH as [|? ? head_not_me tail_not_me].
      destruct head;
        try contradiction.
      destruct action_facts as (? & ? & ? & ?).
      subst.
      destruct head_not_me as [[] | []]; auto;
        subst;
        simpl in *;
        unfold PiggyBank.receive in receive_some;
        [unfold insert in receive_some | unfold smash in receive_some]. 
      [insert_reduce prev_state ctx | smash_reduce prev_state ctx].
      inversion receive_some; eauto.
        try now contract_simpl.
    - now rewrite <- perm.
    - solve_facts.
  Qed.*)

  (** Contract never calls itself *)
  Lemma no_self_calls : forall bstate origin from_addr to_addr amount msg acts ctx prev_state new_state resp_acts,
    reachable bstate ->
    env_contracts bstate to_addr = Some (contract : WeakContract) ->
    chain_state_queue bstate =
    {| act_origin := origin;
      act_from := from_addr;
      act_body :=
        match msg with
        | Some msg => act_call to_addr amount msg
        | None => act_transfer to_addr amount
      end |} :: acts ->
    wc_receive contract bstate ctx prev_state msg = Ok (new_state, resp_acts) ->
    from_addr <> to_addr.
  Proof.
    intros * reach deployed queue receive_some.
    apply only_getter_self_calls in deployed as no_self_calls; auto.
    unfold outgoing_acts in no_self_calls.
    rewrite queue in no_self_calls.
    cbn in no_self_calls.
    destruct_address_eq; auto.
    inversion_clear no_self_calls as [|? ? hd _].
    destruct msg; auto.
    destruct hd as [[] | []];
      auto; subst;
      eapply wc_receive_strong in receive_some as (_ & ? & _ & _ & msg_correct & _);
      destruct_match in msg_correct; auto.
      unfold Bool.reflect.
  Qed.

  (** This is already proved above and not really a safety property *)
  Lemma receive_produces_no_calls_when_running_insert (chain : Chain) 
                                                      (ctx : ContractCallContext) 
                                                      (cstate new_cstate : State) 
                                                      (msg : option Msg) 
                                                      (acts : list ActionBody) :
   msg = Some Insert ->
   PiggyBank.receive chain ctx cstate msg = Ok (new_cstate, acts) ->
   acts = [].
  Proof.
    intros ? Hreceive. subst. 
    unfold PiggyBank.receive in Hreceive. 
    now apply insert_inserts_correct in Hreceive as [<- _]. 
  Qed.
  
  (** The owner never changes between states *)
  Lemma owner_remains (chain : Chain) 
                      (ctx : ContractCallContext) 
                      (prev_state next_state : State) 
                      (msg : option Msg) 
                      (acts : list ActionBody) : 
    PiggyBank.receive chain ctx prev_state msg = Ok (next_state, acts) ->
    prev_state.(owner) = next_state.(owner).
  Proof.
    intros Hreceive. unfold PiggyBank.receive in Hreceive. destruct msg; try discriminate.
    destruct m; cbn in Hreceive; 
    [insert_reduce prev_state ctx | smash_reduce prev_state ctx]; 
    now inversion Hreceive.
  Qed.
  
  (** The owner at any state is the same as the original owner *)
  Lemma owner_correct bstate caddr (trace : ChainTrace empty_state bstate) : 
    env_contracts bstate caddr = Some (PiggyBank.contract : WeakContract) ->
    exists cstate dep,
      deployment_info Setup trace caddr = Some dep /\
      contract_state bstate caddr = Some cstate /\
      cstate.(owner) = dep.(deployment_from).
  Proof.
    contract_induction; intros; auto;
    try (specialize owner_remains with chain ctx prev_state new_state msg new_acts; 
      intros; specialize (H receive_some); rewrite H in IH; assumption).
    - cbn in init_some. unfold PiggyBank.init in init_some.
      destruct result. now inversion init_some.
    - solve_facts.
  Qed.
  
  (** When smashed the PiggyBank stays smashed *)
  Lemma stay_smashed {prev_state msg chain ctx} : 
    prev_state.(piggyState) = Smashed ->  
      exists e : Error, PiggyBank.receive chain ctx prev_state msg = Err e.
  Proof.
    intros state_smashed. unfold PiggyBank.receive.
    destruct msg, prev_state. cbn in *. rewrite state_smashed.
    - destruct m; cbn. 
      + destruct (ctx_amount ctx <=? 0); eauto.
      + eauto.
    - eauto.
  Qed.

  (** The total amount in an intact PiggyBank can only increase *)
  Lemma if_intact_then_balance_can_only_increase (prev_state next_state : State) 
                                                 (ctx : ContractCallContext) 
                                                 (chain : Chain) 
                                                 (new_acts : list ActionBody) : 
    prev_state.(piggyState) = Intact ->
    PiggyBank.receive chain ctx prev_state (Some Insert) = Ok (next_state, new_acts) ->
    Z.le prev_state.(balance) next_state.(balance).
  Proof.
    intros state_intact Hreceive. unfold PiggyBank.receive in Hreceive. 
    destruct prev_state; cbn in *; rewrite state_intact in Hreceive.
    destruct (ctx_amount ctx <=? 0) eqn:E; try discriminate. 
    inversion Hreceive; cbn; lia.
  Qed.
  
  (** initializes to correct state *)
  Lemma initializes_correctly (chain : Chain) (ctx : ContractCallContext) (setup : Setup) (new_state : State) : 
    PiggyBank.init chain ctx setup = Ok new_state ->
      new_state.(piggyState) = Intact.
  Proof.
    intros Hinit. unfold PiggyBank.init in Hinit. now inversion Hinit. 
  Qed.

  (** we need this little lemma for the next property *)
  Lemma neq_false_eq : forall x y : Z, negb (x =? y) = false <-> x = y.
  Proof. split; lia. Qed.

  (** balance in PiggyBank is correct on the blockchain *)
  Lemma balance_on_chain' : 
    forall bstate caddr (trace : ChainTrace empty_state bstate),
    let effective_balance := (env_account_balances bstate caddr - sumZ (fun act => act_body_amount act) (outgoing_acts bstate caddr))%Z in
    reachable bstate ->
    env_contracts bstate caddr = Some (PiggyBank.contract : WeakContract) ->
    exists cstate,
      contract_state bstate caddr = Some cstate /\
      effective_balance = cstate.(balance).
  Proof. 
    intros.
    subst effective_balance.
    contract_induction; intros; auto; cbn in *.
    - unfold PiggyBank.init in init_some. inversion init_some. cbn. lia.    
    - lia.
    - unfold PiggyBank.receive in receive_some.
      destruct msg; try discriminate. destruct m;
      [unfold insert in receive_some | unfold smash in receive_some]; 
      [insert_reduce prev_state ctx | smash_reduce prev_state ctx; apply neq_false_eq in Enonzero];
      inversion receive_some; cbn; lia.
    - unfold PiggyBank.receive in receive_some.
      destruct msg; try discriminate. destruct m;
      [unfold insert in receive_some | unfold smash in receive_some]; 
      [insert_reduce prev_state ctx | smash_reduce prev_state ctx; apply neq_false_eq in Enonzero];
      inversion receive_some; destruct head; cbn in *; lia.
    - now erewrite sumZ_permutation in IH by eauto.
    - solve_facts. 
  Qed. 

  Lemma balance_on_chain :
    forall bstate caddr (trace : ChainTrace empty_state bstate),
    reachable bstate ->
    env_contracts bstate caddr = Some (PiggyBank.contract : WeakContract) ->
    outgoing_acts bstate caddr = [] ->
    exists cstate,
      contract_state bstate caddr = Some cstate /\
      env_account_balances bstate caddr = cstate.(balance).
  Proof.
    intros * trace reach deployed.
    specialize balance_on_chain' as (cstate & balance); eauto.
    intros Hact. rewrite Hact in balance. cbn in *.
    now exists cstate. 
  Qed.

  Lemma no_outgoing_actions_when_intact :
    forall bstate caddr (trace : ChainTrace empty_state bstate),
    reachable bstate ->
    env_contracts bstate caddr = Some (PiggyBank.contract : WeakContract) ->
    exists cstate,
      contract_state bstate caddr = Some cstate /\
      (cstate.(piggyState) = Intact -> outgoing_acts bstate caddr = []).
  Proof.
    intros * trace reach deployed.
    contract_induction; intros; auto.
    - now specialize (IH H). 
    - cbn in *. unfold PiggyBank.receive in receive_some.
      destruct msg; try discriminate. destruct m;
      [unfold insert in receive_some | unfold smash in receive_some];
      [insert_reduce prev_state ctx | smash_reduce prev_state ctx];
      inversion receive_some.
      + unfold is_smashed in Esmash. intuition.
      + destruct new_state. inversion H1. rewrite <- H5 in H. discriminate H.
    - instantiate (CallFacts := fun _ ctx prev_state queue _ =>
      ctx_from ctx <> ctx_contract_address ctx).
      now destruct fact.
    - specialize (IH H). rewrite IH in perm. now eapply Permutation.Permutation_nil in perm.
    - solve_facts.
      rewrite deployed in *;
      match goal with
        | H : Some ?x = Some _ |- _ => inversion H; subst x; clear H
      end. 
      eapply no_self_calls; eauto.
      now constructor.
  Qed.

  (** When the PiggyBank is smashed its balance needs to remain zero *)    
  Lemma balance_is_zero_when_smashed' : 
    forall bstate caddr (trace : ChainTrace empty_state bstate),
    let effective_balance := (env_account_balances bstate caddr - sumZ (fun act => act_body_amount act) (outgoing_acts bstate caddr))%Z in
    reachable bstate ->
    env_contracts bstate caddr = Some (PiggyBank.contract : WeakContract) ->
    exists cstate,
      contract_state bstate caddr = Some cstate /\
      (cstate.(piggyState) = Smashed -> effective_balance = 0).
  Proof. 
    intros.
    subst effective_balance.
    contract_induction; intros; auto; cbn in *.
    - unfold PiggyBank.init in init_some. inversion init_some. 
      destruct result. inversion H1. rewrite <- H4 in H. discriminate H.
    - specialize (IH H). lia.
    - unfold PiggyBank.receive in receive_some.
      destruct msg; try discriminate. destruct m;
      [unfold insert in receive_some | unfold smash in receive_some];
      [insert_reduce prev_state ctx | smash_reduce prev_state ctx];
      inversion receive_some.
      + unfold is_smashed in Esmash. destruct prev_state, new_state.
        inversion H1. cbn in *. intuition.
      + instantiate (CallFacts := fun _ ctx prev_state queue _ =>
        (prev_state.(piggyState) = Intact -> ctx_contract_balance ctx = balance prev_state) /\ 
        (prev_state.(piggyState) = Intact -> queue = [])
        /\ ctx_from ctx <> ctx_contract_address ctx).
        destruct facts as [Hamount [Hqueue _]].
        unfold is_smashed in Esmash. destruct prev_state.(piggyState) eqn:Estate; try discriminate. 
        rewrite Hqueue, Hamount; try reflexivity. cbn. lia.
    - now destruct facts.
    - now erewrite sumZ_permutation in IH by eauto.
    - solve_facts.
      repeat split; rewrite deployed in *;
      match goal with
        | H : Some ?x = Some _ |- _ => inversion H; subst x; clear H
      end.
      + specialize balance_on_chain' as (state1 & construct1 & balance); eauto.
        now constructor.
        intros state_intact. rewrite address_eq_refl. 
        specialize no_outgoing_actions_when_intact as (state2 & [construct2 act]); eauto; try now constructor.
        unfold contract_state in *.
        destruct (env_contract_states bstate_from to_addr); try discriminate. 
        inversion construct1 as [some_s_is_state1]. inversion construct2 as [some_s_is_state2].
        rewrite deployed_state0 in *. 
        inversion some_s_is_state1 as [cstate_is_state1]. inversion some_s_is_state2 as [cstate_is_state2]. 
        rewrite <- cstate_is_state2 in act.
        specialize (act state_intact). rewrite act in balance. rewrite <- balance. cbn.
        destruct (to_addr =? from_addr)%address eqn:addr.
        * lia.
        * admit.

      + specialize no_outgoing_actions_when_intact as (? & ?); eauto.
        * now constructor.
        * destruct H.   
      + eapply no_self_calls; eauto.
        now constructor.
  Qed.

  Lemma balance_is_zero_when_smashed : 
    forall bstate caddr (trace : ChainTrace empty_state bstate),
    reachable bstate ->
    env_contracts bstate caddr = Some (PiggyBank.contract : WeakContract) ->
    outgoing_acts bstate caddr = [] ->
    exists cstate,
      contract_state bstate caddr = Some cstate /\
      (cstate.(piggyState) = Smashed ->
      (env_account_balances bstate caddr = 0)%Z).
  Proof.
    intros * trace reach deployed act.
    specialize balance_is_zero_when_smashed' as (cstate & deploy & balance); eauto.
    rewrite act in balance. cbn in *.
    exists cstate. intuition. 
  Qed.
End SafetyProperties.