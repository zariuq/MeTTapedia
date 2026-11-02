import Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangChannel
import Mettapedia.OSLF.MeTTaIL.ReferenceStepAgreement
import Mettapedia.OSLF.MeTTaIL.MatchSpec

/-! Arbitrary queue enqueue and head-delivery paths through the actual
authored rules. Payloads are parameters, not source syntax trees. The
network transfer theorem joins the independent per-channel FIFO judgment to
this operational component; the full actor scheduler remains separate. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangChannel.Execution

open Mettapedia.OSLF.MeTTaIL Syntax Match MatchSpec ContextualStep
open ReflectiveCanonical ReflectiveSubstitution
open ErlangMailbox (node values mailbox)
open Mettapedia.Languages.Erlang

private theorem root_step (base : BasePremiseEvaluator) (index : Nat)
    (bound : index < language.rewrites.length) (bindings : Bindings) (source target : Pattern)
    (noPremises : language.rewrites[index].premises = [])
    (aligned : ruleDepthAligned language.rewrites[index] = true)
    (matched : bindings ∈ matchPattern language.rewrites[index].left source)
    (applied : applyBindings bindings language.rewrites[index].right = target) :
    ContextualStep.Step base language source target := by
  refine ⟨1, StepAt.rule (rule := language.rewrites[index])
    (initialBindings := bindings) (finalBindings := bindings) (List.getElem_mem _) ?_ ?_ ?_⟩
  · simpa only [matchPatternForRule_eq_syntactic] using matched
  · rw [noPremises]
    exact .nil bindings
  · rw [applyBindingsForRule_eq_syntactic,
      applyRuleBindings_eq_applyBindings _ _ aligned]
    exact applied

theorem send_step (base : BasePremiseEvaluator) (sender receiver message queue : Pattern) :
    ContextualStep.Step base language
      (node "ErChannelSend" [sender, receiver, message, queue])
      (node "ErChannelAppend" [sender, receiver, message, node "ErValuesNil", queue]) := by
  let bs : Bindings := [("receiver", receiver), ("queue", queue), ("message", message), ("sender", sender)]
  refine root_step base 14 (by decide_cbv) bs _ _ (by decide_cbv) (by decide_cbv) ?_ ?_
  · change bs ∈ matchPattern (.apply "ErChannelSend"
      [.fvar "sender", .fvar "receiver", .fvar "message", .fvar "queue"]) _
    simp [bs, node, matchPattern, matchArgs, mergeBindings]
  · change applyBindings bs (.apply "ErChannelAppend"
      [.fvar "sender", .fvar "receiver", .fvar "message", .apply "ErValuesNil" [], .fvar "queue"]) = _
    simp [bs, applyBindings, node]

theorem append_more (base : BasePremiseEvaluator) (sender receiver message reversed head tail : Pattern) :
    ContextualStep.Step base language
      (node "ErChannelAppend" [sender, receiver, message, reversed, node "ErValuesCons" [head, tail]])
      (node "ErChannelAppend" [sender, receiver, message, node "ErValuesCons" [head, reversed], tail]) := by
  let bs : Bindings := [("receiver", receiver), ("reversed", reversed), ("tail", tail), ("head", head), ("message", message), ("sender", sender)]
  refine root_step base 15 (by decide_cbv) bs _ _ (by decide_cbv) (by decide_cbv) ?_ ?_
  · change bs ∈ matchPattern (.apply "ErChannelAppend"
      [.fvar "sender", .fvar "receiver", .fvar "message", .fvar "reversed",
       .apply "ErValuesCons" [.fvar "head", .fvar "tail"]]) _
    simp [bs, node, matchPattern, matchArgs, mergeBindings]
  · change applyBindings bs (.apply "ErChannelAppend"
      [.fvar "sender", .fvar "receiver", .fvar "message", .apply "ErValuesCons" [.fvar "head", .fvar "reversed"],
       .fvar "tail"]) = _
    simp [bs, applyBindings, node]

theorem append_done (base : BasePremiseEvaluator) (sender receiver message reversed : Pattern) :
    ContextualStep.Step base language
      (node "ErChannelAppend" [sender, receiver, message, reversed, node "ErValuesNil"])
      (node "ErChannelRestore" [sender, receiver, reversed, node "ErValuesCons" [message, node "ErValuesNil"]]) := by
  let bs : Bindings := [("receiver", receiver), ("reversed", reversed), ("message", message), ("sender", sender)]
  refine root_step base 16 (by decide_cbv) bs _ _ (by decide_cbv) (by decide_cbv) ?_ ?_
  · change bs ∈ matchPattern (.apply "ErChannelAppend"
      [.fvar "sender", .fvar "receiver", .fvar "message", .fvar "reversed", .apply "ErValuesNil" []]) _
    simp [bs, node, matchPattern, matchArgs, mergeBindings]
  · change applyBindings bs (.apply "ErChannelRestore"
      [.fvar "sender", .fvar "receiver", .fvar "reversed",
       .apply "ErValuesCons" [.fvar "message", .apply "ErValuesNil" []]]) = _
    simp [bs, applyBindings, node]

theorem restore_more (base : BasePremiseEvaluator) (sender receiver head tail queue : Pattern) :
    ContextualStep.Step base language
      (node "ErChannelRestore" [sender, receiver, node "ErValuesCons" [head, tail], queue])
      (node "ErChannelRestore" [sender, receiver, tail, node "ErValuesCons" [head, queue]]) := by
  let bs : Bindings := [("receiver", receiver), ("queue", queue), ("tail", tail), ("head", head), ("sender", sender)]
  refine root_step base 17 (by decide_cbv) bs _ _ (by decide_cbv) (by decide_cbv) ?_ ?_
  · change bs ∈ matchPattern (.apply "ErChannelRestore"
      [.fvar "sender", .fvar "receiver", .apply "ErValuesCons" [.fvar "head", .fvar "tail"], .fvar "queue"]) _
    simp [bs, node, matchPattern, matchArgs, mergeBindings]
  · change applyBindings bs (.apply "ErChannelRestore"
      [.fvar "sender", .fvar "receiver", .fvar "tail", .apply "ErValuesCons" [.fvar "head", .fvar "queue"]]) = _
    simp [bs, applyBindings, node]

theorem restore_done (base : BasePremiseEvaluator) (sender receiver queue : Pattern) :
    ContextualStep.Step base language (node "ErChannelRestore" [sender, receiver, node "ErValuesNil", queue])
      (node "ErChannelQueued" [sender, receiver, queue]) := by
  let bs : Bindings := [("receiver", receiver), ("queue", queue), ("sender", sender)]
  refine root_step base 18 (by decide_cbv) bs _ _ (by decide_cbv) (by decide_cbv) ?_ ?_
  · change bs ∈ matchPattern (.apply "ErChannelRestore"
      [.fvar "sender", .fvar "receiver", .apply "ErValuesNil" [], .fvar "queue"]) _
    simp [bs, node, matchPattern, matchArgs, mergeBindings]
  · change applyBindings bs (.apply "ErChannelQueued" [.fvar "sender", .fvar "receiver", .fvar "queue"]) = _
    simp [bs, applyBindings, node]

theorem deliver_step (base : BasePremiseEvaluator) (sender receiver head tail saved front rear : Pattern) :
    ContextualStep.Step base language
      (node "ErChannelDeliver" [sender, receiver, node "ErValuesCons" [head, tail],
        node "ErMailbox" [saved, front, rear]])
      (node "ErChannelArrived" [sender, receiver, head, tail,
        node "ErMailbox" [saved, front, node "ErValuesCons" [head, rear]]]) := by
  let bs : Bindings := [("receiver", receiver), ("saved", saved), ("rear", rear), ("front", front), ("tail", tail), ("head", head), ("sender", sender)]
  refine root_step base 19 (by decide_cbv) bs _ _ (by decide_cbv) (by decide_cbv) ?_ ?_
  · change bs ∈ matchPattern (.apply "ErChannelDeliver"
      [.fvar "sender", .fvar "receiver", .apply "ErValuesCons" [.fvar "head", .fvar "tail"],
       .apply "ErMailbox" [.fvar "saved", .fvar "front", .fvar "rear"]]) _
    simp [bs, node, matchPattern, matchArgs, mergeBindings]
  · change applyBindings bs (.apply "ErChannelArrived"
      [.fvar "sender", .fvar "receiver", .fvar "head", .fvar "tail",
       .apply "ErMailbox" [.fvar "saved", .fvar "front", .apply "ErValuesCons" [.fvar "head", .fvar "rear"]]]) = _
    simp [bs, applyBindings, node]

abbrev Path (base : BasePremiseEvaluator) := Relation.ReflTransGen (ContextualStep.Step base language)

theorem restore_path (base : BasePremiseEvaluator) (sender receiver : Pattern) (reversed queue : List Pattern) :
    Path base (node "ErChannelRestore" [sender, receiver, values reversed, values queue])
      (node "ErChannelQueued" [sender, receiver, values (reversed.reverse ++ queue)]) := by
  induction reversed generalizing queue with
  | nil => exact .single (restore_done base sender receiver (values queue))
  | cons head tail ih =>
      have path := (Relation.ReflTransGen.single
        (restore_more base sender receiver head (values tail) (values queue))).trans (ih (head :: queue))
      simpa only [values, List.reverse_cons, List.append_assoc, List.singleton_append] using path

theorem append_path (base : BasePremiseEvaluator) (sender receiver message : Pattern)
    (reversed todo : List Pattern) :
    Path base (node "ErChannelAppend" [sender, receiver, message, values reversed, values todo])
      (node "ErChannelQueued" [sender, receiver, values (reversed.reverse ++ todo ++ [message])]) := by
  induction todo generalizing reversed with
  | nil =>
      have rest : Path base
          (node "ErChannelRestore" [sender, receiver, values reversed, node "ErValuesCons" [message, node "ErValuesNil"]])
          (node "ErChannelQueued" [sender, receiver, values (reversed.reverse ++ [message])]) := by
        simpa only [values] using restore_path base sender receiver reversed [message]
      simpa only [values, List.append_nil] using
        (Relation.ReflTransGen.single (append_done base sender receiver message (values reversed))).trans rest
  | cons head tail ih =>
      have path := (Relation.ReflTransGen.single
        (append_more base sender receiver message (values reversed) head (values tail))).trans (ih (head :: reversed))
      simpa only [values, List.reverse_cons, List.append_assoc, List.singleton_append] using path

theorem send_path (base : BasePremiseEvaluator) (sender receiver message : Pattern) (queue : List Pattern) :
    Path base (node "ErChannelSend" [sender, receiver, message, values queue])
      (node "ErChannelQueued" [sender, receiver, values (queue ++ [message])]) :=
  (Relation.ReflTransGen.single (send_step base sender receiver message (values queue))).trans
    (append_path base sender receiver message [] queue)

theorem aligned : ReferenceStep.ReferenceProfile language := by
  intro rule member
  have checked : language.rewrites.all ReferenceStep.ruleAligned = true := by decide_cbv
  exact List.all_eq_true.mp checked rule member

private def deliveryRule : RewriteRule := language.rewrites[19]'(by decide_cbv)

private def deliveryCandidate (rule : RewriteRule) : Bool := match rule.left with
  | .apply label _ => decide (label = "ErChannelDeliver")
  | _ => true

private theorem only_delivery_rule {rule : RewriteRule} {bindings : Bindings} {fields : List Pattern}
    (member : rule ∈ language.rewrites)
    (matched : bindings ∈ matchPattern rule.left (.apply "ErChannelDeliver" fields)) :
    rule = deliveryRule := by
  have candidates : language.rewrites.filter deliveryCandidate = [deliveryRule] := by rfl
  have possible : deliveryCandidate rule = true := by
    cases left : rule.left <;> simp only [deliveryCandidate, left]
    rename_i label arguments
    by_cases same : label = "ErChannelDeliver"
    · simp [same]
    · simp [left, matchPattern, same] at matched
  have selected := List.mem_filter.mpr ⟨member, possible⟩
  rw [candidates] at selected
  exact List.mem_singleton.mp selected

/-- A target step from a channel-delivery request cannot invent a payload,
drop the channel tail, or change the receiver's earlier mailbox contents. -/
theorem delivery_readback (base : BasePremiseEvaluator) (sender receiver queue box target : Pattern)
    (step : ContextualStep.Step base language (node "ErChannelDeliver" [sender, receiver, queue, box]) target) :
    ∃ head tail saved front rear,
      queue = node "ErValuesCons" [head, tail] ∧ box = node "ErMailbox" [saved, front, rear] ∧
      target = node "ErChannelArrived" [sender, receiver, head, tail,
        node "ErMailbox" [saved, front, node "ErValuesCons" [head, rear]]] := by
  obtain ⟨_, firing⟩ := step
  cases firing with
  | @rule _ _ _ _ initial final member matched premises applied =>
      rw [matchPatternForRule_eq_syntactic] at matched
      have row := only_delivery_rule member matched
      subst row
      have empty : deliveryRule.premises = [] := by rfl
      rw [empty] at premises
      cases premises
      have reconstructed := matchPattern_correct matched (show isMatchCorrectAux deliveryRule.left = true by decide_cbv)
      rw [applyBindingsForRule_eq_syntactic,
        applyRuleBindings_eq_applyBindings _ _ (show ruleDepthAligned deliveryRule = true by decide_cbv)] at applied
      have left : deliveryRule.left = .apply "ErChannelDeliver"
          [.fvar "sender", .fvar "receiver", .apply "ErValuesCons" [.fvar "head", .fvar "tail"],
            .apply "ErMailbox" [.fvar "saved", .fvar "front", .fvar "rear"]] := by rfl
      have right : deliveryRule.right = .apply "ErChannelArrived"
          [.fvar "sender", .fvar "receiver", .fvar "head", .fvar "tail",
            .apply "ErMailbox" [.fvar "saved", .fvar "front", .apply "ErValuesCons" [.fvar "head", .fvar "rear"]]] := by rfl
      rw [left] at reconstructed
      rw [right] at applied
      simp only [applyBindings, List.map_cons, List.map_nil] at reconstructed applied
      let capture := fun name => match initial.find? (fun entry => entry.1 == name) with
        | some (_, value) => value
        | none => Pattern.fvar name
      change node "ErChannelDeliver" [capture "sender", capture "receiver",
        node "ErValuesCons" [capture "head", capture "tail"],
        node "ErMailbox" [capture "saved", capture "front", capture "rear"]] =
        node "ErChannelDeliver" [sender, receiver, queue, box] at reconstructed
      change node "ErChannelArrived" [capture "sender", capture "receiver", capture "head", capture "tail",
        node "ErMailbox" [capture "saved", capture "front", node "ErValuesCons" [capture "head", capture "rear"]]] =
        target at applied
      have fields := (Pattern.apply.inj reconstructed).2
      obtain ⟨sameSender, fields⟩ := List.cons.inj fields
      obtain ⟨sameReceiver, fields⟩ := List.cons.inj fields
      obtain ⟨sameQueue, fields⟩ := List.cons.inj fields
      obtain ⟨sameBox, _⟩ := List.cons.inj fields
      refine ⟨capture "head", capture "tail", capture "saved", capture "front", capture "rear",
        sameQueue.symm, sameBox.symm, ?_⟩
      simpa only [sameSender, sameReceiver] using applied.symm

theorem empty_channel_no_step (base : BasePremiseEvaluator) (sender receiver box target : Pattern) :
    ¬ ContextualStep.Step base language
      (node "ErChannelDeliver" [sender, receiver, node "ErValuesNil", box]) target := by
  intro step
  obtain ⟨head, tail, saved, front, rear, impossible, _⟩ :=
    delivery_readback base sender receiver (node "ErValuesNil") box target step
  have tags := (Pattern.apply.inj impossible).1
  exact (by decide : "ErValuesNil" ≠ "ErValuesCons") tags

theorem delivery_iff (base : BasePremiseEvaluator) (sender receiver queue box target : Pattern) :
    ContextualStep.Step base language (node "ErChannelDeliver" [sender, receiver, queue, box]) target ↔
      ∃ head tail saved front rear,
        queue = node "ErValuesCons" [head, tail] ∧ box = node "ErMailbox" [saved, front, rear] ∧
        target = node "ErChannelArrived" [sender, receiver, head, tail,
          node "ErMailbox" [saved, front, node "ErValuesCons" [head, rear]]] := by
  constructor
  · exact delivery_readback base sender receiver queue box target
  · rintro ⟨head, tail, saved, front, rear, rfl, rfl, rfl⟩
    exact deliver_step base sender receiver head tail saved front rear

theorem reference_delivery_iff (relEnv : Engine.RelationEnv) (sender receiver queue box target : Pattern) :
    ReferenceStep.Step relEnv language (node "ErChannelDeliver" [sender, receiver, queue, box]) target ↔
      ∃ head tail saved front rear,
        queue = node "ErValuesCons" [head, tail] ∧ box = node "ErMailbox" [saved, front, rear] ∧
        target = node "ErChannelArrived" [sender, receiver, head, tail,
          node "ErMailbox" [saved, front, node "ErValuesCons" [head, rear]]] := by
  rw [← ReferenceStep.contextualStep_iff_step relEnv language aligned]
  exact delivery_iff (engineBasePremises relEnv) sender receiver queue box target

theorem reference_path (relEnv : Engine.RelationEnv) {source target : Pattern} (path : Path (engineBasePremises relEnv) source target) :
    Relation.ReflTransGen (ReferenceStep.Step relEnv language) source target := by
  induction path with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail ((ReferenceStep.contextualStep_iff_step relEnv language aligned).mp step)

/-- Every admitted source channel transfer has the corresponding authored
head-delivery step, including the exact residual channel and mailbox. -/
theorem network_delivery {α : Type*} (encode : α → Pattern) (relEnv : Engine.RelationEnv)
    {network rest : List (Envelope α)} {message : Envelope α}
    (delivered : Network.Delivers network message rest) (box : Mailbox α) :
    ReferenceStep.Step relEnv language
      (node "ErChannelDeliver" [pid message.key.sender, pid message.key.receiver,
        values ((Network.channel message.key network).map encode), mailbox encode box])
      (node "ErChannelArrived" [pid message.key.sender, pid message.key.receiver, encode message.payload,
        values ((Network.channel message.key rest).map encode), mailbox encode (box.deliver message.payload)]) := by
  rw [Network.delivered_channel_head delivered]
  apply (ReferenceStep.contextualStep_iff_step relEnv language aligned).mp
  simpa only [List.map_cons, values, mailbox, Mailbox.deliver] using
    deliver_step (engineBasePremises relEnv) (pid message.key.sender) (pid message.key.receiver)
      (encode message.payload) (values ((Network.channel message.key rest).map encode))
      (values (box.savedRev.map encode)) (values (box.front.map encode)) (values (box.rearRev.map encode))

theorem network_send {α : Type*} (encode : α → Pattern) (relEnv : Engine.RelationEnv)
    (network : List (Envelope α)) (message : Envelope α) :
    Relation.ReflTransGen (ReferenceStep.Step relEnv language)
      (node "ErChannelSend" [pid message.key.sender, pid message.key.receiver, encode message.payload,
        values ((Network.channel message.key network).map encode)])
      (node "ErChannelQueued" [pid message.key.sender, pid message.key.receiver,
        values ((Network.channel message.key (Network.send message network)).map encode)]) := by
  rw [Network.channel_send]
  simp only [ite_true, List.map_append, List.map_cons, List.map_nil]
  exact reference_path relEnv (send_path (engineBasePremises relEnv) _ _ _ _)

end Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangChannel.Execution
