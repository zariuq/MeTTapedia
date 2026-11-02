import Mettapedia.GSLT.Parsing.ClassAwareChartDemandCompleteness
import Mettapedia.GSLT.Parsing.ClassAwareChartPruning

/-! Indexed execution of root-directed chart closure. The finite checks and
source completeness theorem are unchanged by cursor indexing or hashing. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.ClassAwareChartDemand

open ClassAwarePackedForest ClassAwarePackedForestSaturation
open ClassAwareParserPackCorrespondence ClassAwareParserPackEnumeration ParserProfileSemantics
open ClassAwareNativeForestQualification

def indexedBodyRequests (index : ClassAwareChartIndex.Index) (profile : ParserProfileLayer) (input : List Nat) :
    List PackItem → Nat → List Request
  | [], _ => []
  | .terminal matcher :: rest, cursor =>
    match terminalMatch? profile input matcher cursor with
    | none => []
    | some (middle, _) => indexedBodyRequests index profile input rest middle
  | .nonterminal sort :: rest, cursor =>
    (sort, cursor) :: ((ClassAwareChartIndex.lookup index sort cursor).flatMap
      fun key => indexedBodyRequests index profile input rest key.stop)

theorem indexedBodyRequests_exact (keys : List NodeKey) (bound : Nat)
    (profile : ParserProfileLayer) (input : List Nat) (body : List PackItem) (start : Nat) :
    indexedBodyRequests (ClassAwareChartIndex.build keys bound) profile input body start =
      bodyRequests keys profile input body start := by
  induction body generalizing start with
  | nil => rfl
  | cons item rest ih =>
    cases item with
    | terminal matcher =>
      simp only [indexedBodyRequests, bodyRequests]
      cases terminalMatch? profile input matcher start with
      | none => rfl
      | some result => cases result; simp only [ih]
    | nonterminal sort => simp only [indexedBodyRequests, bodyRequests, ClassAwareChartIndex.lookup_build, ih]

def indexedRequests (profile : ParserProfileLayer) (plan : CompiledParserPackPlan)
    (input : List Nat) (state : State) : List Request :=
  let index := ClassAwareChartIndex.build (ClassAwareChartIndex.recognizedKeys (forest state)) input.length
  state.requests.flatMap fun request =>
    plan.structural.flatMap fun production =>
      if production.resultSort == request.1 then indexedBodyRequests index profile input production.items request.2 else []

theorem indexedRequests_exact (profile : ParserProfileLayer) (plan : CompiledParserPackPlan)
    (input : List Nat) (state : State) :
    indexedRequests profile plan input state = expectedRequests profile plan input state := by
  simp only [indexedRequests, expectedRequests, ClassAwareChartIndex.recognizedKeys_exact, indexedBodyRequests_exact]

def indexedStructural (profile : ParserProfileLayer) (plan : CompiledParserPackPlan)
    (input : List Nat) (state : State) : List Family :=
  let index := ClassAwareChartIndex.build (ClassAwareChartIndex.recognizedKeys (forest state)) input.length
  state.requests.flatMap fun request =>
    (List.finRange plan.structural.length).flatMap fun position =>
      let production := plan.structural.get position
      if production.resultSort == request.1 then
        (ClassAwareChartIndex.items index profile input production.items request.2).map fun body =>
          ⟨⟨production.resultSort, request.2, body.stop⟩, .structural position.val, body.children⟩
      else []

theorem indexedStructural_exact (profile : ParserProfileLayer) (plan : CompiledParserPackPlan)
    (input : List Nat) (state : State) :
    indexedStructural profile plan input state = expectedStructural profile plan input state := by
  simp only [indexedStructural, expectedStructural, ClassAwareChartIndex.recognizedKeys_exact, ClassAwareChartIndex.items_exact]

def step (profile : ParserProfileLayer) (plan : CompiledParserPackPlan)
    (input : List Nat) (state : State) : State := {
  requests := Mettapedia.Util.LinearHash.eraseDupsFast
    ((plan.lexical.startSort, 0) :: (state.requests ++ indexedRequests profile plan input state))
  families := Mettapedia.Util.LinearHash.eraseDupsFast
    (state.families ++ expectedLexical profile plan input state ++ indexedStructural profile plan input state) }

theorem fixed_saturated {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} {state : State} (fixed : step profile plan input state = state) :
    Saturated profile plan input state := by
  have requests := congrArg State.requests fixed
  have families := congrArg State.families fixed
  constructor
  · rw [← requests]
    simp [step, Mettapedia.Util.LinearHash.eraseDupsFast_eq]
  · intro request member
    rw [← requests]
    simp only [step, Mettapedia.Util.LinearHash.eraseDupsFast_eq, indexedRequests_exact,
      List.mem_eraseDups, List.mem_cons, List.mem_append]
    exact Or.inr (Or.inr member)
  · intro family member
    rw [← families]
    simp only [step, Mettapedia.Util.LinearHash.eraseDupsFast_eq, List.mem_eraseDups, List.mem_append]
    exact Or.inl (Or.inr member)
  · intro family member
    rw [← families]
    simp only [step, Mettapedia.Util.LinearHash.eraseDupsFast_eq, indexedStructural_exact,
      List.mem_eraseDups, List.mem_append]
    exact Or.inr member

def finish? (profile : ParserProfileLayer) (plan : CompiledParserPackPlan) (input : List Nat) :
    Nat → State → Option Forest
  | 0, _ => none
  | rounds + 1, state =>
    let next := step profile plan input state
    if next == state then
      ClassAwareChartPruning.prune? (ClassAwareChartClosure.recognizedForest plan input state.families)
    else finish? profile plan input rounds next

theorem finish?_complete {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} (rounds : Nat) (state : State) (result : Forest)
    (finished : finish? profile plan input rounds state = some result) :
    RootParserComplete result profile plan input := by
  induction rounds generalizing state with
  | zero => cases finished
  | succ rounds ih =>
    simp only [finish?] at finished
    split at finished
    · rename_i fixed
      exact ClassAwareChartPruning.prune?_complete
        ((fixed_saturated (by simpa only [beq_iff_eq] using fixed)).root_complete) finished
    · exact ih _ finished

def reference? (profile : ParserProfileLayer) (plan : CompiledParserPackPlan) (input : List Nat)
    (rounds : Nat) : Option Forest := finish? profile plan input rounds ⟨[], []⟩

theorem reference?_complete {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} {rounds : Nat} {result : Forest}
    (finished : reference? profile plan input rounds = some result) :
    RootParserComplete result profile plan input := finish?_complete rounds ⟨[], []⟩ result finished

end Mettapedia.GSLT.Parsing.ClassAwareChartDemand
