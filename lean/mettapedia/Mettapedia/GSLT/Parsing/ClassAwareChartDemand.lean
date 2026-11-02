import Mettapedia.GSLT.Parsing.ClassAwareChartIndex

/-! Root-directed ParserPack chart obligations. Recursive calls are requested
only after their preceding items have been recognized. A requested child is
never omitted merely because the following suffix has not yet succeeded. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.ClassAwareChartDemand

open ClassAwarePackedForest ClassAwarePackedForestSaturation
open ClassAwareParserPackCorrespondence ClassAwareParserPackEnumeration ParserProfileSemantics

abbrev Request := String × Nat

structure State where
  requests : List Request
  families : List Family
  deriving DecidableEq, Repr

def forest (state : State) : Forest := ⟨[], state.families⟩

def bodyRequests (keys : List NodeKey) (profile : ParserProfileLayer) (input : List Nat) :
    List PackItem → Nat → List Request
  | [], _ => []
  | .terminal matcher :: rest, cursor =>
    match terminalMatch? profile input matcher cursor with
    | none => []
    | some (middle, _) => bodyRequests keys profile input rest middle
  | .nonterminal sort :: rest, cursor =>
    (sort, cursor) :: ((keys.filter fun key => key.resultSort == sort && key.start == cursor).flatMap
      fun key => bodyRequests keys profile input rest key.stop)

def expectedRequests (profile : ParserProfileLayer) (plan : CompiledParserPackPlan)
    (input : List Nat) (state : State) : List Request :=
  state.requests.flatMap fun request =>
    plan.structural.flatMap fun production =>
      if production.resultSort == request.1 then
        bodyRequests (recognizedNodeKeys (forest state)) profile input production.items request.2
      else []

def expectedLexical (profile : ParserProfileLayer) (plan : CompiledParserPackPlan)
    (input : List Nat) (state : State) : List Family :=
  state.requests.flatMap fun request =>
    (List.finRange plan.lexical.productions.length).flatMap fun position =>
      let production := plan.lexical.productions.get position
      if production.resultSort == request.1 then
        match terminalMatch? profile input production.matcher request.2 with
        | none => []
        | some (stop, _) => [⟨⟨production.resultSort, request.2, stop⟩,
          .lexical position.val, [.terminal production.matcher request.2 stop]⟩]
      else []

def expectedStructural (profile : ParserProfileLayer) (plan : CompiledParserPackPlan)
    (input : List Nat) (state : State) : List Family :=
  state.requests.flatMap fun request =>
    (List.finRange plan.structural.length).flatMap fun position =>
      let production := plan.structural.get position
      if production.resultSort == request.1 then
        (enumerateRecognizedItems (forest state) profile input production.items request.2).map fun body =>
          ⟨⟨production.resultSort, request.2, body.stop⟩, .structural position.val, body.children⟩
      else []

structure Saturated (profile : ParserProfileLayer) (plan : CompiledParserPackPlan)
    (input : List Nat) (state : State) : Prop where
  root : (plan.lexical.startSort, 0) ∈ state.requests
  requests : expectedRequests profile plan input state ⊆ state.requests
  lexical : expectedLexical profile plan input state ⊆ state.families
  structural : expectedStructural profile plan input state ⊆ state.families

def validate (profile : ParserProfileLayer) (plan : CompiledParserPackPlan)
    (input : List Nat) (state : State) : Bool :=
  decide ((plan.lexical.startSort, 0) ∈ state.requests) &&
  (expectedRequests profile plan input state).all (· ∈ state.requests) &&
  (expectedLexical profile plan input state).all (· ∈ state.families) &&
  (expectedStructural profile plan input state).all (· ∈ state.families)

theorem validate_iff (profile : ParserProfileLayer) (plan : CompiledParserPackPlan)
    (input : List Nat) (state : State) : validate profile plan input state = true ↔ Saturated profile plan input state := by
  simp only [validate, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨root, requests⟩, lexical⟩, structural⟩
    exact ⟨root, fun request member => requests request member,
      fun family member => lexical family member, fun family member => structural family member⟩
  · intro valid
    exact ⟨⟨⟨valid.root, fun request member => valid.requests member⟩,
      fun family member => valid.lexical member⟩, fun family member => valid.structural member⟩

end Mettapedia.GSLT.Parsing.ClassAwareChartDemand
