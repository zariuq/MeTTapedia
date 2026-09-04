import Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.TypedFrontier

/-!
# Typed graph frontier transitions

Tree refinement introduces a fresh constructor at every hole.  Graph
refinement additionally permits a hole to reuse an existing node, which is
the operation that creates sharing and cycles.  The two operations are kept
distinct and both are checked against the expected result sort.

Whether a particular reuse edge is admissible is supplied as a source-derived
edge judgment.  Acyclic, guarded-recursive, linear, and reflective languages
therefore instantiate the same transition with different judgments rather
than selecting decoder-wide feature switches.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.TypedGraphFrontier

open Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.TypedFrontier

universe uSort uHead

abbrev Signature := TypedFrontier.Signature

/-- An open graph port.  `owner = none` denotes the root result port. -/
structure Port (signature : Signature) where
  owner : Option Nat
  expected : signature.SortType

/-- One closed typed edge from a formerly open port to a graph node. -/
structure Edge (signature : Signature) where
  port : Port signature
  target : Nat

/-- Finite graph construction state.  Nodes below `nextNode` may be defined;
all node identities at or above it are reserved for future introduction. -/
structure State (signature : Signature) where
  nodeSort : Nat → Option signature.SortType
  nextNode : Nat
  holes : List (Port signature)
  edges : List (Edge signature)
  remaining : Nat

/-- Introduce a fresh constructor node or close a port by reusing a node that
already exists in the partial graph. -/
inductive Action (signature : Signature) where
  | introduce (holeIndex : Nat) (head : signature.Head)
  | reuse (holeIndex target : Nat)

namespace Signature

variable (signature : Signature)

def childPorts (owner : Nat) (head : signature.Head) :
    List (Port signature) :=
  (signature.childSorts head).map fun sort =>
    { owner := some owner, expected := sort }

def introduceHoles (state : State signature) (holeIndex owner : Nat)
    (head : signature.Head) : List (Port signature) :=
  state.holes.take holeIndex ++ signature.childPorts owner head ++
    state.holes.drop (holeIndex + 1)

def reuseHoles (state : State signature) (holeIndex : Nat) :
    List (Port signature) :=
  state.holes.take holeIndex ++ state.holes.drop (holeIndex + 1)

/-- Lower bound on the actions needed to close the typed frontier. -/
def required (sortCost : signature.SortType → Nat)
    (holes : List (Port signature)) : Nat :=
  (holes.map fun port => sortCost port.expected).sum

/-- A source-derived decision for whether a reuse edge is semantically
admissible.  This is an edge judgment, not a language-mode flag. -/
abbrev ReuseJudgment := State signature → Port signature → Nat → Bool

/-- The state installed by a successful fresh-node action. -/
def introduceState
    (state : State signature) (port : Port signature) (holeIndex : Nat)
    (head : signature.Head) : State signature :=
  { nodeSort := Function.update state.nodeSort state.nextNode
      (some (signature.resultSort head))
    nextNode := state.nextNode + 1
    holes := signature.introduceHoles state holeIndex state.nextNode head
    edges := { port := port, target := state.nextNode } :: state.edges
    remaining := state.remaining - 1 }

/-- The state installed by a successful existing-node reuse action. -/
def reuseState (state : State signature) (port : Port signature)
    (holeIndex target : Nat) : State signature :=
  { state with
    holes := signature.reuseHoles state holeIndex
    edges := { port := port, target := target } :: state.edges
    remaining := state.remaining - 1 }

/-- Exact graph-layer legality exposed to the policy. -/
def Legal (sortCost : signature.SortType → Nat)
    (mayReuse : signature.ReuseJudgment)
    (state : State signature) : Action signature → Prop
  | .introduce holeIndex head =>
      ∃ port,
        state.holes[holeIndex]? = some port ∧
        signature.resultSort head = port.expected ∧
        state.nodeSort state.nextNode = none ∧
        1 + signature.required sortCost
          (signature.introduceHoles state holeIndex state.nextNode head) ≤
            state.remaining
  | .reuse holeIndex target =>
      ∃ port,
        state.holes[holeIndex]? = some port ∧
        state.nodeSort target = some port.expected ∧
        mayReuse state port target = true ∧
        1 + signature.required sortCost
          (signature.reuseHoles state holeIndex) ≤ state.remaining

/-- Checker-owned graph transition. -/
def refine? [DecidableEq signature.SortType]
    (sortCost : signature.SortType → Nat)
    (mayReuse : signature.ReuseJudgment)
    (state : State signature) (action : Action signature) :
    Option (State signature) :=
  match action with
  | .introduce holeIndex head =>
      match state.holes[holeIndex]? with
      | none => none
      | some port =>
          if signature.resultSort head = port.expected &&
              (state.nodeSort state.nextNode).isNone then
            let holes := signature.introduceHoles state holeIndex
              state.nextNode head
            if 1 + signature.required sortCost holes ≤ state.remaining then
              some (signature.introduceState state port holeIndex head)
            else none
          else none
  | .reuse holeIndex target =>
      match state.holes[holeIndex]? with
      | none => none
      | some port =>
          if state.nodeSort target = some port.expected &&
              mayReuse state port target then
            let holes := signature.reuseHoles state holeIndex
            if 1 + signature.required sortCost holes ≤ state.remaining then
              some (signature.reuseState state port holeIndex target)
            else none
          else none

theorem refine?_isSome_iff_legal [DecidableEq signature.SortType]
    (sortCost : signature.SortType → Nat)
    (mayReuse : signature.ReuseJudgment)
    (state : State signature) (action : Action signature) :
    (∃ next, signature.refine? sortCost mayReuse state action = some next) ↔
      signature.Legal sortCost mayReuse state action := by
  cases action with
  | introduce holeIndex head =>
      simp only [refine?, Legal]
      cases lookup : state.holes[holeIndex]? with
      | none => simp
      | some port =>
          by_cases sortMatches : signature.resultSort head = port.expected
          · by_cases fresh : state.nodeSort state.nextNode = none
            · simp only [sortMatches, fresh, Option.isNone_none]
              by_cases budgetFits :
                  1 + signature.required sortCost
                    (signature.introduceHoles state holeIndex state.nextNode
                      head) ≤ state.remaining
              · simp [budgetFits]
              · simp [budgetFits]
            · have notNone : (state.nodeSort state.nextNode).isNone = false := by
                cases value : state.nodeSort state.nextNode with
                | none => exact (fresh value).elim
                | some value => rfl
              simp [sortMatches, notNone, fresh]
          · simp [sortMatches]
  | reuse holeIndex target =>
      simp only [refine?, Legal]
      cases lookup : state.holes[holeIndex]? with
      | none => simp
      | some port =>
          by_cases sortMatches : state.nodeSort target = some port.expected
          · by_cases reuseAllowed : mayReuse state port target = true
            · simp only [sortMatches, reuseAllowed]
              by_cases budgetFits :
                  1 + signature.required sortCost
                    (signature.reuseHoles state holeIndex) ≤ state.remaining
              · simp [budgetFits, reuseAllowed]
              · simp [budgetFits]
            · have denied : mayReuse state port target = false :=
                Bool.eq_false_of_not_eq_true reuseAllowed
              simp [sortMatches, denied]
          · simp [sortMatches]

/-- All installed edges agree with the synthesized sort of their targets. -/
def EdgesTyped (state : State signature) : Prop :=
  ∀ edge ∈ state.edges,
    state.nodeSort edge.target = some edge.port.expected

/-- Every unallocated node identity is absent from the node table. -/
def UnusedFrom (state : State signature) : Prop :=
  ∀ node, state.nextNode ≤ node → state.nodeSort node = none

/-- The graph invariant needed by subsequent typed refinements. -/
def WellTyped (state : State signature) : Prop :=
  signature.EdgesTyped state ∧ signature.UnusedFrom state

/-- Every allocated node identity below the frontier has a synthesized sort. -/
def AllocatedBelow (state : State signature) : Prop :=
  ∀ node, node < state.nextNode → ∃ sort, state.nodeSort node = some sort

/-- Every owned open port and installed edge points back to an allocated node
identity.  Root ports have no owner. -/
def OwnersWithin (state : State signature) : Prop :=
  (∀ port ∈ state.holes, ∀ owner,
      port.owner = some owner → owner < state.nextNode) ∧
  (∀ edge ∈ state.edges, ∀ owner,
      edge.port.owner = some owner → owner < state.nextNode)

/-- Full typed-graph invariant: typed targets, exact node allocation frontier,
and defined source owners. -/
def FullyWellTyped (state : State signature) : Prop :=
  signature.WellTyped state ∧
    signature.AllocatedBelow state ∧
    signature.OwnersWithin state

private theorem mem_of_mem_take {α : Type*} {value : α}
    {values : List α} {count : Nat} (member : value ∈ values.take count) :
    value ∈ values := by
  induction values generalizing count with
  | nil => simp at member
  | cons head tail inductionHypothesis =>
      cases count with
      | zero => simp at member
      | succ count =>
          simp only [List.take_succ_cons, List.mem_cons] at member
          rcases member with equality | tailMember
          · subst value
            exact List.mem_cons_self
          · exact List.mem_cons_of_mem head
              (inductionHypothesis tailMember)

private theorem mem_of_mem_drop {α : Type*} {value : α}
    {values : List α} {count : Nat} (member : value ∈ values.drop count) :
    value ∈ values := by
  induction values generalizing count with
  | nil => simp at member
  | cons head tail inductionHypothesis =>
      cases count with
      | zero => exact member
      | succ count =>
          simp only [List.drop_succ_cons] at member
          exact List.mem_cons_of_mem head (inductionHypothesis member)

private theorem update_preserves_old_node
    (state : State signature) (newSort : signature.SortType) (oldNode : Nat)
    (unused : signature.UnusedFrom state)
    (present : ∃ sort, state.nodeSort oldNode = some sort) :
    Function.update state.nodeSort state.nextNode
      (some newSort) oldNode = state.nodeSort oldNode := by
  by_cases equality : oldNode = state.nextNode
  · subst oldNode
    rcases present with ⟨sort, present⟩
    have absent := unused state.nextNode (Nat.le_refl _)
    rw [absent] at present
    contradiction
  · simp [Function.update, equality]

/-- Installing a fresh node preserves the global edge-typing and freshness
invariant. -/
theorem introduceState_wellTyped
    (state : State signature) (port : Port signature) (holeIndex : Nat)
    (head : signature.Head)
    (wellTyped : signature.WellTyped state)
    (sortMatches : signature.resultSort head = port.expected) :
    signature.WellTyped
      (signature.introduceState state port holeIndex head) := by
  constructor
  · intro edge member
    simp only [introduceState, List.mem_cons] at member ⊢
    rcases member with equality | oldMember
    · subst edge
      simp [Function.update, sortMatches]
    · have oldTyped := wellTyped.1 edge oldMember
      have unchanged := signature.update_preserves_old_node state
        (signature.resultSort head) edge.target wellTyped.2
        ⟨edge.port.expected, oldTyped⟩
      rw [unchanged]
      exact oldTyped
  · intro node lower
    change state.nextNode + 1 ≤ node at lower
    have distinct : node ≠ state.nextNode := by omega
    have oldUnused : state.nodeSort node = none :=
      wellTyped.2 node (by omega)
    change Function.update state.nodeSort state.nextNode
      (some (signature.resultSort head)) node = none
    simp [Function.update, distinct, oldUnused]

/-- Reusing an existing node preserves the global invariant exactly when the
selected target has the port's expected sort. -/
theorem reuseState_wellTyped
    (state : State signature) (port : Port signature)
    (holeIndex target : Nat)
    (wellTyped : signature.WellTyped state)
    (targetTyped : state.nodeSort target = some port.expected) :
    signature.WellTyped
      (signature.reuseState state port holeIndex target) := by
  constructor
  · intro edge member
    simp only [reuseState, List.mem_cons] at member ⊢
    rcases member with equality | oldMember
    · subst edge
      exact targetTyped
    · exact wellTyped.1 edge oldMember
  · exact wellTyped.2

/-- A successful fresh-node transition exposes the exact checked port and
installed state. -/
theorem refine?_introduce_some
    [DecidableEq signature.SortType]
    (sortCost : signature.SortType → Nat)
    (mayReuse : signature.ReuseJudgment)
    (state next : State signature) (holeIndex : Nat)
    (head : signature.Head)
    (refined : signature.refine? sortCost mayReuse state
      (.introduce holeIndex head) = some next) :
    ∃ port,
      state.holes[holeIndex]? = some port ∧
      signature.resultSort head = port.expected ∧
      state.nodeSort state.nextNode = none ∧
      1 + signature.required sortCost
        (signature.introduceHoles state holeIndex state.nextNode head) ≤
          state.remaining ∧
      next = signature.introduceState state port holeIndex head := by
  have legal : signature.Legal sortCost mayReuse state
      (.introduce holeIndex head) :=
    (signature.refine?_isSome_iff_legal sortCost mayReuse state
      (.introduce holeIndex head)).mp ⟨next, refined⟩
  rcases legal with ⟨port, lookup, sortMatches, fresh, budgetFits⟩
  refine ⟨port, lookup, sortMatches, fresh, budgetFits, ?_⟩
  unfold refine? at refined
  simp [lookup, sortMatches, fresh, budgetFits] at refined
  exact refined.symm

/-- A successful reuse transition exposes the exact typed target and installed
state. -/
theorem refine?_reuse_some
    [DecidableEq signature.SortType]
    (sortCost : signature.SortType → Nat)
    (mayReuse : signature.ReuseJudgment)
    (state next : State signature) (holeIndex target : Nat)
    (refined : signature.refine? sortCost mayReuse state
      (.reuse holeIndex target) = some next) :
    ∃ port,
      state.holes[holeIndex]? = some port ∧
      state.nodeSort target = some port.expected ∧
      mayReuse state port target = true ∧
      1 + signature.required sortCost
        (signature.reuseHoles state holeIndex) ≤ state.remaining ∧
      next = signature.reuseState state port holeIndex target := by
  have legal : signature.Legal sortCost mayReuse state
      (.reuse holeIndex target) :=
    (signature.refine?_isSome_iff_legal sortCost mayReuse state
      (.reuse holeIndex target)).mp ⟨next, refined⟩
  rcases legal with ⟨port, lookup, targetTyped, allowed, budgetFits⟩
  refine ⟨port, lookup, targetTyped, allowed, budgetFits, ?_⟩
  unfold refine? at refined
  simp [lookup, targetTyped, allowed, budgetFits] at refined
  exact refined.symm

/-- Every checker-admitted graph action preserves global edge typing. -/
theorem refine?_preserves_wellTyped
    [DecidableEq signature.SortType]
    (sortCost : signature.SortType → Nat)
    (mayReuse : signature.ReuseJudgment)
    (state next : State signature) (action : Action signature)
    (wellTyped : signature.WellTyped state)
    (refined : signature.refine? sortCost mayReuse state action = some next) :
    signature.WellTyped next := by
  cases action with
  | introduce holeIndex head =>
      rcases signature.refine?_introduce_some sortCost mayReuse state next
        holeIndex head refined with
        ⟨port, _lookup, sortMatches, _fresh, _budget, nextEquality⟩
      rw [nextEquality]
      exact signature.introduceState_wellTyped state port holeIndex head
        wellTyped sortMatches
  | reuse holeIndex target =>
      rcases signature.refine?_reuse_some sortCost mayReuse state next
        holeIndex target refined with
        ⟨port, _lookup, targetTyped, _allowed, _budget, nextEquality⟩
      rw [nextEquality]
      exact signature.reuseState_wellTyped state port holeIndex target
        wellTyped targetTyped

/-- Fresh-node installation preserves the complete graph invariant when the
selected port really belongs to the current frontier. -/
theorem introduceState_fullyWellTyped
    (state : State signature) (port : Port signature) (holeIndex : Nat)
    (head : signature.Head)
    (fullyTyped : signature.FullyWellTyped state)
    (portMember : port ∈ state.holes)
    (sortMatches : signature.resultSort head = port.expected) :
    signature.FullyWellTyped
      (signature.introduceState state port holeIndex head) := by
  refine ⟨signature.introduceState_wellTyped state port holeIndex head
    fullyTyped.1 sortMatches, ?_, ?_⟩
  · intro node lower
    change node < state.nextNode + 1 at lower
    by_cases newest : node = state.nextNode
    · subst node
      exact ⟨signature.resultSort head, by
        simp [introduceState, Function.update]⟩
    · have oldLower : node < state.nextNode := by omega
      rcases fullyTyped.2.1 node oldLower with ⟨sort, present⟩
      refine ⟨sort, ?_⟩
      change Function.update state.nodeSort state.nextNode
        (some (signature.resultSort head)) node = some sort
      simpa [Function.update, newest] using present
  · constructor
    · intro candidate member owner ownerEq
      change candidate ∈
        signature.introduceHoles state holeIndex state.nextNode head at member
      simp only [introduceHoles, List.mem_append] at member
      rcases member with prefixOrChild | suffixMember
      · rcases prefixOrChild with prefixMember | childMember
        · have oldMember : candidate ∈ state.holes :=
            mem_of_mem_take prefixMember
          have oldBound := fullyTyped.2.2.1 candidate oldMember owner ownerEq
          change owner < state.nextNode + 1
          omega
        · simp only [childPorts, List.mem_map] at childMember
          rcases childMember with ⟨sort, _sortMember, equality⟩
          subst candidate
          simp only [Option.some.injEq] at ownerEq
          subst owner
          change state.nextNode < state.nextNode + 1
          omega
      · have oldMember : candidate ∈ state.holes :=
          mem_of_mem_drop suffixMember
        have oldBound := fullyTyped.2.2.1 candidate oldMember owner ownerEq
        change owner < state.nextNode + 1
        omega
    · intro edge member owner ownerEq
      simp only [introduceState, List.mem_cons] at member
      rcases member with equality | oldMember
      · subst edge
        have oldBound := fullyTyped.2.2.1 port portMember owner ownerEq
        change owner < state.nextNode + 1
        omega
      · have oldBound := fullyTyped.2.2.2 edge oldMember owner ownerEq
        change owner < state.nextNode + 1
        omega

/-- Existing-node reuse preserves the complete graph invariant. -/
theorem reuseState_fullyWellTyped
    (state : State signature) (port : Port signature)
    (holeIndex target : Nat)
    (fullyTyped : signature.FullyWellTyped state)
    (portMember : port ∈ state.holes)
    (targetTyped : state.nodeSort target = some port.expected) :
    signature.FullyWellTyped
      (signature.reuseState state port holeIndex target) := by
  refine ⟨signature.reuseState_wellTyped state port holeIndex target
    fullyTyped.1 targetTyped, fullyTyped.2.1, ?_⟩
  constructor
  · intro candidate member owner ownerEq
    change candidate ∈ signature.reuseHoles state holeIndex at member
    simp only [reuseHoles, List.mem_append] at member
    rcases member with prefixMember | suffixMember
    · exact fullyTyped.2.2.1 candidate
        (mem_of_mem_take prefixMember) owner ownerEq
    · exact fullyTyped.2.2.1 candidate
        (mem_of_mem_drop suffixMember) owner ownerEq
  · intro edge member owner ownerEq
    simp only [reuseState, List.mem_cons] at member
    rcases member with equality | oldMember
    · subst edge
      exact fullyTyped.2.2.1 port portMember owner ownerEq
    · exact fullyTyped.2.2.2 edge oldMember owner ownerEq

/-- Every checker-admitted action preserves the full typed graph invariant,
including ownership of all dependency edges. -/
theorem refine?_preserves_fullyWellTyped
    [DecidableEq signature.SortType]
    (sortCost : signature.SortType → Nat)
    (mayReuse : signature.ReuseJudgment)
    (state next : State signature) (action : Action signature)
    (fullyTyped : signature.FullyWellTyped state)
    (refined : signature.refine? sortCost mayReuse state action = some next) :
    signature.FullyWellTyped next := by
  cases action with
  | introduce holeIndex head =>
      rcases signature.refine?_introduce_some sortCost mayReuse state next
        holeIndex head refined with
        ⟨port, lookup, sortMatches, _fresh, _budget, nextEquality⟩
      rw [nextEquality]
      exact signature.introduceState_fullyWellTyped state port holeIndex head
        fullyTyped (List.mem_of_getElem? lookup) sortMatches
  | reuse holeIndex target =>
      rcases signature.refine?_reuse_some sortCost mayReuse state next
        holeIndex target refined with
        ⟨port, lookup, targetTyped, _allowed, _budget, nextEquality⟩
      rw [nextEquality]
      exact signature.reuseState_fullyWellTyped state port holeIndex target
        fullyTyped (List.mem_of_getElem? lookup) targetTyped

end Signature

/-! ## Sharing, cycle, and rejection controls -/

private inductive FixtureSort where
  | expr
  | nat
  deriving DecidableEq

private inductive FixtureHead where
  | literal
  deriving DecidableEq

private abbrev fixtureSignature : Signature where
  SortType := FixtureSort
  Head := FixtureHead
  resultSort := fun _ => .expr
  childSorts := fun _ => []

private def fixtureNodeSort : Nat → Option FixtureSort
  | 0 => some .expr
  | _ => none

private def rootPort : Port fixtureSignature :=
  { owner := none, expected := .expr }

private def selfPort : Port fixtureSignature :=
  { owner := some 0, expected := .expr }

private def baseState (port : Port fixtureSignature) :
    State fixtureSignature :=
  { nodeSort := fixtureNodeSort
    nextNode := 1
    holes := [port]
    edges := []
    remaining := 1 }

private def unitCost : FixtureSort → Nat := fun _ => 1

private def unrestrictedReuse : fixtureSignature.ReuseJudgment :=
  fun _state _port _target => true

private def noSelfReuse : fixtureSignature.ReuseJudgment :=
  fun _state port target => decide (port.owner ≠ some target)

theorem baseState_wellTyped (port : Port fixtureSignature) :
    fixtureSignature.WellTyped (baseState port) := by
  constructor
  · simp [Signature.EdgesTyped, baseState]
  · intro node lower
    simp only [baseState] at lower ⊢
    cases node with
    | zero => omega
    | succ node => rfl

theorem baseState_fullyWellTyped (port : Port fixtureSignature)
    (ownerBound : ∀ owner, port.owner = some owner → owner < 1) :
    fixtureSignature.FullyWellTyped (baseState port) := by
  refine ⟨baseState_wellTyped port, ?_, ?_⟩
  · intro node lower
    change node < 1 at lower
    have equality : node = 0 := by omega
    subst node
    exact ⟨.expr, rfl⟩
  · constructor
    · intro candidate member owner ownerEq
      simp only [baseState, List.mem_singleton] at member
      subst candidate
      exact ownerBound owner ownerEq
    · simp [baseState]

/-- Reusing an existing result at a root port is a lawful sharing edge. -/
theorem typed_sharing_edge_is_legal :
    fixtureSignature.Legal unitCost unrestrictedReuse (baseState rootPort)
      (.reuse 0 0) := by
  exact ⟨rootPort, rfl, rfl, rfl, by decide⟩

/-- The same graph operation can close a back-edge when the authored reuse
judgment admits it. -/
theorem typed_self_cycle_is_legal_when_source_admits :
    fixtureSignature.Legal unitCost unrestrictedReuse (baseState selfPort)
      (.reuse 0 0) := by
  exact ⟨selfPort, rfl, rfl, rfl, by decide⟩

/-- A source-derived guardedness judgment can reject the self-cycle without
changing the generic graph decoder. -/
theorem typed_self_cycle_is_rejected_by_guarded_judgment :
    ¬ fixtureSignature.Legal unitCost noSelfReuse (baseState selfPort)
      (.reuse 0 0) := by
  simp [Signature.Legal, noSelfReuse, baseState, selfPort]

private def wrongSortState : State fixtureSignature :=
  { nodeSort := fun
      | 0 => some .nat
      | _ => none
    nextNode := 1
    holes := [rootPort]
    edges := []
    remaining := 1 }

/-- Edge policy approval cannot override a target-sort mismatch. -/
theorem wrong_sort_reuse_is_rejected :
    ¬ fixtureSignature.Legal unitCost unrestrictedReuse wrongSortState
      (.reuse 0 0) := by
  simp [Signature.Legal, wrongSortState, rootPort]

/-- The concrete sharing transition preserves the global typing invariant. -/
theorem typed_sharing_transition_wellTyped :
    fixtureSignature.WellTyped
      (fixtureSignature.reuseState (baseState rootPort) rootPort 0 0) :=
  fixtureSignature.reuseState_wellTyped (baseState rootPort) rootPort 0 0
    (baseState_wellTyped rootPort) rfl

/-- The same sharing transition preserves source ownership as well as target
typing. -/
theorem typed_sharing_transition_fullyWellTyped :
    fixtureSignature.FullyWellTyped
      (fixtureSignature.reuseState (baseState rootPort) rootPort 0 0) :=
  fixtureSignature.reuseState_fullyWellTyped
    (baseState rootPort) rootPort 0 0
    (baseState_fullyWellTyped rootPort (by simp [rootPort]))
    (by simp [baseState]) rfl

#print axioms Signature.refine?_isSome_iff_legal
#print axioms Signature.introduceState_wellTyped
#print axioms Signature.reuseState_wellTyped
#print axioms Signature.refine?_introduce_some
#print axioms Signature.refine?_reuse_some
#print axioms Signature.refine?_preserves_wellTyped
#print axioms Signature.introduceState_fullyWellTyped
#print axioms Signature.reuseState_fullyWellTyped
#print axioms Signature.refine?_preserves_fullyWellTyped
#print axioms typed_sharing_edge_is_legal
#print axioms typed_self_cycle_is_legal_when_source_admits
#print axioms typed_self_cycle_is_rejected_by_guarded_judgment
#print axioms wrong_sort_reuse_is_rejected
#print axioms typed_sharing_transition_wellTyped
#print axioms typed_sharing_transition_fullyWellTyped

end Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.TypedGraphFrontier
