/-
# Root-parametric refinement actions

This module is the small waist shared by concrete GSLT construction roots.
It contains no Gauthier operator, dependent-type constructor, or search
heuristic.  A root supplies its states, holes, actions, decoder, invariant,
and bounded completion predicate; `RefinementLaws` records exactly the local
proof obligations needed by the generic soundness, completeness, prefix, and
no-dead-end theorems below.
-/

namespace Mettapedia.GSLT.LanguageDef.RefinementInterface

universe uState uHole uAction uProgram

/-- Data exposed to a root-conditioned action policy. -/
structure RefinementInterface where
  State : Type uState
  Hole : Type uHole
  Action : Type uAction
  Program : Type uProgram
  initial : Nat → State
  holes : State → List Hole
  legal : State → Action → Prop
  apply? : State → Action → Option State
  terminal : State → Prop
  decode : List Action → Option Program
  wellFormed : Program → Prop
  programCost : Program → Nat
  encode : Program → List Action
  invariant : State → Prop
  canComplete : State → Prop
  budgetOK : Nat → Prop

namespace RefinementInterface

variable (root : RefinementInterface)

/-- Execute an ordered action trace from one refinement state. -/
def run : List root.Action → root.State → Option root.State
  | [], state => some state
  | action :: rest, state => do
      let next ← root.apply? state action
      run rest next

/-- A trace is accepted only when execution terminates and decoding agrees. -/
def Accepts (budget : Nat) (trace : List root.Action)
    (program : root.Program) : Prop :=
  ∃ finalState,
    root.run trace (root.initial budget) = some finalState ∧
      root.terminal finalState ∧
      root.decode trace = some program

/-- State reached by an actual prefix from a budgeted initial state. -/
def Reachable (budget : Nat) (state : root.State) : Prop :=
  ∃ actions, root.run actions (root.initial budget) = some state

/-- A state has an ordered legal completion to a terminal state. -/
def HasCompletion (state : root.State) : Prop :=
  ∃ suffix finalState,
    root.run suffix state = some finalState ∧ root.terminal finalState

/-- Every action occurrence in a trace is legal at its reached prefix state. -/
def EveryPrefixLegal (trace : List root.Action) (start : root.State) : Prop :=
  ∀ before action after,
    trace = before ++ action :: after →
      ∃ prefixState,
        root.run before start = some prefixState ∧
          root.legal prefixState action

/-- An external ranking lists exactly the legal actions, in an arbitrary order. -/
def ListsAllLegalActions (ranking : root.State → List root.Action) : Prop :=
  ∀ state action, action ∈ ranking state ↔ root.legal state action

/-- Every chosen action occurs in the external ranking at its reached state. -/
def EveryPrefixListed (ranking : root.State → List root.Action)
    (trace : List root.Action) (start : root.State) : Prop :=
  ∀ before action after,
    trace = before ++ action :: after →
      ∃ prefixState,
        root.run before start = some prefixState ∧
          action ∈ ranking prefixState

/-- Acceptance observed through a complete external action ranking. -/
def RankedAccepts (ranking : root.State → List root.Action)
    (budget : Nat) (trace : List root.Action) (program : root.Program) : Prop :=
  root.Accepts budget trace program ∧
    root.EveryPrefixListed ranking trace (root.initial budget)

theorem run_append (first second : List root.Action) (state : root.State) :
    root.run (first ++ second) state =
      match root.run first state with
      | none => none
      | some middle => root.run second middle := by
  induction first generalizing state with
  | nil => rfl
  | cons action rest ih =>
      simp only [List.cons_append, run]
      cases hstep : root.apply? state action with
      | none => rfl
      | some middle => exact ih middle

end RefinementInterface

/--
Per-root obligations.  The first three fields connect exposed legality, holes,
and state invariants to execution.  `sound` and `complete` are the semantic
instance obligations.  The last two fields make bounded completion exact and
turn invariant preservation into the generic no-dead-end theorem.
-/
structure RefinementLaws (root : RefinementInterface) where
  legal_iff_apply :
    ∀ state action,
      root.legal state action ↔
        ∃ next, root.apply? state action = some next
  terminal_iff_holes_empty :
    ∀ state, root.terminal state ↔ root.holes state = []
  initial_invariant :
    ∀ budget, root.budgetOK budget → root.invariant (root.initial budget)
  apply_invariant :
    ∀ {state action next},
      root.invariant state →
      root.apply? state action = some next →
      root.invariant next
  sound :
    ∀ {budget trace finalState program},
      root.run trace (root.initial budget) = some finalState →
      root.terminal finalState →
      root.decode trace = some program →
      root.wellFormed program
  complete :
    ∀ {budget program},
      root.budgetOK budget →
      root.wellFormed program →
      root.programCost program ≤ budget →
      root.Accepts budget (root.encode program) program
  invariant_canComplete :
    ∀ {state}, root.invariant state → root.canComplete state
  canComplete_iff_hasCompletion :
    ∀ state, root.canComplete state ↔ root.HasCompletion state

namespace RefinementLaws

variable {root : RefinementInterface} (laws : RefinementLaws root)
include laws

/-- Successful execution exposes policy legality at every proper prefix. -/
theorem everyPrefixLegal_of_run {trace : List root.Action}
    {start finalState : root.State}
    (hrun : root.run trace start = some finalState) :
    root.EveryPrefixLegal trace start := by
  intro before action after htrace
  rw [htrace, root.run_append] at hrun
  cases hprefix : root.run before start with
  | none =>
      rw [hprefix] at hrun
      contradiction
  | some prefixState =>
      rw [hprefix] at hrun
      simp only [RefinementInterface.run] at hrun
      cases hstep : root.apply? prefixState action with
      | none =>
          rw [hstep] at hrun
          contradiction
      | some next =>
          exact
            ⟨prefixState, rfl,
              (RefinementLaws.legal_iff_apply laws prefixState action).mpr
                ⟨next, hstep⟩⟩

/-- Any reachable state preserves the root's semantic invariant. -/
theorem invariant_of_run {actions : List root.Action}
    {start finalState : root.State}
    (hinvariant : root.invariant start)
    (hrun : root.run actions start = some finalState) :
    root.invariant finalState := by
  induction actions generalizing start finalState with
  | nil =>
      simp only [RefinementInterface.run, Option.some.injEq] at hrun
      subst finalState
      exact hinvariant
  | cons action rest ih =>
      simp only [RefinementInterface.run] at hrun
      cases hstep : root.apply? start action with
      | none =>
          rw [hstep] at hrun
          contradiction
      | some next =>
          rw [hstep] at hrun
          exact ih (RefinementLaws.apply_invariant laws hinvariant hstep) hrun

/-- Any reachable state preserves the root's semantic invariant. -/
theorem reachable_invariant {budget : Nat} (hbudget : root.budgetOK budget)
    {state : root.State} (hreachable : root.Reachable budget state) :
    root.invariant state := by
  rcases hreachable with ⟨actions, hrun⟩
  exact invariant_of_run laws
    (RefinementLaws.initial_invariant laws budget hbudget) hrun

/-- T1 soundness: every accepted trace decodes to a root-well-formed program. -/
theorem accepts_sound {budget : Nat} {trace : List root.Action}
    {program : root.Program} (haccepts : root.Accepts budget trace program) :
    root.wellFormed program := by
  rcases haccepts with ⟨finalState, hrun, hterminal, hdecode⟩
  exact RefinementLaws.sound laws hrun hterminal hdecode

/-- T1 completeness: every in-budget well-formed program has its canonical trace. -/
theorem wellFormed_reachable {budget : Nat} {program : root.Program}
    (hbudget : root.budgetOK budget)
    (hwellFormed : root.wellFormed program)
    (hcost : root.programCost program ≤ budget) :
    root.Accepts budget (root.encode program) program :=
  RefinementLaws.complete laws hbudget hwellFormed hcost

/-- Completeness includes legality at every prefix of the canonical trace. -/
theorem wellFormed_everyPrefixLegal {budget : Nat} {program : root.Program}
    (hbudget : root.budgetOK budget)
    (hwellFormed : root.wellFormed program)
    (hcost : root.programCost program ≤ budget) :
    root.EveryPrefixLegal (root.encode program) (root.initial budget) := by
  rcases RefinementLaws.complete laws hbudget hwellFormed hcost with
    ⟨finalState, hrun, _hterminal, _hdecode⟩
  exact everyPrefixLegal_of_run laws hrun

/-- T1 no-dead-ends: every reachable invariant state has a legal completion. -/
theorem reachable_hasCompletion {budget : Nat} (hbudget : root.budgetOK budget)
    {state : root.State} (hreachable : root.Reachable budget state) :
    root.HasCompletion state := by
  have hinvariant := reachable_invariant laws hbudget hreachable
  exact
    (RefinementLaws.canComplete_iff_hasCompletion laws state).mp
      (RefinementLaws.invariant_canComplete laws hinvariant)

/-- A terminal state is exactly a state with no exposed construction holes. -/
theorem terminal_iff_no_holes (state : root.State) :
    root.terminal state ↔ root.holes state = [] :=
  RefinementLaws.terminal_iff_holes_empty laws state

/-! ## Search-order independence -/

/-- A ranking with exact legal support observes precisely the accepted traces. -/
theorem rankedAccepts_iff_accepts
    (ranking : root.State → List root.Action)
    (hcoverage : root.ListsAllLegalActions ranking)
    {budget : Nat} {trace : List root.Action} {program : root.Program} :
    root.RankedAccepts ranking budget trace program ↔
      root.Accepts budget trace program := by
  constructor
  · exact fun hranked => hranked.1
  · intro haccepts
    rcases haccepts with ⟨finalState, hrun, hterminal, hdecode⟩
    refine
      ⟨⟨finalState, hrun, hterminal, hdecode⟩, ?_⟩
    intro before action after htrace
    rcases everyPrefixLegal_of_run laws hrun before action after htrace with
      ⟨prefixState, hprefix, hlegal⟩
    exact ⟨prefixState, hprefix, (hcoverage prefixState action).mpr hlegal⟩

/--
T5: permuting which legal action is tried first changes only enumeration order;
it cannot change the set of accepted completed traces.
-/
theorem rankedAcceptance_invariant_of_permutation
    (first second : root.State → List root.Action)
    (hcoverage : root.ListsAllLegalActions first)
    (hpermutation : ∀ state, (first state).Perm (second state))
    {budget : Nat} {trace : List root.Action} {program : root.Program} :
    root.RankedAccepts first budget trace program ↔
      root.RankedAccepts second budget trace program := by
  have hsecond : root.ListsAllLegalActions second := by
    intro state action
    rw [← (hpermutation state).mem_iff]
    exact hcoverage state action
  rw [rankedAccepts_iff_accepts laws first hcoverage,
    rankedAccepts_iff_accepts laws second hsecond]

end RefinementLaws

end Mettapedia.GSLT.LanguageDef.RefinementInterface
