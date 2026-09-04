import Mathlib.Tactic
import Mettapedia.GSLT.LanguageDef.RefinementInterface

/-!
# Prefix properties for typed and semantic decoding

An output-validity percentage conflates several different contracts.  This
module names the contracts at the generic refinement waist and proves only the
implications that are valid for every decoder.  Small finite countermodels
separate the invalid implications.

The definitions are intentionally independent of a particular traversal or
guest language.  A later GSLT-derived root can therefore state exactly which
prefix theorem it supplies without changing the neural policy interface.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.PrefixProperties

open Mettapedia.GSLT.LanguageDef.RefinementInterface

universe uState uHole uAction uProgram

variable {root : RefinementInterface}

/-- A prefix executes from the budgeted initial state.  This is a structural
property; it does not assert that the prefix can reach an accepted program. -/
def ExecutablePrefix (root : RefinementInterface) (budget : Nat)
    (pre : List root.Action) : Prop :=
  ∃ state, root.run pre (root.initial budget) = some state

/-- A prefix has a suffix whose complete trace is accepted and decoded. -/
def AcceptedPrefix (root : RefinementInterface) (budget : Nat)
    (pre : List root.Action) : Prop :=
  ∃ suffix program, root.Accepts budget (pre ++ suffix) program

/-- Every accepted output satisfies the authored terminal judgment. -/
def AcceptanceSoundAt (root : RefinementInterface) (budget : Nat) : Prop :=
  ∀ {trace program}, root.Accepts budget trace program → root.wellFormed program

/-- Every in-budget admitted program is reached by its canonical encoding. -/
def CanonicalCompleteAt (root : RefinementInterface) (budget : Nat) : Prop :=
  ∀ program, root.wellFormed program → root.programCost program ≤ budget →
    root.Accepts budget (root.encode program) program

/-- Every prefix of an admitted program's canonical encoding executes. -/
def CanonicalPrefixesPreservedAt (root : RefinementInterface)
    (budget : Nat) : Prop :=
  ∀ program, root.wellFormed program → root.programCost program ≤ budget →
    ∀ before after, root.encode program = before ++ after →
      ExecutablePrefix root budget before

/-- Every reachable state has a terminal state completion.  Terminality alone
does not imply successful decoding. -/
def StateProductiveAt (root : RefinementInterface) (budget : Nat) : Prop :=
  ∀ state, root.Reachable budget state → root.HasCompletion state

/-- Every executable prefix extends to an accepted, decoded program. -/
def AcceptedProductiveAt (root : RefinementInterface) (budget : Nat) : Prop :=
  ∀ pre state,
    root.run pre (root.initial budget) = some state →
      AcceptedPrefix root budget pre

/-- Executability is exactly membership in the prefix closure of accepted
traces.  This is stronger than output soundness and gold-trace preservation. -/
def PrefixExactAt (root : RefinementInterface) (budget : Nat) : Prop :=
  ∀ pre,
    ExecutablePrefix root budget pre ↔ AcceptedPrefix root budget pre

/-- Terminal states reached from the initial state always decode.  This is the
missing bridge between a terminal-state completion and an accepted trace. -/
def TerminalDecodeTotalAt (root : RefinementInterface) (budget : Nat) : Prop :=
  ∀ trace state,
    root.run trace (root.initial budget) = some state →
    root.terminal state →
      ∃ program, root.decode trace = some program

/-- Accepted completion always implies that the prefix itself executed. -/
theorem acceptedPrefix_executable
    {budget : Nat} {pre : List root.Action}
    (accepted : AcceptedPrefix root budget pre) :
    ExecutablePrefix root budget pre := by
  rcases accepted with
    ⟨suffix, program, finalState, fullRun, _terminal, _decoded⟩
  rw [root.run_append] at fullRun
  cases prefixRun : root.run pre (root.initial budget) with
  | none =>
      rw [prefixRun] at fullRun
      contradiction
  | some state => exact ⟨state, prefixRun⟩

/-- Canonical completeness includes preservation of every canonical prefix. -/
theorem canonicalComplete_implies_prefixesPreserved
    {budget : Nat} (complete : CanonicalCompleteAt root budget) :
    CanonicalPrefixesPreservedAt root budget := by
  intro program wellFormed cost before after encoded
  rcases complete program wellFormed cost with
    ⟨finalState, fullRun, _terminal, _decoded⟩
  rw [encoded, root.run_append] at fullRun
  cases prefixRun : root.run before (root.initial budget) with
  | none =>
      rw [prefixRun] at fullRun
      contradiction
  | some state => exact ⟨state, prefixRun⟩

/-- Prefix exactness is precisely accepted productivity because the reverse
direction is true for every refinement interface. -/
theorem prefixExact_iff_acceptedProductive {budget : Nat} :
    PrefixExactAt root budget ↔ AcceptedProductiveAt root budget := by
  constructor
  · intro exactPrefix pre state prefixRun
    exact (exactPrefix pre).mp ⟨state, prefixRun⟩
  · intro productive pre
    constructor
    · rintro ⟨state, prefixRun⟩
      exact productive pre state prefixRun
    · exact acceptedPrefix_executable

/-- State productivity becomes accepted productivity when every reached
terminal trace is decodable. -/
theorem stateProductive_and_terminalDecodeTotal_imply_acceptedProductive
    {budget : Nat}
    (productive : StateProductiveAt root budget)
    (decodeTotal : TerminalDecodeTotalAt root budget) :
    AcceptedProductiveAt root budget := by
  intro pre state prefixRun
  have reachable : root.Reachable budget state := ⟨pre, prefixRun⟩
  rcases productive state reachable with
    ⟨suffix, finalState, suffixRun, terminal⟩
  have fullRun :
      root.run (pre ++ suffix) (root.initial budget) = some finalState := by
    rw [root.run_append, prefixRun]
    exact suffixRun
  rcases decodeTotal (pre ++ suffix) finalState fullRun terminal with
    ⟨program, decoded⟩
  exact ⟨suffix, program, finalState, fullRun, terminal, decoded⟩

/-! ## Existing refinement laws imply the correctly scoped contracts -/

variable (laws : RefinementLaws root)
include laws

theorem laws_acceptanceSoundAt (budget : Nat) :
    AcceptanceSoundAt root budget := by
  intro trace program accepted
  exact RefinementLaws.accepts_sound laws accepted

theorem laws_canonicalCompleteAt {budget : Nat}
    (budgetOK : root.budgetOK budget) :
    CanonicalCompleteAt root budget := by
  intro program wellFormed cost
  exact RefinementLaws.wellFormed_reachable laws budgetOK wellFormed cost

theorem laws_canonicalPrefixesPreservedAt {budget : Nat}
    (budgetOK : root.budgetOK budget) :
    CanonicalPrefixesPreservedAt root budget :=
  canonicalComplete_implies_prefixesPreserved
    (laws_canonicalCompleteAt laws budgetOK)

theorem laws_stateProductiveAt {budget : Nat}
    (budgetOK : root.budgetOK budget) :
    StateProductiveAt root budget := by
  intro state reachable
  exact RefinementLaws.reachable_hasCompletion laws budgetOK reachable

theorem laws_prefixExactAt {budget : Nat}
    (budgetOK : root.budgetOK budget)
    (decodeTotal : TerminalDecodeTotalAt root budget) :
    PrefixExactAt root budget := by
  rw [prefixExact_iff_acceptedProductive]
  exact stateProductive_and_terminalDecodeTotal_imply_acceptedProductive
    (laws_stateProductiveAt laws budgetOK) decodeTotal

omit laws

/-! ## Finite separating countermodels -/

/-- Every state is terminal, but no trace decodes.  The system is structurally
productive while no prefix has an accepted completion. -/
private def terminalWithoutDecodeRoot : RefinementInterface where
  State := Unit
  Hole := Unit
  Action := Unit
  Program := Unit
  initial := fun _ => ()
  holes := fun _ => []
  legal := fun _ _ => False
  apply? := fun _ _ => none
  terminal := fun _ => True
  decode := fun _ => none
  wellFormed := fun _ => True
  programCost := fun _ => 0
  encode := fun _ => []
  invariant := fun _ => True
  canComplete := fun _ => True
  budgetOK := fun _ => True

theorem stateProductivity_does_not_imply_prefixExactness :
    StateProductiveAt terminalWithoutDecodeRoot 0 ∧
      ¬ PrefixExactAt terminalWithoutDecodeRoot 0 := by
  constructor
  · intro state _reachable
    exact ⟨[], state, rfl, trivial⟩
  · intro exactPrefix
    have executable :
        ExecutablePrefix terminalWithoutDecodeRoot 0 [] := ⟨(), rfl⟩
    rcases (exactPrefix []).mp executable with
      ⟨suffix, program, finalState, _run, _terminal, decoded⟩
    simp [terminalWithoutDecodeRoot] at decoded

/-- Vacuous output soundness supplies no canonical completeness. -/
theorem acceptanceSoundness_does_not_imply_canonicalCompleteness :
    AcceptanceSoundAt terminalWithoutDecodeRoot 0 ∧
      ¬ CanonicalCompleteAt terminalWithoutDecodeRoot 0 := by
  constructor
  · intro trace program _accepted
    trivial
  · intro complete
    rcases complete () trivial (by simp [terminalWithoutDecodeRoot]) with
      ⟨finalState, _run, _terminal, decoded⟩
    simp [terminalWithoutDecodeRoot] at decoded

/-- Canonical admitted output coexists with an extra accepted invalid trace.
Completeness therefore does not imply soundness. -/
private def extraInvalidDecodeRoot : RefinementInterface where
  State := Unit
  Hole := Unit
  Action := Unit
  Program := Bool
  initial := fun _ => ()
  holes := fun _ => [()]
  legal := fun _ _ => True
  apply? := fun _ _ => some ()
  terminal := fun _ => True
  decode := fun trace => if trace = [] then some true else some false
  wellFormed := fun program => program = true
  programCost := fun _ => 0
  encode := fun _ => []
  invariant := fun _ => True
  canComplete := fun _ => True
  budgetOK := fun _ => True

theorem canonicalCompleteness_does_not_imply_acceptanceSoundness :
    CanonicalCompleteAt extraInvalidDecodeRoot 0 ∧
      ¬ AcceptanceSoundAt extraInvalidDecodeRoot 0 := by
  constructor
  · intro program wellFormed _cost
    subst program
    exact ⟨(), rfl, trivial, rfl⟩
  · intro sound
    have accepted :
        extraInvalidDecodeRoot.Accepts 0 [()] false :=
      ⟨(), rfl, trivial, rfl⟩
    have wellFormed := sound accepted
    simp [extraInvalidDecodeRoot] at wellFormed

#print axioms acceptedPrefix_executable
#print axioms canonicalComplete_implies_prefixesPreserved
#print axioms prefixExact_iff_acceptedProductive
#print axioms stateProductive_and_terminalDecodeTotal_imply_acceptedProductive
#print axioms laws_prefixExactAt
#print axioms stateProductivity_does_not_imply_prefixExactness
#print axioms acceptanceSoundness_does_not_imply_canonicalCompleteness
#print axioms canonicalCompleteness_does_not_imply_acceptanceSoundness

end Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.PrefixProperties
