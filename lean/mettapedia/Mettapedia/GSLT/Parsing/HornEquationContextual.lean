import Mettapedia.GSLT.Parsing.HornEquationInstantiation

/-!
# Checking contextual paths of authored equation occurrences

A path records the source occurrence and argument address of each reduction.
The executable checker uses the existing ground matcher. Its declarative
specification instead uses ground substitution instances of the original
source rows, closed under argument contexts. No scheduler or first-match
policy is imposed, and duplicate source occurrences remain distinct actions.

This checks supplied finite paths. It is not a search procedure, a PeTTa
evaluator, or a native execution correspondence theorem. Primitive evaluation
and binding constructs are not equation-context steps.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.HornEquationContextual

open HornCertificate HornSideAdmission HornGroundMatching HornEquationInstantiation

def RangeSafe (program : Program) : Prop :=
  ∀ rule ∈ program, ∀ left right, equationSides? rule = some (left, right) →
    ∀ identifier ∈ HornSpecialization.termVariables right,
      identifier ∈ HornSpecialization.termVariables left

def OccurrenceRangeSafe (program : Program) (occurrence : Nat) : Prop :=
  ∀ rule, program[occurrence]? = some rule →
    ∀ left right, equationSides? rule = some (left, right) →
      ∀ identifier ∈ HornSpecialization.termVariables right,
        identifier ∈ HornSpecialization.termVariables left

theorem RangeSafe.at {program : Program} (safe : RangeSafe program) (occurrence : Nat) :
    OccurrenceRangeSafe program occurrence := by
  intro rule selected left right decoded identifier occurs
  exact safe rule (List.mem_of_getElem? selected) left right decoded identifier occurs

theorem occurrenceRangeSafe_of_shape {program : Program} {occurrence : Nat}
    {left right : Term}
    (shape : (program[occurrence]?).bind equationSides? = some (left, right))
    (safe : ∀ identifier ∈ HornSpecialization.termVariables right,
      identifier ∈ HornSpecialization.termVariables left) :
    OccurrenceRangeSafe program occurrence := by
  intro rule selected actualLeft actualRight decoded
  have same : (actualLeft, actualRight) = (left, right) := by
    simpa [selected, decoded] using shape
  cases same
  exact safe

def checkRangeSafe (program : Program) : Bool :=
  program.all fun rule =>
    match equationSides? rule with
    | none => false
    | some (left, right) =>
      (HornSpecialization.termVariables right).all fun identifier =>
        decide (identifier ∈ HornSpecialization.termVariables left)

theorem rangeSafe_of_check {program : Program} (checked : checkRangeSafe program = true) :
    RangeSafe program := by
  intro rule member left right decoded identifier occurs
  have row := List.all_eq_true.mp checked rule member
  simp only [decoded] at row
  exact of_decide_eq_true (List.all_eq_true.mp row identifier occurs)

/-- Source occurrence and zero-based argument address, both retained as data. -/
structure Action where
  occurrence : Nat
  address : List Nat
  deriving DecidableEq, Repr

mutual
  inductive StepAt (program : Program) (occurrence : Nat) :
      List Nat → GroundTerm → GroundTerm → Prop where
    | root {rule : Rule} {left right : Term} {substitution : Substitution}
        {source target : GroundTerm}
        (selected : program[occurrence]? = some rule)
        (decoded : equationSides? rule = some (left, right))
        (valid : substitutionValid substitution = true)
        (input : instantiateTerm substitution left = some source)
        (output : instantiateTerm substitution right = some target) :
        StepAt program occurrence [] source target
    | application {index : Nat} {address : List Nat} {head : String}
        {before after : GroundTerms}
        (arguments : ArgumentsStepAt program occurrence index address before after) :
        StepAt program occurrence (index :: address)
          (.app head before) (.app head after)

  inductive ArgumentsStepAt (program : Program) (occurrence : Nat) :
      Nat → List Nat → GroundTerms → GroundTerms → Prop where
    | here {address : List Nat} {before after : GroundTerm} {tail : GroundTerms}
        (head : StepAt program occurrence address before after) :
        ArgumentsStepAt program occurrence 0 address
          (.cons before tail) (.cons after tail)
    | there {index : Nat} {address : List Nat} {head : GroundTerm}
        {before after : GroundTerms}
        (tail : ArgumentsStepAt program occurrence index address before after) :
        ArgumentsStepAt program occurrence (index + 1) address
          (.cons head before) (.cons head after)
end

mutual
  def rewriteAt? (program : Program) (occurrence : Nat) :
      List Nat → GroundTerm → Option GroundTerm
    | [], source => (instantiateEquationAt? program occurrence source).map Prod.fst
    | index :: address, .app head arguments =>
        (rewriteArgumentsAt? program occurrence index address arguments).map (.app head)
    | _ :: _, _ => none
  termination_by _ source => sizeOf source

  def rewriteArgumentsAt? (program : Program) (occurrence : Nat) :
      Nat → List Nat → GroundTerms → Option GroundTerms
    | 0, address, .cons head tail =>
        (rewriteAt? program occurrence address head).map (fun result => .cons result tail)
    | index + 1, address, .cons head tail =>
        (rewriteArgumentsAt? program occurrence index address tail).map (.cons head)
    | _, _, .nil => none
  termination_by _ _ sources => sizeOf sources
end

private theorem root_sound {program : Program} {occurrence : Nat}
    {source target : GroundTerm}
    (produced : (instantiateEquationAt? program occurrence source).map Prod.fst =
      some target) : StepAt program occurrence [] source target := by
  cases selected : program[occurrence]? with
  | none => simp [instantiateEquationAt?, selected] at produced
  | some rule =>
    cases decoded : equationSides? rule with
    | none => simp [instantiateEquationAt?, instantiateEquationRule?, selected, decoded] at produced
    | some sides =>
      rcases sides with ⟨left, right⟩
      cases matched : matchGroundTerm left source [] with
      | none => simp [instantiateEquationAt?, instantiateEquationRule?, selected, decoded,
          matched] at produced
      | some substitution =>
        cases output : instantiateTerm substitution right with
        | none => simp [instantiateEquationAt?, instantiateEquationRule?, selected, decoded,
            matched, output] at produced
        | some result =>
          have same : result = target := by
            simpa [instantiateEquationAt?, instantiateEquationRule?, selected, decoded,
              matched, output] using produced
          subst result
          obtain ⟨input, _, valid⟩ := matchGroundTerm_correct left source matched
          exact .root selected decoded (valid (by decide)) input output

mutual
  theorem rewriteAt?_sound (program : Program) (occurrence : Nat)
      (address : List Nat) (source target : GroundTerm)
      (produced : rewriteAt? program occurrence address source = some target) :
      StepAt program occurrence address source target := by
    cases address with
    | nil => exact root_sound (by simpa [rewriteAt?] using produced)
    | cons index address =>
      cases source with
      | atom _ => simp [rewriteAt?] at produced
      | integer _ => simp [rewriteAt?] at produced
      | app head arguments =>
        cases result : rewriteArgumentsAt? program occurrence index address arguments with
        | none => simp [rewriteAt?, result] at produced
        | some values =>
          have same : GroundTerm.app head values = target := by
            simpa [rewriteAt?, result] using produced
          subst target
          exact .application (rewriteArgumentsAt?_sound program occurrence index address
            arguments values result)
  termination_by sizeOf source

  theorem rewriteArgumentsAt?_sound (program : Program) (occurrence index : Nat)
      (address : List Nat) (sources targets : GroundTerms)
      (produced : rewriteArgumentsAt? program occurrence index address sources = some targets) :
      ArgumentsStepAt program occurrence index address sources targets := by
    cases sources with
    | nil => simp [rewriteArgumentsAt?] at produced
    | cons head tail =>
      cases index with
      | zero =>
        cases result : rewriteAt? program occurrence address head with
        | none => simp [rewriteArgumentsAt?, result] at produced
        | some value =>
          have same : GroundTerms.cons value tail = targets := by
            simpa [rewriteArgumentsAt?, result] using produced
          subst targets
          exact .here (rewriteAt?_sound program occurrence address head value result)
      | succ index =>
        cases result : rewriteArgumentsAt? program occurrence index address tail with
        | none => simp [rewriteArgumentsAt?, result] at produced
        | some values =>
          have same : GroundTerms.cons head values = targets := by
            simpa [rewriteArgumentsAt?, result] using produced
          subst targets
          exact .there (rewriteArgumentsAt?_sound program occurrence index address
            tail values result)
  termination_by sizeOf sources
end

mutual
  theorem rewriteAt?_complete_at {program : Program} {occurrence : Nat}
      (safe : OccurrenceRangeSafe program occurrence)
      {address : List Nat} {source target : GroundTerm}
      (step : StepAt program occurrence address source target) :
      rewriteAt? program occurrence address source = some target := by
    cases step with
    | root selected decoded valid input output =>
      obtain ⟨certificate, produced⟩ := instantiateEquationRule?_complete decoded
        (safe _ selected _ _ decoded) input output
      simp [rewriteAt?, instantiateEquationAt?, selected, produced]
    | application arguments =>
      simp [rewriteAt?, rewriteArgumentsAt?_complete_at safe arguments]
  termination_by sizeOf source

  theorem rewriteArgumentsAt?_complete_at {program : Program} {occurrence : Nat}
      (safe : OccurrenceRangeSafe program occurrence)
      {index : Nat} {address : List Nat} {sources targets : GroundTerms}
      (step : ArgumentsStepAt program occurrence index address sources targets) :
      rewriteArgumentsAt? program occurrence index address sources = some targets := by
    cases step with
    | here head => simp [rewriteArgumentsAt?, rewriteAt?_complete_at safe head]
    | there tail => simp [rewriteArgumentsAt?, rewriteArgumentsAt?_complete_at safe tail]
  termination_by sizeOf sources
end

theorem rewriteAt?_complete {program : Program} (safe : RangeSafe program)
    {occurrence : Nat} {address : List Nat} {source target : GroundTerm}
    (step : StepAt program occurrence address source target) :
    rewriteAt? program occurrence address source = some target :=
  rewriteAt?_complete_at (safe.at occurrence) step

theorem rewriteAt?_iff {program : Program} (safe : RangeSafe program)
    (occurrence : Nat) (address : List Nat) (source target : GroundTerm) :
    rewriteAt? program occurrence address source = some target ↔
      StepAt program occurrence address source target :=
  ⟨rewriteAt?_sound program occurrence address source target, rewriteAt?_complete safe⟩

def replayPath (program : Program) : List Action → GroundTerm → Option GroundTerm
  | [], source => some source
  | action :: rest, source => do
      let next ← rewriteAt? program action.occurrence action.address source
      replayPath program rest next

inductive Path (program : Program) : List Action → GroundTerm → GroundTerm → Prop where
  | nil (source : GroundTerm) : Path program [] source source
  | cons {action : Action} {rest : List Action} {source middle target : GroundTerm}
      (step : StepAt program action.occurrence action.address source middle)
      (tail : Path program rest middle target) :
      Path program (action :: rest) source target

theorem replayPath_sound {program : Program} (actions : List Action)
    (source target : GroundTerm)
    (accepted : replayPath program actions source = some target) :
    Path program actions source target := by
  induction actions generalizing source with
  | nil =>
    have same : source = target := by simpa [replayPath] using accepted
    subst target
    exact .nil source
  | cons action rest ih =>
    cases next : rewriteAt? program action.occurrence action.address source with
    | none => simp [replayPath, next] at accepted
    | some middle =>
      exact .cons (rewriteAt?_sound _ _ _ _ _ next)
        (ih middle (by simpa [replayPath, next] using accepted))

theorem replayPath_complete {program : Program} (safe : RangeSafe program)
    {actions : List Action} {source target : GroundTerm}
    (path : Path program actions source target) :
    replayPath program actions source = some target := by
  induction path with
  | nil => rfl
  | cons step _ ih => simp [replayPath, rewriteAt?_complete safe step, ih]

/-- Unused source rows do not impose unnecessary completeness premises on
a supplied trace: only its selected occurrences must be range-safe. -/
theorem replayPath_complete_on {program : Program} {actions : List Action}
    {source target : GroundTerm} (path : Path program actions source target)
    (safe : ∀ action ∈ actions, OccurrenceRangeSafe program action.occurrence) :
    replayPath program actions source = some target := by
  induction path with
  | nil => rfl
  | @cons action rest source middle target step tail ih =>
    have headSafe := safe action (by simp)
    have tailSafe := fun a (member : a ∈ rest) => safe a (by simp [member])
    simp [replayPath, rewriteAt?_complete_at headSafe step, ih tailSafe]

theorem replayPath_iff {program : Program} (safe : RangeSafe program)
    (actions : List Action) (source target : GroundTerm) :
    replayPath program actions source = some target ↔ Path program actions source target :=
  ⟨replayPath_sound actions source target, replayPath_complete safe⟩

/-- Changing the address is explicit evidence transport, not a different rule. -/
def underArgument (index : Nat) (action : Action) : Action :=
  { action with address := index :: action.address }

private theorem ArgumentsStepAt.context {program : Program} {occurrence : Nat}
    {address : List Nat} {source target : GroundTerm}
    (step : StepAt program occurrence address source target)
    (before after : List GroundTerm) :
    ArgumentsStepAt program occurrence before.length address
      (GroundTerms.ofList (before ++ source :: after))
      (GroundTerms.ofList (before ++ target :: after)) := by
  induction before with
  | nil => exact .here step
  | cons head rest ih => exact .there ih

/-- Context transport preserves the full action list, including repeated
source occurrences, and only prefixes its recorded argument addresses. -/
theorem Path.context {program : Program} {actions : List Action}
    {source target : GroundTerm} (path : Path program actions source target)
    (head : String) (before after : List GroundTerm) :
    Path program (actions.map (underArgument before.length))
      (.app head (GroundTerms.ofList (before ++ source :: after)))
      (.app head (GroundTerms.ofList (before ++ target :: after))) := by
  induction path with
  | nil => exact .nil _
  | cons step _ ih => exact .cons (.application (ArgumentsStepAt.context step before after)) ih

@[simp] theorem contextual_action_count (index : Nat) (actions : List Action) :
    (actions.map (underArgument index)).length = actions.length := List.length_map _

@[simp] theorem contextual_occurrence_order (index : Nat) (actions : List Action) :
    (actions.map (underArgument index)).map Action.occurrence =
      actions.map Action.occurrence := by
  simp [List.map_map, underArgument]

private def constantRule : Rule :=
  ⟨"constant", ⟨"metta-equation",
    .cons (.app "f" .nil) (.cons (.atom "a") .nil)⟩, []⟩

theorem nested_source_occurrence_executes :
    replayPath [constantRule] [⟨0, [1]⟩]
      (.app "pair" (.cons (.integer 7) (.cons (.app "f" .nil) .nil))) =
    some (.app "pair" (.cons (.integer 7) (.cons (.atom "a") .nil))) := by
  simp [replayPath, rewriteAt?, rewriteArgumentsAt?, instantiateEquationAt?,
    instantiateEquationRule?, constantRule, equationSides?, matchGroundTerm,
    matchGroundTerms, instantiateTerm]

theorem absent_argument_refused :
    replayPath [constantRule] [⟨0, [2]⟩]
      (.app "pair" (.cons (.integer 7) (.cons (.app "f" .nil) .nil))) = none := by
  simp [replayPath, rewriteAt?, rewriteArgumentsAt?]

theorem duplicate_occurrences_have_distinct_valid_traces :
    ([Action.mk 0 []] ≠ [Action.mk 1 []]) ∧
    replayPath [constantRule, constantRule] [⟨0, []⟩] (.app "f" .nil) = some (.atom "a") ∧
    replayPath [constantRule, constantRule] [⟨1, []⟩] (.app "f" .nil) = some (.atom "a") := by
  simp [replayPath, rewriteAt?, instantiateEquationAt?, instantiateEquationRule?,
    constantRule, equationSides?, matchGroundTerm, matchGroundTerms,
    instantiateTerm, Action.mk.injEq]

theorem wrong_rule_or_atom_shape_refused :
    replayPath [constantRule] [⟨1, []⟩] (.app "f" .nil) = none ∧
    replayPath [constantRule] [⟨0, []⟩] (.atom "f") = none := by
  simp [replayPath, rewriteAt?, instantiateEquationAt?, instantiateEquationRule?,
    constantRule, equationSides?, matchGroundTerm]

#print axioms rewriteAt?_iff
#print axioms replayPath_iff

end Mettapedia.GSLT.Parsing.HornEquationContextual
