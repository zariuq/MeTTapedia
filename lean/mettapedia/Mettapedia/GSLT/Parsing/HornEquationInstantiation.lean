import Mettapedia.GSLT.Parsing.HornGroundMatching
import Mettapedia.GSLT.Parsing.HornCertificateGSLT

/-!
# Source-certified instantiation of an authored equation occurrence

An unconditional `metta-equation` row can produce a concrete residual by
matching its left side and instantiating its right side. The result carries
an ordinary Horn certificate checked against the original ordered program.
Source occurrence selection is explicit; this operation neither chooses the
first matching rule nor collapses equal-looking occurrences.

The output is a residual expression, not an evaluated value. Recursive
evaluation, its order, and native runtime correspondence remain separate
obligations. In particular, certifying one source row is not an evaluator.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.HornEquationInstantiation

open HornCertificate HornSideAdmission HornGroundMatching HornCertificateGSLT

/-- Decode precisely the unconditional, symbol-headed equation-row shape.
Premise-bearing rows and ordinary Horn relations are not evaluator rules. -/
def equationSides? : Rule → Option (Term × Term)
  | ⟨_, ⟨"metta-equation", .cons (.app head arguments) (.cons right .nil)⟩, []⟩ =>
      some (.app head arguments, right)
  | _ => none

theorem equationSides?_spec {rule : Rule} {left right : Term}
    (decoded : equationSides? rule = some (left, right)) :
    rule.head = ⟨"metta-equation", .cons left (.cons right .nil)⟩ ∧
      rule.body = [] := by
  unfold equationSides? at decoded
  split at decoded <;> simp_all

def equationGoal (call residual : GroundTerm) : GroundAtom :=
  ⟨"metta-equation", .cons call (.cons residual .nil)⟩

/-- Use the existing matcher; do not ask the caller to supply the answer. -/
def instantiateEquationRule? (rule : Rule) (call : GroundTerm) :
    Option (GroundTerm × Certificate) := do
  let (left, right) ← equationSides? rule
  let substitution ← matchGroundTerm left call []
  let residual ← instantiateTerm substitution right
  pure (residual, .node rule substitution .nil)

theorem instantiateEquationRule?_replays {program : Program} {rule : Rule}
    (member : rule ∈ program) {call residual : GroundTerm} {certificate : Certificate}
    (produced : instantiateEquationRule? rule call = some (residual, certificate)) :
    replay program 1 (equationGoal call residual) certificate = true := by
  cases decoded : equationSides? rule with
  | none => simp [instantiateEquationRule?, decoded] at produced
  | some sides =>
      rcases sides with ⟨left, right⟩
      cases matched : matchGroundTerm left call [] with
      | none => simp [instantiateEquationRule?, decoded, matched] at produced
      | some substitution =>
          cases instantiatedRight : instantiateTerm substitution right with
          | none =>
              simp [instantiateEquationRule?, decoded, matched, instantiatedRight] at produced
          | some result =>
              have equal :
                  (result, Certificate.node rule substitution .nil) =
                    (residual, certificate) := by
                simpa [instantiateEquationRule?, decoded, matched, instantiatedRight] using produced
              cases equal
              obtain ⟨instantiatedLeft, _, valid⟩ := matchGroundTerm_correct left call matched
              have validSubstitution := valid (by decide)
              obtain ⟨head, body⟩ := equationSides?_spec decoded
              simp [replay, member, validSubstitution, head, body,
                instantiateAtom, instantiateTerms, instantiatedLeft,
                instantiatedRight, instantiateAtoms, equationGoal, Certificates.toList]

/-- When every right-side variable occurs on the left, the answer-blind
producer realizes every ground instance of this row. Extra bindings in an
independent witness cannot change the produced residual. -/
theorem instantiateEquationRule?_complete {rule : Rule} {left right : Term}
    (decoded : equationSides? rule = some (left, right))
    (rangeSafe : ∀ identifier ∈ HornSpecialization.termVariables right,
      identifier ∈ HornSpecialization.termVariables left)
    {witness : Substitution} {call residual : GroundTerm}
    (leftInstance : instantiateTerm witness left = some call)
    (rightInstance : instantiateTerm witness right = some residual) :
    ∃ certificate, instantiateEquationRule? rule call = some (residual, certificate) := by
  obtain ⟨substitution, matched, preserved⟩ :=
    matchGroundTerm_complete (.nil witness) left call leftInstance
  obtain ⟨matchedInstance, _, _⟩ := matchGroundTerm_correct left call matched
  have leftBound := (instantiateTerm_isSome_iff substitution left).mp
    (by simp [matchedInstance])
  have rightBound := (instantiateTerm_isSome_iff substitution right).mpr
    (fun identifier member => leftBound identifier (rangeSafe identifier member))
  obtain ⟨result, resultInstance⟩ := Option.isSome_iff_exists.mp rightBound
  have transported := instantiateTerm_of_extends preserved right result resultInstance
  have sameResult : result = residual := Option.some.inj (transported.symm.trans rightInstance)
  subst result
  exact ⟨.node rule substitution .nil,
    by simp [instantiateEquationRule?, decoded, matched, resultInstance]⟩

/-- Select a source occurrence by index. Duplicate rule values are still
distinct selectable occurrences; no name map or duplicate eraser is used. -/
def instantiateEquationAt? (program : Program) (occurrence : Nat)
    (call : GroundTerm) : Option (GroundTerm × Certificate) := do
  let rule ← program[occurrence]?
  instantiateEquationRule? rule call

theorem instantiateEquationAt?_replays {program : Program} {occurrence : Nat}
    {call residual : GroundTerm} {certificate : Certificate}
    (produced : instantiateEquationAt? program occurrence call = some (residual, certificate)) :
    replay program 1 (equationGoal call residual) certificate = true := by
  cases selected : program[occurrence]? with
  | none => simp [instantiateEquationAt?, selected] at produced
  | some rule =>
      exact instantiateEquationRule?_replays (List.mem_of_getElem? selected)
        (by simpa [instantiateEquationAt?, selected] using produced)

/-- The produced residual is authorized by a genuine terminal execution of
the original Horn GSLT, not by a new theory defined from the producer. -/
theorem instantiateEquationAt?_source_path {program : Program} {occurrence : Nat}
    {call residual : GroundTerm} {certificate : Certificate}
    (produced : instantiateEquationAt? program occurrence call = some (residual, certificate)) :
    (theory program).MultiStep [(1, equationGoal call residual)] [] := by
  exact (replay_iff_terminal_path program 1 (equationGoal call residual)).mp
    ⟨certificate, instantiateEquationAt?_replays produced⟩

private def constantRule (value : String) : Rule :=
  ⟨"constant", ⟨"metta-equation",
    .cons (.app "f" .nil) (.cons (.atom value) .nil)⟩, []⟩

theorem nullary_call_produces_source_result :
    (instantiateEquationAt? [constantRule "a"] 0 (.app "f" .nil)).map Prod.fst =
      some (.atom "a") := by decide

theorem bare_symbol_does_not_call_rule :
    instantiateEquationAt? [constantRule "a"] 0 (.atom "f") = none := by decide

theorem distinct_source_occurrences_remain_selectable :
    (instantiateEquationAt? [constantRule "a", constantRule "b"] 0
      (.app "f" .nil)).map Prod.fst = some (.atom "a") ∧
    (instantiateEquationAt? [constantRule "a", constantRule "b"] 1
      (.app "f" .nil)).map Prod.fst = some (.atom "b") := by decide

theorem absent_source_occurrence_is_refused :
    instantiateEquationAt? [constantRule "a"] 1 (.app "f" .nil) = none := by decide

theorem premise_bearing_equation_is_not_unconditional :
    instantiateEquationRule?
      { constantRule "a" with body := [⟨"required", .nil⟩] }
      (.app "f" .nil) = none := by decide

theorem right_only_variable_cannot_invent_a_result :
    instantiateEquationRule?
      ⟨"unbound", ⟨"metta-equation",
        .cons (.app "f" .nil) (.cons (.var 0) .nil)⟩, []⟩
      (.app "f" .nil) = none := by decide

#print axioms instantiateEquationAt?_replays
#print axioms instantiateEquationAt?_source_path
#print axioms instantiateEquationRule?_complete

end Mettapedia.GSLT.Parsing.HornEquationInstantiation
