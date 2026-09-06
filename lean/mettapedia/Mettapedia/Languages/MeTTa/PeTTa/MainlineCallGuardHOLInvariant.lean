import Mettapedia.Logic.HOL.TransitionInvariant
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperational

/-!
# Applying an intrinsic HOL proof to the specified call-guard compiler

The step relation is the existing compiler micro-machine. A separate relation
states equality of compiler denotations. An intrinsic HOL derivation composes
the step-to-denotation refinement with preservation of an arbitrary predicate
on compilation results. The model hypotheses are discharged by the existing
one-step compiler theorem and equality elimination, respectively.

This is proof use in the specified operational semantics, not a proof about
the complete CeTTa implementation and not an external proof-format importer.
The negative control keeps the same formulas and derivation but interprets
the predicate as a control-state test that the actual compiler violates.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardHOLInvariant

open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.TransitionInvariant
open Mettapedia.Languages.MeTTa.PeTTa.MainlineTypeQueryGSLT
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardProjection
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardPlan
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperational

def stateType : Ty Unit := .base ()

/-- Three independently interpreted symbols; operational stepping is not
defined to be equality of denotations. -/
inductive Constant : Ty Unit → Type where
  | step : Constant (stateType ⇒ stateType ⇒ .prop)
  | sameResult : Constant (stateType ⇒ stateType ⇒ .prop)
  | property : Constant (stateType ⇒ .prop)

def assumptions : List (ClosedFormula Constant) :=
  [refinementFormula (.const .step) (.const .sameResult),
    preservationFormula (.const .sameResult) (.const .property)]

def conclusion : ClosedFormula Constant :=
  preservationFormula (.const .step) (.const .property)

/-- This derivation uses universal elimination and implication elimination;
the requested conclusion is not an assumption of the theory. -/
theorem preservation_derived : Derivation Constant assumptions conclusion :=
  preservation_of_refinement (Γ := []) Constant.step Constant.sameResult Constant.property

def Carrier (_base : Unit) : Type 1 := ULift.{1} CompileLanguageControl

def constantDenotation (property : CompileLanguageControl → Prop) :
    {type : Ty Unit} → Constant type → Ty.denote.{0, 0} Carrier type
  | _, .step => fun source target =>
      .up (compileLanguageStep? source.down = some target.down)
  | _, .sameResult => fun source target =>
      .up (source.down.denote = target.down.denote)
  | _, .property => fun state => .up (property state.down)

/-- A concrete standard model. Only this specimen chooses full domains; the
general proof-use theorem also applies to non-full Henkin models. -/
def model (property : CompileLanguageControl → Prop) : HenkinModel.{0, 0, 0} Unit Constant :=
  HenkinModel.standard Carrier (constantDenotation property)

def emptyValuation (property : CompileLanguageControl → Prop) :
    HenkinModel.Valuation (model property) [] := fun index => nomatch index

theorem emptyValuation_admissible (property : CompileLanguageControl → Prop) :
    HenkinModel.ValuationAdmissible (model property) (emptyValuation property) := by
  intro type index
  nomatch index

/-- Independent satisfaction of both source assumptions for every predicate
on the reference compiler's result. -/
theorem resultPredicate_satisfies_assumptions (observe : CompilationResult → Prop) :
    Soundness.SatisfiesHyps (model (fun state => observe state.denote))
      (emptyValuation _) assumptions := by
  intro formula member
  rcases List.mem_cons.mp member with equal | member
  · subst formula
    apply (denote_refinementFormula _ _ _ _).mpr
    intro source _ target _ transition
    exact compileLanguageStep_denote_preserved transition
  · rcases List.mem_cons.mp member with equal | impossible
    · subst formula
      apply (denote_preservationFormula _ _ _ _).mpr
      intro source _ target _ equal holds
      change observe target.down.denote
      change source.down.denote = target.down.denote at equal
      change observe source.down.denote at holds
      rwa [← equal]
    · nomatch impossible

/-- A GSLT multi-step proof has the same finite transitions as the standard
reflexive-transitive closure consumed by the HOL theorem. -/
theorem multiStep_finite : ∀ {source target : CompileLanguageControl},
    compileLanguageGSLT.MultiStep source target →
      Relation.ReflTransGen compileLanguageGSLT.Step source target
  | _, _, .refl _ => .refl
  | _, _, .step transition rest =>
      Relation.ReflTransGen.head transition (multiStep_finite rest)

/-- Every finite compiler run preserves the selected result property, by
using the actual intrinsic HOL derivation in the independently satisfied model. -/
theorem run_preserves_result_predicate (observe : CompilationResult → Prop)
    {source target : CompileLanguageControl}
    (run : compileLanguageGSLT.MultiStep source target)
    (holds : observe source.denote) : observe target.denote := by
  exact finite_run_preserves preservation_derived (model (fun state => observe state.denote))
    (emptyValuation _) (emptyValuation_admissible _)
    (resultPredicate_satisfies_assumptions observe)
    (fun state => ULift.up state) (fun _ => by trivial)
    (fun _ _ => Iff.rfl) (fun _ => Iff.rfl) (multiStep_finite run) holds

/-- A terminating compiler execution produces exactly the reference result;
the proof passes through intrinsic HOL, rather than assuming the run theorem. -/
theorem halts_with_specification (owned : OwnedSnapshot) (head : String) (arity : Nat)
    {result : CompilationResult}
    (run : compileLanguageGSLT.MultiStep (compileLanguageStart owned head arity)
      (.halted result)) : result = compileGuards owned head arity := by
  exact run_preserves_result_predicate (fun actual => actual = compileGuards owned head arity)
    run (compileLanguageStart_denote_exact owned head arity)

/-! ## An altered interpretation is rejected despite identical proof syntax -/

def runningPredicate : CompileLanguageControl → Prop
  | .running .. => True
  | _ => False

def emptySource : CompileLanguageControl := .running ⟨0⟩ 0 "f" 0 [] []

def emptyTarget : CompileLanguageControl :=
  .halted (.compiled ⟨⟨0⟩, 0, "f", 0, []⟩)

theorem empty_transition : compileLanguageGSLT.Step emptySource emptyTarget := rfl

theorem empty_transition_changes_control : emptySource ≠ emptyTarget := by decide

/-- The source and target really have the same reference meaning. -/
theorem empty_transition_same_result : emptySource.denote = emptyTarget.denote :=
  compileLanguageStep_denote_preserved empty_transition

/-- Changing only the predicate interpretation refutes satisfaction of the
source theory. Merely retaining an intrinsic derivation cannot fix this. -/
theorem altered_interpretation_not_satisfying :
    ¬ Soundness.SatisfiesHyps (model runningPredicate)
      (emptyValuation _) assumptions := by
  intro satisfied
  have invalid := finite_run_preserves preservation_derived (model runningPredicate)
    (emptyValuation _) (emptyValuation_admissible _) satisfied
    (fun state => ULift.up state) (fun _ => by trivial)
    (fun _ _ => Iff.rfl) (fun _ => Iff.rfl)
    (Relation.ReflTransGen.single empty_transition)
    (show runningPredicate emptySource from trivial)
  exact invalid

/-- Under that altered interpretation the claimed preservation formula is
itself false on the actual one-step compiler execution. -/
theorem altered_interpretation_not_valid :
    ¬ HenkinModel.models (model runningPredicate) conclusion := by
  intro valid
  have preserved := (denote_preservationFormula (model runningPredicate)
    (emptyValuation _) (.const .step) (.const .property)).mp valid
  exact preserved (ULift.up emptySource) trivial (ULift.up emptyTarget) trivial
    empty_transition trivial

#print axioms preservation_derived
#print axioms resultPredicate_satisfies_assumptions
#print axioms run_preserves_result_predicate
#print axioms halts_with_specification
#print axioms altered_interpretation_not_satisfying
#print axioms altered_interpretation_not_valid

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardHOLInvariant
