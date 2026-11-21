import Mettapedia.GSLT.Contracts.CanonicalSuccessorClasses
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalRepresentativeStep
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT

/-!
# Rho as an instance of the canonical-successor contract

The contract `CanonicalSuccessorClasses` takes static equations as a setoid,
a normal-form function for them, and a type-valued raw transition relation. It
proves that stepping the chosen representatives preserves every successor class
exactly when the rules are one-step coherent (`exact_iff_coherent`).

For rho:

* the equations are equality of canonical forms (`rhoEquations`), the normal
  forms are the canonical forms (`rhoForms`), and the raw transitions are the
  least authored step `RhoStep`, a proposition lifted to a type (`rhoRaw`);
* coherence is `rhoStep_canonicalize` (`rho_coherent`), so stepping canonical
  representatives is exact (`rho_exact`), and the authored stepper, run at the
  canonical representative to the bag depth of the term, enumerates exactly the
  successor classes (`successorClasses_iff_modulo`), for open and closed terms;
* the contract's canonical step is `CanonicalRepresentativeStep.CanonicalStep`
  restricted to canonical forms (`canonicalStep_iff`); on canonical forms both
  are the same relation, and only the latter is also defined at a non-canonical
  source, where it steps that spelling as written.

The representative must be the canonical one. Any normal-form function for the
same equations that represents a class by a stuck spelling of a stepping class
is not coherent, so its stepping is not exact
(`noncanonical_representative_not_exact`), and stepping the input as written
is not exact either (`rawSource_not_exact`).

The closed process fiber `RhoProcess`, with the established equations
`rhoProcessEquations` (the same relation, `rhoProcessEquations_iff_rhoEquations`),
is a second instance (`rhoProcess_exact`, `rhoProcess_canonicalStep_iff`,
`rhoProcess_successorClasses_iff_modulo`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalSuccessorInstance

open Mettapedia.GSLT.Contracts
open Mettapedia.GSLT.Contracts.CanonicalSuccessorClasses
  (NormalForms Modulo Coherent exact_iff_coherent enumerate_iff_modulo)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical (canonicalize canonicalize_idempotent)
open Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep (mem_rewriteAt_iff_stepAt)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep
  (RhoStepAt RhoStep rhoRuleInterpretation rhoBasePremises rhoStep_preserves_closed)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalRepresentativeStep
  (rhoStep_canonicalize rhoStepAt_cases rhoStepAt_comm_at rhoStepAt_par_at StepModulo
    rhoStep_not_closed_under_canonical_equality nestedRedex flatRedex nestedRedex_stuck
    flatRedex_steps canonicalize_nestedRedex)

/-! ## The instance on patterns -/

/-- Rho's equations: two patterns are equal when their canonical forms are. -/
def rhoEquations : Setoid Pattern :=
  Setoid.ker (canonicalize rhoReflectivePresentation)

theorem rhoEquations_r {first second : Pattern} :
    rhoEquations.r first second ↔
      canonicalize rhoReflectivePresentation first =
        canonicalize rhoReflectivePresentation second :=
  Iff.rfl

/-- The raw transitions: the least authored rho step, lifted to a type. A
receipt records only that the step exists. -/
abbrev rhoRaw (source target : Pattern) : Type :=
  PLift (RhoStep source target)

theorem nonempty_rhoRaw {source target : Pattern} :
    Nonempty (rhoRaw source target) ↔ RhoStep source target :=
  ⟨fun ⟨⟨step⟩⟩ => step, fun step => ⟨⟨step⟩⟩⟩

/-- Canonical forms are normal forms for rho's equations. -/
def rhoForms : NormalForms rhoEquations where
  normal := canonicalize rhoReflectivePresentation
  sound := canonicalize_idempotent rhoReflectivePresentation
  same := id

/-- **Coherence.** A raw step from any pattern is matched, up to the equations, by
a raw step from its canonical form. -/
theorem rho_coherent : Coherent rhoForms rhoRaw := by
  rintro source target ⟨⟨step⟩⟩
  obtain ⟨result, resultStep, same⟩ := rhoStep_canonicalize step
  exact ⟨result, ⟨⟨resultStep⟩⟩, same⟩

/-- **Exactness.** Stepping canonical representatives reaches exactly the
successor classes of rewriting modulo the equations. -/
theorem rho_exact (source target : Pattern) :
    CanonicalSuccessorClasses.CanonicalStep rhoForms rhoRaw
        (rhoForms.key source) (rhoForms.key target) ↔
      Modulo (equations := rhoEquations) rhoRaw source target :=
  (exact_iff_coherent rhoForms rhoRaw).mpr rho_coherent source target

/-! ## The two canonical steps and the two modulo relations -/

/-- On canonical forms, the contract's canonical step is
`CanonicalRepresentativeStep.CanonicalStep`. -/
theorem canonicalStep_iff (source target : rhoForms.Key) :
    CanonicalSuccessorClasses.CanonicalStep rhoForms rhoRaw source target ↔
      CanonicalRepresentativeStep.CanonicalStep source.val target.val := by
  constructor
  · rintro ⟨result, ⟨⟨step⟩⟩, rfl⟩
    exact ⟨result, step, rfl⟩
  · rintro ⟨result, step, same⟩
    exact ⟨result, ⟨⟨step⟩⟩, Subtype.ext same⟩

/-- `CanonicalRepresentativeStep.CanonicalStep` only reaches canonical forms. -/
theorem canonicalStep_target_canonical {source target : Pattern}
    (step : CanonicalRepresentativeStep.CanonicalStep source target) :
    canonicalize rhoReflectivePresentation target = target := by
  obtain ⟨result, -, rfl⟩ := step
  exact canonicalize_idempotent _ result

/-- The contract's modulo step is `StepModulo` read up to the equations at the
target. -/
theorem modulo_iff_stepModulo (source target : Pattern) :
    Modulo (equations := rhoEquations) rhoRaw source target ↔
      ∃ target', StepModulo source target' ∧
        canonicalize rhoReflectivePresentation target' =
          canonicalize rhoReflectivePresentation target := by
  constructor
  · rintro ⟨⟨redex, contractum, sourceEquation, ⟨step⟩, targetEquation⟩⟩
    exact ⟨contractum, ⟨redex, sourceEquation.symm, step⟩, targetEquation⟩
  · rintro ⟨target', ⟨representative, same, step⟩, targetSame⟩
    exact ⟨⟨representative, target', same.symm, ⟨step⟩, targetSame⟩⟩

/-- `CanonicalRepresentativeStep.stepModulo_iff_canonicalStep`, obtained from the
contract's exactness criterion and rho's coherence. -/
theorem stepModulo_iff_canonicalStep_of_contract (source target : Pattern) :
    (∃ target', StepModulo source target' ∧
        canonicalize rhoReflectivePresentation target' =
          canonicalize rhoReflectivePresentation target) ↔
      CanonicalRepresentativeStep.CanonicalStep (canonicalize rhoReflectivePresentation source)
        (canonicalize rhoReflectivePresentation target) :=
  (modulo_iff_stepModulo source target).symm.trans
    ((rho_exact source target).symm.trans (canonicalStep_iff _ _))

/-! ## An exact enumerator of raw steps -/

mutual
  /-- How deep the authored rules reach into a pattern: one level per parallel
  bag on the way down. -/
  def parallelDepth : Pattern → Nat
    | .collection .hashBag elements _ => parallelDepthList elements + 1
    | _ => 0
  /-- The deepest member of a list. -/
  def parallelDepthList : List Pattern → Nat
    | [] => 0
    | element :: elements => max (parallelDepth element) (parallelDepthList elements)
end

theorem parallelDepth_le_of_mem {elements : List Pattern} {element : Pattern}
    (member : element ∈ elements) : parallelDepth element ≤ parallelDepthList elements := by
  induction elements with
  | nil => cases member
  | cons head tail ih =>
      simp only [parallelDepthList]
      rcases List.mem_cons.mp member with rfl | found
      · exact le_max_left _ _
      · exact (ih found).trans (le_max_right _ _)

/-- Every raw step is taken within the bag depth of its source. -/
theorem rhoStepAt_within_depth : ∀ {fuel : Nat} {source target : Pattern},
    RhoStepAt fuel source target →
      ∃ fuel' ≤ parallelDepth source, RhoStepAt fuel' source target := by
  intro fuel
  induction fuel with
  | zero => intro source target step; cases step
  | succ fuel ih =>
  intro source target step
  rcases rhoStepAt_cases step with
    ⟨elements, termRest, inputIndex, inputBound, outputIndex, outputBound, inputChannel, body,
      binder, outputChannel, payload, rfl, inputEq, outputEq, channels, rfl⟩ |
    ⟨smaller, elements, termRest, index, indexBound, candidate, fuelEq, rfl, innerStep, rfl⟩
  · exact ⟨1, by simp [parallelDepth],
      rhoStepAt_comm_at inputBound outputBound inputEq outputEq channels⟩
  · cases fuelEq
    obtain ⟨inner, innerBound, innerStep'⟩ := ih innerStep
    refine ⟨inner + 1, ?_, rhoStepAt_par_at indexBound innerStep'⟩
    have memberBound := parallelDepth_le_of_mem (List.getElem_mem indexBound)
    simp only [parallelDepth]
    omega

/-- The authored rho stepper, run at every depth up to the bag depth of the
source. -/
def rhoSuccessors (source : Pattern) : List Pattern :=
  (List.range (parallelDepth source + 1)).flatMap fun fuel =>
    Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.rewriteAt
      rhoRuleInterpretation rhoBasePremises rhoCalc fuel source

/-- The stepper lists exactly the raw steps, from any pattern. -/
theorem mem_rhoSuccessors {source target : Pattern} :
    target ∈ rhoSuccessors source ↔ RhoStep source target := by
  simp only [rhoSuccessors, List.mem_flatMap, List.mem_range, mem_rewriteAt_iff_stepAt]
  constructor
  · rintro ⟨fuel, -, step⟩
    exact ⟨fuel, step⟩
  · rintro ⟨fuel, step⟩
    obtain ⟨fuel', bound, step'⟩ := rhoStepAt_within_depth step
    exact ⟨fuel', Nat.lt_succ_of_le bound, step'⟩

/-- **Successor classes.** The normalized answers of the stepper at the canonical
representative are exactly the successor classes modulo the equations. -/
theorem successorClasses_iff_modulo (source target : Pattern) :
    rhoForms.key target ∈
        (rhoSuccessors (canonicalize rhoReflectivePresentation source)).map rhoForms.key ↔
      Modulo (equations := rhoEquations) rhoRaw source target :=
  enumerate_iff_modulo rhoForms rhoRaw rho_coherent (fun key => rhoSuccessors key.val)
    (fun _ _ => mem_rhoSuccessors.trans nonempty_rhoRaw.symm) source target

/-! ## Controls: the representative must be canonical -/

/-- Canonical forms, except that the class of `chosen` is represented by
`chosen` itself. These are normal forms for the same equations. -/
def representedBy (chosen : Pattern) : NormalForms rhoEquations where
  normal state :=
    if canonicalize rhoReflectivePresentation state = canonicalize rhoReflectivePresentation chosen
    then chosen else canonicalize rhoReflectivePresentation state
  sound state := by
    by_cases same : canonicalize rhoReflectivePresentation state =
        canonicalize rhoReflectivePresentation chosen
    · rw [if_pos same]
      exact same.symm
    · rw [if_neg same]
      exact canonicalize_idempotent _ state
  same {first second} equal := by
    rw [rhoEquations_r] at equal
    simp only [equal]

/-- A stuck spelling of a stepping class, chosen as its representative, breaks
coherence. -/
theorem representedBy_not_coherent {chosen representative target : Pattern}
    (same : canonicalize rhoReflectivePresentation chosen =
      canonicalize rhoReflectivePresentation representative)
    (step : RhoStep representative target) (stuck : ∀ result, ¬ RhoStep chosen result) :
    ¬ Coherent (representedBy chosen) rhoRaw := by
  intro coherent
  obtain ⟨result, ⟨⟨chosenStep⟩⟩, -⟩ := coherent representative target ⟨⟨step⟩⟩
  have represented : (representedBy chosen).normal representative = chosen :=
    if_pos same.symm
  rw [represented] at chosenStep
  exact stuck result chosenStep

/-- `{{@0!(0), 0}, for (@0) 0}` as the representative of its class. -/
theorem representedBy_nestedRedex_not_coherent :
    ¬ Coherent (representedBy nestedRedex) rhoRaw :=
  representedBy_not_coherent canonicalize_nestedRedex flatRedex_steps nestedRedex_stuck

/-- **Negative control.** Some normal forms for rho's equations, choosing a
non-canonical representative, are not coherent, and stepping them is not exact. -/
theorem noncanonical_representative_not_exact :
    ∃ forms : NormalForms rhoEquations, ¬ Coherent forms rhoRaw ∧
      ¬ ∀ source target, CanonicalSuccessorClasses.CanonicalStep forms rhoRaw
          (forms.key source) (forms.key target) ↔
        Modulo (equations := rhoEquations) rhoRaw source target := by
  obtain ⟨chosen, representative, target, same, step, stuck⟩ :=
    rhoStep_not_closed_under_canonical_equality
  have incoherent := representedBy_not_coherent same step stuck
  exact ⟨representedBy chosen, incoherent,
    fun exact => incoherent ((exact_iff_coherent _ rhoRaw).mp exact)⟩

/-- **Negative control.** Stepping the input as written, and normalizing the
result, is not exact. -/
theorem rawSource_not_exact :
    ¬ ∀ source target : Pattern,
      CanonicalRepresentativeStep.CanonicalStep source
          (canonicalize rhoReflectivePresentation target) ↔
        Modulo (equations := rhoEquations) rhoRaw source target := by
  obtain ⟨source, representative, target, same, step, stuck⟩ :=
    rhoStep_not_closed_under_canonical_equality
  intro exact
  obtain ⟨result, sourceStep, -⟩ := (exact source target).mpr
    ⟨⟨representative, target, same, ⟨step⟩, rhoEquations.iseqv.refl target⟩⟩
  exact stuck result sourceStep

/-- The stepper at the spelling `{{@0!(0), 0}, for (@0) 0}` lists nothing, while
its class has a successor. -/
theorem rawSource_enumeration_misses :
    rhoSuccessors nestedRedex = [] ∧
      Modulo (equations := rhoEquations) rhoRaw nestedRedex
        (.collection .hashBag [.apply "PZero" []] none) :=
  ⟨List.eq_nil_iff_forall_not_mem.mpr fun target member =>
      nestedRedex_stuck target (mem_rhoSuccessors.mp member),
    ⟨⟨flatRedex, _, canonicalize_nestedRedex, ⟨flatRedex_steps⟩,
      rhoEquations.iseqv.refl _⟩⟩⟩

/-! ## The closed process fiber -/

section ClosedProcesses

open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
  (RhoProcess rhoProcessEquations rhoProcessEquations_iff canonicalize_eq_of_rhoProcessEquations)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem
  (RhoClosedTerm rhoClosedTermWellSorted_process_iff)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalMatch (derivedCanonicalize_eq)

/-- Raw rho steps between closed processes. -/
abbrev rhoProcessRaw (source target : RhoProcess) : Type :=
  PLift (RhoStep source.1 target.1)

/-- Canonical forms are normal forms for the established closed-process
equations. -/
def rhoProcessForms : NormalForms rhoProcessEquations where
  normal := RhoClosedTerm.canonicalize
  sound term := Canonical.canonicalize_idempotent term.1
  same := canonicalize_eq_of_rhoProcessEquations

theorem rhoProcessEquations_iff_rhoEquations (first second : RhoProcess) :
    rhoProcessEquations.r first second ↔ rhoEquations.r first.1 second.1 := by
  rw [rhoProcessEquations_iff, rhoEquations_r, derivedCanonicalize_eq, derivedCanonicalize_eq]

/-- Coherence on closed processes: the canonical source's step stays closed. -/
theorem rhoProcess_coherent : Coherent rhoProcessForms rhoProcessRaw := by
  rintro source target ⟨⟨step⟩⟩
  obtain ⟨result, resultStep, same⟩ := rhoStep_canonicalize step
  rw [derivedCanonicalize_eq] at resultStep
  refine ⟨(rhoProcessForms.normal source).stepTarget resultStep, ⟨⟨resultStep⟩⟩, ?_⟩
  change Canonical.canonicalize result = Canonical.canonicalize target.1
  rw [← derivedCanonicalize_eq, ← derivedCanonicalize_eq]
  exact same

/-- Exactness on closed processes. -/
theorem rhoProcess_exact (source target : RhoProcess) :
    CanonicalSuccessorClasses.CanonicalStep rhoProcessForms rhoProcessRaw
        (rhoProcessForms.key source) (rhoProcessForms.key target) ↔
      Modulo (equations := rhoProcessEquations) rhoProcessRaw source target :=
  (exact_iff_coherent rhoProcessForms rhoProcessRaw).mpr rhoProcess_coherent source target

/-- On closed canonical forms, the contract's canonical step is
`CanonicalRepresentativeStep.CanonicalStep`. -/
theorem rhoProcess_canonicalStep_iff (source target : rhoProcessForms.Key) :
    CanonicalSuccessorClasses.CanonicalStep rhoProcessForms rhoProcessRaw source target ↔
      CanonicalRepresentativeStep.CanonicalStep source.val.1 target.val.1 := by
  constructor
  · rintro ⟨result, ⟨⟨step⟩⟩, rfl⟩
    exact ⟨result.1, step, derivedCanonicalize_eq result.1⟩
  · rintro ⟨result, step, same⟩
    refine ⟨source.val.stepTarget step, ⟨⟨step⟩⟩, Subtype.ext (Subtype.ext ?_)⟩
    exact (derivedCanonicalize_eq result).symm.trans same

/-- The stepper's answers from a closed process, as closed processes. -/
def rhoProcessSuccessors (source : RhoProcess) : List RhoProcess :=
  (rhoSuccessors source.1).pmap (fun _ step => source.stepTarget step)
    (fun _ member => mem_rhoSuccessors.mp member)

theorem mem_rhoProcessSuccessors {source target : RhoProcess} :
    target ∈ rhoProcessSuccessors source ↔ RhoStep source.1 target.1 := by
  simp only [rhoProcessSuccessors, List.mem_pmap]
  constructor
  · rintro ⟨pattern, member, rfl⟩
    exact mem_rhoSuccessors.mp member
  · intro step
    exact ⟨target.1, mem_rhoSuccessors.mpr step, rfl⟩

/-- Successor classes on closed processes. -/
theorem rhoProcess_successorClasses_iff_modulo (source target : RhoProcess) :
    rhoProcessForms.key target ∈
        (rhoProcessSuccessors source.canonicalize).map rhoProcessForms.key ↔
      Modulo (equations := rhoProcessEquations) rhoProcessRaw source target :=
  enumerate_iff_modulo rhoProcessForms rhoProcessRaw rhoProcess_coherent
    (fun key => rhoProcessSuccessors key.val)
    (fun _ _ => mem_rhoProcessSuccessors.trans ⟨fun step => ⟨⟨step⟩⟩, fun ⟨⟨step⟩⟩ => step⟩)
    source target

end ClosedProcesses

#print axioms rho_coherent
#print axioms rho_exact
#print axioms canonicalStep_iff
#print axioms canonicalStep_target_canonical
#print axioms modulo_iff_stepModulo
#print axioms stepModulo_iff_canonicalStep_of_contract
#print axioms rhoStepAt_within_depth
#print axioms mem_rhoSuccessors
#print axioms successorClasses_iff_modulo
#print axioms representedBy_not_coherent
#print axioms representedBy_nestedRedex_not_coherent
#print axioms noncanonical_representative_not_exact
#print axioms rawSource_not_exact
#print axioms rawSource_enumeration_misses
#print axioms rhoProcessEquations_iff_rhoEquations
#print axioms rhoProcess_coherent
#print axioms rhoProcess_exact
#print axioms rhoProcess_canonicalStep_iff
#print axioms mem_rhoProcessSuccessors
#print axioms rhoProcess_successorClasses_iff_modulo

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalSuccessorInstance
