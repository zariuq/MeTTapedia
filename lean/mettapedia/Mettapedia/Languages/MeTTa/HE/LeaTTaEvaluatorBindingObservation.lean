import Mettapedia.Languages.MeTTa.HE.LeaTTaEvaluatorConfigurationConformance
import Mettapedia.Languages.MeTTa.HE.LeaTTaExpectedBindingThreadingConformance
import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory

/-!
# Service-aware evaluator binding observation

Type selection uses structural type presentations, but general evaluation can
store abstract service payloads in bindings.  This module keeps the exact
finite presentation on the specification side and compares its observable
values with the runtime through the service-aware atom relation.

The observation is stated for every finite sub-scope of the declared public
scope.  This makes scope weakening structural while retaining one coherent
alpha witness for every joint readout, so variable sharing is not reduced to
independent pointwise claims.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaEvaluatorBindingObservation

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.CanonAbsorbsFreshening
open LeaTTaBridge
open LeaTTaEvaluatorConfigurationConformance
open LeaTTaExpectedBindingThreadingConformance
open LeaTTaMinimalInstructionConformance
open LeaTTaSpecConformance
open LeaTTaTypeConformance
open Spec.Eval.Minimal
open Spec.Type.Presentation
open Spec.Type.Presentation.Alpha
open Spec.Type.Presentation.Theory
open Spec.Type.RuntimeRefinement
open Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge

/-- A joint specification-side probe of all variables in one finite scope. -/
def bindingScopeProbe (scope : List String) : Atom :=
  .expression (scope.map Atom.var)

/-- Exact runtime syntax corresponding to a scope probe. -/
@[simp] theorem toLeaTTaAtom_bindingScopeProbe (scope : List String) :
    toLeaTTaAtom (bindingScopeProbe scope) =
      .expr (scope.map Metta.Atom.var) := by
  simp [bindingScopeProbe, toLeaTTaAtom, toLeaTTaAtoms_eq_map]

/-! ## Runtime alpha algebra -/

/-- One reachable runtime binding theory extends another when every model of
the output remains a model of the input.  This is the runtime-side analogue
of `EvaluatorBindingExtension.BindingTheoryExtends`; it is intentionally
semantic because reconciliation may change the concrete binding list. -/
def LeaBindingTheoryExtends
    (input output : Metta.Bindings) : Prop :=
  ∀ valuation, LeaBindingSatisfied valuation output →
    LeaBindingSatisfied valuation input

namespace LeaBindingTheoryExtends

@[simp] theorem refl (bindings : Metta.Bindings) :
    LeaBindingTheoryExtends bindings bindings := by
  intro _ satisfied
  exact satisfied

theorem trans {first second third : Metta.Bindings}
    (left : LeaBindingTheoryExtends first second)
    (right : LeaBindingTheoryExtends second third) :
    LeaBindingTheoryExtends first third := by
  intro valuation satisfied
  exact left valuation (right valuation satisfied)

/-- Every successful runtime merge extends its left input. -/
theorem merge_left {left right output : Metta.Bindings}
    (leftNoFloat : LeaBindingsNoFloat left)
    (rightNoFloat : LeaBindingsNoFloat right)
    (member : output ∈ Metta.Bindings.merge left right) :
    LeaBindingTheoryExtends left output := by
  intro valuation satisfied
  exact ((leaMerge_solution_iff valuation leftNoFloat rightNoFloat member).mp
    satisfied).1

/-- Every successful runtime merge extends its right input. -/
theorem merge_right {left right output : Metta.Bindings}
    (leftNoFloat : LeaBindingsNoFloat left)
    (rightNoFloat : LeaBindingsNoFloat right)
    (member : output ∈ Metta.Bindings.merge left right) :
    LeaBindingTheoryExtends right output := by
  intro valuation satisfied
  exact ((leaMerge_solution_iff valuation leftNoFloat rightNoFloat member).mp
    satisfied).2

end LeaBindingTheoryExtends

/-- The totalized head selection used by evaluator continuation merges is a
genuine merge result whenever the two input theories have a common model.
The selected result is reachable, loop-free, and extends both inputs; in
particular, the `getD` fallback is unreachable under these semantic
hypotheses. -/
theorem mergeHeadGetD_of_commonModel
    {left right fallback : Metta.Bindings}
    (leftInvariant : LeaRuntimeBindingInvariant left)
    (rightNoFloat : LeaBindingsNoFloat right)
    (commonModel : ∃ valuation : String → Metta.Atom,
      LeaBindingSatisfied valuation left ∧
        LeaBindingSatisfied valuation right) :
    let selected :=
      (Metta.Bindings.merge left right).head?.getD fallback
    selected ∈ Metta.Bindings.merge left right ∧
      LeaRuntimeBindingInvariant selected ∧
      LeaBindingTheoryExtends left selected ∧
      LeaBindingTheoryExtends right selected := by
  dsimp only
  obtain ⟨valuation, leftSatisfied, rightSatisfied⟩ := commonModel
  obtain ⟨witness, witnessMember, _witnessSatisfied, _witnessNoFloat⟩ :=
    LeaTTaMergeExistence.merge_exists_of_satisfied
      leftInvariant.noFloat rightNoFloat leftSatisfied rightSatisfied
  have selectedMember :
      (Metta.Bindings.merge left right).head?.getD fallback ∈
        Metta.Bindings.merge left right := by
    cases mergeEquation : Metta.Bindings.merge left right with
    | nil => simp [mergeEquation] at witnessMember
    | cons head tail => simp
  have selectedSatisfied : LeaBindingSatisfied valuation
      ((Metta.Bindings.merge left right).head?.getD fallback) :=
    (leaMerge_solution_iff valuation leftInvariant.noFloat rightNoFloat
      selectedMember).mpr ⟨leftSatisfied, rightSatisfied⟩
  have selectedAssignmentsNonVariable : LeaAssignmentsNonVariable
      ((Metta.Bindings.merge left right).head?.getD fallback) :=
    leaMerge_result_assignmentsNonVariable
      leftInvariant.assignmentsNonVariable selectedMember
  have selectedEqualitiesIrreflexive : LeaEqualitiesIrreflexive
      ((Metta.Bindings.merge left right).head?.getD fallback) :=
    leaMerge_result_equalitiesIrreflexive
      leftInvariant.equalitiesIrreflexive selectedMember
  have selectedLoopFree :
      Metta.Bindings.hasLoop
        ((Metta.Bindings.merge left right).head?.getD fallback) = false :=
    leaBindings_hasLoop_false_of_satisfied selectedSatisfied
      selectedAssignmentsNonVariable selectedEqualitiesIrreflexive
  exact ⟨selectedMember,
    leftInvariant.merge rightNoFloat selectedMember selectedLoopFree,
    LeaBindingTheoryExtends.merge_left leftInvariant.noFloat rightNoFloat
      selectedMember,
    LeaBindingTheoryExtends.merge_right leftInvariant.noFloat rightNoFloat
      selectedMember⟩

private theorem applyClassSolution_eq_renBy_of_variables
    (valuation : String → Metta.Atom) (rename : String → String) :
    ∀ atom : Metta.Atom,
      (∀ name, name ∈ atom.vars →
        valuation name = .var (rename name)) →
      applyClassSolution valuation atom = renBy rename atom := by
  intro atom
  induction atom with
  | sym name => simp [applyClassSolution, renBy]
  | var name =>
      intro agrees
      simpa [applyClassSolution, renBy] using
        agrees name (by simp [Metta.Atom.vars])
  | gnd value => simp [applyClassSolution, renBy]
  | expr atoms inductionHypothesis =>
      intro agrees
      simp only [applyClassSolution, renBy, Metta.Atom.expr.injEq]
      apply List.map_congr_left
      intro child childMember
      exact inductionHypothesis child childMember fun name member =>
        agrees name (by
          simp only [Metta.Atom.vars, List.mem_flatten, List.mem_map]
          exact ⟨child.vars, ⟨child, childMember, rfl⟩, member⟩)

private theorem applyClassSolution_congr_on_vars
    {left right : String → Metta.Atom} (atom : Metta.Atom)
    (agrees : ∀ name, name ∈ atom.vars → left name = right name) :
    applyClassSolution left atom = applyClassSolution right atom := by
  induction atom with
  | sym name => simp [applyClassSolution]
  | var name =>
      simpa [applyClassSolution] using
        agrees name (by simp [Metta.Atom.vars])
  | gnd value => simp [applyClassSolution]
  | expr atoms inductionHypothesis =>
      simp only [applyClassSolution, Metta.Atom.expr.injEq]
      apply List.map_congr_left
      intro child childMember
      exact inductionHypothesis child childMember fun name member =>
        agrees name (by
          simp only [Metta.Atom.vars, List.mem_flatten, List.mem_map]
          exact ⟨child.vars, ⟨child, childMember, rfl⟩, member⟩)

/-- Satisfaction of one runtime binding theory depends only on the variables
that occur in that theory.  This is the semantic support lemma needed when a
projection keeps every input variable but intentionally discards unrelated
private variables produced downstream. -/
theorem leaBindingSatisfied_congr_on_vars
    {left right : String → Metta.Atom} {bindings : Metta.Bindings}
    (agrees : ∀ name, name ∈ bindings.vars → left name = right name)
    (satisfied : LeaBindingSatisfied left bindings) :
    LeaBindingSatisfied right bindings := by
  constructor
  · intro name value member
    have nameMember : name ∈ bindings.vars := by
      simp only [Metta.Bindings.vars, List.mem_eraseDups,
        List.mem_flatMap]
      exact ⟨.val name value, member, by simp⟩
    have valueAgreement :
        applyClassSolution left value = applyClassSolution right value :=
      applyClassSolution_congr_on_vars value fun candidate candidateMember =>
        agrees candidate (by
          simp only [Metta.Bindings.vars, List.mem_eraseDups,
            List.mem_flatMap]
          exact ⟨.val name value, member, by simp [candidateMember]⟩)
    calc
      right name = left name := (agrees name nameMember).symm
      _ = applyClassSolution left value := satisfied.1 name value member
      _ = applyClassSolution right value := valueAgreement
  · intro first second member
    have firstMember : first ∈ bindings.vars := by
      simp only [Metta.Bindings.vars, List.mem_eraseDups,
        List.mem_flatMap]
      exact ⟨.eq first second, member, by simp⟩
    have secondMember : second ∈ bindings.vars := by
      simp only [Metta.Bindings.vars, List.mem_eraseDups,
        List.mem_flatMap]
      exact ⟨.eq first second, member, by simp⟩
    calc
      right first = left first := (agrees first firstMember).symm
      _ = left second := satisfied.2 first second member
      _ = right second := agrees second secondMember

/-- Projecting a reachable output remains an extension of an earlier input
theory whenever the projection retains every variable occurring in that
input.  No claim is made that the projected binding list mentions only the
requested variables: equality aliases may retain an out-of-scope right-hand
side, as required by `restrictBnd`'s transitive-chain semantics. -/
theorem restrictBnd_extends_of_input_vars
    {input output : Metta.Bindings} {scope : List String}
    (outputInvariant : LeaRuntimeBindingInvariant output)
    (extension : LeaBindingTheoryExtends input output)
    (inputRetained : ∀ name, name ∈ input.vars → name ∈ scope) :
    LeaBindingTheoryExtends input
      (Metta.Minimal.restrictBnd scope output) := by
  intro valuation projectedSatisfied
  obtain ⟨completed, completedSatisfied, completedAgreement⟩ :=
    LeaTTaExpectedBindingThreadingConformance.restrictBnd_exists_satisfied_extension
      outputInvariant scope valuation projectedSatisfied
  apply leaBindingSatisfied_congr_on_vars
    (left := completed) (right := valuation)
  · intro name member
    exact completedAgreement name (inputRetained name member)
  · exact extension completed completedSatisfied

/-- The expected-application worker's projection retains every variable
already present in its public input theory.  Argument variables stay first;
input-only variables occupy the deduplicated suffix. -/
theorem expectedApplicationRetentionScope_input_vars
    (input : Metta.Bindings) (arguments : List Metta.Atom) :
    ∀ name, name ∈ input.vars →
      name ∈ Metta.Minimal.expectedApplicationRetentionScope input arguments := by
  intro name member
  cases input with
  | nil => simp [Metta.Bindings.vars] at member
  | cons relation rest =>
      unfold Metta.Minimal.expectedApplicationRetentionScope
      by_cases inArguments : name ∈ arguments.flatMap Metta.Atom.vars
      · exact List.mem_append_left _ inArguments
      · apply List.mem_append_right (arguments.flatMap Metta.Atom.vars)
        have containsFalse :
            (arguments.flatMap Metta.Atom.vars).contains name = false :=
          Bool.eq_false_iff.mpr fun containsTrue =>
            inArguments (List.contains_iff_mem.mp containsTrue)
        exact List.mem_filter.mpr ⟨member, by rw [containsFalse]; rfl⟩

/-- Every variable occurring in an application argument is retained by the
expected-application worker, independently of whether the initial binding
record is empty. -/
theorem expectedApplicationRetentionScope_argument_vars
    (input : Metta.Bindings) (arguments : List Metta.Atom) :
    ∀ name, name ∈ arguments.flatMap Metta.Atom.vars →
      name ∈ Metta.Minimal.expectedApplicationRetentionScope input arguments := by
  intro name member
  cases input with
  | nil => exact member
  | cons relation rest =>
      unfold Metta.Minimal.expectedApplicationRetentionScope
      exact List.mem_append_left _ member

/-- Projecting an extending worker result through the repaired application
scope still preserves the complete public input theory. -/
theorem restrictBnd_expectedApplicationRetentionScope_extends
    {input output : Metta.Bindings} (arguments : List Metta.Atom)
    (outputInvariant : LeaRuntimeBindingInvariant output)
    (extension : LeaBindingTheoryExtends input output) :
    LeaBindingTheoryExtends input
      (Metta.Minimal.restrictBnd
        (Metta.Minimal.expectedApplicationRetentionScope input arguments)
        output) :=
  restrictBnd_extends_of_input_vars outputInvariant extension
    (expectedApplicationRetentionScope_input_vars input arguments)

mutual

private theorem runtimeValuation_fixes_variable_of_apply_eq_self
    (valuation : String → Metta.Atom) :
    ∀ (atom : Metta.Atom) (name : String),
      applyClassSolution valuation atom = atom →
      name ∈ atom.vars → valuation name = .var name := by
  intro atom name equation member
  cases atom with
  | sym symbol => simp [Metta.Atom.vars] at member
  | var variableName =>
      simp only [Metta.Atom.vars, List.mem_singleton] at member
      subst name
      simpa [applyClassSolution] using equation
  | gnd value => simp [Metta.Atom.vars] at member
  | expr atoms =>
      apply runtimeValuation_fixes_list_variable_of_apply_eq_self
        valuation atoms name
      · have equation' :
            Metta.Atom.expr
                (atoms.map (applyClassSolution valuation)) =
              Metta.Atom.expr atoms := by
          simpa [applyClassSolution] using equation
        exact Metta.Atom.expr.inj equation'
      · simpa [Metta.Atom.vars] using member

private theorem runtimeValuation_fixes_list_variable_of_apply_eq_self
    (valuation : String → Metta.Atom) :
    ∀ (atoms : List Metta.Atom) (name : String),
      atoms.map (applyClassSolution valuation) = atoms →
      name ∈ (atoms.map Metta.Atom.vars).flatten →
        valuation name = .var name := by
  intro atoms name equation member
  cases atoms with
  | nil => simp at member
  | cons atom atoms =>
      simp only [List.map_cons, List.cons.injEq] at equation
      simp only [List.map_cons, List.flatten_cons,
        List.mem_append] at member
      rcases member with member | member
      · exact runtimeValuation_fixes_variable_of_apply_eq_self
          valuation atom name equation.1 member
      · exact runtimeValuation_fixes_list_variable_of_apply_eq_self
          valuation atoms name equation.2 member

end

/-- Two finite runtime atoms that are homomorphic instances of one another
differ by one coherent permutation of their variable leaves.  Grounded
payloads are constants, so opaque binding values are preserved exactly. -/
theorem runtimeRenaming_of_mutual_instances
    {left right : Metta.Atom}
    (rightInstance : ∃ forward : String → Metta.Atom,
      applyClassSolution forward left = right)
    (leftInstance : ∃ backward : String → Metta.Atom,
      applyClassSolution backward right = left) :
    ∃ permutation : Equiv.Perm String,
      right = renBy permutation left := by
  classical
  obtain ⟨forward, forwardEquation⟩ := rightInstance
  obtain ⟨backward, backwardEquation⟩ := leftInstance
  have composedEquation :
      applyClassSolution
          (fun name => applyClassSolution backward (forward name)) left =
        left := by
    rw [← Spec.Match.ModelTheory.applyClassSolution_comp,
      forwardEquation, backwardEquation]
  let SourceVariable := {name : String // name ∈ left.vars}
  have forwardIsVariable (name : SourceVariable) :
      ∃ target, forward name.1 = .var target := by
    have recovered :=
      runtimeValuation_fixes_variable_of_apply_eq_self
        (fun candidateName =>
          applyClassSolution backward (forward candidateName))
        left name.1 composedEquation name.2
    cases equation : forward name.1 with
    | sym symbol => simp [equation, applyClassSolution] at recovered
    | var target => exact ⟨target, rfl⟩
    | gnd value => simp [equation, applyClassSolution] at recovered
    | expr atoms => simp [equation, applyClassSolution] at recovered
  let target : SourceVariable → String := fun name =>
    Classical.choose (forwardIsVariable name)
  have targetEquation (name : SourceVariable) :
      forward name.1 = .var (target name) :=
    Classical.choose_spec (forwardIsVariable name)
  have targetInjective : Function.Injective target := by
    intro first second targetsEqual
    apply Subtype.ext
    have firstRecovered :=
      runtimeValuation_fixes_variable_of_apply_eq_self
        (fun candidateName =>
          applyClassSolution backward (forward candidateName))
        left first.1 composedEquation first.2
    have secondRecovered :=
      runtimeValuation_fixes_variable_of_apply_eq_self
        (fun candidateName =>
          applyClassSolution backward (forward candidateName))
        left second.1 composedEquation second.2
    rw [targetEquation first] at firstRecovered
    rw [targetEquation second] at secondRecovered
    rw [targetsEqual] at firstRecovered
    simp only [applyClassSolution] at firstRecovered secondRecovered
    exact Metta.Atom.var.inj
      (firstRecovered.symm.trans secondRecovered)
  obtain ⟨permutation, extensionLaw⟩ :=
    Equiv.Perm.exists_extending_pair
      (fun name : SourceVariable => name.1) target
      Subtype.val_injective targetInjective
  have forwardOnVariables (name : String) (member : name ∈ left.vars) :
      forward name = .var (permutation name) := by
    let sourceName : SourceVariable := ⟨name, member⟩
    calc
      forward name = .var (target sourceName) := targetEquation sourceName
      _ = .var (permutation sourceName.1) := by
        rw [(extensionLaw sourceName).symm]
      _ = .var (permutation name) := rfl
  refine ⟨permutation, ?_⟩
  rw [← forwardEquation]
  exact applyClassSolution_eq_renBy_of_variables
    forward permutation left forwardOnVariables

mutual

/-- Atom/runtime correspondence is equivariant under one shared injective
renaming.  Opaque service payloads remain untouched. -/
theorem AtomRuntimeRel.renamed
    {services : Services} {atom : Atom} {runtimeAtom : Metta.Atom}
    (relation : AtomRuntimeRel services atom runtimeAtom)
    (permutation : Equiv.Perm String) :
    AtomRuntimeRel services
      (renameTypeVars permutation atom) (renBy permutation runtimeAtom) := by
  cases relation with
  | symbol name =>
      simpa [renameTypeVars, renBy] using
        (AtomRuntimeRel.symbol (services := services) name)
  | «variable» name =>
      simpa [renameTypeVars, renBy] using
        (AtomRuntimeRel.variable (services := services) (permutation name))
  | grounded value notPayload =>
      simpa [renameTypeVars, renBy] using
        (AtomRuntimeRel.grounded (services := services) value notPayload)
  | bindingPayload bindings runtimeBindings equivalent =>
      simpa [renameTypeVars, renBy] using
        (AtomRuntimeRel.bindingPayload (services := services)
          bindings runtimeBindings equivalent)
  | expression atoms runtimeAtoms related =>
      simpa [renameTypeVars, renBy] using
        (AtomRuntimeRel.expression _ _
          (atomRuntimeRelList_renamed related permutation))

/-- Ordered-list companion of `AtomRuntimeRel.renamed`. -/
theorem atomRuntimeRelList_renamed
    {services : Services} {atoms : List Atom}
    {runtimeAtoms : List Metta.Atom}
    (relation : List.Forall₂ (AtomRuntimeRel services) atoms runtimeAtoms)
    (permutation : Equiv.Perm String) :
    List.Forall₂ (AtomRuntimeRel services)
      (atoms.map (renameTypeVars permutation))
      (runtimeAtoms.map (renBy permutation)) := by
  cases relation with
  | nil => exact .nil
  | cons head tail =>
      exact .cons (AtomRuntimeRel.renamed head permutation)
        (atomRuntimeRelList_renamed tail permutation)

end

/-- Canonical evaluator projection preserves the instantiation of any atom
whose variables are retained, up to one coherent private-variable
permutation.  This is the general transport theorem; joint scope probes are
its list-shaped specialization. -/
theorem restrictBnd_atom_renaming
    {bindings : Metta.Bindings} {atom : Metta.Atom}
    (invariant : LeaRuntimeBindingInvariant bindings)
    (scopeVars : List String)
    (variablesRetained : ∀ name, name ∈ atom.vars → name ∈ scopeVars) :
    ∃ permutation : Equiv.Perm String,
      Metta.instantiate (Metta.Minimal.restrictBnd scopeVars bindings) atom =
        renBy permutation (Metta.instantiate bindings atom) := by
  let projected := Metta.Minimal.restrictBnd scopeVars bindings
  have projectedInvariant : LeaRuntimeBindingInvariant projected :=
    restrictBnd_runtimeInvariant invariant scopeVars
  have rightInstance : ∃ forward : String → Metta.Atom,
      applyClassSolution forward
          (applyClassSolution (leaClassSolution bindings) atom) =
        applyClassSolution (leaClassSolution projected) atom := by
    obtain ⟨complete, completeSatisfied, agrees⟩ :=
      restrictBnd_exists_satisfied_extension invariant scopeVars
        (leaClassSolution projected) projectedInvariant.canonical.1
    have refines := invariant.canonical.2 complete completeSatisfied
    obtain ⟨forward, forwardEquation⟩ :=
      refines.apply_eq_applyClassSolution
    refine ⟨forward, ?_⟩
    calc
      applyClassSolution forward
          (applyClassSolution (leaClassSolution bindings) atom) =
          applyClassSolution complete atom := (forwardEquation atom).symm
      _ = applyClassSolution (leaClassSolution projected) atom :=
        applyClassSolution_congr_on_vars atom fun name member =>
          agrees name (variablesRetained name member)
  have leftInstance : ∃ backward : String → Metta.Atom,
      applyClassSolution backward
          (applyClassSolution (leaClassSolution projected) atom) =
        applyClassSolution (leaClassSolution bindings) atom := by
    have originalSatisfiesProjected :
        LeaBindingSatisfied (leaClassSolution bindings) projected :=
      restrictBnd_satisfied_of_satisfied invariant.noFloat
        invariant.canonical.1 scopeVars
    have refines := projectedInvariant.canonical.2
      (leaClassSolution bindings) originalSatisfiesProjected
    obtain ⟨backward, backwardEquation⟩ :=
      refines.apply_eq_applyClassSolution
    exact ⟨backward, (backwardEquation atom).symm⟩
  obtain ⟨permutation, equation⟩ :=
    runtimeRenaming_of_mutual_instances rightInstance leftInstance
  refine ⟨permutation, ?_⟩
  simpa [projected, applyClassSolution_lea_eq_instantiate] using equation

/-- Canonical evaluator projection preserves every requested joint readout
up to one coherent private-variable permutation.  The side condition is
sharp: a projection cannot preserve a variable it was not asked to retain. -/
theorem restrictBnd_scopeProbe_renaming
    {bindings : Metta.Bindings}
    (invariant : LeaRuntimeBindingInvariant bindings)
    (scopeVars observedScope : List String)
    (subset : ∀ name, name ∈ observedScope → name ∈ scopeVars) :
    ∃ permutation : Equiv.Perm String,
      Metta.instantiate (Metta.Minimal.restrictBnd scopeVars bindings)
          (.expr (observedScope.map Metta.Atom.var)) =
        renBy permutation
          (Metta.instantiate bindings
            (.expr (observedScope.map Metta.Atom.var))) := by
  apply restrictBnd_atom_renaming invariant scopeVars
  intro name member
  simp [Metta.Atom.vars] at member
  exact subset name member

/-- Merging an incoming runtime theory with the visible projection of an
extending output recovers the complete output observation at that scope.

The result is semantic rather than syntactic.  A projected binding may retain
an out-of-scope alias endpoint, and reconciliation may choose a different
private representative.  Principal-model transport proves that the two joint
scope readouts are mutual instances; one coherent permutation then relates
their variable leaves. -/
theorem merge_restrictBnd_scopeProbe_renaming
    {incoming output merged : Metta.Bindings}
    (incomingInvariant : LeaRuntimeBindingInvariant incoming)
    (outputInvariant : LeaRuntimeBindingInvariant output)
    (extension : LeaBindingTheoryExtends incoming output)
    (scope observedScope : List String)
    (observedRetained : ∀ name, name ∈ observedScope → name ∈ scope)
    (member : merged ∈ Metta.Bindings.merge incoming
      (Metta.Minimal.restrictBnd scope output))
    (mergedLoopFree : merged.hasLoop = false) :
    ∃ permutation : Equiv.Perm String,
      Metta.instantiate merged
          (.expr (observedScope.map Metta.Atom.var)) =
        renBy permutation
          (Metta.instantiate output
            (.expr (observedScope.map Metta.Atom.var))) := by
  let projected := Metta.Minimal.restrictBnd scope output
  have projectedInvariant : LeaRuntimeBindingInvariant projected :=
    restrictBnd_runtimeInvariant outputInvariant scope
  have mergedInvariant : LeaRuntimeBindingInvariant merged :=
    incomingInvariant.merge projectedInvariant.noFloat member mergedLoopFree
  let probe := Metta.Atom.expr (observedScope.map Metta.Atom.var)
  have probeVars : ∀ name, name ∈ probe.vars → name ∈ scope := by
    intro name variableMember
    simp [probe, Metta.Atom.vars] at variableMember
    exact observedRetained name variableMember
  have mergedInstance : ∃ forward : String → Metta.Atom,
      applyClassSolution forward
          (applyClassSolution (leaClassSolution output) probe) =
        applyClassSolution (leaClassSolution merged) probe := by
    have mergedSatisfiesProjected :
        LeaBindingSatisfied (leaClassSolution merged) projected :=
      ((leaMerge_solution_iff (leaClassSolution merged)
        incomingInvariant.noFloat projectedInvariant.noFloat member).mp
          mergedInvariant.canonical.1).2
    obtain ⟨complete, completeSatisfied, agrees⟩ :=
      restrictBnd_exists_satisfied_extension outputInvariant scope
        (leaClassSolution merged) mergedSatisfiesProjected
    have refines := outputInvariant.canonical.2 complete completeSatisfied
    obtain ⟨forward, forwardEquation⟩ :=
      refines.apply_eq_applyClassSolution
    refine ⟨forward, ?_⟩
    calc
      applyClassSolution forward
          (applyClassSolution (leaClassSolution output) probe) =
          applyClassSolution complete probe := (forwardEquation probe).symm
      _ = applyClassSolution (leaClassSolution merged) probe :=
        applyClassSolution_congr_on_vars probe fun name variableMember =>
          agrees name (probeVars name variableMember)
  have outputInstance : ∃ backward : String → Metta.Atom,
      applyClassSolution backward
          (applyClassSolution (leaClassSolution merged) probe) =
        applyClassSolution (leaClassSolution output) probe := by
    have outputSatisfiesIncoming :
        LeaBindingSatisfied (leaClassSolution output) incoming :=
      extension (leaClassSolution output) outputInvariant.canonical.1
    have outputSatisfiesProjected :
        LeaBindingSatisfied (leaClassSolution output) projected :=
      restrictBnd_satisfied_of_satisfied outputInvariant.noFloat
        outputInvariant.canonical.1 scope
    have outputSatisfiesMerged :
        LeaBindingSatisfied (leaClassSolution output) merged :=
      (leaMerge_solution_iff (leaClassSolution output)
        incomingInvariant.noFloat projectedInvariant.noFloat member).mpr
          ⟨outputSatisfiesIncoming, outputSatisfiesProjected⟩
    have refines := mergedInvariant.canonical.2
      (leaClassSolution output) outputSatisfiesMerged
    obtain ⟨backward, backwardEquation⟩ :=
      refines.apply_eq_applyClassSolution
    exact ⟨backward, (backwardEquation probe).symm⟩
  obtain ⟨permutation, equation⟩ :=
    runtimeRenaming_of_mutual_instances mergedInstance outputInstance
  refine ⟨permutation, ?_⟩
  simpa [probe, applyClassSolution_lea_eq_instantiate] using equation

/-- Merging an extending output back into its input preserves every joint
scope readout up to one coherent private-variable permutation.  This is the
merge-before-projection law used by `evaluateExpectedApplicationFrom`; it is
deliberately separate from `merge_restrictBnd_scopeProbe_renaming`, whose
runtime order is projection before merge. -/
theorem merge_extending_scopeProbe_renaming
    {incoming output merged : Metta.Bindings}
    (incomingInvariant : LeaRuntimeBindingInvariant incoming)
    (outputInvariant : LeaRuntimeBindingInvariant output)
    (extension : LeaBindingTheoryExtends incoming output)
    (observedScope : List String)
    (member : merged ∈ Metta.Bindings.merge incoming output)
    (mergedLoopFree : merged.hasLoop = false) :
    ∃ permutation : Equiv.Perm String,
      Metta.instantiate merged
          (.expr (observedScope.map Metta.Atom.var)) =
        renBy permutation
          (Metta.instantiate output
            (.expr (observedScope.map Metta.Atom.var))) := by
  have mergedInvariant : LeaRuntimeBindingInvariant merged :=
    incomingInvariant.merge outputInvariant.noFloat member mergedLoopFree
  let probe := Metta.Atom.expr (observedScope.map Metta.Atom.var)
  have mergedInstance : ∃ forward : String → Metta.Atom,
      applyClassSolution forward
          (applyClassSolution (leaClassSolution output) probe) =
        applyClassSolution (leaClassSolution merged) probe := by
    have mergedSatisfiesOutput :
        LeaBindingSatisfied (leaClassSolution merged) output :=
      ((leaMerge_solution_iff (leaClassSolution merged)
        incomingInvariant.noFloat outputInvariant.noFloat member).mp
          mergedInvariant.canonical.1).2
    have refines := outputInvariant.canonical.2
      (leaClassSolution merged) mergedSatisfiesOutput
    obtain ⟨forward, forwardEquation⟩ :=
      refines.apply_eq_applyClassSolution
    exact ⟨forward, (forwardEquation probe).symm⟩
  have outputInstance : ∃ backward : String → Metta.Atom,
      applyClassSolution backward
          (applyClassSolution (leaClassSolution merged) probe) =
        applyClassSolution (leaClassSolution output) probe := by
    have outputSatisfiesIncoming :
        LeaBindingSatisfied (leaClassSolution output) incoming :=
      extension (leaClassSolution output) outputInvariant.canonical.1
    have outputSatisfiesMerged :
        LeaBindingSatisfied (leaClassSolution output) merged :=
      (leaMerge_solution_iff (leaClassSolution output)
        incomingInvariant.noFloat outputInvariant.noFloat member).mpr
          ⟨outputSatisfiesIncoming, outputInvariant.canonical.1⟩
    have refines := mergedInvariant.canonical.2
      (leaClassSolution output) outputSatisfiesMerged
    obtain ⟨backward, backwardEquation⟩ :=
      refines.apply_eq_applyClassSolution
    exact ⟨backward, (backwardEquation probe).symm⟩
  obtain ⟨permutation, equation⟩ :=
    runtimeRenaming_of_mutual_instances mergedInstance outputInstance
  refine ⟨permutation, ?_⟩
  simpa [probe, applyClassSolution_lea_eq_instantiate] using equation

/-- A normal native presentation and one reachable runtime binding state have
the same service-aware observations throughout a declared public scope.

Quantifying over sub-scopes makes the carrier contravariant in `publicScope`
without choosing an order or deduplicating names.  Each individual readout is
joint, so its private alpha witness must preserve sharing across every
position in that readout. -/
structure ScopedPresentationRuntimeObservationRel
    (services : Services) (publicScope : List String)
    (presentation : TypeSubst) (runtimeBindings : Metta.Bindings) : Prop where
  normal : presentation.Normal
  runtime : LeaRuntimeBindingInvariant runtimeBindings
  observes : ∀ observedScope,
    (∀ name, name ∈ observedScope → name ∈ publicScope) →
      AlphaAtomRuntimeRel services
        (presentation.apply (bindingScopeProbe observedScope))
        (Metta.instantiate runtimeBindings
          (toLeaTTaAtom (bindingScopeProbe observedScope)))

/-- Exact native binding theory plus service-aware scoped runtime
observation.  Exactness is intra-specification; only the observation field
crosses the implementation boundary. -/
def ServiceAwareScopedEvaluatorBindingRuntimeRel
    (services : Services) (scope : List String)
    (specBindings : Bindings) (runtimeBindings : Metta.Bindings) : Prop :=
  ∃ presentation : TypeSubst,
    (∀ valuation,
      TypeSubstSatisfied valuation presentation ↔
        TypeBindingSatisfied valuation specBindings) ∧
      ScopedPresentationRuntimeObservationRel
        services scope presentation runtimeBindings

namespace ScopedPresentationRuntimeObservationRel

/-- Binding observation restricts contravariantly with its public scope. -/
theorem mono
    {services : Services} {large small : List String}
    {presentation : TypeSubst} {runtimeBindings : Metta.Bindings}
    (relation : ScopedPresentationRuntimeObservationRel
      services large presentation runtimeBindings)
    (subset : ∀ name, name ∈ small → name ∈ large) :
    ScopedPresentationRuntimeObservationRel
      services small presentation runtimeBindings := by
  refine ⟨relation.normal, relation.runtime, ?_⟩
  intro observedScope observedSubset
  exact relation.observes observedScope fun name member =>
    subset name (observedSubset name member)

/-- Runtime binding projection preserves a scoped service-aware observation
when every public variable is retained.  The result may choose a different
private representative, so the proof composes one coherent alpha witness
rather than asserting literal readout equality. -/
theorem restrictBnd
    {services : Services} {publicScope scopeVars : List String}
    {presentation : TypeSubst} {runtimeBindings : Metta.Bindings}
    (relation : ScopedPresentationRuntimeObservationRel
      services publicScope presentation runtimeBindings)
    (publicRetained : ∀ name, name ∈ publicScope → name ∈ scopeVars) :
    ScopedPresentationRuntimeObservationRel services publicScope presentation
      (Metta.Minimal.restrictBnd scopeVars runtimeBindings) := by
  refine ⟨relation.normal,
    LeaTTaExpectedBindingThreadingConformance.restrictBnd_runtimeInvariant
      relation.runtime scopeVars, ?_⟩
  intro observedScope observedPublic
  rcases relation.observes observedScope observedPublic with
    ⟨observed, alpha, runtime⟩
  obtain ⟨permutation, projectedEquation⟩ :=
    restrictBnd_scopeProbe_renaming relation.runtime scopeVars observedScope
      fun name member => publicRetained name (observedPublic name member)
  have renamedRuntime := AtomRuntimeRel.renamed runtime permutation
  refine ⟨renameTypeVars permutation observed,
    Spec.Type.Presentation.ScopeObservation.ObservedTypeAlphaRel.trans
      alpha ⟨observed, TypeVariableRenamingOf.refl observed,
        ⟨permutation, permutation.injective, rfl⟩⟩, ?_⟩
  have renamedRuntime' : AtomRuntimeRel services
      (renameTypeVars permutation observed)
      (renBy permutation
        (Metta.instantiate runtimeBindings
          (.expr (observedScope.map Metta.Atom.var)))) := by
    simpa using renamedRuntime
  rw [toLeaTTaAtom_bindingScopeProbe, projectedEquation]
  exact renamedRuntime'

/-- Merging a semantically extending output back into its input preserves
the complete scoped observation.  The merge may choose a different private
representative, so equality is intentionally replaced by one coherent
renaming on each joint scope probe. -/
theorem merge_extending
    {services : Services} {publicScope : List String}
    {presentation : TypeSubst}
    {incoming output merged : Metta.Bindings}
    (relation : ScopedPresentationRuntimeObservationRel
      services publicScope presentation output)
    (incomingInvariant : LeaRuntimeBindingInvariant incoming)
    (extension : LeaBindingTheoryExtends incoming output)
    (member : merged ∈ Metta.Bindings.merge incoming output)
    (mergedLoopFree : merged.hasLoop = false) :
    ScopedPresentationRuntimeObservationRel
      services publicScope presentation merged := by
  have mergedInvariant : LeaRuntimeBindingInvariant merged :=
    incomingInvariant.merge relation.runtime.noFloat member mergedLoopFree
  refine ⟨relation.normal, mergedInvariant, ?_⟩
  intro observedScope observedPublic
  rcases relation.observes observedScope observedPublic with
    ⟨observed, alpha, runtime⟩
  obtain ⟨permutation, mergedEquation⟩ :=
    merge_extending_scopeProbe_renaming incomingInvariant relation.runtime
      extension observedScope member mergedLoopFree
  have renamedRuntime := AtomRuntimeRel.renamed runtime permutation
  refine ⟨renameTypeVars permutation observed,
    Spec.Type.Presentation.ScopeObservation.ObservedTypeAlphaRel.trans
      alpha ⟨observed, TypeVariableRenamingOf.refl observed,
        ⟨permutation, permutation.injective, rfl⟩⟩, ?_⟩
  rw [toLeaTTaAtom_bindingScopeProbe, mergedEquation]
  simpa using renamedRuntime

/-- The expected-application order is merge first, project second.  Its
scoped observation follows by the extending-merge theorem and projection
antitonicity, provided the projection retains the declared public scope. -/
theorem merge_then_restrict_retaining
    {services : Services} {publicScope retainedScope : List String}
    {presentation : TypeSubst}
    {incoming output merged : Metta.Bindings}
    (relation : ScopedPresentationRuntimeObservationRel
      services publicScope presentation output)
    (incomingInvariant : LeaRuntimeBindingInvariant incoming)
    (extension : LeaBindingTheoryExtends incoming output)
    (publicRetained : ∀ name, name ∈ publicScope → name ∈ retainedScope)
    (member : merged ∈ Metta.Bindings.merge incoming output)
    (mergedLoopFree : merged.hasLoop = false) :
    ScopedPresentationRuntimeObservationRel services publicScope presentation
      (Metta.Minimal.restrictBnd retainedScope merged) :=
  (relation.merge_extending incomingInvariant extension member
    mergedLoopFree).restrictBnd publicRetained

/-- Continuation-time merge preserves the complete extending output at a
declared public scope when the executable projects through any larger
retention scope.  Keeping the two scopes separate matches the runtime: the
worker owns retention, while its caller owns observation. -/
theorem merge_restrictBnd_retaining
    {services : Services} {publicScope retainedScope : List String}
    {presentation : TypeSubst}
    {incoming output merged : Metta.Bindings}
    (relation : ScopedPresentationRuntimeObservationRel
      services publicScope presentation output)
    (incomingInvariant : LeaRuntimeBindingInvariant incoming)
    (extension : LeaBindingTheoryExtends incoming output)
    (publicRetained : ∀ name, name ∈ publicScope → name ∈ retainedScope)
    (member : merged ∈ Metta.Bindings.merge incoming
      (Metta.Minimal.restrictBnd retainedScope output))
    (mergedLoopFree : merged.hasLoop = false) :
    ScopedPresentationRuntimeObservationRel
      services publicScope presentation merged := by
  have mergedInvariant : LeaRuntimeBindingInvariant merged :=
    incomingInvariant.merge
      (restrictBnd_runtimeInvariant relation.runtime retainedScope).noFloat
      member mergedLoopFree
  refine ⟨relation.normal, mergedInvariant, ?_⟩
  intro observedScope observedPublic
  rcases relation.observes observedScope observedPublic with
    ⟨observed, alpha, runtime⟩
  obtain ⟨permutation, mergedEquation⟩ :=
    merge_restrictBnd_scopeProbe_renaming incomingInvariant relation.runtime
      extension retainedScope observedScope
        (fun name membership => publicRetained name
          (observedPublic name membership))
        member mergedLoopFree
  have renamedRuntime := AtomRuntimeRel.renamed runtime permutation
  refine ⟨renameTypeVars permutation observed,
    Spec.Type.Presentation.ScopeObservation.ObservedTypeAlphaRel.trans
      alpha ⟨observed, TypeVariableRenamingOf.refl observed,
        ⟨permutation, permutation.injective, rfl⟩⟩, ?_⟩
  rw [toLeaTTaAtom_bindingScopeProbe, mergedEquation]
  simpa using renamedRuntime

/-- Specialization in which the public observation scope is also the
executable projection scope. -/
theorem merge_restrictBnd
    {services : Services} {publicScope : List String}
    {presentation : TypeSubst}
    {incoming output merged : Metta.Bindings}
    (relation : ScopedPresentationRuntimeObservationRel
      services publicScope presentation output)
    (incomingInvariant : LeaRuntimeBindingInvariant incoming)
    (extension : LeaBindingTheoryExtends incoming output)
    (member : merged ∈ Metta.Bindings.merge incoming
      (Metta.Minimal.restrictBnd publicScope output))
    (mergedLoopFree : merged.hasLoop = false) :
    ScopedPresentationRuntimeObservationRel
      services publicScope presentation merged :=
  merge_restrictBnd_retaining relation incomingInvariant extension
    (fun _ membership => membership) member mergedLoopFree

end ScopedPresentationRuntimeObservationRel

namespace ServiceAwareScopedEvaluatorBindingRuntimeRel

/-- Service-aware evaluator binding observation is contravariant in scope. -/
theorem mono
    {services : Services} {large small : List String}
    {specBindings : Bindings} {runtimeBindings : Metta.Bindings}
    (relation : ServiceAwareScopedEvaluatorBindingRuntimeRel
      services large specBindings runtimeBindings)
    (subset : ∀ name, name ∈ small → name ∈ large) :
    ServiceAwareScopedEvaluatorBindingRuntimeRel
      services small specBindings runtimeBindings := by
  rcases relation with ⟨presentation, specSolutions, observation⟩
  exact ⟨presentation, specSolutions, observation.mono subset⟩

/-- Exact specification binding theory is unchanged by evaluator-side
projection; the runtime observation transports at precisely the variables
retained by that projection. -/
theorem restrictBnd
    {services : Services} {scope scopeVars : List String}
    {specBindings : Bindings} {runtimeBindings : Metta.Bindings}
    (relation : ServiceAwareScopedEvaluatorBindingRuntimeRel
      services scope specBindings runtimeBindings)
    (scopeRetained : ∀ name, name ∈ scope → name ∈ scopeVars) :
    ServiceAwareScopedEvaluatorBindingRuntimeRel services scope specBindings
      (Metta.Minimal.restrictBnd scopeVars runtimeBindings) := by
  rcases relation with ⟨presentation, specSolutions, observation⟩
  exact ⟨presentation, specSolutions,
    observation.restrictBnd scopeRetained⟩

/-- Exact specification binding theory survives the worker's actual
merge-before-projection order. -/
theorem merge_then_restrict_retaining
    {services : Services} {scope retainedScope : List String}
    {specBindings : Bindings}
    {incoming output merged : Metta.Bindings}
    (relation : ServiceAwareScopedEvaluatorBindingRuntimeRel
      services scope specBindings output)
    (incomingInvariant : LeaRuntimeBindingInvariant incoming)
    (extension : LeaBindingTheoryExtends incoming output)
    (scopeRetained : ∀ name, name ∈ scope → name ∈ retainedScope)
    (member : merged ∈ Metta.Bindings.merge incoming output)
    (mergedLoopFree : merged.hasLoop = false) :
    ServiceAwareScopedEvaluatorBindingRuntimeRel services scope specBindings
      (Metta.Minimal.restrictBnd retainedScope merged) := by
  rcases relation with ⟨presentation, specSolutions, observation⟩
  exact ⟨presentation, specSolutions,
    observation.merge_then_restrict_retaining incomingInvariant extension
      scopeRetained member mergedLoopFree⟩

/-- Exact specification binding theory is retained across a runtime
continuation merge whose projection scope contains the observation scope. -/
theorem merge_restrictBnd_retaining
    {services : Services} {scope retainedScope : List String}
    {specBindings : Bindings}
    {incoming output merged : Metta.Bindings}
    (relation : ServiceAwareScopedEvaluatorBindingRuntimeRel
      services scope specBindings output)
    (incomingInvariant : LeaRuntimeBindingInvariant incoming)
    (extension : LeaBindingTheoryExtends incoming output)
    (scopeRetained : ∀ name, name ∈ scope → name ∈ retainedScope)
    (member : merged ∈ Metta.Bindings.merge incoming
      (Metta.Minimal.restrictBnd retainedScope output))
    (mergedLoopFree : merged.hasLoop = false) :
    ServiceAwareScopedEvaluatorBindingRuntimeRel
      services scope specBindings merged := by
  rcases relation with ⟨presentation, specSolutions, observation⟩
  exact ⟨presentation, specSolutions,
    observation.merge_restrictBnd_retaining incomingInvariant extension
      scopeRetained member mergedLoopFree⟩

/-- Specialization in which continuation observation and projection use one
scope. -/
theorem merge_restrictBnd
    {services : Services} {scope : List String}
    {specBindings : Bindings}
    {incoming output merged : Metta.Bindings}
    (relation : ServiceAwareScopedEvaluatorBindingRuntimeRel
      services scope specBindings output)
    (incomingInvariant : LeaRuntimeBindingInvariant incoming)
    (extension : LeaBindingTheoryExtends incoming output)
    (member : merged ∈ Metta.Bindings.merge incoming
      (Metta.Minimal.restrictBnd scope output))
    (mergedLoopFree : merged.hasLoop = false) :
    ServiceAwareScopedEvaluatorBindingRuntimeRel
      services scope specBindings merged :=
  merge_restrictBnd_retaining relation incomingInvariant extension
    (fun _ membership => membership) member mergedLoopFree

/-- The exact selected-application binding seam.  A common model makes the
worker's totalized merge-head fallback unreachable; the selected merge is
then projected through the repaired retention scope.  The result both
preserves the specification observation at argument variables and extends
the complete runtime input theory. -/
theorem mergeHead_then_restrict_expectedApplicationRetentionScope
    {services : Services} {specBindings : Bindings}
    {incoming output : Metta.Bindings}
    (arguments : List Metta.Atom)
    (relation : ServiceAwareScopedEvaluatorBindingRuntimeRel services
      (arguments.flatMap Metta.Atom.vars) specBindings output)
    (incomingInvariant : LeaRuntimeBindingInvariant incoming)
    (extension : LeaBindingTheoryExtends incoming output) :
    let selected :=
      (Metta.Bindings.merge incoming output).head?.getD output
    let retained := Metta.Minimal.restrictBnd
      (Metta.Minimal.expectedApplicationRetentionScope incoming arguments)
      selected
    ServiceAwareScopedEvaluatorBindingRuntimeRel services
        (arguments.flatMap Metta.Atom.vars) specBindings retained ∧
      LeaBindingTheoryExtends incoming retained := by
  dsimp only
  rcases relation with ⟨presentation, specSolutions, observation⟩
  let valuation := leaClassSolution output
  have commonModel : ∃ valuation : String → Metta.Atom,
      LeaBindingSatisfied valuation incoming ∧
        LeaBindingSatisfied valuation output :=
    ⟨valuation, extension valuation observation.runtime.canonical.1,
      observation.runtime.canonical.1⟩
  obtain ⟨selectedMember, selectedInvariant, selectedExtendsIncoming,
      _selectedExtendsOutput⟩ :=
    mergeHeadGetD_of_commonModel incomingInvariant observation.runtime.noFloat
      (fallback := output) commonModel
  constructor
  · exact ⟨presentation, specSolutions,
      observation.merge_then_restrict_retaining incomingInvariant extension
        (expectedApplicationRetentionScope_argument_vars incoming arguments)
        selectedMember selectedInvariant.loopFree⟩
  · exact restrictBnd_expectedApplicationRetentionScope_extends arguments
      selectedInvariant selectedExtendsIncoming

end ServiceAwareScopedEvaluatorBindingRuntimeRel

/-! ## Service-aware evaluator result boundary -/

/-- An evaluator atom at its emission boundary.  Ordinary results are
compared after applying the exact specification presentation, but before
consulting the runtime binding payload.  Structured diagnostics retain their
published field discipline: the source is an emitted value, while positions
and reported types are literal observations up to private alpha-renaming.

This is deliberately stronger than `EvaluatorAtomObservationRel`.  The
runtime worker may subsequently project private bindings, but it does not
rewrite the atom it already emitted; keeping that fact in the producer's
result carrier makes projection structural instead of requiring a false
arbitrary-scope theorem. -/
inductive EmittedEvaluatorAtomObservationRel (services : Services)
    (presentation : TypeSubst) : Atom → Metta.Atom → Prop where
  | ordinary {atom : Atom} {runtimeAtom : Metta.Atom} :
      AlphaAtomRuntimeRel services (presentation.apply atom) runtimeAtom →
      EmittedEvaluatorAtomObservationRel services presentation atom runtimeAtom
  | incorrectNumberOfArguments {source : Atom}
      {runtimeSource : Metta.Atom} :
      AlphaAtomRuntimeRel services (presentation.apply source) runtimeSource →
      EmittedEvaluatorAtomObservationRel services presentation
        (mkError source .incorrectNumberOfArguments)
        (.expr [.sym "Error", runtimeSource,
          .sym "IncorrectNumberOfArguments"])
  | badArgType {source expected actual : Atom} {position : Nat}
      {runtimeSource runtimeExpected runtimeActual : Metta.Atom}
      {runtimePosition : Nat} :
      position = runtimePosition →
      AlphaAtomRuntimeRel services (presentation.apply source) runtimeSource →
      StructuralAtomObservationRel presentation [] expected runtimeExpected →
      StructuralAtomObservationRel presentation [] actual runtimeActual →
      EmittedEvaluatorAtomObservationRel services presentation
        (mkError source (.badArgType position expected actual))
        (.expr [.sym "Error", runtimeSource,
          .expr [.sym "BadArgType", .gnd (.int (Int.ofNat runtimePosition)),
            runtimeExpected, runtimeActual]])
  | badType {source expected actual : Atom}
      {runtimeSource runtimeExpected runtimeActual : Metta.Atom} :
      AlphaAtomRuntimeRel services (presentation.apply source) runtimeSource →
      StructuralAtomObservationRel presentation [] expected runtimeExpected →
      StructuralAtomObservationRel presentation [] actual runtimeActual →
      EmittedEvaluatorAtomObservationRel services presentation
        (mkError source (.badType expected actual))
        (Metta.Minimal.badTypeAtom runtimeSource runtimeExpected runtimeActual)

namespace EmittedEvaluatorAtomObservationRel

/-- An emitted atom can be observed under any runtime binding payload.  Both
sides of the compatibility equality use the same already-emitted runtime
atom, so no support or projection premise is needed. -/
theorem toBindingObservation
    {services : Services} {presentation : TypeSubst}
    {atom : Atom} {runtimeAtom : Metta.Atom}
    (relation : EmittedEvaluatorAtomObservationRel services presentation
      atom runtimeAtom)
    (runtimeBindings : Metta.Bindings) :
    EvaluatorAtomObservationRel services presentation runtimeBindings
          atom runtimeAtom ∨
      EvaluatorDiagnosticAtomObservationRel services presentation
          runtimeBindings atom runtimeAtom := by
  cases relation with
  | ordinary alpha =>
      rcases alpha with ⟨observed, observedAlpha, atomRelation⟩
      exact Or.inl ⟨observed, runtimeAtom, observedAlpha, atomRelation, rfl⟩
  | incorrectNumberOfArguments source =>
      rcases source with ⟨observed, observedAlpha, atomRelation⟩
      exact Or.inr (.incorrectNumberOfArguments
        ⟨observed, _, observedAlpha, atomRelation, rfl⟩)
  | badArgType position source expected actual =>
      rcases source with ⟨observed, observedAlpha, atomRelation⟩
      exact Or.inr (.badArgType position
        ⟨observed, _, observedAlpha, atomRelation, rfl⟩
        expected actual)
  | badType source expected actual =>
      rcases source with ⟨observed, observedAlpha, atomRelation⟩
      exact Or.inr (.badType
        ⟨observed, _, observedAlpha, atomRelation, rfl⟩
        expected actual)

end EmittedEvaluatorAtomObservationRel

/-- One specification result and one runtime result agree through a finite
specification presentation whose binding observation may contain opaque
service payloads.  Exactness remains intra-specification; the binding
observation is scoped, while the already-emitted atom is independent of
subsequent private-binding projection. -/
def ServiceAwareScopedEvaluatorResultRuntimeRel
    (services : Services) (scope : List String)
    (result : ResultPair) (runtimeResult : Metta.Atom × Metta.Bindings) : Prop :=
  ∃ presentation : TypeSubst,
    (∀ valuation,
      TypeSubstSatisfied valuation presentation ↔
        TypeBindingSatisfied valuation result.2) ∧
    ScopedPresentationRuntimeObservationRel
      services scope presentation runtimeResult.2 ∧
    EmittedEvaluatorAtomObservationRel services presentation
      result.1 runtimeResult.1 ∧
    (Spec.Eval.IsErrorRel result.1 ↔
      runtimeResult.1.isError = true)

namespace EvaluatorAtomObservationRel

/-- Project an explicit atom-observation witness when every variable of both
runtime atoms is retained.  A single projection renaming is obtained from
their joint expression, so nonlinear sharing between the two atoms is
preserved. -/
theorem of_restrictBnd
    {services : Services} {presentation : TypeSubst}
    {bindings : Metta.Bindings} {atom : Atom}
    {runtimeAtom presented : Metta.Atom} {observed : Atom}
    (invariant : LeaRuntimeBindingInvariant bindings)
    (scopeVars : List String)
    (alpha : ObservedTypeAlphaRel (presentation.apply atom) observed)
    (atomRelation : AtomRuntimeRel services observed presented)
    (equation : Metta.instantiate bindings presented =
      Metta.instantiate bindings runtimeAtom)
    (presentedRetained : ∀ name, name ∈ presented.vars → name ∈ scopeVars)
    (runtimeRetained : ∀ name, name ∈ runtimeAtom.vars → name ∈ scopeVars) :
    EvaluatorAtomObservationRel services presentation
      (Metta.Minimal.restrictBnd scopeVars bindings) atom runtimeAtom := by
  let pair := Metta.Atom.expr [presented, runtimeAtom]
  have pairRetained : ∀ name, name ∈ pair.vars → name ∈ scopeVars := by
    intro name member
    simp [pair, Metta.Atom.vars] at member
    rcases member with member | member
    · exact presentedRetained name member
    · exact runtimeRetained name member
  obtain ⟨permutation, pairEquation⟩ :=
    restrictBnd_atom_renaming invariant scopeVars pairRetained
  have unfoldedPairEquation :
      Metta.Atom.expr
          [Metta.instantiate
              (Metta.Minimal.restrictBnd scopeVars bindings) presented,
            Metta.instantiate
              (Metta.Minimal.restrictBnd scopeVars bindings) runtimeAtom] =
        Metta.Atom.expr
          [renBy permutation (Metta.instantiate bindings presented),
            renBy permutation (Metta.instantiate bindings runtimeAtom)] := by
    simpa [pair, Metta.instantiate, Metta.Bindings.resolveAtom, renBy] using
      pairEquation
  have componentEquation :
      Metta.instantiate (Metta.Minimal.restrictBnd scopeVars bindings)
            presented =
          renBy permutation (Metta.instantiate bindings presented) ∧
        Metta.instantiate (Metta.Minimal.restrictBnd scopeVars bindings)
            runtimeAtom =
          renBy permutation (Metta.instantiate bindings runtimeAtom) := by
    simpa using Metta.Atom.expr.inj unfoldedPairEquation
  refine ⟨observed, presented, alpha, atomRelation, ?_⟩
  exact componentEquation.1.trans
    ((congrArg (renBy permutation) equation).trans componentEquation.2.symm)

/-- Reconciliation with an input theory already entailed by the output does
not change an ordinary result-atom observation.  The proof transports the
original post-instantiation equality through the canonical output-to-merge
specialization; no variable-support approximation is used. -/
theorem merge_extending
    {services : Services} {presentation : TypeSubst}
    {incoming output merged : Metta.Bindings}
    {atom : Atom} {runtimeAtom : Metta.Atom}
    (relation : EvaluatorAtomObservationRel services presentation output
      atom runtimeAtom)
    (incomingInvariant : LeaRuntimeBindingInvariant incoming)
    (outputInvariant : LeaRuntimeBindingInvariant output)
    (member : merged ∈ Metta.Bindings.merge incoming output)
    (mergedLoopFree : merged.hasLoop = false) :
    EvaluatorAtomObservationRel services presentation merged
      atom runtimeAtom := by
  rcases relation with ⟨observed, presented, alpha, atomRelation, equation⟩
  have mergedInvariant : LeaRuntimeBindingInvariant merged :=
    incomingInvariant.merge outputInvariant.noFloat member mergedLoopFree
  have mergedSatisfiesOutput :
      LeaBindingSatisfied (leaClassSolution merged) output :=
    ((leaMerge_solution_iff (leaClassSolution merged)
      incomingInvariant.noFloat outputInvariant.noFloat member).mp
        mergedInvariant.canonical.1).2
  have refines := outputInvariant.canonical.2
    (leaClassSolution merged) mergedSatisfiesOutput
  obtain ⟨post, postEquation⟩ := refines.apply_eq_applyClassSolution
  refine ⟨observed, presented, alpha, atomRelation, ?_⟩
  rw [← applyClassSolution_lea_eq_instantiate,
    ← applyClassSolution_lea_eq_instantiate]
  calc
    applyClassSolution (leaClassSolution merged) presented =
        applyClassSolution post
          (applyClassSolution (leaClassSolution output) presented) :=
      postEquation presented
    _ = applyClassSolution post
          (applyClassSolution (leaClassSolution output) runtimeAtom) := by
      apply congrArg (applyClassSolution post)
      simpa only [applyClassSolution_lea_eq_instantiate] using equation
    _ = applyClassSolution (leaClassSolution merged) runtimeAtom :=
      (postEquation runtimeAtom).symm

end EvaluatorAtomObservationRel

namespace EvaluatorDiagnosticAtomObservationRel

/-- Diagnostic observations transport through an extending merge.  Literal
position and type fields are structural and therefore unchanged; only the
source atom uses the semantic merge transport above. -/
theorem merge_extending
    {services : Services} {presentation : TypeSubst}
    {incoming output merged : Metta.Bindings}
    {atom : Atom} {runtimeAtom : Metta.Atom}
    (relation : EvaluatorDiagnosticAtomObservationRel services presentation
      output atom runtimeAtom)
    (incomingInvariant : LeaRuntimeBindingInvariant incoming)
    (outputInvariant : LeaRuntimeBindingInvariant output)
    (member : merged ∈ Metta.Bindings.merge incoming output)
    (mergedLoopFree : merged.hasLoop = false) :
    EvaluatorDiagnosticAtomObservationRel services presentation merged
      atom runtimeAtom := by
  cases relation with
  | incorrectNumberOfArguments sourceRelation =>
      exact .incorrectNumberOfArguments
        (EvaluatorAtomObservationRel.merge_extending sourceRelation
          incomingInvariant outputInvariant member mergedLoopFree)
  | badArgType position sourceRelation expectedRelation actualRelation =>
      exact .badArgType position
        (EvaluatorAtomObservationRel.merge_extending sourceRelation
          incomingInvariant outputInvariant member mergedLoopFree)
        expectedRelation actualRelation
  | badType sourceRelation expectedRelation actualRelation =>
      exact .badType
        (EvaluatorAtomObservationRel.merge_extending sourceRelation
          incomingInvariant outputInvariant member mergedLoopFree)
        expectedRelation actualRelation

end EvaluatorDiagnosticAtomObservationRel

namespace ServiceAwareScopedEvaluatorResultRuntimeRel

/-- Project the service-aware binding component without reopening the atom
observation. -/
theorem bindingState
    {services : Services} {scope : List String}
    {result : ResultPair} {runtimeResult : Metta.Atom × Metta.Bindings}
    (relation : ServiceAwareScopedEvaluatorResultRuntimeRel services scope
      result runtimeResult) :
    ServiceAwareScopedEvaluatorBindingRuntimeRel services scope
      result.2 runtimeResult.2 := by
  rcases relation with
    ⟨presentation, specSolutions, observation, _atom, _error⟩
  exact ⟨presentation, specSolutions, observation⟩

/-- Error classification remains a literal observable of the result
boundary, independently of opaque binding payloads. -/
theorem isError_iff
    {services : Services} {scope : List String}
    {result : ResultPair} {runtimeResult : Metta.Atom × Metta.Bindings}
    (relation : ServiceAwareScopedEvaluatorResultRuntimeRel services scope
      result runtimeResult) :
    Spec.Eval.IsErrorRel result.1 ↔ runtimeResult.1.isError = true := by
  rcases relation with
    ⟨_presentation, _specSolutions, _observation, _atom, errorShape⟩
  exact errorShape

/-- Service-aware result observation is contravariant in the public binding
scope.  The coherent atom witness is retained unchanged. -/
theorem mono
    {services : Services} {large small : List String}
    {result : ResultPair} {runtimeResult : Metta.Atom × Metta.Bindings}
    (relation : ServiceAwareScopedEvaluatorResultRuntimeRel services large
      result runtimeResult)
    (subset : ∀ name, name ∈ small → name ∈ large) :
    ServiceAwareScopedEvaluatorResultRuntimeRel services small
      result runtimeResult := by
  rcases relation with
    ⟨presentation, specSolutions, observation, atomObservation, errorShape⟩
  exact ⟨presentation, specSolutions, observation.mono subset,
    atomObservation, errorShape⟩

/-- Project the runtime binding payload through any retention scope covering
the public observation scope.  The emitted atom is unchanged because its
producer-owned observation is independent of the private binding spelling. -/
theorem restrictBnd
    {services : Services} {publicScope retainedScope : List String}
    {result : ResultPair} {runtimeAtom : Metta.Atom}
    {runtimeBindings : Metta.Bindings}
    (relation : ServiceAwareScopedEvaluatorResultRuntimeRel services
      publicScope result (runtimeAtom, runtimeBindings))
    (publicRetained : ∀ name, name ∈ publicScope → name ∈ retainedScope) :
    ServiceAwareScopedEvaluatorResultRuntimeRel services publicScope result
      (runtimeAtom, Metta.Minimal.restrictBnd retainedScope runtimeBindings) := by
  rcases relation with
    ⟨presentation, specSolutions, observation, atomObservation, errorShape⟩
  exact ⟨presentation, specSolutions, observation.restrictBnd publicRetained,
    atomObservation, errorShape⟩

/-- Result observation survives reconciliation with an input theory already
entailed by the result.  Binding and atom observations are transported by
their respective semantic merge laws; the emitted atom and its literal error
classification are unchanged. -/
theorem merge_extending
    {services : Services} {scope : List String}
    {result : ResultPair} {runtimeAtom : Metta.Atom}
    {incoming output merged : Metta.Bindings}
    (relation : ServiceAwareScopedEvaluatorResultRuntimeRel services scope
      result (runtimeAtom, output))
    (incomingInvariant : LeaRuntimeBindingInvariant incoming)
    (extension : LeaBindingTheoryExtends incoming output)
    (member : merged ∈ Metta.Bindings.merge incoming output)
    (mergedLoopFree : merged.hasLoop = false) :
    ServiceAwareScopedEvaluatorResultRuntimeRel services scope
      result (runtimeAtom, merged) := by
  rcases relation with
    ⟨presentation, specSolutions, observation, atomObservation, errorShape⟩
  exact ⟨presentation, specSolutions,
    observation.merge_extending incomingInvariant extension member
      mergedLoopFree, atomObservation, errorShape⟩

/-- The evaluator's totalized merge-head selection preserves the complete
result observation whenever the recursive output extends its input.  The
common canonical output model proves that the fallback is unreachable. -/
theorem mergeHead_extending
    {services : Services} {scope : List String}
    {result : ResultPair} {runtimeAtom : Metta.Atom}
    {incoming output : Metta.Bindings}
    (relation : ServiceAwareScopedEvaluatorResultRuntimeRel services scope
      result (runtimeAtom, output))
    (incomingInvariant : LeaRuntimeBindingInvariant incoming)
    (extension : LeaBindingTheoryExtends incoming output) :
    let selected :=
      (Metta.Bindings.merge incoming output).head?.getD output
    ServiceAwareScopedEvaluatorResultRuntimeRel services scope
        result (runtimeAtom, selected) ∧
      LeaRuntimeBindingInvariant selected ∧
      LeaBindingTheoryExtends incoming selected := by
  dsimp only
  rcases relation with
    ⟨presentation, specSolutions, observation, atomObservation, errorShape⟩
  let valuation := leaClassSolution output
  have commonModel : ∃ valuation : String → Metta.Atom,
      LeaBindingSatisfied valuation incoming ∧
        LeaBindingSatisfied valuation output :=
    ⟨valuation, extension valuation observation.runtime.canonical.1,
      observation.runtime.canonical.1⟩
  obtain ⟨selectedMember, selectedInvariant, selectedExtendsIncoming,
      _selectedExtendsOutput⟩ :=
    mergeHeadGetD_of_commonModel incomingInvariant observation.runtime.noFloat
      (fallback := output) commonModel
  have original : ServiceAwareScopedEvaluatorResultRuntimeRel services scope
      result (runtimeAtom, output) :=
    ⟨presentation, specSolutions, observation, atomObservation, errorShape⟩
  exact ⟨original.merge_extending incomingInvariant extension selectedMember
      selectedInvariant.loopFree,
    selectedInvariant, selectedExtendsIncoming⟩

/-- The complete continuation boundary used by the selected worker: choose
the executable merge head, then project its private binding payload.  Public
result observation and extension of the worker input both survive when their
respective scopes are retained. -/
theorem mergeHead_then_restrict_retaining
    {services : Services} {publicScope retainedScope : List String}
    {result : ResultPair} {runtimeAtom : Metta.Atom}
    {incoming output : Metta.Bindings}
    (relation : ServiceAwareScopedEvaluatorResultRuntimeRel services
      publicScope result (runtimeAtom, output))
    (incomingInvariant : LeaRuntimeBindingInvariant incoming)
    (extension : LeaBindingTheoryExtends incoming output)
    (publicRetained : ∀ name, name ∈ publicScope → name ∈ retainedScope)
    (inputRetained : ∀ name, name ∈ incoming.vars → name ∈ retainedScope) :
    let selected :=
      (Metta.Bindings.merge incoming output).head?.getD output
    let retained := Metta.Minimal.restrictBnd retainedScope selected
    ServiceAwareScopedEvaluatorResultRuntimeRel services publicScope
        result (runtimeAtom, retained) ∧
      LeaRuntimeBindingInvariant retained ∧
      LeaBindingTheoryExtends incoming retained := by
  dsimp only
  obtain ⟨selectedRelation, selectedInvariant, selectedExtension⟩ :=
    relation.mergeHead_extending incomingInvariant extension
  exact ⟨selectedRelation.restrictBnd publicRetained,
    LeaTTaExpectedBindingThreadingConformance.restrictBnd_runtimeInvariant
      selectedInvariant retainedScope,
    restrictBnd_extends_of_input_vars selectedInvariant selectedExtension
      inputRetained⟩

/-- Specialization to the repaired expected-application retention scope.
The worker input variables are retained by construction; only containment of
the caller's declared public observation scope remains a consumer premise. -/
theorem mergeHead_then_restrict_expectedApplicationRetentionScope
    {services : Services} {publicScope : List String}
    {result : ResultPair} {runtimeAtom : Metta.Atom}
    {incoming output : Metta.Bindings} (arguments : List Metta.Atom)
    (relation : ServiceAwareScopedEvaluatorResultRuntimeRel services
      publicScope result (runtimeAtom, output))
    (incomingInvariant : LeaRuntimeBindingInvariant incoming)
    (extension : LeaBindingTheoryExtends incoming output)
    (publicRetained : ∀ name, name ∈ publicScope →
      name ∈ Metta.Minimal.expectedApplicationRetentionScope
        incoming arguments) :
    let selected :=
      (Metta.Bindings.merge incoming output).head?.getD output
    let retained := Metta.Minimal.restrictBnd
      (Metta.Minimal.expectedApplicationRetentionScope incoming arguments)
      selected
    ServiceAwareScopedEvaluatorResultRuntimeRel services publicScope
        result (runtimeAtom, retained) ∧
      LeaRuntimeBindingInvariant retained ∧
      LeaBindingTheoryExtends incoming retained := by
  apply mergeHead_then_restrict_retaining relation incomingInvariant extension
    publicRetained
  exact expectedApplicationRetentionScope_input_vars incoming arguments

/-- Assemble a result boundary from its exact specification presentation,
service-aware binding observation, atom observation, and error shape. -/
theorem ofBindingState
    {services : Services} {scope : List String}
    {presentation : TypeSubst} {result : ResultPair}
    {runtimeResult : Metta.Atom × Metta.Bindings}
    (specSolutions : ∀ valuation,
      TypeSubstSatisfied valuation presentation ↔
        TypeBindingSatisfied valuation result.2)
    (bindingObservation : ScopedPresentationRuntimeObservationRel
      services scope presentation runtimeResult.2)
    (atomObservation : EmittedEvaluatorAtomObservationRel services
      presentation result.1 runtimeResult.1)
    (errorShape : Spec.Eval.IsErrorRel result.1 ↔
      runtimeResult.1.isError = true) :
    ServiceAwareScopedEvaluatorResultRuntimeRel services scope
      result runtimeResult :=
  ⟨presentation, specSolutions, bindingObservation, atomObservation,
    errorShape⟩

end ServiceAwareScopedEvaluatorResultRuntimeRel

/-! ## Boundary canaries -/

/-- Empty bindings establish the service-aware carrier at every scope. -/
theorem serviceAwareBindingRuntimeRel_empty
    (services : Services) (scope : List String) :
    ServiceAwareScopedEvaluatorBindingRuntimeRel services scope
      Bindings.empty Metta.Bindings.empty := by
  refine ⟨[], ?_, ?_⟩
  · intro valuation
    simp [TypeSubstSatisfied, TypeBindingSatisfied, Bindings.empty]
  · refine ⟨TypeSubst.normal_empty, leaRuntimeBindingInvariant_empty, ?_⟩
    intro observedScope _subset
    rw [TypeSubst.apply_empty]
    refine ⟨bindingScopeProbe observedScope,
      ObservedTypeAlphaRel.refl _, ?_⟩
    rw [show Metta.Bindings.empty = [] from rfl,
      Metta.instantiate_nil, toLeaTTaAtom_bindingScopeProbe]
    unfold bindingScopeProbe
    apply AtomRuntimeRel.expression
    induction observedScope with
    | nil => exact .nil
    | cons name tail inductionHypothesis =>
        exact .cons (.variable name)
          (inductionHypothesis fun candidate member =>
            _subset candidate (by simp [member]))

/-- Positive result canary: an inert symbol and empty binding theory agree at
every scope through the service-aware carrier. -/
theorem serviceAwareResultRuntimeRel_emptySymbol
    (services : Services) (scope : List String) :
    ServiceAwareScopedEvaluatorResultRuntimeRel services scope
      (.symbol "a", Bindings.empty) (.sym "a", Metta.Bindings.empty) := by
  rcases serviceAwareBindingRuntimeRel_empty services scope with
    ⟨presentation, specSolutions, observation⟩
  refine ⟨presentation, specSolutions, observation, .ordinary ?_, ?_⟩
  · refine ⟨.symbol "a", ?_,
      AtomRuntimeRel.symbol (services := services) "a"⟩
    simpa [TypeSubst.apply] using
      (ObservedTypeAlphaRel.refl (Atom.symbol "a"))
  · simp [Spec.Eval.IsErrorRel, Metta.Atom.isError]

/-- Negative result canary: binding-payload support does not weaken the atom
shape boundary; a symbol cannot be observed as an expression. -/
theorem serviceAware_symbol_not_runtime_expression
    (services : Services) (scope : List String) :
    ¬ServiceAwareScopedEvaluatorResultRuntimeRel services scope
      (.symbol "a", Bindings.empty) (.expr [], Metta.Bindings.empty) := by
  intro relation
  rcases relation with
    ⟨presentation, _specSolutions, _observation, atomObservation,
      _errorShape⟩
  cases atomObservation with
  | ordinary atomObservation =>
    obtain ⟨observed, alpha, atom⟩ := atomObservation
    have applied : presentation.apply (Atom.symbol "a") =
        Atom.symbol "a" := by simp [TypeSubst.apply]
    rw [applied] at alpha
    obtain ⟨permutation, alphaEquation⟩ :=
      Spec.Type.Presentation.ScopeObservation.ObservedTypeAlphaRel.exists_permutation
        alpha
    have observedSymbol : observed = Atom.symbol "a" := by
      simpa [renameTypeVars] using alphaEquation
    have presentedSymbol : AtomRuntimeRel services
        (Atom.symbol "a") (.expr []) := by
      simpa [observedSymbol] using atom
    cases presentedSymbol

/-- Positive continuation canary: projection and re-merge are the identity
on the empty reachable theory at every public scope. -/
theorem serviceAwareBindingRuntimeRel_empty_continuationMerge
    (services : Services) :
    ServiceAwareScopedEvaluatorBindingRuntimeRel services []
      Bindings.empty Metta.Bindings.empty := by
  apply ServiceAwareScopedEvaluatorBindingRuntimeRel.merge_restrictBnd
    (serviceAwareBindingRuntimeRel_empty services [])
    leaRuntimeBindingInvariant_empty
    (LeaBindingTheoryExtends.refl Metta.Bindings.empty)
  · simp [Metta.Bindings.empty, Metta.Minimal.restrictBnd,
      Metta.Minimal.restrictBndRaw, Metta.Bindings.merge]
  · simp [Metta.Bindings.empty, Metta.Bindings.hasLoop,
      Metta.Bindings.vars]

private def runtimeXIsA : Metta.Bindings :=
  [.val "x" (.sym "A")]

private def runtimeXIsB : Metta.Bindings :=
  [.val "x" (.sym "B")]

/-- Negative continuation canary: replacing a public assignment is not a
runtime theory extension, so the continuation theorem cannot erase that
semantic conflict. -/
theorem runtime_public_assignment_replacement_not_extension :
    ¬LeaBindingTheoryExtends runtimeXIsA runtimeXIsB := by
  intro extension
  let valuation : String → Metta.Atom := fun name =>
    if name = "x" then .sym "B" else .var name
  have satisfiesB : LeaBindingSatisfied valuation runtimeXIsB := by
    constructor
    · intro name value member
      simp [runtimeXIsB] at member
      rcases member with ⟨rfl, rfl⟩
      simp [valuation, applyClassSolution]
    · intro left right member
      simp [runtimeXIsB] at member
  have satisfiesA := extension valuation satisfiesB
  have forced := satisfiesA.1 "x" (.sym "A") (by
    simp [runtimeXIsA])
  simp [valuation, applyClassSolution] at forced

/-- Native singleton presentation used by the opaque-payload canary. -/
def payloadPresentation (services : Services) : TypeSubst :=
  TypeSubst.bind [] "x"
    (.grounded (services.bindingPayload Bindings.empty))

/-- Native evaluator binding carried by the payload canary. -/
def payloadSpecBindings (services : Services) : Bindings :=
  ⟨[("x", .grounded (services.bindingPayload Bindings.empty))], []⟩

/-- Runtime evaluator binding corresponding to `payloadSpecBindings`. -/
def payloadRuntimeBindings : Metta.Bindings :=
  [.val "x" (.gnd (.bindings []))]

/-- The opaque empty binding payload stays inside the repaired runtime's
recursive host-float-free and canonical binding domain. -/
theorem payloadRuntimeBindings_invariant :
    LeaRuntimeBindingInvariant payloadRuntimeBindings := by
  apply leaRuntimeBindingInvariant_empty.merge
      (right := payloadRuntimeBindings)
      (out := payloadRuntimeBindings)
  · intro name value member
    simp [payloadRuntimeBindings] at member
    rcases member with ⟨rfl, rfl⟩
    simp [MettaAtomNoFloat, StoredBindingsNoFloat]
  · change payloadRuntimeBindings ∈
      Metta.Bindings.merge []
        [Metta.BindingRel.val "x" (.gnd (.bindings []))]
    rw [Metta.Bindings.merge]
    change payloadRuntimeBindings ∈
      Metta.Bindings.empty.addVarBinding "x" (.gnd (.bindings []))
    rw [Metta.Bindings.addVarBinding_fresh]
    · simp [payloadRuntimeBindings, Metta.Bindings.empty,
        Metta.Bindings.addValRaw, Metta.Bindings.removeVal]
    · rfl
    · intro target impossible
      cases impossible
  · exact Metta.Bindings.hasLoop_singleton_val_of_not_mem _ _
      (by simp [Metta.Atom.vars])

theorem payloadPresentation_normal (services : Services) :
    (payloadPresentation services).Normal := by
  apply TypeSubst.normal_empty.bind
  simp [TypeSubst.typeVars]

theorem payloadPresentation_solutions (services : Services)
    (valuation : String → Atom) :
    TypeSubstSatisfied valuation (payloadPresentation services) ↔
      TypeBindingSatisfied valuation (payloadSpecBindings services) := by
  simp [payloadPresentation, payloadSpecBindings, TypeSubst.bind,
    TypeSubst.erase, TypeSubstSatisfied, TypeBindingSatisfied,
    applyTypeValuation]

private theorem payloadPresentation_apply_probe
    (services : Services) (scope : List String)
    (onlyX : ∀ name, name ∈ scope → name = "x") :
    (payloadPresentation services).apply (bindingScopeProbe scope) =
      .expression
        (scope.map fun _ =>
          .grounded (services.bindingPayload Bindings.empty)) := by
  unfold bindingScopeProbe
  simp only [TypeSubst.apply, List.map_map]
  apply congrArg Atom.expression
  apply List.map_congr_left
  intro name member
  rw [onlyX name member]
  simp [payloadPresentation, TypeSubst.bind, TypeSubst.apply,
    TypeSubst.lookup]

private theorem payloadRuntimeBindings_instantiate_probe
    (scope : List String)
    (onlyX : ∀ name, name ∈ scope → name = "x") :
    Metta.instantiate payloadRuntimeBindings
        (toLeaTTaAtom (bindingScopeProbe scope)) =
      .expr (scope.map fun _ => .gnd (.bindings [])) := by
  rw [toLeaTTaAtom_bindingScopeProbe]
  unfold Metta.instantiate
  simp only [Metta.Bindings.resolveAtom, List.map_map]
  apply congrArg Metta.Atom.expr
  apply List.map_congr_left
  intro name member
  rw [onlyX name member]
  simp [payloadRuntimeBindings, Metta.Bindings.resolveAtom,
    Metta.Bindings.resolve_singleton_val_self_of_not_mem,
    Metta.Atom.vars]

/-- Positive carrier boundary: a matcher-reachable opaque binding payload is
represented by the service-aware carrier at its public variable. -/
theorem serviceAwareBindingRuntimeRel_payload (services : Services) :
    ServiceAwareScopedEvaluatorBindingRuntimeRel services ["x"]
      (payloadSpecBindings services) payloadRuntimeBindings := by
  refine ⟨payloadPresentation services,
    payloadPresentation_solutions services, ?_⟩
  refine ⟨payloadPresentation_normal services,
    payloadRuntimeBindings_invariant, ?_⟩
  intro observedScope subset
  have onlyX : ∀ name, name ∈ observedScope → name = "x" := by
    intro name member
    simpa using subset name member
  rw [payloadPresentation_apply_probe services observedScope onlyX,
    payloadRuntimeBindings_instantiate_probe observedScope onlyX]
  refine ⟨.expression
      (observedScope.map fun _ =>
        .grounded (services.bindingPayload Bindings.empty)),
    ObservedTypeAlphaRel.refl _, ?_⟩
  apply AtomRuntimeRel.expression
  let payloadRelated : ∀ names : List String,
      List.Forall₂ (AtomRuntimeRel services)
        (names.map fun _ =>
          .grounded (services.bindingPayload Bindings.empty))
        (names.map fun _ => .gnd (.bindings [])) := by
    intro names
    induction names with
    | nil => exact .nil
    | cons _name tail inductionHypothesis =>
        exact .cons
          (.bindingPayload Bindings.empty [] LeaBindingRelEquiv.empty)
          inductionHypothesis
  exact payloadRelated observedScope

/-- Alpha observation cannot erase a literal binding and replace it with an
unbound variable.  This is the local negative fact behind the requirement
that projection scopes contain every subsequently observed variable. -/
theorem expression_symbol_variable_not_alpha :
    ¬ObservedTypeAlphaRel
      (.expression [.symbol "B"]) (.expression [.var "y"]) := by
  rintro ⟨source,
    ⟨leftRename, _leftInjective, leftEquation⟩,
    ⟨rightRename, _rightInjective, rightEquation⟩⟩
  cases source with
  | symbol name => simp [renameTypeVars] at leftEquation
  | var name => simp [renameTypeVars] at leftEquation
  | grounded value => simp [renameTypeVars] at leftEquation
  | expression atoms =>
      cases atoms with
      | nil => simp [renameTypeVars] at leftEquation
      | cons head tail =>
          have leftExpression :
              Atom.expression
                  ((head :: tail).map (renameTypeVars leftRename)) =
                Atom.expression [.symbol "B"] := by
            simpa only [renameTypeVars] using leftEquation.symm
          have leftParts :
              renameTypeVars leftRename head = .symbol "B" ∧
                tail.map (renameTypeVars leftRename) = [] := by
            simpa [renameTypeVars] using
              Atom.expression.inj leftExpression
          have rightExpression :
              Atom.expression
                  ((head :: tail).map (renameTypeVars rightRename)) =
                Atom.expression [.var "y"] := by
            simpa only [renameTypeVars] using rightEquation.symm
          have rightParts :
              renameTypeVars rightRename head = .var "y" ∧
                tail.map (renameTypeVars rightRename) = [] := by
            simpa [renameTypeVars] using
              Atom.expression.inj rightExpression
          cases head <;>
            simp [renameTypeVars] at leftParts rightParts

/-- Negative carrier boundary: a runtime binding projection that drops `y`
cannot represent a specification result that still fixes `y` to `B`. -/
theorem dropped_public_binding_not_observed (services : Services) :
    ¬AlphaAtomRuntimeRel services
      (.expression [.symbol "B"]) (.expr [.var "y"]) := by
  rintro ⟨observed, alpha, runtime⟩
  cases runtime with
  | expression atoms runtimeAtoms related =>
      cases related with
      | cons head tail =>
          cases tail
          cases head
          exact expression_symbol_variable_not_alpha alpha

end Mettapedia.Languages.MeTTa.HE.LeaTTaEvaluatorBindingObservation
