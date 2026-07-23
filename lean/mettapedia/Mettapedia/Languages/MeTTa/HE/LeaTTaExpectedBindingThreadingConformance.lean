import Mettapedia.Languages.MeTTa.HE.LeaTTaEvaluatorConfigurationConformance
import Mettapedia.Languages.MeTTa.HE.LeaTTaMergeExistence
import Mettapedia.Languages.MeTTa.HE.LeaTTaQueryObservationalAnchor
import Mettapedia.Languages.MeTTa.HE.LeaTTaTypeImage

/-!
# Expected-application binding projection

Repair 19 retains the applicability assignments visible in the already
instantiated application and expected type.  The runtime realizes that
boundary by resolving those variables, discarding unrelated private
relations, and merging the projection with the incoming evaluator bindings.

This module proves the representation-independent facts about the projection
itself.  Resolution is semantically inert under every model of the source
binding theory; exact HE-image provenance is preserved; and the projected
binding list is satisfied by every model of the source.  These are the three
inputs needed by the selected-application seed correspondence.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaExpectedBindingThreadingConformance

open Metta
open Metta.Minimal
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.RuntimeCorrectness
open LeaTTaBridge
open Spec.Type.Presentation.ScopeObservation

/-- The evaluator's bounded fixpoint wrapper does not change the value of an
atom in any model of the binding theory.  This is distinct from the core
`Bindings.resolveAtom`: it records the exact wrapper used by `restrictBnd`. -/
theorem evaluatorResolveAtom_semantically_inert
    {bindings : Metta.Bindings} {valuation : String → Metta.Atom}
    (satisfied : LeaBindingSatisfied valuation bindings) :
    ∀ fuel atom,
      applyClassSolution valuation
          (Metta.Minimal.resolveAtom bindings fuel atom) =
        applyClassSolution valuation atom := by
  intro fuel
  induction fuel with
  | zero => intro atom; rfl
  | succ fuel inductionHypothesis =>
      intro atom
      rw [Metta.Minimal.resolveAtom]
      split
      · rfl
      · rw [inductionHypothesis]
        exact instantiate_semantically_inert satisfied atom

/-- The evaluator's bounded fixpoint wrapper stays inside the exact HE atom
image whenever its source binding record and input atom do. -/
theorem evaluatorResolveAtom_heImage
    {bindings : Metta.Bindings} (bindingsImage : LeaBindingsHEImage bindings) :
    ∀ fuel atom, LeaAtomHEImage atom →
      LeaAtomHEImage (Metta.Minimal.resolveAtom bindings fuel atom) := by
  intro fuel
  induction fuel with
  | zero => intro atom atomImage; exact atomImage
  | succ fuel inductionHypothesis =>
      intro atom atomImage
      rw [Metta.Minimal.resolveAtom]
      split
      · exact atomImage
      · exact inductionHypothesis _
          (instantiate_heImage bindingsImage atom atomImage)

private theorem mapM_noFloat_pointwise
    {f : Metta.Atom → Option Metta.Atom} :
    ∀ (inputs outputs : List Metta.Atom),
      inputs.mapM f = some outputs →
      (∀ input ∈ inputs, ∀ output, f input = some output →
        MettaAtomNoFloat output) →
      ∀ output ∈ outputs, MettaAtomNoFloat output
  | [], outputs, run, _stepSafe => by
      simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at run
      subst run
      intro output member
      exact absurd member (List.not_mem_nil)
  | input :: inputs, outputs, run, stepSafe => by
      cases headRun : f input with
      | none => simp [List.mapM_cons, headRun] at run
      | some headOutput =>
          cases tailRun : inputs.mapM f with
          | none => simp [List.mapM_cons, headRun, tailRun] at run
          | some tailOutputs =>
              have outputsEquation : headOutput :: tailOutputs = outputs := by
                simpa [List.mapM_cons, headRun, tailRun] using run
              subst outputs
              intro output member
              rcases List.mem_cons.mp member with rfl | tailMember
              · exact stepSafe input List.mem_cons_self _ headRun
              · exact mapM_noFloat_pointwise inputs tailOutputs tailRun
                  (fun atom atomMember =>
                    stepSafe atom (List.mem_cons_of_mem _ atomMember))
                  output tailMember

private theorem resolveAtomAux_noFloat
    {bindings : Metta.Bindings} (bindingsNoFloat : LeaBindingsNoFloat bindings) :
    ∀ (fuel : Nat) (visited : List String) (atom result : Metta.Atom),
      MettaAtomNoFloat atom →
      Metta.Bindings.resolveAtomAux bindings fuel visited atom = some result →
      MettaAtomNoFloat result := by
  intro fuel
  induction fuel with
  | zero =>
      intro visited atom result _ run
      simp [Metta.Bindings.resolveAtomAux] at run
  | succ fuel inductionHypothesis =>
      intro visited atom result atomNoFloat run
      cases atom with
      | sym symbol =>
          simp only [Metta.Bindings.resolveAtomAux] at run
          cases run
          exact atomNoFloat
      | gnd ground =>
          simp only [Metta.Bindings.resolveAtomAux] at run
          cases run
          exact atomNoFloat
      | expr atoms =>
          simp only [Metta.Bindings.resolveAtomAux] at run
          cases mapRun : atoms.mapM
              (Metta.Bindings.resolveAtomAux bindings fuel visited) with
          | none => rw [mapRun] at run; cases run
          | some resolved =>
              rw [mapRun] at run
              cases run
              have atomsNoFloat : ∀ atom ∈ atoms,
                  MettaAtomNoFloat atom := by
                simpa [MettaAtomNoFloat] using atomNoFloat
              simpa [MettaAtomNoFloat] using
                (mapM_noFloat_pointwise atoms resolved mapRun
                  (fun input inputMember output outputRun =>
                    inductionHypothesis visited input output
                      (atomsNoFloat input inputMember)
                      outputRun))
      | var name =>
          simp only [Metta.Bindings.resolveAtomAux] at run
          by_cases visitedClass :
              ((Metta.Bindings.eqClassOrdered bindings name).any
                visited.contains) = true
          · rw [if_pos visitedClass] at run
            cases run
          · rw [if_neg visitedClass] at run
            cases valuesEquation : Metta.Bindings.classValues bindings name with
            | nil =>
                rw [valuesEquation] at run
                cases run
                simp [MettaAtomNoFloat]
            | cons value values =>
                rw [valuesEquation] at run
                have valueNoFloat : MettaAtomNoFloat value :=
                  leaClassValue_noFloat bindingsNoFloat (by
                    rw [valuesEquation]
                    exact List.mem_cons_self)
                cases value with
                | var target =>
                    by_cases targetInClass :
                        target ∈ Metta.Bindings.eqClassOrdered bindings name
                    · by_cases singletonClass :
                          (Metta.Bindings.eqClassOrdered bindings name).length = 1
                      · simp [targetInClass, singletonClass] at run
                      · have resultEquation : Metta.Atom.var
                            (Metta.Bindings.eqRepresentative bindings name) =
                              result := by
                          simpa [targetInClass, singletonClass] using run
                        subst result
                        simp [MettaAtomNoFloat]
                    · apply inductionHypothesis
                        (Metta.Bindings.eqClassOrdered bindings name ++ visited)
                        (.var target) result valueNoFloat
                      simpa [targetInClass] using run
                | sym symbol =>
                    apply inductionHypothesis
                        (Metta.Bindings.eqClassOrdered bindings name ++ visited)
                        (.sym symbol) result valueNoFloat
                    simpa using run
                | gnd ground =>
                    apply inductionHypothesis
                        (Metta.Bindings.eqClassOrdered bindings name ++ visited)
                        (.gnd ground) result valueNoFloat
                    simpa using run
                | expr atoms =>
                    apply inductionHypothesis
                        (Metta.Bindings.eqClassOrdered bindings name ++ visited)
                        (.expr atoms) result valueNoFloat
                    simpa using run

private theorem atom_size_pos (atom : Metta.Atom) : 0 < atom.size := by
  cases atom <;> simp only [Metta.Atom.size] <;> omega

private theorem atom_size_lt_of_mem {atom : Metta.Atom} :
    ∀ {atoms : List Metta.Atom}, atom ∈ atoms →
      atom.size < (Metta.Atom.expr atoms).size
  | head :: tail, member => by
      rcases List.mem_cons.mp member with rfl | tailMember
      · simp only [Metta.Atom.size, List.map_cons, List.sum_cons]
        omega
      · have smaller := atom_size_lt_of_mem tailMember
        simp only [Metta.Atom.size, List.map_cons, List.sum_cons] at smaller ⊢
        omega

/-- Equality-class-aware instantiation preserves the host-float-free domain
when every direct value stored by the binding record is host-float-free. -/
theorem instantiate_noFloat
    {bindings : Metta.Bindings} (bindingsNoFloat : LeaBindingsNoFloat bindings) :
    ∀ atom : Metta.Atom, MettaAtomNoFloat atom →
      MettaAtomNoFloat (Metta.instantiate bindings atom) := by
  suffices key : ∀ (bound : Nat) (atom : Metta.Atom), atom.size ≤ bound →
      MettaAtomNoFloat atom →
      MettaAtomNoFloat (Metta.Bindings.resolveAtom bindings atom) by
    intro atom atomNoFloat
    exact key atom.size atom le_rfl atomNoFloat
  intro bound
  induction bound with
  | zero =>
      intro atom sizeBound
      exact absurd sizeBound (by have := atom_size_pos atom; omega)
  | succ bound inductionHypothesis =>
      intro atom sizeBound atomNoFloat
      cases atom with
      | sym symbol => simpa [Metta.Bindings.resolveAtom] using atomNoFloat
      | gnd ground => simpa [Metta.Bindings.resolveAtom] using atomNoFloat
      | var name =>
          simp only [Metta.Bindings.resolveAtom]
          cases resolveEquation : Metta.Bindings.resolve bindings name with
          | none => simpa using atomNoFloat
          | some result =>
              simp only [Option.getD_some]
              have auxiliary : Metta.Bindings.resolveAtomAux bindings
                  (Metta.Bindings.resolutionFuel bindings (.var name)) []
                  (.var name) = some result := by
                by_cases unresolved :
                    ((Metta.Bindings.eqClassOrdered bindings name == [name]) &&
                      (Metta.Bindings.classValues bindings name).isEmpty) = true
                · simp [Metta.Bindings.resolve, unresolved] at resolveEquation
                · simpa [Metta.Bindings.resolve, unresolved] using resolveEquation
              exact resolveAtomAux_noFloat bindingsNoFloat _ _ _ _
                (by simp [MettaAtomNoFloat]) auxiliary
      | expr atoms =>
          simp only [Metta.Bindings.resolveAtom, MettaAtomNoFloat]
          have atomsNoFloat : ∀ atom ∈ atoms,
              MettaAtomNoFloat atom := by
            simpa [MettaAtomNoFloat] using atomNoFloat
          intro output member
          obtain ⟨input, inputMember, rfl⟩ := List.mem_map.mp member
          exact inductionHypothesis input
            (by
              have smaller := atom_size_lt_of_mem inputMember
              omega)
            (atomsNoFloat input inputMember)

/-- The evaluator's bounded fixpoint wrapper preserves the host-float-free
domain. -/
theorem evaluatorResolveAtom_noFloat
    {bindings : Metta.Bindings} (bindingsNoFloat : LeaBindingsNoFloat bindings) :
    ∀ fuel atom, MettaAtomNoFloat atom →
      MettaAtomNoFloat (Metta.Minimal.resolveAtom bindings fuel atom) := by
  intro fuel
  induction fuel with
  | zero => intro atom atomNoFloat; exact atomNoFloat
  | succ fuel inductionHypothesis =>
      intro atom atomNoFloat
      rw [Metta.Minimal.resolveAtom]
      split
      · exact atomNoFloat
      · exact inductionHypothesis _
          (instantiate_noFloat bindingsNoFloat atom atomNoFloat)

/-- Homomorphic specialization of a satisfying runtime valuation is again a
model of the same binding equations. -/
theorem leaBindingSatisfied_specialize
    {bindings : Metta.Bindings}
    {general post : String → Metta.Atom}
    (satisfied : LeaBindingSatisfied general bindings) :
    LeaBindingSatisfied
      (fun name => applyClassSolution post (general name)) bindings := by
  constructor
  · intro name value member
    calc
      applyClassSolution post (general name) =
          applyClassSolution post (applyClassSolution general value) :=
        congrArg (applyClassSolution post)
          (satisfied.1 name value member)
      _ = applyClassSolution
          (fun key => applyClassSolution post (general key)) value :=
        Spec.Match.ModelTheory.applyClassSolution_comp post general value
  · intro left right member
    exact congrArg (applyClassSolution post)
      (satisfied.2 left right member)

/-- The reachable canonical binding invariant makes runtime instantiation
idempotent.  This is a semantic theorem about the repaired binding theory,
not an unconditional claim about arbitrary cyclic `Bindings`. -/
theorem instantiate_idempotent_of_runtimeInvariant
    {bindings : Metta.Bindings}
    (invariant :
      LeaTTaSpecConformance.LeaRuntimeBindingInvariant bindings)
    (atom : Metta.Atom) :
    Metta.instantiate bindings (Metta.instantiate bindings atom) =
      Metta.instantiate bindings atom := by
  have inert := instantiate_semantically_inert invariant.canonical.1 atom
  simpa only [applyClassSolution_lea_eq_instantiate] using inert

/-- On reachable host-float-free inputs, the evaluator's bounded fixpoint
wrapper computes exactly one canonical instantiation.  The fuel premise is
sharp: zero fuel returns the input without inspecting the binding. -/
theorem evaluatorResolveAtom_eq_instantiate_of_runtimeInvariant
    {bindings : Metta.Bindings}
    (invariant :
      LeaTTaSpecConformance.LeaRuntimeBindingInvariant bindings)
    (atom : Metta.Atom) (atomNoFloat : MettaAtomNoFloat atom) :
    ∀ fuel, 0 < fuel →
      Metta.Minimal.resolveAtom bindings fuel atom =
        Metta.instantiate bindings atom := by
  intro fuel positive
  cases fuel with
  | zero => omega
  | succ fuel =>
      rw [Metta.Minimal.resolveAtom]
      let instantiated := Metta.instantiate bindings atom
      have instantiatedNoFloat : MettaAtomNoFloat instantiated :=
        instantiate_noFloat invariant.noFloat atom atomNoFloat
      by_cases fixed : (instantiated == atom) = true
      · rw [if_pos fixed]
        exact (mettaAtom_eq_of_beq_true_noFloat
          instantiatedNoFloat atomNoFloat fixed).symm
      · rw [if_neg fixed]
        cases fuel with
        | zero => rfl
        | succ remaining =>
            rw [Metta.Minimal.resolveAtom]
            have idempotent : Metta.instantiate bindings instantiated =
                instantiated := by
              exact instantiate_idempotent_of_runtimeInvariant
                invariant atom
            have reflexive : (instantiated == instantiated) = true :=
              mettaAtom_beq_self_noFloat instantiated instantiatedNoFloat
            rw [idempotent, if_pos reflexive]

/-- Every model of a binding record is a model of its evaluator-visible
projection.  The result is directional: projection intentionally forgets
constraints outside `scopeVars`, so the converse is false in general. -/
theorem restrictBndRaw_satisfied_of_satisfied
    {bindings : Metta.Bindings} {valuation : String → Metta.Atom}
    (satisfied : LeaBindingSatisfied valuation bindings)
    (scopeVars : List String) :
    LeaBindingSatisfied valuation
      (Metta.Minimal.restrictBndRaw scopeVars bindings) := by
  constructor
  · intro name value member
    unfold Metta.Minimal.restrictBndRaw at member
    rcases List.mem_append.mp member with solvedMember | equalityMember
    · obtain ⟨candidateName, _candidateMember, emitted⟩ :=
        List.mem_filterMap.mp solvedMember
      cases resolvedEquation : Metta.Minimal.resolveAtom bindings
          (bindings.length + 1) (.var candidateName) with
      | var target =>
          by_cases same : target = candidateName <;>
            simp [resolvedEquation, same] at emitted
      | sym symbol =>
          simp [resolvedEquation] at emitted
          rcases emitted with ⟨rfl, rfl⟩
          simpa [applyClassSolution, resolvedEquation] using
            (evaluatorResolveAtom_semantically_inert satisfied
              (bindings.length + 1) (.var candidateName)).symm
      | gnd grounded =>
          simp [resolvedEquation] at emitted
          rcases emitted with ⟨rfl, rfl⟩
          simpa [applyClassSolution, resolvedEquation] using
            (evaluatorResolveAtom_semantically_inert satisfied
              (bindings.length + 1) (.var candidateName)).symm
      | expr atoms =>
          simp [resolvedEquation] at emitted
          rcases emitted with ⟨rfl, rfl⟩
          simpa [applyClassSolution, resolvedEquation] using
            (evaluatorResolveAtom_semantically_inert satisfied
              (bindings.length + 1) (.var candidateName)).symm
    · have impossible : Metta.BindingRel.val name value ∈
          bindings.filter (fun relation => match relation with
            | .eq left right => scopeVars.contains left &&
                scopeVars.contains right
            | _ => false) := equalityMember
      obtain ⟨sourceMember, selected⟩ := List.mem_filter.mp impossible
      simp at selected
  · intro left right member
    unfold Metta.Minimal.restrictBndRaw at member
    rcases List.mem_append.mp member with solvedMember | equalityMember
    · obtain ⟨candidateName, _candidateMember, emitted⟩ :=
        List.mem_filterMap.mp solvedMember
      cases resolvedEquation : Metta.Minimal.resolveAtom bindings
          (bindings.length + 1) (.var candidateName) with
      | var target =>
          by_cases same : target = candidateName
          · simp [resolvedEquation, same] at emitted
          · simp [resolvedEquation, same] at emitted
            rcases emitted with ⟨rfl, rfl⟩
            simpa [applyClassSolution, resolvedEquation] using
              (evaluatorResolveAtom_semantically_inert satisfied
                (bindings.length + 1) (.var candidateName)).symm
      | sym symbol => simp [resolvedEquation] at emitted
      | gnd grounded => simp [resolvedEquation] at emitted
      | expr atoms => simp [resolvedEquation] at emitted
    · exact satisfied.2 left right (List.mem_filter.mp equalityMember).1

/-- Every model of the visible projection extends to a model of the complete
reachable runtime binding theory while preserving the requested variables.
Together with `restrictBndRaw_satisfied_of_satisfied`, this characterizes
`restrictBndRaw` as the exact existential projection of a binding theory. -/
theorem restrictBndRaw_exists_satisfied_extension
    {bindings : Metta.Bindings}
    (invariant :
      LeaTTaSpecConformance.LeaRuntimeBindingInvariant bindings)
    (scopeVars : List String) (projected : String → Metta.Atom)
    (projectedSatisfied : LeaBindingSatisfied projected
      (Metta.Minimal.restrictBndRaw scopeVars bindings)) :
    ∃ complete : String → Metta.Atom,
      LeaBindingSatisfied complete bindings ∧
        ∀ name ∈ scopeVars, complete name = projected name := by
  let complete : String → Metta.Atom := fun name =>
    applyClassSolution projected (leaClassSolution bindings name)
  have completeSatisfied : LeaBindingSatisfied complete bindings := by
    exact leaBindingSatisfied_specialize invariant.canonical.1
  refine ⟨complete, completeSatisfied, ?_⟩
  intro name nameMember
  have variableNoFloat : MettaAtomNoFloat (.var name) := by
    simp [MettaAtomNoFloat]
  have resolvedEquation :
      Metta.Minimal.resolveAtom bindings (bindings.length + 1) (.var name) =
        Metta.instantiate bindings (.var name) := by
    apply evaluatorResolveAtom_eq_instantiate_of_runtimeInvariant
      invariant (.var name) variableNoFloat
    omega
  have classEquation : leaClassSolution bindings name =
      Metta.instantiate bindings (.var name) := by
    simpa only [applyClassSolution] using
      (applyClassSolution_lea_eq_instantiate bindings (.var name))
  by_cases fixed :
      (Metta.Minimal.resolveAtom bindings (bindings.length + 1) (.var name) ==
        .var name) = true
  · have resolvedNoFloat : MettaAtomNoFloat
        (Metta.Minimal.resolveAtom bindings (bindings.length + 1)
          (.var name)) :=
      evaluatorResolveAtom_noFloat invariant.noFloat _ _ variableNoFloat
    have resolvedFixed :
        Metta.Minimal.resolveAtom bindings (bindings.length + 1)
            (.var name) = .var name :=
      mettaAtom_eq_of_beq_true_noFloat resolvedNoFloat variableNoFloat fixed
    have instantiatedFixed :
        Metta.instantiate bindings (.var name) = .var name := by
      rw [← resolvedEquation]
      exact resolvedFixed
    simp [complete, classEquation, instantiatedFixed, applyClassSolution]
  · cases concreteEquation : Metta.Minimal.resolveAtom bindings
        (bindings.length + 1) (.var name) with
    | var target =>
        have different : target ≠ name := by
          intro same
          subst target
          have selfTrue : ((.var name : Metta.Atom) == .var name) = true :=
            by
              change Metta.Atom.beq (.var name) (.var name) = true
              simp [Metta.Atom.beq]
          rw [concreteEquation, selfTrue] at fixed
          exact fixed rfl
        have retained : Metta.BindingRel.eq name target ∈
            Metta.Minimal.restrictBndRaw scopeVars bindings := by
          unfold Metta.Minimal.restrictBndRaw
          apply List.mem_append_left
          apply List.mem_filterMap.mpr
          exact ⟨name, nameMember, by simp [concreteEquation, different]⟩
        have equation := projectedSatisfied.2 name target retained
        calc
          complete name =
              applyClassSolution projected
                (Metta.instantiate bindings (.var name)) := by
            simp [complete, classEquation]
          _ = applyClassSolution projected (.var target) := by
            rw [← concreteEquation, resolvedEquation]
          _ = projected name := by
            simpa [applyClassSolution] using equation.symm
    | sym symbol =>
        have retained : Metta.BindingRel.val name (.sym symbol) ∈
            Metta.Minimal.restrictBndRaw scopeVars bindings := by
          unfold Metta.Minimal.restrictBndRaw
          apply List.mem_append_left
          apply List.mem_filterMap.mpr
          exact ⟨name, nameMember, by simp [concreteEquation]⟩
        have equation := projectedSatisfied.1 name (.sym symbol) retained
        calc
          complete name =
              applyClassSolution projected
                (Metta.instantiate bindings (.var name)) := by
            simp [complete, classEquation]
          _ = applyClassSolution projected (.sym symbol) := by
            rw [← concreteEquation, resolvedEquation]
          _ = projected name := equation.symm
    | gnd grounded =>
        have retained : Metta.BindingRel.val name (.gnd grounded) ∈
            Metta.Minimal.restrictBndRaw scopeVars bindings := by
          unfold Metta.Minimal.restrictBndRaw
          apply List.mem_append_left
          apply List.mem_filterMap.mpr
          exact ⟨name, nameMember, by simp [concreteEquation]⟩
        have equation := projectedSatisfied.1 name (.gnd grounded) retained
        calc
          complete name =
              applyClassSolution projected
                (Metta.instantiate bindings (.var name)) := by
            simp [complete, classEquation]
          _ = applyClassSolution projected (.gnd grounded) := by
            rw [← concreteEquation, resolvedEquation]
          _ = projected name := equation.symm
    | expr atoms =>
        have retained : Metta.BindingRel.val name (.expr atoms) ∈
            Metta.Minimal.restrictBndRaw scopeVars bindings := by
          unfold Metta.Minimal.restrictBndRaw
          apply List.mem_append_left
          apply List.mem_filterMap.mpr
          exact ⟨name, nameMember, by simp [concreteEquation]⟩
        have equation := projectedSatisfied.1 name (.expr atoms) retained
        calc
          complete name =
              applyClassSolution projected
                (Metta.instantiate bindings (.var name)) := by
            simp [complete, classEquation]
          _ = applyClassSolution projected (.expr atoms) := by
            rw [← concreteEquation, resolvedEquation]
          _ = projected name := equation.symm

/-- Projecting an image-valued binding record preserves exact HE-image
provenance for every retained direct value. -/
theorem restrictBndRaw_heImage
    {bindings : Metta.Bindings} (bindingsImage : LeaBindingsHEImage bindings)
    (scopeVars : List String) :
    LeaBindingsHEImage (Metta.Minimal.restrictBndRaw scopeVars bindings) := by
  intro name value member
  unfold Metta.Minimal.restrictBndRaw at member
  rcases List.mem_append.mp member with solvedMember | equalityMember
  · obtain ⟨candidateName, _candidateMember, emitted⟩ :=
      List.mem_filterMap.mp solvedMember
    cases resolvedEquation : Metta.Minimal.resolveAtom bindings
        (bindings.length + 1) (.var candidateName) with
    | var target =>
        by_cases same : target = candidateName <;>
          simp [resolvedEquation, same] at emitted
    | sym symbol =>
        simp [resolvedEquation] at emitted
        rcases emitted with ⟨rfl, rfl⟩
        simpa [resolvedEquation] using
          (evaluatorResolveAtom_heImage bindingsImage
            (bindings.length + 1) (.var candidateName)
              (leaAtomHEImage_var candidateName))
    | gnd grounded =>
        simp [resolvedEquation] at emitted
        rcases emitted with ⟨rfl, rfl⟩
        simpa [resolvedEquation] using
          (evaluatorResolveAtom_heImage bindingsImage
            (bindings.length + 1) (.var candidateName)
              (leaAtomHEImage_var candidateName))
    | expr atoms =>
        simp [resolvedEquation] at emitted
        rcases emitted with ⟨rfl, rfl⟩
        simpa [resolvedEquation] using
          (evaluatorResolveAtom_heImage bindingsImage
            (bindings.length + 1) (.var candidateName)
              (leaAtomHEImage_var candidateName))
  · obtain ⟨_sourceMember, selected⟩ := List.mem_filter.mp equalityMember
    simp at selected

/-- The evaluator-visible projection of a host-float-free binding record is
host-float-free.  Retained equalities carry no atom payload. -/
theorem restrictBndRaw_noFloat
    {bindings : Metta.Bindings} (bindingsNoFloat : LeaBindingsNoFloat bindings)
    (scopeVars : List String) :
    LeaBindingsNoFloat (Metta.Minimal.restrictBndRaw scopeVars bindings) := by
  intro name value member
  unfold Metta.Minimal.restrictBndRaw at member
  rcases List.mem_append.mp member with solvedMember | equalityMember
  · obtain ⟨candidateName, _candidateMember, emitted⟩ :=
      List.mem_filterMap.mp solvedMember
    cases resolvedEquation : Metta.Minimal.resolveAtom bindings
        (bindings.length + 1) (.var candidateName) with
    | var target =>
        by_cases same : target = candidateName <;>
          simp [resolvedEquation, same] at emitted
    | sym symbol =>
        simp [resolvedEquation] at emitted
        rcases emitted with ⟨rfl, rfl⟩
        simpa [resolvedEquation] using
          (evaluatorResolveAtom_noFloat bindingsNoFloat
            (bindings.length + 1) (.var candidateName) (by
              simp [MettaAtomNoFloat]))
    | gnd grounded =>
        simp [resolvedEquation] at emitted
        rcases emitted with ⟨rfl, rfl⟩
        simpa [resolvedEquation] using
          (evaluatorResolveAtom_noFloat bindingsNoFloat
            (bindings.length + 1) (.var candidateName) (by
              simp [MettaAtomNoFloat]))
    | expr atoms =>
        simp [resolvedEquation] at emitted
        rcases emitted with ⟨rfl, rfl⟩
        simpa [resolvedEquation] using
          (evaluatorResolveAtom_noFloat bindingsNoFloat
            (bindings.length + 1) (.var candidateName) (by
              simp [MettaAtomNoFloat]))
  · obtain ⟨_sourceMember, selected⟩ := List.mem_filter.mp equalityMember
    simp at selected

/-- Projection preserves LeaTTa's normalized representation: a residual
variable/variable solution is emitted as an equality edge, never as a value
assignment whose payload is a bare variable. -/
theorem restrictBndRaw_assignmentsNonVariable
    (bindings : Metta.Bindings) (scopeVars : List String) :
    LeaAssignmentsNonVariable
      (Metta.Minimal.restrictBndRaw scopeVars bindings) := by
  intro key target member
  unfold Metta.Minimal.restrictBndRaw at member
  rcases List.mem_append.mp member with solvedMember | equalityMember
  · obtain ⟨candidateName, _candidateMember, emitted⟩ :=
      List.mem_filterMap.mp solvedMember
    cases resolvedEquation : Metta.Minimal.resolveAtom bindings
        (bindings.length + 1) (.var candidateName) with
    | var resolvedTarget =>
        by_cases same : resolvedTarget = candidateName <;>
          simp [resolvedEquation, same] at emitted
    | sym symbol => simp [resolvedEquation] at emitted
    | gnd grounded => simp [resolvedEquation] at emitted
    | expr atoms => simp [resolvedEquation] at emitted
  · obtain ⟨_sourceMember, selected⟩ := List.mem_filter.mp equalityMember
    simp at selected

/-- Projection cannot introduce a reflexive equality edge.  Newly emitted
aliases are guarded by disequality, while retained edges inherit the source
normal form. -/
theorem restrictBndRaw_equalitiesIrreflexive
    {bindings : Metta.Bindings}
    (irreflexive : LeaEqualitiesIrreflexive bindings)
    (scopeVars : List String) :
    LeaEqualitiesIrreflexive
      (Metta.Minimal.restrictBndRaw scopeVars bindings) := by
  intro key member
  unfold Metta.Minimal.restrictBndRaw at member
  rcases List.mem_append.mp member with solvedMember | equalityMember
  · obtain ⟨candidateName, _candidateMember, emitted⟩ :=
      List.mem_filterMap.mp solvedMember
    cases resolvedEquation : Metta.Minimal.resolveAtom bindings
        (bindings.length + 1) (.var candidateName) with
    | var resolvedTarget =>
        by_cases same : resolvedTarget = candidateName
        · simp [resolvedEquation, same] at emitted
        · simp [resolvedEquation, same] at emitted
          rcases emitted with ⟨rfl, rfl⟩
          exact same rfl
    | sym symbol => simp [resolvedEquation] at emitted
    | gnd grounded => simp [resolvedEquation] at emitted
    | expr atoms => simp [resolvedEquation] at emitted
  · exact irreflexive key (List.mem_filter.mp equalityMember).1

/-! ## Canonical replay of the visible projection -/

/-- A satisfiable, host-float-free raw projection has a successful canonical
replay through the ordinary runtime binding merger.  Consequently the total
fallback in `restrictBnd` is unreachable on every semantic input. -/
theorem restrictBnd_mem_merge
    {bindings : Metta.Bindings} {valuation : String → Metta.Atom}
    (bindingsNoFloat : LeaBindingsNoFloat bindings)
    (satisfied : LeaBindingSatisfied valuation bindings)
    (scopeVars : List String) :
    Metta.Minimal.restrictBnd scopeVars bindings ∈
      Metta.Bindings.merge []
        (Metta.Minimal.restrictBndRaw scopeVars bindings) := by
  let raw := Metta.Minimal.restrictBndRaw scopeVars bindings
  have rawNoFloat : LeaBindingsNoFloat raw := by
    exact restrictBndRaw_noFloat bindingsNoFloat scopeVars
  have rawSatisfied : LeaBindingSatisfied valuation raw := by
    exact restrictBndRaw_satisfied_of_satisfied satisfied scopeVars
  obtain ⟨output, outputMember, _outputSatisfied, _outputNoFloat⟩ :=
    LeaTTaMergeExistence.merge_exists_of_satisfied
      (valuation := valuation) (left := []) (right := raw)
      (by simp [LeaBindingsNoFloat]) rawNoFloat
      (by simp [LeaBindingSatisfied]) rawSatisfied
  change ((Metta.Bindings.merge [] raw).head?).getD raw ∈
    Metta.Bindings.merge [] raw
  cases mergeEquation : Metta.Bindings.merge [] raw with
  | nil => simp [mergeEquation] at outputMember
  | cons head tail => simp

/-- Every model of a reachable binding record remains a model of its
canonically replayed evaluator-visible projection. -/
theorem restrictBnd_satisfied_of_satisfied
    {bindings : Metta.Bindings} {valuation : String → Metta.Atom}
    (bindingsNoFloat : LeaBindingsNoFloat bindings)
    (satisfied : LeaBindingSatisfied valuation bindings)
    (scopeVars : List String) :
    LeaBindingSatisfied valuation
      (Metta.Minimal.restrictBnd scopeVars bindings) := by
  have rawNoFloat := restrictBndRaw_noFloat bindingsNoFloat scopeVars
  have member := restrictBnd_mem_merge bindingsNoFloat satisfied scopeVars
  exact (leaMerge_solution_iff valuation
    (by simp [LeaBindingsNoFloat]) rawNoFloat member).mpr
      ⟨by simp [LeaBindingSatisfied],
        restrictBndRaw_satisfied_of_satisfied satisfied scopeVars⟩

/-- Every model of the canonical visible projection extends to a model of
the complete reachable runtime theory while preserving the requested
variables. -/
theorem restrictBnd_exists_satisfied_extension
    {bindings : Metta.Bindings}
    (invariant :
      LeaTTaSpecConformance.LeaRuntimeBindingInvariant bindings)
    (scopeVars : List String) (projected : String → Metta.Atom)
    (projectedSatisfied : LeaBindingSatisfied projected
      (Metta.Minimal.restrictBnd scopeVars bindings)) :
    ∃ complete : String → Metta.Atom,
      LeaBindingSatisfied complete bindings ∧
        ∀ name ∈ scopeVars, complete name = projected name := by
  have member := restrictBnd_mem_merge invariant.noFloat
    invariant.canonical.1 scopeVars
  have rawNoFloat := restrictBndRaw_noFloat invariant.noFloat scopeVars
  have rawSatisfied : LeaBindingSatisfied projected
      (Metta.Minimal.restrictBndRaw scopeVars bindings) :=
    ((leaMerge_solution_iff projected
      (by simp [LeaBindingsNoFloat]) rawNoFloat member).mp
        projectedSatisfied).2
  exact restrictBndRaw_exists_satisfied_extension
    invariant scopeVars projected rawSatisfied

/-- Canonical replay preserves exact HE-image provenance. -/
theorem restrictBnd_heImage
    {bindings : Metta.Bindings} (bindingsImage : LeaBindingsHEImage bindings)
    (scopeVars : List String) :
    LeaBindingsHEImage (Metta.Minimal.restrictBnd scopeVars bindings) := by
  let raw := Metta.Minimal.restrictBndRaw scopeVars bindings
  have rawImage : LeaBindingsHEImage raw :=
    restrictBndRaw_heImage bindingsImage scopeVars
  unfold Metta.Minimal.restrictBnd
  change LeaBindingsHEImage
    ((Metta.Bindings.merge [] raw).head?.getD raw)
  cases mergeEquation : Metta.Bindings.merge [] raw with
  | nil => simpa [mergeEquation] using rawImage
  | cons output outputs =>
      have outputMember : output ∈ Metta.Bindings.merge [] raw := by
        rw [mergeEquation]
        simp
      have outputImage := leaMerge_result_image
        (left := ([] : Metta.Bindings)) (right := raw)
        (by simp [LeaBindingsHEImage]) rawImage outputMember
      simpa [mergeEquation] using outputImage

/-- Canonical replay preserves the host-float-free semantic domain. -/
theorem restrictBnd_noFloat
    {bindings : Metta.Bindings} (bindingsNoFloat : LeaBindingsNoFloat bindings)
    (scopeVars : List String) :
    LeaBindingsNoFloat (Metta.Minimal.restrictBnd scopeVars bindings) := by
  let raw := Metta.Minimal.restrictBndRaw scopeVars bindings
  have rawNoFloat : LeaBindingsNoFloat raw :=
    restrictBndRaw_noFloat bindingsNoFloat scopeVars
  unfold Metta.Minimal.restrictBnd
  change LeaBindingsNoFloat
    ((Metta.Bindings.merge [] raw).head?.getD raw)
  cases mergeEquation : Metta.Bindings.merge [] raw with
  | nil => simpa [mergeEquation] using rawNoFloat
  | cons output outputs =>
      have outputMember : output ∈ Metta.Bindings.merge [] raw := by
        rw [mergeEquation]
        simp
      have outputNoFloat := leaMerge_result_noFloat
        (left := ([] : Metta.Bindings)) (right := raw)
        (by simp [LeaBindingsNoFloat]) rawNoFloat outputMember
      simpa [mergeEquation] using outputNoFloat

/-- Canonical replay never reintroduces bare-variable value assignments. -/
theorem restrictBnd_assignmentsNonVariable
    (bindings : Metta.Bindings) (scopeVars : List String) :
    LeaAssignmentsNonVariable
      (Metta.Minimal.restrictBnd scopeVars bindings) := by
  let raw := Metta.Minimal.restrictBndRaw scopeVars bindings
  have rawNormalized : LeaAssignmentsNonVariable raw :=
    restrictBndRaw_assignmentsNonVariable bindings scopeVars
  unfold Metta.Minimal.restrictBnd
  change LeaAssignmentsNonVariable
    ((Metta.Bindings.merge [] raw).head?.getD raw)
  cases mergeEquation : Metta.Bindings.merge [] raw with
  | nil => simpa [mergeEquation] using rawNormalized
  | cons output outputs =>
      have outputMember : output ∈ Metta.Bindings.merge [] raw := by
        rw [mergeEquation]
        simp
      have outputNormalized := leaMerge_result_assignmentsNonVariable
        (left := ([] : Metta.Bindings)) (right := raw)
        leaAssignmentsNonVariable_empty outputMember
      simpa [mergeEquation] using outputNormalized

/-- Canonical replay preserves equality irreflexivity. -/
theorem restrictBnd_equalitiesIrreflexive
    {bindings : Metta.Bindings}
    (irreflexive : LeaEqualitiesIrreflexive bindings)
    (scopeVars : List String) :
    LeaEqualitiesIrreflexive
      (Metta.Minimal.restrictBnd scopeVars bindings) := by
  let raw := Metta.Minimal.restrictBndRaw scopeVars bindings
  have rawIrreflexive : LeaEqualitiesIrreflexive raw :=
    restrictBndRaw_equalitiesIrreflexive irreflexive scopeVars
  unfold Metta.Minimal.restrictBnd
  change LeaEqualitiesIrreflexive
    ((Metta.Bindings.merge [] raw).head?.getD raw)
  cases mergeEquation : Metta.Bindings.merge [] raw with
  | nil => simpa [mergeEquation] using rawIrreflexive
  | cons output outputs =>
      have outputMember : output ∈ Metta.Bindings.merge [] raw := by
        rw [mergeEquation]
        simp
      have outputIrreflexive := leaMerge_result_equalitiesIrreflexive
        (left := ([] : Metta.Bindings)) (right := raw)
        leaEqualitiesIrreflexive_empty outputMember
      simpa [mergeEquation] using outputIrreflexive

/-- Reachable visible projections carry the complete runtime binding
invariant because the producer canonically replays the raw projection from
the invariant empty accumulator. -/
theorem restrictBnd_runtimeInvariant
    {bindings : Metta.Bindings}
    (invariant :
      LeaTTaSpecConformance.LeaRuntimeBindingInvariant bindings)
    (scopeVars : List String) :
    LeaTTaSpecConformance.LeaRuntimeBindingInvariant
      (Metta.Minimal.restrictBnd scopeVars bindings) := by
  have member := restrictBnd_mem_merge invariant.noFloat
    invariant.canonical.1 scopeVars
  have rawNoFloat := restrictBndRaw_noFloat invariant.noFloat scopeVars
  have projectedSatisfied := restrictBnd_satisfied_of_satisfied
    invariant.noFloat invariant.canonical.1 scopeVars
  have projectedNonVariable :=
    restrictBnd_assignmentsNonVariable bindings scopeVars
  have projectedIrreflexive := restrictBnd_equalitiesIrreflexive
    invariant.equalitiesIrreflexive scopeVars
  have projectedLoopFree :
      (Metta.Minimal.restrictBnd scopeVars bindings).hasLoop = false :=
    leaBindings_hasLoop_false_of_satisfied projectedSatisfied
      projectedNonVariable projectedIrreflexive
  exact LeaTTaSpecConformance.leaRuntimeBindingInvariant_empty.merge
    rawNoFloat member projectedLoopFree

/-- Every projection of a reachable runtime binding passes the executable
loop gate.  The proof is semantic: an original canonical model satisfies the
projection, and the two preceding representation lemmas discharge the
normalized-loop criterion. -/
theorem restrictBnd_hasLoop_false
    {bindings : Metta.Bindings}
    (invariant :
      LeaTTaSpecConformance.LeaRuntimeBindingInvariant bindings)
    (scopeVars : List String) :
    (Metta.Minimal.restrictBnd scopeVars bindings).hasLoop = false := by
  exact (restrictBnd_runtimeInvariant invariant scopeVars).loopFree

/-- Scoped type-presentation simulation retains the runtime's complete
reachable binding invariant. -/
theorem scopedTypePresentationSimulationState_runtimeInvariant
    {scope : List String}
    {presentation : Spec.Type.Presentation.TypeSubst}
    {runtimeBindings : Metta.Bindings}
    (state : ScopedTypePresentationSimulationState
      scope presentation runtimeBindings) :
    LeaTTaSpecConformance.LeaRuntimeBindingInvariant runtimeBindings := by
  rcases state with
    ⟨_normal, branchPresentation, specBindings, branchState, _theory⟩
  exact branchState.semantic.runtime

/-! ## Exact runtime seed algebra -/

/-- Every concrete application seed constructed from an arbitrary successful
operator-head theory denotes exactly the conjunction of the incoming runtime
theory and the evaluator-visible projection of that head theory.  This is the
generic repair-19 boundary; selected-policy helpers below are projections of
it, while the operator-head cast consumes it directly. -/
theorem selectedApplicationInitialBindingsFromTheory_member_solution_iff
    {incoming theory seed : Metta.Bindings}
    (incomingInvariant :
      LeaTTaSpecConformance.LeaRuntimeBindingInvariant incoming)
    (theoryInvariant :
      LeaTTaSpecConformance.LeaRuntimeBindingInvariant theory)
    (expression expected : Metta.Atom)
    (member : seed ∈
      Metta.Minimal.selectedApplicationInitialBindingsFromTheory
        incoming expression expected theory)
    (valuation : String → Metta.Atom) :
    LeaBindingSatisfied valuation seed ↔
      LeaBindingSatisfied valuation incoming ∧
        LeaBindingSatisfied valuation
          (Metta.Minimal.restrictBnd
            (Metta.Minimal.expectedApplicationVisibleScope expression expected)
            theory) := by
  apply leaMerge_solution_iff valuation incomingInvariant.noFloat
    (restrictBnd_noFloat theoryInvariant.noFloat _)
  simpa [Metta.Minimal.selectedApplicationInitialBindingsFromTheory] using member

/-- A seed produced from an arbitrary successful operator-head theory remains
host-float-free. -/
theorem selectedApplicationInitialBindingsFromTheory_member_noFloat
    {incoming theory seed : Metta.Bindings}
    (incomingInvariant :
      LeaTTaSpecConformance.LeaRuntimeBindingInvariant incoming)
    (theoryInvariant :
      LeaTTaSpecConformance.LeaRuntimeBindingInvariant theory)
    (expression expected : Metta.Atom)
    (member : seed ∈
      Metta.Minimal.selectedApplicationInitialBindingsFromTheory
        incoming expression expected theory) :
    LeaBindingsNoFloat seed := by
  apply leaMerge_result_noFloat incomingInvariant.noFloat
    (restrictBnd_noFloat theoryInvariant.noFloat _)
  simpa [Metta.Minimal.selectedApplicationInitialBindingsFromTheory] using member

/-- Exact HE-image provenance is closed under the general head-theory seed
merge. -/
theorem selectedApplicationInitialBindingsFromTheory_member_heImage
    {incoming theory seed : Metta.Bindings}
    (incomingImage : LeaBindingsHEImage incoming)
    (theoryImage : LeaBindingsHEImage theory)
    (expression expected : Metta.Atom)
    (member : seed ∈
      Metta.Minimal.selectedApplicationInitialBindingsFromTheory
        incoming expression expected theory) :
    LeaBindingsHEImage seed := by
  apply leaMerge_result_image incomingImage
    (restrictBnd_heImage theoryImage
      (Metta.Minimal.expectedApplicationVisibleScope expression expected))
  simpa [Metta.Minimal.selectedApplicationInitialBindingsFromTheory] using member

/-- Any common model of the incoming runtime theory and the visible
operator-head theory produces at least one repair-19 application seed. -/
theorem selectedApplicationInitialBindingsFromTheory_exists_of_common_model
    {incoming theory : Metta.Bindings}
    (incomingInvariant :
      LeaTTaSpecConformance.LeaRuntimeBindingInvariant incoming)
    (theoryInvariant :
      LeaTTaSpecConformance.LeaRuntimeBindingInvariant theory)
    (expression expected : Metta.Atom)
    (valuation : String → Metta.Atom)
    (incomingSatisfied : LeaBindingSatisfied valuation incoming)
    (visibleSatisfied : LeaBindingSatisfied valuation
      (Metta.Minimal.restrictBnd
        (Metta.Minimal.expectedApplicationVisibleScope expression expected)
        theory)) :
    ∃ seed,
      seed ∈ Metta.Minimal.selectedApplicationInitialBindingsFromTheory
        incoming expression expected theory ∧
        LeaBindingSatisfied valuation seed ∧ LeaBindingsNoFloat seed := by
  obtain ⟨seed, member, satisfied, noFloat⟩ :=
    LeaTTaMergeExistence.merge_exists_of_satisfied
      incomingInvariant.noFloat
      (restrictBnd_noFloat theoryInvariant.noFloat _)
      incomingSatisfied visibleSatisfied
  exact ⟨seed, by
    simpa [Metta.Minimal.selectedApplicationInitialBindingsFromTheory] using member,
      satisfied, noFloat⟩

/-- A loop-free seed produced from an arbitrary successful operator-head
theory carries the full reachable runtime invariant required by both argument
evaluation and rule reduction. -/
theorem selectedApplicationInitialBindingsFromTheory_member_runtimeInvariant
    {incoming theory seed : Metta.Bindings}
    (incomingInvariant :
      LeaTTaSpecConformance.LeaRuntimeBindingInvariant incoming)
    (theoryInvariant :
      LeaTTaSpecConformance.LeaRuntimeBindingInvariant theory)
    (expression expected : Metta.Atom)
    (member : seed ∈
      Metta.Minimal.selectedApplicationInitialBindingsFromTheory
        incoming expression expected theory)
    (loopFree : seed.hasLoop = false) :
    LeaTTaSpecConformance.LeaRuntimeBindingInvariant seed := by
  apply incomingInvariant.merge
    (restrictBnd_noFloat theoryInvariant.noFloat _)
    (by
      simpa [Metta.Minimal.selectedApplicationInitialBindingsFromTheory] using member)
    loopFree

/-- The selected policy's evaluator-visible projection stays in the semantic
domain carried by the exact type-presentation simulation. -/
theorem selectedApplicationVisibleBindings_noFloat
    {scope : List String}
    {presentation : Spec.Type.Presentation.TypeSubst}
    {selected : Metta.Minimal.SelectedFunctionType}
    (state : ScopedTypePresentationSimulationState
      scope presentation selected.typeBindings)
    (expression expected : Metta.Atom) :
    LeaBindingsNoFloat
      (Metta.Minimal.selectedApplicationVisibleBindings
        expression expected selected) := by
  exact restrictBnd_noFloat
    (scopedTypePresentationSimulationState_runtimeInvariant state).noFloat _

/-- The selected policy's visible binding projection is itself a reachable
runtime binding state, ready to seed recursive expected-aware evaluation. -/
theorem selectedApplicationVisibleBindings_runtimeInvariant
    {scope : List String}
    {presentation : Spec.Type.Presentation.TypeSubst}
    {selected : Metta.Minimal.SelectedFunctionType}
    (state : ScopedTypePresentationSimulationState
      scope presentation selected.typeBindings)
    (expression expected : Metta.Atom) :
    LeaTTaSpecConformance.LeaRuntimeBindingInvariant
      (Metta.Minimal.selectedApplicationVisibleBindings
        expression expected selected) := by
  exact restrictBnd_runtimeInvariant
    (scopedTypePresentationSimulationState_runtimeInvariant state) _

/-- Every concrete selected-application seed denotes exactly the conjunction
of the incoming runtime theory and the evaluator-visible selected theory.
This is the runtime half of the published `for b in succs` boundary. -/
theorem selectedApplicationInitialBindings_member_solution_iff
    {scope : List String}
    {presentation : Spec.Type.Presentation.TypeSubst}
    {incoming seed : Metta.Bindings}
    {selected : Metta.Minimal.SelectedFunctionType}
    (incomingInvariant :
      LeaTTaSpecConformance.LeaRuntimeBindingInvariant incoming)
    (selectedState : ScopedTypePresentationSimulationState
      scope presentation selected.typeBindings)
    (expression expected : Metta.Atom)
    (member : seed ∈
      Metta.Minimal.selectedApplicationInitialBindings
        incoming expression expected selected)
    (valuation : String → Metta.Atom) :
    LeaBindingSatisfied valuation seed ↔
      LeaBindingSatisfied valuation incoming ∧
        LeaBindingSatisfied valuation
          (Metta.Minimal.selectedApplicationVisibleBindings
            expression expected selected) := by
  simpa [Metta.Minimal.selectedApplicationInitialBindings,
      Metta.Minimal.selectedApplicationVisibleBindings] using
    selectedApplicationInitialBindingsFromTheory_member_solution_iff
      incomingInvariant
      (scopedTypePresentationSimulationState_runtimeInvariant selectedState)
      expression expected
      (by
        simpa [Metta.Minimal.selectedApplicationInitialBindings] using member)
      valuation

/-- A produced selected-application seed remains host-float-free. -/
theorem selectedApplicationInitialBindings_member_noFloat
    {scope : List String}
    {presentation : Spec.Type.Presentation.TypeSubst}
    {incoming seed : Metta.Bindings}
    {selected : Metta.Minimal.SelectedFunctionType}
    (incomingInvariant :
      LeaTTaSpecConformance.LeaRuntimeBindingInvariant incoming)
    (selectedState : ScopedTypePresentationSimulationState
      scope presentation selected.typeBindings)
    (expression expected : Metta.Atom)
    (member : seed ∈
      Metta.Minimal.selectedApplicationInitialBindings
        incoming expression expected selected) :
    LeaBindingsNoFloat seed := by
  exact selectedApplicationInitialBindingsFromTheory_member_noFloat
    incomingInvariant
    (scopedTypePresentationSimulationState_runtimeInvariant selectedState)
    expression expected
    (by
      simpa [Metta.Minimal.selectedApplicationInitialBindings] using member)

/-- Exact HE-image provenance is closed under the selected seed merge.  The
image hypotheses are deliberately separate from semantic simulation: not
every host-float-free grounded value lies in the structural HE image. -/
theorem selectedApplicationInitialBindings_member_heImage
    {incoming seed : Metta.Bindings}
    {selected : Metta.Minimal.SelectedFunctionType}
    (incomingImage : LeaBindingsHEImage incoming)
    (selectedImage : LeaBindingsHEImage selected.typeBindings)
    (expression expected : Metta.Atom)
    (member : seed ∈
      Metta.Minimal.selectedApplicationInitialBindings
        incoming expression expected selected) :
    LeaBindingsHEImage seed := by
  exact selectedApplicationInitialBindingsFromTheory_member_heImage
    incomingImage selectedImage expression expected
    (by
      simpa [Metta.Minimal.selectedApplicationInitialBindings] using member)

/-- Any common model of the incoming runtime theory and the visible selected
theory produces at least one application seed.  This is the non-vacuity half
of the seed boundary; incompatibility is represented by an empty seed list. -/
theorem selectedApplicationInitialBindings_exists_of_common_model
    {scope : List String}
    {presentation : Spec.Type.Presentation.TypeSubst}
    {incoming : Metta.Bindings}
    {selected : Metta.Minimal.SelectedFunctionType}
    (incomingInvariant :
      LeaTTaSpecConformance.LeaRuntimeBindingInvariant incoming)
    (selectedState : ScopedTypePresentationSimulationState
      scope presentation selected.typeBindings)
    (expression expected : Metta.Atom)
    (valuation : String → Metta.Atom)
    (incomingSatisfied : LeaBindingSatisfied valuation incoming)
    (visibleSatisfied : LeaBindingSatisfied valuation
      (Metta.Minimal.selectedApplicationVisibleBindings
        expression expected selected)) :
    ∃ seed,
      seed ∈ Metta.Minimal.selectedApplicationInitialBindings
        incoming expression expected selected ∧
        LeaBindingSatisfied valuation seed ∧
          LeaBindingsNoFloat seed := by
  obtain ⟨seed, member, satisfied, noFloat⟩ :=
    selectedApplicationInitialBindingsFromTheory_exists_of_common_model
      incomingInvariant
      (scopedTypePresentationSimulationState_runtimeInvariant selectedState)
      expression expected valuation incomingSatisfied
      (by
        simpa [Metta.Minimal.selectedApplicationVisibleBindings] using
          visibleSatisfied)
  exact ⟨seed, by
    simpa [Metta.Minimal.selectedApplicationInitialBindings] using member,
      satisfied, noFloat⟩

/-- A loop-free selected seed carries the full reachable runtime binding
invariant required by recursive evaluator calls.  Loop-freedom remains an
explicit operational gate; it is never inferred from mere merge membership. -/
theorem selectedApplicationInitialBindings_member_runtimeInvariant
    {scope : List String}
    {presentation : Spec.Type.Presentation.TypeSubst}
    {incoming seed : Metta.Bindings}
    {selected : Metta.Minimal.SelectedFunctionType}
    (incomingInvariant :
      LeaTTaSpecConformance.LeaRuntimeBindingInvariant incoming)
    (selectedState : ScopedTypePresentationSimulationState
      scope presentation selected.typeBindings)
    (expression expected : Metta.Atom)
    (member : seed ∈
      Metta.Minimal.selectedApplicationInitialBindings
        incoming expression expected selected)
    (loopFree : seed.hasLoop = false) :
    LeaTTaSpecConformance.LeaRuntimeBindingInvariant seed := by
  exact selectedApplicationInitialBindingsFromTheory_member_runtimeInvariant
    incomingInvariant
    (scopedTypePresentationSimulationState_runtimeInvariant selectedState)
    expression expected
    (by
      simpa [Metta.Minimal.selectedApplicationInitialBindings] using member)
    loopFree

end Mettapedia.Languages.MeTTa.HE.LeaTTaExpectedBindingThreadingConformance
