import Mettapedia.GSLT.Logic.BagRelativePushout
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalStepperCompleteness
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.ParallelContextAdequacy

/-!
# Rho as a bag reactive system

Rho reduces only at the top of its parallel soup: COMM fires between an
output and an input that sit side by side, parallel composition carries a
step through its siblings, and nothing reduces under a prefix or inside a
quotation.  So the contexts in which rho reacts are exactly parallel
contexts, and a process is, for the purposes of reaction, the multiset of its
parallel components.

This module makes that reading exact.

* **Components.**  `components P` is the multiset of non-parallel, non-inert
  pieces of the canonical form of `P`.  Two pure processes have the same
  components exactly when they are structurally congruent.
* **Rules.**  A COMM instance `{x!(q), for(y<-x)p}` is a reaction rule of the
  bag context category of `BagRelativePushout`: its redex is the component
  multiset of the COMM source, its reactum the component multiset of
  `p{@q/y}`.
* **Labels.**  A transition labelled by parallel partners exists exactly when
  the process and the partners form a COMM redex beside a context that shares
  nothing with the partners; so every least label is drawn from one redex, the
  shape `− | in(n, λx.q)`.
* **Adequacy.**  A process reduces exactly when its component multiset reacts,
  with the identity label, in that reactive system: for the paper relation
  `Reduction.Reduces` on the pure carrier (`reduces_iff_actIPO_identity`), and
  for the established rho GSLT on closed processes
  (`step_iff_actIPO_identity`).

The controls fire COMM on a shared channel, refuse it across different
channels, refuse a label carrying an idle partner, and refuse reaction under
an input prefix.  `Conditions201202` derives Conditions 20.1 and 20.2 of
*Finding Mind* for rho from this presentation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.RhoBagReactiveSystem

open _root_.CategoryTheory
open Mettapedia.GSLT.RelativePushout
open Mettapedia.GSLT.RedexRelativeCongruence (ReactionRule ActIPO IPOBisimilar)
open Mettapedia.GSLT.BagRelativePushout (Bag bag bag_comp bag_injective bag_surjective
  isIdemPushout_bag isIdemPushout_bag_iff)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.PureBoundary
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalStepperCompleteness
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.SubstitutionCanonicalCommutation
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalTyping
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.OSLF.Framework.ConstructorCategory (rhoProc)
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.ParallelContextAdequacy
  (waitingInput outputPartner)

/-! ## Parallel components -/

/-- The parallel components of a process: the non-parallel, non-inert pieces
of its canonical form, as a multiset. -/
def components (process : Pattern) : Multiset Pattern :=
  (bagContents [canonicalize process] : List Pattern)

/-- A canonical form is rebuilt from its sorted components. -/
theorem canonicalize_eq_collapseBag_sortPatterns (process : Pattern) :
    canonicalize process =
      collapseBag (sortPatterns (bagContents [canonicalize process])) := by
  rw [← normalizeBagElements_eq_sort_bagContents]
  exact (collapse_normalize_singleton_of_isCanonical (canonicalize_isCanonical process)).symm

/-- Components determine the canonical form, and conversely. -/
theorem components_eq_iff_canonicalize_eq {left right : Pattern} :
    components left = components right ↔ canonicalize left = canonicalize right := by
  constructor
  · intro equal
    have perm : List.Perm (bagContents [canonicalize left]) (bagContents [canonicalize right]) :=
      Multiset.coe_eq_coe.mp equal
    calc canonicalize left
        = collapseBag (sortPatterns (bagContents [canonicalize left])) :=
          canonicalize_eq_collapseBag_sortPatterns left
      _ = collapseBag (sortPatterns (bagContents [canonicalize right])) := by
          rw [sortPatterns_eq_of_perm perm]
      _ = canonicalize right := (canonicalize_eq_collapseBag_sortPatterns right).symm
  · intro equal
    simp only [components, equal]

/-- Equal components give structurally congruent processes. -/
theorem structuralCongruence_of_components_eq {left right : Pattern}
    (equal : components left = components right) : StructuralCongruence left right :=
  structuralCongruence_of_canonicalize_eq (components_eq_iff_canonicalize_eq.mp equal)

/-- On the pure carrier, structurally congruent processes have equal
components. -/
theorem components_eq_of_structuralCongruence {left right : Pattern}
    (leftTwoSort : HashSetFree left) (rightTwoSort : HashSetFree right)
    (congruence : StructuralCongruence left right) : components left = components right :=
  components_eq_iff_canonicalize_eq.mpr
    (canonicalize_eq_of_structuralCongruence congruence leftTwoSort rightTwoSort)

/-- **Components are structural congruence classes** on the pure carrier. -/
theorem components_eq_iff_structuralCongruence {left right : Pattern}
    (leftTwoSort : HashSetFree left) (rightTwoSort : HashSetFree right) :
    components left = components right ↔ StructuralCongruence left right :=
  ⟨structuralCongruence_of_components_eq,
    components_eq_of_structuralCongruence leftTwoSort rightTwoSort⟩

/-- The contents of a list, as a multiset, is the sum of the contents of its
members. -/
theorem coe_bagContents_eq_sum (patterns : List Pattern) :
    ((bagContents patterns : List Pattern) : Multiset Pattern) =
      (patterns.map fun pattern =>
        ((bagContents [pattern] : List Pattern) : Multiset Pattern)).sum := by
  induction patterns with
  | nil => simp [bagContents]
  | cons head tail inductionHypothesis =>
      rw [bagContents_cons, ← Multiset.coe_add, inductionHypothesis]
      simp

/-- **A parallel composition has the sum of its members' components.** -/
theorem components_parallel (elements : List Pattern) :
    components (.collection .hashBag elements none) = (elements.map components).sum := by
  unfold components
  rw [canonicalize_bag,
    bagContents_collapse_normalized (isCanonicalList_map_canonicalize' elements),
    normalizeBagElements_eq_sort_bagContents,
    ← Multiset.coe_eq_coe.mpr (sortPatterns_perm _), coe_bagContents_eq_sum, List.map_map]
  rfl

/-- Every component is a canonical pattern that is neither inert nor
parallel. -/
theorem mem_components {process atom : Pattern} (membership : atom ∈ components process) :
    IsCanonical atom ∧ atom ≠ .apply "PZero" [] ∧
      ∀ nested, atom ≠ .collection .hashBag nested none := by
  have listed : atom ∈ normalizeBagElements ([process].map canonicalize) := by
    rw [normalizeBagElements_eq_sort_bagContents]
    exact sortPatterns_mem_iff.mpr (Multiset.mem_coe.mp membership)
  exact ⟨(canonicalList_facts [process]).1 atom listed,
    (canonicalList_facts [process]).2.1 atom listed,
    (canonicalList_facts [process]).2.2 atom listed⟩

/-- A component is its own only component. -/
theorem components_of_mem {process atom : Pattern} (membership : atom ∈ components process) :
    components atom = {atom} := by
  obtain ⟨canonical, noZero, noBag⟩ := mem_components membership
  unfold components
  rw [canonicalize_eq_of_isCanonical canonical, bagContents_singleton_of_plain noZero noBag]
  rfl

/-- A list of components contributes exactly itself. -/
theorem sum_map_components_of_le {process : Pattern} {atoms : List Pattern}
    (le : (atoms : Multiset Pattern) ≤ components process) :
    (atoms.map components).sum = atoms := by
  induction atoms with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      have headMember : head ∈ components process :=
        Multiset.mem_of_le le (Multiset.mem_coe.mpr (List.mem_cons_self))
      have tailLe : (tail : Multiset Pattern) ≤ components process :=
        le_trans (Multiset.coe_le.mpr (List.sublist_cons_self head tail).subperm) le
      rw [List.map_cons, List.sum_cons, components_of_mem headMember,
        inductionHypothesis tailLe, Multiset.singleton_add, Multiset.cons_coe]

/-- The inert process `0`. -/
abbrev inert : Pattern := .apply "PZero" []

/-- The inert process has no components. -/
theorem components_inert : components inert = 0 := by
  rfl

theorem components_output (channel payload : Pattern) :
    components (.apply "POutput" [channel, payload]) =
      {.apply "POutput" [canonicalize channel, canonicalize payload]} := by
  unfold components
  rw [canonicalize_output, bagContents_singleton_of_plain (by simp) (by simp)]
  rfl

theorem components_input (channel body : Pattern) :
    components (.apply "PInput" [channel, .lambda none body]) =
      {.apply "PInput" [canonicalize channel, .lambda none (canonicalize body)]} := by
  unfold components
  rw [canonicalize_input, bagContents_singleton_of_plain (by simp) (by simp)]
  rfl

/-! ## The COMM rules -/

/-- The single interface of the bag context category over rho patterns. -/
abbrev parallelInterface : SingleObj (Bag Pattern) := BagRelativePushout.Obj Pattern

/-- A process, as an agent of the bag context category: its components. -/
def agent (process : Pattern) : parallelInterface ⟶ parallelInterface :=
  bag (components process)

/-- The COMM source `{x!(q), for(y<-x)p}`. -/
def commSource (channel body payload : Pattern) : Pattern :=
  .collection .hashBag
    [.apply "POutput" [channel, payload], .apply "PInput" [channel, .lambda none body]] none

theorem components_commSource (channel body payload : Pattern) :
    components (commSource channel body payload) =
      {.apply "POutput" [canonicalize channel, canonicalize payload],
        .apply "PInput" [canonicalize channel, .lambda none (canonicalize body)]} := by
  rw [commSource, components_parallel]
  simp [components_output, components_input, Multiset.singleton_add]

/-- **The COMM instance as a reaction rule**: the components of
`{x!(q), for(y<-x)p}` react to the components of `p{@q/y}`. -/
def commRule (channel body payload : Pattern) : ReactionRule parallelInterface where
  codomain := parallelInterface
  redex := bag (components (commSource channel body payload))
  reactum := bag (components (semanticCommSubst body payload))

/-- The COMM instances satisfying an admissibility condition on their
source. -/
def commRulesWhere (admissible : Pattern → Prop) : ReactionRule parallelInterface → Prop :=
  fun rule => ∃ channel body payload,
    admissible (commSource channel body payload) ∧ rule = commRule channel body payload

/-- COMM instances on the pure (hash-set-free) carrier. -/
def pureCommRules : ReactionRule parallelInterface → Prop :=
  commRulesWhere HashSetFree

/-! ## Labelled transitions -/

/-- **The labelled transitions of a COMM rule family.**  A process with
components `source` has a transition labelled by the parallel partners
`label` exactly when `source` together with `label` is a COMM redex beside a
reaction context that shares nothing with the label; the target is the
reactum beside that context. -/
theorem actIPO_bag_iff (admissible : Pattern → Prop) (label source target : Multiset Pattern) :
    ActIPO (commRulesWhere admissible) (bag label) (bag source) (bag target) ↔
      ∃ channel body payload, admissible (commSource channel body payload) ∧
        ∃ context : Multiset Pattern,
          source + label = components (commSource channel body payload) + context ∧
          label ∩ context = 0 ∧
          target = components (semanticCommSubst body payload) + context := by
  constructor
  · rintro ⟨rule, ⟨channel, body, payload, sourceAllowed, rfl⟩, reaction, square, ipo, targetEq⟩
    -- Every arrow of the bag category is the bag of its own coordinates.
    let context : Multiset Pattern := Multiplicative.toAdd reaction
    refine ⟨channel, body, payload, sourceAllowed, context, ?_, ?_, ?_⟩
    · have coordinates : bag source ≫ bag label =
          bag (components (commSource channel body payload)) ≫ bag context := square
      rw [bag_comp, bag_comp] at coordinates
      exact bag_injective coordinates
    · exact (isIdemPushout_bag_iff source _ label context square).mp ipo
    · have coordinates : bag target =
          bag (components (semanticCommSubst body payload)) ≫ bag context := targetEq
      rw [bag_comp] at coordinates
      exact bag_injective coordinates
  · rintro ⟨channel, body, payload, sourceAllowed, context, sourceEq, disjoint, targetEq⟩
    have square : bag source ≫ bag label =
        bag (components (commSource channel body payload)) ≫ bag context := by
      rw [bag_comp, bag_comp, sourceEq]
    refine ⟨commRule channel body payload, ⟨channel, body, payload, sourceAllowed, rfl⟩,
      bag context, square, isIdemPushout_bag source _ label context square disjoint, ?_⟩
    change bag target = bag (components (semanticCommSubst body payload)) ≫ bag context
    rw [bag_comp, targetEq]

/-- **Identity-labelled transitions of a COMM rule family are its
reactions**: a rule's redex beside a reaction context becomes its reactum
beside the same context.  The identity label is always least. -/
theorem actIPO_identity_iff (admissible : Pattern → Prop) (source target : Multiset Pattern) :
    ActIPO (commRulesWhere admissible) (𝟙 parallelInterface) (bag source) (bag target) ↔
      ∃ channel body payload, admissible (commSource channel body payload) ∧
        ∃ context : Multiset Pattern,
          source = components (commSource channel body payload) + context ∧
          target = components (semanticCommSubst body payload) + context := by
  change ActIPO _ (bag 0) _ _ ↔ _
  rw [actIPO_bag_iff]
  simp only [add_zero, Multiset.zero_inter, true_and]

/-- **Every label is drawn from one COMM redex**: the least label of a
transition consists of parallel partners that, together with the process,
complete a single `{x!(q), for(y<-x)p}`. -/
theorem label_le_redex {admissible : Pattern → Prop} {label source target : Multiset Pattern}
    (step : ActIPO (commRulesWhere admissible) (bag label) (bag source) (bag target)) :
    ∃ channel body payload, admissible (commSource channel body payload) ∧
      label ≤ components (commSource channel body payload) := by
  obtain ⟨channel, body, payload, sourceAllowed, context, sourceEq, disjoint, -⟩ :=
    (actIPO_bag_iff admissible label source target).mp step
  refine ⟨channel, body, payload, sourceAllowed, Multiset.le_iff_count.mpr fun atom => ?_⟩
  have counts := congrArg (Multiset.count atom) sourceEq
  have shared := congrArg (Multiset.count atom) disjoint
  simp only [Multiset.count_add, Multiset.count_inter, Multiset.count_zero] at counts shared
  omega

/-- A reacting process has, among its components, the output and the input of
the COMM redex. -/
theorem output_input_mem_of_reacts {source channel body payload : Pattern}
    {context : Multiset Pattern}
    (sourceEq : components source = components (commSource channel body payload) + context) :
    .apply "POutput" [canonicalize channel, canonicalize payload] ∈ components source ∧
      .apply "PInput" [canonicalize channel, .lambda none (canonicalize body)] ∈
        components source := by
  rw [sourceEq, components_commSource]
  simp

/-! ## Adequacy for the paper reduction relation -/

/-- Every paper reduction from a pure process is a reaction of a pure COMM
instance on components. -/
theorem reacts_of_reduces {source target : Pattern} (step : Reduces source target) :
    HashSetFree source →
      ∃ channel body payload, HashSetFree (commSource channel body payload) ∧
        ∃ context : Multiset Pattern,
          components source = components (commSource channel body payload) + context ∧
          components target = components (semanticCommSubst body payload) + context := by
  induction step with
  | @comm channel payload body rest =>
      intro pure
      simp only [HashSetFree, List.cons_append, List.nil_append, HashSetFreeList] at pure
      refine ⟨channel, body, payload, ?_, (rest.map components).sum, ?_, ?_⟩
      · simp only [commSource, HashSetFree, HashSetFreeList]
        exact ⟨pure.1, pure.2.1, trivial⟩
      · rw [components_parallel, commSource, components_parallel]
        simp [add_assoc]
      · rw [components_parallel]
        simp
  | @equiv source source' target target' sourceCongruence _ targetCongruence
      inductionHypothesis =>
      intro pure
      have pure' := (hashSetFree_iff_of_structuralCongruence sourceCongruence).mp pure
      obtain ⟨channel, body, payload, sourceAllowed, context, sourceEq, targetEq⟩ :=
        inductionHypothesis pure'
      have targetPure' := hashSetFree_of_reduces ‹Reduces source' target'› pure'
      have targetPure := (hashSetFree_iff_of_structuralCongruence targetCongruence).mp targetPure'
      refine ⟨channel, body, payload, sourceAllowed, context, ?_, ?_⟩
      · rw [components_eq_of_structuralCongruence pure pure' sourceCongruence, sourceEq]
      · rw [← components_eq_of_structuralCongruence targetPure' targetPure targetCongruence,
          targetEq]
  | @par inner inner' rest _ inductionHypothesis =>
      intro pure
      simp only [HashSetFree, HashSetFreeList] at pure
      obtain ⟨channel, body, payload, sourceAllowed, context, sourceEq, targetEq⟩ :=
        inductionHypothesis pure.1
      refine ⟨channel, body, payload, sourceAllowed, context + (rest.map components).sum, ?_, ?_⟩
      · rw [components_parallel, List.map_cons, List.sum_cons, sourceEq, add_assoc]
      · rw [components_parallel, List.map_cons, List.sum_cons, targetEq, add_assoc]
  | @par_any inner inner' before after _ inductionHypothesis =>
      intro pure
      simp only [HashSetFree] at pure
      rw [hashSetFreeList_append_iff, hashSetFreeList_append_iff] at pure
      simp only [HashSetFreeList] at pure
      obtain ⟨channel, body, payload, sourceAllowed, context, sourceEq, targetEq⟩ :=
        inductionHypothesis pure.1.2.1
      refine ⟨channel, body, payload, sourceAllowed,
        context + ((before.map components).sum + (after.map components).sum), ?_, ?_⟩
      · rw [components_parallel]
        simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, add_zero, sourceEq]
        abel
      · rw [components_parallel]
        simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, add_zero, targetEq]
        abel

/-- Every reaction of a COMM instance on the components of a process is
realized by a paper reduction of that process. -/
theorem reduces_of_reacts {source channel body payload : Pattern}
    {context : Multiset Pattern}
    (sourceEq : components source = components (commSource channel body payload) + context) :
    ∃ target, Nonempty (Reduces source target) ∧
      components target = components (semanticCommSubst body payload) + context := by
  obtain ⟨residue, residueEq⟩ : ∃ residue : List Pattern,
      (residue : Multiset Pattern) = context := ⟨context.toList, Multiset.coe_toList context⟩
  subst residueEq
  have residueLe : (residue : Multiset Pattern) ≤ components source := by
    rw [sourceEq]
    exact Multiset.le_add_left _ _
  have residueSum := sum_map_components_of_le residueLe
  have presented : components source =
      components (.collection .hashBag
        ([.apply "POutput" [channel, payload], .apply "PInput" [channel, .lambda none body]] ++
          residue) none) := by
    rw [sourceEq, components_parallel, commSource, components_parallel]
    simp [residueSum, add_assoc]
  refine ⟨.collection .hashBag ([semanticCommSubst body payload] ++ residue) none,
    ⟨Reduces.equiv (structuralCongruence_of_components_eq presented) Reduces.comm
      (StructuralCongruence.refl _)⟩, ?_⟩
  rw [components_parallel]
  simp [residueSum]

/-- **Adequacy of the bag reactive system for the paper relation.**  On the
pure carrier, a process reduces to a target exactly when its components react
to the target's components by a pure COMM instance with the identity label.
Targets are determined up to structural congruence, which is equality of
components. -/
theorem reduces_iff_actIPO_identity {source target : Pattern} (pure : HashSetFree source) :
    Nonempty (Reduces source target) ↔
      ActIPO pureCommRules (𝟙 parallelInterface) (agent source) (agent target) := by
  rw [agent, agent, pureCommRules, actIPO_identity_iff]
  constructor
  · rintro ⟨step⟩
    exact reacts_of_reduces step pure
  · rintro ⟨channel, body, payload, -, context, sourceEq, targetEq⟩
    obtain ⟨reached, ⟨step⟩, reachedEq⟩ := reduces_of_reacts sourceEq
    exact ⟨Reduces.equiv (StructuralCongruence.refl _) step
      (structuralCongruence_of_components_eq (reachedEq.trans targetEq.symm))⟩

/-! ## Adequacy for the established rho GSLT -/

/-- COMM instances whose source is a closed rho process. -/
def closedCommRules : ReactionRule parallelInterface → Prop :=
  commRulesWhere (RhoClosedTermWellSorted rhoProc)

/-- A closed COMM instance is a pure one. -/
theorem pureCommRules_of_closedCommRules {rule : ReactionRule parallelInterface}
    (closed : closedCommRules rule) : pureCommRules rule := by
  obtain ⟨channel, body, payload, sourceClosed, ruleEq⟩ := closed
  exact ⟨channel, body, payload, rhoProcWellSorted_hashSetFree
    ((rhoClosedTermWellSorted_process_iff _).mp sourceClosed).1, ruleEq⟩

/-- Every step of the established rho GSLT is a reaction of a closed COMM
instance on components. -/
theorem closedReacts_of_step {source target : RhoProcess}
    (step : rhoLanguageDefGSLT.Step source target) :
    ∃ channel body payload,
      RhoClosedTermWellSorted rhoProc (commSource channel body payload) ∧
        ∃ context : Multiset Pattern,
          components source.1 = components (commSource channel body payload) + context ∧
          components target.1 = components (semanticCommSubst body payload) + context := by
  obtain ⟨redex, contractum, sourceEquation, derivedStep, targetEquation⟩ := step
  have redexClosed := (rhoClosedTermWellSorted_process_iff redex.1).mp redex.2
  obtain ⟨reached, depthOne, reachedEq⟩ :=
    canonicalStep_complete_of_rhoStep redexClosed.1 redexClosed.2 derivedStep
  obtain ⟨bindings, matched, applied⟩ := rhoStepAt_one_inv depthOne
  obtain ⟨elements, termRest, inputIndex, inputBound, outputIndex, outputBound,
    inputChannel, body, inputBinder, outputChannel, payload, shape,
    inputEq, outputEq, channels, bindingsEq⟩ := rhoComm_match_shape matched
  obtain ⟨canonicalTyped, canonicalSafe⟩ := closed_canonicalize redexClosed.1 redexClosed.2
  rw [shape] at canonicalTyped canonicalSafe
  obtain ⟨rfl, elementsTyped⟩ := rho_parallel_wellSorted_inv canonicalTyped
  have canonical := canonicalize_isCanonical redex.1
  rw [shape] at canonical
  obtain ⟨-, -, plain, canonicalList⟩ :
      2 ≤ elements.length ∧ sortPatterns elements = elements ∧
        (∀ element ∈ elements, element ≠ .apply "PZero" [] ∧
          ∀ nested, element ≠ .collection .hashBag nested none) ∧
        IsCanonicalList elements := canonical
  have inputMember : elements[inputIndex] ∈ elements := List.getElem_mem inputBound
  have outputMember : (elements.eraseIdx inputIndex)[outputIndex] ∈ elements :=
    List.mem_of_mem_eraseIdx (List.getElem_mem outputBound)
  have inputCanonical := isCanonicalList_mem canonicalList inputMember
  have outputCanonical := isCanonicalList_mem canonicalList outputMember
  have inputClosed := closed_member canonicalTyped canonicalSafe inputMember
  have outputClosed := closed_member canonicalTyped canonicalSafe outputMember
  rw [inputEq] at inputCanonical inputClosed
  rw [outputEq] at outputCanonical outputClosed
  obtain ⟨rfl, _, bodyTyped⟩ := rho_input_wellSorted_inv inputClosed.1
  obtain ⟨_, payloadTyped⟩ := rho_output_wellSorted_inv outputClosed.1
  rw [isCanonical_apply_general _ _ (by simp)] at inputCanonical outputCanonical
  have inputChannelCanonical : IsCanonical inputChannel := inputCanonical.1
  have bodyCanonical : IsCanonical body := inputCanonical.2.1
  have outputChannelCanonical : IsCanonical outputChannel := outputCanonical.1
  have payloadCanonical : IsCanonical payload := outputCanonical.2.1
  have channelsEq : outputChannel = inputChannel := by
    have equal := (rhoCanonicalEquivalent_iff _ _).mp channels
    rw [canonicalize_eq_of_isCanonical inputChannelCanonical,
      canonicalize_eq_of_isCanonical outputChannelCanonical] at equal
    exact equal.symm
  subst channelsEq
  set residue := (elements.eraseIdx inputIndex).eraseIdx outputIndex with residueDef
  have perm : List.Perm elements
      (.apply "PInput" [outputChannel, .lambda none body] ::
        .apply "POutput" [outputChannel, payload] :: residue) := by
    have extracted := (List.getElem_cons_eraseIdx_perm inputBound).symm.trans
      ((List.getElem_cons_eraseIdx_perm outputBound).symm.cons _)
    rw [inputEq, outputEq] at extracted
    exact extracted
  have redexComponents : components redex.1 = elements := by
    unfold components
    rw [shape]
    simp only [bagContents, List.flatMap_cons, List.flatMap_nil, bagSplice, List.append_nil]
    rw [List.filter_eq_self.mpr (fun element membership => by
      simpa using (plain element membership).1)]
  have residueLe : (residue : Multiset Pattern) ≤ components redex.1 := by
    rw [redexComponents, Multiset.coe_eq_coe.mpr perm, ← Multiset.cons_coe, ← Multiset.cons_coe]
    exact (Multiset.le_cons_self _ _).trans (Multiset.le_cons_self _ _)
  have residueSum := sum_map_components_of_le residueLe
  have closedSource : RhoClosedTermWellSorted rhoProc (commSource outputChannel body payload) :=
    (rhoClosedTermWellSorted_process_iff _).mpr
      ⟨.parallel (.cons outputClosed.1 (.cons inputClosed.1 .nil)), by
        have outputSafe := binderSafe_of_output outputClosed.2
        have inputSafe := binderSafe_of_input inputClosed.2
        simp [commSource, binderSafeAt, binderSafeListAt, outputSafe.1, outputSafe.2,
          inputSafe.2]⟩
  refine ⟨outputChannel, body, payload, closedSource, residue, ?_, ?_⟩
  · rw [components_eq_iff_canonicalize_eq.mpr sourceEquation, redexComponents,
      Multiset.coe_eq_coe.mpr perm, components_commSource,
      canonicalize_eq_of_isCanonical outputChannelCanonical,
      canonicalize_eq_of_isCanonical bodyCanonical,
      canonicalize_eq_of_isCanonical payloadCanonical,
      ← Multiset.cons_coe, ← Multiset.cons_coe, Multiset.insert_eq_cons, Multiset.cons_add,
      Multiset.singleton_add, Multiset.cons_swap]
  · have reachedShape :
        reached = .collection .hashBag (semanticCommSubst body payload :: residue) none := by
      rw [← applied, bindingsEq]
      exact apply_commBindingsAt bodyTyped payloadTyped elements inputIndex outputIndex
        outputChannel
    have targetEq : canonicalize target.1 = canonicalize reached :=
      targetEquation.symm.trans reachedEq.symm
    rw [components_eq_iff_canonicalize_eq.mpr targetEq, reachedShape, components_parallel,
      List.map_cons, List.sum_cons, residueSum]

/-- Every reaction of a closed COMM instance on the components of a closed
process is realized by a step of the established rho GSLT. -/
theorem step_of_closedReacts {source : RhoProcess} {channel body payload : Pattern}
    (closed : RhoClosedTermWellSorted rhoProc (commSource channel body payload))
    {context : Multiset Pattern}
    (sourceEq : components source.1 = components (commSource channel body payload) + context) :
    ∃ target : RhoProcess, rhoLanguageDefGSLT.Step source target ∧
      components target.1 = components (semanticCommSubst body payload) + context := by
  obtain ⟨residue, rfl⟩ : ∃ residue : List Pattern, (residue : Multiset Pattern) = context :=
    ⟨context.toList, Multiset.coe_toList context⟩
  obtain ⟨commTyped, commSafe⟩ := (rhoClosedTermWellSorted_process_iff _).mp closed
  have outputClosed := closed_member commTyped commSafe List.mem_cons_self
  have inputClosed := closed_member commTyped commSafe
    (List.mem_cons_of_mem _ List.mem_cons_self)
  obtain ⟨_, payloadTyped⟩ := rho_output_wellSorted_inv outputClosed.1
  obtain ⟨-, _, bodyTyped⟩ := rho_input_wellSorted_inv inputClosed.1
  have bodySafe := (binderSafe_of_input inputClosed.2).2
  have perm : List.Perm (normalizeBagElements ([source.1].map canonicalize))
      (.apply "PInput" [canonicalize channel, .lambda none (canonicalize body)] ::
        .apply "POutput" [canonicalize channel, canonicalize payload] :: residue) := by
    rw [normalizeBagElements_eq_sort_bagContents]
    refine (sortPatterns_perm _).symm.trans (Multiset.coe_eq_coe.mp ?_)
    change components source.1 = _
    rw [sourceEq, components_commSource, ← Multiset.cons_coe, ← Multiset.cons_coe,
      Multiset.insert_eq_cons, Multiset.cons_add, Multiset.singleton_add, Multiset.cons_swap]
  obtain ⟨tail, fired, tailPerm⟩ := canonical_comm_of_pair
    (canonicalize_procWellSorted _ bodyTyped) (canonicalize_procWellSorted _ payloadTyped)
    ((rhoCanonicalEquivalent_iff _ _).mpr rfl) perm
  rw [canonicalize_parallel_singleton] at fired
  have derived : RhoStep (RhoClosedTerm.canonicalize source).1
      (.collection .hashBag
        (semanticCommSubst (canonicalize body) (canonicalize payload) :: tail) none) :=
    ⟨1, fired⟩
  refine ⟨(RhoClosedTerm.canonicalize source).stepTarget derived,
    ⟨RhoClosedTerm.canonicalize source, (RhoClosedTerm.canonicalize source).stepTarget derived,
      (canonicalize_idempotent source.1).symm, derived, rfl⟩, ?_⟩
  change components (.collection .hashBag
      (semanticCommSubst (canonicalize body) (canonicalize payload) :: tail) none) = _
  have tailSum : (tail.map components).sum = residue := by
    rw [← Multiset.coe_eq_coe.mpr tailPerm, coe_bagContents_eq_sum, List.map_map]
    rfl
  rw [components_parallel, List.map_cons, List.sum_cons, tailSum,
    components_eq_iff_canonicalize_eq.mpr (canonicalize_semanticCommSubst_canonicalize
      bodyTyped bodySafe (rhoProcWellSorted_hashSetFree payloadTyped))]

/-- **Adequacy of the bag reactive system for the established rho GSLT.**  A
closed process steps to a target, modulo the rho equations, exactly when its
components react to the target's components by a closed COMM instance with
the identity label. -/
theorem step_iff_actIPO_identity (source target : RhoProcess) :
    rhoLanguageDefGSLT.Step source target ↔
      ActIPO closedCommRules (𝟙 parallelInterface) (agent source.1) (agent target.1) := by
  rw [agent, agent, closedCommRules, actIPO_identity_iff]
  constructor
  · exact closedReacts_of_step
  · rintro ⟨channel, body, payload, closed, context, sourceEq, targetEq⟩
    obtain ⟨reached, step, reachedEq⟩ := step_of_closedReacts closed sourceEq
    exact rhoLanguageDefGSLT.rewrites_resp_right step
      (components_eq_iff_canonicalize_eq.mp (reachedEq.trans targetEq.symm))

/-! ## Controls -/

/-- The shared-channel COMM source `{@0!(0), for(y <- @0) 0}` is a closed
process. -/
theorem sharedChannelSource_closed :
    RhoClosedTermWellSorted rhoProc (commSource closedNilName.1 inert inert) :=
  (rhoClosedTermWellSorted_process_iff _).mpr
    ⟨.parallel (.cons (.output (.quote .unit) .unit) (.cons (.input (.quote .unit) .unit) .nil)),
      by decide⟩

/-- **Positive control.**  COMM on the shared channel `@0` reacts, with the
identity label, to the components of its contractum. -/
theorem sharedChannel_reacts :
    ActIPO closedCommRules (𝟙 parallelInterface)
      (agent (commSource closedNilName.1 inert inert)) (agent (semanticCommSubst inert inert)) := by
  rw [agent, agent, closedCommRules, actIPO_identity_iff]
  exact ⟨_, _, _, sharedChannelSource_closed, 0, (add_zero _).symm, (add_zero _).symm⟩

/-- **Positive control, labelled.**  The output `@0!(0)` on its own has a
transition whose least label is its input partner `for(y <- @0) 0`: the label
is a parallel partner `− | in(n, λx.q)`. -/
theorem output_transition_labelled_by_input_partner :
    ActIPO closedCommRules (agent waitingInput.1) (agent outputPartner.1)
      (agent (semanticCommSubst inert inert)) := by
  rw [agent, agent, agent, closedCommRules, actIPO_bag_iff]
  refine ⟨closedNilName.1, inert, inert, sharedChannelSource_closed, 0, ?_,
    Multiset.inter_zero _, (add_zero _).symm⟩
  rw [add_zero, components_commSource]
  simp [waitingInput, outputPartner, components_output, components_input,
    Multiset.singleton_add, Multiset.insert_eq_cons]

/-- The free drop `*@0` is its own only component. -/
theorem components_freeDrop : components freeDrop = {freeDrop} := by
  unfold components
  rw [show canonicalize freeDrop = freeDrop from canonicalize_free_drop_stays_inert,
    bagContents_singleton_of_plain (by simp [freeDrop]) (by simp [freeDrop])]
  rfl

/-- **Negative control, labelled.**  An idle partner `*@0` beside the input
partner makes the label wasteful: the output has no transition with that
label, whatever the target. -/
theorem output_no_transition_with_idle_partner (target : parallelInterface ⟶ parallelInterface) :
    ¬ ActIPO closedCommRules (bag (components waitingInput.1 + components freeDrop))
      (agent outputPartner.1) target := by
  change ¬ ActIPO _ _ _ (bag (Multiplicative.toAdd target))
  rw [agent, closedCommRules, actIPO_bag_iff]
  rintro ⟨channel, body, payload, -, context, sourceEq, disjoint, -⟩
  have idleInSum : freeDrop ∈ components outputPartner.1 +
      (components waitingInput.1 + components freeDrop) := by
    simp [components_freeDrop]
  rw [sourceEq, components_commSource] at idleInSum
  have idleInContext : freeDrop ∈ context := by
    simpa [freeDrop] using idleInSum
  have idleShared : freeDrop ∈ (components waitingInput.1 + components freeDrop) ∩ context :=
    Multiset.mem_inter.mpr ⟨by simp [components_freeDrop], idleInContext⟩
  rw [disjoint] at idleShared
  simp at idleShared

/-- A second closed name `@(@0!(0))`. -/
abbrev otherName : Pattern := .apply "NQuote" [outputPartner.1]

/-- An output on `@0` beside an input on `@(@0!(0))`. -/
def mismatchedChannels : RhoProcess :=
  ⟨.collection .hashBag
      [outputPartner.1, .apply "PInput" [otherName, .lambda none inert]] none,
    (rhoClosedTermWellSorted_process_iff _).mpr
      ⟨.parallel (.cons (.output (.quote .unit) .unit)
        (.cons (.input (.quote (.output (.quote .unit) .unit)) .unit) .nil)), by decide⟩⟩

/-- No COMM redex is among the components of `mismatchedChannels`. -/
theorem mismatchedChannels_no_commRedex :
    ¬ ∃ channel body payload, ∃ context : Multiset Pattern,
      components mismatchedChannels.1 = components (commSource channel body payload) + context := by
  rintro ⟨channel, body, payload, context, sourceEq⟩
  obtain ⟨outputMember, inputMember⟩ := output_input_mem_of_reacts sourceEq
  simp only [mismatchedChannels, components_parallel, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero, outputPartner, components_output,
    components_input, Multiset.singleton_add, Multiset.mem_cons, Multiset.mem_singleton,
    Pattern.apply.injEq, List.cons.injEq, and_true] at outputMember inputMember
  simp only [true_and, String.reduceEq, false_and, or_false, false_or] at outputMember inputMember
  have distinct : canonicalize closedNilName.1 ≠ canonicalize otherName := by decide
  exact distinct (outputMember.1.symm.trans inputMember.1)

/-- **Negative control.**  Output and input on different channels do not
reduce, for the paper relation. -/
theorem mismatchedChannels_not_reduces (target : Pattern) :
    ¬ Nonempty (Reduces mismatchedChannels.1 target) := by
  have pure := rhoProcWellSorted_hashSetFree
    ((rhoClosedTermWellSorted_process_iff _).mp mismatchedChannels.2).1
  rw [reduces_iff_actIPO_identity pure, agent, agent, pureCommRules, actIPO_identity_iff]
  rintro ⟨channel, body, payload, -, context, sourceEq, -⟩
  exact mismatchedChannels_no_commRedex ⟨channel, body, payload, context, sourceEq⟩

/-- **Negative control.**  Output and input on different channels do not step
in the established rho GSLT. -/
theorem mismatchedChannels_not_step (target : RhoProcess) :
    ¬ rhoLanguageDefGSLT.Step mismatchedChannels target := by
  rw [step_iff_actIPO_identity, agent, agent, closedCommRules, actIPO_identity_iff]
  rintro ⟨channel, body, payload, -, context, sourceEq, -⟩
  exact mismatchedChannels_no_commRedex ⟨channel, body, payload, context, sourceEq⟩

/-- The shared-channel COMM source, guarded by an input prefix on
`@(@0!(0))`. -/
def guardedComm : RhoProcess :=
  ⟨.apply "PInput" [otherName, .lambda none (commSource closedNilName.1 inert inert)],
    (rhoClosedTermWellSorted_process_iff _).mpr
      ⟨.input (.quote (.output (.quote .unit) .unit))
        (.parallel (.cons (.output (.quote .unit) .unit)
          (.cons (.input (.quote .unit) .unit) .nil))), by decide⟩⟩

/-- A prefixed process is one component, and that component is an input. -/
theorem guardedComm_no_commRedex :
    ¬ ∃ channel body payload, ∃ context : Multiset Pattern,
      components guardedComm.1 = components (commSource channel body payload) + context := by
  rintro ⟨channel, body, payload, context, sourceEq⟩
  have outputMember := (output_input_mem_of_reacts sourceEq).1
  simp [guardedComm, components_input] at outputMember

/-- **Negative control: no reaction under an input prefix.**  The redex that
reacts in `sharedChannel_reacts` is inert once guarded, for the paper
relation. -/
theorem guardedComm_not_reduces (target : Pattern) :
    ¬ Nonempty (Reduces guardedComm.1 target) := by
  have pure := rhoProcWellSorted_hashSetFree
    ((rhoClosedTermWellSorted_process_iff _).mp guardedComm.2).1
  rw [reduces_iff_actIPO_identity pure, agent, agent, pureCommRules, actIPO_identity_iff]
  rintro ⟨channel, body, payload, -, context, sourceEq, -⟩
  exact guardedComm_no_commRedex ⟨channel, body, payload, context, sourceEq⟩

/-- The same, in the established rho GSLT. -/
theorem guardedComm_not_step (target : RhoProcess) :
    ¬ rhoLanguageDefGSLT.Step guardedComm target := by
  rw [step_iff_actIPO_identity, agent, agent, closedCommRules, actIPO_identity_iff]
  rintro ⟨channel, body, payload, -, context, sourceEq, -⟩
  exact guardedComm_no_commRedex ⟨channel, body, payload, context, sourceEq⟩

#print axioms components_eq_iff_structuralCongruence
#print axioms components_parallel
#print axioms isIdemPushout_bag_iff
#print axioms actIPO_bag_iff
#print axioms actIPO_identity_iff
#print axioms label_le_redex
#print axioms reduces_iff_actIPO_identity
#print axioms step_iff_actIPO_identity
#print axioms sharedChannel_reacts
#print axioms output_transition_labelled_by_input_partner
#print axioms output_no_transition_with_idle_partner
#print axioms mismatchedChannels_not_reduces
#print axioms mismatchedChannels_not_step
#print axioms guardedComm_not_reduces
#print axioms guardedComm_not_step

end Mettapedia.GSLT.RhoBagReactiveSystem
