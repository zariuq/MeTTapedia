import Mettapedia.Languages.Metamath.MM2NormalProofOwnedClosure
import Mettapedia.Languages.Metamath.MM2VerifierProgram
import Mettapedia.Languages.Metamath.MM2TwoTransformProgram
import Mettapedia.Languages.ProcessCalculi.MORK.ComputableInputMonotonicity
import Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveGSLTNativeTypes
import Mettapedia.Languages.ProcessCalculi.MORK.MM2RuleScopedExecution

/-!
# Capability closure for assembled normal-proof execution

The owned-state proof establishes that active executable shells and protected
verifier rows retain their source.  This module strengthens that result for
continuations stored inside body-matcher data: every newly created carrier
either contains a fixed data continuation or propagates a continuation from
an actually matched predecessor carrier.

The final scheduled-step theorem passes the concrete realization through the
reflective execution GSLTs, OSLF, and their exact generated native types.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2NormalProofCapabilityClosure

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2SourceEventTransformation
open Mettapedia.Languages.Metamath.MM2SourceActionPlan
open Mettapedia.Languages.Metamath.MM2Transformation
open Mettapedia.Languages.Metamath.MM2VerifierProgram
open Mettapedia.Languages.Metamath.MM2TwoTransformProgram
open Mettapedia.Languages.Metamath.MM2NormalProofOwnedClosure
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-! ## Carrier-local closure -/

/-- The property required of one carrier row in a capability state. -/
def NormalBodyCarrierAuthorized (carrier : Atom) : Prop :=
  ∀ continuation,
    NormalBodyContinuationCapture carrier continuation →
      NormalBodyContinuationAuthorized continuation ∧
        ∀ nested,
          ¬ NormalBodyContinuationCapture continuation nested

/-- The strengthened atom-local invariant entails the original executable
ownership condition used by the normal owned-state development. -/
theorem normalBodyCarrierAuthorized_implies_capabilities
    {space : List Atom}
    (state : AtomsWithin NormalBodyCarrierAuthorized space) :
    NormalBodyContinuationCapabilities space := by
  intro carrier carrierMember continuation captured
  exact (state carrier carrierMember continuation captured).1

private def nestedCarrierLeaf : Atom := .symbol "mm-nested-carrier-leaf"

private def nestedCarrierInner : Atom :=
  .expression
    [.symbol "mm-body-match", .symbol "proof", .symbol "position",
      .symbol "source-body", .symbol "actual-body", nestedCarrierLeaf]

private def nestedCarrierOuter : Atom :=
  .expression
    [.symbol "mm-body-prefix", .symbol "proof", .symbol "position",
      .symbol "replacement-body", .symbol "actual-body", .symbol "source-tail",
      nestedCarrierInner]

/-- Negative control: a carrier cannot hide another carrier in its continuation
field, even when neither row is itself an executable shell. -/
theorem nested_body_carrier_is_rejected :
    ¬ NormalBodyCarrierAuthorized nestedCarrierOuter := by
  intro authorized
  have outer := authorized nestedCarrierInner
    (NormalBodyContinuationCapture.bodyPrefix _ _ _ _ _ _)
  exact (outer.2 nestedCarrierLeaf)
    (NormalBodyContinuationCapture.bodyMatch _ _ _ _ _)

/-- Template atoms whose outer shape cannot become a body carrier after
substitution.  Variables at the head are excluded because they could acquire
either carrier tag from the matcher environment. -/
@[simp] def normalContinuationSafeTemplateAtom : Atom → Bool
  | .var _ => false
  | .symbol _ | .grounded _ => true
  | .expression [] => true
  | .expression (.symbol tag :: _) =>
      tag != "mm-body-match" && tag != "mm-body-prefix"
  | .expression (.var _ :: _) => false
  | .expression (.grounded _ :: _) => true
  | .expression (.expression _ :: _) => true

@[simp] def normalContinuationSafeSink : Sink → Bool
  | .add atom => normalContinuationSafeTemplateAtom atom
  | .remove _ | .head _ _ | .tail _ _ => true

def NormalContinuationSafeTemplate (template : Template) : Prop :=
  template.sinks.all normalContinuationSafeSink = true

/-- Recognize precisely the two carrier heads whose final field may later be
republished as a continuation. -/
@[simp] def normalBodyCarrierTag : Atom → Bool
  := isNormalBodyCarrierShape

private theorem normalBodyContinuationCapture_has_tag
    {carrier continuation : Atom}
    (captured : NormalBodyContinuationCapture carrier continuation) :
    normalBodyCarrierTag carrier = true := by
  cases captured <;> rfl

/-- An atom outside both body-cursor families satisfies the carrier authority
predicate vacuously: it has no continuation field that can be republished. -/
theorem normalBodyCarrierAuthorized_of_shape_false
    {atom : Atom} (absent : isNormalBodyCarrierShape atom = false) :
    NormalBodyCarrierAuthorized atom := by
  intro continuation captured
  have hasTag := normalBodyContinuationCapture_has_tag captured
  rw [normalBodyCarrierTag, absent] at hasTag
  contradiction

/-- Every proof-neutral initial atom lies inside the normal continuation
capability boundary. -/
theorem normalBodyCarrierAuthorized_of_proofNeutral
    {atom : Atom} (neutral : isProofNeutralInitialAtom atom = true) :
    NormalBodyCarrierAuthorized atom := by
  apply normalBodyCarrierAuthorized_of_shape_false
  simp only [isProofNeutralInitialAtom, Bool.and_eq_true,
    Bool.not_eq_true'] at neutral
  exact neutral.2.2

/-- A list whose atoms are all proof-neutral satisfies the continuation
capability boundary pointwise. -/
theorem atomsWithin_normalBodyCarrierAuthorized_of_all_proofNeutral
    {rows : List Atom}
    (neutral : rows.all isProofNeutralInitialAtom = true) :
    AtomsWithin NormalBodyCarrierAuthorized rows := by
  intro row member
  exact normalBodyCarrierAuthorized_of_proofNeutral
    ((List.all_eq_true.mp neutral) row member)

/-- Every row admitted from source events begins inside the continuation
capability boundary required by the arbitrary normal executor. -/
theorem AdmittedSourceEventInput.initialRows_body_carrier_authorized
    {owner : Atom} (input : AdmittedSourceEventInput owner) :
    AtomsWithin NormalBodyCarrierAuthorized input.initialRows := by
  intro row member
  exact normalBodyCarrierAuthorized_of_shape_false
    (input.initialRows_no_normal_body_carrier row member)

/-- None of the verifier-owned inert code rows is also a normal body cursor. -/
theorem normalVerifierInternalRows_no_normal_body_carrier :
    normalVerifierInternalRows.all (fun atom =>
      !(isNormalBodyCarrierShape atom)) = true := by
  decide +kernel

/-- None of the executable rules in the fixed authored normal verifier is a
body cursor at top level. -/
theorem authoredNormalVerifierRules_no_normal_body_carrier :
    authoredNormalVerifierRules.all (fun atom =>
      !(isNormalBodyCarrierShape atom)) = true := by
  decide +kernel

/-- The complete database-independent normal-and-compressed verifier output
contains no body cursor at its outermost row boundary.  Body cursors arise
only through authorized execution of verifier-owned templates. -/
theorem genericVerifierProgram_no_normal_body_carrier :
    (genericVerifierProgram authoredMetamathVerifierGSLT).all (fun atom =>
      !(isNormalBodyCarrierShape atom)) = true := by
  decide +kernel

theorem normalVerifierInternalRows_body_carrier_authorized :
    AtomsWithin NormalBodyCarrierAuthorized normalVerifierInternalRows := by
  intro row member
  apply normalBodyCarrierAuthorized_of_shape_false
  have safe := (List.all_eq_true.mp
    normalVerifierInternalRows_no_normal_body_carrier) row member
  simpa only [Bool.not_eq_true'] using safe

theorem authoredNormalVerifierRules_body_carrier_authorized :
    AtomsWithin NormalBodyCarrierAuthorized authoredNormalVerifierRules := by
  intro row member
  apply normalBodyCarrierAuthorized_of_shape_false
  have safe := (List.all_eq_true.mp
    authoredNormalVerifierRules_no_normal_body_carrier) row member
  simpa only [Bool.not_eq_true'] using safe

/-- The actual database-independent verifier transformation begins inside the
normal continuation-capability boundary. -/
theorem genericVerifierProgram_body_carrier_authorized :
    AtomsWithin NormalBodyCarrierAuthorized
      (genericVerifierProgram authoredMetamathVerifierGSLT) := by
  intro row member
  apply normalBodyCarrierAuthorized_of_shape_false
  have safe := (List.all_eq_true.mp
    genericVerifierProgram_no_normal_body_carrier) row member
  simpa only [Bool.not_eq_true'] using safe

/-- The independently constructed source-data transformation output begins
inside the same continuation-capability boundary. -/
theorem sourceDataProgram_body_carrier_authorized
    {owner : Atom} (input : AdmittedSourceEventInput owner)
    (actions : AdmittedSourceActionPlans owner input.statements) :
    AtomsWithin NormalBodyCarrierAuthorized
      (sourceDataProgram input actions) :=
  atomsWithin_normalBodyCarrierAuthorized_of_all_proofNeutral
    (sourceDataProgram_all_proofNeutral input actions)

/-- The actual two-transform composition begins inside the normal
continuation-capability boundary. -/
theorem composeProgram_body_carrier_authorized
    {owner : Atom} (input : AdmittedSourceEventInput owner)
    (actions : AdmittedSourceActionPlans owner input.statements) :
    AtomsWithin NormalBodyCarrierAuthorized
      (composeProgram authoredMetamathVerifierGSLT input actions) := by
  intro row member
  rw [composeProgram, List.mem_append] at member
  rcases member with verifier | source
  · exact genericVerifierProgram_body_carrier_authorized row verifier
  · exact sourceDataProgram_body_carrier_authorized input actions row source

/-- The complete fixed verifier artifact begins inside the body-continuation
capability boundary, including both its inert code rows and executable rules. -/
theorem authored_normal_verifier_program_body_carrier_authorized
    (target : MM2Target) :
    AtomsWithin NormalBodyCarrierAuthorized
      (transformNormalVerifierSlice authoredMetamathVerifierGSLT target).program := by
  intro row member
  rw [GenericVerifierSliceArtifact.program,
    authored_transformNormalVerifierSlice_internalRows,
    ← authoredNormalVerifierRules_eq_transform target,
    List.mem_append] at member
  rcases member with internal | rule
  · exact normalVerifierInternalRows_body_carrier_authorized row internal
  · exact authoredNormalVerifierRules_body_carrier_authorized row rule

/-- Composition with admitted source events preserves the same entry-side
continuation authority boundary. -/
theorem composeAdmittedNormalProgram_body_carrier_authorized
    (target : MM2Target) {owner : Atom}
    (input : AdmittedSourceEventInput owner) :
    AtomsWithin NormalBodyCarrierAuthorized
      (composeAdmittedNormalProgram authoredMetamathVerifierGSLT target input) := by
  intro row member
  rw [composeAdmittedNormalProgram, List.mem_append] at member
  rcases member with verifier | source
  · exact authored_normal_verifier_program_body_carrier_authorized target
      row verifier
  · exact
      AdmittedSourceEventInput.initialRows_body_carrier_authorized input row
        source

/-- Removing one physical support key preserves the complete owned normal
machine state.  This is the live-space boundary used by rule-scoped firing. -/
theorem NormalProofMachineOwnedState.morkEraseSupport
    {space : List Atom} (state : NormalProofMachineOwnedState space)
    (removed : Atom) :
    NormalProofMachineOwnedState (morkEraseSupport space removed) := by
  constructor
  · constructor
    · exact state.1.1.filter _
    · intro raw member
      unfold cRawExecFacts at member
      rw [List.mem_filterMap] at member
      obtain ⟨atom, atomMember, extracted⟩ := member
      exact state.1.2 raw (by
        unfold cRawExecFacts
        rw [List.mem_filterMap]
        exact ⟨atom, (List.mem_filter.mp atomMember).1, extracted⟩)
  · exact morkEraseSupport_atomsWithin NormalVerifierInternalRowIntact
      space removed state.2

theorem NormalProofMachineExecutionContext.morkEraseSupport
    {space : List Atom} (context : NormalProofMachineExecutionContext space)
    (removed : Atom) :
    NormalProofMachineExecutionContext (morkEraseSupport space removed) := by
  constructor
  · intro raw member
    unfold cRawExecFacts at member
    rw [List.mem_filterMap] at member
    obtain ⟨atom, atomMember, extracted⟩ := member
    apply context.1 raw
    unfold cRawExecFacts
    rw [List.mem_filterMap]
    exact ⟨atom, (List.mem_filter.mp atomMember).1, extracted⟩
  · exact morkEraseSupport_atomsWithin NormalVerifierInternalRowIntact
      space removed context.2

private theorem normalContinuationSafeTemplateAtom_tag_false
    (substitution : Subst) (template : Atom)
    (safe : normalContinuationSafeTemplateAtom template = true) :
    normalBodyCarrierTag (applySubst substitution template) = false := by
  cases template with
  | var name => simp at safe
  | symbol name => rfl
  | grounded value => rfl
  | expression children =>
      cases children with
      | nil => rfl
      | cons head tail =>
          cases head with
          | var name => simp at safe
          | symbol tag =>
              simp only [normalContinuationSafeTemplateAtom,
                Bool.and_eq_true, bne_iff_ne] at safe
              simp [applySubst, applySubst.applySubstList,
                normalBodyCarrierTag, safe.1, safe.2]
          | grounded value => rfl
          | expression nested => rfl

/-- A successfully instantiated rule-scoped output with a structurally safe
head cannot become a normal body cursor. -/
theorem normalContinuationSafeTemplateAtom_ruleScoped_authorized
    (input : InputSpec) (substitution : Subst) (template atom : Atom)
    (safe : normalContinuationSafeTemplateAtom template = true)
    (instantiated :
      instantiateRuleTemplateAtom? input substitution template = some atom) :
    NormalBodyCarrierAuthorized atom := by
  unfold instantiateRuleTemplateAtom? at instantiated
  split at instantiated
  · have equal : applySubst substitution template = atom :=
      Option.some.inj instantiated
    subst atom
    apply normalBodyCarrierAuthorized_of_shape_false
    exact normalContinuationSafeTemplateAtom_tag_false substitution template
      safe
  · contradiction

/-- Exact rule-scoped safety test: every sink that can add a row must have a
structurally safe output head; removal targets are unrestricted. -/
@[simp] def ruleScopedNormalContinuationSafeSink : Sink → Bool
  | .add atom | .head _ atom | .tail _ atom =>
      normalContinuationSafeTemplateAtom atom
  | .remove _ => true

def RuleScopedNormalContinuationSafeTemplate (template : Template) : Prop :=
  template.sinks.all ruleScopedNormalContinuationSafeSink = true

/-- A structurally safe rule-scoped template satisfies the exact
addition-only capability obligation for arbitrary matcher rows. -/
theorem ruleScopedNormalContinuationSafeTemplate_additions
    (input : InputSpec) (rows : List Subst) (template : Template)
    (safe : RuleScopedNormalContinuationSafeTemplate template) :
    RuleScopedTemplateAdditionsWithin NormalBodyCarrierAuthorized input rows
      template := by
  intro sink member
  have sinkSafe := (List.all_eq_true.mp safe) sink member
  cases sink with
  | add atom =>
      simp only [ruleScopedNormalContinuationSafeSink] at sinkSafe
      intro substitution _ result instantiated
      exact normalContinuationSafeTemplateAtom_ruleScoped_authorized input
        substitution atom result sinkSafe instantiated
  | remove atom => trivial
  | head count atom =>
      simp only [ruleScopedNormalContinuationSafeSink] at sinkSafe
      intro substitution _ result instantiated
      exact normalContinuationSafeTemplateAtom_ruleScoped_authorized input
        substitution atom result sinkSafe instantiated
  | tail count atom =>
      simp only [ruleScopedNormalContinuationSafeSink] at sinkSafe
      intro substitution _ result instantiated
      exact normalContinuationSafeTemplateAtom_ruleScoped_authorized input
        substitution atom result sinkSafe instantiated

/-- Bridge condition for support-valued templates: an added output is either
fully inherited from the matched input or structurally unable to become a
normal body carrier.  Extrema sinks are excluded because the older
fully-bound addition relation does not model their ordering semantics. -/
@[simp] def ruleScopedNormalCapabilityBridgeSink
    (input : InputSpec) : Sink → Bool
  | .add atom =>
      ruleTemplateVariablesInherited input atom ||
        normalContinuationSafeTemplateAtom atom
  | .remove _ => true
  | .head _ _ | .tail _ _ => false

def RuleScopedNormalCapabilityBridgeTemplate
    (input : InputSpec) (template : Template) : Prop :=
  template.sinks.all (ruleScopedNormalCapabilityBridgeSink input) = true

/-- A fully-bound capability proof transfers to rule-scoped execution when
each addition is either input-inherited or structurally carrier-free.  This
isolates the exact semantic difference caused by output-local variables. -/
theorem ruleScopedNormalCapabilityBridge_additions
    (input : InputSpec) (rows : List Subst) (template : Template)
    (supported : ReflectiveSupportSetTemplate template)
    (bridge : RuleScopedNormalCapabilityBridgeTemplate input template)
    (reflective :
      ReflectiveAddedAtomsWithin NormalBodyCarrierAuthorized rows template) :
    RuleScopedTemplateAdditionsWithin NormalBodyCarrierAuthorized input rows
      template := by
  intro sink member
  have sinkBridge := (List.all_eq_true.mp bridge) sink member
  cases sink with
  | add authored =>
      simp only [ruleScopedNormalCapabilityBridgeSink, Bool.or_eq_true]
        at sinkBridge
      intro substitution rowMember atom instantiated
      rcases sinkBridge with inherited | safe
      · apply reflective atom
        refine ⟨.add authored, member, authored, rfl, substitution,
          rowMember, ?_⟩
        rw [
          ← instantiateRuleTemplateAtom?_eq_instantiateTemplateAtom?
            input substitution authored inherited]
        exact instantiated
      · exact normalContinuationSafeTemplateAtom_ruleScoped_authorized
          input substitution authored atom safe instantiated
  | remove authored => trivial
  | head count authored =>
      exact False.elim (supported (.head count authored) member)
  | tail count authored =>
      exact False.elim (supported (.tail count authored) member)

/-- Atom-local form of the complete normal verifier ownership invariant. -/
def NormalRuleScopedOwnedAtom (atom : Atom) : Prop :=
  RawExecAtomWithin normalProofMachineRawFacts atom ∧
    NormalVerifierInternalRowIntact atom

/-- Structural data outputs are harmless for both executable provenance and
protected verifier-owned rows under rule-scoped instantiation. -/
theorem normalOwnedSafeTemplateAtom_ruleScoped_authorized
    (input : InputSpec) (substitution : Subst) (template atom : Atom)
    (safe : normalOwnedSafeTemplateAtom template = true)
    (instantiated :
      instantiateRuleTemplateAtom? input substitution template = some atom) :
    NormalRuleScopedOwnedAtom atom := by
  unfold instantiateRuleTemplateAtom? at instantiated
  split at instantiated
  · have equal : applySubst substitution template = atom :=
      Option.some.inj instantiated
    subst atom
    constructor
    · intro raw extracted
      rw [normalOwnedSafeTemplateAtom_raw_none substitution template safe]
        at extracted
      contradiction
    · unfold NormalVerifierInternalRowIntact
      intro internalShape
      rw [normalOwnedSafeTemplateAtom_internal_false substitution template
        safe] at internalShape
      contradiction
  · contradiction

/-- An owned-output bridge admits inherited values proved by the old matcher
semantics and structurally data-only output-local templates. -/
@[simp] def ruleScopedNormalOwnedBridgeSink
    (input : InputSpec) : Sink → Bool
  | .add atom =>
      ruleTemplateVariablesInherited input atom ||
        normalOwnedSafeTemplateAtom atom
  | .remove _ => true
  | .head _ _ | .tail _ _ => false

def RuleScopedNormalOwnedBridgeTemplate
    (input : InputSpec) (template : Template) : Prop :=
  template.sinks.all (ruleScopedNormalOwnedBridgeSink input) = true

/-- A support template whose produced atoms use only variables inherited from
the input.  Such a template has identical successful instantiations under the
fully-bound and rule-scoped interpreters. -/
@[simp] def ruleScopedInheritedSink (input : InputSpec) : Sink → Bool
  | .add atom | .head _ atom | .tail _ atom =>
      ruleTemplateVariablesInherited input atom
  | .remove _ => true

def RuleScopedInheritedTemplate (input : InputSpec)
    (template : Template) : Prop :=
  template.sinks.all (ruleScopedInheritedSink input) = true

theorem ruleScopedInheritedTemplate_additions_of_reflective
    (property : Atom → Prop) (input : InputSpec) (rows : List Subst)
    (template : Template)
    (supported : ReflectiveSupportSetTemplate template)
    (inherited : RuleScopedInheritedTemplate input template)
    (reflective : ReflectiveAddedAtomsWithin property rows template) :
    RuleScopedTemplateAdditionsWithin property input rows template := by
  intro sink member
  have sinkInherited := (List.all_eq_true.mp inherited) sink member
  cases sink with
  | remove atom => trivial
  | add authored =>
      intro substitution rowMember atom instantiated
      apply reflective atom
      refine ⟨.add authored, member, authored, rfl, substitution,
        rowMember, ?_⟩
      rw [← instantiateRuleTemplateAtom?_eq_instantiateTemplateAtom?
        input substitution authored sinkInherited]
      exact instantiated
  | head count authored =>
      exact False.elim (supported (.head count authored) member)
  | tail count authored =>
      exact False.elim (supported (.tail count authored) member)

/-- Fully-bound ownership proofs transfer to the actual rule-scoped executor
under the exact inherited-or-data-only bridge condition. -/
theorem ruleScopedNormalOwnedBridge_additions
    (input : InputSpec) (rows : List Subst) (template : Template)
    (supported : ReflectiveSupportSetTemplate template)
    (bridge : RuleScopedNormalOwnedBridgeTemplate input template)
    (reflective :
      ReflectiveAddedAtomsWithin NormalRuleScopedOwnedAtom rows template) :
    RuleScopedTemplateAdditionsWithin NormalRuleScopedOwnedAtom input rows
      template := by
  intro sink member
  have sinkBridge := (List.all_eq_true.mp bridge) sink member
  cases sink with
  | add authored =>
      simp only [ruleScopedNormalOwnedBridgeSink, Bool.or_eq_true]
        at sinkBridge
      intro substitution rowMember atom instantiated
      rcases sinkBridge with inherited | safe
      · apply reflective atom
        refine ⟨.add authored, member, authored, rfl, substitution,
          rowMember, ?_⟩
        rw [
          ← instantiateRuleTemplateAtom?_eq_instantiateTemplateAtom?
            input substitution authored inherited]
        exact instantiated
      · exact normalOwnedSafeTemplateAtom_ruleScoped_authorized input
          substitution authored atom safe instantiated
  | remove authored => trivial
  | head count authored =>
      exact False.elim (supported (.head count authored) member)
  | tail count authored =>
      exact False.elim (supported (.tail count authored) member)

/-- The existing owned state implies its atom-local rule-scoped form. -/
theorem NormalProofMachineOwnedState.atomsWithin_ruleScopedOwned
    {space : List Atom} (state : NormalProofMachineOwnedState space) :
    AtomsWithin NormalRuleScopedOwnedAtom space := by
  intro atom member
  exact ⟨state.1.2.atom member, state.2 atom member⟩

/-- Ordinary duplicate freedom plus atom-local ownership reconstructs the
existing owned state. -/
theorem normalProofMachineOwnedState_of_ruleScopedOwned
    {space : List Atom} (nodup : space.Nodup)
    (within : AtomsWithin NormalRuleScopedOwnedAtom space) :
    NormalProofMachineOwnedState space := by
  constructor
  · exact ⟨nodup, by
      intro raw member
      unfold cRawExecFacts at member
      rw [List.mem_filterMap] at member
      obtain ⟨atom, atomMember, extracted⟩ := member
      exact (within atom atomMember).1 raw extracted⟩
  · intro atom member
    exact (within atom member).2

/-- Addition obligations are monotone in their matcher-row carrier. -/
theorem reflectiveAddedAtomsWithin_of_rows_subset
    (property : Atom → Prop) (small large : List Subst) (template : Template)
    (included : ∀ substitution ∈ small, substitution ∈ large)
    (largeWithin : ReflectiveAddedAtomsWithin property large template) :
    ReflectiveAddedAtomsWithin property small template := by
  intro atom added
  rcases added with
    ⟨sink, sinkMember, authored, sinkEq,
      substitution, rowMember, instantiated⟩
  apply largeWithin atom
  exact ⟨sink, sinkMember, authored, sinkEq,
    substitution, included substitution rowMember, instantiated⟩

/-- Every guarded compatible-matcher row used by the physical rule-scoped
executor also occurs in the ordinary read-copy presentation used by the
existing semantic capability proofs.  The proof depends only on carrier
inclusion, not on matcher enumeration order. -/
theorem ruleScopedCompatRow_mem_reflectiveRead
    (space : List Atom) (directive : SourceExecFact) (pattern : Pattern)
    (inputEq : directive.rule.input = .compat pattern)
    {substitution : Subst}
    (member : substitution ∈
      (((cMatchInputSpecMork []
          (morkInsertSupport
            (morkEraseSupport space directive.atom) directive.atom)
          directive.rule.input).filter fun (candidate, _) =>
            matchSourceGuards candidate directive.rule.guards).map Prod.fst)) :
    substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (directive.atom ::
          (morkEraseSupport space directive.atom).erase directive.atom)
        directive.rule.input).map Prod.fst := by
  rw [List.mem_map] at member
  obtain ⟨⟨final, witnesses⟩, filtered, rfl⟩ := member
  have matched := (List.mem_filter.mp filtered).1
  cases pattern with
  | mk patterns =>
      rw [inputEq] at matched ⊢
      have transferred :=
        Conformance.Computable.cmatchInputSpec_compat_mono []
          (morkInsertSupport
            (morkEraseSupport space directive.atom) directive.atom)
          (directive.atom :: morkEraseSupport space directive.atom)
          patterns
          (by
            intro atom atomMember
            rw [morkInsertSupport_morkEraseSupport_self] at atomMember
            simp only [List.mem_append, List.mem_singleton] at atomMember
            rcases atomMember with live | selected
            · exact List.mem_cons_of_mem directive.atom live
            · exact selected ▸ List.mem_cons_self)
          (by
            rw [List.mem_map]
            exact ⟨(final, witnesses), matched, rfl⟩)
      rw [List.erase_of_not_mem
        (not_mem_morkEraseSupport_self space directive.atom)]
      exact transferred

/-- A compatible support-valued rule may reuse a fully-bound capability proof
inside the physical rule-scoped executor.  Guard filtering only removes
matcher rows, and read-copy reordering is handled by matcher monotonicity. -/
private theorem ruleScopedCompatCapability_additions_of_reflective
    {space : List Atom} (directive : SourceExecFact)
    (compat : ∃ pattern, directive.rule.input = .compat pattern)
    (supported : ReflectiveSupportSetTemplate directive.rule.tmpl)
    (bridge : RuleScopedNormalCapabilityBridgeTemplate directive.rule.input
      directive.rule.tmpl)
    (reflective :
      let live := morkEraseSupport space directive.atom
      let rows := (Conformance.Computable.cmatchInputSpec []
        (directive.atom :: live.erase directive.atom)
        directive.rule.input).map Prod.fst
      ReflectiveAddedAtomsWithin NormalBodyCarrierAuthorized rows
        directive.rule.tmpl) :
    let live := morkEraseSupport space directive.atom
    let read := morkInsertSupport live directive.atom
    let rows := (cMatchInputSpecMork [] read directive.rule.input).filter fun
      (substitution, _) => matchSourceGuards substitution directive.rule.guards
    RuleScopedTemplateAdditionsWithin NormalBodyCarrierAuthorized
      directive.rule.input (rows.map Prod.fst) directive.rule.tmpl := by
  obtain ⟨pattern, inputEq⟩ := compat
  dsimp only
  apply ruleScopedNormalCapabilityBridge_additions
      directive.rule.input _ directive.rule.tmpl supported bridge
  apply reflectiveAddedAtomsWithin_of_rows_subset
      NormalBodyCarrierAuthorized _ _ directive.rule.tmpl
  · intro substitution member
    exact ruleScopedCompatRow_mem_reflectiveRead space directive pattern
      inputEq member
  · exact reflective

/-- Ownership analogue of
`ruleScopedCompatCapability_additions_of_reflective`. -/
private theorem ruleScopedCompatOwned_additions_of_reflective
    {space : List Atom} (directive : SourceExecFact)
    (compat : ∃ pattern, directive.rule.input = .compat pattern)
    (supported : ReflectiveSupportSetTemplate directive.rule.tmpl)
    (bridge : RuleScopedNormalOwnedBridgeTemplate directive.rule.input
      directive.rule.tmpl)
    (reflective :
      let live := morkEraseSupport space directive.atom
      let rows := (Conformance.Computable.cmatchInputSpec []
        (directive.atom :: live.erase directive.atom)
        directive.rule.input).map Prod.fst
      ReflectiveAddedAtomsWithin NormalRuleScopedOwnedAtom rows
        directive.rule.tmpl) :
    let live := morkEraseSupport space directive.atom
    let read := morkInsertSupport live directive.atom
    let rows := (cMatchInputSpecMork [] read directive.rule.input).filter fun
      (substitution, _) => matchSourceGuards substitution directive.rule.guards
    RuleScopedTemplateAdditionsWithin NormalRuleScopedOwnedAtom
      directive.rule.input (rows.map Prod.fst) directive.rule.tmpl := by
  obtain ⟨pattern, inputEq⟩ := compat
  dsimp only
  apply ruleScopedNormalOwnedBridge_additions
      directive.rule.input _ directive.rule.tmpl supported bridge
  apply reflectiveAddedAtomsWithin_of_rows_subset
      NormalRuleScopedOwnedAtom _ _ directive.rule.tmpl
  · intro substitution member
    exact ruleScopedCompatRow_mem_reflectiveRead space directive pattern
      inputEq member
  · exact reflective

private theorem normalContinuationSafeTemplateAtom_no_capture
    (substitution : Subst) (template : Atom)
    (safe : normalContinuationSafeTemplateAtom template = true) :
    ∀ continuation,
      ¬ NormalBodyContinuationCapture
        (applySubst substitution template) continuation := by
  intro continuation captured
  have hasTag := normalBodyContinuationCapture_has_tag captured
  rw [normalContinuationSafeTemplateAtom_tag_false substitution template safe]
    at hasTag
  contradiction

private theorem normalContinuationSafeInstantiation_no_capture
    {substitution : Subst} {template carrier continuation : Atom}
    (safe : normalContinuationSafeTemplateAtom template = true)
    (instantiates :
      instantiateTemplateAtom? substitution template = some carrier) :
    ¬ NormalBodyContinuationCapture carrier continuation := by
  have instantiated : applySubst substitution template = carrier := by
    unfold instantiateTemplateAtom? at instantiates
    split at instantiates
    · exact Option.some.inj instantiates
    · simp at instantiates
  rw [← instantiated]
  exact normalContinuationSafeTemplateAtom_no_capture substitution template
    safe continuation

/-- A carrier-free sink template preserves the continuation capability
invariant without inspecting matcher rows. -/
theorem normalContinuationSafeTemplate_added_closed
    (rows : List Subst) (template : Template)
    (safe : NormalContinuationSafeTemplate template) :
    ReflectiveAddedAtomsWithin NormalBodyCarrierAuthorized rows template := by
  intro carrier added continuation captured
  rcases added with
    ⟨sink, sinkMember, authored, rfl,
      substitution, _rowMember, instantiates⟩
  have safeSink := (List.all_eq_true.mp safe) (.add authored) sinkMember
  have safeAuthored : normalContinuationSafeTemplateAtom authored = true := by
    simpa using safeSink
  exact False.elim
    (normalContinuationSafeInstantiation_no_capture safeAuthored instantiates
      captured)

/-! ## Matcher-derived continuation origin -/

private theorem matchAtom_bodyMatchPattern_captures
    (sourcePattern actualPattern : Atom)
    {result : Subst} {atom : Atom}
    (matched : Conformance.Computable.cmatchAtom []
      (.expression
        [.symbol "mm-body-match", .var "proof", .var "pc",
          sourcePattern, actualPattern, .var "continuation"])
      atom = some result) :
    ∃ continuation,
      Subst.lookup result "continuation" = some continuation ∧
        NormalBodyContinuationCapture atom continuation := by
  rw [Conformance.cmatchAtom_eq_matchAtom] at matched
  have relational := matchAtom_sound matched
  cases relational with
  | expr_cons headMatched tail1 =>
      cases headMatched
      cases tail1 with
      | expr_cons proofMatched tail2 =>
          cases tail2 with
          | expr_cons positionMatched tail3 =>
              cases tail3 with
              | expr_cons sourceMatched tail4 =>
                  cases tail4 with
                  | expr_cons actualMatched tail5 =>
                      cases tail5 with
                      | expr_cons continuationMatched finalTail =>
                          cases finalTail
                          cases continuationMatched with
                          | var_fresh lookup =>
                              exact ⟨_, by simp [Subst.lookup],
                                .bodyMatch _ _ _ _ _⟩
                          | var_bound lookup =>
                              exact ⟨_, lookup, .bodyMatch _ _ _ _ _⟩

private theorem matchAtom_bodyPrefixPattern_captures
    (replacementPattern actualPattern sourceTailPattern : Atom)
    {result : Subst} {atom : Atom}
    (matched : Conformance.Computable.cmatchAtom []
      (.expression
        [.symbol "mm-body-prefix", .var "proof", .var "pc",
          replacementPattern, actualPattern, sourceTailPattern,
          .var "continuation"])
      atom = some result) :
    ∃ continuation,
      Subst.lookup result "continuation" = some continuation ∧
        NormalBodyContinuationCapture atom continuation := by
  rw [Conformance.cmatchAtom_eq_matchAtom] at matched
  have relational := matchAtom_sound matched
  cases relational with
  | expr_cons headMatched tail1 =>
      cases headMatched
      cases tail1 with
      | expr_cons proofMatched tail2 =>
          cases tail2 with
          | expr_cons positionMatched tail3 =>
              cases tail3 with
              | expr_cons replacementMatched tail4 =>
                  cases tail4 with
                  | expr_cons actualMatched tail5 =>
                      cases tail5 with
                      | expr_cons sourceTailMatched tail6 =>
                          cases tail6 with
                          | expr_cons continuationMatched finalTail =>
                              cases finalTail
                              cases continuationMatched with
                              | var_fresh lookup =>
                                  exact ⟨_, by simp [Subst.lookup],
                                    .bodyPrefix _ _ _ _ _ _⟩
                              | var_bound lookup =>
                                  exact ⟨_, lookup,
                                    .bodyPrefix _ _ _ _ _ _⟩

private theorem matchedContinuation_origin
    {space : List Atom} (directive : SourceExecFact)
    (first : Atom) (rest : List Atom)
    {substitution : Subst} {continuation : Atom}
    (rowMember : substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (directive.atom :: space.erase directive.atom)
        (.compat (mkPattern (first :: rest)))).map Prod.fst)
    (firstCapture : ∀ {afterFirst firstAtom},
      Conformance.Computable.cmatchAtom [] first firstAtom =
          some afterFirst →
        ∃ value,
          Subst.lookup afterFirst "continuation" = some value ∧
            NormalBodyContinuationCapture firstAtom value)
    (directiveNotCarrier : ∀ value,
      ¬ NormalBodyContinuationCapture directive.atom value)
    (instantiates : instantiateTemplateAtom? substitution
      (.var "continuation") = some continuation) :
    ∃ carrier ∈ space,
      NormalBodyContinuationCapture carrier continuation := by
  obtain ⟨carrier, captured, carrierMember, capturedLookup, capture⟩ :=
    Conformance.Computable.cmatchInputSpec_first_capture_origin
      NormalBodyContinuationCapture "continuation" rowMember firstCapture
  have continuationLookup :
      Subst.lookup substitution "continuation" = some continuation :=
    (instantiateTemplateAtom?_var_eq_some_iff substitution "continuation"
      continuation).1 instantiates
  have capturedEq : captured = continuation :=
    Option.some.inj (capturedLookup.symm.trans continuationLookup)
  subst captured
  rcases List.mem_cons.mp carrierMember with selected | prior
  · exact False.elim (directiveNotCarrier continuation (selected ▸ capture))
  · exact ⟨carrier, List.mem_of_mem_erase prior, capture⟩

private theorem instantiateTemplateAtom?_eq_some
    {substitution : Subst} {template atom : Atom}
    (instantiates :
      instantiateTemplateAtom? substitution template = some atom) :
    applySubst substitution template = atom := by
  unfold instantiateTemplateAtom? at instantiates
  split at instantiates
  · exact Option.some.inj instantiates
  · simp at instantiates

/-- Exact decoder for the continuation field of either body carrier. -/
@[simp] def normalBodyContinuation? : Atom → Option Atom
  | .expression
      [.symbol "mm-body-match", _, _, _, _, continuation] =>
        some continuation
  | .expression
      [.symbol "mm-body-prefix", _, _, _, _, _, continuation] =>
        some continuation
  | _ => none

private theorem normalBodyContinuationCapture_decodes
    {carrier continuation : Atom}
    (captured : NormalBodyContinuationCapture carrier continuation) :
    normalBodyContinuation? carrier = some continuation := by
  cases captured <;> rfl

private theorem normalBodyContinuationCapture_unique
    {carrier left right : Atom}
    (leftCapture : NormalBodyContinuationCapture carrier left)
    (rightCapture : NormalBodyContinuationCapture carrier right) :
    left = right := by
  exact Option.some.inj
    ((normalBodyContinuationCapture_decodes leftCapture).symm.trans
      (normalBodyContinuationCapture_decodes rightCapture))

private theorem instantiated_template_binds_var
    {substitution : Subst} {template carrier : Atom} (variableName : String)
    (instantiates :
      instantiateTemplateAtom? substitution template = some carrier)
    (occurs : variableName ∈ atomFreeVars template) :
    ∃ value,
      Subst.lookup substitution variableName = some value ∧
        applySubst substitution (.var variableName) = value ∧
        instantiateTemplateAtom? substitution (.var variableName) =
          some value := by
  have covered : templateCovered substitution template = true := by
    unfold instantiateTemplateAtom? at instantiates
    split at instantiates
    · assumption
    · simp at instantiates
  obtain ⟨value, lookup⟩ :=
    templateCovered_lookup_of_mem_freeVars substitution template covered
      variableName occurs
  have applied : applySubst substitution (.var variableName) = value := by
    simp [applySubst, lookup]
  exact ⟨value, lookup, applied,
    (instantiateTemplateAtom?_var_eq_some_iff substitution variableName
      value).2 lookup⟩

/-! ## Fixed essential-hypothesis continuation -/

private def assertionEssentialContinuationTemplate : Atom :=
  .expression
    [.symbol "mm-assertion-essential-complete",
      .var "scope", .var "proof", .var "pc", .var "next-pc",
      .var "label", .var "next-hyp-position", .var "hyp-end",
      .var "next-stack-position", .var "stack-base",
      .var "hyp-position", .var "child-occurrence"]

private def assertionEssentialCarrierTemplate : Atom :=
  .expression
    [.symbol "mm-body-match", .var "proof", .var "pc",
      .var "source-body", .var "actual-body",
      assertionEssentialContinuationTemplate]

private theorem assertionEssentialContinuation_authorized
    (substitution : Subst) :
    NormalBodyContinuationAuthorized
      (applySubst substitution assertionEssentialContinuationTemplate) := by
  constructor
  · intro raw extracted
    simp [assertionEssentialContinuationTemplate, applySubst,
      applySubst.applySubstList, extractRawExecFact] at extracted
  · intro internalShape
    simp [assertionEssentialContinuationTemplate, applySubst,
      applySubst.applySubstList, isVerifierOwnedInternalRowShape,
      isVerifierOwnedInternalNamespace] at internalShape

private theorem assertionEssentialContinuation_not_carrier
    (substitution : Subst) (nested : Atom) :
    ¬ NormalBodyContinuationCapture
      (applySubst substitution assertionEssentialContinuationTemplate)
      nested := by
  intro captured
  have hasTag := normalBodyContinuationCapture_has_tag captured
  simp [assertionEssentialContinuationTemplate, applySubst,
    applySubst.applySubstList, normalBodyCarrierTag] at hasTag

/-- The essential-hypothesis launcher creates a carrier whose continuation is
fixed verifier data.  It does not copy executable authority from proof data. -/
theorem normalAssertionEssential_capability_additions_closed
    (space : List Atom) :
    let rows := (Conformance.Computable.cmatchInputSpec []
      (normalAssertionEssentialDirective.atom ::
        space.erase normalAssertionEssentialDirective.atom)
      normalAssertionEssentialDirective.rule.input).map Prod.fst
    ReflectiveAddedAtomsWithin NormalBodyCarrierAuthorized rows
      normalAssertionEssentialDirective.rule.tmpl := by
  dsimp only
  intro carrier added continuation captured
  rcases added with
    ⟨sink, sinkMember, authored, sinkEq,
      substitution, _rowMember, instantiates⟩
  subst sink
  change Sink.add authored ∈
    [Sink.remove
      (.expression
        [.symbol "mm-assertion-bind", .var "scope", .var "proof",
          .var "pc", .var "next-pc", .var "label",
          .var "hyp-position", .var "hyp-end", .var "stack-position",
          .var "stack-base"]),
     Sink.remove
      (.expression
        [.symbol "mm-stack-cell", .var "proof", .var "stack-position",
          .expression
            [.symbol "mm-formula", .var "typecode", .var "actual-body"],
          .var "child-occurrence"]),
     Sink.add assertionEssentialCarrierTemplate] at sinkMember
  have authoredEq : authored = assertionEssentialCarrierTemplate := by
    simpa using sinkMember
  subst authored
  have instantiated := instantiateTemplateAtom?_eq_some instantiates
  have expectedCapture : NormalBodyContinuationCapture carrier
      (applySubst substitution assertionEssentialContinuationTemplate) := by
    rw [← instantiated]
    simpa [assertionEssentialCarrierTemplate, applySubst,
      applySubst.applySubstList] using
      (NormalBodyContinuationCapture.bodyMatch
        (applySubst substitution (.var "proof"))
        (applySubst substitution (.var "pc"))
        (applySubst substitution (.var "source-body"))
        (applySubst substitution (.var "actual-body"))
        (applySubst substitution assertionEssentialContinuationTemplate))
  have continuationEq :=
    normalBodyContinuationCapture_unique captured expectedCapture
  subst continuation
  exact ⟨assertionEssentialContinuation_authorized substitution,
    assertionEssentialContinuation_not_carrier substitution⟩

/-! ## Propagated body-match continuations -/

private def bodyMatchConstFirstPattern : Atom :=
  .expression
    [.symbol "mm-body-match", .var "proof", .var "pc",
      .expression
        [.symbol "mm-cons",
          .expression [.symbol "mm-const", .var "constant-name"],
          .var "source-tail"],
      .expression
        [.symbol "mm-cons",
          .expression [.symbol "mm-const", .var "constant-name"],
          .var "actual-tail"],
      .var "continuation"]

private def bodyMatchConstTailTemplate : Atom :=
  .expression
    [.symbol "mm-body-match", .var "proof", .var "pc",
      .var "source-tail", .var "actual-tail", .var "continuation"]

private def bodyMatchReloadTemplate : Atom :=
  .expression
    [.symbol "mm-reload-body-match", .var "proof", .var "pc"]

/-- A constant match shortens both formula bodies while copying the exact
continuation captured from the matched predecessor carrier. -/
theorem normalBodyMatchConst_capability_additions_closed
    {space : List Atom}
    (state : AtomsWithin NormalBodyCarrierAuthorized space) :
    let rows := (Conformance.Computable.cmatchInputSpec []
      (normalBodyMatchConstDirective.atom ::
        space.erase normalBodyMatchConstDirective.atom)
      normalBodyMatchConstDirective.rule.input).map Prod.fst
    ReflectiveAddedAtomsWithin NormalBodyCarrierAuthorized rows
      normalBodyMatchConstDirective.rule.tmpl := by
  dsimp only
  intro carrier added continuation captured
  rcases added with
    ⟨sink, sinkMember, authored, sinkEq,
      substitution, rowMember, instantiates⟩
  subst sink
  change Sink.add authored ∈
    [Sink.remove bodyMatchConstFirstPattern,
     Sink.add bodyMatchConstTailTemplate,
     Sink.add bodyMatchReloadTemplate] at sinkMember
  have authoredCases :
      authored = bodyMatchConstTailTemplate ∨
        authored = bodyMatchReloadTemplate := by
    simpa using sinkMember
  rcases authoredCases with tail | reload
  · subst authored
    have rowMember' : substitution ∈
        (Conformance.Computable.cmatchInputSpec []
          (normalBodyMatchConstDirective.atom ::
            space.erase normalBodyMatchConstDirective.atom)
          (.compat (mkPattern [bodyMatchConstFirstPattern]))).map
            Prod.fst := by
      exact rowMember
    obtain ⟨value, _lookup, applied, valueInstantiates⟩ :=
      instantiated_template_binds_var "continuation" instantiates
        (by decide)
    obtain ⟨priorCarrier, priorMember, priorCaptured⟩ :=
      matchedContinuation_origin normalBodyMatchConstDirective
        bodyMatchConstFirstPattern [] rowMember'
        (matchAtom_bodyMatchPattern_captures
          (.expression
            [.symbol "mm-cons",
              .expression [.symbol "mm-const", .var "constant-name"],
              .var "source-tail"])
          (.expression
            [.symbol "mm-cons",
              .expression [.symbol "mm-const", .var "constant-name"],
              .var "actual-tail"]))
        (by
          intro payload carrierCapture
          have hasTag := normalBodyContinuationCapture_has_tag carrierCapture
          simp [normalBodyMatchConstDirective, normalBodyMatchConstRule,
            normalBodyCarrierTag] at hasTag)
        valueInstantiates
    have instantiated := instantiateTemplateAtom?_eq_some instantiates
    have expectedCapture : NormalBodyContinuationCapture carrier value := by
      rw [← instantiated]
      change NormalBodyContinuationCapture
        (.expression
          [.symbol "mm-body-match",
            applySubst substitution (.var "proof"),
            applySubst substitution (.var "pc"),
            applySubst substitution (.var "source-tail"),
            applySubst substitution (.var "actual-tail"),
            applySubst substitution (.var "continuation")]) value
      rw [applied]
      exact .bodyMatch _ _ _ _ _
    have continuationEq :=
      normalBodyContinuationCapture_unique captured expectedCapture
    subst continuation
    exact state priorCarrier priorMember value priorCaptured
  · subst authored
    exact False.elim
      (normalContinuationSafeInstantiation_no_capture rfl instantiates
        captured)

private def bodyMatchVariableFirstPattern : Atom :=
  .expression
    [.symbol "mm-body-match", .var "proof", .var "pc",
      .expression
        [.symbol "mm-cons",
          .expression [.symbol "mm-variable", .var "variable-name"],
          .var "source-tail"],
      .var "actual-body", .var "continuation"]

private def bodyMatchVariableSubstitutionPattern : Atom :=
  .expression
    [.symbol "mm-substitution", .var "proof", .var "pc",
      .var "variable-name", .var "replacement-body"]

private def bodyMatchVariablePrefixTemplate : Atom :=
  .expression
    [.symbol "mm-body-prefix", .var "proof", .var "pc",
      .var "replacement-body", .var "actual-body",
      .var "source-tail", .var "continuation"]

/-- A variable match copies its predecessor continuation into the prefix
machine; the independently matched substitution row supplies formula data,
not executable authority. -/
theorem normalBodyMatchVariable_capability_additions_closed
    {space : List Atom}
    (state : AtomsWithin NormalBodyCarrierAuthorized space) :
    let rows := (Conformance.Computable.cmatchInputSpec []
      (normalBodyMatchVariableDirective.atom ::
        space.erase normalBodyMatchVariableDirective.atom)
      normalBodyMatchVariableDirective.rule.input).map Prod.fst
    ReflectiveAddedAtomsWithin NormalBodyCarrierAuthorized rows
      normalBodyMatchVariableDirective.rule.tmpl := by
  dsimp only
  intro carrier added continuation captured
  rcases added with
    ⟨sink, sinkMember, authored, sinkEq,
      substitution, rowMember, instantiates⟩
  subst sink
  change Sink.add authored ∈
    [Sink.remove bodyMatchVariableFirstPattern,
     Sink.add bodyMatchVariablePrefixTemplate,
     Sink.add bodyMatchReloadTemplate] at sinkMember
  have authoredCases :
      authored = bodyMatchVariablePrefixTemplate ∨
        authored = bodyMatchReloadTemplate := by
    simpa using sinkMember
  rcases authoredCases with prefixSink | reload
  · subst authored
    have rowMember' : substitution ∈
        (Conformance.Computable.cmatchInputSpec []
          (normalBodyMatchVariableDirective.atom ::
            space.erase normalBodyMatchVariableDirective.atom)
          (.compat (mkPattern
            [bodyMatchVariableFirstPattern,
              bodyMatchVariableSubstitutionPattern]))).map Prod.fst := by
      exact rowMember
    obtain ⟨value, _lookup, applied, valueInstantiates⟩ :=
      instantiated_template_binds_var "continuation" instantiates
        (by decide)
    obtain ⟨priorCarrier, priorMember, priorCaptured⟩ :=
      matchedContinuation_origin normalBodyMatchVariableDirective
        bodyMatchVariableFirstPattern
        [bodyMatchVariableSubstitutionPattern] rowMember'
        (matchAtom_bodyMatchPattern_captures
          (.expression
            [.symbol "mm-cons",
              .expression [.symbol "mm-variable", .var "variable-name"],
              .var "source-tail"])
          (.var "actual-body"))
        (by
          intro payload carrierCapture
          have hasTag := normalBodyContinuationCapture_has_tag carrierCapture
          simp [normalBodyMatchVariableDirective,
            normalBodyMatchVariableRule, normalBodyCarrierTag] at hasTag)
        valueInstantiates
    have instantiated := instantiateTemplateAtom?_eq_some instantiates
    have expectedCapture : NormalBodyContinuationCapture carrier value := by
      rw [← instantiated]
      change NormalBodyContinuationCapture
        (.expression
          [.symbol "mm-body-prefix",
            applySubst substitution (.var "proof"),
            applySubst substitution (.var "pc"),
            applySubst substitution (.var "replacement-body"),
            applySubst substitution (.var "actual-body"),
            applySubst substitution (.var "source-tail"),
            applySubst substitution (.var "continuation")]) value
      rw [applied]
      exact .bodyPrefix _ _ _ _ _ _
    have continuationEq :=
      normalBodyContinuationCapture_unique captured expectedCapture
    subst continuation
    exact state priorCarrier priorMember value priorCaptured
  · subst authored
    exact False.elim
      (normalContinuationSafeInstantiation_no_capture rfl instantiates
        captured)

private def bodyPrefixNilPattern : Atom :=
  .expression
    [.symbol "mm-body-prefix", .var "proof", .var "pc",
      .expression [.symbol "mm-nil"], .var "actual-body",
      .var "source-tail", .var "continuation"]

private def bodyPrefixNilTailTemplate : Atom :=
  .expression
    [.symbol "mm-body-match", .var "proof", .var "pc",
      .var "source-tail", .var "actual-body", .var "continuation"]

/-- Finishing one replacement prefix returns to body matching with the exact
continuation captured from the consumed prefix carrier. -/
theorem normalBodyPrefixNil_capability_additions_closed
    {space : List Atom}
    (state : AtomsWithin NormalBodyCarrierAuthorized space) :
    let rows := (Conformance.Computable.cmatchInputSpec []
      (normalBodyPrefixNilDirective.atom ::
        space.erase normalBodyPrefixNilDirective.atom)
      normalBodyPrefixNilDirective.rule.input).map Prod.fst
    ReflectiveAddedAtomsWithin NormalBodyCarrierAuthorized rows
      normalBodyPrefixNilDirective.rule.tmpl := by
  dsimp only
  intro carrier added continuation captured
  rcases added with
    ⟨sink, sinkMember, authored, sinkEq,
      substitution, rowMember, instantiates⟩
  subst sink
  change Sink.add authored ∈
    [Sink.remove bodyPrefixNilPattern,
     Sink.add bodyPrefixNilTailTemplate,
     Sink.add bodyMatchReloadTemplate] at sinkMember
  have authoredCases :
      authored = bodyPrefixNilTailTemplate ∨
        authored = bodyMatchReloadTemplate := by
    simpa using sinkMember
  rcases authoredCases with tail | reload
  · subst authored
    have rowMember' : substitution ∈
        (Conformance.Computable.cmatchInputSpec []
          (normalBodyPrefixNilDirective.atom ::
            space.erase normalBodyPrefixNilDirective.atom)
          (.compat (mkPattern [bodyPrefixNilPattern]))).map Prod.fst := by
      exact rowMember
    obtain ⟨value, _lookup, applied, valueInstantiates⟩ :=
      instantiated_template_binds_var "continuation" instantiates
        (by decide)
    obtain ⟨priorCarrier, priorMember, priorCaptured⟩ :=
      matchedContinuation_origin normalBodyPrefixNilDirective
        bodyPrefixNilPattern [] rowMember'
        (matchAtom_bodyPrefixPattern_captures
          (.expression [.symbol "mm-nil"])
          (.var "actual-body") (.var "source-tail"))
        (by
          intro payload carrierCapture
          have hasTag := normalBodyContinuationCapture_has_tag carrierCapture
          simp [normalBodyPrefixNilDirective, normalBodyPrefixNilRule,
            normalBodyCarrierTag] at hasTag)
        valueInstantiates
    have instantiated := instantiateTemplateAtom?_eq_some instantiates
    have expectedCapture : NormalBodyContinuationCapture carrier value := by
      rw [← instantiated]
      change NormalBodyContinuationCapture
        (.expression
          [.symbol "mm-body-match",
            applySubst substitution (.var "proof"),
            applySubst substitution (.var "pc"),
            applySubst substitution (.var "source-tail"),
            applySubst substitution (.var "actual-body"),
            applySubst substitution (.var "continuation")]) value
      rw [applied]
      exact .bodyMatch _ _ _ _ _
    have continuationEq :=
      normalBodyContinuationCapture_unique captured expectedCapture
    subst continuation
    exact state priorCarrier priorMember value priorCaptured
  · subst authored
    exact False.elim
      (normalContinuationSafeInstantiation_no_capture rfl instantiates
        captured)

private def bodyPrefixConsPattern : Atom :=
  .expression
    [.symbol "mm-body-prefix", .var "proof", .var "pc",
      .expression
        [.symbol "mm-cons", .var "replacement-symbol",
          .var "replacement-tail"],
      .expression
        [.symbol "mm-cons", .var "replacement-symbol",
          .var "actual-tail"],
      .var "source-tail", .var "continuation"]

private def bodyPrefixConsTailTemplate : Atom :=
  .expression
    [.symbol "mm-body-prefix", .var "proof", .var "pc",
      .var "replacement-tail", .var "actual-tail",
      .var "source-tail", .var "continuation"]

/-- Consuming one equal replacement symbol preserves the predecessor
continuation while shortening both compared bodies. -/
theorem normalBodyPrefixCons_capability_additions_closed
    {space : List Atom}
    (state : AtomsWithin NormalBodyCarrierAuthorized space) :
    let rows := (Conformance.Computable.cmatchInputSpec []
      (normalBodyPrefixConsDirective.atom ::
        space.erase normalBodyPrefixConsDirective.atom)
      normalBodyPrefixConsDirective.rule.input).map Prod.fst
    ReflectiveAddedAtomsWithin NormalBodyCarrierAuthorized rows
      normalBodyPrefixConsDirective.rule.tmpl := by
  dsimp only
  intro carrier added continuation captured
  rcases added with
    ⟨sink, sinkMember, authored, sinkEq,
      substitution, rowMember, instantiates⟩
  subst sink
  change Sink.add authored ∈
    [Sink.remove bodyPrefixConsPattern,
     Sink.add bodyPrefixConsTailTemplate,
     Sink.add bodyMatchReloadTemplate] at sinkMember
  have authoredCases :
      authored = bodyPrefixConsTailTemplate ∨
        authored = bodyMatchReloadTemplate := by
    simpa using sinkMember
  rcases authoredCases with tail | reload
  · subst authored
    have rowMember' : substitution ∈
        (Conformance.Computable.cmatchInputSpec []
          (normalBodyPrefixConsDirective.atom ::
            space.erase normalBodyPrefixConsDirective.atom)
          (.compat (mkPattern [bodyPrefixConsPattern]))).map Prod.fst := by
      exact rowMember
    obtain ⟨value, _lookup, applied, valueInstantiates⟩ :=
      instantiated_template_binds_var "continuation" instantiates
        (by decide)
    obtain ⟨priorCarrier, priorMember, priorCaptured⟩ :=
      matchedContinuation_origin normalBodyPrefixConsDirective
        bodyPrefixConsPattern [] rowMember'
        (matchAtom_bodyPrefixPattern_captures
          (.expression
            [.symbol "mm-cons", .var "replacement-symbol",
              .var "replacement-tail"])
          (.expression
            [.symbol "mm-cons", .var "replacement-symbol",
              .var "actual-tail"])
          (.var "source-tail"))
        (by
          intro payload carrierCapture
          have hasTag := normalBodyContinuationCapture_has_tag carrierCapture
          simp [normalBodyPrefixConsDirective, normalBodyPrefixConsRule,
            normalBodyCarrierTag] at hasTag)
        valueInstantiates
    have instantiated := instantiateTemplateAtom?_eq_some instantiates
    have expectedCapture : NormalBodyContinuationCapture carrier value := by
      rw [← instantiated]
      change NormalBodyContinuationCapture
        (.expression
          [.symbol "mm-body-prefix",
            applySubst substitution (.var "proof"),
            applySubst substitution (.var "pc"),
            applySubst substitution (.var "replacement-tail"),
            applySubst substitution (.var "actual-tail"),
            applySubst substitution (.var "source-tail"),
            applySubst substitution (.var "continuation")]) value
      rw [applied]
      exact .bodyPrefix _ _ _ _ _ _
    have continuationEq :=
      normalBodyContinuationCapture_unique captured expectedCapture
    subst continuation
    exact state priorCarrier priorMember value priorCaptured
  · subst authored
    exact False.elim
      (normalContinuationSafeInstantiation_no_capture rfl instantiates
        captured)

private def bodyMatchNilPattern : Atom :=
  .expression
    [.symbol "mm-body-match", .var "proof", .var "pc",
      .expression [.symbol "mm-nil"], .expression [.symbol "mm-nil"],
      .var "continuation"]

/-- Publishing a completed body-match continuation cannot create another
carrier: the strengthened predecessor invariant explicitly excludes nested
body-machine carriers. -/
theorem normalBodyMatchNil_capability_additions_closed
    {space : List Atom}
    (state : AtomsWithin NormalBodyCarrierAuthorized space) :
    let rows := (Conformance.Computable.cmatchInputSpec []
      (normalBodyMatchNilDirective.atom ::
        space.erase normalBodyMatchNilDirective.atom)
      normalBodyMatchNilDirective.rule.input).map Prod.fst
    ReflectiveAddedAtomsWithin NormalBodyCarrierAuthorized rows
      normalBodyMatchNilDirective.rule.tmpl := by
  dsimp only
  intro carrier added continuation captured
  rcases added with
    ⟨sink, sinkMember, authored, sinkEq,
      substitution, rowMember, instantiates⟩
  subst sink
  change Sink.add authored ∈
    [Sink.remove bodyMatchNilPattern,
     Sink.add (.var "continuation"),
     Sink.add bodyMatchReloadTemplate] at sinkMember
  have authoredCases :
      authored = (.var "continuation" : Atom) ∨
        authored = bodyMatchReloadTemplate := by
    simpa using sinkMember
  rcases authoredCases with continuationSink | reload
  · subst authored
    obtain ⟨priorCarrier, priorMember, priorCaptured⟩ :=
      matchedContinuation_origin normalBodyMatchNilDirective
        bodyMatchNilPattern [] rowMember
        (matchAtom_bodyMatchPattern_captures
          (.expression [.symbol "mm-nil"])
          (.expression [.symbol "mm-nil"]))
        (by
          intro payload carrierCapture
          have hasTag := normalBodyContinuationCapture_has_tag carrierCapture
          simp [normalBodyMatchNilDirective, normalBodyMatchNilRule,
            normalBodyCarrierTag] at hasTag)
        instantiates
    exact False.elim
      ((state priorCarrier priorMember carrier priorCaptured).2
        continuation captured)
  · subst authored
    exact False.elim
      (normalContinuationSafeInstantiation_no_capture rfl instantiates
        captured)

private def NoNormalBodyCarrier (atom : Atom) : Prop :=
  ∀ nested, ¬ NormalBodyContinuationCapture atom nested

private theorem noNormalBodyCarrier_of_tag_false
    {atom : Atom} (tagFalse : normalBodyCarrierTag atom = false) :
    NoNormalBodyCarrier atom := by
  intro nested captured
  have hasTag := normalBodyContinuationCapture_has_tag captured
  rw [tagFalse] at hasTag
  contradiction

private theorem normalProofMachineRule_no_body_carrier
    {atom : Atom} (member : atom ∈ normalProofMachineRules) :
    NoNormalBodyCarrier atom := by
  apply noNormalBodyCarrier_of_tag_false
  have checked : normalProofMachineRules.all (fun rule =>
      normalBodyCarrierTag rule == false) = true := by
    decide +kernel
  exact beq_iff_eq.mp
    ((List.all_eq_true.mp checked) atom member)

/-- The body-rule reloader publishes only its fixed executable shell or one
of the five exact body-machine rules recovered from the owned bundle. -/
theorem normalBodyReload_additions_no_carrier
    {space : List Atom} (owned : NormalProofMachineExecutionContext space) :
    let rows := (Conformance.Computable.cmatchInputSpec []
      (normalBodyReloadDirective.atom ::
        space.erase normalBodyReloadDirective.atom)
      normalBodyReloadDirective.rule.input).map Prod.fst
    ReflectiveAddedAtomsWithin NoNormalBodyCarrier rows
      normalBodyReloadDirective.rule.tmpl := by
  dsimp only
  intro atom added nested captured
  rcases added with
    ⟨sink, sinkMember, authored, sinkEq,
      substitution, rowMember, instantiates⟩
  subst sink
  change Sink.add authored ∈
    [Sink.add
      (.expression
        [.symbol "exec",
          .expression [.symbol "11", .symbol "mm-normal-body-reload"],
          .var "body-reload-self-input", .var "body-reload-self-output"]),
     Sink.remove
      (.expression
        [.symbol "mm-reload-body-match", .var "body-reload-proof",
          .var "body-reload-pc"]),
     Sink.add (.var "body-rule-const"),
     Sink.add (.var "body-rule-variable"),
     Sink.add (.var "body-rule-prefix-nil"),
     Sink.add (.var "body-rule-prefix-cons"),
     Sink.add (.var "body-rule-nil")] at sinkMember
  have authoredCases :
      authored =
          (.expression
            [.symbol "exec",
              .expression [.symbol "11", .symbol "mm-normal-body-reload"],
              .var "body-reload-self-input",
              .var "body-reload-self-output"] : Atom) ∨
        authored ∈
          [(.var "body-rule-const" : Atom), .var "body-rule-variable",
            .var "body-rule-prefix-nil", .var "body-rule-prefix-cons",
            .var "body-rule-nil"] := by
    simpa using sinkMember
  rcases authoredCases with selfSink | ruleSink
  · subst authored
    have instantiated := instantiateTemplateAtom?_eq_some instantiates
    rw [← instantiated] at captured
    have hasTag := normalBodyContinuationCapture_has_tag captured
    simp [applySubst, applySubst.applySubstList, normalBodyCarrierTag]
      at hasTag
  · have authorized :=
      normalBodyReload_captured_rule_authorized owned rowMember ruleSink
        instantiates
    have machineMember : atom ∈ normalProofMachineRules := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at authorized
      rcases authorized with rfl | rfl | rfl | rfl | rfl <;>
        simp [normalProofMachineRules]
    exact (normalProofMachineRule_no_body_carrier machineMember) nested
      captured

/-- The result-body reloader has the same capability discipline: a fixed
executable self shell plus seven exact rules from its owned bundle. -/
theorem normalBodyBuildReload_additions_no_carrier
    {space : List Atom} (owned : NormalProofMachineExecutionContext space) :
    let rows := (Conformance.Computable.cmatchInputSpec []
      (normalBodyBuildReloadDirective.atom ::
        space.erase normalBodyBuildReloadDirective.atom)
      normalBodyBuildReloadDirective.rule.input).map Prod.fst
    ReflectiveAddedAtomsWithin NoNormalBodyCarrier rows
      normalBodyBuildReloadDirective.rule.tmpl := by
  dsimp only
  intro atom added nested captured
  rcases added with
    ⟨sink, sinkMember, authored, sinkEq,
      substitution, rowMember, instantiates⟩
  subst sink
  have authoredCases :
      authored =
          (.expression
            [.symbol "exec",
              .expression
                [.symbol "30", .symbol "mm-normal-body-build-reload"],
              .var "build-reload-self-input",
              .var "build-reload-self-output"] : Atom) ∨
        authored ∈
          [(.var "build-rule-const" : Atom), .var "build-rule-variable",
            .var "build-rule-prefix-nil", .var "build-rule-prefix-cons",
            .var "build-rule-nil", .var "build-rule-reverse-cons",
            .var "build-rule-reverse-nil"] := by
    change Sink.add authored ∈
      [Sink.add
        (.expression
          [.symbol "exec",
            .expression
              [.symbol "30", .symbol "mm-normal-body-build-reload"],
            .var "build-reload-self-input",
            .var "build-reload-self-output"]),
       Sink.remove
        (.expression
          [.symbol "mm-reload-body-build", .var "build-reload-proof",
            .var "build-reload-pc"]),
       Sink.add (.var "build-rule-const"),
       Sink.add (.var "build-rule-variable"),
       Sink.add (.var "build-rule-prefix-nil"),
       Sink.add (.var "build-rule-prefix-cons"),
       Sink.add (.var "build-rule-nil"),
       Sink.add (.var "build-rule-reverse-cons"),
       Sink.add (.var "build-rule-reverse-nil")] at sinkMember
    simpa using sinkMember
  rcases authoredCases with selfSink | ruleSink
  · subst authored
    have instantiated := instantiateTemplateAtom?_eq_some instantiates
    rw [← instantiated] at captured
    have hasTag := normalBodyContinuationCapture_has_tag captured
    simp [applySubst, applySubst.applySubstList, normalBodyCarrierTag]
      at hasTag
  · have authorized :=
      normalBodyBuildReload_captured_rule_authorized owned rowMember ruleSink
        instantiates
    have machineMember : atom ∈ normalProofMachineRules := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at authorized
      rcases authorized with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [normalProofMachineRules]
    exact (normalProofMachineRule_no_body_carrier machineMember) nested
      captured

/-- The DV reloader likewise recovers only its eight exact authored rules;
captured data cannot acquire body-continuation authority. -/
theorem normalDVReload_additions_no_carrier
    {space : List Atom} (owned : NormalProofMachineExecutionContext space) :
    let rows := (Conformance.Computable.cmatchInputSpec []
      (normalDVReloadDirective.atom ::
        space.erase normalDVReloadDirective.atom)
      normalDVReloadDirective.rule.input).map Prod.fst
    ReflectiveAddedAtomsWithin NoNormalBodyCarrier rows
      normalDVReloadDirective.rule.tmpl := by
  dsimp only
  intro atom added nested captured
  rcases added with
    ⟨sink, sinkMember, authored, sinkEq,
      substitution, rowMember, instantiates⟩
  subst sink
  have authoredCases :
      authored =
          (.expression
            [.symbol "exec",
              .expression [.symbol "22", .symbol "mm-normal-dv-reload"],
              .var "dv-reload-self-input",
              .var "dv-reload-self-output"] : Atom) ∨
        authored ∈
          [(.var "dv-rule-pair-begin" : Atom), .var "dv-rule-left-const",
            .var "dv-rule-left-variable", .var "dv-rule-right-const",
            .var "dv-rule-right-variable", .var "dv-rule-right-nil",
            .var "dv-rule-left-nil", .var "dv-rule-complete"] := by
    change Sink.add authored ∈
      [Sink.add
        (.expression
          [.symbol "exec",
            .expression [.symbol "22", .symbol "mm-normal-dv-reload"],
            .var "dv-reload-self-input", .var "dv-reload-self-output"]),
       Sink.remove
        (.expression
          [.symbol "mm-reload-dv", .var "dv-reload-proof",
            .var "dv-reload-pc"]),
       Sink.add (.var "dv-rule-pair-begin"),
       Sink.add (.var "dv-rule-left-const"),
       Sink.add (.var "dv-rule-left-variable"),
       Sink.add (.var "dv-rule-right-const"),
       Sink.add (.var "dv-rule-right-variable"),
       Sink.add (.var "dv-rule-right-nil"),
       Sink.add (.var "dv-rule-left-nil"),
       Sink.add (.var "dv-rule-complete")] at sinkMember
    simpa using sinkMember
  rcases authoredCases with selfSink | ruleSink
  · subst authored
    have instantiated := instantiateTemplateAtom?_eq_some instantiates
    rw [← instantiated] at captured
    have hasTag := normalBodyContinuationCapture_has_tag captured
    simp [applySubst, applySubst.applySubstList, normalBodyCarrierTag]
      at hasTag
  · have authorized :=
      normalDVReload_captured_rule_authorized owned rowMember ruleSink
        instantiates
    have machineMember : atom ∈ normalProofMachineRules := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at authorized
      rcases authorized with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl <;> simp [normalProofMachineRules]
    exact (normalProofMachineRule_no_body_carrier machineMember) nested
      captured

/-- Dispatch reload accepts only a rule from the exact verifier-owned
dispatch relation; suggestive row names alone are not capability evidence. -/
theorem normalDispatchReload_additions_no_carrier
    {space : List Atom} (owned : NormalVerifierInternalRowsIntact space) :
    let rows := (Conformance.Computable.cmatchInputSpec []
      (normalDispatchReloadDirective.atom ::
        space.erase normalDispatchReloadDirective.atom)
      normalDispatchReloadDirective.rule.input).map Prod.fst
    ReflectiveAddedAtomsWithin NoNormalBodyCarrier rows
      normalDispatchReloadDirective.rule.tmpl := by
  dsimp only
  intro atom added nested captured
  rcases added with
    ⟨sink, sinkMember, authored, sinkEq,
      substitution, rowMember, instantiates⟩
  subst sink
  change Sink.add authored ∈
    [Sink.add
      (.expression
        [.symbol "exec",
          .expression
            [.symbol "32", .symbol "mm-normal-dispatch-reload"],
          .var "reload-self-input", .var "reload-self-output"]),
     Sink.remove
      (.expression
        [.symbol "mm-reload-normal-dispatch", .var "reload-proof"]),
     Sink.add (.var "reload-rule")] at sinkMember
  have authoredCases :
      authored =
          (.expression
            [.symbol "exec",
              .expression
                [.symbol "32", .symbol "mm-normal-dispatch-reload"],
              .var "reload-self-input", .var "reload-self-output"] : Atom) ∨
        authored = .var "reload-rule" := by
    simpa using sinkMember
  rcases authoredCases with selfSink | ruleSink
  · subst authored
    have instantiated := instantiateTemplateAtom?_eq_some instantiates
    rw [← instantiated] at captured
    have hasTag := normalBodyContinuationCapture_has_tag captured
    simp [applySubst, applySubst.applySubstList, normalBodyCarrierTag]
      at hasTag
  · subst authored
    have machineMember : atom ∈ normalProofMachineRules :=
      normalDispatchReload_captured_rule_authorized_of_internal owned rowMember
        instantiates
    exact (normalProofMachineRule_no_body_carrier machineMember) nested
      captured

/-! ## Whole normal-machine capability closure -/

/-- Finite classification of the parsed normal verifier by the only six
templates capable of constructing or publishing body carriers.  Every other
template is structurally unable to create one. -/
private def normalProofMachineDirectiveCapabilityClassified
    (directive : SourceExecFact) : Bool :=
  decide (directive = normalAssertionEssentialDirective) ||
    decide (directive = normalBodyMatchConstDirective) ||
    decide (directive = normalBodyMatchVariableDirective) ||
    decide (directive = normalBodyPrefixNilDirective) ||
    decide (directive = normalBodyPrefixConsDirective) ||
    decide (directive = normalBodyMatchNilDirective) ||
    decide (directive = normalBodyReloadDirective) ||
    decide (directive = normalBodyBuildReloadDirective) ||
    decide (directive = normalDVReloadDirective) ||
    decide (directive = normalDispatchReloadDirective) ||
    directive.rule.tmpl.sinks.all normalContinuationSafeSink

private theorem normalProofMachineDirectives_all_capabilityClassified :
    normalProofMachineDirectives.all
      normalProofMachineDirectiveCapabilityClassified = true := by
  decide +kernel

theorem normalProofMachineDirective_capability_classification
    {directive : SourceExecFact}
    (member : directive ∈ normalProofMachineDirectives) :
    directive = normalAssertionEssentialDirective ∨
      directive = normalBodyMatchConstDirective ∨
      directive = normalBodyMatchVariableDirective ∨
      directive = normalBodyPrefixNilDirective ∨
      directive = normalBodyPrefixConsDirective ∨
      directive = normalBodyMatchNilDirective ∨
      directive = normalBodyReloadDirective ∨
      directive = normalBodyBuildReloadDirective ∨
      directive = normalDVReloadDirective ∨
      directive = normalDispatchReloadDirective ∨
      NormalContinuationSafeTemplate directive.rule.tmpl := by
  have checked :=
    (List.all_eq_true.mp
      normalProofMachineDirectives_all_capabilityClassified) directive member
  simp only [normalProofMachineDirectiveCapabilityClassified,
    Bool.or_eq_true, decide_eq_true_eq] at checked
  unfold NormalContinuationSafeTemplate
  aesop

/-- Every parsed normal-verifier directive preserves continuation capability
origin, including the six templates that manipulate body carriers. -/
theorem normalProofMachineDirective_capability_additions_closed
    {space : List Atom}
    (owned : NormalProofMachineOwnedState space)
    (state : AtomsWithin NormalBodyCarrierAuthorized space)
    {directive : SourceExecFact}
    (member : directive ∈ normalProofMachineDirectives) :
    let rows := (Conformance.Computable.cmatchInputSpec []
      (directive.atom :: space.erase directive.atom)
      directive.rule.input).map Prod.fst
    ReflectiveAddedAtomsWithin NormalBodyCarrierAuthorized rows
      directive.rule.tmpl := by
  rcases normalProofMachineDirective_capability_classification member with
    essential | bodyConst | bodyVariable | prefixNil | prefixCons |
      bodyNil | bodyReload | bodyBuildReload | dvReload | dispatchReload |
      safe
  · subst directive
    exact normalAssertionEssential_capability_additions_closed space
  · subst directive
    exact normalBodyMatchConst_capability_additions_closed state
  · subst directive
    exact normalBodyMatchVariable_capability_additions_closed state
  · subst directive
    exact normalBodyPrefixNil_capability_additions_closed state
  · subst directive
    exact normalBodyPrefixCons_capability_additions_closed state
  · subst directive
    exact normalBodyMatchNil_capability_additions_closed state
  · subst directive
    dsimp only
    intro atom added continuation captured
    exact False.elim
      (normalBodyReload_additions_no_carrier
        (NormalProofMachineOwnedState.executionContext owned) atom added
        continuation captured)
  · subst directive
    dsimp only
    intro atom added continuation captured
    exact False.elim
      (normalBodyBuildReload_additions_no_carrier
        (NormalProofMachineOwnedState.executionContext owned) atom added
        continuation captured)
  · subst directive
    dsimp only
    intro atom added continuation captured
    exact False.elim
      (normalDVReload_additions_no_carrier
        (NormalProofMachineOwnedState.executionContext owned) atom added
        continuation captured)
  · subst directive
    dsimp only
    intro atom added continuation captured
    exact False.elim
      (normalDispatchReload_additions_no_carrier owned.2 atom added
        continuation captured)
  · exact normalContinuationSafeTemplate_added_closed _ _ safe

/-- Continuation closure for the real authored ambient context.  The dispatch
reloader remains a separately audited case because its exact carrier theorem
predates the ambient-context abstraction. -/
theorem normalProofMachineDirective_capability_additions_closed_of_ne_dispatch
    {space : List Atom}
    (context : NormalProofMachineExecutionContext space)
    (state : AtomsWithin NormalBodyCarrierAuthorized space)
    {directive : SourceExecFact}
    (member : directive ∈ normalProofMachineDirectives)
    (notDispatch : directive ≠ normalDispatchReloadDirective) :
    let rows := (Conformance.Computable.cmatchInputSpec []
      (directive.atom :: space.erase directive.atom)
      directive.rule.input).map Prod.fst
    ReflectiveAddedAtomsWithin NormalBodyCarrierAuthorized rows
      directive.rule.tmpl := by
  rcases normalProofMachineDirective_capability_classification member with
    essential | bodyConst | bodyVariable | prefixNil | prefixCons |
      bodyNil | bodyReload | bodyBuildReload | dvReload | dispatchReload |
      safe
  · subst directive
    exact normalAssertionEssential_capability_additions_closed space
  · subst directive
    exact normalBodyMatchConst_capability_additions_closed state
  · subst directive
    exact normalBodyMatchVariable_capability_additions_closed state
  · subst directive
    exact normalBodyPrefixNil_capability_additions_closed state
  · subst directive
    exact normalBodyPrefixCons_capability_additions_closed state
  · subst directive
    exact normalBodyMatchNil_capability_additions_closed state
  · subst directive
    dsimp only
    intro atom added continuation captured
    exact False.elim
      (normalBodyReload_additions_no_carrier context atom added continuation
        captured)
  · subst directive
    dsimp only
    intro atom added continuation captured
    exact False.elim
      (normalBodyBuildReload_additions_no_carrier context atom added
        continuation captured)
  · subst directive
    dsimp only
    intro atom added continuation captured
    exact False.elim
      (normalDVReload_additions_no_carrier context atom added continuation
        captured)
  · exact False.elim (notDispatch dispatchReload)
  · exact normalContinuationSafeTemplate_added_closed _ _ safe

/-- Combine the existing executable and protected-row addition obligations
into the atom-local ownership predicate used by the rule-scoped executor. -/
private theorem reflectiveAddedOwnedAtom_of_raw_and_internal
    (rows : List Subst) (template : Template)
    (rawWithin :
      ReflectiveAddedRawWithin normalProofMachineRawFacts rows template)
    (internalWithin :
      ReflectiveAddedAtomsWithin NormalVerifierInternalRowIntact rows
        template) :
    ReflectiveAddedAtomsWithin NormalRuleScopedOwnedAtom rows template := by
  intro atom added
  exact ⟨rawWithin atom added, internalWithin atom added⟩

/-- Every authored normal directive satisfies both source-relative ownership
obligations under the fully-bound matcher semantics.  The body-match
completion consumes the stronger continuation-capability state. -/
private theorem
    normalProofMachineDirective_reflective_owned_additions_closed
    {space : List Atom}
    (owned : NormalProofMachineOwnedState space)
    (state : AtomsWithin NormalBodyCarrierAuthorized space)
    {directive : SourceExecFact}
    (member : directive ∈ normalProofMachineDirectives) :
    let rows := (Conformance.Computable.cmatchInputSpec []
      (directive.atom :: space.erase directive.atom)
      directive.rule.input).map Prod.fst
    ReflectiveAddedAtomsWithin NormalRuleScopedOwnedAtom rows
      directive.rule.tmpl := by
  rcases normalProofMachineDirective_owned_classification member with
    bodyReload | dvReload | bodyBuildReload | dispatchReload | hypothesis |
      assertionPop | assertionFloating | bodyMatchNil | safe
  · subst directive
    rcases normalBodyReload_owned_additions_closed
        (NormalProofMachineOwnedState.executionContext owned) with
      ⟨rawWithin, internalWithin⟩
    exact reflectiveAddedOwnedAtom_of_raw_and_internal _ _ rawWithin
      internalWithin
  · subst directive
    rcases normalDVReload_owned_additions_closed
        (NormalProofMachineOwnedState.executionContext owned) with
      ⟨rawWithin, internalWithin⟩
    exact reflectiveAddedOwnedAtom_of_raw_and_internal _ _ rawWithin
      internalWithin
  · subst directive
    rcases normalBodyBuildReload_owned_additions_closed
        (NormalProofMachineOwnedState.executionContext owned) with
      ⟨rawWithin, internalWithin⟩
    exact reflectiveAddedOwnedAtom_of_raw_and_internal _ _ rawWithin
      internalWithin
  · subst directive
    rcases normalDispatchReload_owned_additions_closed owned with
      ⟨rawWithin, internalWithin⟩
    exact reflectiveAddedOwnedAtom_of_raw_and_internal _ _ rawWithin
      internalWithin
  · subst directive
    exact reflectiveAddedOwnedAtom_of_raw_and_internal _ _
      (normalHypothesis_additions_raw_closed
        (NormalProofMachineOwnedState.executionContext owned))
      (normalHypothesis_additions_internal_closed
        (NormalProofMachineOwnedState.executionContext owned))
  · subst directive
    exact reflectiveAddedOwnedAtom_of_raw_and_internal _ _
      (normalAssertionPop_additions_raw_closed
        (NormalProofMachineOwnedState.executionContext owned))
      (normalAssertionPop_additions_internal_closed
        (NormalProofMachineOwnedState.executionContext owned))
  · subst directive
    exact reflectiveAddedOwnedAtom_of_raw_and_internal _ _
      (normalAssertionFloating_additions_raw_closed
        (NormalProofMachineOwnedState.executionContext owned))
      (normalAssertionFloating_additions_internal_closed
        (NormalProofMachineOwnedState.executionContext owned))
  · subst directive
    let capability : NormalProofMachineCapabilityState space :=
      ⟨owned, normalBodyCarrierAuthorized_implies_capabilities state⟩
    exact reflectiveAddedOwnedAtom_of_raw_and_internal _ _
      (normalBodyMatchNil_additions_raw_closed capability.2)
      (normalBodyMatchNil_additions_internal_closed capability.2)
  · exact reflectiveAddedOwnedAtom_of_raw_and_internal _ _
      (normalOwnedSafeTemplate_raw_closed _ _ safe)
      (normalOwnedSafeTemplate_internal_closed _ _ safe)

/-- The normal output obligation does not require the ambient space to contain
only normal directives.  Except for the legacy dispatch reloader, every
directive is justified by the complete authored execution context plus exact
continuation provenance. -/
theorem normalProofMachineDirective_reflective_owned_additions_closed_of_ne_dispatch
    {space : List Atom}
    (context : NormalProofMachineExecutionContext space)
    (state : AtomsWithin NormalBodyCarrierAuthorized space)
    {directive : SourceExecFact}
    (member : directive ∈ normalProofMachineDirectives)
    (notDispatch : directive ≠ normalDispatchReloadDirective) :
    let rows := (Conformance.Computable.cmatchInputSpec []
      (directive.atom :: space.erase directive.atom)
      directive.rule.input).map Prod.fst
    ReflectiveAddedAtomsWithin NormalRuleScopedOwnedAtom rows
      directive.rule.tmpl := by
  rcases normalProofMachineDirective_owned_classification member with
    bodyReload | dvReload | bodyBuildReload | dispatchReload | hypothesis |
      assertionPop | assertionFloating | bodyMatchNil | safe
  · subst directive
    rcases normalBodyReload_owned_additions_closed context with
      ⟨rawWithin, internalWithin⟩
    exact reflectiveAddedOwnedAtom_of_raw_and_internal _ _ rawWithin
      internalWithin
  · subst directive
    rcases normalDVReload_owned_additions_closed context with
      ⟨rawWithin, internalWithin⟩
    exact reflectiveAddedOwnedAtom_of_raw_and_internal _ _ rawWithin
      internalWithin
  · subst directive
    rcases normalBodyBuildReload_owned_additions_closed context with
      ⟨rawWithin, internalWithin⟩
    exact reflectiveAddedOwnedAtom_of_raw_and_internal _ _ rawWithin
      internalWithin
  · exact False.elim (notDispatch dispatchReload)
  · subst directive
    exact reflectiveAddedOwnedAtom_of_raw_and_internal _ _
      (normalHypothesis_additions_raw_closed context)
      (normalHypothesis_additions_internal_closed context)
  · subst directive
    exact reflectiveAddedOwnedAtom_of_raw_and_internal _ _
      (normalAssertionPop_additions_raw_closed context)
      (normalAssertionPop_additions_internal_closed context)
  · subst directive
    exact reflectiveAddedOwnedAtom_of_raw_and_internal _ _
      (normalAssertionFloating_additions_raw_closed context)
      (normalAssertionFloating_additions_internal_closed context)
  · subst directive
    let capabilities : NormalBodyContinuationCapabilities space :=
      normalBodyCarrierAuthorized_implies_capabilities state
    exact reflectiveAddedOwnedAtom_of_raw_and_internal _ _
      (normalBodyMatchNil_additions_raw_closed capabilities)
      (normalBodyMatchNil_additions_internal_closed capabilities)
  · exact reflectiveAddedOwnedAtom_of_raw_and_internal _ _
      (normalOwnedSafeTemplate_raw_closed _ _ safe)
      (normalOwnedSafeTemplate_internal_closed _ _ safe)

/-! ## Capability closure for the actual rule-scoped executor -/

@[simp] private def normalRuleScopedCompatInput : InputSpec → Bool
  | .compat _ => true
  | .explicit _ => false

private theorem normalProofMachineDirectives_all_ruleScopedCompatInput :
    normalProofMachineDirectives.all (fun directive =>
      normalRuleScopedCompatInput directive.rule.input) = true := by
  decide +kernel

private theorem normalProofMachineDirective_ruleScoped_compatInput
    {directive : SourceExecFact}
    (member : directive ∈ normalProofMachineDirectives) :
    ∃ pattern, directive.rule.input = .compat pattern := by
  have checked :=
    (List.all_eq_true.mp
      normalProofMachineDirectives_all_ruleScopedCompatInput) directive member
  cases inputEq : directive.rule.input with
  | compat pattern => exact ⟨pattern, rfl⟩
  | explicit factors =>
      simp [inputEq] at checked

private theorem normalProofMachineDirectives_all_ruleScopedOwnedBridge :
    normalProofMachineDirectives.all (fun directive =>
      directive.rule.tmpl.sinks.all
        (ruleScopedNormalOwnedBridgeSink directive.rule.input)) = true := by
  decide +kernel

private theorem normalProofMachineDirective_ruleScoped_ownedBridge
    {directive : SourceExecFact}
    (member : directive ∈ normalProofMachineDirectives) :
    RuleScopedNormalOwnedBridgeTemplate directive.rule.input
      directive.rule.tmpl := by
  exact (List.all_eq_true.mp
    normalProofMachineDirectives_all_ruleScopedOwnedBridge) directive member

/-- Every authored normal directive satisfies the exact ownership obligation
of the physical rule-scoped executor. -/
theorem normalProofMachineDirective_ruleScoped_owned_additions_closed
    {space : List Atom}
    (owned : NormalProofMachineOwnedState space)
    (state : AtomsWithin NormalBodyCarrierAuthorized space)
    {directive : SourceExecFact}
    (member : directive ∈ normalProofMachineDirectives) :
    let live := morkEraseSupport space directive.atom
    let read := morkInsertSupport live directive.atom
    let rows := (cMatchInputSpecMork [] read directive.rule.input).filter fun
      (substitution, _) => matchSourceGuards substitution directive.rule.guards
    RuleScopedTemplateAdditionsWithin NormalRuleScopedOwnedAtom
      directive.rule.input (rows.map Prod.fst) directive.rule.tmpl := by
  apply ruleScopedCompatOwned_additions_of_reflective directive
    (normalProofMachineDirective_ruleScoped_compatInput member)
    (normalProofMachineDirective_support_set member)
    (normalProofMachineDirective_ruleScoped_ownedBridge member)
  exact normalProofMachineDirective_reflective_owned_additions_closed
    (NormalProofMachineOwnedState.morkEraseSupport owned directive.atom)
    (morkEraseSupport_atomsWithin NormalBodyCarrierAuthorized space
      directive.atom state)
    member

/-- Rule-scoped form of the ambient-context theorem.  Guard filtering and
support coalescing do not weaken the exact reload-carrier argument. -/
theorem normalProofMachineDirective_ruleScoped_owned_additions_closed_of_ne_dispatch
    {space : List Atom}
    (context : NormalProofMachineExecutionContext space)
    (state : AtomsWithin NormalBodyCarrierAuthorized space)
    {directive : SourceExecFact}
    (member : directive ∈ normalProofMachineDirectives)
    (notDispatch : directive ≠ normalDispatchReloadDirective) :
    let live := morkEraseSupport space directive.atom
    let read := morkInsertSupport live directive.atom
    let rows := (cMatchInputSpecMork [] read directive.rule.input).filter fun
      (substitution, _) => matchSourceGuards substitution directive.rule.guards
    RuleScopedTemplateAdditionsWithin NormalRuleScopedOwnedAtom
      directive.rule.input (rows.map Prod.fst) directive.rule.tmpl := by
  apply ruleScopedCompatOwned_additions_of_reflective directive
    (normalProofMachineDirective_ruleScoped_compatInput member)
    (normalProofMachineDirective_support_set member)
    (normalProofMachineDirective_ruleScoped_ownedBridge member)
  exact
    normalProofMachineDirective_reflective_owned_additions_closed_of_ne_dispatch
      (NormalProofMachineExecutionContext.morkEraseSupport context
        directive.atom)
      (morkEraseSupport_atomsWithin NormalBodyCarrierAuthorized space
        directive.atom state)
      member notDispatch

/-- One actual rule-scoped firing preserves the complete normal verifier
ownership state. -/
theorem normalProofMachineDirective_ruleScoped_fire_owned
    {space : List Atom}
    (owned : NormalProofMachineOwnedState space)
    (state : AtomsWithin NormalBodyCarrierAuthorized space)
    {directive : SourceExecFact}
    (member : directive ∈ normalProofMachineDirectives) :
    NormalProofMachineOwnedState
      (cFireRuleScopedSourceExecFact space directive) := by
  apply normalProofMachineOwnedState_of_ruleScopedOwned
    (cFireRuleScopedSourceExecFact_list_nodup space directive owned.1.1)
  exact cFireRuleScopedSourceExecFact_atomsWithin_of_additions
    NormalRuleScopedOwnedAtom space directive
    (NormalProofMachineOwnedState.atomsWithin_ruleScopedOwned owned)
    (normalProofMachineDirective_ruleScoped_owned_additions_closed
      owned state member)

private def normalProofMachineDirectiveRuleScopedCapabilityClassified
    (directive : SourceExecFact) : Bool :=
  decide (directive = normalAssertionEssentialDirective) ||
    decide (directive = normalBodyMatchConstDirective) ||
    decide (directive = normalBodyMatchVariableDirective) ||
    decide (directive = normalBodyPrefixNilDirective) ||
    decide (directive = normalBodyPrefixConsDirective) ||
    decide (directive = normalBodyMatchNilDirective) ||
    decide (directive = normalBodyReloadDirective) ||
    decide (directive = normalBodyBuildReloadDirective) ||
    decide (directive = normalDVReloadDirective) ||
    decide (directive = normalDispatchReloadDirective) ||
    directive.rule.tmpl.sinks.all ruleScopedNormalContinuationSafeSink

private theorem
    normalProofMachineDirectives_all_ruleScopedCapabilityClassified :
    normalProofMachineDirectives.all
      normalProofMachineDirectiveRuleScopedCapabilityClassified = true := by
  decide +kernel

theorem normalProofMachineDirective_ruleScoped_capability_classification
    {directive : SourceExecFact}
    (member : directive ∈ normalProofMachineDirectives) :
    directive = normalAssertionEssentialDirective ∨
      directive = normalBodyMatchConstDirective ∨
      directive = normalBodyMatchVariableDirective ∨
      directive = normalBodyPrefixNilDirective ∨
      directive = normalBodyPrefixConsDirective ∨
      directive = normalBodyMatchNilDirective ∨
      directive = normalBodyReloadDirective ∨
      directive = normalBodyBuildReloadDirective ∨
      directive = normalDVReloadDirective ∨
      directive = normalDispatchReloadDirective ∨
      RuleScopedNormalContinuationSafeTemplate directive.rule.tmpl := by
  have checked :=
    (List.all_eq_true.mp
      normalProofMachineDirectives_all_ruleScopedCapabilityClassified)
      directive member
  simp only [normalProofMachineDirectiveRuleScopedCapabilityClassified,
    Bool.or_eq_true, decide_eq_true_eq] at checked
  unfold RuleScopedNormalContinuationSafeTemplate
  aesop

private theorem
    normalProofMachineDirective_ruleScoped_capability_additions_of_bridge
    {space : List Atom}
    (owned : NormalProofMachineOwnedState space)
    (state : AtomsWithin NormalBodyCarrierAuthorized space)
    {directive : SourceExecFact}
    (member : directive ∈ normalProofMachineDirectives)
    (compat : ∃ pattern, directive.rule.input = .compat pattern)
    (bridge : RuleScopedNormalCapabilityBridgeTemplate directive.rule.input
      directive.rule.tmpl) :
    let live := morkEraseSupport space directive.atom
    let read := morkInsertSupport live directive.atom
    let rows := (cMatchInputSpecMork [] read directive.rule.input).filter fun
      (substitution, _) => matchSourceGuards substitution directive.rule.guards
    RuleScopedTemplateAdditionsWithin NormalBodyCarrierAuthorized
      directive.rule.input (rows.map Prod.fst) directive.rule.tmpl := by
  apply ruleScopedCompatCapability_additions_of_reflective directive compat
    (normalProofMachineDirective_support_set member) bridge
  exact normalProofMachineDirective_capability_additions_closed
    (NormalProofMachineOwnedState.morkEraseSupport owned directive.atom)
    (morkEraseSupport_atomsWithin NormalBodyCarrierAuthorized space
      directive.atom state)
    member

/-- Every parsed normal-verifier directive satisfies the exact addition-only
capability obligation of the actual physical, guard-filtered rule-scoped
executor.  Output-local binders are admitted only on structurally
carrier-free templates; input-inherited outputs reuse the matcher-derived
authority proof. -/
theorem normalProofMachineDirective_ruleScoped_capability_additions_closed
    {space : List Atom}
    (owned : NormalProofMachineOwnedState space)
    (state : AtomsWithin NormalBodyCarrierAuthorized space)
    {directive : SourceExecFact}
    (member : directive ∈ normalProofMachineDirectives) :
    let live := morkEraseSupport space directive.atom
    let read := morkInsertSupport live directive.atom
    let rows := (cMatchInputSpecMork [] read directive.rule.input).filter fun
      (substitution, _) => matchSourceGuards substitution directive.rule.guards
    RuleScopedTemplateAdditionsWithin NormalBodyCarrierAuthorized
      directive.rule.input (rows.map Prod.fst) directive.rule.tmpl := by
  rcases
      normalProofMachineDirective_ruleScoped_capability_classification member
    with essential | bodyConst | bodyVariable | prefixNil | prefixCons |
      bodyNil | bodyReload | bodyBuildReload | dvReload | dispatchReload |
      safe
  · subst directive
    apply
      normalProofMachineDirective_ruleScoped_capability_additions_of_bridge
        owned state member ⟨_, rfl⟩
    unfold RuleScopedNormalCapabilityBridgeTemplate
    decide +kernel
  · subst directive
    apply
      normalProofMachineDirective_ruleScoped_capability_additions_of_bridge
        owned state member ⟨_, rfl⟩
    unfold RuleScopedNormalCapabilityBridgeTemplate
    decide +kernel
  · subst directive
    apply
      normalProofMachineDirective_ruleScoped_capability_additions_of_bridge
        owned state member ⟨_, rfl⟩
    unfold RuleScopedNormalCapabilityBridgeTemplate
    decide +kernel
  · subst directive
    apply
      normalProofMachineDirective_ruleScoped_capability_additions_of_bridge
        owned state member ⟨_, rfl⟩
    unfold RuleScopedNormalCapabilityBridgeTemplate
    decide +kernel
  · subst directive
    apply
      normalProofMachineDirective_ruleScoped_capability_additions_of_bridge
        owned state member ⟨_, rfl⟩
    unfold RuleScopedNormalCapabilityBridgeTemplate
    decide +kernel
  · subst directive
    apply
      normalProofMachineDirective_ruleScoped_capability_additions_of_bridge
        owned state member ⟨_, rfl⟩
    unfold RuleScopedNormalCapabilityBridgeTemplate
    decide +kernel
  · subst directive
    apply
      normalProofMachineDirective_ruleScoped_capability_additions_of_bridge
        owned state member ⟨_, rfl⟩
    unfold RuleScopedNormalCapabilityBridgeTemplate
    decide +kernel
  · subst directive
    apply
      normalProofMachineDirective_ruleScoped_capability_additions_of_bridge
        owned state member ⟨_, rfl⟩
    unfold RuleScopedNormalCapabilityBridgeTemplate
    decide +kernel
  · subst directive
    apply
      normalProofMachineDirective_ruleScoped_capability_additions_of_bridge
        owned state member ⟨_, rfl⟩
    unfold RuleScopedNormalCapabilityBridgeTemplate
    decide +kernel
  · subst directive
    apply
      normalProofMachineDirective_ruleScoped_capability_additions_of_bridge
        owned state member ⟨_, rfl⟩
    unfold RuleScopedNormalCapabilityBridgeTemplate
    decide +kernel
  · exact ruleScopedNormalContinuationSafeTemplate_additions
      directive.rule.input _ directive.rule.tmpl safe

private theorem
    normalProofMachineDirectives_all_ruleScopedCapabilityBridge :
    normalProofMachineDirectives.all (fun directive =>
      directive.rule.tmpl.sinks.all
        (ruleScopedNormalCapabilityBridgeSink directive.rule.input)) = true := by
  decide +kernel

private theorem normalProofMachineDirective_ruleScoped_capabilityBridge
    {directive : SourceExecFact}
    (member : directive ∈ normalProofMachineDirectives) :
    RuleScopedNormalCapabilityBridgeTemplate directive.rule.input
      directive.rule.tmpl := by
  exact (List.all_eq_true.mp
    normalProofMachineDirectives_all_ruleScopedCapabilityBridge)
      directive member

/-- Ambient-context version of continuation closure for the physical
rule-scoped executor. -/
theorem normalProofMachineDirective_ruleScoped_capability_additions_closed_of_ne_dispatch
    {space : List Atom}
    (context : NormalProofMachineExecutionContext space)
    (state : AtomsWithin NormalBodyCarrierAuthorized space)
    {directive : SourceExecFact}
    (member : directive ∈ normalProofMachineDirectives)
    (notDispatch : directive ≠ normalDispatchReloadDirective) :
    let live := morkEraseSupport space directive.atom
    let read := morkInsertSupport live directive.atom
    let rows := (cMatchInputSpecMork [] read directive.rule.input).filter fun
      (substitution, _) => matchSourceGuards substitution directive.rule.guards
    RuleScopedTemplateAdditionsWithin NormalBodyCarrierAuthorized
      directive.rule.input (rows.map Prod.fst) directive.rule.tmpl := by
  apply ruleScopedCompatCapability_additions_of_reflective directive
    (normalProofMachineDirective_ruleScoped_compatInput member)
    (normalProofMachineDirective_support_set member)
    (normalProofMachineDirective_ruleScoped_capabilityBridge member)
  exact normalProofMachineDirective_capability_additions_closed_of_ne_dispatch
    (NormalProofMachineExecutionContext.morkEraseSupport context
      directive.atom)
    (morkEraseSupport_atomsWithin NormalBodyCarrierAuthorized space
      directive.atom state)
    member notDispatch

/-- One actual rule-scoped firing of an authored normal verifier directive
preserves continuation authority. -/
theorem normalProofMachineDirective_ruleScoped_fire_bodyCarrierAuthorized
    {space : List Atom}
    (owned : NormalProofMachineOwnedState space)
    (state : AtomsWithin NormalBodyCarrierAuthorized space)
    {directive : SourceExecFact}
    (member : directive ∈ normalProofMachineDirectives) :
    AtomsWithin NormalBodyCarrierAuthorized
      (cFireRuleScopedSourceExecFact space directive) := by
  exact cFireRuleScopedSourceExecFact_atomsWithin_of_additions
    NormalBodyCarrierAuthorized space directive state
    (normalProofMachineDirective_ruleScoped_capability_additions_closed
      owned state member)

/-- The induction motive for arbitrary normal execution combines established
verifier ownership with non-nesting continuation provenance. -/
def NormalProofMachineClosedCapabilityState (space : List Atom) : Prop :=
  NormalProofMachineOwnedState space ∧
    AtomsWithin NormalBodyCarrierAuthorized space

/-- One explicitly selected authored normal directive preserves the complete
capability-origin state under the actual rule-scoped physical executor. -/
theorem NormalProofMachineClosedCapabilityState.fireRuleScoped
    {space : List Atom}
    (state : NormalProofMachineClosedCapabilityState space)
    {directive : SourceExecFact}
    (member : directive ∈ normalProofMachineDirectives) :
    NormalProofMachineClosedCapabilityState
      (cFireRuleScopedSourceExecFact space directive) := by
  exact ⟨normalProofMachineDirective_ruleScoped_fire_owned
      state.1 state.2 member,
    normalProofMachineDirective_ruleScoped_fire_bodyCarrierAuthorized
      state.1 state.2 member⟩

/-- One scheduler-selected rule-scoped transition preserves the complete
normal capability state.  Membership of the selected directive is recovered
from the owned executable inventory. -/
theorem NormalProofMachineClosedCapabilityState.ruleScopedStep
    {space target : List Atom}
    (state : NormalProofMachineClosedCapabilityState space)
    (moved :
      cRuleScopedSourceWorkQueueStep .leaveInert space = some target) :
    NormalProofMachineClosedCapabilityState target := by
  unfold cRuleScopedSourceWorkQueueStep at moved
  cases selected : selectNextScheduled (cSupportedSourceExecFacts space) with
  | none => simp [selected] at moved
  | some directive =>
      simp only [selected] at moved
      have targetEq : cFireRuleScopedSourceExecFact space directive = target :=
        Option.some.inj moved
      subst target
      apply state.fireRuleScoped
      exact normalProofMachine_supportedWithin_of_rawWithin space
        state.1.1.2 directive (selectNextScheduled_mem selected)

/-- The complete normal capability state is preserved through every primitive
transition in an arbitrary OSLF-classified rule-scoped trace. -/
theorem NormalProofMachineClosedCapabilityState.of_ruleScopedNativeTypeTrace
    {policy : UnsupportedExecPolicy} (policyEq : policy = .leaveInert)
    {fuel : Nat} {source target : List Atom}
    (initial : NormalProofMachineClosedCapabilityState source)
    (trace : RuleScopedNativeTypeTrace policy fuel source target) :
    NormalProofMachineClosedCapabilityState target := by
  subst policy
  induction trace with
  | refl => exact initial
  | step native tail induction =>
      apply induction
      exact initial.ruleScopedStep
        ((satisfies_ruleScopedNativeListExactTargetNativeType_iff_step
          .leaveInert _ _).1 native)

/-- The exact-fuel rule-scoped evaluator preserves the complete normal
capability state at its returned boundary. -/
theorem NormalProofMachineClosedCapabilityState.ruleScopedRunN
    (fuel : Nat) {source : List Atom}
    (initial : NormalProofMachineClosedCapabilityState source) :
    NormalProofMachineClosedCapabilityState
      (cRuleScopedSourceWorkQueueRunN .leaveInert fuel source).1 := by
  exact initial.of_ruleScopedNativeTypeTrace rfl
    (cRuleScopedSourceWorkQueueRunN_nativeTypeTrace .leaveInert fuel source)

/-- One explicitly selected authored normal directive preserves the complete
capability-origin state. -/
theorem NormalProofMachineClosedCapabilityState.fire
    {space : List Atom}
    (state : NormalProofMachineClosedCapabilityState space)
    {directive : SourceExecFact}
    (member : directive ∈ normalProofMachineDirectives) :
    NormalProofMachineClosedCapabilityState
      (cFireReflectiveSourceExecFact space directive) := by
  constructor
  · exact NormalProofMachineCapabilityState.fire_owned
      ⟨state.1,
        normalBodyCarrierAuthorized_implies_capabilities state.2⟩ member
  · exact cFireReflectiveSourceExecFact_atomsWithin
      NormalBodyCarrierAuthorized space directive
      (normalProofMachineDirective_support_set member) state.2
      (normalProofMachineDirective_capability_additions_closed state.1
        state.2 member)

/-- One scheduler-selected list transition preserves the complete normal
capability state.  Directive membership is reconstructed from the owned raw
inventory rather than accepted as an external premise. -/
theorem NormalProofMachineClosedCapabilityState.step
    {space target : List Atom}
    (state : NormalProofMachineClosedCapabilityState space)
    (moved : cReflectiveSourceWorkQueueStep .leaveInert space = some target) :
    NormalProofMachineClosedCapabilityState target := by
  unfold cReflectiveSourceWorkQueueStep at moved
  cases selected : selectNextScheduled (cSupportedSourceExecFacts space) with
  | none => simp [selected] at moved
  | some directive =>
      simp only [selected] at moved
      have targetEq : cFireReflectiveSourceExecFact space directive = target :=
        Option.some.inj moved
      subst target
      apply state.fire
      exact normalProofMachine_supportedWithin_of_rawWithin space
        state.1.1.2 directive (selectNextScheduled_mem selected)

/-- A scheduled transition packaged with both exact OSLF/NTT witnesses: the
executable list realization and the authored support-valued MM2 semantics. -/
structure NormalCapabilityScheduledStep
    (source target : List Atom) : Type where
  moved : cReflectiveSourceWorkQueueStep .leaveInert source = some target
  targetState : NormalProofMachineClosedCapabilityState target
  executableNative :
    (gsltOSLF (reflectiveNativeListExecGSLT .leaveInert)).satisfies source
      (reflectiveNativeListExactTargetNativeType .leaveInert target).pred
  supportNative :
    ReflectiveSupportNativeTypeTrace .leaveInert source.toFinset target.toFinset

/-- Capability preservation and both OSLF-generated native witnesses are
constructed from the same concrete scheduled step. -/
def NormalProofMachineClosedCapabilityState.scheduledStep
    {source target : List Atom}
    (state : NormalProofMachineClosedCapabilityState source)
    (moved : cReflectiveSourceWorkQueueStep .leaveInert source = some target) :
    NormalCapabilityScheduledStep source target := by
  let adequate : CReflectiveAdequateTrace .leaveInert 1 source target :=
    .step state.1.1.reflectiveInvariant moved (.refl)
  exact
    { moved := moved
      targetState := state.step moved
      executableNative :=
        (satisfies_reflectiveNativeListExactTargetNativeType_iff_step
          .leaveInert source target).2 moved
      supportNative := adequate.toSupportNativeTypeTrace }

/-- A quiescent normal state cannot invent a packaged target step. -/
theorem no_normalCapabilityScheduledStep_of_no_selected
    {source : List Atom}
    (noneSelected :
      selectNextScheduled (cSupportedSourceExecFacts source) = none) :
    ¬ ∃ target, Nonempty (NormalCapabilityScheduledStep source target) := by
  rintro ⟨target, ⟨packaged⟩⟩
  have moved := packaged.moved
  unfold cReflectiveSourceWorkQueueStep at moved
  simp [noneSelected] at moved

/-- The strengthened capability state is preserved along an arbitrary
threaded concrete reachability witness. -/
theorem NormalProofMachineClosedCapabilityState.of_reachable
    {fuel : Nat} {source target : List Atom}
    (initial : NormalProofMachineClosedCapabilityState source)
    (reachable : CReflectiveReachable .leaveInert fuel source target) :
    NormalProofMachineClosedCapabilityState target := by
  induction reachable with
  | refl => exact initial
  | step moved tail induction =>
      exact induction (initial.step moved)

/-- Arbitrary normal execution from one capability-closed admitted boundary
is an adequate trace of the actual authored MM2 GSLT. -/
def normalCapabilityAdequateTrace
    (fuel : Nat) (source : List Atom)
    (initial : NormalProofMachineClosedCapabilityState source) :
    CReflectiveAdequateTrace .leaveInert fuel source
      (cReflectiveSourceWorkQueueRunN .leaveInert fuel source).1 :=
  cReflectiveSourceWorkQueueRunN_adequateTrace .leaveInert fuel source
    (fun _ reachable =>
      (initial.of_reachable reachable).1.1.reflectiveInvariant)

/-- OSLF classifies every primitive transition in the arbitrary authored-MM2
normal run by the exact generated native type of its successor. -/
def normalCapabilitySupportNativeTypeTrace
    (fuel : Nat) (source : List Atom)
    (initial : NormalProofMachineClosedCapabilityState source) :
    ReflectiveSupportNativeTypeTrace .leaveInert source.toFinset
      (cReflectiveSourceWorkQueueRunN .leaveInert fuel source).1.toFinset :=
  (normalCapabilityAdequateTrace fuel source initial).toSupportNativeTypeTrace

section AxiomAudit

#print axioms normalBodyCarrierAuthorized_implies_capabilities
#print axioms nested_body_carrier_is_rejected
#print axioms normalBodyCarrierAuthorized_of_shape_false
#print axioms normalBodyCarrierAuthorized_of_proofNeutral
#print axioms atomsWithin_normalBodyCarrierAuthorized_of_all_proofNeutral
#print axioms normalContinuationSafeTemplateAtom_ruleScoped_authorized
#print axioms ruleScopedNormalContinuationSafeTemplate_additions
#print axioms ruleScopedInheritedTemplate_additions_of_reflective
#print axioms reflectiveAddedAtomsWithin_of_rows_subset
#print axioms ruleScopedCompatRow_mem_reflectiveRead
#print axioms AdmittedSourceEventInput.initialRows_body_carrier_authorized
#print axioms normalVerifierInternalRows_no_normal_body_carrier
#print axioms authoredNormalVerifierRules_no_normal_body_carrier
#print axioms genericVerifierProgram_no_normal_body_carrier
#print axioms normalVerifierInternalRows_body_carrier_authorized
#print axioms authoredNormalVerifierRules_body_carrier_authorized
#print axioms genericVerifierProgram_body_carrier_authorized
#print axioms sourceDataProgram_body_carrier_authorized
#print axioms composeProgram_body_carrier_authorized
#print axioms authored_normal_verifier_program_body_carrier_authorized
#print axioms composeAdmittedNormalProgram_body_carrier_authorized
#print axioms normalContinuationSafeTemplate_added_closed
#print axioms normalAssertionEssential_capability_additions_closed
#print axioms normalBodyMatchConst_capability_additions_closed
#print axioms normalBodyMatchVariable_capability_additions_closed
#print axioms normalBodyPrefixNil_capability_additions_closed
#print axioms normalBodyPrefixCons_capability_additions_closed
#print axioms normalBodyMatchNil_capability_additions_closed
#print axioms normalProofMachineDirective_capability_classification
#print axioms normalProofMachineDirective_capability_additions_closed
#print axioms normalProofMachineDirective_capability_additions_closed_of_ne_dispatch
#print axioms normalProofMachineDirective_ruleScoped_owned_additions_closed
#print axioms normalProofMachineDirective_reflective_owned_additions_closed_of_ne_dispatch
#print axioms normalProofMachineDirective_ruleScoped_owned_additions_closed_of_ne_dispatch
#print axioms normalProofMachineDirective_ruleScoped_fire_owned
#print axioms normalProofMachineDirective_ruleScoped_capability_classification
#print axioms normalProofMachineDirective_ruleScoped_capability_additions_closed
#print axioms normalProofMachineDirective_ruleScoped_capability_additions_closed_of_ne_dispatch
#print axioms normalProofMachineDirective_ruleScoped_fire_bodyCarrierAuthorized
#print axioms NormalProofMachineClosedCapabilityState.fireRuleScoped
#print axioms NormalProofMachineClosedCapabilityState.ruleScopedStep
#print axioms NormalProofMachineClosedCapabilityState.of_ruleScopedNativeTypeTrace
#print axioms NormalProofMachineClosedCapabilityState.ruleScopedRunN
#print axioms NormalProofMachineClosedCapabilityState.fire
#print axioms NormalProofMachineClosedCapabilityState.step
#print axioms NormalProofMachineClosedCapabilityState.scheduledStep
#print axioms no_normalCapabilityScheduledStep_of_no_selected
#print axioms NormalProofMachineClosedCapabilityState.of_reachable
#print axioms normalCapabilityAdequateTrace
#print axioms normalCapabilitySupportNativeTypeTrace

end AxiomAudit

end Mettapedia.Languages.Metamath.MM2NormalProofCapabilityClosure
