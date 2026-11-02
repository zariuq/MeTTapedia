import Mettapedia.Logic.TierZero.Adequacy.HOLLightLicensedValues

/-! # Actual ordinary firings preserve rooted context and theorem authority -/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightLicensedSemantics

open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight.DefinitionAdapters
open Mettapedia.Languages.HOLLight.ProofExecution.Registered
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Logic
open InferenceSchemaActivation (action)
open HOLLightContextActivation (Entry theoremPayload theoremPayload_fixed)
open HOLLightContextLicensing
open HOLLightLicensedActivation
open HOLLightLicensedValues

theorem weakening_valid {O : Type*} [DecidableEq O]
    (initial : TheoryContext) (policy : AxiomPolicy) [DecidablePred policy] (contexts : Nat → TheoryContext)
    (beforeContext afterContext : Nat) (fact : Theorem) (label : O → Value)
    {before : Configuration Value O} {picked : Selection O}
    (qualified : picked.Valid locatedAction label (weakeningRule beforeContext afterContext fact) before)
    (assignment : ABTProtectedParameters.Assignment InferenceSchemaActivation.Head 0)
    (solved : locatedAction.Models assignment (picked.problem label (weakeningRule beforeContext afterContext fact) before))
    (incoming : ∀ occurrence ∈ picked.read, Meaning initial policy contexts (locatedAction.apply assignment (label occurrence))) :
    ∀ occurrence ∈ picked.made, Meaning initial policy contexts (locatedAction.apply assignment (label occurrence)) := by
  have reads := read_values initial policy contexts assignment label
    (Selection.models_problem locatedAction qualified solved).2.2.1 (by
      intro value member
      simp only [weakeningRule, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · exact pair_fixed _ _ (available_fixed _)
      · exact pair_fixed _ _ (included_fixed _ _)
      · exact pair_fixed _ _ (theoremPayload_fixed _ _)) incoming
  have licensed := (reads (licenses, available afterContext) (by simp [weakeningRule])).1 afterContext rfl
  have path := (reads (licenses, included beforeContext afterContext) (by simp [weakeningRule])).2.1 beforeContext afterContext rfl
  have original := (reads (judgments, theoremPayload beforeContext fact) (by simp [weakeningRule])).2.2 beforeContext fact rfl
  intro occurrence made
  have member : label occurrence ∈ (weakeningRule beforeContext afterContext fact).produce := by
    rw [← qualified.outputs]
    exact List.mem_map.mpr ⟨occurrence, made, rfl⟩
  have same : label occurrence = (judgments, theoremPayload afterContext fact) := List.mem_singleton.mp member
  rw [same, pair_fixed _ _ (theoremPayload_fixed _ _) assignment]
  exact meaning_theorem initial policy contexts afterContext fact licensed (transport_theorem policy path original.2)

theorem composition_valid {O : Type*} [DecidableEq O]
    (initial : TheoryContext) (policy : AxiomPolicy) [DecidablePred policy] (contexts : Nat → TheoryContext)
    (first middle last : Nat) (label : O → Value)
    {before : Configuration Value O} {picked : Selection O}
    (qualified : picked.Valid locatedAction label (compositionRule first middle last) before)
    (assignment : ABTProtectedParameters.Assignment InferenceSchemaActivation.Head 0)
    (solved : locatedAction.Models assignment (picked.problem label (compositionRule first middle last) before))
    (incoming : ∀ occurrence ∈ picked.read, Meaning initial policy contexts (locatedAction.apply assignment (label occurrence))) :
    ∀ occurrence ∈ picked.made, Meaning initial policy contexts (locatedAction.apply assignment (label occurrence)) := by
  have reads := read_values initial policy contexts assignment label
    (Selection.models_problem locatedAction qualified solved).2.2.1 (by
      intro value member
      simp only [compositionRule, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact pair_fixed _ _ (included_fixed _ _)
      · exact pair_fixed _ _ (included_fixed _ _)) incoming
  have left := (reads (licenses, included first middle) (by simp [compositionRule])).2.1 first middle rfl
  have right := (reads (licenses, included middle last) (by simp [compositionRule])).2.1 middle last rfl
  intro occurrence made
  have member : label occurrence ∈ (compositionRule first middle last).produce := by
    rw [← qualified.outputs]
    exact List.mem_map.mpr ⟨occurrence, made, rfl⟩
  have same : label occurrence = (licenses, included first last) := List.mem_singleton.mp member
  rw [same, pair_fixed _ _ (included_fixed _ _) assignment]
  exact meaning_included initial policy contexts first last (path_trans policy left right)

private theorem command_origin (policy : AxiomPolicy) [DecidablePred policy] (contexts : Nat → TheoryContext)
    (entries : Nat → Option (Entry contexts)) (source : Nat) (cache : Array Theorem)
    {actual : RuleInstance Value} (computed : commandActivate policy contexts entries source cache = some actual) :
    ∃ entry raw, entries source = some entry ∧
      HOLLightContextActivation.activate policy contexts entries source cache = some raw ∧ actual = commandRule entry raw := by
  cases known : entries source with
  | none => simp [commandActivate, known] at computed
  | some entry =>
      cases baseComputed : HOLLightContextActivation.activate policy contexts entries source cache with
      | none => simp [commandActivate, known, baseComputed] at computed
      | some raw =>
          have same : commandRule entry raw = actual := by simpa [commandActivate, known, baseComputed] using computed
          exact ⟨entry, raw, rfl, rfl, same.symm⟩

theorem command_valid {O : Type*} [DecidableEq O]
    (initial : TheoryContext) (policy : AxiomPolicy) [DecidablePred policy] (contexts : Nat → TheoryContext)
    (entries : Nat → Option (Entry contexts)) (source : Nat) (cache : Array Theorem)
    {actual : RuleInstance Value} (computed : commandActivate policy contexts entries source cache = some actual)
    (label : O → Value) {before : Configuration Value O} {picked : Selection O}
    (qualified : picked.Valid locatedAction label actual before)
    (assignment : ABTProtectedParameters.Assignment InferenceSchemaActivation.Head 0)
    (solved : locatedAction.Models assignment (picked.problem label actual before))
    (incoming : ∀ occurrence ∈ picked.read, Meaning initial policy contexts (locatedAction.apply assignment (label occurrence))) :
    ∀ occurrence ∈ picked.made, Meaning initial policy contexts (locatedAction.apply assignment (label occurrence)) := by
  obtain ⟨entry, raw, known, baseComputed, rfl⟩ := command_origin policy contexts entries source cache computed
  obtain ⟨actualEntry, output, parents, actualKnown, checked, selected, contextSame, rawSame⟩ :=
    HOLLightContextActivation.origin policy contexts entries source cache baseComputed
  have entrySame : entry = actualEntry := Option.some.inj (known.symm.trans actualKnown)
  subst actualEntry
  subst raw
  have reads := read_values initial policy contexts assignment label
    (Selection.models_problem locatedAction qualified solved).2.2.1 (by
      intro value member
      rcases List.mem_cons.mp member with rfl | member
      · exact pair_fixed _ _ (available_fixed _)
      · obtain ⟨base, baseMember, rfl⟩ := List.mem_map.mp member
        obtain ⟨fact, _, rfl⟩ := List.mem_map.mp baseMember
        exact pair_fixed _ _ (theoremPayload_fixed _ _)) incoming
  have priorLicense := (reads (licenses, available entry.before) (List.mem_cons_self ..)).1 entry.before rfl
  have priorProofs : ∀ index ∈ entry.command.parents, ∀ fact,
      cache[index]? = some fact → TheoryDerives policy (contexts entry.before) fact := by
    intro index cited fact found
    have factMember := DerivationGraph.lookupPremises_cited cache selected index cited fact found
    have baseMember : (InferenceSchemaKernel.Space.judgments, theoremPayload entry.before fact) ∈
        (HOLLightContextActivation.fromResult source entry cache parents output).read :=
      List.mem_map.mpr ⟨fact, factMember, rfl⟩
    have liftedMember : (judgments, theoremPayload entry.before fact) ∈
        ((HOLLightContextActivation.fromResult source entry cache parents output).read.map lift) :=
      List.mem_map.mpr ⟨_, baseMember, rfl⟩
    exact ((reads _ (List.mem_cons_of_mem _ liftedMember)).2.2 entry.before fact rfl).2
  have licensedOutput := checked_command_licenses_output initial policy priorLicense entry.command cache checked priorProofs
  have licensedAfter : Licensed initial policy (contexts entry.after) := contextSame ▸ licensedOutput.1
  have path : Path policy (contexts entry.before) (contexts entry.after) := contextSame ▸ licensedOutput.2.1
  intro occurrence made
  have member : label occurrence ∈ administrativeOutputs entry ++
      (HOLLightContextActivation.fromResult source entry cache parents output).produce.map lift := by
    have actualMember : label occurrence ∈ picked.made.map label := List.mem_map.mpr ⟨occurrence, made, rfl⟩
    rw [qualified.outputs] at actualMember
    exact actualMember
  rcases List.mem_append.mp member with administrative | logical
  · by_cases sameContext : entry.after = entry.before
    · simp [administrativeOutputs, sameContext] at administrative
    · simp only [administrativeOutputs, if_neg sameContext, List.mem_cons, List.not_mem_nil, or_false] at administrative
      rcases administrative with same | same
      · rw [same, pair_fixed _ _ (available_fixed _) assignment]
        exact meaning_available initial policy contexts entry.after licensedAfter
      · rw [same, pair_fixed _ _ (included_fixed _ _) assignment]
        exact meaning_included initial policy contexts entry.before entry.after path
  · simp only [HOLLightContextActivation.fromResult, List.map_map, Function.comp_def, lift] at logical
    obtain ⟨fact, factMember, same⟩ := List.mem_map.mp logical
    rw [← same, pair_fixed _ _ (theoremPayload_fixed _ _) assignment]
    apply meaning_theorem initial policy contexts entry.after fact licensedAfter
    rw [← contextSame]
    exact licensedOutput.2.2 fact factMember

theorem output_valid {O : Type*} [DecidableEq O]
    (initial : TheoryContext) (policy : AxiomPolicy) [DecidablePred policy] (contexts : Nat → TheoryContext)
    (entries : Nat → Option (Entry contexts)) (source : Source) (inputs : Inputs)
    {actual : RuleInstance Value} (computed : activate policy contexts entries source inputs = some actual)
    (label : O → Value) {before : Configuration Value O} {picked : Selection O}
    (qualified : picked.Valid locatedAction label actual before)
    (assignment : ABTProtectedParameters.Assignment InferenceSchemaActivation.Head 0)
    (solved : locatedAction.Models assignment (picked.problem label actual before))
    (incoming : ∀ occurrence ∈ picked.read, Meaning initial policy contexts (locatedAction.apply assignment (label occurrence))) :
    ∀ occurrence ∈ picked.made, Meaning initial policy contexts (locatedAction.apply assignment (label occurrence)) := by
  cases source with
  | inl source =>
      cases inputs with
      | inl cache => exact command_valid initial policy contexts entries source cache computed label qualified assignment solved incoming
      | inr data => simp [activate] at computed
  | inr operation =>
      cases operation with
      | false =>
          cases inputs with
          | inl cache => simp [activate] at computed
          | inr data =>
              cases data with
              | inr parameters => simp [activate] at computed
              | inl parameters =>
                  obtain ⟨old, new, fact⟩ := parameters
                  have same : weakeningRule old new fact = actual := Option.some.inj computed
                  subst actual
                  exact weakening_valid initial policy contexts old new fact label qualified assignment solved incoming
      | true =>
          cases inputs with
          | inl cache => simp [activate] at computed
          | inr data =>
              cases data with
              | inl parameters => simp [activate] at computed
              | inr parameters =>
                  obtain ⟨first, middle, last⟩ := parameters
                  have same : compositionRule first middle last = actual := Option.some.inj computed
                  subst actual
                  exact composition_valid initial policy contexts first middle last label qualified assignment solved incoming

end Mettapedia.Logic.TierZero.Adequacy.HOLLightLicensedSemantics
