import Mettapedia.OSLF.Syntax.DeterministicGSOSFiniteActions

/-!
# Actual laws from independently authored finite-premise rules

An overlapping firing set must have one complete typed target readout.
Matching positive premises give an actual inclusion of the finite rule's
names into the full available-name family. Selecting any firing rule then
constructs a complete guarded schema and a natural law. Injectivity of
typed free-tree relabeling proves independence of that selection, exact
denotation and uniqueness of the law. Indexed authored occurrences remain
available independently of the set of rule readouts.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.DeterministicGSOS

open CategoryTheory Mettapedia.TypeTheory

universe u

variable {S : Signature.{u}} (Actions : S.Srt → Type u)

/-- Partially recover a typed name in a smaller availability family. This
does not assume that different argument positions have different sorts. -/
def restrictVariable {sort : S.Srt} {operator : S.Operator sort}
    (first second : Guard Actions operator) {index : S.Srt}
    (name : RuleVariable Actions operator second index) :
    Option (RuleVariable Actions operator first index) :=
  match name with
  | .original position => some (.original position)
  | .derivative address _ =>
      if available : first address = true then some (.derivative address available) else none

theorem restrictVariable_inclusion {sort : S.Srt} {operator : S.Operator sort}
    {first second : Guard Actions operator}
    (enabled : ∀ address, first address = true → second address = true)
    (base : PUnit.{u + 1}) (index : S.Srt)
    (name : RuleVariable Actions operator first index) :
    restrictVariable Actions first second (variableInclusion Actions enabled base index name) = some name := by
  cases name with
  | original position => rfl
  | derivative address present => simp [restrictVariable, variableInclusion, present]

/-- Relabeling available typed names is injective, including their positions. -/
theorem variableInclusion_injective {sort : S.Srt} {operator : S.Operator sort}
    {first second : Guard Actions operator}
    (enabled : ∀ address, first address = true → second address = true)
    (base : PUnit.{u + 1}) (index : S.Srt) :
    Function.Injective (variableInclusion Actions enabled base index) := by
  intro earlier later same
  have recovered := congrArg (restrictVariable Actions first second) same
  rw [restrictVariable_inclusion, restrictVariable_inclusion] at recovered
  exact Option.some.inj recovered

/-- The universal readout remembers every name and the complete constructor tree. -/
theorem universalRename_injective {sort : S.Srt} (operator : S.Operator sort)
    (guard : Guard Actions operator) :
    Function.Injective (S.rename (universalInclusion Actions operator guard) (sort := sort)) :=
  IndexedPolynomial.Free.map_injective S.polynomial _
    (variableInclusion_injective Actions (fun _ _ => rfl)) PUnit.unit sort

namespace FiniteRule

variable {Actions}

/-- Every positive finite premise supplies its named derivative in the full guard. -/
theorem matched_enabled {sort : S.Srt} {operator : S.Operator sort}
    (rule : FiniteRule Actions operator) (guard : Guard Actions operator)
    (matching : rule.Matches guard) (address : Address Actions operator)
    (enabled : observedGuard Actions rule.observed rule.pattern address = true) :
    guard address = true := by
  classical
  by_cases present : address ∈ rule.observed
  · exact (matching address present).trans
      (by simpa only [observedGuard, dif_pos present] using enabled)
  · simp [observedGuard, present] at enabled

/-- Interpret a finite rule's positive-variable family at a matching complete guard. -/
noncomputable def matchedInclusion {sort : S.Srt} {operator : S.Operator sort}
    (rule : FiniteRule Actions operator) (guard : Guard Actions operator)
    (matching : rule.Matches guard) :
    ruleVariables Actions operator (observedGuard Actions rule.observed rule.pattern) ⟶
      ruleVariables Actions operator guard :=
  variableInclusion Actions (rule.matched_enabled guard matching)

/-- Both routes preserve the exact original and derivative names. -/
theorem matchedInclusion_universal {sort : S.Srt} {operator : S.Operator sort}
    (rule : FiniteRule Actions operator) (guard : Guard Actions operator)
    (matching : rule.Matches guard) :
    rule.matchedInclusion guard matching ≫ universalInclusion Actions operator guard =
      universalInclusion Actions operator (observedGuard Actions rule.observed rule.pattern) := by
  funext base index
  apply ConcreteCategory.hom_ext
  intro name
  cases name <;> rfl

/-- The matched target has the independently authored complete universal readout. -/
theorem matched_target_readout {sort : S.Srt} {operator : S.Operator sort}
    (rule : FiniteRule Actions operator) (guard : Guard Actions operator)
    (matching : rule.Matches guard) :
    S.rename (universalInclusion Actions operator guard)
      (S.rename (rule.matchedInclusion guard matching) rule.target) = rule.readout := by
  have composition := IndexedPolynomial.Free.map_comp S.polynomial
    (fun base index => rule.matchedInclusion guard matching base index)
    (fun base index => universalInclusion Actions operator guard base index) rule.target
  change S.rename (universalInclusion Actions operator guard)
      (S.rename (rule.matchedInclusion guard matching) rule.target) =
    S.rename (rule.matchedInclusion guard matching ≫ universalInclusion Actions operator guard)
      rule.target at composition
  exact composition.trans
    (congrArg (fun mapping => S.rename mapping rule.target)
      (rule.matchedInclusion_universal guard matching))

end FiniteRule

namespace FinitePresentation

/-- A deterministic format condition on independently authored firing clauses.
No desired natural law or denotation witness is supplied. -/
def Consistent (presentation : FinitePresentation Actions) : Prop :=
  ∀ sort (operator : S.Operator sort) action guard
    (first second : FiniteRule Actions operator),
      first ∈ presentation sort operator action → first.Matches guard →
      second ∈ presentation sort operator action → second.Matches guard →
      first.readout = second.readout

/-- Choose a firing finite clause and interpret its actual typed target. -/
noncomputable def toSchemas (presentation : FinitePresentation Actions) : GuardedSchemas Actions := by
  classical
  exact fun sort operator guard action =>
    if firing : ∃ rule ∈ presentation sort operator action, rule.Matches guard then
      some (S.rename (firing.choose.matchedInclusion guard firing.choose_spec.2) firing.choose.target)
    else none

/-- Exact denotation is earned from the local overlapping-clause consistency. -/
theorem toSchemas_denotes (presentation : FinitePresentation Actions)
    (consistent : Consistent Actions presentation) :
    Denotes Actions presentation (toSchemas Actions presentation) := by
  classical
  intro sort operator action guard target
  by_cases firing : ∃ rule ∈ presentation sort operator action, rule.Matches guard
  · have computed : universalReadout Actions (toSchemas Actions presentation) operator guard action =
        some firing.choose.readout := by
      simp only [universalReadout, toSchemas, dif_pos firing, Option.map_some]
      exact congrArg some (firing.choose.matched_target_readout guard firing.choose_spec.2)
    rw [computed, Option.some.injEq]
    constructor
    · intro same
      exact ⟨firing.choose, firing.choose_spec.1, firing.choose_spec.2, same⟩
    · rintro ⟨rule, member, matching, readout⟩
      exact (consistent sort operator action guard firing.choose rule
        firing.choose_spec.1 firing.choose_spec.2 member matching).trans readout
  · simp only [universalReadout, toSchemas, dif_neg firing, Option.map_none]
    constructor
    · intro impossible
      cases impossible
    · rintro ⟨rule, member, matching, _⟩
      exact False.elim (firing ⟨rule, member, matching⟩)

/-- The constructed schema selects the exact target of any supplied firing clause. -/
theorem toSchemas_firing (presentation : FinitePresentation Actions)
    (consistent : Consistent Actions presentation)
    {sort : S.Srt} {operator : S.Operator sort} (action : Actions sort)
    (guard : Guard Actions operator) (rule : FiniteRule Actions operator)
    (member : rule ∈ presentation sort operator action) (matching : rule.Matches guard) :
    toSchemas Actions presentation sort operator guard action =
      some (S.rename (rule.matchedInclusion guard matching) rule.target) := by
  apply Option.map_injective (universalRename_injective Actions operator guard)
  change universalReadout Actions (toSchemas Actions presentation) operator guard action = _
  exact ((toSchemas_denotes Actions presentation consistent sort operator action guard rule.readout).mpr
    ⟨rule, member, matching, rfl⟩).trans
      (congrArg some (rule.matched_target_readout guard matching).symm)

/-- Instantiate the selected firing clauses as a real natural law. Consistency
is needed for exact denotation of all clauses, proved below. -/
noncomputable def toLaw (presentation : FinitePresentation Actions) : Law S Actions :=
  DeterministicGSOS.toLaw Actions (toSchemas Actions presentation)

theorem toLaw_denotes (presentation : FinitePresentation Actions)
    (consistent : Consistent Actions presentation) :
    Denotes Actions presentation (fromLaw Actions (toLaw Actions presentation)) := by
  rw [toLaw, fromLaw_toLaw]
  exact toSchemas_denotes Actions presentation consistent

/-- Exact denotation forces the independent overlapping-clause condition. -/
theorem consistent_of_denotes {presentation : FinitePresentation Actions} {rules : GuardedSchemas Actions}
    (denotes : Denotes Actions presentation rules) : Consistent Actions presentation := by
  intro sort operator action guard first second firstMember firstMatches secondMember secondMatches
  have firstRead := (denotes sort operator action guard first.readout).mpr
    ⟨first, firstMember, firstMatches, rfl⟩
  have secondRead := (denotes sort operator action guard second.readout).mpr
    ⟨second, secondMember, secondMatches, rfl⟩
  exact Option.some.inj (firstRead.symm.trans secondRead)

/-- Universal-name injectivity makes the guarded presentation unique. -/
theorem schemas_unique {presentation : FinitePresentation Actions} {first second : GuardedSchemas Actions}
    (firstDenotes : Denotes Actions presentation first) (secondDenotes : Denotes Actions presentation second) :
    first = second := by
  funext sort operator guard action
  apply Option.map_injective (universalRename_injective Actions operator guard)
  change universalReadout Actions first operator guard action = universalReadout Actions second operator guard action
  cases firstRead : universalReadout Actions first operator guard action with
  | none =>
      cases secondRead : universalReadout Actions second operator guard action with
      | none => rfl
      | some target =>
          have firing := (secondDenotes sort operator action guard target).mp secondRead
          have impossible := (firstDenotes sort operator action guard target).mpr firing
          rw [firstRead] at impossible
          cases impossible
  | some target =>
      exact ((secondDenotes sort operator action guard target).mpr
        ((firstDenotes sort operator action guard target).mp firstRead)).symm

/-- Any law denoting the actual authored format is the independently constructed law. -/
theorem law_unique (presentation : FinitePresentation Actions)
    (consistent : Consistent Actions presentation) (candidate : Law S Actions)
    (denotes : Denotes Actions presentation (fromLaw Actions candidate)) :
    candidate = toLaw Actions presentation := by
  have recovered := schemas_unique Actions denotes (toSchemas_denotes Actions presentation consistent)
  exact (toLaw_fromLaw Actions candidate).symm.trans
    (congrArg (DeterministicGSOS.toLaw Actions) recovered)

/-- The ordinary finite-premise converse needs exactly deterministic consistency. -/
theorem admits_law_iff_consistent (presentation : FinitePresentation Actions) :
    (∃ candidate : Law S Actions, Denotes Actions presentation (fromLaw Actions candidate)) ↔
      Consistent Actions presentation := by
  constructor
  · rintro ⟨candidate, denotes⟩
    exact consistent_of_denotes Actions denotes
  · intro consistent
    exact ⟨toLaw Actions presentation, toLaw_denotes Actions presentation consistent⟩

/-- Denotational equivalence compares only independently authored successful firings. -/
def Equivalent (first second : FinitePresentation Actions) : Prop :=
  ∀ sort (operator : S.Operator sort) action guard target,
    (∃ rule ∈ first sort operator action, rule.Matches guard ∧ rule.readout = target) ↔
      ∃ rule ∈ second sort operator action, rule.Matches guard ∧ rule.readout = target

/-- Rule-set denotational equivalence is exactly equality of constructed natural laws. -/
theorem equivalent_iff_law_equal (first second : FinitePresentation Actions)
    (firstConsistent : Consistent Actions first) (secondConsistent : Consistent Actions second) :
    Equivalent Actions first second ↔ toLaw Actions first = toLaw Actions second := by
  constructor
  · intro equivalent
    have firstDenotes := toSchemas_denotes Actions first firstConsistent
    have secondDenotes := toSchemas_denotes Actions second secondConsistent
    have transferred : Denotes Actions second (toSchemas Actions first) := by
      intro sort operator action guard target
      exact (firstDenotes sort operator action guard target).trans
        (equivalent sort operator action guard target)
    exact congrArg (DeterministicGSOS.toLaw Actions) (schemas_unique Actions transferred secondDenotes)
  · intro equal sort operator action guard target
    have sameRead :
        universalReadout Actions (fromLaw Actions (toLaw Actions first)) operator guard action = some target ↔
          universalReadout Actions (fromLaw Actions (toLaw Actions second)) operator guard action = some target := by
      rw [equal]
    exact ((toLaw_denotes Actions first firstConsistent sort operator action guard target).symm.trans sameRead).trans
      (toLaw_denotes Actions second secondConsistent sort operator action guard target)

/-- Every independently consistent finite presentation has the earned
finite-observation property of its constructed guarded law. -/
theorem toSchemas_finitely_observed (presentation : FinitePresentation Actions)
    (consistent : Consistent Actions presentation) :
    FiniteSuccessfulObservation Actions (toSchemas Actions presentation) :=
  (toSchemas_denotes Actions presentation consistent).finiteSuccessfulObservation Actions

/-- Reconstructing the finite rules preserves their denotation, rather than
their redundant authored clause identities. -/
theorem presentation_roundtrip (presentation : FinitePresentation Actions)
    (consistent : Consistent Actions presentation) :
    Equivalent Actions presentation (soundFinitePresentation Actions (toSchemas Actions presentation)) := by
  intro sort operator action guard target
  exact (toSchemas_denotes Actions presentation consistent sort operator action guard target).symm.trans
    (finiteSuccessfulObservation_denotes Actions
      (toSchemas_finitely_observed Actions presentation consistent) sort operator action guard target)

/-- A finitely observed natural law is recovered from its reconstructed
ordinary finite-premise presentation by the independent rule constructor. -/
theorem law_roundtrip (candidate : Law S Actions)
    (finite : FiniteSuccessfulObservation Actions (fromLaw Actions candidate)) :
    toLaw Actions (soundFinitePresentation Actions (fromLaw Actions candidate)) = candidate := by
  have denotes := finiteSuccessfulObservation_denotes Actions finite
  exact (law_unique Actions _ (consistent_of_denotes Actions denotes) candidate denotes).symm

end FinitePresentation

/-- An independently indexed authored specification can retain duplicate clauses. -/
structure AuthoredFinitePresentation where
  Origin : (sort : S.Srt) → S.Operator sort → Actions sort → Type u
  rule : ∀ sort operator action, Origin sort operator action → FiniteRule Actions operator

namespace AuthoredFinitePresentation

variable {Actions}

/-- Forgetting clause identifiers exposes only the underlying rule set. -/
def readoutSet (presentation : AuthoredFinitePresentation Actions) : FinitePresentation Actions :=
  fun sort operator action => Set.range (presentation.rule sort operator action)

/-- An actual firing retains its exact authored origin and all matched premises. -/
abbrev Firing (presentation : AuthoredFinitePresentation Actions) {sort : S.Srt}
    (operator : S.Operator sort) (action : Actions sort) (guard : Guard Actions operator) :=
  { origin : presentation.Origin sort operator action //
      (presentation.rule sort operator action origin).Matches guard }

/-- Read the complete typed target while the separate firing value retains
its authored origin. Duplicate clauses can have the same term readout. -/
noncomputable def Firing.readout {presentation : AuthoredFinitePresentation Actions}
    {sort : S.Srt} {operator : S.Operator sort} {action : Actions sort} {guard : Guard Actions operator}
    (firing : presentation.Firing operator action guard) : S.Term (universalVariables Actions operator) sort :=
  (presentation.rule sort operator action firing.val).readout

/-- Instantiate the selected authored firing clauses. The denotation theorem
below separately uses local target consistency. -/
noncomputable def toLaw (presentation : AuthoredFinitePresentation Actions) : Law S Actions :=
  FinitePresentation.toLaw Actions presentation.readoutSet

theorem firing_readout {presentation : AuthoredFinitePresentation Actions}
    (consistent : FinitePresentation.Consistent Actions presentation.readoutSet)
    {sort : S.Srt} {operator : S.Operator sort} {action : Actions sort} {guard : Guard Actions operator}
    (firing : presentation.Firing operator action guard) :
    universalReadout Actions (fromLaw Actions presentation.toLaw) operator guard action = some firing.readout :=
  (FinitePresentation.toLaw_denotes Actions presentation.readoutSet consistent sort operator action guard
    firing.readout).mpr ⟨presentation.rule sort operator action firing.val,
      ⟨firing.val, rfl⟩, firing.property, rfl⟩

end AuthoredFinitePresentation

end Mettapedia.OSLF.DeterministicGSOS
