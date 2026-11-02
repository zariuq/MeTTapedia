import Mettapedia.OSLF.NativeTypes.GeneratedLogic.RhoModelAgreement

/-!
# The normalized ρ profile, read at the front door

The normalized ρ profile agrees with the reference structure of ρ's model language on the class of ρ's carrier
(`RhoModel.agreement`). So it has a faithful reading there (`faithful`), its observation `Done` the formula `is {}`.

- **Canonical forms for the front door** (`forms`): the profile's normal form, on the closed object terms whose
  normal form is in ρ's carrier, which is the class of the carrier (`domain_iff`).
- **Coherence at fuel one**: a normal form's bag has no bag among its members (`form_members`), so no rule fires
  inside a member there, and every step from an equivalent of a canonical state is matched, up to normal form, by a
  COMM at the root of the state itself (`coherent`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.RhoModel

open Mettapedia.OSLF.MeTTaIL Syntax Match
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep (StepAt PremisesAt rewriteAt mem_rewriteAt_iff_stepAt)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Instances.Normalized
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical (HashSetFree)

variable (relEnv : RelationEnv)

/-! ## The reading -/

/-- The observation `Done` tests for the empty parallel process. -/
theorem done_tests : NormalizedReading.Tests RhoProfile.profile ⟨0, by decide⟩ RhoProfile.done where
  observe pattern := by
    show (pattern == RhoProfile.done) = true ↔ pattern = RhoProfile.done
    exact beq_iff_eq
  admitted := checkOpenPatternWellSorted_sound (by decide +kernel)
  normal := by
    change CanonicalBags.lawNormal (Complete.Normalized.laws plan) (QuoteDrop.normal presentation RhoProfile.done) = _
    have quoteDrops : QuoteDrop.normal presentation RhoProfile.done = RhoProfile.done := by decide +kernel
    rw [Complete.RhoPresented.laws_eq, quoteDrops]
    simp [CanonicalBags.lawNormal, CanonicalBags.canon, CollectionLaws.normalize, RhoProfile.done,
      CanonicalBags.arrange_bag, PatternLexOrder.sortLex]

theorem done_carrier : carrier RhoProfile.done = true := by decide +kernel

/-- **The normalized ρ profile's faithful reading at the front door**, on the class of ρ's carrier. -/
def faithful : Embeddings.Faithful RhoProfile.profile.driver relEnv language
    (fun leaf : RhoProfile.profile.Leaf => LocalReading.pairVariable leaf true)
    (fun leaf : RhoProfile.profile.Leaf => LocalReading.pairVariable leaf false) RhoModel.reading :=
  NormalizedReading.reading RhoProfile.profile relEnv language RhoModel.reading (agreement relEnv)
    fun _ => some RhoProfile.done


/-! ## Normal forms have no bag among a bag's members -/

/-- A parallel composition, with any tail. -/
def IsBag (pattern : Pattern) : Prop := ∃ items rest, pattern = .collection .hashBag items rest

abbrev bagLaw : CollectionLaws.Laws := ⟨.hashBag, some "PZero"⟩

theorem normalize_collection (kind : CollType) (elements : List Pattern) (rest : Option String) :
    CollectionLaws.normalize laws (.collection kind elements rest) =
      .collection kind (if kind = .hashBag then (elements.map (CollectionLaws.normalize laws)).flatMap
        (CollectionLaws.splice bagLaw) else elements.map (CollectionLaws.normalize laws)) rest := by
  rw [CollectionLaws.normalize, show laws = [bagLaw] from Complete.RhoPresented.laws_eq]
  cases kind <;> rfl

/-- Normalization keeps a term's head: only a bag with a tail normalizes to one. -/
theorem normalize_bag_inv {pattern : Pattern} {items : List Pattern} {rest : Option String}
    (normalized : CollectionLaws.normalize laws pattern = .collection .hashBag items rest) :
    ∃ elements, pattern = .collection .hashBag elements rest := by
  cases pattern with
  | collection kind elements tail =>
    rw [normalize_collection] at normalized
    simp only [Pattern.collection.injEq] at normalized
    obtain ⟨rfl, _, rfl⟩ := normalized
    exact ⟨elements, rfl⟩
  | _ => simp [CollectionLaws.normalize] at normalized

theorem splice_cases {value member : Pattern} (found : member ∈ CollectionLaws.splice bagLaw value) :
    (∃ items, value = .collection .hashBag items none ∧ member ∈ items) ∨
      (member = value ∧ ∀ items, value ≠ .collection .hashBag items none) := by
  cases value with
  | collection kind items tail =>
    cases tail with
    | none =>
      by_cases bagged : kind = .hashBag
      · subst bagged
        exact .inl ⟨items, rfl, by simpa [CollectionLaws.splice] using found⟩
      · simp [CollectionLaws.splice, bagged] at found
        exact .inr ⟨found, fun _ same => bagged (Pattern.collection.inj same).1⟩
    | some name =>
      simp [CollectionLaws.splice] at found
      exact .inr ⟨found, fun _ same => by cases same⟩
  | apply label arguments =>
    cases arguments with
    | nil =>
      simp only [CollectionLaws.splice] at found
      split at found
      · cases found
      · exact .inr ⟨List.mem_singleton.mp found, fun _ same => by cases same⟩
    | cons => exact .inr ⟨List.mem_singleton.mp found, fun _ same => by cases same⟩
  | _ => exact .inr ⟨List.mem_singleton.mp found, fun _ same => by cases same⟩

/-- **A normalized bag of an object term has no bag among its members.** -/
theorem normalize_members : ∀ (pattern : Pattern), isObjectPattern pattern = true → ∀ {items : List Pattern},
    CollectionLaws.normalize laws pattern = .collection .hashBag items none → ∀ member ∈ items, ¬ IsBag member := by
  intro pattern
  induction pattern using Pattern.inductionOn with
  | hcollection kind elements rest ih =>
    intro object items normalized member found
    rw [normalize_collection] at normalized
    simp only [Pattern.collection.injEq] at normalized
    obtain ⟨rfl, itemsEq, rfl⟩ := normalized
    obtain ⟨_, members⟩ := object_collection_iff.mp object
    simp only [if_true] at itemsEq
    subst itemsEq
    obtain ⟨element, elementFound, spliced⟩ := List.mem_flatMap.mp found
    obtain ⟨original, originalFound, rfl⟩ := List.mem_map.mp elementFound
    rcases splice_cases spliced with ⟨inner, innerEq, innerFound⟩ | ⟨rfl, notBag⟩
    · exact ih original originalFound (members original originalFound) innerEq member innerFound
    · rintro ⟨bagItems, tail, bagEq⟩
      obtain ⟨originalItems, rfl⟩ := normalize_bag_inv bagEq
      have originalObject := members _ originalFound
      have tailNone := (object_collection_iff.mp originalObject).1
      subst tailNone
      exact notBag bagItems bagEq
  | _ => intro _ _ normalized; simp [CollectionLaws.normalize] at normalized

theorem canon_bag_inv {pattern : Pattern} {items : List Pattern} {rest : Option String}
    (ordered : CanonicalBags.canon pattern = .collection .hashBag items rest) :
    ∃ elements, pattern = .collection .hashBag elements rest ∧
      items = CanonicalBags.arrange .hashBag (elements.map CanonicalBags.canon) := by
  cases pattern with
  | collection kind elements tail =>
    simp only [CanonicalBags.canon, Pattern.collection.injEq] at ordered
    obtain ⟨rfl, rfl, rfl⟩ := ordered
    exact ⟨elements, rfl, rfl⟩
  | _ => simp [CanonicalBags.canon] at ordered

theorem canon_not_bag {pattern : Pattern} (notBag : ¬ IsBag pattern) : ¬ IsBag (CanonicalBags.canon pattern) := by
  rintro ⟨items, rest, ordered⟩
  obtain ⟨elements, rfl, _⟩ := canon_bag_inv ordered
  exact notBag ⟨elements, rest, rfl⟩

/-- **A normal form's bag has no bag among its members.** -/
theorem form_members {pattern : Pattern} (object : isObjectPattern pattern = true) {items : List Pattern}
    (normal : RhoProfile.form pattern = .collection .hashBag items none) : ∀ member ∈ items, ¬ IsBag member := by
  change CanonicalBags.canon (CollectionLaws.normalize laws (QuoteDrop.normal presentation pattern)) = _ at normal
  obtain ⟨elements, normalized, rfl⟩ := canon_bag_inv normal
  have quoteDropObject : isObjectPattern (QuoteDrop.normal presentation pattern) = true :=
    (QuoteDrop.QuoteDropForward.objectPattern_eq (QuoteDrop.quoteDrop_forward (declaration := presentation) pattern)) ▸
      object
  intro member found
  rw [CanonicalBags.arrange_mem] at found
  obtain ⟨original, originalFound, rfl⟩ := List.mem_map.mp found
  exact canon_not_bag (normalize_members _ quoteDropObject normalized original originalFound)

/-! ## At a bag without bag members, every step is a COMM at the root -/

theorem step_bag {fuel : ℕ} {source target : Pattern} (step : Step fuel source target) : IsBag source := by
  cases step with
  | rule member matched _ _ =>
    have admitted : carrier source = true := by
      by_contra outside
      simp only [interpretation, outside, if_false] at matched
      cases matched
    change _ ∈ (if carrier source then _ else []) at matched
    rw [if_pos admitted] at matched
    rw [rewrites_eq] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · obtain ⟨elements, rest, _, _, _, _, _, _, _, _, rfl, _⟩ := comm_shape matched
      exact ⟨elements, rest, rfl⟩
    · obtain ⟨elements, rest, _, _, rfl, _⟩ := parCong_shape matched
      exact ⟨elements, rest, rfl⟩

theorem step_root {fuel : ℕ} {elements : List Pattern} {target : Pattern}
    (step : Step fuel (.collection .hashBag elements none) target) (flat : ∀ member ∈ elements, ¬ IsBag member)
    (more : ℕ) : Step (more + 1) (.collection .hashBag elements none) target := by
  cases step with
  | rule member matched premises applied =>
    have memberCopy := member
    rw [rewrites_eq] at memberCopy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at memberCopy
    rcases memberCopy with rfl | rfl
    · change PremisesAt _ _ _ _ _ [] _ at premises
      cases premises
      exact StepAt.rule member matched (PremisesAt.nil _) applied
    · have admitted : carrier (.collection .hashBag elements none) = true := by
        by_contra outside
        simp only [interpretation, outside, if_false] at matched
        cases matched
      change _ ∈ (if carrier (.collection .hashBag elements none) then _ else []) at matched
      rw [if_pos admitted] at matched
      obtain ⟨elements', rest', index, bound, sameSource, rfl⟩ := parCong_shape matched
      simp only [Pattern.collection.injEq] at sameSource
      obtain ⟨_, rfl, rfl⟩ := sameSource
      change PremisesAt _ _ _ _ _ [.congruence (.fvar "S") (.fvar "T")] _ at premises
      cases premises with
      | cons first rest =>
        cases first with
        | congruence recursive _ _ =>
          simp only [applyBindings, List.find?] at recursive
          simp at recursive
          exact absurd (step_bag recursive) (flat _ (List.getElem_mem bound))


/-! ## The normal form, by structural recursion -/

mutual
  /-- The collection laws' normal form, by structural recursion, so that the kernel evaluates it. -/
  def normalizeK : Pattern → Pattern
    | .bvar index => .bvar index
    | .fvar name => .fvar name
    | .apply label arguments => .apply label (normalizeKList arguments)
    | .lambda binder body => .lambda binder (normalizeK body)
    | .multiLambda arity binders body => .multiLambda arity binders (normalizeK body)
    | .subst body replacement => .subst (normalizeK body) (normalizeK replacement)
    | .collection kind elements rest =>
      .collection kind (if kind = .hashBag then (normalizeKList elements).flatMap (CollectionLaws.splice bagLaw)
        else normalizeKList elements) rest
  termination_by structural pattern => pattern

  def normalizeKList : List Pattern → List Pattern
    | [] => []
    | pattern :: patterns => normalizeK pattern :: normalizeKList patterns
  termination_by structural patterns => patterns
end

mutual
  /-- The canonical order of bags, by structural recursion. -/
  def canonK : Pattern → Pattern
    | .bvar index => .bvar index
    | .fvar name => .fvar name
    | .apply label arguments => .apply label (canonKList arguments)
    | .lambda binder body => .lambda binder (canonK body)
    | .multiLambda arity binders body => .multiLambda arity binders (canonK body)
    | .subst body replacement => .subst (canonK body) (canonK replacement)
    | .collection kind elements rest => .collection kind (CanonicalBags.arrange kind (canonKList elements)) rest
  termination_by structural pattern => pattern

  def canonKList : List Pattern → List Pattern
    | [] => []
    | pattern :: patterns => canonK pattern :: canonKList patterns
  termination_by structural patterns => patterns
end

theorem normalizeKList_eq {patterns : List Pattern}
    (each : ∀ pattern ∈ patterns, normalizeK pattern = CollectionLaws.normalize laws pattern) :
    normalizeKList patterns = patterns.map (CollectionLaws.normalize laws) := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns ih =>
    rw [normalizeKList, each pattern List.mem_cons_self,
      ih fun other member => each other (List.mem_cons_of_mem _ member), List.map_cons]

theorem normalizeK_eq (pattern : Pattern) : normalizeK pattern = CollectionLaws.normalize laws pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar => rw [normalizeK, CollectionLaws.normalize]
  | hfvar => rw [normalizeK, CollectionLaws.normalize]
  | happly label arguments ih => rw [normalizeK, CollectionLaws.normalize, normalizeKList_eq ih]
  | hlambda _ _ ih => rw [normalizeK, CollectionLaws.normalize, ih]
  | hmultiLambda _ _ _ ih => rw [normalizeK, CollectionLaws.normalize, ih]
  | hsubst _ _ bodyIh replacementIh => rw [normalizeK, CollectionLaws.normalize, bodyIh, replacementIh]
  | hcollection kind elements rest ih => rw [normalizeK, normalize_collection, normalizeKList_eq ih]

theorem canonKList_eq {patterns : List Pattern} (each : ∀ pattern ∈ patterns, canonK pattern = CanonicalBags.canon pattern) :
    canonKList patterns = patterns.map CanonicalBags.canon := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns ih =>
    rw [canonKList, each pattern List.mem_cons_self,
      ih fun other member => each other (List.mem_cons_of_mem _ member), List.map_cons]

theorem canonK_eq (pattern : Pattern) : canonK pattern = CanonicalBags.canon pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar => rw [canonK, CanonicalBags.canon]
  | hfvar => rw [canonK, CanonicalBags.canon]
  | happly label arguments ih => rw [canonK, CanonicalBags.canon, canonKList_eq ih]
  | hlambda _ _ ih => rw [canonK, CanonicalBags.canon, ih]
  | hmultiLambda _ _ _ ih => rw [canonK, CanonicalBags.canon, ih]
  | hsubst _ _ bodyIh replacementIh => rw [canonK, CanonicalBags.canon, bodyIh, replacementIh]
  | hcollection kind elements rest ih => rw [canonK, CanonicalBags.canon, canonKList_eq ih]

/-- **The profile's normal form, computed by structural recursion.** -/
def formK (pattern : Pattern) : Pattern := canonK (normalizeK (QuoteDrop.normal presentation pattern))

theorem formK_eq (pattern : Pattern) : formK pattern = RhoProfile.form pattern := by
  rw [formK, canonK_eq, normalizeK_eq]
  rfl

theorem formK_fun : formK = RhoProfile.form := funext formK_eq

/-! ## Canonical forms -/

/-- **The domain of the canonical forms**: closed object terms whose normal form is in ρ's carrier. -/
def domain (term : Pattern) : Bool :=
  term.isWellScopedAt 0 && isObjectPattern term && carrier (formK term)

/-- A property every move keeps, both ways, is kept along the model's equality. -/
theorem modelEquiv_keeps {P : Pattern → Prop} (kept : ∀ {first second}, Move first second → (P first ↔ P second))
    {first second : Pattern} (equal : ModelEquiv first second) : P first ↔ P second := by
  have moves := modelEquiv_iff.mp equal
  clear equal
  induction moves with
  | rel _ _ move => exact kept move
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ first second => exact first.trans second

theorem modelEquiv_isState {first second : Pattern} (equal : ModelEquiv first second) :
    IsState first ↔ IsState second :=
  modelEquiv_keeps (P := IsState) (fun move => by unfold IsState IsObject; rw [move.scoped_eq 0, move.object_eq]) equal

theorem modelEquiv_pure {first second : Pattern} (equal : ModelEquiv first second) :
    HashSetFree first ↔ HashSetFree second :=
  modelEquiv_keeps (P := HashSetFree) (fun move => move.pure_iff) equal

theorem modelEquiv_scoped {first second : Pattern} (equal : ModelEquiv first second) :
    first.isWellScopedAt 0 = true ↔ second.isWellScopedAt 0 = true :=
  modelEquiv_keeps (P := fun term => term.isWellScopedAt 0 = true) (fun move => by rw [move.scoped_eq 0]) equal

theorem domain_iff {term : Pattern} :
    domain term = true ↔ IsState term ∧ carrier (RhoProfile.form term) = true := by
  simp only [domain, Bool.and_eq_true, IsState, IsObject, formK_eq]

theorem form_form (term : Pattern) : RhoProfile.form (RhoProfile.form term) = RhoProfile.form term :=
  form_eq (.symm _ _ (form_modelEquiv term))

theorem domain_pure {term : Pattern} (inside : domain term = true) : HashSetFree term :=
  (modelEquiv_pure (form_modelEquiv term)).mpr (carrier_state (domain_iff.mp inside).2).2

/-- **The domain is the class of ρ's carrier.** -/
theorem domain_region {term : Pattern} : domain term = true ↔ Region term := by
  constructor
  · intro inside
    obtain ⟨state, admitted⟩ := domain_iff.mp inside
    exact ⟨state, domain_pure inside, RhoProfile.form term, admitted, .symm _ _ (form_modelEquiv term)⟩
  · rintro ⟨state, _, origin, admitted, equal⟩
    refine domain_iff.mpr ⟨state, ?_⟩
    rw [← form_eq equal]
    exact form_carrier admitted

/-- **The normal form gives canonical forms on the class of ρ's carrier.** -/
theorem canonical_form : Canonical relEnv language RhoProfile.form domain RhoModel.reading where
  object inside := (domain_iff.mp inside).1.2
  admitted_canon inside := by
    obtain ⟨_, admitted⟩ := domain_iff.mp inside
    exact domain_iff.mpr ⟨(carrier_state admitted).1, by rw [form_form]; exact admitted⟩
  invariant inside equivalent := by
    obtain ⟨state, admitted⟩ := domain_iff.mp inside
    have equal := modelEquiv_of_objectEquivalent equivalent
    exact domain_iff.mpr ⟨(modelEquiv_isState equal).mp state, by rw [← form_eq equal]; exact admitted⟩
  stepsAdmitted _ _ _ formInside := by
    obtain ⟨_, admitted⟩ := domain_iff.mp formInside
    rw [form_form] at admitted
    exact domain_iff.mpr ⟨(modelEquiv_isState (form_modelEquiv _)).mpr (carrier_state admitted).1, admitted⟩
  equivalent inside := same_of_modelEquiv (form_modelEquiv _) (domain_iff.mp inside).1.2 (domain_pure inside)
  same _ equivalent := form_eq (modelEquiv_of_objectEquivalent equivalent)
  closed inside := by
    obtain ⟨state, _⟩ := domain_iff.mp inside
    rw [state.1]
    exact (modelEquiv_scoped (form_modelEquiv _)).mp state.1

/-- **Coherence at any fuel**: a step from an equivalent of a canonical state of the domain is matched, up to normal
form, by a COMM at the root of the state, which the stepper lists. -/
theorem coherent_form (fuel : ℕ) :
    CoherentPlain relEnv language (fuel + 1) RhoProfile.form domain List.singleton RhoModel.reading := by
  intro state redex witness contractum _ inside canonState _ before _ valid
  obtain ⟨modelFuel, modelStep⟩ := valid.2
  obtain ⟨receipt, fired, related⟩ := step_receipt modelFuel modelStep
  obtain ⟨next, nextFired, nextRelated⟩ := RhoProfile.primitive_form fired
  have sameForm : RhoProfile.form redex = state :=
    (form_eq (modelEquiv_of_objectEquivalent before)).symm.trans canonState
  rw [sameForm] at nextFired
  obtain ⟨stateState, stateFormAdmitted⟩ := domain_iff.mp inside
  have admitted : carrier state = true := canonState ▸ stateFormAdmitted
  obtain ⟨⟨_, licensed⟩, firing, _, filled, _⟩ := nextFired
  simp only [GeneralPlanEnvironment.environmentWith_empty] at firing
  obtain ⟨listed, listedFuel, listedStep, moved⟩ := licensed_step licensed rfl rfl admitted firing
  rw [← filled] at moved
  obtain ⟨items, rest, rfl⟩ := step_bag listedStep
  have restNone : rest = none := (object_collection_iff.mp stateState.2).1
  subst restNone
  have flat := form_members stateState.2 canonState
  have rooted := step_root listedStep flat fuel
  refine ⟨(.base [], listed), ?_, ?_⟩
  · simp only [listedAt, List.singleton, List.flatMap_cons, List.flatMap_nil, List.append_nil, ruleSteps,
      RhoModel.reading]
    exact List.mem_map.mpr ⟨listed, mem_rewriteAt_iff_stepAt.mpr rooted, rfl⟩
  · exact form_eq (modelEquiv_trans (moves_modelEquiv moved)
      (modelEquiv_trans (.symm _ _ nextRelated) (moves_modelEquiv related)))

theorem canonical : Canonical relEnv language formK domain RhoModel.reading := by
  rw [formK_fun]
  exact canonical_form relEnv

theorem coherent (fuel : ℕ) : CoherentPlain relEnv language (fuel + 1) formK domain List.singleton RhoModel.reading := by
  rw [formK_fun]
  exact coherent_form relEnv fuel

/-- **The canonical forms of ρ's model language**, for the front door, computed by structural recursion. -/
def forms (fuel : ℕ) : CanonicalForms relEnv language (fuel + 1) :=
  .ofPlain (reading := RhoModel.reading) (canonical relEnv) (coherent relEnv fuel)

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.RhoModel
