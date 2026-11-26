import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.FirstOrderEq
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Tensor

/-!
# Conservative extension by resolved occurrence groups

Adding resolved ports to a firing preserves the models of its information.
Admission then requires resource compatibility and exact coverage of the
group under those models. The same argument applies to read and take groups.
An entry retains its occurrence identity and contributes an output block.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.QuantifiedPremise

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled)
open OneFrame (Terms frames ext)

universe uT uS uO

variable {T : Type uT} {S : Type uS} {O : Type uO}

/-- The group either consumes each entry or keeps it available. -/
inductive Mode where
  | take
  | read

/-- An occurrence with its captured entry value and its own output block. -/
structure Entry (O : Type uO) (T : Type uT) where
  occurrence : O
  input : T
  outputs : List T
  deriving DecidableEq, Repr

/-- The selected entries in read order and the allocation for their outputs. -/
structure Group (O : Type uO) (T : Type uT) where
  entries : List (Entry O T)
  made : List O

namespace Group

def outputs (group : Group O T) : List T :=
  group.entries.flatMap Entry.outputs

def takes (group : Group O T) : Mode → List (Entry O T)
  | .take => group.entries
  | .read => []

def reads (group : Group O T) : Mode → List (Entry O T)
  | .take => []
  | .read => group.entries

/-- Instances already settled in the frame need no new schematic variables. -/
def Ground (group : Group O T) (A : SubstitutionAction T S) : Prop :=
  (∀ entry ∈ group.entries, ∀ σ, A.apply σ entry.input = entry.input) ∧
    ∀ out ∈ group.outputs, ∀ σ, A.apply σ out = out

/-- Each selected occurrence carries the claimed label at the entry state. -/
def LabelsAgree (group : Group O T) (s : State (Terms T) O) : Prop :=
  ∀ entry ∈ group.entries, s.label entry.occurrence = entry.input

/-- One instance of the scoped relation per occurrence, with no omitted
occurrence in the entry view. The relation may depend on an outer match. -/
structure Exact (group : Group O T) (s : State (Terms T) O)
    (accepts : O → T → List T → Prop) : Prop where
  distinct : (group.entries.map Entry.occurrence).Nodup
  sound : ∀ entry ∈ group.entries, entry.occurrence ∈ s.present ∧
    s.label entry.occurrence = entry.input ∧ accepts entry.occurrence entry.input entry.outputs
  complete : ∀ o ∈ s.present, (∃ out, accepts o (s.label o) out) →
    o ∈ group.entries.map Entry.occurrence

theorem Exact.labelsAgree {group : Group O T} {s : State (Terms T) O}
    {accepts : O → T → List T → Prop} (exactGroup : group.Exact s accepts) :
    group.LabelsAgree s :=
  fun entry member => (exactGroup.sound entry member).2.1

def extendRule (group : Group O T) (mode : Mode) (base : Rule (Terms T)) : Rule (Terms T) :=
  { base with body := { base.body with
      take := base.body.take ++ (group.takes mode).map Entry.input
      read := base.body.read ++ (group.reads mode).map Entry.input
      produce := base.body.produce ++ group.outputs } }

def extendSelection (group : Group O T) (mode : Mode) (base : Selection O) : Selection O :=
  ⟨base.taken ++ (group.takes mode).map Entry.occurrence,
    base.read ++ (group.reads mode).map Entry.occurrence, base.made ++ group.made⟩

/-- The raw catalog of finite expansions. Exactness is a premise of a
quantified firing, and the raw catalog only supplies its physical rules. -/
def expansions (P : Program (Terms T)) : Program (Terms T) :=
  { rule | ∃ base ∈ P, ∃ (group : Group O T) (mode : Mode), rule = group.extendRule mode base }

variable (A : SubstitutionAction T S) {P : Program (Terms T)}
  {s : State (Terms T) O}

def elaborate (group : Group O T) (mode : Mode) (base : Firing O (ext A) P s.frame) :
    Firing O (ext A) (expansions (O := O) P) s.frame :=
  ⟨group.extendRule mode base.rule, ⟨base.rule, base.member, group, mode, rfl⟩,
    base.ext, base.opening, group.extendSelection mode base.selection, base.seen⟩

private theorem mem_takes {group : Group O T} {mode : Mode} {entry : Entry O T}
    (member : entry ∈ group.takes mode) : entry ∈ group.entries := by
  cases mode with
  | take => exact member
  | read => simp [takes] at member

private theorem mem_reads {group : Group O T} {mode : Mode} {entry : Entry O T}
    (member : entry ∈ group.reads mode) : entry ∈ group.entries := by
  cases mode with
  | take => simp [reads] at member
  | read => exact member

private theorem terms_extend (group : Group O T) (mode : Mode) (base : Rule (Terms T)) (value : T) :
    value ∈ (group.extendRule mode base).terms ↔
      value ∈ base.terms ∨ value ∈ group.entries.map Entry.input ∨ value ∈ group.outputs := by
  cases mode <;>
    simp only [Rule.terms, extendRule, takes, reads, List.map_nil, List.append_nil, List.mem_append] <;>
    tauto

theorem fresh_elaborate_iff (group : Group O T) (mode : Mode) (base : Firing O (ext A) P s.frame)
    (ground : group.Ground A) :
    (group.elaborate A mode base).Fresh (frames A) s ↔ base.Fresh (frames A) s := by
  constructor
  · intro fresh b g h
    obtain ⟨u, original, rule⟩ := fresh b g h
    refine ⟨u, original, fun t member => rule t ((terms_extend group mode base.rule t).mpr (.inl member))⟩
  · intro fresh b g h
    obtain ⟨u, original, rule⟩ := fresh b g h
    refine ⟨u, original, fun t member => ?_⟩
    rcases (terms_extend group mode base.rule t).mp member with atBase | inputs | outputs
    · exact rule t atBase
    · obtain ⟨entry, inside, rfl⟩ := List.mem_map.mp inputs
      show A.E (A.apply u (A.apply base.opening entry.input)) (A.apply h entry.input)
      rw [ground.1 entry inside base.opening, ground.1 entry inside u, ground.1 entry inside h]
      exact A.equivalence.refl _
    · show A.E (A.apply u (A.apply base.opening t)) (A.apply h t)
      rw [ground.2 t outputs base.opening, ground.2 t outputs u, ground.2 t outputs h]
      exact A.equivalence.refl _

theorem opened_elaborate (group : Group O T) (mode : Mode) (base : Firing O (ext A) P s.frame)
    (ground : group.Ground A) :
    (group.elaborate A mode base).opened (frames A) =
      { base.opened (frames A) with
        take := (base.opened (frames A)).take ++ (group.takes mode).map Entry.input
        read := (base.opened (frames A)).read ++ (group.reads mode).map Entry.input
        produce := (base.opened (frames A)).produce ++ group.outputs } := by
  have takeFixed : ∀ t ∈ (group.takes mode).map Entry.input, A.apply base.opening t = t := by
    intro t member
    obtain ⟨entry, inside, rfl⟩ := List.mem_map.mp member
    exact ground.1 entry (mem_takes inside) _
  have readFixed : ∀ t ∈ (group.reads mode).map Entry.input, A.apply base.opening t = t := by
    intro t member
    obtain ⟨entry, inside, rfl⟩ := List.mem_map.mp member
    exact ground.1 entry (mem_reads inside) _
  let openTerm := (frames A).act (a := base.rule.locals) (b := (ext A).target base.ext) base.opening
  have takeEq : ((group.takes mode).map Entry.input).map openTerm =
      (group.takes mode).map Entry.input := JointFirings.map_fixed A _ takeFixed
  have readEq : ((group.reads mode).map Entry.input).map openTerm =
      (group.reads mode).map Entry.input := JointFirings.map_fixed A _ readFixed
  have produceEq : group.outputs.map openTerm = group.outputs :=
    JointFirings.map_fixed A _ (fun out member => ground.2 out member base.opening)
  dsimp only [openTerm] at takeEq readEq produceEq
  simp only [elaborate, extendRule, Firing.opened, RuleInstance.map, List.map_append,
    takeEq, readEq, produceEq]

private theorem extra_models (group : Group O T) (base : Firing O (ext A) P s.frame)
    (labels : group.LabelsAgree s) (σ : S) (entries : List (Entry O T))
    (within : ∀ entry ∈ entries, entry ∈ group.entries) :
    A.Models σ (base.matching (frames A) s (entries.map Entry.input)
      (entries.map Entry.occurrence)) := by
  induction entries with
  | nil => exact A.models_nil σ
  | cons entry rest ih =>
      change A.Models σ ((entry.input, base.row (frames A) s entry.occurrence) ::
        base.matching (frames A) s (rest.map Entry.input) (rest.map Entry.occurrence))
      refine (A.models_cons _ _ _).mpr ⟨?_, ih fun e member => within e (List.mem_cons_of_mem _ member)⟩
      show A.E (A.apply σ entry.input) (A.apply σ (A.apply A.identity (s.label entry.occurrence)))
      rw [A.apply_identity, labels entry (within entry List.mem_cons_self)]
      exact A.equivalence.refl _

theorem models_elaborate_iff (group : Group O T) (mode : Mode) (base : Firing O (ext A) P s.frame)
    (ground : group.Ground A) (labels : group.LabelsAgree s)
    (takeLength : base.rule.body.take.length = base.selection.taken.length)
    (readLength : base.rule.body.read.length = base.selection.read.length) (σ : S) :
    A.Models σ ((group.elaborate A mode base).information (frames A) s) ↔
      A.Models σ (base.information (frames A) s) := by
  have taken : (base.opened (frames A)).take.length = base.selection.taken.length := by
    simpa [Firing.opened, RuleInstance.map] using takeLength
  have read : (base.opened (frames A)).read.length = base.selection.read.length := by
    simpa [Firing.opened, RuleInstance.map] using readLength
  let next := group.elaborate A mode base
  have equations : next.information (frames A) s =
      (frames A).applyStore ((ext A).weaken base.ext) s.knowledge ++
      (base.matching (frames A) s (base.opened (frames A)).take base.selection.taken ++
        base.matching (frames A) s ((group.takes mode).map Entry.input)
          ((group.takes mode).map Entry.occurrence)) ++
      (base.matching (frames A) s (base.opened (frames A)).read base.selection.read ++
        base.matching (frames A) s ((group.reads mode).map Entry.input)
          ((group.reads mode).map Entry.occurrence)) ++
      (base.opened (frames A)).tell := by
    unfold Firing.information
    rw [opened_elaborate A group mode base ground]
    simp only [next, elaborate, extendSelection, Firing.matching]
    rw [List.zipWith_append taken, List.zipWith_append read]
    rfl
  change A.Models σ (next.information (frames A) s) ↔ _
  rw [equations]
  unfold Firing.information
  simp only [SubstitutionAction.models_append,
    extra_models A group base labels σ _ (fun _ member => mem_takes member),
    extra_models A group base labels σ _ (fun _ member => mem_reads member), and_true]

variable [DecidableEq O]

/-- The independent resource checks of the expanded instance. -/
structure Fits (group : Group O T) (mode : Mode) (s : State (Terms T) O)
    (selection : Selection O) : Prop where
  taken : (group.extendSelection mode selection).taken.Nodup
  made : (group.extendSelection mode selection).made.Nodup
  allocation : group.outputs.length = group.made.length
  enabled : Enabled (fun _ : O => ()) s.present ((group.extendSelection mode selection).commit (T := Unit))

private theorem enabled_base (group : Group O T) (mode : Mode) (base : Selection O)
    (enabled : Enabled (fun _ : O => ()) s.present ((group.extendSelection mode base).commit (T := Unit))) :
    Enabled (fun _ : O => ()) s.present (base.commit (T := Unit)) := by
  have takes : base.taken.toFinset ⊆ (group.extendSelection mode base).taken.toFinset :=
    fun _ h => List.mem_toFinset.mpr (List.mem_append_left _ (List.mem_toFinset.mp h))
  have reads : base.read.toFinset ⊆ (group.extendSelection mode base).read.toFinset :=
    fun _ h => List.mem_toFinset.mpr (List.mem_append_left _ (List.mem_toFinset.mp h))
  have makes : base.made.toFinset ⊆ (group.extendSelection mode base).made.toFinset :=
    fun _ h => List.mem_toFinset.mpr (List.mem_append_left _ (List.mem_toFinset.mp h))
  exact ⟨takes.trans enabled.taken_subset, reads.trans enabled.kept_subset,
    Disjoint.mono takes reads enabled.apart, Disjoint.mono_left makes enabled.fresh,
    fun _ inside => (List.not_mem_nil inside).elim⟩

/-- Raw admission consumes and produces the expected resources. The exact
entry relation is a separate premise of a quantified firing. -/
theorem elaborate_admits_iff (group : Group O T) (mode : Mode) (base : Firing O (ext A) P s.frame)
    (ground : group.Ground A) (labels : group.LabelsAgree s)
    (makeLength : base.rule.body.produce.length = base.selection.made.length) :
    (step (frames A) O (ext A) (expansions (O := O) P)).Admits
        (group.elaborate A mode base) ↔
      base.Admits (frames A) s ∧ group.Fits mode s base.selection := by
  change (group.elaborate A mode base).Admits (frames A) s ↔ _
  let next := group.elaborate A mode base
  have guard (b : PUnit) (σ : S) :
      next.Holds (frames A) s (b := b) σ ↔ base.Holds (frames A) s (b := b) σ := Iff.rfl
  constructor
  · rintro ⟨⟨fresh, taken, made, takeLen, readLen, makeLen, seenLen⟩, available, solved, asks⟩
    have takeBase : base.rule.body.take.length = base.selection.taken.length := by
      simp only [elaborate, extendRule, extendSelection, List.length_append, List.length_map] at takeLen
      exact Nat.add_right_cancel takeLen
    have readBase : base.rule.body.read.length = base.selection.read.length := by
      simp only [elaborate, extendRule, extendSelection, List.length_append, List.length_map] at readLen
      exact Nat.add_right_cancel readLen
    have allocation : group.outputs.length = group.made.length := by
      simp only [elaborate, extendRule, extendSelection, List.length_append, makeLength] at makeLen
      exact Nat.add_left_cancel makeLen
    have models := models_elaborate_iff A group mode base ground labels takeBase readBase
    obtain ⟨b, σ, model⟩ := solved
    refine ⟨⟨⟨(fresh_elaborate_iff A group mode base ground).mp fresh,
        (List.nodup_append'.mp taken).1, (List.nodup_append'.mp made).1,
        takeBase, readBase, makeLength, seenLen⟩,
      enabled_base group mode base.selection available, ⟨b, σ, (models σ).mp model⟩,
      fun b' τ model' => (guard b' τ).mp (asks b' τ ((models τ).mpr model'))⟩,
      ⟨taken, made, allocation, available⟩⟩
  · rintro ⟨⟨⟨fresh, _, _, takeLen, readLen, _, seenLen⟩, _, solved, asks⟩, resources⟩
    have models := models_elaborate_iff A group mode base ground labels takeLen readLen
    obtain ⟨b, σ, model⟩ := solved
    refine ⟨⟨(fresh_elaborate_iff A group mode base ground).mpr fresh,
      resources.taken, resources.made, ?_, ?_, ?_, seenLen⟩, resources.enabled,
      ⟨b, σ, (models σ).mpr model⟩, fun b' τ model' => (guard b' τ).mpr (asks b' τ ((models τ).mp model'))⟩
    · simp [elaborate, extendRule, extendSelection, takeLen]
    · simp [elaborate, extendRule, extendSelection, readLen]
    · simp [elaborate, extendRule, extendSelection, makeLength, resources.allocation]

/-- Observe the single publication on occurrence identities and labels.
Output blocks are paired with fresh identities after the base's own outputs. -/
theorem elaborate_publication (group : Group O T) (mode : Mode) (base : Firing O (ext A) P s.frame)
    (ground : group.Ground A)
    (makeLength : base.rule.body.produce.length = base.selection.made.length)
    (admitted : (step (frames A) O (ext A) (expansions (O := O) P)).Admits
      (group.elaborate A mode base)) :
    let next := (group.elaborate A mode base).result (frames A) s
    let selection := group.extendSelection mode base.selection
    next.present = (s.present \ selection.taken.toFinset) ∪ selection.made.toFinset ∧
      (∀ o ∉ selection.made, next.label o = s.label o) ∧
      ∀ entry ∈ (base.selection.made.zip (base.opened (frames A)).produce) ++
        group.made.zip group.outputs, next.label entry.1 = entry.2 := by
  change (group.elaborate A mode base).Admits (frames A) s at admitted
  have shape := admitted.1
  have baseMadeLength :
      base.selection.made.length = (base.opened (frames A)).produce.length := by
    simpa [Firing.opened, RuleInstance.map] using makeLength.symm
  dsimp only
  refine ⟨rfl, fun o notMade => ?_, fun entry member => ?_⟩
  · rw [Firing.result_label_other (X := frames A) (s := s) (group.elaborate A mode base) notMade]
    exact A.apply_identity _
  · apply Firing.result_label_made (X := frames A) (s := s) (group.elaborate A mode base) shape
    rw [opened_elaborate A group mode base ground]
    change entry ∈ (base.selection.made ++ group.made).zip
      ((base.opened (frames A)).produce ++ group.outputs)
    rw [List.zip_append baseMadeLength]
    exact member

end Group

variable [DecidableEq O] (A : SubstitutionAction T S) (P : Program (Terms T))

/-- The relation supplied by an outer firing at one of its settlements. It
decides both inclusion in the scoped group and the outputs of an entry. -/
abbrev ScopedRelation := (s : State (Terms T) O) → Firing O (ext A) P s.frame →
  S → O → T → List T → Prop

/-- Exact quantified firings use the ordinary effect on the expanded rule
catalog. An expansion is eligible only with its underlying rule and a group
that is exact at every model of the base information. -/
def scopedStep (mode : Mode) (relation : ScopedRelation (O := O) A P) :
    Interface.Step (frames A) O (State (Terms T) O)
      (fun s => Firing O (ext A) (Group.expansions (O := O) P) s.frame) :=
  Spaces.restrict (step (frames A) O (ext A) (Group.expansions (O := O) P)).toStep
    fun {s} expanded => ∃ (base : Firing O (ext A) P s.frame) (group : Group O T),
      expanded = group.elaborate A mode base ∧ group.Ground A ∧ group.LabelsAgree s ∧
      base.rule.body.produce.length = base.selection.made.length ∧
      A.Entails (base.information (frames A) s) (fun σ => group.Exact s (relation s base σ))

/-- Both directions of the compilation, for any candidate of the expanded
catalog. Extra bindings acquired by different entries stay separate. -/
theorem scopedStep_admits_iff (mode : Mode) (relation : ScopedRelation (O := O) A P)
    {s : State (Terms T) O} (expanded : Firing O (ext A) (Group.expansions (O := O) P) s.frame) :
    (scopedStep A P mode relation).Admits expanded ↔
      ∃ (base : Firing O (ext A) P s.frame) (group : Group O T),
        expanded = group.elaborate A mode base ∧ group.Ground A ∧ base.Admits (frames A) s ∧
        group.Fits mode s base.selection ∧
        A.Entails (base.information (frames A) s) (fun σ => group.Exact s (relation s base σ)) := by
  constructor
  · rintro ⟨admitted, base, group, rfl, ground, labels, makeLength, exactGroup⟩
    obtain ⟨baseAdmits, fits⟩ := (group.elaborate_admits_iff A mode base ground labels makeLength).mp admitted
    exact ⟨base, group, rfl, ground, baseAdmits, fits, exactGroup⟩
  · rintro ⟨base, group, rfl, ground, baseAdmits, fits, exactGroup⟩
    obtain ⟨_, σ, solved⟩ := baseAdmits.2.2.1
    have labels := (exactGroup σ solved).labelsAgree
    have makeLength := baseAdmits.1.2.2.2.2.2.1
    exact ⟨(group.elaborate_admits_iff A mode base ground labels makeLength).mpr ⟨baseAdmits, fits⟩,
      base, group, rfl, ground, labels, makeLength, exactGroup⟩

#print axioms Group.models_elaborate_iff
#print axioms Group.elaborate_admits_iff
#print axioms Group.elaborate_publication
#print axioms scopedStep_admits_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.QuantifiedPremise

