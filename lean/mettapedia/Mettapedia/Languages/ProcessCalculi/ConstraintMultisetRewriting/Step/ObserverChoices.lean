import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ObserverAbstraction

/-!
# The whole observer: choices, aliases, later export, and which probes it may make

The environment's record is the whole of what it knows: sighted sets, held references (repeated ones
included, since each position is a handle), and the choices it was told. An isomorphism of an escaped
state to itself renames by an automorphism of that whole record (`escapeIso_self_mem`).

* **The correspondence between two executions grows** (`Transport.Escape.traceEquiv_correspondence`):
  the renaming that relates the ends of trace-equivalent runs carries the identities the start's
  record mentions onto themselves, and the identities the end's record mentions onto those of the
  other end. Restricted to what was exported, it is a partial bijection between the executions that
  keeps its old part and extends to names exported later (`Record.support_rename`).
* **Recording choices** (`choiceEscape`): a firing makes the environment record each sighted set and
  each occurrence it took, as a held reference.

## Controls (`ChoiceControls`)

At `{5, 6}`, both labelled `0`:

* **Respect needs the matching probe class** (`permitted_present_breaks_respect`): after taking one
  occurrence and sighting `{5, 6}`, the two runs are trace equivalent and their ends equivalent
  relative to the record (`ends_recordEquivalent`). The probe `present 5` names only identities the
  record mentions, so the pointwise permission accepts it, yet it observes differently at the two
  ends, and the record does not support it. Only the supported probes respect the equivalence
  (`Observation.RecordEquivalent.observes`).
* **Raw order is outside the profile** (`order_distinguishes`): "the least sighted identity is
  present" also separates the two ends.
* **No deterministic equivariant selection from a symmetric pair** (`no_equivariant_selection`,
  `no_selection_from_pair`). A selection may instead be a nondeterministic firing that records its
  choice (`choice_recorded_identified`: taking `5` and taking `6`, each recorded, are trace
  equivalent, with records related by the exchange), or use extra structure: once the record also
  holds `5`, every automorphism fixes it (`remembered_member_fixed`), and the record of the pair with
  a remembered member tells the two runs apart (`remembered_distinguishes`).
* **Repeated references** (`aliasing_visible`, `aliasing_classes`): holding `5` twice is not holding
  `5` and `6`; it constrains the renamings as holding `5` once does (`aliasing_same_automorphisms`).
* **A name exported later** (`later_export_identified`, `earlier_export_distinguishes`): sighting
  `{5, 6}` and then taking `5` (recorded) is trace equivalent to sighting `{5, 6}` and then taking
  `6`; the later export extends the correspondence. When `5` was held from the start, the same two
  runs are told apart.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Observation

universe uO

namespace Record

variable {O : Type uO} [DecidableEq O]

theorem mem_support_rename {π : O ≃ O} {r : Record O} {o : O} :
    o ∈ support (rename π r) ↔ π.symm o ∈ support r := by
  rw [mem_support, mem_support]
  constructor
  · rintro ⟨e', renamed, l', inside, there⟩
    obtain ⟨e, inR, rfl⟩ := List.mem_map.mp renamed
    obtain ⟨l, inE, rfl⟩ := Finset.mem_map.mp inside
    obtain ⟨a, inl, rfl⟩ := List.mem_map.mp there
    exact ⟨e, inR, l, inE, by rwa [Equiv.symm_apply_apply]⟩
  · rintro ⟨e, member, l, inside, there⟩
    exact ⟨renameEntry π e, List.mem_map_of_mem member, tupleEmbedding π l, Finset.mem_map_of_mem _ inside,
      List.mem_map.mpr ⟨π.symm o, there, Equiv.apply_symm_apply π o⟩⟩

/-- **Renaming a record renames the identities it mentions.** -/
theorem support_rename (π : O ≃ O) (r : Record O) : support (rename π r) = (support r).map π.toEmbedding := by
  ext o
  rw [mem_support_rename, Finset.mem_map_equiv]

omit [DecidableEq O] in
theorem references_rename (π : O ≃ O) (l : List O) : references (l.map π) = rename π (references l) := by
  simp only [references, rename, List.map_map]
  exact List.map_congr_left fun o _ => (renameEntry_reference π o).symm

end Record

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Observation

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open Observation (Record)

universe uO uT uH uOcc uS uF uI

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {State : Type uS} {Firing : State → Type uF}
  {P : Step X O State Firing} {T : Transport P}

/-- **An isomorphism of an escaped state to itself renames by an automorphism of its whole record.** -/
theorem escapeIso_self_mem {x : Escaped P} (i : T.EscapeIso x x) :
    (T.toStateIso i.base).rename ∈ Record.automorphisms x.record :=
  i.record

/-- **The correspondence between two executions grows**: the renaming relating the ends of
trace-equivalent runs carries the identities the start's record mentions onto themselves, and the
identities one end's record mentions onto those of the other's. -/
theorem Transport.Escape.traceEquiv_correspondence {natural : T.Natural} {D : T.Escape} {x : Escaped P}
    {r r' : D.step.Run x} (equivalent : (T.escaping natural D).TraceEquiv x r r') :
    ∃ i : T.Iso r.last.state r'.last.state,
      (Record.support x.record).map (T.toStateIso i).rename.toEmbedding = Record.support x.record ∧
        (Record.support r.last.record).map (T.toStateIso i).rename.toEmbedding =
          Record.support r'.last.record := by
  obtain ⟨i, past, later, later', grown, grown', recorded⟩ := Transport.Escape.traceEquiv_past equivalent
  have kept : Record.rename (T.toStateIso i).rename x.record = x.record := past
  refine ⟨i, ?_, ?_⟩
  · rw [← Record.support_rename, kept]
  · rw [← Record.support_rename, grown, grown', Record.rename_append, kept, recorded]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

open Interface (Frames Transport Escaped FrameProbe)
open Observation (Record querySightings RecordEquivalent ModuloProbe)
open GuardFreeProcessOrders (SameUpTo)

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

section Choices

variable (A : SubstitutionAction T S) (label : O → T)

/-- **Recording choices**: a firing makes the environment record each set its predicate queries
sighted and each occurrence it took, as a held reference. -/
def choiceEscape : (renamingTransport A label).Escape where
  row _ o := some (label o)
  row_iso i o := .some (Frames.Carried.of_E (by
    show A.E (A.apply A.identity (label o)) (label (i.rename o))
    rw [A.apply_identity, i.keeps]
    exact A.equivalence.refl _))
  records f := querySightings f.queries ++ Record.references f.selection.taken
  publishes _ _ := []
  records_move i f := by
    show querySightings (f.queries.map (renameQuery i.rename)) ++
        Record.references (f.selection.taken.map i.rename) =
      Record.rename i.rename (querySightings f.queries ++ Record.references f.selection.taken)
    rw [Observation.querySightings_rename, Record.rename_append, Record.references_rename]
  publishes_move _ _ _ := .nil
  records_alike {C} {f} _ same := by
    subst same
    rfl
  publishes_alike {C} {f} _ same _ _ := by
    subst same
    exact .nil

/-- The escape-relative transport that records choices. -/
abbrev choiceEscaping :=
  (renamingTransport A label).escaping (renamingNatural A label) (choiceEscape A label)

end Choices

omit [DecidableEq O] in
/-- **No deterministic equivariant selection from a symmetric pair**: a selection that commutes with
every renaming of records picks neither member of a pair that an automorphism of the record
exchanges. -/
theorem no_equivariant_selection (select : Record O → O)
    (equivariant : ∀ (π : O ≃ O) (r : Record O), select (Record.rename π r) = π (select r))
    {r : Record O} {π : O ≃ O} (aut : π ∈ Record.automorphisms r) {a b : O} (apart : a ≠ b)
    (exchanges : π a = b ∧ π b = a) : select r ≠ a ∧ select r ≠ b := by
  have fixed : π (select r) = select r := by
    rw [← equivariant]
    exact congrArg select aut
  refine ⟨fun picked => ?_, fun picked => ?_⟩
  · rw [picked, exchanges.1] at fixed
    exact apart fixed.symm
  · rw [picked, exchanges.2] at fixed
    exact apart fixed

namespace ChoiceControls

open Mettapedia.Logic.LP
open ConstraintMultisetRewriting.Controls (signature)
open EscapeControls (blank twins seeAll takeFive swapTwins swapTwins_keeps twins_renamed takeFive_valid
  takeSix_valid)
open ObserverControls (escaping start runFive runSix swapIso sighting_dissolved)
open Observation.Record (sighting reference references automorphisms)
open MeTTaCalculus.OccurrenceCommits (regionOf)

/-- The substitution action of the controls. -/
abbrev A := ConstraintMultisetRewriting.Controls.A

/-! ### Respect needs the matching probe class -/

/-- The end of taking `5`: occurrence `6` is left. -/
theorem endFive_present : (runFive []).last.state.present = {6} := by decide

/-- The end of taking `6`: occurrence `5` is left. -/
theorem endSix_present : (runSix []).last.state.present = {5} := by decide

theorem endFive_record : (runFive []).last.record = [sighting {5, 6}] := rfl

/-- **The two ends are equivalent relative to the record**, by the exchange. -/
theorem ends_recordEquivalent :
    RecordEquivalent A blank [sighting {5, 6}] (runFive []).last.state (runSix []).last.state := by
  have aut : swapTwins ∈ automorphisms [sighting ({5, 6} : Finset ℕ)] :=
    Observation.RecordControls.sighting_swap.1
  have moved : (runFive []).last.state.present.map swapTwins.toEmbedding = (runSix []).last.state.present := by
    rw [endFive_present, endSix_present]
    decide
  refine ⟨fun σ => Iff.rfl, fun o fixed => ?_, fun σ _ => ⟨swapTwins, aut, fun o => A.equivalence.refl _, moved⟩⟩
  rw [endFive_present, endSix_present]
  have notFive : o ≠ 5 := fun same => by
    have := fixed _ aut
    rw [same, Equiv.swap_apply_left] at this
    exact absurd this (by decide)
  have notSix : o ≠ 6 := fun same => by
    have := fixed _ aut
    rw [same, Equiv.swap_apply_right] at this
    exact absurd this (by decide)
  simp [notFive, notSix]

/-- **Weakening pointwise fixing to automorphisms of the record breaks respect for the old probe
class.** The runs are trace equivalent and their ends equivalent relative to the record. The probe
`present 5` names only an identity the record mentions, so the pointwise permission accepts it; it
observes differently at the two ends; and the record does not support it. -/
theorem permitted_present_breaks_respect :
    escaping.TraceEquiv (start []) (runFive []) (runSix []) ∧
      RecordEquivalent A blank (runFive []).last.record (runFive []).last.state (runSix []).last.state ∧
      (ModuloProbe.present 5 : ModuloProbe A ℕ).names ⊆ Record.support (runFive []).last.record ∧
      ¬ ((ModuloProbe.present 5 : ModuloProbe A ℕ).Observes blank (runFive []).last.state ↔
        (ModuloProbe.present 5 : ModuloProbe A ℕ).Observes blank (runSix []).last.state) ∧
      ¬ (ModuloProbe.present 5 : ModuloProbe A ℕ).Supported (runFive []).last.record := by
  refine ⟨sighting_dissolved, ends_recordEquivalent, ?_, ?_, fun supported => ?_⟩
  · rw [endFive_record]
    decide
  · show ¬ (5 ∈ (runFive []).last.state.present ↔ 5 ∈ (runSix []).last.state.present)
    rw [endFive_present, endSix_present]
    decide
  · have moved := supported _ Observation.RecordControls.sighting_swap.1
    have := ModuloProbe.present.inj moved
    exact absurd this (by decide)

/-- **The same holds for frame probes**: `present 5` observes differently at the two ends, and the
record does not support it. -/
theorem frame_present_breaks_respect :
    ¬ ((FrameProbe.present 5 : FrameProbe (Frames.ofSubstitution A) PUnit.unit ℕ).Observes
          (Interface.ofConfiguration A blank (runFive []).last.state) ↔
        (FrameProbe.present 5 : FrameProbe (Frames.ofSubstitution A) PUnit.unit ℕ).Observes
          (Interface.ofConfiguration A blank (runSix []).last.state)) ∧
      ¬ (FrameProbe.present 5 : FrameProbe (Frames.ofSubstitution A) PUnit.unit ℕ).Supported
        (runFive []).last.record := by
  refine ⟨?_, fun supported => ?_⟩
  · show ¬ (5 ∈ (runFive []).last.state.present ↔ 5 ∈ (runSix []).last.state.present)
    rw [endFive_present, endSix_present]
    decide
  · have := FrameProbe.present.inj (supported _ Observation.RecordControls.sighting_swap.1)
    exact absurd this (by decide)

/-- **Raw order is outside the profile**: "the least sighted identity is present" separates the two
trace-equivalent ends. -/
theorem order_distinguishes :
    ({5, 6} : Finset ℕ).min' ⟨5, by decide⟩ = 5 ∧
      ¬ (({5, 6} : Finset ℕ).min' ⟨5, by decide⟩ ∈ (runFive []).last.state.present ↔
        ({5, 6} : Finset ℕ).min' ⟨5, by decide⟩ ∈ (runSix []).last.state.present) := by
  rw [endFive_present, endSix_present]
  decide

/-! ### Selections -/

/-- **No deterministic equivariant selection picks a member of the sighted pair.** -/
theorem no_selection_from_pair :
    ¬ ∃ select : Record ℕ → ℕ, (∀ (π : ℕ ≃ ℕ) (r : Record ℕ), select (Record.rename π r) = π (select r)) ∧
      select [sighting {5, 6}] ∈ ({5, 6} : Finset ℕ) := by
  rintro ⟨select, equivariant, picked⟩
  obtain ⟨notFive, notSix⟩ := no_equivariant_selection select equivariant
    Observation.RecordControls.sighting_swap.1 (a := 5) (b := 6) (by decide) ⟨rfl, rfl⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at picked
  rcases picked with five | six
  · exact notFive five
  · exact notSix six

/-- **Extra structure permits a selection**: once the record also holds `5`, every automorphism fixes
`5`. -/
theorem remembered_member_fixed :
    ∀ π ∈ automorphisms [sighting ({5, 6} : Finset ℕ), reference 5], π 5 = 5 := by
  intro π aut
  have carried : Record.rename π ([sighting {5, 6}] ++ references [5]) = [sighting {5, 6}] ++ references [5] := aut
  exact Record.references_rename_eq_iff.mp (Record.rename_append_eq_iff.mp carried).2 5
    (List.mem_singleton_self 5)

/-- **The record of an unordered pair with a remembered member tells the two runs apart**, while the
record of the unordered pair alone does not (`ObserverControls.sighted_set_identified`). -/
theorem remembered_distinguishes :
    ¬ escaping.TraceEquiv (start [sighting {5, 6}, reference 5]) (runFive _) (runSix _) :=
  ObserverControls.fixed_distinguishes remembered_member_fixed

/-- The escape-relative transport of the controls that records choices. -/
abbrev choices := choiceEscaping A blank

/-- Take `5`, sight `{5, 6}`, and record the choice. -/
abbrev choiceFive (R : Record ℕ) : (choiceEscape A blank).step.Run (start R) :=
  .cons takeFive takeFive_valid (.nil _)

/-- Take `6`, sight `{5, 6}`, and record the choice. -/
abbrev choiceSix (R : Record ℕ) : (choiceEscape A blank).step.Run (start R) :=
  .cons (takeFive.rename swapTwins) takeSix_valid (.nil _)

/-- The exchange of `5` and `6`, relative to an environment that knows nothing. -/
def freshSwap : choices.Iso (start []) (start []) := ⟨swapIso, .nil, rfl⟩

/-- **A nondeterministic selection that records its choice**: taking `5` and taking `6`, each
recorded, are trace equivalent; their records differ, and the exchange carries one to the other. -/
theorem choice_recorded_identified :
    choices.TraceEquiv (start []) (choiceFive []) (choiceSix []) ∧
      (choiceFive []).last.record = [sighting {5, 6}, reference 5] ∧
      (choiceSix []).last.record = [sighting {5, 6}, reference 6] ∧
      Record.rename swapTwins [sighting {5, 6}, reference 5] = [sighting {5, 6}, reference 6] :=
  ⟨.rel _ _ (.inr (Transport.Similar.single freshSwap takeFive_valid takeSix_valid rfl)), rfl,
    by decide, by decide⟩

/-! ### Repeated references -/

/-- **Holding `5` twice is not holding `5` and `6`**: no renaming carries one record to the other. -/
theorem aliasing_visible (π : ℕ ≃ ℕ) : Record.rename π [reference 5, reference 5] ≠ [reference 5, reference 6] := by
  intro carried
  simp only [Record.rename, List.map_cons, List.map_nil, List.cons.injEq, and_true,
    Record.renameEntry_reference] at carried
  have five := Record.reference_injective carried.1
  have six := Record.reference_injective carried.2
  rw [five] at six
  exact absurd six (by decide)

/-- **The two records give different state classes.** -/
theorem aliasing_classes :
    ¬ Nonempty (choices.Iso (start [reference 5, reference 5]) (start [reference 5, reference 6])) :=
  fun ⟨i⟩ => aliasing_visible _ i.record

/-- **A repeated reference constrains the renamings as a single one does.** -/
theorem aliasing_same_automorphisms (π : ℕ ≃ ℕ) :
    π ∈ automorphisms [reference 5, reference 5] ↔ π ∈ automorphisms [reference 5] := by
  show Record.rename π (references [5, 5]) = references [5, 5] ↔
    Record.rename π (references [5]) = references [5]
  rw [Record.references_rename_eq_iff, Record.references_rename_eq_iff]
  simp

/-! ### A name exported later -/

/-- Sight `{5, 6}` and take nothing. -/
def sightBoth : Firing (Term signature) (Subst signature) ℕ := ⟨⟨[], [], [], [], []⟩, [seeAll], ⟨[], [], []⟩⟩

/-- Take `o`, sighting nothing. -/
def takeOnly (o : ℕ) : Firing (Term signature) (Subst signature) ℕ :=
  ⟨⟨[.const 0], [], [], [], []⟩, [], ⟨[o], [], []⟩⟩

theorem sightBoth_valid : sightBoth.Valid A blank twins := by
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide,
    ⟨Subst.id signature, by simp [Selection.problem, Selection.equations, twins, sightBoth]⟩,
    by simp [sightBoth]⟩, ?_⟩
  intro query member σ _
  obtain rfl := List.mem_singleton.mp member
  show MeTTaCalculus.OccurrenceCommits.regionOf blank twins.present (fun _ => true) = {5, 6}
  decide

/-- What sighting both leaves. -/
abbrev afterSight : Configuration (Term signature) ℕ := sightBoth.result blank twins

theorem afterSight_present : afterSight.present = {5, 6} := by decide

theorem takeOnly_valid (o : ℕ) (present : o ∈ ({5, 6} : Finset ℕ)) :
    (takeOnly o).Valid A blank afterSight := by
  refine ⟨⟨List.nodup_singleton o, List.nodup_nil, rfl, rfl, rfl, ?_,
    ⟨Subst.id signature, ?_⟩, by simp [takeOnly]⟩, by simp [takeOnly]⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton] at present
    rcases present with rfl | rfl <;> decide
  · intro e member
    simp [Selection.problem, Selection.equations, takeOnly, sightBoth, Selection.result, Firing.result,
      twins, blank] at member
    obtain rfl := member
    exact A.equivalence.refl _

/-- Sight `{5, 6}`, then take `o` and record it. -/
abbrev sightThenTake (R : Record ℕ) (o : ℕ) (present : o ∈ ({5, 6} : Finset ℕ)) :
    (choiceEscape A blank).step.Run (start R) :=
  .cons sightBoth sightBoth_valid (.cons (takeOnly o) (takeOnly_valid o present) (.nil _))

theorem sightBoth_renamed : sightBoth.rename swapTwins = sightBoth := by
  have kept : ({5, 6} : Finset ℕ).map swapTwins.toEmbedding = {5, 6} := by decide
  show (⟨⟨[], [], [], [], []⟩, [⟨seeAll.region, ({5, 6} : Finset ℕ).map swapTwins.toEmbedding⟩],
    ⟨[], [], []⟩⟩ : Firing (Term signature) (Subst signature) ℕ) = sightBoth
  rw [kept]
  rfl

/-- The exchange of `5` and `6` after sighting both, relative to that record. -/
def afterSwap :
    choices.Iso ((choiceEscape A blank).step.result (s := start []) sightBoth sightBoth_valid)
      ((choiceEscape A blank).step.result (s := start []) sightBoth sightBoth_valid) :=
  ⟨⟨swapTwins, swapTwins_keeps, ⟨fun _ => Iff.rfl, by
      show afterSight.present.map swapTwins.toEmbedding = afterSight.present
      rw [afterSight_present]
      decide⟩⟩, .nil, by decide⟩

/-- **A name exported later extends the correspondence**: sighting `{5, 6}` and then taking `5`,
recorded, is trace equivalent to sighting `{5, 6}` and then taking `6`. -/
theorem later_export_identified :
    choices.TraceEquiv (start []) (sightThenTake [] 5 (by decide)) (sightThenTake [] 6 (by decide)) :=
  .rel _ _ (.inr (Transport.similar_cons_cons.mpr ⟨freshSwap, sightBoth_renamed,
    Transport.Similar.single afterSwap _ _ rfl⟩))

/-- **When `5` was held from the start, the same runs are told apart**: the renaming relating the
ends must fix `5` for the old reference and carry `5` to `6` for the new one. -/
theorem earlier_export_distinguishes :
    ¬ choices.TraceEquiv (start [reference 5]) (sightThenTake _ 5 (by decide)) (sightThenTake _ 6 (by decide)) := by
  intro equivalent
  obtain ⟨i, carried⟩ := Transport.Escape.traceEquiv_record equivalent
  change Record.rename i.rename [reference 5, sighting {5, 6}, reference 5] =
    [reference 5, sighting {5, 6}, reference 6] at carried
  simp only [Record.rename, List.map_cons, List.map_nil, List.cons.injEq, and_true,
    Record.renameEntry_reference] at carried
  have old := Record.reference_injective carried.1
  have new := Record.reference_injective carried.2.2
  rw [old] at new
  exact absurd new (by decide)

end ChoiceControls

#print axioms Observation.Record.support_rename
#print axioms Interface.escapeIso_self_mem
#print axioms Interface.Transport.Escape.traceEquiv_correspondence
#print axioms choiceEscape
#print axioms no_equivariant_selection
#print axioms ChoiceControls.ends_recordEquivalent
#print axioms ChoiceControls.permitted_present_breaks_respect
#print axioms ChoiceControls.frame_present_breaks_respect
#print axioms ChoiceControls.order_distinguishes
#print axioms ChoiceControls.no_selection_from_pair
#print axioms ChoiceControls.remembered_member_fixed
#print axioms ChoiceControls.remembered_distinguishes
#print axioms ChoiceControls.choice_recorded_identified
#print axioms ChoiceControls.aliasing_visible
#print axioms ChoiceControls.aliasing_classes
#print axioms ChoiceControls.aliasing_same_automorphisms
#print axioms ChoiceControls.later_export_identified
#print axioms ChoiceControls.earlier_export_distinguishes

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
