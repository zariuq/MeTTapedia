import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.CardinalityQueries
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.NativePacketStep
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.NativePacketRounds

/-!
# Querying the actual row closure in a context packet

The packet's rigid identity still selects a physical resource. Nonbinding
queries instead interpret its supplied row code under its supplied capture
environment. Schemas and latent equations use the existing native matching
relation, at the querying activation's actual target.

Exact membership and cardinality observations share this region. No source
row dictionary, guard marker or native admission predicate is consulted.
The existing fixed-collect query round profile is unchanged.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.NativePacketQueryView

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open MeTTaCalculus.OccurrenceCommits (Enabled regionOf mem_regionOf)
open TaggedAssignments (Object Substitution)
open ContextPackets (Value Environment)
open NativePacketStep (Terms Ports RowCode packetAction)

variable {S : Signature} {O : Type} {Γ : Ctx S} {sort : S.Srt}

def MatchesAt (target : Object S) (pattern : Term (signature S target.2.arity) Γ sort)
    (value : Terms S O Γ sort) : Prop :=
  ∃ (physical : O) (code : RowCode S Γ sort)
      (captures : Assignment code.captures.arity target.2.arity),
    value = Value.row (physical,code) ⟨code.captures,target,captures⟩ ∧
      ContextualConditionalRows.Matches code.locals.arity code.captures.arity
        captures pattern code.row

theorem matchesAt_row (target : Object S) (pattern : Term (signature S target.2.arity) Γ sort)
    (physical : O) (code : RowCode S Γ sort) (captures : Assignment code.captures.arity target.2.arity) :
    MatchesAt target pattern (Value.row (physical,code) ⟨code.captures,target,captures⟩) ↔
      ContextualConditionalRows.Matches code.locals.arity code.captures.arity captures pattern code.row := by
  constructor
  · rintro ⟨other,otherCode,otherCaptures,equal,matched⟩
    have fields := Value.row.inj equal
    have sameCode : code = otherCode := congrArg Prod.snd fields.1
    subst otherCode
    have sameCaptures : captures = otherCaptures :=
      eq_of_heq (Environment.assignment_heq S fields.2)
    subst otherCaptures
    exact matched
  · intro matched
    exact ⟨physical,code,captures,rfl,matched⟩

def rowMatches (site : Object S) (pattern : Term (signature S site.2.arity) Γ sort)
    (substitution : Substitution S) (value : Terms S O Γ sort) : Prop :=
  MatchesAt (substitution site).1 (instantiate (substitution site).2 pattern)
    (ContextPackets.apply S substitution value)

theorem rowMatches_identity (site : Object S) (pattern : Term (signature S site.2.arity) Γ sort)
    (value : Terms S O Γ sort) :
    rowMatches site pattern (TaggedAssignments.identity S) value ↔ MatchesAt site pattern value := by
  unfold rowMatches
  have applied : ContextPackets.apply S (TaggedAssignments.identity S) value = value :=
    (ContextPackets.action S (NativePacketStep.Rigid S O Γ sort)).apply_identity value
  rw [applied]
  change MatchesAt site (instantiate (generator site.2.arity) pattern) value ↔ _
  rw [instantiate_identity]

theorem rowMatches_compose (site : Object S) (pattern : Term (signature S site.2.arity) Γ sort)
    (post before : Substitution S) (value : Terms S O Γ sort) :
    rowMatches site pattern (TaggedAssignments.compose S post before) value ↔
      rowMatches (before site).1 (instantiate (before site).2 pattern) post
        (ContextPackets.apply S before value) := by
  unfold rowMatches
  have applied : ContextPackets.apply S (TaggedAssignments.compose S post before) value =
      ContextPackets.apply S post (ContextPackets.apply S before value) :=
    (ContextPackets.action S (NativePacketStep.Rigid S O Γ sort)).apply_compose post before value
  rw [applied]
  change MatchesAt _ (instantiate (Assignment.compose (post (before site).1).2 (before site).2) pattern) _ ↔ _
  rw [Assignment.instantiate_compose]

theorem not_rowMatches_anchor (site source : Object S)
    (pattern : Term (signature S site.2.arity) Γ sort) (substitution : Substitution S) :
    ¬ rowMatches site pattern substitution (ContextPackets.anchor source : Terms S O Γ sort) := by
  rintro ⟨physical,code,captures,equal,_⟩
  rw [ContextPackets.apply_anchor] at equal
  cases equal

theorem rowMatches_old_iff (s : NativeState S O Γ sort) (base use : Nat)
    (pattern : Term (signature S s.infoFrame.arity) Γ sort) (substitution : Substitution S)
    (captured : (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Solves substitution
      (NativePacketStep.captureRow s use,ContextPackets.anchor (NativePacketStep.baseObject s base)))
    (occurrence : O) :
    rowMatches (NativePacketStep.useObject s use) pattern substitution (NativePacketStep.oldRow s base occurrence) ↔
      ContextualConditionalRows.Matches s.locals s.infoFrame.arity
        (substitution (NativePacketStep.useObject s use)).2
        (instantiate (substitution (NativePacketStep.useObject s use)).2 pattern)
        (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows occurrence) := by
  unfold rowMatches
  rw [← NativePacketStep.read_row_solved s base use substitution captured occurrence]
  change MatchesAt _ _ (Value.row (occurrence,NativePacketStep.oldCode s occurrence)
    ⟨(NativePacketStep.oldCode s occurrence).captures,_,
      Assignment.compose (substitution (NativePacketStep.useObject s use)).2
        (ContextualSelectionViews.capturedTarget s.locals s.state.declarations)⟩) ↔ _
  rw [matchesAt_row]
  exact (ContextualConditionalRows.matches_map_iff s.locals s.state.declarations
    (ContextualSelectionViews.capturedTarget s.locals s.state.declarations)
    (substitution (NativePacketStep.useObject s use)).2
    (instantiate (substitution (NativePacketStep.useObject s use)).2 pattern)
    (s.state.rows occurrence)).symm

theorem rowMatches_output_iff {s : NativeState S O Γ sort} (producer : LiveFiring s)
    (site : Object S) (pattern : Term (signature S site.2.arity) Γ sort) (use : Nat)
    (substitution : Substitution S) (target : Object S)
    (reader : Assignment site.2.arity target.2.arity)
    (writer : Assignment s.infoFrame.arity target.2.arity)
    (read : substitution site = ⟨target,reader⟩)
    (write : substitution (NativePacketStep.useObject s use) = ⟨target,writer⟩) (occurrence : O) :
    rowMatches site pattern substitution (NativePacketStep.outputRow producer use occurrence) ↔
      instantiate reader pattern = instantiate writer (producer.outputs occurrence) := by
  unfold rowMatches
  rw [read]
  change MatchesAt target (instantiate reader pattern)
    (Value.row (occurrence,NativePacketStep.outputCode producer occurrence)
      ⟨s.infoFrame,_,Assignment.compose (substitution (NativePacketStep.useObject s use)).2
        (generator s.infoFrame.arity)⟩) ↔ _
  dsimp only [NativePacketStep.useObject] at write ⊢
  rw [write]
  change MatchesAt target (instantiate reader pattern)
    (Value.row (occurrence,NativePacketStep.outputCode producer occurrence)
      ⟨s.infoFrame,target,Assignment.compose writer (generator s.infoFrame.arity)⟩) ↔ _
  rw [Assignment.compose_identity_right]
  apply (matchesAt_row target (instantiate reader pattern) occurrence
    (NativePacketStep.outputCode producer occurrence) writer).trans
  exact (ContextualConditionalRows.ofStored_matches_iff s.locals s.infoFrame.arity writer
    (instantiate reader pattern) (.shared (producer.outputs occurrence))).trans
      (ContextualGuardMatching.shared_matches_iff s.locals writer
        (instantiate reader pattern) (producer.outputs occurrence))

noncomputable def region (site : Object S) (pattern : Term (signature S site.2.arity) Γ sort)
    (substitution : Substitution S) (value : Terms S O Γ sort) : Bool := by
  classical
  exact decide (rowMatches site pattern substitution value)

theorem region_true_iff (site : Object S) (pattern : Term (signature S site.2.arity) Γ sort)
    (substitution : Substitution S) (value : Terms S O Γ sort) :
    region site pattern substitution value = true ↔ rowMatches site pattern substitution value := by
  classical
  change decide (rowMatches site pattern substitution value) = true ↔ _
  exact decide_eq_true_iff

theorem region_false_iff (site : Object S) (pattern : Term (signature S site.2.arity) Γ sort)
    (substitution : Substitution S) (value : Terms S O Γ sort) :
    region site pattern substitution value = false ↔ ¬ rowMatches site pattern substitution value := by
  classical
  change decide (rowMatches site pattern substitution value) = false ↔ _
  exact decide_eq_false_iff_not

noncomputable def exactQuery (site : Object S) (pattern : Term (signature S site.2.arity) Γ sort)
    (seen : Finset (Ports O)) : PredicateQueryAdmission.Query (Terms S O Γ sort) (Substitution S) (Ports O) :=
  ⟨region site pattern,seen⟩

noncomputable def countQuery (site : Object S) (pattern : Term (signature S site.2.arity) Γ sort)
    (number : Nat) : CardinalityQueries.Query (Terms S O Γ sort) (Substitution S) :=
  ⟨region site pattern,number⟩

variable [DecidableEq O]

theorem source_region (s : NativeState S O Γ sort) (base use : Nat)
    (pattern : Term (signature S s.infoFrame.arity) Γ sort) (substitution : Substitution S)
    (label : Ports O → Terms S O Γ sort)
    (old : ∀ occurrence ∈ s.state.present, label (.inl occurrence) = NativePacketStep.oldRow s base occurrence)
    (anchor : label (.inr ()) = ContextPackets.anchor (NativePacketStep.baseObject s base))
    (captured : (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Solves substitution
      (NativePacketStep.captureRow s use,ContextPackets.anchor (NativePacketStep.baseObject s base))) :
    regionOf label (NativePacketStep.present s) (region (NativePacketStep.useObject s use) pattern substitution) =
      (ContextualConditionalGuards.region s.locals (substitution (NativePacketStep.useObject s use)).2
        (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows)
        s.state.present pattern).image Sum.inl := by
  classical
  ext port
  constructor
  · intro member
    obtain ⟨present,matched⟩ := mem_regionOf.mp member
    have actual := (region_true_iff _ _ _ _).mp matched
    cases port with
    | inl occurrence =>
        have inside := (NativePacketStep.mem_present_inl s occurrence).mp present
        rw [old occurrence inside] at actual
        exact Finset.mem_image.mpr ⟨occurrence,
          (ContextualConditionalGuards.mem_region _ _ _ _ _ _).mpr
            ⟨inside,(rowMatches_old_iff s base use pattern substitution captured occurrence).mp actual⟩,rfl⟩
    | inr token =>
        cases token
        rw [anchor] at actual
        exact False.elim (not_rowMatches_anchor _ _ _ _ actual)
  · intro member
    obtain ⟨occurrence,inside,rfl⟩ := Finset.mem_image.mp member
    obtain ⟨present,matched⟩ := (ContextualConditionalGuards.mem_region _ _ _ _ _ _).mp inside
    apply mem_regionOf.mpr
    refine ⟨(NativePacketStep.mem_present_inl s occurrence).mpr present,?_⟩
    apply (region_true_iff _ _ _ _).mpr
    rw [old occurrence present]
    exact (rowMatches_old_iff s base use pattern substitution captured occurrence).mpr matched

theorem own_region {s : NativeState S O Γ sort} (f : LiveFiring s) (base use : Nat)
    (enabled : Enabled (fun _ : O => ()) s.state.present (f.selection.commit (T := Unit)))
    (pattern : Term (signature S s.infoFrame.arity) Γ sort) (substitution : Substitution S)
    (model : (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Models substitution
      ((NativePacketStep.selection f).problem (NativePacketStep.label f base use)
        (NativePacketStep.body f use) (NativePacketStep.configuration s base))) :
    regionOf (NativePacketStep.label f base use) (NativePacketStep.present s)
        (region (NativePacketStep.useObject s use) pattern substitution) =
      (ContextualConditionalGuards.region s.locals (substitution (NativePacketStep.useObject s use)).2
        (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows)
        s.state.present pattern).image Sum.inl := by
  apply source_region s base use pattern substitution (NativePacketStep.label f base use)
  · intro occurrence present
    have unmade : occurrence ∉ f.selection.made := fun made =>
      Finset.disjoint_left.mp enabled.fresh (List.mem_toFinset.mpr made) present
    exact if_neg unmade
  · rfl
  · exact NativePacketStep.model_reads_capture f base use substitution model

theorem own_count_ask_iff {s : NativeState S O Γ sort} (f : LiveFiring s) {base use : Nat}
    (different : base ≠ use)
    (enabled : Enabled (fun _ : O => ()) s.state.present (f.selection.commit (T := Unit)))
    (pattern : Term (signature S s.infoFrame.arity) Γ sort) (number : Nat) :
    (countQuery (NativePacketStep.useObject s use) pattern number).Ask
        (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
        ((NativePacketStep.selection f).problem (NativePacketStep.label f base use)
          (NativePacketStep.body f use) (NativePacketStep.configuration s base))
        (NativePacketStep.label f base use) (NativePacketStep.present s) ↔
      ContextualConditionalGuards.Ask s.locals (FamilyInformation.memberInformation f)
        (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows)
        s.state.present (.count pattern number) := by
  have point (substitution : Substitution S)
      (model : (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Models substitution
        ((NativePacketStep.selection f).problem (NativePacketStep.label f base use)
          (NativePacketStep.body f use) (NativePacketStep.configuration s base))) :
      (countQuery (NativePacketStep.useObject s use) pattern number).Holds substitution
          (NativePacketStep.label f base use) (NativePacketStep.present s) ↔
        ContextualConditionalGuards.Holds s.locals (substitution (NativePacketStep.useObject s use)).2
          (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows)
          s.state.present (.count pattern number) := by
    change (regionOf _ _ (region _ _ _)).card = number ↔ _
    rw [own_region f base use enabled pattern substitution model,
      Finset.card_image_of_injective _ Sum.inl_injective]
    rfl
  constructor
  · intro asked Future future candidate model
    let target : Frames.Frame S := ⟨Future,future⟩
    have fitModel := NativePacketStep.model_fit f different enabled target candidate model
    have answer := (point _ fitModel).mp (asked _ fitModel)
    rw [NativePacketStep.fit_use s base use target candidate] at answer
    exact answer
  · intro asked substitution model
    apply (point substitution model).mpr
    exact asked _ _ _ (NativePacketStep.model_reads_information f base use substitution model)

theorem own_exact_ask_iff {s : NativeState S O Γ sort} (f : LiveFiring s) {base use : Nat}
    (different : base ≠ use)
    (enabled : Enabled (fun _ : O => ()) s.state.present (f.selection.commit (T := Unit)))
    (pattern : Term (signature S s.infoFrame.arity) Γ sort) (seen : Finset O) :
    (exactQuery (NativePacketStep.useObject s use) pattern (seen.image Sum.inl)).Ask
        (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
        ((NativePacketStep.selection f).problem (NativePacketStep.label f base use)
          (NativePacketStep.body f use) (NativePacketStep.configuration s base))
        (NativePacketStep.label f base use) (NativePacketStep.present s) ↔
      ContextualPredicateQueryAdmission.AskData (FamilyInformation.memberInformation f)
        (ContextualPredicateQueryAdmission.matchingQuery s.locals pattern seen)
        (ContextualPredicateQueryAdmission.nativeLabels s.locals s.state) s.state.present := by
  have point (substitution : Substitution S)
      (model : (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Models substitution
        ((NativePacketStep.selection f).problem (NativePacketStep.label f base use)
          (NativePacketStep.body f use) (NativePacketStep.configuration s base))) :
      ((exactQuery (NativePacketStep.useObject s use) pattern (seen.image Sum.inl)).atSolution substitution).Holds
          (NativePacketStep.label f base use) (NativePacketStep.present s) ↔
        ((ContextualPredicateQueryAdmission.matchingQuery s.locals pattern seen).atSolution
          ⟨(substitution (NativePacketStep.useObject s use)).1.2.Names,
            (substitution (NativePacketStep.useObject s use)).1.2.arity,
            (substitution (NativePacketStep.useObject s use)).2⟩).Holds
          (ContextualPredicateQueryAdmission.nativeLabels s.locals s.state) s.state.present := by
    change regionOf _ _ (region _ _ _) = seen.image Sum.inl ↔ _
    rw [own_region f base use enabled pattern substitution model,Finset.image_inj Sum.inl_injective]
    change _ ↔ ((ContextualPredicateQueryAdmission.matchingQuery s.locals pattern seen).atSolution
      ⟨(substitution (NativePacketStep.useObject s use)).1.2.Names,
        (substitution (NativePacketStep.useObject s use)).1.2.arity,
        (substitution (NativePacketStep.useObject s use)).2⟩).Holds
      (fun occurrence => (occurrence,
        ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows occurrence)) s.state.present
    exact (ContextualPredicateQueryAdmission.matching_holds_iff s.locals pattern seen
      (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows)
      s.state.present
      ⟨(substitution (NativePacketStep.useObject s use)).1.2.Names,
        (substitution (NativePacketStep.useObject s use)).1.2.arity,
        (substitution (NativePacketStep.useObject s use)).2⟩).symm
  constructor
  · intro asked Future future candidate model
    let target : Frames.Frame S := ⟨Future,future⟩
    have fitModel := NativePacketStep.model_fit f different enabled target candidate model
    have answer := (point _ fitModel).mp (asked _ fitModel)
    rw [NativePacketStep.fit_use s base use target candidate] at answer
    exact answer
  · intro asked substitution model
    apply (point substitution model).mpr
    exact asked _ _ _ (NativePacketStep.model_reads_information f base use substitution model)

theorem own_absence_ask_iff {s : NativeState S O Γ sort} (f : LiveFiring s) {base use : Nat}
    (different : base ≠ use)
    (enabled : Enabled (fun _ : O => ()) s.state.present (f.selection.commit (T := Unit)))
    (pattern : Term (signature S s.infoFrame.arity) Γ sort) :
    (exactQuery (NativePacketStep.useObject s use) pattern (∅ : Finset (Ports O))).Ask
        (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
        ((NativePacketStep.selection f).problem (NativePacketStep.label f base use)
          (NativePacketStep.body f use) (NativePacketStep.configuration s base))
        (NativePacketStep.label f base use) (NativePacketStep.present s) ↔
      ContextualConditionalGuards.Ask s.locals (FamilyInformation.memberInformation f)
        (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows)
        s.state.present (.predicate .none pattern) := by
  simpa only [Finset.image_empty] using
    (own_exact_ask_iff f different enabled pattern ∅).trans
      (ContextualPredicateQueryAdmission.matching_ask_empty_iff s.locals
        (FamilyInformation.memberInformation f) pattern
        (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows) s.state.present)

theorem family_region {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (index : Fin members.length) (pattern : Term (signature S s.infoFrame.arity) Γ sort)
    (substitution : Substitution S)
    (model : (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Models substitution
      (NativePacketRounds.jointProblem members)) :
    regionOf (NativePacketRounds.label members) (NativePacketStep.present s)
        (region (NativePacketStep.useObject s (NativePacketRounds.useTag index)) pattern substitution) =
      (ContextualConditionalGuards.region s.locals
        (substitution (NativePacketStep.useObject s (NativePacketRounds.useTag index))).2
        (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows)
        s.state.present pattern).image Sum.inl := by
  apply source_region s 0 (NativePacketRounds.useTag index) pattern substitution (NativePacketRounds.label members)
  · exact NativePacketRounds.label_old members
  · rfl
  · exact NativePacketRounds.member_models_capture members index substitution
      (NativePacketRounds.joint_models_member members index substitution model)

private theorem pair_retarget {domain : Frames.Frame S} {first second : Object S}
    (same : first = second) (candidate : Assignment domain.arity first.2.arity) :
    (⟨first,candidate⟩ : (target : Object S) × Assignment domain.arity target.2.arity) =
      ⟨second,NativePacketRounds.retarget same candidate⟩ := by
  cases same
  rfl

theorem readData_use {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (index : Fin members.length) (substitution : Substitution S)
    (model : (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Models substitution
      (NativePacketRounds.jointProblem members)) :
    substitution (NativePacketStep.useObject s (NativePacketRounds.useTag index)) =
      ⟨(substitution (NativePacketStep.baseObject s 0)).1,
        (NativePacketRounds.readData members substitution model).member index⟩ := by
  exact pair_retarget
    (ContextPackets.capture_targets (source := NativePacketStep.baseObject s 0)
      (target := NativePacketStep.useObject s (NativePacketRounds.useTag index))
      (ContextualSelectionViews.capturedTarget s.locals s.state.declarations) substitution
      (NativePacketRounds.member_models_capture members index substitution
        (NativePacketRounds.joint_models_member members index substitution model)))
    (substitution (NativePacketStep.useObject s (NativePacketRounds.useTag index))).2

omit [DecidableEq O] in
private theorem region_retarget {s : NativeState S O Γ sort} {first second : Object S}
    (same : first = second) (candidate : Assignment s.infoFrame.arity first.2.arity)
    (pattern : Term (signature S s.infoFrame.arity) Γ sort) :
    ContextualConditionalGuards.region s.locals (NativePacketRounds.retarget same candidate)
        (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows) s.state.present pattern =
      ContextualConditionalGuards.region s.locals candidate
        (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows) s.state.present pattern := by
  cases same
  rfl

theorem readData_region {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (index : Fin members.length) (substitution : Substitution S)
    (model : (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Models substitution
      (NativePacketRounds.jointProblem members)) (pattern : Term (signature S s.infoFrame.arity) Γ sort) :
    ContextualConditionalGuards.region s.locals ((NativePacketRounds.readData members substitution model).member index)
        (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows) s.state.present pattern =
      ContextualConditionalGuards.region s.locals
        (substitution (NativePacketStep.useObject s (NativePacketRounds.useTag index))).2
        (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows) s.state.present pattern := by
  exact region_retarget
    (ContextPackets.capture_targets (source := NativePacketStep.baseObject s 0)
      (target := NativePacketStep.useObject s (NativePacketRounds.useTag index))
      (ContextualSelectionViews.capturedTarget s.locals s.state.declarations) substitution
      (NativePacketRounds.member_models_capture members index substitution
        (NativePacketRounds.joint_models_member members index substitution model)))
    (substitution (NativePacketStep.useObject s (NativePacketRounds.useTag index))).2 pattern

theorem family_output_iff {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (reader writer : Fin members.length) (pattern : Term (signature S s.infoFrame.arity) Γ sort)
    (substitution : Substitution S)
    (model : (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Models substitution
      (NativePacketRounds.jointProblem members)) (occurrence : O) :
    rowMatches (NativePacketStep.useObject s (NativePacketRounds.useTag reader)) pattern substitution
        (NativePacketStep.outputRow members[writer] (NativePacketRounds.useTag writer) occurrence) ↔
      instantiate ((NativePacketRounds.readData members substitution model).member reader) pattern =
        instantiate ((NativePacketRounds.readData members substitution model).member writer)
          (members[writer].outputs occurrence) :=
  rowMatches_output_iff members[writer] _ pattern (NativePacketRounds.useTag writer) substitution
    (substitution (NativePacketStep.baseObject s 0)).1 _ _
    (readData_use members reader substitution model) (readData_use members writer substitution model) occurrence

theorem family_count_ask_iff {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (nonempty : members ≠ [])
    (enabled : ∀ index : Fin members.length,
      Enabled (fun _ : O => ()) s.state.present (members[index].selection.commit (T := Unit)))
    (index : Fin members.length) (pattern : Term (signature S s.infoFrame.arity) Γ sort) (number : Nat) :
    (countQuery (NativePacketStep.useObject s (NativePacketRounds.useTag index)) pattern number).Ask
        (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)) (NativePacketRounds.jointProblem members)
        (NativePacketRounds.label members) (NativePacketStep.present s) ↔
      ∀ (target : Frames.Frame S) (data : FamilyInformation.SolutionData s members target),
        (ContextualConditionalGuards.region s.locals (data.member index)
          (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows)
          s.state.present pattern).card = number := by
  have point (substitution : Substitution S)
      (model : (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Models substitution
        (NativePacketRounds.jointProblem members)) :
      (countQuery (NativePacketStep.useObject s (NativePacketRounds.useTag index)) pattern number).Holds substitution
          (NativePacketRounds.label members) (NativePacketStep.present s) ↔
        (ContextualConditionalGuards.region s.locals
          (substitution (NativePacketStep.useObject s (NativePacketRounds.useTag index))).2
          (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows)
          s.state.present pattern).card = number := by
    change (regionOf _ _ (region _ _ _)).card = number ↔ _
    rw [family_region members index pattern substitution model,
      Finset.card_image_of_injective _ Sum.inl_injective]
  constructor
  · intro asked target data
    have model := NativePacketRounds.fitData_joint data nonempty enabled
    have actual := (point _ model).mp (asked _ model)
    rw [NativePacketRounds.fitData_use data index] at actual
    exact actual
  · intro asked substitution model
    have actual := asked _ (NativePacketRounds.readData members substitution model)
    rw [readData_region members index substitution model pattern] at actual
    exact (point substitution model).mpr actual

theorem family_exact_ask_iff {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (nonempty : members ≠ [])
    (enabled : ∀ index : Fin members.length,
      Enabled (fun _ : O => ()) s.state.present (members[index].selection.commit (T := Unit)))
    (index : Fin members.length) (pattern : Term (signature S s.infoFrame.arity) Γ sort) (seen : Finset O) :
    (exactQuery (NativePacketStep.useObject s (NativePacketRounds.useTag index)) pattern (seen.image Sum.inl)).Ask
        (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)) (NativePacketRounds.jointProblem members)
        (NativePacketRounds.label members) (NativePacketStep.present s) ↔
      ∀ (target : Frames.Frame S) (data : FamilyInformation.SolutionData s members target),
        ContextualConditionalGuards.region s.locals (data.member index)
          (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows)
          s.state.present pattern = seen := by
  have point (substitution : Substitution S)
      (model : (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Models substitution
        (NativePacketRounds.jointProblem members)) :
      ((exactQuery (NativePacketStep.useObject s (NativePacketRounds.useTag index)) pattern (seen.image Sum.inl)).atSolution
        substitution).Holds (NativePacketRounds.label members) (NativePacketStep.present s) ↔
        ContextualConditionalGuards.region s.locals
          (substitution (NativePacketStep.useObject s (NativePacketRounds.useTag index))).2
          (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows)
          s.state.present pattern = seen := by
    change regionOf _ _ (region _ _ _) = seen.image Sum.inl ↔ _
    rw [family_region members index pattern substitution model,Finset.image_inj Sum.inl_injective]
  constructor
  · intro asked target data
    have model := NativePacketRounds.fitData_joint data nonempty enabled
    have actual := (point _ model).mp (asked _ model)
    rw [NativePacketRounds.fitData_use data index] at actual
    exact actual
  · intro asked substitution model
    have actual := asked _ (NativePacketRounds.readData members substitution model)
    rw [readData_region members index substitution model pattern] at actual
    exact (point substitution model).mpr actual

omit [DecidableEq O] in
private theorem matching_retarget {s : NativeState S O Γ sort} {first second : Object S}
    (same : first = second) (candidate : Assignment s.infoFrame.arity first.2.arity)
    (pattern : Term (signature S s.infoFrame.arity) Γ sort) (occurrence : O) :
    ContextualConditionalRows.Matches s.locals s.infoFrame.arity (NativePacketRounds.retarget same candidate)
        (instantiate (NativePacketRounds.retarget same candidate) pattern)
        (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows occurrence) ↔
      ContextualConditionalRows.Matches s.locals s.infoFrame.arity candidate (instantiate candidate pattern)
        (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows occurrence) := by
  cases same
  rfl

theorem family_old_iff {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (reader : Fin members.length) (pattern : Term (signature S s.infoFrame.arity) Γ sort)
    (substitution : Substitution S)
    (model : (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Models substitution
      (NativePacketRounds.jointProblem members)) (occurrence : O) :
    rowMatches (NativePacketStep.useObject s (NativePacketRounds.useTag reader)) pattern substitution
        (NativePacketStep.oldRow s 0 occurrence) ↔
      ContextualConditionalRows.Matches s.locals s.infoFrame.arity
        ((NativePacketRounds.readData members substitution model).member reader)
        (instantiate ((NativePacketRounds.readData members substitution model).member reader) pattern)
        (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows occurrence) := by
  have captured := NativePacketRounds.member_models_capture members reader substitution
    (NativePacketRounds.joint_models_member members reader substitution model)
  apply (rowMatches_old_iff s 0 (NativePacketRounds.useTag reader) pattern substitution captured occurrence).trans
  exact (matching_retarget (ContextPackets.capture_targets _ substitution captured)
    (substitution (NativePacketStep.useObject s (NativePacketRounds.useTag reader))).2 pattern occurrence).symm

omit [DecidableEq O] in
theorem fitData_old_iff {s : NativeState S O Γ sort} {members : List (LiveFiring s)} {target : Frames.Frame S}
    (data : FamilyInformation.SolutionData s members target) (reader : Fin members.length)
    (pattern : Term (signature S s.infoFrame.arity) Γ sort) (occurrence : O) :
    rowMatches (NativePacketStep.useObject s (NativePacketRounds.useTag reader)) pattern
        (NativePacketRounds.fitData data) (NativePacketStep.oldRow s 0 occurrence) ↔
      ContextualConditionalRows.Matches s.locals s.infoFrame.arity (data.member reader)
        (instantiate (data.member reader) pattern)
        (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows occurrence) := by
  have actual := rowMatches_old_iff s 0 (NativePacketRounds.useTag reader) pattern
    (NativePacketRounds.fitData data) (NativePacketRounds.fitData_capture data reader) occurrence
  rw [NativePacketRounds.fitData_use data reader] at actual
  exact actual

omit [DecidableEq O] in
theorem fitData_output_iff {s : NativeState S O Γ sort} {members : List (LiveFiring s)} {target : Frames.Frame S}
    (data : FamilyInformation.SolutionData s members target) (reader writer : Fin members.length)
    (pattern : Term (signature S s.infoFrame.arity) Γ sort) (occurrence : O) :
    rowMatches (NativePacketStep.useObject s (NativePacketRounds.useTag reader)) pattern
        (NativePacketRounds.fitData data)
        (NativePacketStep.outputRow members[writer] (NativePacketRounds.useTag writer) occurrence) ↔
      instantiate (data.member reader) pattern = instantiate (data.member writer) (members[writer].outputs occurrence) :=
  rowMatches_output_iff members[writer] _ pattern (NativePacketRounds.useTag writer)
    (NativePacketRounds.fitData data) (0,target) _ _
    (NativePacketRounds.fitData_use data reader) (NativePacketRounds.fitData_use data writer) occurrence

theorem made_label {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (writer : Fin members.length)
    (enabled : Enabled (fun _ : O => ()) s.state.present (members[writer].selection.commit (T := Unit)))
    (occurrence : O) (made : occurrence ∈ members[writer].selection.made)
    (unique : ∀ other : Fin members.length, occurrence ∈ members[other].selection.made → other = writer) :
    NativePacketRounds.label members (.inl occurrence) =
      NativePacketStep.outputRow members[writer] (NativePacketRounds.useTag writer) occurrence := by
  have unpresent : occurrence ∉ s.state.present := fun present =>
    Finset.disjoint_left.mp enabled.fresh (List.mem_toFinset.mpr made) present
  simp only [NativePacketRounds.label,if_neg unpresent,
    NativePacketRounds.owner_unique members occurrence writer made unique]

theorem family_count_ignoresWrites_iff {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (nonempty : members ≠ [])
    (enabled : ∀ index : Fin members.length,
      Enabled (fun _ : O => ()) s.state.present (members[index].selection.commit (T := Unit)))
    (reader writer : Fin members.length)
    (unique : ∀ occurrence ∈ members[writer].selection.made, ∀ other : Fin members.length,
      occurrence ∈ members[other].selection.made → other = writer)
    (pattern : Term (signature S s.infoFrame.arity) Γ sort) (number : Nat) :
    (countQuery (NativePacketStep.useObject s (NativePacketRounds.useTag reader)) pattern number).IgnoresWrites
        (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)) (NativePacketRounds.jointProblem members)
        (NativePacketRounds.label members) (NativePacketStep.selection members[writer]) ↔
      ∀ (target : Frames.Frame S) (data : FamilyInformation.SolutionData s members target),
        (∀ occurrence ∈ members[writer].selection.taken,
          ¬ ContextualConditionalRows.Matches s.locals s.infoFrame.arity (data.member reader)
            (instantiate (data.member reader) pattern)
            (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows occurrence)) ∧
        (∀ occurrence ∈ members[writer].selection.made,
          instantiate (data.member reader) pattern ≠ instantiate (data.member writer) (members[writer].outputs occurrence)) := by
  constructor
  · intro ignored target data
    have model := NativePacketRounds.fitData_joint data nonempty enabled
    refine ⟨?_,?_⟩
    · intro occurrence taken matched
      have written : Sum.inl occurrence ∈ (NativePacketStep.selection members[writer]).taken ++
          (NativePacketStep.selection members[writer]).made :=
        List.mem_append_left _ (List.mem_map_of_mem taken)
      have outside := (region_false_iff _ _ _ _).mp (ignored _ model _ written)
      apply outside
      rw [NativePacketRounds.label_old members occurrence
        ((enabled writer).taken_subset (List.mem_toFinset.mpr taken))]
      exact (fitData_old_iff data reader pattern occurrence).mpr matched
    · intro occurrence made same
      have written : Sum.inl occurrence ∈ (NativePacketStep.selection members[writer]).taken ++
          (NativePacketStep.selection members[writer]).made :=
        List.mem_append_right _ (List.mem_map_of_mem made)
      have outside := (region_false_iff _ _ _ _).mp (ignored _ model _ written)
      apply outside
      rw [made_label members writer (enabled writer) occurrence made (unique occurrence made)]
      exact (fitData_output_iff data reader writer pattern occurrence).mpr same
  · intro ignored substitution model port written
    have mapped : port ∈ (members[writer].selection.taken ++ members[writer].selection.made).map Sum.inl := by
      simpa only [NativePacketStep.selection,List.map_append] using written
    obtain ⟨occurrence,member,rfl⟩ := List.mem_map.mp mapped
    change region (NativePacketStep.useObject s (NativePacketRounds.useTag reader)) pattern substitution
      (NativePacketRounds.label members (.inl occurrence)) = false
    apply (region_false_iff _ _ _ _).mpr
    intro matched
    have native := ignored _ (NativePacketRounds.readData members substitution model)
    rcases List.mem_append.mp member with taken | made
    · rw [NativePacketRounds.label_old members occurrence
        ((enabled writer).taken_subset (List.mem_toFinset.mpr taken))] at matched
      exact native.1 occurrence taken ((family_old_iff members reader pattern substitution model occurrence).mp matched)
    · rw [made_label members writer (enabled writer) occurrence made (unique occurrence made)] at matched
      exact native.2 occurrence made
        ((family_output_iff members reader writer pattern substitution model occurrence).mp matched)

omit [DecidableEq O] in
theorem exact_count_ignoresWrites_iff (site : Object S) (pattern : Term (signature S site.2.arity) Γ sort)
    (seen : Finset (Ports O)) (number : Nat) (problem : EquationStore (Terms S O Γ sort))
    (label : Ports O → Terms S O Γ sort) (writer : Selection (Ports O)) :
    (exactQuery site pattern seen).IgnoresWrites
        (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)) problem label writer ↔
      (countQuery site pattern number).IgnoresWrites
        (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)) problem label writer := Iff.rfl

def equationCheck (site : Object S) (left right : Term (signature S site.2.arity) Γ sort) :
    Check (Terms S O Γ sort) :=
  .equal (ContextPackets.observation site (observe left)) (ContextPackets.observation site (observe right))

omit [DecidableEq O] in
theorem equation_check_iff (site : Object S) (left right : Term (signature S site.2.arity) Γ sort)
    (substitution : Substitution S) (label : Ports O → Terms S O Γ sort) (world : Finset (Ports O)) :
    (equationCheck site left right).Holds (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
        substitution label world ↔
      instantiate (substitution site).2 left = instantiate (substitution site).2 right := by
  change Value.observation (TaggedAssignments.pack (substitution site).1
      (observe (instantiate (substitution site).2 left))) =
    Value.observation (TaggedAssignments.pack (substitution site).1
      (observe (instantiate (substitution site).2 right))) ↔ _
  constructor
  · intro equal
    exact observe_injective (TaggedAssignments.pack_injective (substitution site).1 (Value.observation.inj equal))
  · intro equal
    exact congrArg (fun value : Term (signature S (substitution site).1.2.arity) Γ sort =>
      (Value.observation (TaggedAssignments.pack (substitution site).1 (observe value)) : Terms S O Γ sort)) equal

theorem own_equation_ask_iff {s : NativeState S O Γ sort} (f : LiveFiring s) {base use : Nat}
    (different : base ≠ use)
    (enabled : Enabled (fun _ : O => ()) s.state.present (f.selection.commit (T := Unit)))
    (left right : Term (signature S s.infoFrame.arity) Γ sort) :
    (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Entails
        ((NativePacketStep.selection f).problem (NativePacketStep.label f base use)
          (NativePacketStep.body f use) (NativePacketStep.configuration s base))
        (fun substitution => (equationCheck (NativePacketStep.useObject s use) left right).Holds
          (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)) substitution
          (NativePacketStep.label f base use) (NativePacketStep.present s)) ↔
      ContextualConditionalGuards.Ask s.locals (FamilyInformation.memberInformation f)
        (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows)
        s.state.present (.equal left right) := by
  constructor
  · intro asked Future future candidate model
    let target : Frames.Frame S := ⟨Future,future⟩
    have fitModel := NativePacketStep.model_fit f different enabled target candidate model
    have equal := (equation_check_iff (NativePacketStep.useObject s use) left right
      (NativePacketStep.fit s base use target candidate)
      (NativePacketStep.label f base use) (NativePacketStep.present s)).mp (asked _ fitModel)
    rw [NativePacketStep.fit_use s base use target candidate] at equal
    exact equal
  · intro asked substitution model
    apply (equation_check_iff (NativePacketStep.useObject s use) left right substitution
      (NativePacketStep.label f base use) (NativePacketStep.present s)).mpr
    exact asked _ _ _ (NativePacketStep.model_reads_information f base use substitution model)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.NativePacketQueryView
