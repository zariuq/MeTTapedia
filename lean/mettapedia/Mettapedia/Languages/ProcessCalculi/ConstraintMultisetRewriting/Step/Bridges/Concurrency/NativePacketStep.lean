import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.ContextPackets
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.FamilyInformation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.FirstOrderEq

/-!
# An unguarded native match as an actual program firing

This is a finite symbolic common image. Its physical store is a bag of
occurrences, its commit is one match, its guards are empty, its program is a
fixed singleton, and its knowledge is one store. The row closures retain the
actual schema, latent equations and produced expressions. One extra read-only
row carries the complete captured environment. Each use has a distinct tag.

The admission theorem concerns unguarded live native firings with their real
syntactic shapes. It does not assert a guarded compiler, a round comparison,
or transport of a native solver's returned frame.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.NativePacketStep

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open TaggedAssignments (Object Substitution)
open FamilyInformation (memberInformation)
open ContextPackets (Environment Value)

variable {S : Signature} {O : Type} [DecidableEq O] {Γ : Ctx S} {sort : S.Srt}

structure RowCode (S : Signature) (Γ : Ctx S) (sort : S.Srt) : Type 1 where
  locals : Frames.Frame S
  captures : Frames.Frame S
  row : ContextualConditionalRows.Row locals.arity captures.arity Γ sort

abbrev Rigid (S : Signature) (O : Type) (Γ : Ctx S) (sort : S.Srt) := O × RowCode S Γ sort
abbrev Terms (S : Signature) (O : Type) (Γ : Ctx S) (sort : S.Srt) := Value S (Rigid S O Γ sort)
abbrev Ports (O : Type) := O ⊕ Unit

def baseObject (s : NativeState S O Γ sort) (tag : Nat) : Object S :=
  (tag,⟨s.state.Names,s.state.declarations⟩)

def useObject (s : NativeState S O Γ sort) (tag : Nat) : Object S := (tag,s.infoFrame)

def oldCode (s : NativeState S O Γ sort) (occurrence : O) : RowCode S Γ sort :=
  ⟨⟨s.Local,s.locals⟩,⟨s.state.Names,s.state.declarations⟩,s.state.rows occurrence⟩

def outputCode {s : NativeState S O Γ sort} (f : LiveFiring s) (occurrence : O) : RowCode S Γ sort :=
  ⟨⟨s.Local,s.locals⟩,s.infoFrame,ContextualConditionalRows.ofStored s.locals _ (.shared (f.outputs occurrence))⟩

def oldRow (s : NativeState S O Γ sort) (tag : Nat) (occurrence : O) : Terms S O Γ sort :=
  .row (occurrence,oldCode s occurrence)
    ⟨⟨s.state.Names,s.state.declarations⟩,baseObject s tag,generator s.state.declarations⟩

def readRow (s : NativeState S O Γ sort) (tag : Nat) (occurrence : O) : Terms S O Γ sort :=
  .row (occurrence,oldCode s occurrence)
    ⟨⟨s.state.Names,s.state.declarations⟩,useObject s tag,
      ContextualSelectionViews.capturedTarget s.locals s.state.declarations⟩

def outputRow {s : NativeState S O Γ sort} (f : LiveFiring s) (tag : Nat) (occurrence : O) : Terms S O Γ sort :=
  .row (occurrence,outputCode f occurrence) ⟨s.infoFrame,useObject s tag,generator s.infoFrame.arity⟩

def captureRow (s : NativeState S O Γ sort) (tag : Nat) : Terms S O Γ sort :=
  ContextPackets.capture (source := baseObject s 0) (useObject s tag)
    (ContextualSelectionViews.capturedTarget s.locals s.state.declarations)

def label {s : NativeState S O Γ sort} (f : LiveFiring s) (base use : Nat) : Ports O → Terms S O Γ sort
  | .inl occurrence => if occurrence ∈ f.selection.made then outputRow f use occurrence else oldRow s base occurrence
  | .inr () => ContextPackets.anchor (baseObject s base)

def present (s : NativeState S O Γ sort) : Finset (Ports O) :=
  insert (.inr ()) (s.state.present.image Sum.inl)

def selection {s : NativeState S O Γ sort} (f : LiveFiring s) : Selection (Ports O) :=
  ⟨f.selection.taken.map Sum.inl,f.selection.read.map Sum.inl ++ [.inr ()],f.selection.made.map Sum.inl⟩

def body {s : NativeState S O Γ sort} (f : LiveFiring s) (use : Nat) : RuleInstance (Terms S O Γ sort) :=
  ⟨f.selection.taken.map (readRow s use),f.selection.read.map (readRow s use) ++ [captureRow s use],
    ContextPackets.problem (useObject s use) (memberInformation f),[],f.selection.made.map (outputRow f use)⟩

def configuration (s : NativeState S O Γ sort) (base : Nat) :
    Configuration (Terms S O Γ sort) (Ports O) :=
  ⟨ContextPackets.problem (baseObject s base) s.state.equations,present s⟩

def packetAction := ContextPackets.action S (Rigid S O Γ sort)

def rule {s : NativeState S O Γ sort} (f : LiveFiring s) (use : Nat) :
    RuleSyntax.Rule (RuleSyntax.OneFrame.Terms (Terms S O Γ sort)) :=
  ⟨PUnit.unit,body f use,[]⟩

def program {s : NativeState S O Γ sort} (f : LiveFiring s) (use : Nat) :
    RuleSyntax.Program (RuleSyntax.OneFrame.Terms (Terms S O Γ sort)) := {rule f use}

def firing {s : NativeState S O Γ sort} (f : LiveFiring s) (use : Nat) :
    RuleSyntax.Firing (Ports O) (RuleSyntax.OneFrame.ext (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)))
      (program f use) PUnit.unit :=
  ⟨rule f use,Set.mem_singleton _,PUnit.unit,TaggedAssignments.identity S,selection f,[]⟩

def source {s : NativeState S O Γ sort} (f : LiveFiring s) (base use : Nat) :=
  RuleSyntax.OneFrame.embed (label f base use) (configuration s base)

theorem mem_present_inl (s : NativeState S O Γ sort) (occurrence : O) :
    Sum.inl occurrence ∈ present s ↔ occurrence ∈ s.state.present := by
  simp [present]

theorem selection_enabled {s : NativeState S O Γ sort} (f : LiveFiring s) :
    Enabled (fun _ : Ports O => ()) (present s) ((selection f).commit (T := Unit)) ↔
      Enabled (fun _ : O => ()) s.state.present (f.selection.commit (T := Unit)) := by
  constructor
  · intro enabled
    refine ⟨?_,?_,?_,?_,fun _ inside => by simp [Selection.commit] at inside⟩
    · intro occurrence inside
      apply (mem_present_inl s occurrence).mp
      exact enabled.taken_subset (by simpa [selection,Selection.commit] using inside)
    · intro occurrence inside
      apply (mem_present_inl s occurrence).mp
      exact enabled.kept_subset (by simpa [selection,Selection.commit] using inside)
    · rw [Finset.disjoint_left]
      intro occurrence taken read
      exact Finset.disjoint_left.mp enabled.apart
        (show Sum.inl occurrence ∈ (selection f).commit.taken by simpa [selection,Selection.commit] using taken)
        (show Sum.inl occurrence ∈ (selection f).commit.kept by simpa [selection,Selection.commit] using read)
    · rw [Finset.disjoint_left]
      intro occurrence made old
      exact Finset.disjoint_left.mp enabled.fresh
        (show Sum.inl occurrence ∈ (selection f).commit.made by simpa [selection,Selection.commit] using made)
        ((mem_present_inl s occurrence).mpr old)
  · intro enabled
    refine ⟨?_,?_,?_,?_,fun _ inside => by simp [Selection.commit] at inside⟩
    · intro port inside
      obtain ⟨occurrence,member,rfl⟩ : ∃ occurrence ∈ f.selection.taken, Sum.inl occurrence = port := by
        simpa [selection,Selection.commit] using inside
      exact (mem_present_inl s occurrence).mpr (enabled.taken_subset (List.mem_toFinset.mpr member))
    · intro port inside
      have cases : (∃ occurrence ∈ f.selection.read, Sum.inl occurrence = port) ∨ port = .inr () := by
        simpa [selection,Selection.commit,or_comm] using inside
      rcases cases with ⟨occurrence,member,rfl⟩ | rfl
      · exact (mem_present_inl s occurrence).mpr (enabled.kept_subset (List.mem_toFinset.mpr member))
      · exact Finset.mem_insert_self _ _
    · rw [Finset.disjoint_left]
      intro port taken read
      obtain ⟨occurrence,member,rfl⟩ : ∃ occurrence ∈ f.selection.taken, Sum.inl occurrence = port := by
        simpa [selection,Selection.commit] using taken
      exact Finset.disjoint_left.mp enabled.apart (List.mem_toFinset.mpr member)
        (by simpa [selection,Selection.commit] using read)
    · rw [Finset.disjoint_left]
      intro port made old
      obtain ⟨occurrence,member,rfl⟩ : ∃ occurrence ∈ f.selection.made, Sum.inl occurrence = port := by
        simpa [selection,Selection.commit] using made
      exact Finset.disjoint_left.mp enabled.fresh (List.mem_toFinset.mpr member) ((mem_present_inl s occurrence).mp old)

noncomputable def overwrite (original : Substitution S) (point : Object S)
    (replacement : (target : Object S) × Assignment point.2.arity target.2.arity) : Substitution S := by
  classical
  intro current
  by_cases same : current = point
  · subst current
    exact replacement
  · exact original current

theorem overwrite_at (original : Substitution S) (point : Object S)
    (replacement : (target : Object S) × Assignment point.2.arity target.2.arity) :
    overwrite original point replacement point = replacement := by
  classical
  simp [overwrite]

theorem overwrite_other (original : Substitution S) (point current : Object S)
    (replacement : (target : Object S) × Assignment point.2.arity target.2.arity) (different : current ≠ point) :
    overwrite original point replacement current = original current := by
  classical
  simp [overwrite,different]

omit [DecidableEq O] in
theorem objects_different (s : NativeState S O Γ sort) {base use : Nat} (different : base ≠ use) :
    baseObject s base ≠ useObject s use := fun equal => different (congrArg Prod.fst equal)

def location : Terms S O Γ sort → Option (Object S)
  | .rigid _ => none
  | .observation packed => some packed.1
  | .environment environment => some environment.target
  | .row _ environment => some environment.target

omit [DecidableEq O] in
theorem apply_at (first second : Substitution S) (point : Object S) (equal : first point = second point)
    (term : Terms S O Γ sort) (located : location term = some point) :
    ContextPackets.apply S first term = ContextPackets.apply S second term := by
  cases term with
  | rigid _ => cases located
  | observation packed =>
      obtain ⟨at',observation⟩ := packed
      have same : at' = point := Option.some.inj located
      subst at'
      change Value.observation (TaggedAssignments.pack (first point).1 (instantiateObservation (first point).2 observation)) =
        Value.observation (TaggedAssignments.pack (second point).1 (instantiateObservation (second point).2 observation))
      rw [equal]
  | environment environment =>
      have same : environment.target = point := Option.some.inj located
      subst point
      change Value.environment (Environment.mk environment.domain (first environment.target).1
          (Assignment.compose (first environment.target).2 environment.assignment)) =
        Value.environment (Environment.mk environment.domain (second environment.target).1
          (Assignment.compose (second environment.target).2 environment.assignment))
      rw [equal]
  | row code environment =>
      have same : environment.target = point := Option.some.inj located
      subst point
      change Value.row code (Environment.mk environment.domain (first environment.target).1
          (Assignment.compose (first environment.target).2 environment.assignment)) =
        Value.row code (Environment.mk environment.domain (second environment.target).1
          (Assignment.compose (second environment.target).2 environment.assignment))
      rw [equal]

theorem label_location {s : NativeState S O Γ sort} (f : LiveFiring s) (base use : Nat)
    (enabled : Enabled (fun _ : O => ()) s.state.present (f.selection.commit (T := Unit)))
    (port : Ports O) (inside : port ∈ present s) :
    location (label f base use port) = some (baseObject s base) := by
  cases port with
  | inl occurrence =>
      have old := (mem_present_inl s occurrence).mp inside
      have notMade : occurrence ∉ f.selection.made := fun made =>
        Finset.disjoint_left.mp enabled.fresh (List.mem_toFinset.mpr made) old
      simp [label,notMade,oldRow,location]
  | inr token => cases token; rfl

omit [DecidableEq O] in
theorem problem_locations (point : Object S) (equations : ContextualResidual.Problem point.2.arity)
    (equation : Terms S O Γ sort × Terms S O Γ sort)
    (inside : equation ∈ ContextPackets.problem point equations) :
    location equation.1 = some point ∧ location equation.2 = some point := by
  obtain ⟨original,_,rfl⟩ := List.mem_map.mp inside
  exact ⟨rfl,rfl⟩

theorem source_location {s : NativeState S O Γ sort} (f : LiveFiring s) (base use : Nat)
    (enabled : Enabled (fun _ : O => ()) s.state.present (f.selection.commit (T := Unit)))
    (term : Terms S O Γ sort) (inside : (source f base use).Mentions term) :
    location term = some (baseObject s base) := by
  rcases inside with known | known | ⟨port,present,equal⟩
  · obtain ⟨equation,member,rfl⟩ := List.mem_map.mp known
    exact (problem_locations _ _ equation member).1
  · obtain ⟨equation,member,rfl⟩ := List.mem_map.mp known
    exact (problem_locations _ _ equation member).2
  · rw [← equal]
    exact label_location f base use enabled port present

omit [DecidableEq O] in
theorem rule_location {s : NativeState S O Γ sort} (f : LiveFiring s) (use : Nat) :
    ∀ term ∈ (rule f use).terms, location term = some (useObject s use) := by
  intro term inside
  simp only [rule,RuleSyntax.Rule.terms,body,List.mem_append] at inside
  rcases inside with ((((((taken | read) | toldLeft) | toldRight) | checked) | made) | collect)
  · obtain ⟨_,_,rfl⟩ := List.mem_map.mp taken
    rfl
  · rcases read with read | anchor
    · obtain ⟨_,_,rfl⟩ := List.mem_map.mp read
      rfl
    · obtain rfl := List.mem_singleton.mp anchor
      rfl
  · obtain ⟨equation,member,rfl⟩ := List.mem_map.mp toldLeft
    exact (problem_locations _ _ equation member).1
  · obtain ⟨equation,member,rfl⟩ := List.mem_map.mp toldRight
    exact (problem_locations _ _ equation member).2
  · cases checked
  · obtain ⟨_,_,rfl⟩ := List.mem_map.mp made
    rfl
  · cases collect

theorem fresh {s : NativeState S O Γ sort} (f : LiveFiring s) {base use : Nat} (different : base ≠ use)
    (enabled : Enabled (fun _ : O => ()) s.state.present (f.selection.commit (T := Unit))) :
    (firing f use).Fresh (RuleSyntax.OneFrame.frames (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)))
      (source f base use) := by
  intro _ old ruleModel
  let joint := overwrite old (useObject s use) (ruleModel (useObject s use))
  refine ⟨joint,?_,?_⟩
  · intro term inside
    change ContextPackets.apply S joint (ContextPackets.apply S (TaggedAssignments.identity S) term) =
      ContextPackets.apply S old term
    rw [show ContextPackets.apply S (TaggedAssignments.identity S) term = term from
      (ContextPackets.action S (Rigid S O Γ sort)).apply_identity term]
    exact apply_at joint old (baseObject s base)
      (overwrite_other old (useObject s use) (baseObject s base) _ (objects_different s different))
      term (source_location f base use enabled term inside)
  · intro term inside
    change ContextPackets.apply S joint (ContextPackets.apply S (TaggedAssignments.identity S) term) =
      ContextPackets.apply S ruleModel term
    rw [show ContextPackets.apply S (TaggedAssignments.identity S) term = term from
      (ContextPackets.action S (Rigid S O Γ sort)).apply_identity term]
    exact apply_at joint ruleModel (useObject s use) (overwrite_at old (useObject s use) _)
      term (rule_location f use term inside)

omit [DecidableEq O] in
theorem opened_eq {s : NativeState S O Γ sort} (f : LiveFiring s) (use : Nat) :
    (firing f use).opened (RuleSyntax.OneFrame.frames (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))) =
      body f use := by
  change (body f use).map ((ContextPackets.action S (Rigid S O Γ sort)).apply (TaggedAssignments.identity S)) = _
  have identity : (ContextPackets.action S (Rigid S O Γ sort)).apply (TaggedAssignments.identity S) = id :=
    funext (ContextPackets.action S (Rigid S O Γ sort)).apply_identity
  rw [identity]
  simp [body,RuleInstance.map]

theorem keeps_labels {s : NativeState S O Γ sort} (f : LiveFiring s) (base use : Nat) :
    (selection f).made.map (label f base use) = (body f use).produce := by
  change (f.selection.made.map Sum.inl).map (label f base use) = f.selection.made.map (outputRow f use)
  rw [List.map_map]
  exact List.map_congr_left fun occurrence member => by simp [label,member]

noncomputable def fit (s : NativeState S O Γ sort) (base use : Nat) (target : Frames.Frame S)
    (candidate : Assignment s.infoFrame.arity target.arity) : Substitution S :=
  overwrite (TaggedAssignments.single (baseObject s base) (0,target)
      (Assignment.compose candidate (ContextualSelectionViews.capturedTarget s.locals s.state.declarations)))
    (useObject s use) ⟨(0,target),candidate⟩

omit [DecidableEq O] in
theorem fit_use (s : NativeState S O Γ sort) (base use : Nat) (target : Frames.Frame S)
    (candidate : Assignment s.infoFrame.arity target.arity) :
    fit s base use target candidate (useObject s use) = ⟨(0,target),candidate⟩ :=
  overwrite_at _ _ _

omit [DecidableEq O] in
theorem fit_base (s : NativeState S O Γ sort) {base use : Nat} (different : base ≠ use)
    (target : Frames.Frame S) (candidate : Assignment s.infoFrame.arity target.arity) :
    fit s base use target candidate (baseObject s base) =
      ⟨(0,target),Assignment.compose candidate (ContextualSelectionViews.capturedTarget s.locals s.state.declarations)⟩ :=
  (overwrite_other _ _ _ _ (objects_different s different)).trans (TaggedAssignments.single_at _ _ _)

omit [DecidableEq O] in
theorem fit_capture (s : NativeState S O Γ sort) {base use : Nat} (different : base ≠ use)
    (target : Frames.Frame S) (candidate : Assignment s.infoFrame.arity target.arity) :
    (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Solves (fit s base use target candidate)
      (captureRow s use,ContextPackets.anchor (baseObject s base)) := by
  apply (ContextPackets.capture_solution (source := baseObject s base) (target := useObject s use)
    (ContextualSelectionViews.capturedTarget s.locals s.state.declarations) _).mpr
  rw [fit_use,fit_base s different]
  rfl

omit [DecidableEq O] in
theorem read_row_solved (s : NativeState S O Γ sort) (base use : Nat) (substitution : Substitution S)
    (captured : (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Solves substitution
      (captureRow s use,ContextPackets.anchor (baseObject s base))) (occurrence : O) :
    ContextPackets.apply S substitution (readRow s use occurrence) =
      ContextPackets.apply S substitution (oldRow s base occurrence) := by
  have equal := (ContextPackets.capture_solution (source := baseObject s base) (target := useObject s use)
    (ContextualSelectionViews.capturedTarget s.locals s.state.declarations) substitution).mp captured
  change Value.row (occurrence,oldCode s occurrence)
      (Environment.mk (baseObject s base).2 (substitution (useObject s use)).1
        (Assignment.compose (substitution (useObject s use)).2
          (ContextualSelectionViews.capturedTarget s.locals s.state.declarations))) =
    Value.row (occurrence,oldCode s occurrence)
      (Environment.mk (baseObject s base).2 (substitution (baseObject s base)).1
        (Assignment.compose (substitution (baseObject s base)).2 (generator (baseObject s base).2.arity)))
  rw [Assignment.compose_identity_right]
  exact congrArg (Value.row (occurrence,oldCode s occurrence)) equal

private theorem models_mapped {T U V W : Type*} (A : SubstitutionAction T U) (candidate : U)
    (label : W → T) (pattern : V → T) (selected : V → W) : ∀ values : List V,
    A.Models candidate (Selection.equations label (values.map pattern) (values.map selected)) ↔
      ∀ value ∈ values, A.Solves candidate (pattern value,label (selected value))
  | [] => by simp [Selection.equations]
  | value :: rest => by
      simp only [Selection.equations,List.map_cons,List.zipWith_cons_cons,
        SubstitutionAction.models_cons,List.forall_mem_cons]
      exact and_congr Iff.rfl (models_mapped A candidate label pattern selected rest)

private theorem equations_read_append {T V W : Type*} (label : W → T) (pattern : V → T) (selected : V → W)
    (lastPattern : T) (lastSelected : W) : ∀ values : List V,
    Selection.equations label (values.map pattern ++ [lastPattern]) (values.map selected ++ [lastSelected]) =
      Selection.equations label (values.map pattern) (values.map selected) ++ [(lastPattern,label lastSelected)]
  | [] => rfl
  | value :: rest => by
      simpa only [Selection.equations,List.map_cons,List.cons_append,List.zipWith_cons_cons,List.cons.injEq,true_and] using
        equations_read_append label pattern selected lastPattern lastSelected rest

theorem model_reads_information {s : NativeState S O Γ sort} (f : LiveFiring s) (base use : Nat)
    (substitution : Substitution S)
    (model : (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Models substitution
      ((selection f).problem (label f base use) (body f use) (configuration s base))) :
    ContextualResidual.Models (substitution (useObject s use)).2 (memberInformation f) := by
  apply (ContextPackets.models_problem substitution (useObject s use) (memberInformation f)).mp
  intro equation inside
  exact model equation (List.mem_append_right _ inside)

theorem model_fit {s : NativeState S O Γ sort} (f : LiveFiring s) {base use : Nat} (different : base ≠ use)
    (enabled : Enabled (fun _ : O => ()) s.state.present (f.selection.commit (T := Unit)))
    (target : Frames.Frame S) (candidate : Assignment s.infoFrame.arity target.arity)
    (solved : ContextualResidual.Models candidate (memberInformation f)) :
    (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Models (fit s base use target candidate)
      ((selection f).problem (label f base use) (body f use) (configuration s base)) := by
  let substitution := fit s base use target candidate
  have captured := fit_capture s different target candidate
  have unmade : ∀ occurrence ∈ f.selection.taken ++ f.selection.read, occurrence ∉ f.selection.made := by
    intro occurrence member made
    have old : occurrence ∈ s.state.present := by
      rcases List.mem_append.mp member with taken | read
      · exact enabled.taken_subset (List.mem_toFinset.mpr taken)
      · exact enabled.kept_subset (List.mem_toFinset.mpr read)
    exact Finset.disjoint_left.mp enabled.fresh (List.mem_toFinset.mpr made) old
  have rowSolved : ∀ occurrence ∈ f.selection.taken ++ f.selection.read,
      (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Solves substitution
        (readRow s use occurrence,label f base use (.inl occurrence)) := by
    intro occurrence member
    rw [label,if_neg (unmade occurrence member)]
    exact read_row_solved s base use substitution captured occurrence
  simp only [Selection.problem,SubstitutionAction.models_append]
  refine ⟨⟨⟨?old,?take⟩,?read⟩,?tell⟩
  case old =>
    apply (ContextPackets.models_problem substitution (baseObject s base) s.state.equations).mpr
    change ContextualResidual.Models (fit s base use target candidate (baseObject s base)).2 s.state.equations
    rw [fit_base s different]
    exact ((NativeResidual.models_problemOf_iff f.selection f.rule candidate).mp solved).1
  case take =>
    apply (models_mapped _ substitution (label f base use) (readRow s use) Sum.inl f.selection.taken).mpr
    intro occurrence member
    exact rowSolved occurrence (List.mem_append_left _ member)
  case read =>
    change (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Models substitution
      (Selection.equations (label f base use) (f.selection.read.map (readRow s use) ++ [captureRow s use])
        (f.selection.read.map Sum.inl ++ [.inr ()]))
    rw [equations_read_append,SubstitutionAction.models_append]
    refine ⟨?_,?_⟩
    · apply (models_mapped _ substitution (label f base use) (readRow s use) Sum.inl f.selection.read).mpr
      intro occurrence member
      exact rowSolved occurrence (List.mem_append_right _ member)
    · intro equation member
      obtain rfl := List.mem_singleton.mp member
      exact captured
  case tell =>
    apply (ContextPackets.models_problem substitution (useObject s use) (memberInformation f)).mpr
    change ContextualResidual.Models (fit s base use target candidate (useObject s use)).2 (memberInformation f)
    rw [fit_use]
    exact solved

theorem model_reads_capture {s : NativeState S O Γ sort} (f : LiveFiring s) (base use : Nat)
    (substitution : Substitution S)
    (model : (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Models substitution
      ((selection f).problem (label f base use) (body f use) (configuration s base))) :
    (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Solves substitution
      (captureRow s use,ContextPackets.anchor (baseObject s base)) := by
  have readModel : (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Models substitution
      (Selection.equations (label f base use) (f.selection.read.map (readRow s use) ++ [captureRow s use])
        (f.selection.read.map Sum.inl ++ [.inr ()])) := by
    intro equation inside
    exact model equation (List.mem_append_left _ (List.mem_append_right _ inside))
  rw [equations_read_append,SubstitutionAction.models_append] at readModel
  exact readModel.2 _ List.mem_cons_self

theorem entails_information_iff {s : NativeState S O Γ sort} (f : LiveFiring s) {base use : Nat}
    (different : base ≠ use)
    (enabled : Enabled (fun _ : O => ()) s.state.present (f.selection.commit (T := Unit)))
    (observation : (target : Frames.Frame S) → Assignment s.infoFrame.arity target.arity → Prop) :
    (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Entails
        ((selection f).problem (label f base use) (body f use) (configuration s base))
        (fun substitution => observation (substitution (useObject s use)).1.2 (substitution (useObject s use)).2) ↔
      (Frames.contextual S).Entails (memberInformation f) observation := by
  constructor
  · intro asked target candidate model
    have holds := asked _ (model_fit f different enabled target candidate model)
    dsimp only at holds
    rw [fit_use] at holds
    exact holds
  · intro asked substitution model
    exact asked _ _ (model_reads_information f base use substitution model)

theorem fire_present {s : NativeState S O Γ sort} (f : LiveFiring s) :
    fire (present s) ((selection f).commit (T := Unit)) =
      insert (.inr ()) ((fire s.state.present (f.selection.commit (T := Unit))).image Sum.inl) := by
  ext port
  cases port with
  | inl occurrence => simp [mem_fire,present,selection,Selection.commit]
  | inr token => cases token; simp [mem_fire,present,selection,Selection.commit]

def baseFiring {s : NativeState S O Γ sort} (f : LiveFiring s) (use : Nat) :
    AnnotatedRuns.Firing (Terms S O Γ sort) (Substitution S) (Ports O) :=
  AnnotatedRuns.Firing.ofPlain (body f use,selection f)

variable [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

theorem native_unguarded_iff {s : NativeState S O Γ sort} (f : LiveFiring s)
    (shapes : native.Shapes f.toNative) (noChecks : f.rule.checks = []) (noQueries : f.patterns = []) :
    f.toNative.Realized ↔
      Enabled (fun _ : O => ()) s.state.present (f.selection.commit (T := Unit)) ∧
        (Frames.contextual S).Solvable (a := s.infoFrame) (memberInformation f) := by
  have checks : f.toNative.prepared.rule.checks = [] := by
    change f.rule.checks.map _ = []
    rw [noChecks]
    rfl
  have queries : f.toNative.queries = [] := by
    change f.patterns.map _ = []
    rw [noQueries]
    rfl
  constructor
  · intro admitted
    have data := (native_admits_iff f.toNative).mp admitted
    exact ⟨data.2.1,data.2.2.1⟩
  · rintro ⟨enabled,solvable⟩
    apply (native_admits_iff f.toNative).mpr
    refine ⟨shapes,enabled,solvable,?_⟩
    intro target candidate _
    refine ⟨?_,?_⟩
    · intro check member
      rw [checks] at member
      cases member
    · intro query member
      rw [queries] at member
      cases member

theorem base_valid_iff {s : NativeState S O Γ sort} (f : LiveFiring s) {base use : Nat} (different : base ≠ use)
    (shapes : native.Shapes f.toNative) (noChecks : f.rule.checks = []) (noQueries : f.patterns = []) :
    (baseFiring f use).Valid (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
      (label f base use) (configuration s base) ↔ f.toNative.Realized := by
  change (AnnotatedRuns.Firing.ofPlain (body f use,selection f)).Valid _ _ _ ↔ _
  rw [AnnotatedRuns.Firing.valid_ofPlain_iff]
  constructor
  · intro valid
    apply (native_unguarded_iff f shapes noChecks noQueries).mpr
    have enabled : Enabled (fun _ : Ports O => ()) (present s) ((selection f).commit (T := Unit)) :=
      ⟨valid.occurrences.taken_subset,valid.occurrences.kept_subset,valid.occurrences.apart,valid.occurrences.fresh,
        fun _ member => by simp [Selection.commit] at member⟩
    obtain ⟨substitution,model⟩ := valid.consistent
    exact ⟨(selection_enabled f).mp enabled,
      ⟨(substitution (useObject s use)).1.2,(substitution (useObject s use)).2,
        model_reads_information f base use substitution model⟩⟩
  · intro realized
    obtain ⟨enabled,⟨target,candidate,model⟩⟩ := (native_unguarded_iff f shapes noChecks noQueries).mp realized
    have packetEnabled := (selection_enabled f).mpr enabled
    refine ⟨?_,?_,?_,?_,keeps_labels f base use,?_,?_,?_⟩
    · exact shapes.1.map Sum.inl_injective
    · exact shapes.2.1.map Sum.inl_injective
    · simp [body,selection]
    · simp [body,selection]
    · exact ⟨packetEnabled.taken_subset,packetEnabled.kept_subset,packetEnabled.apart,packetEnabled.fresh,
        fun _ member => by simp [Selection.commit] at member⟩
    · exact ⟨fit s base use target candidate,model_fit f different enabled target candidate model⟩
    · intro check member
      cases member

omit [DecidableEq O] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem image_eq {s : NativeState S O Γ sort} (f : LiveFiring s) (use : Nat) :
    RuleSyntax.OneFrame.toFirstOrder (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
      (program f use) (firing f use) = baseFiring f use := by
  unfold RuleSyntax.OneFrame.toFirstOrder
  rw [opened_eq]
  rfl

theorem unguarded_admission_iff {s : NativeState S O Γ sort} (f : LiveFiring s) {base use : Nat}
    (different : base ≠ use) (shapes : native.Shapes f.toNative)
    (noChecks : f.rule.checks = []) (noQueries : f.patterns = []) :
    (RuleSyntax.step (RuleSyntax.OneFrame.frames (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)))
        (Ports O) (RuleSyntax.OneFrame.ext (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)))
        (program f use)).Admits (s := source f base use) (firing f use) ↔ f.toNative.Realized := by
  have keeping : (firing f use).selection.made.map (label f base use) =
      ((firing f use).opened (RuleSyntax.OneFrame.frames
        (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)))).produce := by
    rw [opened_eq]
    exact keeps_labels f base use
  have comparison := RuleSyntax.OneFrame.admits_toFirstOrder_iff (configuration s base) (firing f use)
    (A := packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)) (label := label f base use)
  constructor
  · intro admitted
    have baseAdmitted := (comparison.mp ⟨admitted,keeping⟩).1
    rw [image_eq] at baseAdmitted
    exact (base_valid_iff f different shapes noChecks noQueries).mp baseAdmitted
  · intro realized
    have valid := (base_valid_iff f different shapes noChecks noQueries).mpr realized
    have enabled := ((native_admits_iff f.toNative).mp realized).2.1
    apply (comparison.mpr ?_).1
    refine ⟨?_,fresh f different enabled,rfl⟩
    rw [image_eq]
    exact valid

theorem result_present {s : NativeState S O Γ sort} (f : LiveFiring s) (base use : Nat)
    (realized : f.toNative.Realized) :
    ((firing f use).result (RuleSyntax.OneFrame.frames
      (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))) (source f base use)).present =
      insert (.inr ()) ((native.result f.toNative realized).state.present.image Sum.inl) := by
  have nativePresent := native.toStep.present_result f.toNative realized
  change (native.result f.toNative realized).state.present =
    fire s.state.present (f.selection.commit (T := Unit)) at nativePresent
  rw [nativePresent]
  exact fire_present f

omit [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem result_labels {s : NativeState S O Γ sort} (f : LiveFiring s) (base use : Nat) :
    ((firing f use).result (RuleSyntax.OneFrame.frames
      (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))) (source f base use)).label = label f base use := by
  have keeping : (firing f use).selection.made.map (label f base use) =
      ((firing f use).opened (RuleSyntax.OneFrame.frames
        (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)))).produce := by
    rw [opened_eq]
    exact keeps_labels f base use
  change RuleSyntax.relabel ((firing f use).row (RuleSyntax.OneFrame.frames
      (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))) (source f base use))
    (firing f use).selection.made
    ((firing f use).opened (RuleSyntax.OneFrame.frames
      (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)))).produce = _
  have rowEqual : (firing f use).row (RuleSyntax.OneFrame.frames
      (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))) (source f base use) = label f base use :=
    RuleSyntax.OneFrame.row_eq (configuration s base) (firing f use) (label := label f base use)
  rw [rowEqual,← keeping]
  exact RuleSyntax.OneFrame.relabel_map_self (label f base use) (firing f use).selection.made

omit [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem result_output {s : NativeState S O Γ sort} (f : LiveFiring s) (base use : Nat)
    (occurrence : O) (made : occurrence ∈ f.selection.made) :
    ((firing f use).result (RuleSyntax.OneFrame.frames
      (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))) (source f base use)).label (.inl occurrence) =
      outputRow f use occurrence := by
  rw [result_labels]
  simp [label,made]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.NativePacketStep
