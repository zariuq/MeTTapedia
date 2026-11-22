import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NativeFieldMeaning

/-!
# Native field schemas as actual fresh occurrence firings

A prepared snapshot has ten field occurrences and one witness certificate.
The canonical opening is fresh. Written fields are taken and replaced at a
fresh generation; unchanged fields and the certificate are retained. These
generation numbers are logical occurrence identities.

The values and guards inhabit the received source model. Array layouts,
word operations and preparation by a particular native consumer remain
separate implementation obligations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeFieldExecution

open Mettapedia.Logic Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open NativeClauseData NativeFieldSchema InterpretedFrames
open DefinitionAdapters
open MeTTaCalculus.OccurrenceCommits (Enabled)

universe w

noncomputable def sourceDomains {initial context : TheoryContext} {policy : AxiomPolicy}
    {cache : Array Theorem}
    (frame : RegisteredReplayModels.Frame.{w} initial policy context cache)
    (other : TypeFamilySemantics.OperatorFamilies.{w})
    (assignment : TypeFamilySemantics.Assignment.{w}) :
    (frame.model other assignment).InhabitedDomains := by
  apply (frame.model other assignment).inhabitedDomains_of_fullDomains
    (frame.model_fullDomains other assignment)
  intro atomic
  change (frame.family.model other assignment).Carrier atomic
  rw [frame.family.carrier]
  exact (TypeFamilySemantics.evaluate
    (TypeFamilySemantics.primitiveFamilies (frame.family.operators other)) assignment
    atomic.val).inhabitant

abbrev Occurrence := (Field × Nat) ⊕ Unit

def certificate : Occurrence := .inr ()

def row (generation : Field → Nat) (field : Field) : Occurrence :=
  .inl (field, generation field)

def nextRow (generation : Field → Nat) (field : Field) : Occurrence :=
  .inl (field, generation field + 1)

theorem row_injective (generation : Field → Nat) : Function.Injective (row generation) :=
  fun _ _ same => congrArg Prod.fst (Sum.inl.inj same)

theorem nextRow_injective (generation : Field → Nat) : Function.Injective (nextRow generation) :=
  fun _ _ same => congrArg Prod.fst (Sum.inl.inj same)

theorem field_member (field : Field) : field ∈ Field.all := by
  cases field <;> simp [Field.all]

def present (generation : Field → Nat) : Finset Occurrence :=
  insert certificate (Field.all.toFinset.image (row generation))

def selection {ops : Operations} (spec : Syntax ops) (generation : Field → Nat) :
    Selection Occurrence where
  taken := spec.writes.map (row generation)
  read := spec.reads.map (row generation)
  made := spec.writes.map (nextRow generation)

theorem row_present (generation : Field → Nat) (field : Field) :
    row generation field ∈ present generation :=
  Finset.mem_insert_of_mem (Finset.mem_image.mpr
    ⟨field, List.mem_toFinset.mpr (field_member field), rfl⟩)

theorem read_not_written {ops : Operations} (spec : Syntax ops) (field : Field)
    (read : field ∈ spec.reads) : field ∉ spec.writes := by
  simpa only [decide_eq_true_eq] using (List.mem_filter.mp read).2

theorem physical_enabled {ops : Operations} (spec : Syntax ops) (generation : Field → Nat) :
    Enabled (fun _ : Occurrence => ()) (present generation)
      ((PreparedRules.Schema.selected certificate (selection spec generation)).commit (T := Unit)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change (spec.writes.map (row generation)).toFinset ⊆ present generation
    intro occurrence member
    obtain ⟨field, _, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
    exact row_present generation field
  · change (certificate :: spec.reads.map (row generation)).toFinset ⊆ present generation
    intro occurrence member
    rcases List.mem_cons.mp (List.mem_toFinset.mp member) with same | member
    · subst occurrence
      exact Finset.mem_insert_self _ _
    · obtain ⟨field, _, rfl⟩ := List.mem_map.mp member
      exact row_present generation field
  · change Disjoint (spec.writes.map (row generation)).toFinset
      (certificate :: spec.reads.map (row generation)).toFinset
    apply Finset.disjoint_left.mpr
    intro occurrence taken read
    obtain ⟨field, written, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp taken)
    rcases List.mem_cons.mp (List.mem_toFinset.mp read) with same | read
    · cases same
    · obtain ⟨other, read, same⟩ := List.mem_map.mp read
      have sameField := row_injective generation same
      subst other
      exact read_not_written spec field read written
  · change Disjoint (spec.writes.map (nextRow generation)).toFinset (present generation)
    apply Finset.disjoint_left.mpr
    intro occurrence made old
    obtain ⟨field, _, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp made)
    rcases Finset.mem_insert.mp old with same | old
    · cases same
    · obtain ⟨other, _, same⟩ := Finset.mem_image.mp old
      have sameField := congrArg Prod.fst (Sum.inl.inj same)
      change other = field at sameField
      subst other
      have impossible := congrArg Prod.snd (Sum.inl.inj same)
      change generation field = generation field + 1 at impossible
      omega
  · intro query member
    cases member

variable {ops : Operations} (table : Fin 29 → Syntax ops)
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (domains : model.InhabitedDomains) (index : Fin 29)

def snapshot (values : model.Valuation ((table index).locals.map Ty.toHOL))
    (generation : Field → Nat) : RuleSyntax.State (Terms (Value table model)) Occurrence where
  frame := ground.{w+1}
  knowledge := []
  present := present generation
  label occurrence _ :=
    match occurrence with
    | .inl (field, _) => cell table model (table index).before field values
    | .inr _ => (schema table model domains index).certificate values

def firing (generation : Field → Nat) :
    RuleSyntax.Firing Occurrence extensions (program table model domains) ground.{w+1} :=
  (schema table model domains index).firing (rule_member table model domains index)
    certificate (selection (table index) generation)

theorem matches_snapshot
    (values : model.Valuation ((table index).locals.map Ty.toHOL))
    (generation : Field → Nat) (fields : List Field) :
    PreparedRules.Matches (locals := localFrame table model domains index)
      (fields.map (cell table model (table index).before))
      (fields.map (row generation))
      (fun occurrence => (snapshot table model domains index values generation).label
        occurrence PUnit.unit) values := by
  induction fields with
  | nil => simp [PreparedRules.Matches]
  | cons field later ih =>
      simpa [PreparedRules.Matches, snapshot, row] using ih

/-- Every physical and matching premise is discharged by the constructed
snapshot and selection. Admission depends on the source guard at the
prepared witness, while the opening itself remains fresh. -/
theorem admitted_iff
    (values : model.Valuation ((table index).locals.map Ty.toHOL))
    (generation : Field → Nat) :
    (RuleSyntax.step (frames (Value table model)) Occurrence extensions
      (program table model domains)).Admits
      (s := snapshot table model domains index values generation)
      (firing table model domains index generation) ↔
      (model.denote (table index).guard values).down := by
  change (RuleSyntax.step (frames (Value table model)) Occurrence extensions
    (program table model domains)).Admits
      ((schema table model domains index).firing (rule_member table model domains index)
        certificate (selection (table index) generation)) ↔ _
  rw [PreparedRules.admitted_iff (schema table model domains index)
    (rule_member table model domains index)
    (snapshot table model domains index values generation) certificate
    (selection (table index) generation) values (fun _ => rfl)]
  constructor
  · intro admitted
    exact admitted.2.2.2.2.2.2.2
  · intro guard
    refine ⟨(table index).writes_distinct.map (row_injective generation),
      (table index).writes_distinct.map (nextRow_injective generation), ?_, ?_, ?_,
      physical_enabled (table index) generation,
      ⟨PUnit.unit, ?_, matches_snapshot table model domains index values generation _,
        matches_snapshot table model domains index values generation _⟩, guard⟩
    · simp [schema, selection]
    · simp [schema, selection]
    · simp [schema, selection]
    · intro equation member
      cases member

theorem guard_refused
    (values : model.Valuation ((table index).locals.map Ty.toHOL))
    (generation : Field → Nat)
    (refused : ¬ (model.denote (table index).guard values).down) :
    ¬ (RuleSyntax.step (frames (Value table model)) Occurrence extensions
      (program table model domains)).Admits
      (s := snapshot table model domains index values generation)
      (firing table model domains index generation) :=
  fun admitted => refused ((admitted_iff table model domains index values generation).mp admitted)

def withoutCertificate
    (values : model.Valuation ((table index).locals.map Ty.toHOL))
    (generation : Field → Nat) : RuleSyntax.State (Terms (Value table model)) Occurrence :=
  { snapshot table model domains index values generation with
    present := (present generation).erase certificate }

theorem missing_certificate_refused
    (values : model.Valuation ((table index).locals.map Ty.toHOL))
    (generation : Field → Nat) :
    ¬ (RuleSyntax.step (frames (Value table model)) Occurrence extensions
      (program table model domains)).Admits
      (s := withoutCertificate table model domains index values generation)
      (firing table model domains index generation) := by
  intro admitted
  have selected : certificate ∈
      ((firing table model domains index generation).selection.commit (T := Unit)).kept := by
    change certificate ∈ (certificate :: _).toFinset
    exact List.mem_toFinset.mpr List.mem_cons_self
  have inside := admitted.2.1.kept_subset selected
  simp [withoutCertificate] at inside

def outputRow (generation : Field → Nat) (field : Field) : Occurrence :=
  if field ∈ (table index).writes then nextRow generation field else row generation field

theorem output_present
    (values : model.Valuation ((table index).locals.map Ty.toHOL))
    (generation : Field → Nat) (field : Field) :
    outputRow table index generation field ∈
      ((firing table model domains index generation).result (frames (Value table model))
        (snapshot table model domains index values generation)).present := by
  change outputRow table index generation field ∈
    (present generation \ ((table index).writes.map (row generation)).toFinset) ∪
      ((table index).writes.map (nextRow generation)).toFinset
  by_cases written : field ∈ (table index).writes
  · rw [outputRow, if_pos written]
    exact Finset.mem_union_right _ (List.mem_toFinset.mpr
      (List.mem_map.mpr ⟨field, written, rfl⟩))
  · rw [outputRow, if_neg written]
    apply Finset.mem_union_left
    refine Finset.mem_sdiff.mpr ⟨row_present generation field, ?_⟩
    intro taken
    obtain ⟨other, member, same⟩ := List.mem_map.mp (List.mem_toFinset.mp taken)
    exact written ((row_injective generation same) ▸ member)

theorem result_readout
    (values : model.Valuation ((table index).locals.map Ty.toHOL))
    (generation : Field → Nat)
    (admitted : (RuleSyntax.step (frames (Value table model)) Occurrence extensions
      (program table model domains)).Admits
      (s := snapshot table model domains index values generation)
      (firing table model domains index generation))
    (environment : (extend ground.{w+1} (localFrame table model domains index)).Carrier)
    (satisfies : Satisfies
      ((firing table model domains index generation).result (frames (Value table model))
        (snapshot table model domains index values generation)).knowledge environment)
    (field : Field) :
    ((firing table model domains index generation).result (frames (Value table model))
      (snapshot table model domains index values generation)).label
        (outputRow table index generation field) environment =
      cell table model (table index).after field values := by
  by_cases written : field ∈ (table index).writes
  · rw [outputRow, if_pos written]
    apply PreparedRules.produced_readout (schema table model domains index)
      (rule_member table model domains index)
      (snapshot table model domains index values generation) certificate
      (selection (table index) generation) values (fun _ => rfl) admitted
      (nextRow generation field) (cell table model (table index).after field)
    · change (nextRow generation field,
        fun (environment : (extend ground.{w+1} (localFrame table model domains index)).Carrier) =>
          cell table model (table index).after field environment.2) ∈
        ((table index).writes.map (nextRow generation)).zip
          (((table index).writes.map (cell table model (table index).after)).map
            (fun term (environment : (extend ground.{w+1} (localFrame table model domains index)).Carrier) =>
              term environment.2))
      rw [List.map_map, List.zip_map']
      exact List.mem_map.mpr ⟨field, written, rfl⟩
    · exact satisfies
  · rw [outputRow, if_neg written]
    have absent : row generation field ∉ (selection (table index) generation).made := by
      intro made
      obtain ⟨other, _, same⟩ := List.mem_map.mp made
      have sameField := congrArg Prod.fst (Sum.inl.inj same)
      change other = field at sameField
      subst other
      have impossible := congrArg Prod.snd (Sum.inl.inj same)
      change generation field + 1 = generation field at impossible
      omega
    calc
      _ = (snapshot table model domains index values generation).label
          (row generation field) environment.1 := by
        exact PreparedRules.other_readout (schema table model domains index)
          (rule_member table model domains index)
          (snapshot table model domains index values generation) certificate
          (selection (table index) generation) (row generation field) absent environment
      _ = _ := by
        change cell table model (table index).before field values =
          cell table model (table index).after field values
        simp only [cell, (table index).unchanged field written]

open NativeClauseReadback ProofExecution TypeFamilySemantics in
/-- A received native step has exactly a prepared field firing with the
same pre-state, record and post-state. Preparing a subsequent certificate
and composing the resulting extended states require a separate run contract. -/
theorem received_prepared_firing (logical : NativeFieldMeaning.LogicalOperations ops)
    (commands : List Registered.Command) (state : Registered.State)
    (accepted : Registered.replayFrom SourceProfileModels.policy
      (Registered.empty SourceProfile.primitiveContext) commands = some state)
    (reading : Reading (signature ops) (NativeFieldMeaning.clauses table) state)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    (generation : Field → Nat) :
    let model := (SourceProfileModels.sourceReplayFrame commands state accepted).frame.model other assignment
    let domains := sourceDomains (SourceProfileModels.sourceReplayFrame commands state accepted).frame
      other assignment
    ∀ source record target, (signature ops).stepValue model source record target ↔
      ∃ index values,
        source = model.denote (pack ops (table index).before) values ∧
        record = model.denote (table index).record values ∧
        target = model.denote (pack ops (table index).after) values ∧
        (RuleSyntax.step (frames (Value table model)) Occurrence extensions
          (program table model domains)).Admits
          (s := snapshot table model domains index values generation)
          (firing table model domains index generation) := by
  let frame := (SourceProfileModels.sourceReplayFrame commands state accepted).frame
  dsimp only
  intro source record target
  rw [NativeFieldMeaning.received_field_cases ops logical table commands state accepted
    reading other assignment]
  constructor
  · rintro ⟨index, values, before, recordSame, after, guard⟩
    exact ⟨index, values, before, recordSame, after,
      (admitted_iff table (frame.model other assignment)
        (sourceDomains frame other assignment) index values generation).mpr guard⟩
  · rintro ⟨index, values, before, recordSame, after, admitted⟩
    exact ⟨index, values, before, recordSame, after,
      (admitted_iff table (frame.model other assignment)
        (sourceDomains frame other assignment) index values generation).mp admitted⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeFieldExecution
