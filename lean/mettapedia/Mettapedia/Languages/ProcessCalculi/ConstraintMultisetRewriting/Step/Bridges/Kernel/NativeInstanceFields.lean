import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NativeInstanceReadback

/-!
# Prepared native instance calls with effect and permission checks

Each of the twenty-nine field rules has a fresh local environment and an
additional effect value. Its certificate fixes both. The rule checks the
received case guard, the actual native result equality and the explicit
permission profile. A certificate does not choose the permission profile.

This is an interpreted admission profile for one prepared call. It does
not supply a pending-record stream, a one-use ticket or an executable native
preparation procedure.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeInstanceFields

open Mettapedia.Logic Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open NativeClauseData NativeFieldSchema InterpretedFrames
open ProofExecution TypeFamilySemantics

universe w


variable {ops : Operations}

structure Profile (table : Fin 29 → Syntax ops)
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) where
  effect : Frame.{w+1}
  holds : (index : Fin 29) → model.Valuation ((table index).locals.map Ty.toHOL) →
    effect.Carrier → Prop

abbrev Locals (table : Fin 29 → Syntax ops)
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) (profile : Profile table model)
    (index : Fin 29) :=
  model.Valuation ((table index).locals.map Ty.toHOL) × profile.effect.Carrier

abbrev Value (table : Fin 29 → Syntax ops)
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) (profile : Profile table model) :=
  NativeFieldSchema.Value table model ⊕ (Σ index : Fin 29, Locals table model profile index)

def localFrame (table : Fin 29 → Syntax ops)
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (domains : model.InhabitedDomains) (profile : Profile table model) (index : Fin 29) : Frame.{w+1} where
  Carrier := Locals table model profile index
  nonempty := by
    obtain ⟨effect⟩ := profile.effect.nonempty
    exact ⟨((fun {type} _ => domains.witness type), effect)⟩

def cell (table : Fin 29 → Syntax ops)
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) (domains : model.InhabitedDomains)
    (profile : Profile table model) (index : Fin 29)
    (fields : (field : Field) → HOL.Term Symbol ((table index).locals.map Ty.toHOL) (field.type ops))
    (field : Field) : Terms (Value table model profile) (localFrame table model domains profile index) :=
  fun values => .inl (NativeFieldSchema.cell table model fields field values.1)

def schema (table : Fin 29 → Syntax ops)
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) (domains : model.InhabitedDomains)
    (profile : Profile table model)
    (index : Fin 29) : PreparedRules.Schema (Value table model profile) where
  locals := localFrame table model domains profile index
  certificate values := .inr ⟨index, values⟩
  certificate_injective := by
    intro first second same
    apply eq_of_heq
    exact (Sigma.mk.inj_iff.mp (Sum.inr.inj same)).2
  proposition proposition := .inl (.inr (.inr proposition))
  proposition_injective := by
    intro first second same
    simpa only [Sum.inl.injEq, Sum.inr.injEq] using same
  take := (table index).writes.map (cell table model domains profile index (table index).before)
  read := (table index).reads.map (cell table model domains profile index (table index).before)
  produce := (table index).writes.map (cell table model domains profile index (table index).after)
  guard values := (model.denote (table index).guard values.1).down ∧
    profile.holds index values.1 values.2

def program (table : Fin 29 → Syntax ops)
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) (domains : model.InhabitedDomains)
    (profile : Profile table model) :
    RuleSyntax.Program (Terms (Value table model profile)) :=
  Set.range (fun index => (schema table model domains profile index).rule)

theorem program_finite (table : Fin 29 → Syntax ops)
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) (domains : model.InhabitedDomains)
    (profile : Profile table model) :
    (program table model domains profile).Finite := Set.finite_range _

variable (table : Fin 29 → Syntax ops)
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) (domains : model.InhabitedDomains)
    (profile : Profile table model) (index : Fin 29)

theorem member :
    (schema table model domains profile index).rule ∈ program table model domains profile :=
  ⟨index, rfl⟩

def snapshot (values : Locals table model profile index) (generation : Field → Nat) :
    RuleSyntax.State (Terms (Value table model profile)) NativeFieldExecution.Occurrence where
  frame := ground.{w+1}
  knowledge := []
  present := NativeFieldExecution.present generation
  label occurrence _ := match occurrence with
    | .inl (field, _) => .inl (NativeFieldSchema.cell table model (table index).before field values.1)
    | .inr _ => (schema table model domains profile index).certificate values

def firing (generation : Field → Nat) :
    RuleSyntax.Firing NativeFieldExecution.Occurrence extensions
      (program table model domains profile) ground.{w+1} :=
  (schema table model domains profile index).firing
    (member table model domains profile index) NativeFieldExecution.certificate
    (NativeFieldExecution.selection (table index) generation)

theorem matches_snapshot (values : Locals table model profile index) (generation : Field → Nat)
    (fields : List Field) :
    PreparedRules.Matches (locals := localFrame table model domains profile index)
      (fields.map (cell table model domains profile index (table index).before))
      (fields.map (NativeFieldExecution.row generation))
      (fun occurrence => (snapshot table model domains profile index values generation).label
        occurrence PUnit.unit) values := by
  induction fields with
  | nil => simp [PreparedRules.Matches]
  | cons field later ih =>
      simpa [PreparedRules.Matches, snapshot, cell, NativeFieldExecution.row] using ih

theorem admitted_iff (values : Locals table model profile index) (generation : Field → Nat) :
    (RuleSyntax.step (frames (Value table model profile)) NativeFieldExecution.Occurrence extensions
      (program table model domains profile)).Admits
      (s := snapshot table model domains profile index values generation)
      (firing table model domains profile index generation) ↔
      (schema table model domains profile index).guard values := by
  change (RuleSyntax.step (frames (Value table model profile)) NativeFieldExecution.Occurrence extensions
    (program table model domains profile)).Admits
      ((schema table model domains profile index).firing
        (member table model domains profile index) NativeFieldExecution.certificate
        (NativeFieldExecution.selection (table index) generation)) ↔ _
  rw [PreparedRules.admitted_iff (schema table model domains profile index)
    (member table model domains profile index)
    (snapshot table model domains profile index values generation) NativeFieldExecution.certificate
    (NativeFieldExecution.selection (table index) generation) values (fun _ => rfl)]
  constructor
  · intro admitted
    exact admitted.2.2.2.2.2.2.2
  · intro guard
    refine ⟨(table index).writes_distinct.map (NativeFieldExecution.row_injective generation),
      (table index).writes_distinct.map (NativeFieldExecution.nextRow_injective generation),
      ?_, ?_, ?_, NativeFieldExecution.physical_enabled (table index) generation,
      ⟨PUnit.unit, ?_, matches_snapshot table model domains profile index values generation _,
        matches_snapshot table model domains profile index values generation _⟩, guard⟩
    · simp [schema, NativeFieldExecution.selection]
    · simp [schema, NativeFieldExecution.selection]
    · simp [schema, NativeFieldExecution.selection]
    · intro equation inside
      cases inside

theorem profile_refused (values : Locals table model profile index) (generation : Field → Nat)
    (denied : ¬ profile.holds index values.1 values.2) :
    ¬ (RuleSyntax.step (frames (Value table model profile)) NativeFieldExecution.Occurrence extensions
      (program table model domains profile)).Admits
      (s := snapshot table model domains profile index values generation)
      (firing table model domains profile index generation) := by
  intro admitted
  exact denied ((admitted_iff table model domains profile index values generation).mp admitted).2

theorem guard_refused (values : Locals table model profile index) (generation : Field → Nat)
    (denied : ¬ (model.denote (table index).guard values.1).down) :
    ¬ (RuleSyntax.step (frames (Value table model profile)) NativeFieldExecution.Occurrence extensions
      (program table model domains profile)).Admits
      (s := snapshot table model domains profile index values generation)
      (firing table model domains profile index generation) := by
  intro admitted
  exact denied ((admitted_iff table model domains profile index values generation).mp admitted).1

def withoutCertificate (values : Locals table model profile index) (generation : Field → Nat) :
    RuleSyntax.State (Terms (Value table model profile)) NativeFieldExecution.Occurrence :=
  { snapshot table model domains profile index values generation with
    present := (NativeFieldExecution.present generation).erase NativeFieldExecution.certificate }

theorem missing_certificate_refused (values : Locals table model profile index) (generation : Field → Nat) :
    ¬ (RuleSyntax.step (frames (Value table model profile)) NativeFieldExecution.Occurrence extensions
      (program table model domains profile)).Admits
      (s := withoutCertificate table model domains profile index values generation)
      (firing table model domains profile index generation) := by
  intro admitted
  have selected : NativeFieldExecution.certificate ∈
      ((firing table model domains profile index generation).selection.commit (T := Unit)).kept := by
    change NativeFieldExecution.certificate ∈ (NativeFieldExecution.certificate :: _).toFinset
    exact List.mem_toFinset.mpr List.mem_cons_self
  have inside := admitted.2.1.kept_subset selected
  simp [withoutCertificate] at inside

theorem result_readout (values : Locals table model profile index) (generation : Field → Nat)
    (admitted : (RuleSyntax.step (frames (Value table model profile)) NativeFieldExecution.Occurrence extensions
      (program table model domains profile)).Admits
      (s := snapshot table model domains profile index values generation)
      (firing table model domains profile index generation))
    (environment : (extend ground.{w+1} (localFrame table model domains profile index)).Carrier)
    (satisfies : Satisfies
      ((firing table model domains profile index generation).result (frames (Value table model profile))
        (snapshot table model domains profile index values generation)).knowledge environment)
    (field : Field) :
    ((firing table model domains profile index generation).result (frames (Value table model profile))
      (snapshot table model domains profile index values generation)).label
        (NativeFieldExecution.outputRow table index generation field) environment =
      cell table model domains profile index (table index).after field values := by
  by_cases written : field ∈ (table index).writes
  · rw [NativeFieldExecution.outputRow, if_pos written]
    apply PreparedRules.produced_readout (schema table model domains profile index)
      (member table model domains profile index)
      (snapshot table model domains profile index values generation) NativeFieldExecution.certificate
      (NativeFieldExecution.selection (table index) generation) values (fun _ => rfl) admitted
      (NativeFieldExecution.nextRow generation field)
      (cell table model domains profile index (table index).after field)
    · change (NativeFieldExecution.nextRow generation field,
        fun (environment : (extend ground.{w+1} (localFrame table model domains profile index)).Carrier) =>
          cell table model domains profile index (table index).after field environment.2) ∈
        ((table index).writes.map (NativeFieldExecution.nextRow generation)).zip
          (((table index).writes.map (cell table model domains profile index (table index).after)).map
            (fun term (environment : (extend ground.{w+1} (localFrame table model domains profile index)).Carrier) =>
              term environment.2))
      rw [List.map_map, List.zip_map']
      exact List.mem_map.mpr ⟨field, written, rfl⟩
    · exact satisfies
  · rw [NativeFieldExecution.outputRow, if_neg written]
    have missing : NativeFieldExecution.row generation field ∉
        (NativeFieldExecution.selection (table index) generation).made := by
      intro made
      obtain ⟨other, _, same⟩ := List.mem_map.mp made
      have sameField := congrArg Prod.fst (Sum.inl.inj same)
      change other = field at sameField
      subst other
      have impossible := congrArg Prod.snd (Sum.inl.inj same)
      change generation field + 1 = generation field at impossible
      omega
    calc
      _ = (snapshot table model domains profile index values generation).label
          (NativeFieldExecution.row generation field) environment.1 := by
        exact PreparedRules.other_readout (schema table model domains profile index)
          (member table model domains profile index)
          (snapshot table model domains profile index values generation) NativeFieldExecution.certificate
          (NativeFieldExecution.selection (table index) generation)
          (NativeFieldExecution.row generation field) missing environment
      _ = _ := by
        change Sum.inl (NativeFieldSchema.cell table model (table index).before field values.1) =
          Sum.inl (NativeFieldSchema.cell table model (table index).after field values.1)
        simp only [NativeFieldSchema.cell, (table index).unchanged field written]


/-- Independent state and record carriers keep the field-rule construction
parametric in its actual semantic representation. -/
def resultAndPermissionProfile (table : Fin 29 → Syntax ops)
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (State Record : Type (w+1)) (inhabited : Nonempty State)
    (before : (index : Fin 29) → model.Valuation ((table index).locals.map Ty.toHOL) → State)
    (record : (index : Fin 29) → model.Valuation ((table index).locals.map Ty.toHOL) → Record)
    (after : (index : Fin 29) → model.Valuation ((table index).locals.map Ty.toHOL) → State)
    (result : State → Record → State → State) (allowed : State → Record → State → Prop) :
    Profile table model where
  effect := ⟨State, inhabited⟩
  holds index values effect := after index values = result (before index values) (record index values) effect ∧
    allowed (before index values) (record index values) effect

/-- A typed state/record interpretation, kept independent of the concrete
source product presentation during guard construction. -/
structure PackAdapter (native : NativeClauseReadback.Signature) (table : Fin 29 → Syntax ops)
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) where
  before : (index : Fin 29) → model.Valuation ((table index).locals.map Ty.toHOL) → native.State model
  record : (index : Fin 29) → model.Valuation ((table index).locals.map Ty.toHOL) → native.Record model
  after : (index : Fin 29) → model.Valuation ((table index).locals.map Ty.toHOL) → native.State model

/-- The adapter uses the actual source tuple and record expressions. -/
def sourcePacks (table : Fin 29 → Syntax ops)
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) : PackAdapter (signature ops) table model where
  before index values := model.denote (pack ops (table index).before) values
  record index values := model.denote (table index).record values
  after index values := model.denote (pack ops (table index).after) values

def profileOfAdapter {native : NativeClauseReadback.Signature}
    (table : Fin 29 → Syntax ops) (contract : NativeInstanceReadback.Signature native)
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) (domains : model.InhabitedDomains)
    (packs : PackAdapter native table model)
    (allow : NativeInstanceReadback.Signature.Allow (native := native) model) : Profile table model :=
  resultAndPermissionProfile table model (native.State model) (native.Record model)
    ⟨domains.witness native.state⟩ packs.before packs.record packs.after
    (contract.resultValue model) (fun source record effect => (allow source record effect).down)

attribute [local irreducible] NativeClauseData.signature

/-- The concrete profile instantiates the typed adapter with the received
source tuple expressions and native result operation. -/
noncomputable def interpretedProfile (table : Fin 29 → Syntax ops)
    (contract : NativeInstanceReadback.Signature (signature ops))
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) (domains : model.InhabitedDomains)
    (allow : NativeInstanceReadback.Signature.Allow (native := signature ops) model) : Profile table model :=
  @profileOfAdapter.{w} ops (signature ops) table contract model domains
    (sourcePacks.{w} table model) allow

/-- Prepared admission is the actual field program's firing, including the
source, record and target denotations supplied by its typed pack adapter. -/
def preparedAdmits {native : NativeClauseReadback.Signature}
    (table : Fin 29 → Syntax ops) (contract : NativeInstanceReadback.Signature native)
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) (domains : model.InhabitedDomains)
    (packs : PackAdapter native table model)
    (allow : NativeInstanceReadback.Signature.Allow (native := native) model)
    (generation : Field → Nat) (source : native.State model) (record : native.Record model)
    (effect target : native.State model) : Prop :=
  let profile := profileOfAdapter table contract model domains packs allow
  ∃ (index : Fin 29) (values : model.Valuation ((table index).locals.map Ty.toHOL)),
    source = packs.before index @values ∧ record = packs.record index @values ∧
    target = packs.after index @values ∧
    (RuleSyntax.step (frames (Value table model profile)) NativeFieldExecution.Occurrence extensions
      (program table model domains profile)).Admits
      (s := snapshot table model domains profile index (@values, effect) generation)
      (firing table model domains profile index generation)

theorem adapter_admission_iff {native : NativeClauseReadback.Signature}
    (table : Fin 29 → Syntax ops) (contract : NativeInstanceReadback.Signature native)
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) (domains : model.InhabitedDomains)
    (packs : PackAdapter native table model)
    (allow : NativeInstanceReadback.Signature.Allow (native := native) model)
    (generation : Field → Nat) (source : native.State model) (record : native.Record model)
    (effect target : native.State model) :
    (∃ index values,
      source = packs.before index values ∧ record = packs.record index values ∧
      target = packs.after index values ∧ (model.denote (table index).guard values).down) ∧
        target = contract.resultValue model source record effect ∧ (allow source record effect).down ↔
      preparedAdmits table contract model domains packs allow generation source record effect target := by
  dsimp only [preparedAdmits]
  constructor
  · rintro ⟨⟨index, values, before, recordSame, after, guard⟩, effectSame, permitted⟩
    refine ⟨index, values, before, recordSame, after, ?_⟩
    apply (admitted_iff table model domains
      (profileOfAdapter table contract model domains packs allow) index (values, effect) generation).mpr
    exact ⟨guard, by simpa only [profileOfAdapter, resultAndPermissionProfile,
      ← before, ← recordSame, ← after] using effectSame,
      by simpa only [profileOfAdapter, resultAndPermissionProfile,
        ← before, ← recordSame] using permitted⟩
  · rintro ⟨index, values, before, recordSame, after, admitted⟩
    have guard := (admitted_iff table model domains
      (profileOfAdapter table contract model domains packs allow) index (values, effect) generation).mp admitted
    refine ⟨⟨index, values, before, recordSame, after, guard.1⟩, ?_, ?_⟩
    · simpa only [profileOfAdapter, resultAndPermissionProfile,
        ← before, ← recordSame, ← after] using guard.2.1
    · simpa only [profileOfAdapter, resultAndPermissionProfile,
        ← before, ← recordSame] using guard.2.2

theorem prepared_permission_refused {native : NativeClauseReadback.Signature}
    (table : Fin 29 → Syntax ops) (contract : NativeInstanceReadback.Signature native)
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) (domains : model.InhabitedDomains)
    (packs : PackAdapter native table model)
    (allow : NativeInstanceReadback.Signature.Allow (native := native) model)
    (generation : Field → Nat) (source : native.State model) (record : native.Record model)
    (effect target : native.State model) (denied : ¬ (allow source record effect).down) :
    ¬ preparedAdmits table contract model domains packs allow generation source record effect target := by
  intro admitted
  exact denied ((adapter_admission_iff table contract model domains packs allow generation
    source record effect target).mpr admitted).2.2

theorem prepared_effect_refused {native : NativeClauseReadback.Signature}
    (table : Fin 29 → Syntax ops) (contract : NativeInstanceReadback.Signature native)
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) (domains : model.InhabitedDomains)
    (packs : PackAdapter native table model)
    (allow : NativeInstanceReadback.Signature.Allow (native := native) model)
    (generation : Field → Nat) (source : native.State model) (record : native.Record model)
    (effect target : native.State model)
    (different : target ≠ contract.resultValue model source record effect) :
    ¬ preparedAdmits table contract model domains packs allow generation source record effect target := by
  intro admitted
  exact different ((adapter_admission_iff table contract model domains packs allow generation
    source record effect target).mpr admitted).2.1

/-- The source instance is exactly admission of one of the twenty-nine
effect-and-permission field rules at a prepared certificate. -/
theorem received_admission (table : Fin 29 → Syntax ops)
    (contract : NativeInstanceReadback.Signature (signature ops))
    (logical : NativeFieldMeaning.LogicalOperations ops)
    (commands : List Registered.Command) (state : Registered.State)
    (accepted : Registered.replayFrom SourceProfileModels.policy
      (Registered.empty SourceProfile.primitiveContext) commands = some state)
    (cases : NativeClauseReadback.Reading (signature ops) (NativeFieldMeaning.clauses table) state)
    (reading : NativeInstanceReadback.Reading contract state)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) (generation : Field → Nat) :
    let model := (SourceProfileModels.sourceReplayFrame commands state accepted).frame.model other assignment
    let domains := NativeFieldExecution.sourceDomains
      (SourceProfileModels.sourceReplayFrame commands state accepted).frame other assignment
    ∀ (allow : NativeInstanceReadback.Signature.Allow (native := signature ops) model),
    ∀ source record effect target,
      contract.instanceValue model allow source record effect target ↔
        preparedAdmits table contract model domains (sourcePacks table model) allow
          generation source record effect target := by
  dsimp only
  intro allow source record effect target
  rw [NativeInstanceReadback.received_instance contract commands state accepted reading other assignment]
  rw [NativeFieldMeaning.received_field_cases ops logical table commands state accepted cases other assignment]
  exact adapter_admission_iff table contract _ _ (sourcePacks table _) allow
    generation source record effect target

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeInstanceFields
