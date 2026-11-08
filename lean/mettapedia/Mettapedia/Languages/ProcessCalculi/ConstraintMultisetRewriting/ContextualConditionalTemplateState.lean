import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateSource
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalRowPacking
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceSchedules

/-!
# Independent source updates with conditional captured productions

The existing template syntax supplies actor variables, private template
holes and per-row equations. Its binding equations and resource admission
use the resolved-clause source semantics. The source update installs
authored production descriptors without inspecting a native solver or
target. Incoming row locals and the clause's query variables may differ.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateState

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualConditionalRows ContextualTemplateSource

variable {S : Signature} {Query Inner Local O : Type} {Γ : Ctx S} {sort : S.Srt}
    (queries : Query → MetaArity S) (inners : Inner → MetaArity S) (locals : Local → MetaArity S)
    (before : ContextualClauseSourceState.World locals O Γ sort)
    (rule : ContextualConditionalTemplateSource.Rule queries inners before.declarations Γ sort)
    (picked : Selection O)

abbrev expanded := Expanded queries inners

def ordinaryBits : List Bool := rule.code.produce.map fun production =>
  match production with
  | .ordinary _ => true
  | _ => false

def rawPlan : ContextualPublication.Plan (Term (signature S (Raw queries inners before.declarations)) Γ sort) :=
  ⟨rule.code.lower queries inners before.declarations, ordinaryBits queries inners locals before rule, by
    simp only [ordinaryBits, Rule.lower, List.length_map, List.length_mapIdx]⟩

abbrev resultFamily := family (expanded queries inners) locals before.declarations
abbrev rawLocals := ContextualPublication.privateFamily locals (resultFamily queries inners locals before)

def actorEnv : Assignment (Actor queries before.declarations) (resultFamily queries inners locals before) :=
  Assignment.compose (queryEmbedding (expanded queries inners) locals before.declarations)
    (actorInclusion queries inners before.declarations)

abbrev PrivateNames : Bool → Type
  | false => Query ⊕ (Nat × Inner)
  | true => Local ⊕ ((Query ⊕ (Nat × Inner)) ⊕ (Mettapedia.Logic.LP.ScopedVar Local ⊕ before.Names))

abbrev privateDeclarations : ∀ side, PrivateNames (Query := Query) (Inner := Inner) locals before side → MetaArity S
  | false => expanded queries inners
  | true => rawLocals queries inners locals before

abbrev resultLocals := ContextualConditionalRowPacking.family (PrivateNames (Query := Query) (Inner := Inner) locals before)
  (privateDeclarations queries inners locals before)

variable [DecidableEq O]

abbrev information := ContextualClauseSourceState.information (expanded queries inners) locals before
  (rawPlan queries inners locals before rule) picked

abbrev Admitted := ContextualClauseSourceState.Admitted (expanded queries inners) locals before
  (rawPlan queries inners locals before rule) picked

def packOrdinary (row : Row (rawLocals queries inners locals before) (resultFamily queries inners locals before) Γ sort) :=
  ContextualConditionalRowPacking.pack (PrivateNames (Query := Query) (Inner := Inner) locals before) (privateDeclarations queries inners locals before)
    (resultFamily queries inners locals before) true row

def packTemplate (row : Row (expanded queries inners) (resultFamily queries inners locals before) Γ sort) :=
  ContextualConditionalRowPacking.pack (PrivateNames (Query := Query) (Inner := Inner) locals before) (privateDeclarations queries inners locals before)
    (resultFamily queries inners locals before) false row

def producedDescription (origin : Nat)
    (description : ContextualConditionalTemplateSource.Description queries inners before.declarations Γ sort) :
    Row (resultLocals queries inners locals before) (resultFamily queries inners locals before) Γ sort :=
  match description with
  | ⟨.ordinary value, _⟩ => packOrdinary queries inners locals before
      (ContextualConditionalPublication.ordinary locals (resultFamily queries inners locals before)
        (resultFamily queries inners locals before)
        ⟨information queries inners locals before rule picked,
          instantiate (actorEnv queries inners locals before) value⟩)
  | ⟨.shared value, _⟩ => packOrdinary queries inners locals before
      (ofStored _ _ (.shared (instantiate (actorEnv queries inners locals before) value)))
  | ⟨.schema body, conditions⟩ => packTemplate queries inners locals before
      (ContextualConditionalTemplates.stored queries inners before.declarations
        (actorEnv queries inners locals before) origin ⟨.schema body, conditions⟩)

def producedRows := List.ofFn fun port : Fin rule.code.produce.length =>
  producedDescription queries inners locals before rule picked port.val ⟨rule.code.produce.get port, rule.conditions port⟩

def retainedRow (occurrence : O) :
    Row (resultLocals queries inners locals before) (resultFamily queries inners locals before) Γ sort :=
  packOrdinary queries inners locals before
    (ContextualClauseSourceState.retainedRow (expanded queries inners) locals before occurrence)

variable [DecidableEq Query] [DecidableEq Inner] [DecidableEq Local]

abbrev target : ContextualClauseSourceState.World (resultLocals queries inners locals before) O Γ sort where
  Names := (Query ⊕ (Nat × Inner)) ⊕ (Mettapedia.Logic.LP.ScopedVar Local ⊕ before.Names)
  equality := by let _ := before.equality; infer_instance
  declarations := resultFamily queries inners locals before
  equations := information queries inners locals before rule picked
  present := (before.present \ picked.taken.toFinset) ∪ picked.made.toFinset
  rows occurrence :=
    (ContextualTemplateSource.assign picked.made (producedRows queries inners locals before rule picked) occurrence).getD
      (retainedRow queries inners locals before occurrence)

variable {queries inners locals before rule picked}

omit [DecidableEq Query] [DecidableEq Inner] [DecidableEq Local] in
theorem output_shape (source : Admitted queries inners locals before rule picked) :
    picked.made.length = rule.code.produce.length := by
  simpa only [rawPlan, Rule.lower, List.length_mapIdx] using source.output_shape

omit [DecidableEq O] [DecidableEq Query] [DecidableEq Inner] [DecidableEq Local] in
theorem actor_value (value : Term (signature S (Actor queries before.declarations)) Γ sort) :
    queryView (expanded queries inners) locals before.declarations
        (instantiate (actorInclusion queries inners before.declarations) value) =
      instantiate (actorEnv queries inners locals before) value :=
  (Assignment.instantiate_compose _ _ _).symm

omit [DecidableEq O] [DecidableEq Query] [DecidableEq Inner] [DecidableEq Local] in
theorem raw_produced_row (port : Fin rule.code.produce.length) :
    ContextualClauseSourceState.producedRow (expanded queries inners) locals before
        (rawPlan queries inners locals before rule) picked
        ⟨port.val, by simpa only [rawPlan, Rule.lower, List.length_mapIdx] using port.isLt⟩ =
      match rule.code.produce.get port with
      | .ordinary value => ContextualConditionalPublication.ordinary locals (resultFamily queries inners locals before)
          (resultFamily queries inners locals before)
          ⟨information queries inners locals before rule picked, instantiate (actorEnv queries inners locals before) value⟩
      | .shared value => ofStored _ _ (.shared (instantiate (actorEnv queries inners locals before) value))
      | .schema body => ofStored _ _ (.shared
          (queryView (expanded queries inners) locals before.declarations
            (instantiate (templateInclusion queries inners before.declarations port.val) body))) := by
  have bit : (ordinaryBits queries inners locals before rule).get
      ⟨port.val, by simp only [ordinaryBits, List.length_map]; exact port.isLt⟩ =
      match rule.code.produce.get port with | .ordinary _ => true | _ => false := by
    simp only [ordinaryBits, List.get_eq_getElem, List.getElem_map]
  unfold ContextualClauseSourceState.producedRow
  erw [Rule.lower_at_port, bit]
  cases production : rule.code.produce.get port <;>
    simp only [Production.lower, actor_value, Bool.false_eq_true, if_true, if_false]

theorem produced_at_shape (distinct : picked.made.Nodup) (outputs : picked.made.length = rule.code.produce.length)
    (port : Fin picked.made.length) :
    (target queries inners locals before rule picked).rows (picked.made.get port) =
      producedDescription queries inners locals before rule picked port.val
        ⟨rule.code.produce.get ⟨port.val, outputs ▸ port.isLt⟩,
          rule.conditions ⟨port.val, outputs ▸ port.isLt⟩⟩ := by
  have size : picked.made.length = (producedRows queries inners locals before rule picked).length := by
    simpa only [producedRows, List.length_ofFn] using outputs
  change (ContextualTemplateSource.assign _ _ _).getD _ = _
  rw [ContextualTemplateSource.assign_get picked.made _ distinct size port]
  exact List.get_ofFn _ _

theorem produced_at (source : Admitted queries inners locals before rule picked) (port : Fin picked.made.length) :
    (target queries inners locals before rule picked).rows (picked.made.get port) =
      producedDescription queries inners locals before rule picked port.val
        ⟨rule.code.produce.get ⟨port.val, output_shape source ▸ port.isLt⟩,
          rule.conditions ⟨port.val, output_shape source ▸ port.isLt⟩⟩ :=
  produced_at_shape source.output_distinct (output_shape source) port

theorem retained_at (occurrence : O) (notMade : occurrence ∉ picked.made) :
    (target queries inners locals before rule picked).rows occurrence = retainedRow queries inners locals before occurrence := by
  change (ContextualTemplateSource.assign _ _ _).getD _ = _
  cases selected : ContextualTemplateSource.assign picked.made (producedRows queries inners locals before rule picked) occurrence with
  | none => rfl
  | some value => exact False.elim (notMade (ContextualTemplateSource.assign_mem _ _ _ _ selected))

omit [DecidableEq O] [DecidableEq Query] [DecidableEq Inner] [DecidableEq Local] in
theorem schema_description_matches (origin : Nat)
    (body : Term (signature S (Blueprint queries inners before.declarations)) Γ sort)
    (conditions : ContextualResidual.Problem (Blueprint queries inners before.declarations))
    {Next : Type} (next : Next → MetaArity S)
    (candidate : Assignment (resultFamily queries inners locals before) next) (pattern : Term (signature S next) Γ sort) :
    Matches (resultLocals queries inners locals before) (resultFamily queries inners locals before) candidate pattern
        (producedDescription queries inners locals before rule picked origin ⟨.schema body, conditions⟩) ↔
      Matches inners (Actor queries before.declarations)
        (Assignment.compose candidate (actorEnv queries inners locals before)) pattern ⟨.schema body, conditions⟩ := by
  change Matches _ _ candidate pattern (packTemplate queries inners locals before _) ↔ _
  rw [packTemplate, ContextualConditionalRowPacking.matches_iff]
  exact ContextualConditionalTemplates.stored_matches_iff queries inners before.declarations _ origin candidate _ pattern

omit [DecidableEq O] [DecidableEq Query] [DecidableEq Inner] [DecidableEq Local] in
theorem ordinary_description_matches
    (value : Term (signature S (Actor queries before.declarations)) Γ sort) (origin : Nat)
    {Next : Type} (next : Next → MetaArity S)
    (candidate : Assignment (resultFamily queries inners locals before) next) (pattern : Term (signature S next) Γ sort) :
    Matches (resultLocals queries inners locals before) (resultFamily queries inners locals before) candidate pattern
        (producedDescription queries inners locals before rule picked origin ⟨.ordinary value, PUnit.unit⟩) ↔
      ContextualPublication.SourceInstances (information queries inners locals before rule picked)
        (instantiate (actorEnv queries inners locals before) value) next pattern := by
  change Matches _ _ candidate pattern (packOrdinary queries inners locals before _) ↔ _
  rw [packOrdinary, ContextualConditionalRowPacking.matches_iff]
  exact ContextualConditionalPublication.ordinary_matches_iff locals _ _ candidate _ pattern

theorem retained_matches (occurrence : O) (notMade : occurrence ∉ picked.made)
    {Next : Type} (next : Next → MetaArity S)
    (candidate : Assignment (resultFamily queries inners locals before) next) (pattern : Term (signature S next) Γ sort) :
    Matches (resultLocals queries inners locals before) (resultFamily queries inners locals before) candidate pattern
        ((target queries inners locals before rule picked).rows occurrence) ↔
      Matches locals before.declarations
        (Assignment.compose candidate (captureEmbedding (expanded queries inners) locals before.declarations))
        pattern (before.rows occurrence) := by
  rw [retained_at occurrence notMade]
  change Matches _ _ candidate pattern (packOrdinary queries inners locals before _) ↔ _
  rw [packOrdinary, ContextualConditionalRowPacking.matches_iff]
  have original := ContextualClauseSourceState.retained_matches (queries := expanded queries inners) (locals := locals)
    (before := before) (plan := rawPlan queries inners locals before rule) (picked := picked) occurrence notMade next candidate pattern
  rw [ContextualClauseSourceState.retained_at occurrence notMade] at original
  exact original

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateState
