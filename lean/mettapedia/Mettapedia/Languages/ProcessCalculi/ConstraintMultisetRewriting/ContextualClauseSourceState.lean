import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalSourceAdmission

/-!
# A resolved clause's source state update, before native allocation

The source state contains equations and stored rows, without a native scope
ledger or solver cache. Each step introduces its query and per-use row names
in the independently indexed source family. Its continuation retains those
bindings. Ordinary outputs store the source value and conditions as a fresh
schema; shared outputs retain the source references.

The update is constructed from source syntax and admission. It does not
call the native solver or project a native target state.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseSourceState

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualConditionalRows

variable {S : Signature} {Local Query O : Type} {Γ : Ctx S} {sort : S.Srt}

structure World (locals : Local → MetaArity S) (O : Type) (context : Ctx S) (sort : S.Srt) : Type 1 where
  Names : Type
  equality : DecidableEq Names
  declarations : Names → MetaArity S
  equations : ContextualResidual.Problem declarations
  present : Finset O
  rows : O → Row locals declarations context sort

abbrev World.native {locals : Local → MetaArity S} (world : World locals O Γ sort) (occupied : Finset Nat) :
    ContextualConditionalExecution.State locals O Γ sort :=
  ⟨world.Names, world.equality, world.declarations, occupied, world.equations, world.present, world.rows⟩

variable (queries : Query → MetaArity S) (locals : Local → MetaArity S)
    (before : World locals O Γ sort)
    (plan : ContextualPublication.Plan
      (Term (signature S (queryFamily queries before.declarations)) Γ sort))
    (picked : Selection O) [DecidableEq O]

abbrev Admitted := ContextualConditionalSourceAdmission.Admitted queries locals before.declarations
  picked plan.rule before.rows before.equations before.present

abbrev resultFamily := family queries locals before.declarations
abbrev resultLocals := ContextualPublication.privateFamily locals (resultFamily queries locals before)

def information := ContextualConditionalSourceProblem.problem queries locals before.declarations
  picked plan.rule before.rows before.equations

def producedRow (port : Fin plan.rule.produce.length) :
    Row (resultLocals queries locals before) (resultFamily queries locals before) Γ sort :=
  let value := queryView queries locals before.declarations (plan.rule.produce.get port)
  if plan.reusable.get ⟨port.val, plan.shape.symm ▸ port.isLt⟩ then
    ContextualConditionalPublication.ordinary locals (resultFamily queries locals before)
      (resultFamily queries locals before) ⟨information queries locals before plan picked, value⟩
  else ofStored _ _ (.shared value)

def producedRows := List.ofFn (producedRow queries locals before plan picked)

def retainedRow (occurrence : O) :
    Row (resultLocals queries locals before) (resultFamily queries locals before) Γ sort :=
  ContextualConditionalPublication.extendPrivate locals (resultFamily queries locals before)
    (resultFamily queries locals before)
    ((before.rows occurrence).map locals before.declarations (captureEmbedding queries locals before.declarations))

variable [DecidableEq Query] [DecidableEq Local]

abbrev target : World (resultLocals queries locals before) O Γ sort where
  Names := Query ⊕ (Mettapedia.Logic.LP.ScopedVar Local ⊕ before.Names)
  equality := by let _ := before.equality; infer_instance
  declarations := resultFamily queries locals before
  equations := information queries locals before plan picked
  present := (before.present \ picked.taken.toFinset) ∪ picked.made.toFinset
  rows occurrence :=
    (ContextualTemplateSource.assign picked.made (producedRows queries locals before plan picked) occurrence).getD
      (retainedRow queries locals before occurrence)

def continuationEnv : Assignment (queryFamily queries before.declarations) (resultFamily queries locals before) :=
  queryEmbedding queries locals before.declarations

variable {queries locals before plan picked}

theorem produced_at_shape (distinct : picked.made.Nodup)
    (outputs : picked.made.length = plan.rule.produce.length) (port : Fin picked.made.length) :
    (target queries locals before plan picked).rows (picked.made.get port) =
      producedRow queries locals before plan picked ⟨port.val, outputs ▸ port.isLt⟩ := by
  have size : picked.made.length = (producedRows queries locals before plan picked).length := by
    simpa only [producedRows, List.length_ofFn] using outputs
  change (ContextualTemplateSource.assign _ _ _).getD _ = _
  rw [ContextualTemplateSource.assign_get picked.made _ distinct size port]
  exact List.get_ofFn _ _

theorem produced_at (source : Admitted queries locals before plan picked) (port : Fin picked.made.length) :
    (target queries locals before plan picked).rows (picked.made.get port) =
      producedRow queries locals before plan picked ⟨port.val, source.output_shape ▸ port.isLt⟩ :=
  produced_at_shape source.output_distinct source.output_shape port

theorem retained_at (occurrence : O) (notMade : occurrence ∉ picked.made) :
    (target queries locals before plan picked).rows occurrence = retainedRow queries locals before occurrence := by
  change (ContextualTemplateSource.assign _ _ _).getD _ = _
  cases found : ContextualTemplateSource.assign picked.made (producedRows queries locals before plan picked) occurrence with
  | none => rfl
  | some value =>
      exact False.elim (notMade (ContextualTemplateSource.assign_mem _ _ _ _ found))

theorem ordinary_output_instances (source : Admitted queries locals before plan picked)
    (port : Fin picked.made.length)
    (ordinary : plan.reusable.get ⟨port.val, source.output_shape.trans plan.shape.symm ▸ port.isLt⟩ = true)
    {Next : Type} (next : Next → MetaArity S)
    (candidate : Assignment (resultFamily queries locals before) next) (pattern : Term (signature S next) Γ sort) :
    Matches (resultLocals queries locals before) (resultFamily queries locals before) candidate pattern
      ((target queries locals before plan picked).rows (picked.made.get port)) ↔
    ContextualPublication.SourceInstances (information queries locals before plan picked)
      (queryView queries locals before.declarations
        (plan.rule.produce.get ⟨port.val, source.output_shape ▸ port.isLt⟩)) next pattern := by
  rw [produced_at source port]
  unfold producedRow
  rw [ordinary]
  exact ContextualConditionalPublication.ordinary_matches_iff locals _ _ candidate _ pattern

theorem retained_matches (occurrence : O) (notMade : occurrence ∉ picked.made)
    {Next : Type} (next : Next → MetaArity S)
    (candidate : Assignment (resultFamily queries locals before) next) (pattern : Term (signature S next) Γ sort) :
    Matches (resultLocals queries locals before) (resultFamily queries locals before) candidate pattern
      ((target queries locals before plan picked).rows occurrence) ↔
    Matches locals before.declarations
      (Assignment.compose candidate (captureEmbedding queries locals before.declarations)) pattern (before.rows occurrence) := by
  rw [retained_at occurrence notMade]
  exact (ContextualConditionalPublication.extendPrivate_matches_iff locals _ _ candidate _ pattern).trans
    (matches_map_iff locals _ (captureEmbedding queries locals before.declarations) candidate pattern _)

theorem shared_output_row (source : Admitted queries locals before plan picked)
    (port : Fin picked.made.length)
    (isShared : plan.reusable.get ⟨port.val, source.output_shape.trans plan.shape.symm ▸ port.isLt⟩ = false) :
    (target queries locals before plan picked).rows (picked.made.get port) = ofStored _ _ (.shared
      (queryView queries locals before.declarations
        (plan.rule.produce.get ⟨port.val, source.output_shape ▸ port.isLt⟩))) := by
  rw [produced_at source port]
  unfold producedRow
  rw [isShared]
  rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseSourceState
