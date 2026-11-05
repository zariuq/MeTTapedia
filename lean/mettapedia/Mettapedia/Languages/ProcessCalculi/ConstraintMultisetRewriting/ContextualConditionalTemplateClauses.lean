import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateState
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualWorldFrameComparison

/-!
# Conditional template clauses on arbitrary incoming row families

Binding and resources use the existing clause compiler. Authored schema
descriptors install conditional template metadata in its result. Ordinary
and shared outputs use that actual result directly. The independent source
update has the same information and physical effects; its row comparison
keeps explicit actor captures and private template holes distinct.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateClauses

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualConditionalRows ContextualTemplateSource
open ContextualConditionalTemplateState

variable {S : Signature} {Query Inner Local O : Type} {Γ : Ctx S} {sort : S.Srt}
    (queries : Query → MetaArity S) (inners : Inner → MetaArity S) (locals : Local → MetaArity S)
    [DecidableEq Query] [DecidableEq Inner] [DecidableEq Local] [DecidableEq O]
    [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
    (before : ContextualClauseSourceState.World locals O Γ sort) (occupied : Finset Nat)
    (rule : ContextualConditionalTemplateSource.Rule queries inners before.declarations Γ sort)
    (picked : Selection O)

abbrev Compiled := ContextualConditionalClauses.Compiled (expanded queries inners) locals
  (before := before.native occupied) (rawPlan queries inners locals before rule) picked

variable {queries inners locals before occupied rule picked}

theorem realize (source : Admitted queries inners locals before rule picked) (fuel : Nat) :
    ∃ compiled : Compiled queries inners locals before occupied rule picked, compiled.firing.fuel = fuel :=
  ContextualConditionalClauses.realize (expanded queries inners) locals
    (before := before.native occupied) (rawPlan queries inners locals before rule) picked source fuel

namespace Compiled

variable (compiled : Compiled queries inners locals before occupied rule picked)

def actorValues : Assignment (Actor queries before.declarations) compiled.firing.target.declarations :=
  Assignment.compose compiled.continuationEnv (actorInclusion queries inners before.declarations)

theorem actor_square : actorValues compiled =
    Assignment.compose compiled.sourceFrame.assignment (actorEnv queries inners locals before) := by
  exact (Assignment.compose_associative _ _ _).symm

abbrev PrivateNames : Bool → Type
  | false => Query ⊕ (Nat × Inner)
  | true => (Local ⊕ (Query ⊕ (Nat × Inner))) ⊕ compiled.firing.update.Variables

abbrev privateDeclarations : ∀ side, PrivateNames compiled side → MetaArity S
  | false => expanded queries inners
  | true => ContextualPublication.privateFamily (ContextualClauseFrames.bank (expanded queries inners) locals)
      compiled.firing.update.declaration

abbrev resultLocals := ContextualConditionalRowPacking.family (PrivateNames compiled) (privateDeclarations compiled)

def packOrdinary (row : Row (privateDeclarations compiled true) compiled.firing.target.declarations Γ sort) :=
  ContextualConditionalRowPacking.pack (PrivateNames compiled) (privateDeclarations compiled)
    compiled.firing.target.declarations true row

def packTemplate (row : Row (expanded queries inners) compiled.firing.target.declarations Γ sort) :=
  ContextualConditionalRowPacking.pack (PrivateNames compiled) (privateDeclarations compiled)
    compiled.firing.target.declarations false row

def descriptor := rule.outputsFor picked.made

def rows (occurrence : O) : Row (resultLocals compiled) compiled.firing.target.declarations Γ sort :=
  match descriptor (rule := rule) (picked := picked) occurrence with
  | some (origin, ⟨.schema body, conditions⟩) => packTemplate compiled
      (ContextualConditionalTemplates.stored queries inners before.declarations
        (actorValues compiled) origin ⟨.schema body, conditions⟩)
  | _ => packOrdinary compiled (compiled.firing.target.rows occurrence)

def target : ContextualConditionalExecution.State (resultLocals compiled) O Γ sort where
  Names := compiled.firing.target.Names
  equality := compiled.firing.target.equality
  declarations := compiled.firing.target.declarations
  occupied := compiled.firing.target.occupied
  equations := compiled.firing.target.equations
  present := compiled.firing.target.present
  rows := rows compiled

theorem information_exact : (target compiled).equations =
    ContextualResidual.mapProblem compiled.sourceFrame.assignment
      (ContextualConditionalTemplateState.target queries inners locals before rule picked).equations :=
  compiled.result_equations

theorem physical_exact : (target compiled).present =
    (ContextualConditionalTemplateState.target queries inners locals before rule picked).present :=
  compiled.physical_result

theorem schema_matches (occurrence : O) (origin : Nat)
    (body : Term (signature S (Blueprint queries inners before.declarations)) Γ sort)
    (conditions : ContextualResidual.Problem (Blueprint queries inners before.declarations))
    (selected : descriptor (rule := rule) (picked := picked) occurrence = some (origin, ⟨.schema body, conditions⟩))
    {Next : Type} (next : Next → MetaArity S)
    (candidate : Assignment (target compiled).declarations next) (pattern : Term (signature S next) Γ sort) :
    Matches (resultLocals compiled) (target compiled).declarations candidate pattern ((target compiled).rows occurrence) ↔
      Matches inners (Actor queries before.declarations)
        (Assignment.compose candidate (actorValues compiled)) pattern ⟨.schema body, conditions⟩ := by
  change Matches (resultLocals compiled) compiled.firing.target.declarations candidate pattern (rows compiled occurrence) ↔ _
  simp only [rows, selected]
  change Matches (resultLocals compiled) compiled.firing.target.declarations candidate pattern (packTemplate compiled _) ↔ _
  exact (ContextualConditionalRowPacking.matches_iff (PrivateNames compiled) (privateDeclarations compiled)
    compiled.firing.target.declarations false _ candidate pattern).trans
      (ContextualConditionalTemplates.stored_matches_iff queries inners before.declarations _ origin candidate _ pattern)

theorem retained_matches (occurrence : O) (notMade : occurrence ∉ picked.made)
    {Next : Type} (next : Next → MetaArity S)
    (candidate : Assignment (target compiled).declarations next) (pattern : Term (signature S next) Γ sort) :
    Matches (resultLocals compiled) (target compiled).declarations candidate pattern ((target compiled).rows occurrence) ↔
      Matches locals before.declarations
        (Assignment.compose candidate (Assignment.compose (ContextualComputedFreshFrame.includeSource compiled.firing.update)
          (ContextualSelectionViews.capturedTarget (ContextualClauseFrames.bank (expanded queries inners) locals)
            before.declarations))) pattern (before.rows occurrence) := by
  have absent : descriptor (rule := rule) (picked := picked) occurrence = none := by
    cases selected : descriptor (rule := rule) (picked := picked) occurrence with
    | none => rfl
    | some entry => exact False.elim (notMade (ContextualTemplateSource.assign_mem _ _ _ _ selected))
  change Matches (resultLocals compiled) compiled.firing.target.declarations candidate pattern (rows compiled occurrence) ↔ _
  simp only [rows, absent]
  change Matches (resultLocals compiled) compiled.firing.target.declarations candidate pattern (packOrdinary compiled _) ↔ _
  have native := compiled.firing.retained_matches occurrence (by rw [compiled.selected]; exact notMade) next candidate pattern
  refine (ContextualConditionalRowPacking.matches_iff (PrivateNames compiled) (privateDeclarations compiled)
    compiled.firing.target.declarations true _ candidate pattern).trans ?_
  exact native.trans (ContextualConditionalPublication.extendPrivate_matches_iff locals (expanded queries inners)
    before.declarations _ _ pattern)

end Compiled

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateClauses
