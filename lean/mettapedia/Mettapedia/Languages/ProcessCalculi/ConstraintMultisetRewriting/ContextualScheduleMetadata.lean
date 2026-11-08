import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceSchedules

/-!
# Inspectable source-schedule shapes, original guard cuts and production origins

Guard cuts move into the terminal family by injective capture extensions,
without adding equations of later steps. A production keeps its own original
declarations, conditions and value. Its transport is used for shared references;
ordinary schema meaning remains attached to its birth prefix.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceSchedules

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualGuardMatching ContextualConditionalRows

variable {S : Signature} {O V W : Type} {declaration : V → MetaArity S} {later : W → MetaArity S}
    {Γ : Ctx S} {sort : S.Srt}

structure Shape (O : Type) where
  selection : Selection O
  takeCount : Nat
  readCount : Nat
  outputCount : Nat

def Shape.Holds (shape : Shape O) : Prop :=
  shape.selection.taken.Nodup ∧ shape.selection.made.Nodup ∧
    shape.takeCount = shape.selection.taken.length ∧ shape.readCount = shape.selection.read.length ∧
    shape.selection.made.length = shape.outputCount

structure Cut (declaration : V → MetaArity S) (O : Type) (context : Ctx S) (sort : S.Srt) : Type 1 where
  LocalNames : Type
  locals : LocalNames → MetaArity S
  problem : ContextualResidual.Problem declaration
  rows : O → Row locals declaration context sort
  world : Finset O
  checks : List (Check (Term (signature S declaration) context sort))

def Cut.Holds (cut : Cut declaration O Γ sort) : Prop :=
  ∀ check ∈ cut.checks, ContextualConditionalGuards.Ask cut.locals cut.problem cut.rows cut.world check

def Cut.map (change : Assignment declaration later) (cut : Cut declaration O Γ sort) : Cut later O Γ sort :=
  ⟨cut.LocalNames, cut.locals, ContextualResidual.mapProblem change cut.problem,
    (fun occurrence => (cut.rows occurrence).map cut.locals declaration change), cut.world,
    cut.checks.map (Check.map (instantiate change))⟩

theorem Cut.extension_iff (cut : Cut declaration O Γ sort) (extension : Extension declaration) :
    (cut.map extension.assignment).Holds ↔ cut.Holds := by
  simp only [Cut.Holds, Cut.map, List.forall_mem_map]
  apply forall_congr'
  intro check
  apply forall_congr'
  intro _member
  exact ContextualConditionalNaturality.ask_extension_iff cut.locals extension cut.problem cut.rows cut.world check

structure Birth (declaration : V → MetaArity S) (O : Type) (context : Ctx S) (sort : S.Srt) : Type 1 where
  SavedNames : Type
  equality : DecidableEq SavedNames
  saved : SavedNames → MetaArity S
  problem : ContextualResidual.Problem saved
  value : Term (signature S saved) context sort
  reusable : Bool
  occurrence : Option O
  transport : Assignment saved declaration

def Birth.map (change : Assignment declaration later) (birth : Birth declaration O Γ sort) : Birth later O Γ sort :=
  ⟨birth.SavedNames, birth.equality, birth.saved, birth.problem, birth.value, birth.reusable, birth.occurrence,
    Assignment.compose change birth.transport⟩

variable {Local Query : Type} {locals : Local → MetaArity S}

def originalShape (before : ContextualClauseSourceState.World locals O Γ sort) (queries : Query → MetaArity S)
    (plan : ContextualPublication.Plan (Term (signature S (queryFamily queries before.declarations)) Γ sort))
    (picked : Selection O) : Shape O :=
  ⟨picked, plan.rule.take.length, plan.rule.read.length, plan.rule.produce.length⟩

def originalCut (before : ContextualClauseSourceState.World locals O Γ sort) (queries : Query → MetaArity S)
    (plan : ContextualPublication.Plan (Term (signature S (queryFamily queries before.declarations)) Γ sort))
    (picked : Selection O) : Cut (family queries locals before.declarations) O Γ sort :=
  ⟨Local, locals, ContextualClauseSourceState.information queries locals before plan picked,
    ContextualConditionalSourceAdmission.sourceRows queries locals before.declarations before.rows, before.present,
    plan.rule.checks.map (Check.map (queryView queries locals before.declarations))⟩

def originalBirths [DecidableEq Local] [DecidableEq Query]
    (before : ContextualClauseSourceState.World locals O Γ sort) (queries : Query → MetaArity S)
    (plan : ContextualPublication.Plan (Term (signature S (queryFamily queries before.declarations)) Γ sort))
    (picked : Selection O) : List (Birth (family queries locals before.declarations) O Γ sort) :=
  List.ofFn fun port : Fin plan.rule.produce.length =>
    ⟨Query ⊕ (Mettapedia.Logic.LP.ScopedVar Local ⊕ before.Names),
      (by let _ := before.equality; infer_instance), family queries locals before.declarations,
      ContextualClauseSourceState.information queries locals before plan picked,
      queryView queries locals before.declarations (plan.rule.produce.get port),
      plan.reusable.get ⟨port.val, plan.shape.symm ▸ port.isLt⟩,
      picked.made[port.val]?, generator (family queries locals before.declarations)⟩

namespace Schedule

variable [DecidableEq O] {First Last : Type} {first : First → MetaArity S} {last : Last → MetaArity S}
    {before : ContextualClauseSourceState.World first O Γ sort} {after : ContextualClauseSourceState.World last O Γ sort}

def shapes : {Last : Type} → {last : Last → MetaArity S} →
    {after : ContextualClauseSourceState.World last O Γ sort} → Schedule S O Γ sort before after → List (Shape O)
  | _, _, _, .nil _ => []
  | _, _, _, @Schedule.snoc _ _ _ _ _ _ _ _ _ _ _ _ _ mid past queries plan picked =>
      past.shapes ++ [originalShape mid queries plan picked]

def cuts : {Last : Type} → {last : Last → MetaArity S} →
    {after : ContextualClauseSourceState.World last O Γ sort} →
    Schedule S O Γ sort before after → List (Cut after.declarations O Γ sort)
  | _, _, _, .nil _ => []
  | _, _, _, @Schedule.snoc _ _ _ _ _ _ _ _ _ middle _ _ _ mid past queries plan picked =>
      past.cuts.map (Cut.map (captureFrame queries middle mid.declarations).assignment) ++ [originalCut mid queries plan picked]

def births : {Last : Type} → {last : Last → MetaArity S} →
    {after : ContextualClauseSourceState.World last O Γ sort} →
    Schedule S O Γ sort before after → List (Birth after.declarations O Γ sort)
  | _, _, _, .nil _ => []
  | _, _, _, @Schedule.snoc _ _ _ _ _ _ _ _ _ middle _ _ _ mid past queries plan picked =>
      past.births.map (Birth.map (captureFrame queries middle mid.declarations).assignment) ++ originalBirths mid queries plan picked

def ShapesHold (schedule : Schedule S O Γ sort before after) : Prop := ∀ shape ∈ schedule.shapes, shape.Holds
def CutsHold (schedule : Schedule S O Γ sort before after) : Prop := ∀ cut ∈ schedule.cuts, cut.Holds

theorem shapes_snoc {Middle Query : Type} {middle : Middle → MetaArity S}
    [DecidableEq Middle] [DecidableEq Query] {mid : ContextualClauseSourceState.World middle O Γ sort}
    (past : Schedule S O Γ sort before mid) (queries : Query → MetaArity S)
    (plan : ContextualPublication.Plan (Term (signature S (queryFamily queries mid.declarations)) Γ sort)) (picked : Selection O) :
    (Schedule.snoc past queries plan picked).ShapesHold ↔ past.ShapesHold ∧ (originalShape mid queries plan picked).Holds := by
  change (∀ shape ∈ past.shapes ++ [originalShape mid queries plan picked], shape.Holds) ↔ _
  rw [List.forall_mem_append, List.forall_mem_singleton]
  rfl

theorem cuts_snoc {Middle Query : Type} {middle : Middle → MetaArity S}
    [DecidableEq Middle] [DecidableEq Query] {mid : ContextualClauseSourceState.World middle O Γ sort}
    (past : Schedule S O Γ sort before mid) (queries : Query → MetaArity S)
    (plan : ContextualPublication.Plan (Term (signature S (queryFamily queries mid.declarations)) Γ sort)) (picked : Selection O) :
    (Schedule.snoc past queries plan picked).CutsHold ↔ past.CutsHold ∧ (originalCut mid queries plan picked).Holds := by
  change (∀ cut ∈ past.cuts.map (Cut.map (captureFrame queries middle mid.declarations).assignment) ++
    [originalCut mid queries plan picked], cut.Holds) ↔ _
  rw [List.forall_mem_append, List.forall_mem_singleton]
  apply and_congr_left
  intro _last
  simp only [List.forall_mem_map]
  apply forall_congr'
  intro cut
  apply forall_congr'
  intro _member
  exact cut.extension_iff (captureFrame queries middle mid.declarations)

theorem cuts_count (schedule : Schedule S O Γ sort before after) : schedule.cuts.length = schedule.selections.length := by
  induction schedule with
  | nil _ => rfl
  | snoc _ _ _ _ prior =>
      change (_ ++ [_]).length = (_ ++ [_]).length
      simpa only [List.length_append, List.length_map, List.length_cons, List.length_nil] using
        congrArg (fun count => count + 1) prior

end Schedule

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceSchedules
