import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardMatching
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameUnifier
import Lean.Elab.Tactic.Omega

/-!
# Scoped occurrence guards as nonbinding future-model asks

Equality, absence and counts reuse the existing `Check` constructors. A row
contributes one physical identity when it has a local instance, independently
of the number of local witnesses. Admission observes every later-family model
of the equation store. Pointwise absence is not such an admission decision.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardSemantics

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualGuardMatching

universe u
variable {S : Signature} {Local Shared Next Later : Type} {O : Type u}
  (locals : Local → MetaArity S) {captures : Shared → MetaArity S}
  {next : Next → MetaArity S} {later : Later → MetaArity S}

noncomputable def region (candidate : Assignment captures next) {Γ : Ctx S} {sort : S.Srt}
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (world : Finset O)
    (pattern : Term (signature S captures) Γ sort) : Finset O := by
  classical
  exact world.filter fun occurrence => Matches locals candidate (instantiate candidate pattern) (rows occurrence)

def Holds (candidate : Assignment captures next) {Γ : Ctx S} {sort : S.Srt}
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (world : Finset O) :
    Check (Term (signature S captures) Γ sort) → Prop
  | .equal left right => instantiate candidate left = instantiate candidate right
  | .absent pattern => ∀ occurrence ∈ world,
      ¬ Matches locals candidate (instantiate candidate pattern) (rows occurrence)
  | .count pattern number => (region locals candidate rows world pattern).card = number

theorem mem_region (candidate : Assignment captures next) {Γ : Ctx S} {sort : S.Srt}
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (world : Finset O)
    (pattern : Term (signature S captures) Γ sort) (occurrence : O) :
    occurrence ∈ region locals candidate rows world pattern ↔ occurrence ∈ world ∧
      Matches locals candidate (instantiate candidate pattern) (rows occurrence) := by
  classical
  simp only [region, Finset.mem_filter]

theorem absent_iff_empty (candidate : Assignment captures next) {Γ : Ctx S} {sort : S.Srt}
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (world : Finset O)
    (pattern : Term (signature S captures) Γ sort) :
    Holds locals candidate rows world (.absent pattern) ↔ region locals candidate rows world pattern = ∅ := by
  classical
  simp only [Holds, Finset.eq_empty_iff_forall_notMem, mem_region, not_and]

theorem region_singleton [DecidableEq O] (candidate : Assignment captures next)
    {Γ : Ctx S} {sort : S.Srt} (rows : O → ContextualStoredRows.Row locals captures Γ sort)
    (pattern : Term (signature S captures) Γ sort) (occurrence : O)
    (matched : Matches locals candidate (instantiate candidate pattern) (rows occurrence)) :
    region locals candidate rows {occurrence} pattern = {occurrence} := by
  classical
  ext other
  constructor
  · intro member
    exact ((mem_region locals candidate rows {occurrence} pattern other).mp member).1
  · intro member
    have same : other = occurrence := Finset.mem_singleton.mp member
    subst other
    exact (mem_region locals candidate rows {occurrence} pattern occurrence).mpr
      ⟨Finset.mem_singleton_self _, matched⟩

theorem region_shared [DecidableEq O] (candidate : Assignment captures captures)
    {Γ : Ctx S} {sort : S.Srt} (label : O → Term (signature S captures) Γ sort)
    (world : Finset O) (pattern : Term (signature S captures) Γ sort) :
    region locals candidate (fun occurrence => .shared (label occurrence)) world pattern =
      Check.matches (ContextualFamilies.action captures Γ sort) candidate label world pattern := rfl

theorem holds_shared [DecidableEq O] (candidate : Assignment captures captures)
    {Γ : Ctx S} {sort : S.Srt} (label : O → Term (signature S captures) Γ sort)
    (world : Finset O) (check : Check (Term (signature S captures) Γ sort)) :
    Holds locals candidate (fun occurrence => .shared (label occurrence)) world check ↔
      check.Holds (ContextualFamilies.action captures Γ sort) candidate label world := by
  cases check with
  | equal left right => rfl
  | absent pattern => rfl
  | count pattern number => rw [Holds, Check.Holds, region_shared]

theorem region_after_capture_transport (change : Assignment captures later) (candidate : Assignment later next)
    {Γ : Ctx S} {sort : S.Srt} (rows : O → ContextualStoredRows.Row locals captures Γ sort)
    (world : Finset O) (pattern : Term (signature S captures) Γ sort) :
    region locals candidate (fun occurrence => (rows occurrence).map locals change) world
        (instantiate change pattern) =
      region locals (Assignment.compose candidate change) rows world pattern := by
  classical
  ext occurrence
  simp only [mem_region, matches_after_capture_transport, Assignment.instantiate_compose]

theorem holds_after_capture_transport (change : Assignment captures later) (candidate : Assignment later next)
    {Γ : Ctx S} {sort : S.Srt} (rows : O → ContextualStoredRows.Row locals captures Γ sort)
    (world : Finset O) (check : Check (Term (signature S captures) Γ sort)) :
    Holds locals candidate (fun occurrence => (rows occurrence).map locals change) world
        (check.map (instantiate change)) ↔
      Holds locals (Assignment.compose candidate change) rows world check := by
  cases check with
  | equal left right => simp only [Holds, Check.map, Assignment.instantiate_compose]
  | absent pattern =>
      simp only [Holds, Check.map, matches_after_capture_transport, Assignment.instantiate_compose]
  | count pattern number => simp only [Holds, Check.map, region_after_capture_transport]

def Ask {Γ : Ctx S} {sort : S.Srt}
    (problem : EquationStore (Term (signature S captures) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (world : Finset O)
    (check : Check (Term (signature S captures) Γ sort)) : Prop :=
  ∀ (Future : Type) (future : Future → MetaArity S) (candidate : Assignment captures future),
    ContextualFrameUnifier.Models candidate problem → Holds locals candidate rows world check

theorem Ask.equal_refl {Γ : Ctx S} {sort : S.Srt}
    (problem : EquationStore (Term (signature S captures) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (world : Finset O)
    (term : Term (signature S captures) Γ sort) : Ask locals problem rows world (.equal term term) := by
  intro Future future candidate _
  rfl

theorem Ask.equal_of_mem {Γ : Ctx S} {sort : S.Srt}
    (problem : EquationStore (Term (signature S captures) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (world : Finset O)
    (left right : Term (signature S captures) Γ sort) (member : (left, right) ∈ problem) :
    Ask locals problem rows world (.equal left right) := by
  intro Future future candidate solved
  exact solved _ member

theorem Ask.append {Γ : Ctx S} {sort : S.Srt}
    {problem : EquationStore (Term (signature S captures) Γ sort)}
    {rows : O → ContextualStoredRows.Row locals captures Γ sort} {world : Finset O}
    {check : Check (Term (signature S captures) Γ sort)}
    (admitted : Ask locals problem rows world check)
    (extra : EquationStore (Term (signature S captures) Γ sort)) :
    Ask locals (problem ++ extra) rows world check := by
  intro Future future candidate solved
  exact admitted Future future candidate ((ContextualFrameUnifier.models_append candidate problem extra).mp solved).1

theorem Ask.future {Γ : Ctx S} {sort : S.Srt}
    {problem : EquationStore (Term (signature S captures) Γ sort)}
    {rows : O → ContextualStoredRows.Row locals captures Γ sort} {world : Finset O}
    {check : Check (Term (signature S captures) Γ sort)}
    (admitted : Ask locals problem rows world check) (candidate : Assignment captures next)
    (solved : ContextualFrameUnifier.Models candidate problem) (change : Assignment next later) :
    Holds locals (Assignment.compose change candidate) rows world check :=
  admitted Later later _ (ContextualFrameUnifier.models_compose solved change)

theorem Ask.transport {Γ : Ctx S} {sort : S.Srt}
    {problem : EquationStore (Term (signature S captures) Γ sort)}
    {rows : O → ContextualStoredRows.Row locals captures Γ sort} {world : Finset O}
    {check : Check (Term (signature S captures) Γ sort)}
    (admitted : Ask locals problem rows world check) (change : Assignment captures later) :
    Ask locals (ContextualFrameUnifier.mapProblem change problem)
      (fun occurrence => (rows occurrence).map locals change) world (check.map (instantiate change)) := by
  intro Future future candidate solved
  have oldModels := (ContextualFrameUnifier.models_mapProblem change candidate problem).mp solved
  exact (holds_after_capture_transport locals change candidate rows world check).mpr
    (admitted Future future (Assignment.compose candidate change) oldModels)

/-- All-future asks specialize to the older endomorphic entailment. No
reflection from an arbitrary smaller declaration frame is assumed. -/
theorem Ask.shared_entails [DecidableEq O] {Γ : Ctx S} {sort : S.Srt}
    {problem : EquationStore (Term (signature S captures) Γ sort)}
    (label : O → Term (signature S captures) Γ sort) (world : Finset O)
    (check : Check (Term (signature S captures) Γ sort))
    (admitted : Ask locals problem (fun occurrence => .shared (label occurrence)) world check) :
    (ContextualFamilies.action captures Γ sort).Entails problem
      (fun candidate => check.Holds (ContextualFamilies.action captures Γ sort) candidate label world) := by
  intro candidate solved
  exact (holds_shared locals candidate label world check).mp (admitted Shared captures candidate solved)

theorem region_erase [DecidableEq O] (candidate : Assignment captures next) {Γ : Ctx S} {sort : S.Srt}
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (world : Finset O)
    (pattern : Term (signature S captures) Γ sort) (occurrence : O) :
    region locals candidate rows (world.erase occurrence) pattern =
      (region locals candidate rows world pattern).erase occurrence := by
  classical
  simp only [region, Finset.filter_erase]

theorem absent_after_erase_iff_count_one [DecidableEq O] (candidate : Assignment captures next)
    {Γ : Ctx S} {sort : S.Srt} (rows : O → ContextualStoredRows.Row locals captures Γ sort)
    (world : Finset O) (pattern : Term (signature S captures) Γ sort) (occurrence : O)
    (present : occurrence ∈ world)
    (matched : Matches locals candidate (instantiate candidate pattern) (rows occurrence)) :
    Holds locals candidate rows (world.erase occurrence) (.absent pattern) ↔
      Holds locals candidate rows world (.count pattern 1) := by
  classical
  have member := (mem_region locals candidate rows world pattern occurrence).mpr ⟨present, matched⟩
  rw [absent_iff_empty, region_erase, ← Finset.card_eq_zero, Finset.card_erase_of_mem member]
  change (region locals candidate rows world pattern).card - 1 = 0 ↔
    (region locals candidate rows world pattern).card = 1
  have positive := Finset.card_pos.mpr ⟨occurrence, member⟩
  omega

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardSemantics
