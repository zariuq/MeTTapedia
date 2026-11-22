import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.OlderUnknown
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MillerInitialControls

/-!
# The unifier's Miller family in the computable settler, its answers trimmed

The tree's fibre solves Miller pattern stores over telescopes of universe families
(`UnificationWithLevels.TreeFibre.Miller.millerGlbSolver`). Its solved runs end with principal answers that
keep every unknown, solved or not, so they are not initial; deleting the unknowns an answer does not mention
makes them initial (`Miller.initial_of_patternTrimmed`). The tree proves that an initial solution exists
(`Miller.millerGlb_solved_initial`), choosing the families of the answer's frame classically.

**The Miller family** (`millerFamily`) computes the trimmed answer itself:
* membership in the fragment is decided (`Miller.inMillerGlbB`), with its certificate;
* a solved run's answer frame is read back declaration by declaration as universe families, the reading
  checked (`views?`), so the trimming (`trimOut`) is computed;
* the trimmed answer is initial by the pattern trimming theorem, its pattern coverage given by the run's
  invariant (`Miller.drive_inv`); a refuted run refutes; anything else declines.

It joins the computable settler after the tower's and the older-unknown families (`allFamilies`,
`allSettler`), which agrees with the semantic settler on the union of the decided fragments
(`all_agrees_ideal`).

**Controls, evaluated by the kernel.** The store `λ x y z. F x y ≐ λ x y z. G y z` of the fibre's controls,
where both sides are pruned in place: the earlier families leave it undecided (`both_older_undecided`), the
Miller family settles it along its trimmed answer (`both_settled`), the computable converting step admits a
firing at it (`bothFiring_decided`), where the earlier settler declines (`bothFiring_older_undecided`). A store
outside the fragment, D2's coerce store, the Miller family declines (`coerce_miller_declined`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.MillerFamily

open _root_.CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate
open Interface.DependentFull Interface.DependentFull.Controls
open UnificationWithLevels (InitialSolution Agree)
open UnificationWithLevels.TreeFibre (famCode trimOut trimCtx AllUniverses)
open ComputableControls OlderUnknown

/-- The fibre's Miller solver of the tower. -/
abbrev millerTower : ContextualDependentWorklist.Solver setting.levels :=
  UnificationWithLevels.TreeFibre.Miller.Controls.millerGlbTower

/-- The fibre's inhabitants of the tower's universes. -/
abbrev towerInh : UnificationWithLevels.TreeFibre.Miller.Inhabitants setting.R :=
  UnificationWithLevels.TreeFibre.Miller.Controls.towerInh

/-! ## Reading a frame as universe families -/

/-- A declaration read as a universe family, by default `Ground`. -/
def readView (Δ : Context setting.R) (j : Fin Δ.arity) : List Tower.Head × Tower.Head :=
  (UnificationWithLevels.TreeFibre.Miller.readFam (Ctx.lookup Δ.raw j)).getD ([], .legacyGround)

/-- **The family views of a frame**: every declaration read as a universe family, the reading checked. -/
def views? (Δ : Context setting.R) :
    Option {view : Fin Δ.arity → List Tower.Head × Tower.Head //
      (∀ j, Ctx.lookup Δ.raw j = famCode (view j).1 (view j).2) ∧
        ∀ j, (∀ p ∈ (view j).1, setting.R.isUniverse p) ∧ setting.R.isUniverse (view j).2} :=
  if h : (∀ j, Ctx.lookup Δ.raw j = famCode (readView Δ j).1 (readView Δ j).2) ∧
      ∀ j, (∀ p ∈ (readView Δ j).1, setting.R.isUniverse p) ∧ setting.R.isUniverse (readView Δ j).2 then
    some ⟨readView Δ, h⟩
  else none

/-! ## The family -/

/-- **The Miller family**: on a store of the fragment, a solved run settles along its trimmed answer, a
refuted run refutes; every other store is declined. -/
def millerFamily (fuel : Nat) : Family setting.levels := fun I =>
  if inside : UnificationWithLevels.TreeFibre.Miller.inMillerGlbB (S := setting) I = true then
    match solved : ContextualDependentWorklist.run millerTower I fuel with
    | .solved state finished =>
        match views? state.target with
        | some v =>
            .settled _
              (trimOut v.val v.property.1 (fun j => v.property.2 j) towerInh
                (UnificationWithLevels.TreeFibre.Miller.mentionedOf state.answer) ≫ state.answer)
              (UnificationWithLevels.TreeFibre.Miller.initial_of_patternTrimmed (S := setting)
                TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
                ContextualDependentPiSpine.Controls.rigid TowerModel.complete towerInh
                (state.completed finished) v.val v.property.1 (fun j => v.property.2 j)
                (UnificationWithLevels.TreeFibre.Miller.drive_inv (S := setting) TowerModel.facts
                  TowerModel.roots TowerModel.heads TowerModel.algebra ContextualDependentPiSpine.Controls.rigid
                  TowerModel.complete ContextualDependentGeneralPattern.DispatchControls.tower_normalizes towerInh
                  ContextualDependentNormalCheckingTower.head_typing_unique
                  UnificationWithLevels.TreeFibre.LevelGlb.towerGlb
                  UnificationWithLevels.TreeFibre.LevelGlb.towerGlb_isGlb fuel
                  (Update.pending setting.levels I)
                  (UnificationWithLevels.TreeFibre.Miller.MillerInv.pending
                    (UnificationWithLevels.TreeFibre.Miller.inMillerGlb_of_B I inside).families I)
                  (UnificationWithLevels.TreeFibre.Miller.inMillerGlb_of_B I inside) state finished
                  solved).1.covered)
        | none => .undecided
    | .refuted absent => .refuted absent
    | .stuck _ => .undecided
    | .cutoff _ => .undecided
  else .undecided

/-- **The computable settler's families**: the tower's driver, the older-unknown family, and the Miller
family. -/
def allFamilies : List (Family setting.levels) :=
  olderFamilies ++ ([millerFamily 6] : List (Family setting.levels))

/-- **The computable settler with the Miller family.** -/
def allSettler : Settler setting.levels := Settler.ofFamilies setting.levels allFamilies

/-- **On the union of the decided fragments the computable settler agrees with the semantic one.** -/
theorem all_agrees_ideal {Δ : Context setting.R} {I : EquationStore (TotalTerm Δ)}
    (decided : DecidedBy setting.levels allFamilies I) :
    ((∃ (M : Context setting.R) (σ : M ⟶ Δ) (initial : InitialSolution (frames setting.levels) I σ),
        allSettler I = .settled M σ initial) ↔ (frames setting.levels).Solvable I) ∧
      ((∃ (M : Context setting.R) (σ : M ⟶ Δ) (initial : InitialSolution (frames setting.levels) I σ),
        Settler.ideal setting.levels I = .settled M σ initial) ↔ (frames setting.levels).Solvable I) ∧
      ∀ (M M' : Context setting.R) (σ : M ⟶ Δ) (σ' : M' ⟶ Δ)
        (initial : InitialSolution (frames setting.levels) I σ)
        (initial' : InitialSolution (frames setting.levels) I σ'),
        allSettler I = .settled M σ initial → Settler.ideal setting.levels I = .settled M' σ' initial' →
        ∃ (g : M ⟶ M') (g' : M' ⟶ M), Agree (frames setting.levels) σ (g ≫ σ') ∧
          Agree (frames setting.levels) σ' (g' ≫ σ) ∧ Agree (frames setting.levels) (g ≫ g') (𝟙 M) ∧
          Agree (frames setting.levels) (g' ≫ g) (𝟙 M') :=
  ofFamilies_agrees_ideal setting.levels decided

/-- **The converting and templating steps with this settler admit what the semantic settler's admit**, on
the union of the decided fragments. -/
theorem all_steps_iff_ideal {s : State setting.R Nat} {f : Firing setting.levels s}
    (decided : DecidedBy setting.levels allFamilies f.information) :
    ((convertingStep setting.levels Nat allSettler).Admits f ↔
        (convertingStep setting.levels Nat (Settler.ideal setting.levels)).Admits f) ∧
      ((templatingStep setting.levels Nat allSettler).Admits f ↔
        (templatingStep setting.levels Nat (Settler.ideal setting.levels)).Admits f) :=
  ⟨ofFamilies_converting_iff_ideal setting.levels allFamilies decided,
    ofFamilies_templating_iff_ideal setting.levels allFamilies decided⟩

/-! ## Controls -/

open UnificationWithLevels.TreeFibre.Miller.Controls (bothStore ctxB binB ctxBB)

/-- **The earlier families leave the store pruned on both sides undecided.** -/
theorem both_older_undecided :
    (firstDecisionAt setting.levels bothStore olderFamilies).isSettled = false ∧
      (firstDecisionAt setting.levels bothStore olderFamilies).isRefuted = false := by
  decide +kernel

/-- **The Miller family settles it, along its trimmed answer.** -/
theorem both_settled : (millerFamily 6 bothStore).isSettled = true := by decide +kernel

/-- The state at the store pruned on both sides: its frame `F G : U₀ → U₀ → U₀`, the store as knowledge. -/
def bothState : State setting.R Nat := ⟨ctxBB, bothStore, ∅, fun _ => Elimination.last ctxB binB⟩

/-- A firing at that state that reads its knowledge and makes nothing. -/
def bothFiring : Firing setting.levels bothState where
  helpers := .nil _
  taken := []
  read := []
  takes := []
  reads := []
  makes := []
  tells := []
  guards := []
  queries := []

/-- **Decided by the kernel: the computable converting step admits it**, settling along the trimmed answer. -/
theorem bothFiring_decided : admits? allFamilies bothFiring = some true := by decide +kernel

/-- **The earlier computable settler declines it.** -/
theorem bothFiring_older_undecided : admits? olderFamilies bothFiring = none := by decide +kernel

/-- **Outside the fragment the Miller family declines**: D2's coerce store is not over universe families. -/
theorem coerce_miller_declined :
    (millerFamily 6 ProgrammingOnTheStep.Refinement.coerceFiring.information).isSettled = false ∧
      (millerFamily 6 ProgrammingOnTheStep.Refinement.coerceFiring.information).isRefuted = false := by
  decide +kernel

end NativeTypesOnTheStep.MillerFamily

#print axioms NativeTypesOnTheStep.MillerFamily.views?
#print axioms NativeTypesOnTheStep.MillerFamily.millerFamily
#print axioms NativeTypesOnTheStep.MillerFamily.allSettler
#print axioms NativeTypesOnTheStep.MillerFamily.all_agrees_ideal
#print axioms NativeTypesOnTheStep.MillerFamily.all_steps_iff_ideal
#print axioms NativeTypesOnTheStep.MillerFamily.both_older_undecided
#print axioms NativeTypesOnTheStep.MillerFamily.both_settled
#print axioms NativeTypesOnTheStep.MillerFamily.bothFiring_decided
#print axioms NativeTypesOnTheStep.MillerFamily.bothFiring_older_undecided
#print axioms NativeTypesOnTheStep.MillerFamily.coerce_miller_declined

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
