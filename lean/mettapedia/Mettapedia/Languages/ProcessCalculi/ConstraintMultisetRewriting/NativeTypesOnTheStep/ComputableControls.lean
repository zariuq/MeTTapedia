import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.ComputableSettler
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.ConversionControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentWorklistControls

/-!
# Decided admission in the tower, evaluated by the kernel

**The tower's families** (`towerFamilies`) are the tree's worklist driver with its actual step (rigid
clash check, typed η conversion scan, newest-unknown dispatcher), as a decided family. The settler
`towerSettler` is computable.

**Deciding usability between heads** (`below_heads_iff`): in the tower the ground head is usable only
at itself and a universe exactly at the universes above it (`HeadBelow`, decidable through normal forms
of levels). With `convertsAlong_var_iff` this decides conversion of a variable row whose types at the
answer are heads (`rowConverts?`, `rowConverts?_sound`).

**Deciding admission** (`admits?`): for a firing without guards or queries, the first decisive family
settles (then rows, shapes and enabling are checked at its answer), refutes (refused), or declines
(`none`). It is sound and complete where it answers (`admits?_sound`), so it gives a `Decidable`
instance on its fragment (`decideAdmission`).

**Controls, evaluated by the kernel.**
* The lifting firing (`liftFiring`: helpers `x : U₀`, `Y : U₁`, told `Y ≐ U₀`, made row `x` at `Y`) is the
  first failure in a universe instead of a variable type. Its information is decided by the driver, and
  the computable converting step admits it (`lift_decided`, `lift_admitted`), where the present step
  refuses it (`lift_separation`); its row is typed at every solution (`lift_typedAfterMatch`).
* Telling `Y ≐ Ground` instead, the decision refuses it (`groundLift_decided`, `groundLift_refused`).
* The tree's own heterogeneous store is settled by the family (`twin_settled`), the rigid clash refuted
  (`clash_refuted_by_family`).
* **D2's coerce firing is outside the families**: the driver declines its information
  (`coerce_outside_families`), so the decision answers nothing (`coerce_undecided`). Its unknown type
  `X` is the oldest declaration of its frame and is learned only through a heterogeneous equation; the
  driver solves newest unknowns through homogeneous equations. The semantic converting step admits it
  (`ConversionControls.coerce_converted`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.ComputableControls

open _root_.CategoryTheory Opposite Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface.DependentFull Interface.DependentFull.Controls
open UnificationWithLevels (InitialSolution)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled)

/-! ## Usability between heads -/

/-- **Usability between heads in the tower**: the ground head at itself, a universe at the universes
above it. -/
def HeadBelow : Tower.Head → Tower.Head → Prop
  | .legacyGround, .legacyGround => True
  | .sort l, .sort r => Tower.Cumulative (.sort l) (.sort r)
  | _, _ => False

instance (h h' : Tower.Head) : Decidable (HeadBelow h h') := by
  cases h <;> cases h' <;> unfold HeadBelow <;> infer_instance

/-- **Usability between heads is `HeadBelow`.** -/
theorem below_heads_iff {n : Nat} {Γ : Tower.Ctx n} (formed : CtxFormed Tower.rules Γ)
    (h h' : Tower.Head) : Below Tower.rules Γ (.head h) (.head h') ↔ HeadBelow h h' := by
  constructor
  · intro le
    cases h with
    | legacyGround =>
        have notUniverse : ∀ u, Tower.rules.isUniverse u →
            ¬ TypeEq Tower.rules Γ (.head .legacyGround) (.head u) := by
          intro u hu e
          rcases LevelTower.head_injective e formed with same | same
          · subst same
            cases hu
          · cases u with
            | legacyGround => cases hu
            | sort _ => exact same
        have equal := Below.rigid (S := setting) le formed notUniverse
          (fun A B e => TypeEq.pi_ne_head TowerModel.facts formed e.symm)
          (fun A B e => TypeEq.sigma_ne_head TowerModel.facts formed e.symm)
        rcases LevelTower.head_injective equal formed with same | same
        · subst same
          trivial
        · cases h' with
          | legacyGround => trivial
          | sort _ => exact same.elim
    | sort l =>
        obtain ⟨v, hv, eT, c⟩ := (Below.universe_iff (S := setting) TowerModel.facts TowerModel.algebra
          formed (LevelTower.IsUniverse.sort l)).mp le
        rcases LevelTower.head_injective eT formed with same | same
        · subst same
          cases hv with
          | sort r => exact c
        · cases h' with
          | legacyGround =>
              cases hv with
              | sort r => exact same.elim
          | sort r =>
              cases hv with
              | sort r' =>
                  intro valuation
                  exact (c valuation).trans (le_of_eq (same valuation).symm)
  · intro below
    cases h with
    | legacyGround =>
        cases h' with
        | legacyGround => exact below_refl_of_isType ⟨_, .sort _, ground_typed _⟩
        | sort _ => exact below.elim
    | sort l =>
        cases h' with
        | legacyGround => exact below.elim
        | sort r => exact .subUniv below

/-- The head of a code, when the code is a head. -/
def headCode? {n : Nat} : Tower.Tm n → Option Tower.Head
  | .head h => some h
  | _ => none

theorem headCode?_eq_some {n : Nat} {t : Tower.Tm n} {h : Tower.Head} (some : headCode? t = some h) :
    t = .head h := by
  cases t <;> simp_all [headCode?]

/-- **A decision between two types whose codes are heads.** -/
def headBelow? {n : Nat} (A B : Tower.Tm n) : Option Bool :=
  (headCode? A).bind fun h => (headCode? B).map fun h' => decide (HeadBelow h h')

theorem headBelow?_sound {n : Nat} {Γ : Tower.Ctx n} (formed : CtxFormed Tower.rules Γ)
    {A B : Tower.Tm n} {b : Bool} (decided : headBelow? A B = some b) :
    b = true ↔ Below Tower.rules Γ A B := by
  obtain ⟨h, hA, rest⟩ := Option.bind_eq_some_iff.mp decided
  obtain ⟨h', hB, rfl⟩ := Option.map_eq_some_iff.mp rest
  rw [headCode?_eq_some hA, headCode?_eq_some hB, below_heads_iff formed, decide_eq_true_iff]

/-! ## Deciding conversion of a variable row -/

/-- The variable of a code, when the code is a variable. -/
def varCode? {n : Nat} : Tower.Tm n → Option (Fin n)
  | .var i => some i
  | _ => none

theorem varCode?_eq_some {n : Nat} {t : Tower.Tm n} {i : Fin n} (some : varCode? t = some i) :
    t = .var i := by
  cases t <;> simp_all [varCode?]

/-- **A decision of conversion for a variable row whose types at the answer are heads.** -/
def rowConverts? {M Δ : Context Tower.rules} (σ : M ⟶ Δ) (m : Make Δ) : Option Bool :=
  (varCode? m.code).bind fun i =>
    headBelow? (subst σ.substitution (Ctx.lookup Δ.raw i)) (m.type.reindex σ).code

theorem rowConverts?_sound {M Δ : Context Tower.rules} {σ : M ⟶ Δ} {m : Make Δ} {b : Bool}
    (decided : rowConverts? σ m = some b) : b = true ↔ ConvertsAlong m σ := by
  obtain ⟨i, hi, below⟩ := Option.bind_eq_some_iff.mp decided
  rw [convertsAlong_var_iff m σ (varCode?_eq_some hi)]
  exact headBelow?_sound M.formed below

/-- A decision of conversion for every made row. -/
def rowsConvert? {M Δ : Context Tower.rules} (σ : M ⟶ Δ) : List (Nat × Make Δ) → Option Bool
  | [] => some true
  | m :: rest =>
      match rowConverts? σ m.2, rowsConvert? σ rest with
      | some first, some others => some (first && others)
      | _, _ => none

theorem rowsConvert?_sound {M Δ : Context Tower.rules} (σ : M ⟶ Δ) :
    ∀ {makes : List (Nat × Make Δ)} {b : Bool}, rowsConvert? σ makes = some b →
      (b = true ↔ ∀ m ∈ makes, ConvertsAlong m.2 σ)
  | [], b, decided => by
      simp only [rowsConvert?, Option.some.injEq] at decided
      subst decided
      simp
  | m :: rest, b, decided => by
      unfold rowsConvert? at decided
      cases first : rowConverts? σ m.2 with
      | none => rw [first] at decided; cases decided
      | some a =>
          cases others : rowsConvert? σ rest with
          | none => rw [first, others] at decided; cases decided
          | some c =>
              rw [first, others] at decided
              simp only [Option.some.injEq] at decided
              subst decided
              rw [Bool.and_eq_true, rowConverts?_sound first, rowsConvert?_sound σ others,
                List.forall_mem_cons]

/-! ## Deciding admission -/

/-- **The decision of admission of the computable converting step**, for a firing without guards or
queries: settled, check rows, shapes and enabling at the answer; refuted, refuse; otherwise decline. -/
def admits? (families : List (Family setting.levels)) {s : State setting.R Nat}
    (f : Firing setting.levels s) : Option Bool :=
  if f.guards.isEmpty && f.queries.isEmpty then
    match firstDecisionAt setting.levels f.information families with
    | .settled _ σ _ => (rowsConvert? σ f.makes).map fun rows =>
        rows && decide (f.taken.Nodup ∧ f.made.Nodup ∧ f.takes.length = f.taken.length ∧
          f.reads.length = f.read.length) &&
        decide ((∀ o ∈ f.taken, o ∈ s.present) ∧ (∀ o ∈ f.read, o ∈ s.present) ∧
          (∀ o ∈ f.taken, o ∉ f.read) ∧ ∀ o ∈ f.made, o ∉ s.present)
    | .refuted _ => some false
    | .undecided => none
  else none

/-- **The decision is sound and complete where it answers.** -/
theorem admits?_sound (families : List (Family setting.levels)) {s : State setting.R Nat}
    {f : Firing setting.levels s} {b : Bool} (decided : admits? families f = some b) :
    b = true ↔ (convertingStep setting.levels Nat (Settler.ofFamilies setting.levels families)).Admits f := by
  unfold admits? at decided
  split at decided
  · rename_i empty
    obtain ⟨noGuards, noQueries⟩ := Bool.and_eq_true_iff.mp empty
    have noGuards : f.guards = [] := List.isEmpty_iff.mp noGuards
    have noQueries : f.queries = [] := List.isEmpty_iff.mp noQueries
    cases first : firstDecisionAt setting.levels f.information families with
    | settled M σ initial =>
        rw [first] at decided
        obtain ⟨rows, hrows, rfl⟩ := Option.map_eq_some_iff.mp decided
        have verdict : Settler.ofFamilies setting.levels families f.information = .settled M σ initial := by
          unfold Settler.ofFamilies
          rw [first]
          rfl
        rw [converting_admits_iff_of_settled setting.levels _ noQueries verdict, noGuards,
          Bool.and_eq_true, Bool.and_eq_true, rowsConvert?_sound σ hrows, decide_eq_true_iff,
          decide_eq_true_iff]
        constructor
        · rintro ⟨⟨rowsHold, a, b, c, d⟩, enabled⟩
          exact ⟨⟨a, b, c, d, rowsHold⟩, (enabled_iff f).mpr enabled, Frames.models_nil _⟩
        · rintro ⟨⟨a, b, c, d, rowsHold⟩, enabled, -⟩
          exact ⟨⟨rowsHold, a, b, c, d⟩, (enabled_iff f).mp enabled⟩
    | refuted none =>
        rw [first] at decided
        simp only [Option.some.injEq] at decided
        subst decided
        simp only [Bool.false_eq_true, false_iff]
        exact fun admitted => none admitted.2.2.1
    | undecided =>
        rw [first] at decided
        cases decided
  · cases decided

/-- **Decidable admission on the decided fragment.** -/
def decideAdmission (families : List (Family setting.levels)) {s : State setting.R Nat}
    (f : Firing setting.levels s) {b : Bool} (decided : admits? families f = some b) :
    Decidable ((convertingStep setting.levels Nat (Settler.ofFamilies setting.levels families)).Admits f) :=
  if h : b = true then isTrue ((admits?_sound families decided).mp h)
  else isFalse fun admitted => h ((admits?_sound families decided).mpr admitted)

/-! ## The tower's families -/

/-- The tree's worklist driver with its actual step, as the tower's decided family. -/
def towerFamilies : List (Family setting.levels) :=
  [driverFamily setting.levels ContextualDependentWorklist.Controls.step 4]

/-- **The computable settler of the tower.** -/
def towerSettler : Settler setting.levels := Settler.ofFamilies setting.levels towerFamilies

/-! ## The lifting firing: a universe learned by matching -/

/-- `U₁`, formed over any frame. -/
def bigUniverse (Γ : Context Tower.rules) : TypeOver Γ :=
  ⟨.head (.sort (.succ Tower.zero)), .sort (.succ (.succ Tower.zero)), .sort _, .headType (.sort _)⟩

/-- The frame `x : U₀, Y : U₁`. -/
abbrev liftFrame : Context Tower.rules := extend base (bigUniverse _)

/-- `Y`, as a type over the frame. -/
def yType : TypeOver liftFrame := ⟨.var 0, .sort (.succ Tower.zero), .sort _, Derivable.var 0⟩

/-- **The made row**: `x` at `Y`. -/
def liftRow : Make liftFrame := ⟨yType, .var 1⟩

/-- The told equation `Y ≐ U₀`, at `U₁`. -/
def liftTell : Equation (TotalTerm liftFrame) :=
  ContextualDependentFlex.equation (Γ := base) (type := bigUniverse base)
    ⟨.var 0, Derivable.var 0⟩ ⟨.head (.sort Tower.zero), .headType (.sort _)⟩

/-- Make the helpers `x : U₀` and `Y : U₁`, tell `Y ≐ U₀`, and make the row `1 : x : Y`. -/
def liftFiring : Firing setting.levels emptyState where
  helpers := .cons (smallUniverse _) (.cons (bigUniverse _) (.nil _))
  taken := []
  read := []
  takes := []
  reads := []
  makes := [(1, liftRow)]
  tells := [liftTell]
  guards := []
  queries := []

/-- **Decided by the kernel**: the computable converting step admits the lifting firing. -/
theorem lift_decided : admits? towerFamilies liftFiring = some true := by decide +kernel

/-- **The computable converting step admits the lifting firing.** -/
theorem lift_admitted : (convertingStep setting.levels Nat towerSettler).Admits liftFiring :=
  (admits?_sound towerFamilies lift_decided).mp rfl

/-- `x : U₀` is not of type `Y` in the frame: `U₀` is usable only at universes, and the variable type
`Y` is no universe. -/
theorem lift_not_wellTyped : ¬ liftRow.WellTyped := by
  intro typed
  have le : TypeLe Tower.rules liftFrame.raw (.head (.sort Tower.zero)) (.var 0) := Typed.generation typed
  have formed : CtxFormed Tower.rules liftFrame.raw := liftFrame.formed
  have below : Below Tower.rules liftFrame.raw (.head (.sort Tower.zero)) (.var 0) :=
    TypeLe.toBelow le yType.isType
  obtain ⟨v, -, eT, -⟩ := (Below.universe_iff (S := setting) TowerModel.facts TowerModel.algebra formed
    (LevelTower.IsUniverse.sort _)).mp below
  have neutral : Neutral (TowerModel.roles (L := Nat)) (.var 0 : Tower.Tm 2) := .var 0
  exact (TypeEq.neutral_form (TowerModel.facts (L := Nat)) eT formed neutral (.inl ⟨v, rfl⟩)).not_former.1
    v rfl

/-- **The separation**: the computable converting step admits the lifting firing, the present step
refuses it. -/
theorem lift_separation :
    (convertingStep setting.levels Nat towerSettler).Admits liftFiring ∧
      ¬ (step setting.levels Nat).Admits liftFiring :=
  ⟨lift_admitted, fun admitted => lift_not_wellTyped (admitted.1.2.2.2.2 (1, liftRow) (List.mem_singleton_self _))⟩

/-- **Its row is typed at every solution of its information**, by the soundness of the converting
step. -/
theorem lift_typedAfterMatch : TypedAfterMatch setting.levels liftFiring.information liftRow :=
  converting_typedAfterMatch setting.levels towerSettler lift_admitted (1, liftRow) (List.mem_singleton_self _)

/-! ## Telling `Y ≐ Ground` instead: refused -/

/-- The told equation `Y ≐ Ground`, at `U₁`. -/
def groundTell : Equation (TotalTerm liftFrame) :=
  ContextualDependentFlex.equation (Γ := base) (type := bigUniverse base)
    ⟨.var 0, Derivable.var 0⟩ ⟨ground, .cumul (ground_typed _) (fun _ => Nat.le_succ _)⟩

/-- The lifting firing with `Y ≐ Ground` told. -/
def groundLiftFiring : Firing setting.levels emptyState :=
  { liftFiring with tells := [groundTell] }

/-- **Decided by the kernel**: refused, since `U₀` is not usable at `Ground`. -/
theorem groundLift_decided : admits? towerFamilies groundLiftFiring = some false := by decide +kernel

theorem groundLift_refused : ¬ (convertingStep setting.levels Nat towerSettler).Admits groundLiftFiring :=
  fun admitted => Bool.false_ne_true ((admits?_sound towerFamilies groundLift_decided).mpr admitted)

/-! ## The tree's own stores, and D2's coerce store -/

/-- **The tree's heterogeneous store, woken after its type solution, is settled by the family.** -/
theorem twin_settled :
    (driverFamily setting.levels ContextualDependentWorklist.Controls.step 4
      ContextualDependentWorklist.Controls.twinStore).isSettled = true := by decide +kernel

/-- **The rigid clash is refuted by the family.** -/
theorem clash_refuted_by_family :
    (driverFamily setting.levels ContextualDependentWorklist.Controls.step 4
      ContextualDependentWorklist.Controls.clash).isRefuted = true := by decide +kernel

/-- **D2's coerce store is outside the family**: the driver neither settles nor refutes it. -/
theorem coerce_outside_families :
    (driverFamily setting.levels ContextualDependentWorklist.Controls.step 4
        ProgrammingOnTheStep.Refinement.coerceFiring.information).isSettled = false ∧
      (driverFamily setting.levels ContextualDependentWorklist.Controls.step 4
        ProgrammingOnTheStep.Refinement.coerceFiring.information).isRefuted = false := by
  decide +kernel

/-- ... **so the decision answers nothing on the coerce firing.** -/
theorem coerce_undecided : admits? towerFamilies ProgrammingOnTheStep.Refinement.coerceFiring = none := by
  decide +kernel

end NativeTypesOnTheStep.ComputableControls

#print axioms NativeTypesOnTheStep.ComputableControls.below_heads_iff
#print axioms NativeTypesOnTheStep.ComputableControls.headBelow?_sound
#print axioms NativeTypesOnTheStep.ComputableControls.rowConverts?_sound
#print axioms NativeTypesOnTheStep.ComputableControls.rowsConvert?_sound
#print axioms NativeTypesOnTheStep.ComputableControls.admits?_sound
#print axioms NativeTypesOnTheStep.ComputableControls.decideAdmission
#print axioms NativeTypesOnTheStep.ComputableControls.towerSettler
#print axioms NativeTypesOnTheStep.ComputableControls.lift_decided
#print axioms NativeTypesOnTheStep.ComputableControls.lift_admitted
#print axioms NativeTypesOnTheStep.ComputableControls.lift_not_wellTyped
#print axioms NativeTypesOnTheStep.ComputableControls.lift_separation
#print axioms NativeTypesOnTheStep.ComputableControls.lift_typedAfterMatch
#print axioms NativeTypesOnTheStep.ComputableControls.groundLift_decided
#print axioms NativeTypesOnTheStep.ComputableControls.groundLift_refused
#print axioms NativeTypesOnTheStep.ComputableControls.twin_settled
#print axioms NativeTypesOnTheStep.ComputableControls.clash_refuted_by_family
#print axioms NativeTypesOnTheStep.ComputableControls.coerce_outside_families
#print axioms NativeTypesOnTheStep.ComputableControls.coerce_undecided

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
