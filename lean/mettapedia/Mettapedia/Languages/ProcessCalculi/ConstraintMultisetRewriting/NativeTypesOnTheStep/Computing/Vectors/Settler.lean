import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Vectors.AppendReadings
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.ComputableSettler
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentWorklistSolver
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.ExecutableTowerChoices

/-!
# A computable settler for the vectors package

The tower's computable settler runs the tree's worklist driver with a solver step whose first move
refutes a store at a rigid clash. That move is sound only in a package without computation: in the
vectors package `vec A (succ k)` and `Σ A (vec A k)` are spines of different heads and equal types.
So this package needs its own solver step, and it is built from the tree's parts with the package's
own conversion:

* **the package's executable conversion** (`vecReducer`, from its fourteen rows) drives the typed η
  conversion scan, which discharges the equations the package's conversion makes true;
* **the newest-unknown dispatcher** of the tree solves a definition of the newest declaration, checked
  by the executable checker of the package, with its declared types formed (`vecDeclared`) and the
  tower's head choices (`vecChoices`);
* **nothing is refuted** (`vecRound_never_refutes`): an unsolved store is stuck, never "no".

Every progressing round is an exact transition (`vecRound_progress_exact`: every solution of the
residual store composed with the answer solves the store, and every solution of the store factors
through it) and lowers the rank, the number of declarations and then the number of equations
(`vecRound_progress_lowers`). The worklist driver over this step is a decided family
(`vecFamily`), so the settler of the family is computable (`vecSettler`).

**Deciding admission** (`vecAdmits?`). For a firing without guards or queries whose made rows come
with their own types in their frame, the family settles the information, and each made row must
convert along the answer by the package's executable conversion. It has three outcomes: `some true`
is sound (`vecAdmits?_sound`: the computable converting step admits the firing), `some false` is sound
(`vecAdmits?_refuted`: no settler's converting step admits it), and `none` claims nothing.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing.Vectors

open _root_.CategoryTheory Opposite Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate
open Interface.DependentFull (Make State Firing enabled_iff)
open UnificationWithLevels (InitialSolution)
open TowerNumbersModel (num zero succ numRec ctors u)
open TowerVectorsModel (unit tt add U0 numC zeroC succC unitC ttC vecC addC)
open ProgrammingOnTheStep.IndexedFamilies.Eliminator (level1)

/-! ## The package's declared types are formed -/

/-- **Every declared type of the package is a type.** -/
theorem vecDeclared (lv : LevelExpr Nat) : DeclaredTypesFormed (TowerVectorsModel.rules lv) := by
  intro name type declared
  have D := TowerVectorsModel.vecDeclared_rules lv
  have tw := TowerVectorsModel.towerLike_rules lv
  have family : ∀ {m : Nat} {Δ : Ctx Tower.Head m},
      Typed (TowerVectorsModel.rules lv) Δ (.pi numC U0) (.head (.sort (.max (.const 0) (.succ (.const 0))))) :=
    fun {_ _} => TowerVectorsModel.family_typed tw rfl
  change TowerVectorsModel.constantType lv name = some type at declared
  unfold TowerVectorsModel.constantType at declared
  split at declared
  · cases declared
    exact ⟨u, tw.isUniverse _, tw.pi_small D.num_typed (tw.pi_small D.num_typed D.num_typed)⟩
  split at declared
  · cases declared
    exact D.elimType_typed
  split at declared
  · cases declared
    obtain ⟨w, hw, t⟩ := TowerNumbersModel.recType_typed lv
    exact ⟨w, hw, Derivable.mono (TowerVectorsModel.sub_numbers₂ lv) t⟩
  split at declared
  · cases declared
    obtain ⟨w, hw, t⟩ := TowerVectorsModel.voidRecType_typed lv
    exact ⟨w, hw, Derivable.mono (TowerVectorsModel.sub_void lv) t⟩
  split at declared
  · cases declared
    exact ⟨_, tw.isUniverse _, .piForm D.num_typed (tw.isUniverse _) family (tw.isUniverse _) (tw.join _ _)⟩
  split at declared
  · cases declared
    exact ⟨_, tw.isUniverse _, .piForm family (tw.isUniverse _) family (tw.isUniverse _) (tw.join _ _)⟩
  split at declared
  · cases declared
    obtain ⟨w, hw, typed⟩ := TowerEliminatorModel.elimType_typed (.const 0) lv
    have sub : RulesSub Tower.rules (TowerVectorsModel.rules lv) :=
      ⟨id, id, id, id, id, (fun h => nomatch h), (fun h => nomatch h)⟩
    exact ⟨w, hw, Derivable.mono sub typed⟩
  change (if name = TowerVectorsModel.vec then some TowerVectorsModel.vecType
    else if name = TowerVectorsModel.unitRec then some (recType unit (.sort lv) TowerVectorsModel.unitCtors)
    else TowerVectorsModel.baseStage.constantType name) = some type at declared
  split at declared
  · cases declared
    exact ⟨_, tw.isUniverse _, .piForm tw.u0_typed (tw.isUniverse _) family (tw.isUniverse _) (tw.join _ _)⟩
  split at declared
  · cases declared
    exact tw.unitRecType_typed rfl rfl lv
  change (if name = unit then some (.head u) else if name = tt then some (ctorType unit [])
    else if name = TowerVectorsModel.void then some (.head u)
    else TowerNumbersModel.rules₂.constantType name) = some type at declared
  split at declared
  · cases declared
    exact ⟨_, tw.isUniverse _, .headType (tw.headTyping _)⟩
  split at declared
  · cases declared
    exact ⟨u, tw.isUniverse _, D.unit_typed⟩
  split at declared
  · cases declared
    exact ⟨_, tw.isUniverse _, .headType (tw.headTyping _)⟩
  change (if name = num then some (.head u) else if name = zero then some (ctorType num [])
    else if name = succ then some (ctorType num [.recursive]) else none) = some type at declared
  split at declared
  · cases declared
    exact ⟨_, tw.isUniverse _, .headType (tw.headTyping _)⟩
  split at declared
  · cases declared
    exact ⟨u, tw.isUniverse _, D.num_typed⟩
  split at declared
  · cases declared
    exact ⟨u, tw.isUniverse _, tw.pi_small D.num_typed D.num_typed⟩
  · cases declared

/-! ## The solver step of the package -/

/-- The package at level one, as a setting. -/
abbrev vecS : Setting Tower.Head ℕ := TowerVectorsModel.setting level1 fun _ => 0

instance vecHeadEqDecidable : DecidableRel vecS.R.headEq := fun left right =>
  LevelTower.instDecidableHeadEq left right

instance vecCumulativeDecidable : DecidableRel vecS.R.cumulative := fun left right =>
  LevelTower.instDecidableCumulative left right

instance vecUniverseDecidable (head : Tower.Head) : Decidable (vecS.R.isUniverse head) :=
  inferInstanceAs (Decidable (Tower.IsUniverse head))

/-- The tower's head choices, for the package. -/
def vecChoices : ExecutableChecking.HeadChoices vecS.R where
  typing head := ExecutableTowerChoices.choices.typing head
  join := ExecutableTowerChoices.choices.join

/-- **One round of the package's solver**: discharge the equations the package's conversion makes
true, else define the newest declaration; otherwise stuck. It refutes nothing. -/
def vecRound (fuel : Nat) {Γ : Context vecS.R} (problem : EquationStore (TotalTerm Γ)) :
    ContextualDependentWorklist.Round vecS.levels (ContextualDependentWorklist.size (S := vecS)) problem :=
  if shorter : (Conversion.scan (S := vecS) (TowerVectorsModel.facts level1) (TowerVectorsModel.roots level1)
      (TowerVectorsModel.heads level1) (TowerVectorsModel.algebra level1) (vecReducer level1) fuel
      problem).length < problem.length then
    .progress (ContextualDependentUpdate.conversion (S := vecS) (TowerVectorsModel.facts level1)
      (TowerVectorsModel.roots level1) (TowerVectorsModel.heads level1) (TowerVectorsModel.algebra level1)
      (vecReducer level1) fuel problem) (Prod.Lex.right _ shorter)
  else
    match ContextualDependentWorklist.newestOf (S := vecS) (TowerVectorsModel.facts level1)
        (TowerVectorsModel.roots level1) (TowerVectorsModel.heads level1) (TowerVectorsModel.algebra level1)
        (vecDeclared level1) vecChoices (vecReducer level1) fuel Γ with
    | none => .stuck
    | some view =>
        match ContextualDependentWorklist.throughNewest (S := vecS) view problem
            (ContextualDependentWorklist.dispatchNewest (S := vecS) (TowerVectorsModel.facts level1)
              (TowerVectorsModel.roots level1) (TowerVectorsModel.heads level1)
              (TowerVectorsModel.algebra level1) (vecDeclared level1) vecChoices (vecReducer level1) fuel
              view.type) with
        | none => .stuck
        | some ⟨update, smaller⟩ => .progress update (Prod.Lex.left _ _ smaller)

/-- **The package's solver step.** -/
def vecSolver (fuel : Nat) : ContextualDependentWorklist.Solver vecS.levels where
  rank := ContextualDependentWorklist.size (S := vecS)
  round := vecRound fuel

/-- **The round never refutes**: a store it cannot solve is stuck, never refuted. -/
theorem vecRound_never_refutes (fuel : Nat) {Γ : Context vecS.R} {problem : EquationStore (TotalTerm Γ)}
    (absent : ¬ (frames vecS.levels).Solvable problem) : vecRound fuel problem ≠ .refuted absent := by
  unfold vecRound
  split
  · exact fun same => by cases same
  · split
    · exact fun same => by cases same
    · split
      · exact fun same => by cases same
      · exact fun same => by cases same

/-- **A progressing round lowers the rank**: the number of declarations, then of equations. -/
theorem vecRound_progress_lowers (fuel : Nat) {Γ : Context vecS.R} {problem : EquationStore (TotalTerm Γ)}
    {update : Update vecS.levels problem}
    {smaller : ContextualDependentWorklist.Below (ContextualDependentWorklist.size (S := vecS) update.remaining)
      (ContextualDependentWorklist.size (S := vecS) problem)}
    (_progress : vecRound fuel problem = .progress update smaller) :
    ContextualDependentWorklist.Below (ContextualDependentWorklist.size (S := vecS) update.remaining)
      (ContextualDependentWorklist.size (S := vecS) problem) :=
  smaller

/-- **A progressing round is exact**: solutions of the residual store, composed with the answer,
solve the store, and every solution of the store factors through the answer. -/
theorem vecRound_progress_exact (fuel : Nat) {Γ : Context vecS.R} {problem : EquationStore (TotalTerm Γ)}
    {update : Update vecS.levels problem}
    {smaller : ContextualDependentWorklist.Below (ContextualDependentWorklist.size (S := vecS) update.remaining)
      (ContextualDependentWorklist.size (S := vecS) problem)}
    (_progress : vecRound fuel problem = .progress update smaller) :
    (∀ (Δ : Context vecS.R) (residual : Δ ⟶ update.target),
        (frames vecS.levels).Models residual update.remaining →
          (frames vecS.levels).Models (residual ≫ update.answer) problem) ∧
      ∀ (Δ : Context vecS.R) (solution : Δ ⟶ Γ), (frames vecS.levels).Models solution problem →
        ∃ residual : Δ ⟶ update.target, (frames vecS.levels).Models residual update.remaining ∧
          ∀ term : TotalTerm Γ,
            (frames vecS.levels).E (term.reindex solution) (term.reindex (residual ≫ update.answer)) :=
  ⟨update.sound, update.complete⟩

/-- **The package's decided family**: the worklist driver over the package's solver step. -/
def vecFamily (fuel budget : Nat) : Family vecS.levels :=
  driverFamily vecS.levels (vecSolver fuel) budget

/-- **The package's computable settler.** -/
def vecSettler (fuel budget : Nat) : Settler vecS.levels :=
  Settler.ofFamilies vecS.levels [vecFamily fuel budget]

/-! ## Deciding admission -/

/-- The checks at a settled answer: every made row converts along it by the package's executable
conversion, and the shapes and the enabling hold. -/
def vecChecksAt (fuel : Nat) {s : State vecS.R Nat} (f : Firing vecS.levels s)
    (frameType : ∀ m ∈ f.makes, Σ' B : TypeOver f.helpers.frame, FrameTypedAt m.2 B)
    {M : Context vecS.R} (σ : M ⟶ f.helpers.frame) : Bool :=
  f.makes.attach.all (fun m => (Conversion.compareTypes (S := vecS) (TowerVectorsModel.facts level1)
      (TowerVectorsModel.roots level1) (TowerVectorsModel.heads level1)
      (TowerVectorsModel.algebra level1) (vecReducer level1) fuel ((frameType m.1 m.2).1.reindex σ)
      (m.1.2.type.reindex σ)).isSome) &&
    decide (f.taken.Nodup ∧ f.made.Nodup ∧ f.takes.length = f.taken.length ∧
      f.reads.length = f.read.length) &&
    decide ((∀ o ∈ f.taken, o ∈ s.present) ∧ (∀ o ∈ f.read, o ∈ s.present) ∧
      (∀ o ∈ f.taken, o ∉ f.read) ∧ ∀ o ∈ f.made, o ∉ s.present)

/-- The verdict of admission at a decision on the information. -/
def vecAdmitsAt? (fuel : Nat) {s : State vecS.R Nat} (f : Firing vecS.levels s)
    (frameType : ∀ m ∈ f.makes, Σ' B : TypeOver f.helpers.frame, FrameTypedAt m.2 B) :
    Decision vecS.levels f.information → Option Bool
  | .settled _ σ _ => if vecChecksAt fuel f frameType σ then some true else none
  | .refuted _ => some false
  | .undecided => none

/-- **The decision of admission of the computable converting step over the package**, for a firing
without guards or queries whose made rows come with their own types in their frame. Three outcomes:
`some true` when the first decisive family settles, every made row converts along the answer by the
package's executable conversion, and the shapes and the enabling hold; `some false` when a family
refutes the information; `none` otherwise, which claims nothing: a budget that runs out, or a
conversion not found within it, is not a refusal. -/
def vecAdmits? (families : List (Family vecS.levels)) (fuel : Nat) {s : State vecS.R Nat}
    (f : Firing vecS.levels s)
    (frameType : ∀ m ∈ f.makes, Σ' B : TypeOver f.helpers.frame, FrameTypedAt m.2 B) : Option Bool :=
  if f.guards.isEmpty && f.queries.isEmpty then
    vecAdmitsAt? fuel f frameType (firstDecisionAt vecS.levels f.information families)
  else none

/-- **`some true` is sound**: the computable converting step admits the firing. -/
theorem vecAdmits?_sound {families : List (Family vecS.levels)} {fuel : Nat} {s : State vecS.R Nat}
    {f : Firing vecS.levels s}
    {frameType : ∀ m ∈ f.makes, Σ' B : TypeOver f.helpers.frame, FrameTypedAt m.2 B}
    (decided : vecAdmits? families fuel f frameType = some true) :
    (convertingStep vecS.levels Nat (Settler.ofFamilies vecS.levels families)).Admits f := by
  unfold vecAdmits? at decided
  by_cases empty : (f.guards.isEmpty && f.queries.isEmpty) = true
  · rw [if_pos empty] at decided
    obtain ⟨noGuards, noQueries⟩ := Bool.and_eq_true_iff.mp empty
    have noGuards : f.guards = [] := List.isEmpty_iff.mp noGuards
    have noQueries : f.queries = [] := List.isEmpty_iff.mp noQueries
    cases first : firstDecisionAt vecS.levels f.information families with
    | settled M σ initial =>
        rw [first] at decided
        by_cases checks : vecChecksAt fuel f frameType σ = true
        · unfold vecChecksAt at checks
          simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at checks
          obtain ⟨⟨rows, a, b, c, d⟩, enabled⟩ := checks
          have verdict : Settler.ofFamilies vecS.levels families f.information = .settled M σ initial := by
            unfold Settler.ofFamilies
            rw [first]
            rfl
          rw [converting_admits_iff_of_settled vecS.levels _ noQueries verdict, noGuards]
          refine ⟨⟨a, b, c, d, fun m member => ?_⟩, (enabled_iff f).mpr enabled, Frames.models_nil _⟩
          obtain ⟨certificate, -⟩ := Option.isSome_iff_exists.mp (rows ⟨m, member⟩ (List.mem_attach _ _))
          exact ⟨(frameType m member).1, (frameType m member).2, below_of_typeEq certificate.down⟩
        · have none : vecAdmitsAt? fuel f frameType (.settled M σ initial) = none := by
            simp only [vecAdmitsAt?, checks, if_false, Bool.false_eq_true]
          rw [none] at decided
          cases decided
    | refuted none =>
        rw [first] at decided
        cases decided
    | undecided =>
        rw [first] at decided
        cases decided
  · rw [if_neg empty] at decided
    cases decided

/-- **`some false` is sound**: the information has no solution, so no settler's converting step
admits the firing. -/
theorem vecAdmits?_refuted {families : List (Family vecS.levels)} {fuel : Nat} {s : State vecS.R Nat}
    {f : Firing vecS.levels s}
    {frameType : ∀ m ∈ f.makes, Σ' B : TypeOver f.helpers.frame, FrameTypedAt m.2 B}
    (decided : vecAdmits? families fuel f frameType = some false) (settler : Settler vecS.levels) :
    ¬ (convertingStep vecS.levels Nat settler).Admits f := by
  intro admitted
  unfold vecAdmits? at decided
  by_cases empty : (f.guards.isEmpty && f.queries.isEmpty) = true
  · rw [if_pos empty] at decided
    cases first : firstDecisionAt vecS.levels f.information families with
    | settled M σ initial =>
        rw [first] at decided
        by_cases checks : vecChecksAt fuel f frameType σ = true
        · have some : vecAdmitsAt? fuel f frameType (.settled M σ initial) = some true := by
            simp only [vecAdmitsAt?, checks, if_true]
          rw [some] at decided
          cases decided
        · have none : vecAdmitsAt? fuel f frameType (.settled M σ initial) = none := by
            simp only [vecAdmitsAt?, checks, if_false, Bool.false_eq_true]
          rw [none] at decided
          cases decided
    | refuted none => exact none admitted.2.2.1
    | undecided =>
        rw [first] at decided
        cases decided
  · rw [if_neg empty] at decided
    cases decided

end NativeTypesOnTheStep.Computing.Vectors

#print axioms NativeTypesOnTheStep.Computing.Vectors.vecDeclared
#print axioms NativeTypesOnTheStep.Computing.Vectors.vecChoices
#print axioms NativeTypesOnTheStep.Computing.Vectors.vecRound
#print axioms NativeTypesOnTheStep.Computing.Vectors.vecSolver
#print axioms NativeTypesOnTheStep.Computing.Vectors.vecRound_never_refutes
#print axioms NativeTypesOnTheStep.Computing.Vectors.vecRound_progress_lowers
#print axioms NativeTypesOnTheStep.Computing.Vectors.vecRound_progress_exact
#print axioms NativeTypesOnTheStep.Computing.Vectors.vecFamily
#print axioms NativeTypesOnTheStep.Computing.Vectors.vecSettler
#print axioms NativeTypesOnTheStep.Computing.Vectors.vecAdmits?
#print axioms NativeTypesOnTheStep.Computing.Vectors.vecAdmits?_sound
#print axioms NativeTypesOnTheStep.Computing.Vectors.vecAdmits?_refuted

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
