import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Vectors.FamilyLimits
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentClosedBoundary

/-!
# The four acceptance tests, on the repaired step over the qualified vectors package

The four permanent acceptance tests of `ProgrammingOnTheStep.AcceptanceTests`, asked again of the
converting step over the qualified package with vectors, their eliminator and declared addition, with
the package's computable settler. Each tempting law still fails there; three of them for the reason
they failed before, and the first for a new one.

1. **A solvable store with no principal answer** (`principalLaw_fails`). The package's computation
   enters the knowledge, so unification is modulo it, and it is not unitary: `add x y ≐ 1` over
   `x y : num` is solved by `x ↦ 0, y ↦ 1` and by `x ↦ 1, y ↦ 0`, and has no principal answer. The
   package's settler postpones it, neither settling nor refuting (`principal_test_postponed`). The
   store is outside the pattern fragment; whether the tower's pattern-fragment witness keeps its
   failure over this package is not settled here.
2. **The none query against framing** (`frameLaw_fails`). The dependent step has a none query. The firing
   that makes a number `0` where no present row is `0` is admitted at the empty state and refused
   beside a present `0`, for every settler, although its made label avoids the added row and the
   knowledge is untouched. What holds (`frame_test_graded`): a firing without queries keeps its
   admission under framing, for every settler.
3. **Pairwise compatibility without a joint wave** (`waveLaw_fails`). Over `X Y : num`, the tells
   `X ≐ Y`, `X ≐ 0`, `Y ≐ 1` are admitted two by two in one firing, decided by the kernel for the
   package's settler and holding for every settler (`wave_pairs_admitted`), and the three together are
   refused for every settler (`wave_triple_refused`). The law is read here with joint firings, not
   with runs and residuals.
4. **Solvable without being inhabited** (`inhabitationLaw_fails`). `i ≐ i` over `i : fin 0` is solved
   by the identity and has no closed solution, `fin 0` being empty. On the step, the firing that makes
   a helper `i : fin 0` and tells `i ≐ i` is admitted, decided by the kernel, and its information has
   no closed solution (`admitted_not_closed`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ProgrammingOnTheStep.IndexedFamilies.AcceptanceOnTheRepairedStep

open _root_.CategoryTheory Opposite Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentClosedBoundary
open Interface.DependentFull (Make State Firing enabled_iff)
open NativeTypesOnTheStep NativeTypesOnTheStep.Computing.Vectors
open TowerNumbersModel (num zero succ ctors u mem_zero mem_succ)
open TowerVectorsModel (U0 numC zeroC succC finC)
open ProgrammingOnTheStep.IndexedFamilies.Eliminator (level1 pkg D numType)

/-! ## 1. A solvable store with no principal answer -/

section Principal

/-- **The tempting law, over the vectors package**: every solvable store of its fibre has a principal
answer. -/
def PrincipalLaw : Prop :=
  ∀ {Γ : Context vecS.R} (K : EquationStore (TotalTerm Γ)),
    (frames vecS.levels).Solvable K → ∃ (Δ : Context vecS.R) (σ : Δ ⟶ Γ), (frames vecS.levels).Principal K σ

/-- **Test 1: the law still fails**, at `add x y ≐ 1`. -/
theorem principalLaw_fails : ¬ PrincipalLaw := by
  intro law
  obtain ⟨_, σ, principal⟩ := law addStore addStore_solvable
  exact addStore_no_principal σ principal

/-- **What holds at the test**: the store is solvable, has no principal answer, and the package's
settler neither settles nor refutes it. -/
theorem principal_test_postponed :
    (frames vecS.levels).Solvable addStore ∧
      (∀ {Δ : Context pkg} (σ : Δ ⟶ addFrame), ¬ (frames vecS.levels).Principal addStore σ) ∧
      (vecFamily 16 4 addStore).isSettled = false ∧ (vecFamily 16 4 addStore).isRefuted = false :=
  ⟨addStore_solvable, fun σ => addStore_no_principal σ, addStore_postponed⟩

end Principal

/-! ## 2. The none query against framing -/

section Framing

/-- A state framed by more present rows, read by the state's own labels. -/
def frameBy (s : State pkg Nat) (E : Finset Nat) : State pkg Nat :=
  ⟨s.frame, s.knowledge, s.present ∪ E, s.label⟩

/-- The same firing at the framed state, field for field. -/
def reframe {s : State pkg Nat} (f : Firing vecS.levels s) (E : Finset Nat) :
    Firing vecS.levels (frameBy s E) :=
  ⟨f.helpers, f.taken, f.read, f.takes, f.reads, f.makes, f.tells, f.guards, f.queries⟩

/-- **The tempting law (the frame rule) on the converting step**: an admitted firing stays admitted
beside more present rows its made labels avoid; the knowledge is untouched. -/
def FrameLaw (settler : Settler vecS.levels) : Prop :=
  ∀ (s : State pkg Nat) (E : Finset Nat) (f : Firing vecS.levels s),
    (convertingStep vecS.levels Nat settler).Admits f → (∀ o ∈ f.made, o ∉ E) →
      (convertingStep vecS.levels Nat settler).Admits (reframe f E)

/-- The row `0 : num`, closed. -/
def zeroRow : TotalTerm (empty pkg) := ⟨numType _, ⟨zeroC, D.zero_typed⟩⟩

/-- The empty state. -/
def emptyState : State pkg Nat := ⟨empty pkg, [], ∅, fun _ => zeroRow⟩

/-- **`spawn`**: make the row `1 : 0` where no present row is `0`. -/
def spawn (s : State pkg Nat) (closed : s.frame = empty pkg) : Firing vecS.levels s where
  helpers := .nil _
  taken := []
  read := []
  takes := []
  reads := []
  makes := [(1, ⟨closed ▸ numType _, closed ▸ zeroC⟩)]
  tells := []
  guards := []
  queries := [DependentFull.Query.predicate vecS.levels Nat .none (closed ▸ zeroRow)]

/-- `spawn` at the empty state. -/
abbrev spawnEmpty : Firing vecS.levels emptyState := spawn emptyState rfl

/-- **`spawn` is admitted at the empty state, by every settler.** -/
theorem spawn_admitted (settler : Settler vecS.levels) :
    (convertingStep vecS.levels Nat settler).Admits spawnEmpty := by
  apply converting_admits_of_admits vecS.levels settler
  refine ⟨⟨List.nodup_nil, List.nodup_singleton _, rfl, rfl, fun m member => ?_⟩,
    (enabled_iff spawnEmpty).mpr ⟨fun _ member => absurd member List.not_mem_nil,
      fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil,
      fun o _ inside => Finset.notMem_empty o inside⟩,
    ⟨empty pkg, 𝟙 _, Frames.models_nil _⟩, fun _ _ _ => ⟨Frames.models_nil _, fun q member => ?_⟩⟩
  · obtain rfl := List.mem_singleton.mp member
    exact D.zero_typed
  · obtain rfl := List.mem_singleton.mp member
    exact (DependentFull.Query.predicate_holds_iff .none _ _ _ _).mpr fun o inside =>
      absurd inside (Finset.notMem_empty o)

/-- **Beside a present `0`, `spawn` is refused, by every settler.** -/
theorem spawn_refused_beside (settler : Settler vecS.levels) :
    ¬ (convertingStep vecS.levels Nat settler).Admits (reframe spawnEmpty {0}) := by
  rintro ⟨-, -, ⟨Θ, τ, solved⟩, holds⟩
  have query := (holds Θ τ solved).2 _ (List.mem_singleton_self _)
  have none := (DependentFull.Query.predicate_holds_iff .none _ _ _ _).mp query
  exact none 0 (by simp [frameBy, emptyState]) (((frames vecS.levels).equivalence Θ).refl _)

/-- **Test 2: the frame law fails on the repaired step**, for every settler. -/
theorem frameLaw_fails (settler : Settler vecS.levels) : ¬ FrameLaw settler := fun law =>
  spawn_refused_beside settler
    (law emptyState {0} spawnEmpty (spawn_admitted settler) (by simp [Firing.made, spawnEmpty, spawn]))

/-- **What holds at the test**: a firing without queries keeps its admission beside present rows its
made labels avoid, for every settler. -/
theorem frame_test_graded (settler : Settler vecS.levels) {s : State pkg Nat} {E : Finset Nat}
    {f : Firing vecS.levels s} (noQueries : f.queries = [])
    (admitted : (convertingStep vecS.levels Nat settler).Admits f) (avoid : ∀ o ∈ f.made, o ∉ E) :
    (convertingStep vecS.levels Nat settler).Admits (reframe f E) := by
  obtain ⟨shapes, enabled, solvable, holds⟩ := admitted
  obtain ⟨taken, read, apart, fresh⟩ := (enabled_iff f).mp enabled
  refine ⟨shapes, (enabled_iff (reframe f E)).mpr ⟨fun o member => Finset.mem_union_left _ (taken o member),
    fun o member => Finset.mem_union_left _ (read o member), apart, fun o member inside => ?_⟩, solvable,
    fun Θ τ solved => ⟨(holds Θ τ solved).1, fun q member => ?_⟩⟩
  · rcases Finset.mem_union.mp inside with present | added
    · exact fresh o member present
    · exact avoid o member added
  · have : q ∈ f.queries := member
    rw [noQueries] at this
    exact absurd this List.not_mem_nil

end Framing

/-! ## 3. Pairwise compatibility without a joint wave -/

section Wave

/-- `X`, over `X Y : num`. -/
def xTerm : TotalTerm addFrame := ⟨numType _, ⟨.var 1, Derivable.var (1 : Fin 2)⟩⟩

/-- `Y`, over `X Y : num`. -/
def yTerm : TotalTerm addFrame := ⟨numType _, ⟨.var 0, Derivable.var (0 : Fin 2)⟩⟩

/-- `X ≐ Y`. -/
def sameEq : Equation (TotalTerm addFrame) := (xTerm, yTerm)

/-- `X ≐ 0`. -/
def zeroEq : Equation (TotalTerm addFrame) := (xTerm, ⟨numType _, ⟨zeroC, D.zero_typed⟩⟩)

/-- `Y ≐ 1`. -/
def oneEq : Equation (TotalTerm addFrame) := (yTerm, ⟨numType _, ⟨one, D.succ_typed D.zero_typed⟩⟩)

/-- The state over `X Y : num`, with nothing present. -/
def waveState : State pkg Nat := ⟨addFrame, [], ∅, fun _ => xTerm⟩

/-- **One firing telling a list of equations**, nothing taken or made. -/
def tellFiring (tells : EquationStore (TotalTerm addFrame)) : Firing vecS.levels waveState where
  helpers := .nil _
  taken := []
  read := []
  takes := []
  reads := []
  makes := []
  tells := tells
  guards := []
  queries := []

/-- No made rows. -/
def noRows (tells : EquationStore (TotalTerm addFrame)) :
    ∀ m ∈ (tellFiring tells).makes, Σ' B : TypeOver (tellFiring tells).helpers.frame, FrameTypedAt m.2 B :=
  fun _ member => absurd member List.not_mem_nil

theorem same_zero_decided : vecAdmits? [vecFamily 16 4] 16 (tellFiring [sameEq, zeroEq]) (noRows _) = some true := by
  decide +kernel

theorem same_one_decided : vecAdmits? [vecFamily 16 4] 16 (tellFiring [sameEq, oneEq]) (noRows _) = some true := by
  decide +kernel

theorem zero_one_decided : vecAdmits? [vecFamily 16 4] 16 (tellFiring [zeroEq, oneEq]) (noRows _) = some true := by
  decide +kernel

/-- A telling firing is admitted by every settler once one admits it: with no made rows the settler
does not enter its admission. -/
theorem tell_admitted_every {tells : EquationStore (TotalTerm addFrame)} {settler' : Settler vecS.levels}
    (admitted : (convertingStep vecS.levels Nat settler').Admits (tellFiring tells)) (settler : Settler vecS.levels) :
    (convertingStep vecS.levels Nat settler).Admits (tellFiring tells) := by
  obtain ⟨⟨a, b, c, d, _⟩, enabled, solvable, holds⟩ := admitted
  exact ⟨⟨a, b, c, d, fun _ member => absurd member List.not_mem_nil⟩, enabled, solvable, holds⟩

/-- **The three pairs are admitted, decided by the kernel for the package's settler, and so for every
settler.** -/
theorem wave_pairs_admitted (settler : Settler vecS.levels) :
    (convertingStep vecS.levels Nat settler).Admits (tellFiring [sameEq, zeroEq]) ∧
      (convertingStep vecS.levels Nat settler).Admits (tellFiring [sameEq, oneEq]) ∧
      (convertingStep vecS.levels Nat settler).Admits (tellFiring [zeroEq, oneEq]) :=
  ⟨tell_admitted_every (vecAdmits?_sound same_zero_decided) settler,
    tell_admitted_every (vecAdmits?_sound same_one_decided) settler,
    tell_admitted_every (vecAdmits?_sound zero_one_decided) settler⟩

/-- `X ≐ Y`, `X ≐ 0`, `Y ≐ 1` together have no solution: `0` and `1` are different numbers. -/
theorem triple_unsolvable :
    ¬ (frames vecS.levels).Solvable (tellFiring [sameEq, zeroEq, oneEq]).information := by
  rintro ⟨Θ, τ, solved⟩
  have formed : CtxFormed pkg Θ.raw := Θ.formed
  have same : Equal pkg Θ.raw (τ.substitution (1 : Fin 2)) (τ.substitution (0 : Fin 2)) numC :=
    ((equivalent_iff vecS.levels _ _).mp
      (solved sameEq (List.mem_append_right _ (List.mem_cons_self ..)))).2
  have atZero : Equal pkg Θ.raw (τ.substitution (1 : Fin 2)) zeroC numC :=
    ((equivalent_iff vecS.levels _ _).mp
      (solved zeroEq (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))).2
  have atOne : Equal pkg Θ.raw (τ.substitution (0 : Fin 2)) one numC :=
    ((equivalent_iff vecS.levels _ _).mp
      (solved oneEq (List.mem_append_right _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))).2
  exact num_ctor_apart formed mem_zero mem_succ (by decide) (as := []) (bs := [zeroC])
    (.trans (.symm atZero) (.trans same atOne))

/-- **The three together are refused, for every settler.** -/
theorem wave_triple_refused (settler : Settler vecS.levels) :
    ¬ (convertingStep vecS.levels Nat settler).Admits (tellFiring [sameEq, zeroEq, oneEq]) :=
  fun admitted => triple_unsolvable admitted.2.2.1

/-- **A witness for `frame_test_graded`**: the telling firing `X ≐ Y, X ≐ 0` keeps its admission
beside the present row `7`. -/
theorem frame_test_witness (settler : Settler vecS.levels) :
    (convertingStep vecS.levels Nat settler).Admits (reframe (tellFiring [sameEq, zeroEq]) {7}) :=
  frame_test_graded settler rfl (wave_pairs_admitted settler).1 (fun _ member => absurd member List.not_mem_nil)

/-- **The tempting law, with joint firings**: three tells that fire together two by two fire together. -/
def WaveLaw (settler : Settler vecS.levels) : Prop :=
  ∀ a b c : Equation (TotalTerm addFrame),
    (convertingStep vecS.levels Nat settler).Admits (tellFiring [a, b]) →
    (convertingStep vecS.levels Nat settler).Admits (tellFiring [a, c]) →
    (convertingStep vecS.levels Nat settler).Admits (tellFiring [b, c]) →
    (convertingStep vecS.levels Nat settler).Admits (tellFiring [a, b, c])

/-- **Test 3: the law fails on the repaired step**, for every settler. -/
theorem waveLaw_fails (settler : Settler vecS.levels) : ¬ WaveLaw settler := fun law =>
  wave_triple_refused settler (law sameEq zeroEq oneEq (wave_pairs_admitted settler).1
    (wave_pairs_admitted settler).2.1 (wave_pairs_admitted settler).2.2)

end Wave

/-! ## 4. Solvable without being inhabited -/

section Inhabitation

/-- **The tempting law, over the vectors package**: a solvable store of its fibre has a closed
solution. -/
def InhabitationLaw : Prop :=
  ∀ {Γ : Context vecS.R} (K : EquationStore (TotalTerm Γ)),
    (frames vecS.levels).Solvable K → ClosedSolvable (S := vecS) K

/-- `fin 0`, the type of indices into the empty vector. -/
def finZeroType : TypeOver (empty pkg) :=
  ⟨finC zeroC, u, LevelTower.IsUniverse.sort _, TowerVectorsLookup.fin_typed level1 D.zero_typed⟩

/-- The frame `i : fin 0`. -/
abbrev finFrame : Context pkg := extend (empty pkg) finZeroType

/-- **`i ≐ i`, over `i : fin 0`.** -/
def finStore : EquationStore (TotalTerm finFrame) :=
  [(Elimination.last (empty pkg) finZeroType, Elimination.last (empty pkg) finZeroType)]

theorem finStore_solvable : (frames vecS.levels).Solvable finStore :=
  ⟨finFrame, 𝟙 _, fun e member => by
    obtain rfl := List.mem_singleton.mp member
    exact ((frames vecS.levels).equivalence _).refl _⟩

/-- **`fin 0` has no closed point**: a closed solution would be a closed index into the empty vector. -/
theorem finStore_not_closed : ¬ ClosedSolvable (S := vecS) finStore := by
  rintro ⟨σ, -⟩
  have typed : Typed pkg Ctx.nil (σ.substitution 0) (finC zeroC) := σ.typed 0
  exact TowerVectorsLookup.fin_zero_empty level1 typed

/-- **Test 4: the law fails on the repaired package**, at `i ≐ i` over `i : fin 0`. -/
theorem inhabitationLaw_fails : ¬ InhabitationLaw := fun law =>
  finStore_not_closed (law finStore finStore_solvable)

/-- **The firing that makes a helper `i : fin 0` and tells `i ≐ i`**, at the empty state. -/
def finFiring : Firing vecS.levels emptyState where
  helpers := .cons finZeroType (.nil _)
  taken := []
  read := []
  takes := []
  reads := []
  makes := []
  tells := finStore
  guards := []
  queries := []

def finNoRows : ∀ m ∈ finFiring.makes, Σ' B : TypeOver finFiring.helpers.frame, FrameTypedAt m.2 B :=
  fun _ member => absurd member List.not_mem_nil

/-- **Decided by the kernel**: the computable converting step admits it. -/
theorem fin_decided : vecAdmits? [vecFamily 16 4] 16 finFiring finNoRows = some true := by decide +kernel

/-- **Test 4 on the step**: the computable converting step admits a firing whose information has no
closed solution. -/
theorem admitted_not_closed :
    (convertingStep vecS.levels Nat (vecSettler 16 4)).Admits finFiring ∧
      ¬ ClosedSolvable (S := vecS) finFiring.information :=
  ⟨vecAdmits?_sound fin_decided, finStore_not_closed⟩

end Inhabitation

end ProgrammingOnTheStep.IndexedFamilies.AcceptanceOnTheRepairedStep

#print axioms ProgrammingOnTheStep.IndexedFamilies.AcceptanceOnTheRepairedStep.principalLaw_fails
#print axioms ProgrammingOnTheStep.IndexedFamilies.AcceptanceOnTheRepairedStep.principal_test_postponed
#print axioms ProgrammingOnTheStep.IndexedFamilies.AcceptanceOnTheRepairedStep.spawn_admitted
#print axioms ProgrammingOnTheStep.IndexedFamilies.AcceptanceOnTheRepairedStep.spawn_refused_beside
#print axioms ProgrammingOnTheStep.IndexedFamilies.AcceptanceOnTheRepairedStep.frameLaw_fails
#print axioms ProgrammingOnTheStep.IndexedFamilies.AcceptanceOnTheRepairedStep.frame_test_graded
#print axioms ProgrammingOnTheStep.IndexedFamilies.AcceptanceOnTheRepairedStep.same_zero_decided
#print axioms ProgrammingOnTheStep.IndexedFamilies.AcceptanceOnTheRepairedStep.same_one_decided
#print axioms ProgrammingOnTheStep.IndexedFamilies.AcceptanceOnTheRepairedStep.zero_one_decided
#print axioms ProgrammingOnTheStep.IndexedFamilies.AcceptanceOnTheRepairedStep.wave_pairs_admitted
#print axioms ProgrammingOnTheStep.IndexedFamilies.AcceptanceOnTheRepairedStep.triple_unsolvable
#print axioms ProgrammingOnTheStep.IndexedFamilies.AcceptanceOnTheRepairedStep.wave_triple_refused
#print axioms ProgrammingOnTheStep.IndexedFamilies.AcceptanceOnTheRepairedStep.frame_test_witness
#print axioms ProgrammingOnTheStep.IndexedFamilies.AcceptanceOnTheRepairedStep.waveLaw_fails
#print axioms ProgrammingOnTheStep.IndexedFamilies.AcceptanceOnTheRepairedStep.finStore_solvable
#print axioms ProgrammingOnTheStep.IndexedFamilies.AcceptanceOnTheRepairedStep.finStore_not_closed
#print axioms ProgrammingOnTheStep.IndexedFamilies.AcceptanceOnTheRepairedStep.inhabitationLaw_fails
#print axioms ProgrammingOnTheStep.IndexedFamilies.AcceptanceOnTheRepairedStep.fin_decided
#print axioms ProgrammingOnTheStep.IndexedFamilies.AcceptanceOnTheRepairedStep.admitted_not_closed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
