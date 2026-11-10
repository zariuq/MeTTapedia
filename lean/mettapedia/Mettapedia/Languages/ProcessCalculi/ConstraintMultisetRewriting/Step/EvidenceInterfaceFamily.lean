import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EvidenceInterface
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DisequalityFramesControls

/-!
# Four ways of not finding a row, at dependent frames

`Evidence.Family` separates four ways of not finding `p(a)` on the first-order step with
disequations. Here the same four members and four probes (`Evidence.Family.Member`, `Probe`) live on
the dependent full step with disequations (`DisequalityFrames.Dependent.withDisequations`), at the
frame `X : U0, x : X, g : Ground`:

* the sought row `p(a)` is the type `Ground`, the opposition `opp(a)` is `Ground → Ground` (row `1`),
  and the open row `p(X)` is the variable `X` (row `2`);
* the probes ask the absence of `Ground`, read row `1` as `Ground → Ground`, tell `X ≐ Ground`, and
  read row `2` as `Ground`.

| member | state | absence of `Ground` | read `Ground → Ground` | tell `X ≐ Ground` | read `Ground` |
|---|---|---|---|---|---|
| covered absence | no rows | admitted | refused | admitted | refused |
| refutation row | row `Ground → Ground` | admitted | admitted | admitted | refused |
| incomplete search | row `X`, `X` open | refused | refused | admitted | admitted |
| disequality | row `X`, `X ≠ Ground` | admitted | refused | refused | refused |

`table` proves the sixteen verdicts, the same as the first-order ones, and `profiles_distinct` that no
two members agree on the four probes. At the refutation member the absence holds because no solution
equates `Ground` with `Ground → Ground` (a rigid clash); at the disequality member, because every
admitted solution keeps `X` apart from `Ground`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.EvidenceInterface.DependentFamily

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface.DependentFull
open Interface.DependentFull.Controls
open Interface.DependentFull.IndependenceControls
open Interface (Frames)
open DisequalityFrames (Separates separates_id_iff)
open Evidence.Family (Member Probe)

abbrev X := ContextualDependentEta.frames setting.levels
abbrev Q := (DisequalityFrames.Dependent.prestep setting.levels Nat).step
abbrev P := DisequalityFrames.Dependent.withDisequations setting.levels Nat

/-! ## Facts of the frame -/

/-- **No solution equates `Ground` with `Ground → Ground`.** -/
theorem ground_ne_arrow {Θ : Context Tower.rules} (τ : Θ ⟶ triple) :
    ¬ X.E (X.act τ groundUniverse) (X.act τ arrowUniverse) := fun equated =>
  ground_arrow_clash Θ.formed (typeEq_of_equal τ rfl equated)

/-- `X ↦ Ground → Ground` keeps `X` apart from `Ground`. -/
theorem toArrow_apart : ¬ X.E (X.act toArrow xUniverse) (X.act toArrow groundUniverse) := fun equated =>
  ground_apart toArrow toArrow_solves ((X.equivalence point).symm equated)

theorem act_id_eq {Δ : Context Tower.rules} (t : TotalTerm Δ) : X.act (𝟙 Δ) t = t := X.act_id t

/-! ## Rows, members and probes -/

/-- Row `1` is `Ground → Ground`; every other row is `X`. -/
def rowLabel : Nat → TotalTerm triple
  | 1 => arrowUniverse
  | _ => xUniverse

/-- A state at the frame with the given rows and no knowledge. -/
def rowsAt (present : Finset Nat) : State Tower.rules Nat := ⟨triple, [], present, rowLabel⟩

/-- The disequation `X ≠ Ground`. -/
def apartG : Equation (TotalTerm triple) := (xUniverse, groundUniverse)

theorem apartG_separated : Separates X (X.id triple) [apartG] :=
  (separates_id_iff _).mpr ⟨point, toArrow, fun d member => by
    obtain rfl := List.mem_singleton.mp member
    exact toArrow_apart⟩

/-- The state of each member. -/
def state : Member → Q.DState
  | .covered => Q.plain (rowsAt ∅)
  | .refuted => Q.plain (rowsAt {1})
  | .incomplete => Q.plain (rowsAt {2})
  | .disequal => ⟨rowsAt {2}, [apartG], apartG_separated⟩

/-- The firing of each probe, without helpers. -/
def plainProbe : Probe → Plain setting.levels Nat triple
  | .absentP => ⟨[], [], [], [], [], [], [], [Query.absent setting.levels Nat groundUniverse]⟩
  | .readOpp => ⟨[], [1], [], [arrowUniverse], [], [], [], []⟩
  | .bindA => ⟨[], [], [], [], [], [(xUniverse, groundUniverse)], [], []⟩
  | .findP => ⟨[], [2], [], [groundUniverse], [], [], [], []⟩

/-- A probe at a member, telling no disequation. -/
def probe : (m : Member) → Probe → Q.DFiring (state m)
  | .covered, π => Interface.Step.DFiring.silent _ (Plain.toFiring (s := rowsAt ∅) (plainProbe π))
      (DisequalityFrames.Dependent.toFiring_reflects _)
  | .refuted, π => Interface.Step.DFiring.silent _ (Plain.toFiring (s := rowsAt {1}) (plainProbe π))
      (DisequalityFrames.Dependent.toFiring_reflects _)
  | .incomplete, π => Interface.Step.DFiring.silent _ (Plain.toFiring (s := rowsAt {2}) (plainProbe π))
      (DisequalityFrames.Dependent.toFiring_reflects _)
  | .disequal, π => Interface.Step.DFiring.silent _ (Plain.toFiring (s := rowsAt {2}) (plainProbe π))
      (DisequalityFrames.Dependent.toFiring_reflects _)

/-- **The outcome of a member**: which probes its state admits. -/
def profile (m : Member) (π : Probe) : Prop := P.Admits (probe m π)

/-! ## The equation-only members, at the firings without helpers -/

/-- At an equation-only member, a probe is admitted exactly when its firing without helpers is. -/
theorem plain_profile_iff (present : Finset Nat) (π : Probe) :
    P.Admits (Interface.Step.DFiring.silent (Q.plain (rowsAt present))
        (Plain.toFiring (s := rowsAt present) (plainProbe π)) (DisequalityFrames.Dependent.toFiring_reflects _)) ↔
      (plainProbe π).Admits (rowsAt present).toLocal :=
  (Interface.Step.conservative _ _ rfl rfl).trans (Plain.admits_toFiring _)

theorem shapes (π : Probe) : (plainProbe π).Shapes := by
  cases π <;> exact ⟨List.nodup_nil, List.nodup_nil, rfl, rfl, fun _ member => absurd member List.not_mem_nil⟩

theorem enabled (present : Finset Nat) (π : Probe) (reads : ∀ o ∈ (plainProbe π).read, o ∈ present) :
    MeTTaCalculus.OccurrenceCommits.Enabled (fun _ : Nat => ()) (rowsAt present).toLocal.present
      ((plainProbe π).selection.commit (T := Unit)) := by
  refine (Plain.enabled_iff _ _).mpr ⟨fun _ member => ?_, reads, fun _ member => ?_, fun _ member => ?_⟩ <;>
    cases π <;> exact absurd member List.not_mem_nil

theorem refused_missing (present : Finset Nat) (π : Probe) {o : Nat} (inside : o ∈ (plainProbe π).read)
    (missing : o ∉ present) : ¬ (plainProbe π).Admits (rowsAt present).toLocal := fun admitted =>
  missing (((Plain.enabled_iff _ _).mp admitted.2.1).2.1 o inside)

theorem no_reads (π : Probe) (none : (plainProbe π).read = []) (present : Finset Nat) :
    ∀ o ∈ (plainProbe π).read, o ∈ present := fun _ member => absurd (none ▸ member) List.not_mem_nil

theorem holds_plain (present : Finset Nat) (π : Probe) (noQueries : (plainProbe π).queries = [])
    {Θ : Context Tower.rules} (τ : Θ ⟶ triple) : (plainProbe π).Holds (rowsAt present).toLocal τ := by
  refine ⟨?_, fun q member => absurd (noQueries ▸ member) List.not_mem_nil⟩
  cases π <;> exact Frames.models_nil _

/-- Telling `X ≐ Ground` is admitted at every equation-only member. -/
theorem bindA_plain (present : Finset Nat) : (plainProbe .bindA).Admits (rowsAt present).toLocal :=
  ⟨shapes .bindA, enabled present .bindA (no_reads .bindA rfl present),
    ⟨point, toGround, fun e member => by
      obtain rfl := List.mem_singleton.mp member
      exact toGround_solves⟩,
    fun _ τ _ => holds_plain present .bindA rfl τ⟩

/-- The absence of `Ground` holds at a member whose rows are never `Ground`. -/
theorem absentP_plain (present : Finset Nat)
    (apart : ∀ {Θ : Context Tower.rules} (τ : Θ ⟶ triple), ∀ o ∈ present,
      ¬ X.E (X.act τ groundUniverse) (X.act τ (rowLabel o))) :
    (plainProbe .absentP).Admits (rowsAt present).toLocal := by
  refine ⟨shapes .absentP, enabled present .absentP (no_reads .absentP rfl present),
    ⟨triple, 𝟙 triple, fun e member => absurd member List.not_mem_nil⟩, fun _ τ _ => ⟨Frames.models_nil _, ?_⟩⟩
  intro q member
  obtain rfl := List.mem_singleton.mp member
  exact (Query.absent_holds_iff _ _ _ τ).mpr fun o inside => apart τ o inside

/-- **The covered member.** -/
theorem covered_profile :
    profile .covered .absentP ∧ ¬ profile .covered .readOpp ∧ profile .covered .bindA ∧
      ¬ profile .covered .findP :=
  ⟨(plain_profile_iff ∅ .absentP).mpr (absentP_plain ∅ fun _ o inside => absurd inside (Finset.notMem_empty o)),
    fun admitted => refused_missing ∅ .readOpp (List.mem_singleton_self 1) (Finset.notMem_empty 1)
      ((plain_profile_iff ∅ .readOpp).mp admitted),
    (plain_profile_iff ∅ .bindA).mpr (bindA_plain ∅),
    fun admitted => refused_missing ∅ .findP (List.mem_singleton_self 2) (Finset.notMem_empty 2)
      ((plain_profile_iff ∅ .findP).mp admitted)⟩

/-- **The refutation member.** -/
theorem refuted_profile :
    profile .refuted .absentP ∧ profile .refuted .readOpp ∧ profile .refuted .bindA ∧
      ¬ profile .refuted .findP := by
  refine ⟨(plain_profile_iff {1} .absentP).mpr (absentP_plain {1} fun τ o inside => ?_),
    (plain_profile_iff {1} .readOpp).mpr ⟨shapes .readOpp, enabled {1} .readOpp fun o member => ?_,
      solvable_refl _ fun e member => ?_, fun _ τ _ => holds_plain {1} .readOpp rfl τ⟩,
    (plain_profile_iff {1} .bindA).mpr (bindA_plain {1}),
    fun admitted => refused_missing {1} .findP (List.mem_singleton_self 2) (by decide)
      ((plain_profile_iff {1} .findP).mp admitted)⟩
  · obtain rfl := Finset.mem_singleton.mp inside
    exact ground_ne_arrow τ
  · obtain rfl := List.mem_singleton.mp member
    exact Finset.mem_singleton_self 1
  · obtain rfl := List.mem_singleton.mp member
    rfl

/-- **The incomplete member.** -/
theorem incomplete_profile :
    ¬ profile .incomplete .absentP ∧ ¬ profile .incomplete .readOpp ∧ profile .incomplete .bindA ∧
      profile .incomplete .findP := by
  refine ⟨fun admitted => ?_,
    fun admitted => refused_missing {2} .readOpp (List.mem_singleton_self 1) (by decide)
      ((plain_profile_iff {2} .readOpp).mp admitted),
    (plain_profile_iff {2} .bindA).mpr (bindA_plain {2}),
    (plain_profile_iff {2} .findP).mpr ⟨shapes .findP, enabled {2} .findP fun o member => ?_,
      ⟨point, toGround, fun e member => ?_⟩, fun _ τ _ => holds_plain {2} .findP rfl τ⟩⟩
  · have asked := ((plain_profile_iff {2} .absentP).mp admitted).2.2.2 point toGround
      (fun e member => absurd member List.not_mem_nil)
    have absent := (Query.absent_holds_iff _ _ _ toGround).mp (asked.2 _ (List.mem_singleton_self _)) 2
      (Finset.mem_singleton_self 2)
    exact absent ((X.equivalence point).symm toGround_solves)
  · obtain rfl := List.mem_singleton.mp member
    exact Finset.mem_singleton_self 2
  · obtain rfl := List.mem_singleton.mp member
    exact (X.equivalence point).symm toGround_solves

/-! ## The disequality member -/

theorem disequal_absentP : profile .disequal .absentP := by
  refine (Interface.Step.admits_iff_separating _ (probe .disequal .absentP)).mpr
    ⟨shapes .absentP, enabled {2} .absentP (no_reads .absentP rfl {2}),
      ⟨point, toArrow, fun e member => absurd member List.not_mem_nil, ?_⟩, ?_⟩
  · intro d member equated
    rcases List.mem_append.mp member with carried | none
    · obtain rfl := List.mem_singleton.mp carried
      exact toArrow_apart ((congrArg₂ X.E (congrArg (X.act toArrow) (act_id_eq xUniverse))
        (congrArg (X.act toArrow) (act_id_eq groundUniverse))).mp equated)
    · exact absurd none List.not_mem_nil
  · intro b g _ separated
    refine ⟨Frames.models_nil _, fun q member => ?_⟩
    obtain rfl := List.mem_singleton.mp member
    refine (Query.absent_holds_iff _ _ _ g).mpr fun o inside equated => ?_
    obtain rfl := Finset.mem_singleton.mp inside
    apply separated _ (List.mem_append_left _ (List.mem_singleton_self _))
    exact (congrArg (X.E (X.act g (X.act (𝟙 triple) xUniverse)))
      (congrArg (X.act g) (act_id_eq groundUniverse))).mpr ((X.equivalence b).symm equated)

theorem disequal_readOpp : ¬ profile .disequal .readOpp := by
  intro admitted
  obtain ⟨-, enabledHere, -, -⟩ := (Interface.Step.admits_iff_separating _ (probe .disequal .readOpp)).mp admitted
  have read := ((enabled_iff _).mp enabledHere).2.1 1 (List.mem_singleton_self 1)
  exact absurd read (by decide)

theorem read_apart_eq {b : Context Tower.rules} (g : b ⟶ triple) (t : TotalTerm triple) :
    X.act (X.comp g (𝟙 triple)) t = X.act g t :=
  (X.act_comp g (𝟙 triple) t).trans (congrArg (X.act g) (act_id_eq t))

/-- The two sides of `X ≠ Ground`, read along a firing without helpers, at a solution. -/
theorem read_apart {b : Context Tower.rules} (g : b ⟶ triple) :
    X.E (X.act (X.comp g (𝟙 triple)) xUniverse) (X.act (X.comp g (𝟙 triple)) groundUniverse) ↔
      X.E (X.act g xUniverse) (X.act g groundUniverse) :=
  (congrArg₂ X.E (read_apart_eq g xUniverse) (read_apart_eq g groundUniverse)).to_iff

theorem disequal_bindA : ¬ profile .disequal .bindA := by
  refine Interface.Step.refused_of_carried _ (probe .disequal .bindA) (d := apartG) (List.mem_singleton_self _) ?_
  intro b g solved
  exact (read_apart g).mpr (solved _ (List.mem_append_right _ (List.mem_singleton_self _)))

theorem disequal_findP : ¬ profile .disequal .findP := by
  refine Interface.Step.refused_of_carried _ (probe .disequal .findP) (d := apartG) (List.mem_singleton_self _) ?_
  intro b g solved
  have read : X.E (X.act g groundUniverse) (X.act g (X.act (𝟙 triple) xUniverse)) :=
    solved _ (Firing.read_mem (Plain.toFiring (s := rowsAt {2}) (plainProbe .findP)) (List.mem_singleton_self _))
  have read' : X.E (X.act g groundUniverse) (X.act g xUniverse) :=
    (congrArg (X.E (X.act g groundUniverse)) (congrArg (X.act g) (act_id_eq xUniverse))).mp read
  exact (read_apart g).mpr ((X.equivalence b).symm read')

/-! ## The table -/

/-- **The sixteen verdicts**, the same as at the first-order step. -/
theorem table :
    (profile .covered .absentP ∧ ¬ profile .covered .readOpp ∧ profile .covered .bindA ∧
      ¬ profile .covered .findP) ∧
    (profile .refuted .absentP ∧ profile .refuted .readOpp ∧ profile .refuted .bindA ∧
      ¬ profile .refuted .findP) ∧
    (¬ profile .incomplete .absentP ∧ ¬ profile .incomplete .readOpp ∧
      profile .incomplete .bindA ∧ profile .incomplete .findP) ∧
    (profile .disequal .absentP ∧ ¬ profile .disequal .readOpp ∧ ¬ profile .disequal .bindA ∧
      ¬ profile .disequal .findP) :=
  ⟨covered_profile, refuted_profile, incomplete_profile,
    ⟨disequal_absentP, disequal_readOpp, disequal_bindA, disequal_findP⟩⟩

/-- **No two members coincide** at dependent frames. -/
theorem profiles_distinct (m₁ m₂ : Member) (different : m₁ ≠ m₂) : profile m₁ ≠ profile m₂ := by
  obtain ⟨⟨c1, c2, c3, c4⟩, ⟨r1, r2, r3, r4⟩, ⟨i1, i2, i3, i4⟩, ⟨d1, d2, d3, d4⟩⟩ := table
  intro same
  have at_ : ∀ π, profile m₁ π ↔ profile m₂ π := fun π => by rw [same]
  cases m₁ <;> cases m₂
  all_goals first
    | exact different rfl
    | exact c2 ((at_ .readOpp).mpr r2)
    | exact i1 ((at_ .absentP).mp c1)
    | exact d3 ((at_ .bindA).mp c3)
    | exact c2 ((at_ .readOpp).mp r2)
    | exact i1 ((at_ .absentP).mp r1)
    | exact d3 ((at_ .bindA).mp r3)
    | exact i1 ((at_ .absentP).mpr c1)
    | exact i1 ((at_ .absentP).mpr r1)
    | exact i1 ((at_ .absentP).mpr d1)
    | exact d3 ((at_ .bindA).mpr c3)
    | exact d3 ((at_ .bindA).mpr r3)
    | exact i1 ((at_ .absentP).mp d1)

#print axioms ground_ne_arrow
#print axioms covered_profile
#print axioms refuted_profile
#print axioms incomplete_profile
#print axioms disequal_absentP
#print axioms disequal_bindA
#print axioms disequal_findP
#print axioms table
#print axioms profiles_distinct

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.EvidenceInterface.DependentFamily
