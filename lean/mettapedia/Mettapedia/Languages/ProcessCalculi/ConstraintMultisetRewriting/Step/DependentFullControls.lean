import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFull
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentClosedBoundaryControls

/-!
# The dependent full step in the cumulative tower: typing and query controls

**Told equations are heterogeneous** (`tell_heterogeneous`): a solution of a firing's information
makes each told equation's types equal and then its terms equal at the left type, as R76's
heterogeneous equations do (`ContextualDependentTwins.solves_iff`). A told equation between terms of
different types is neither aligned in advance nor refused by shape: it is refused only when no
solution can make both sides equal, as for the rigid clash `Ground ≐ U0` (`clash_refused`).

The frames below are `X : U0` (`base`) and `X : U0, x : X, g : Ground` (`triple`), and
`p : Ground` (`point`) for solutions.

**State typing controls.**
* `refined_admitted`, `refined_made_type`: a firing makes the helpers `x : X` and `g : Ground`,
  makes the row `x : X`, and tells the heterogeneous `(x : X) ≐ (g : Ground)`. It is admitted, and
  at every solution of its information the made row's type `X` is `Ground`, although the row's own
  type is the variable `X` (`refined_type_is_variable`).
* `illTyped_refused`: a make of `U0` at type `Ground` in the empty frame is refused: nothing closed
  has type `Ground`.
* `take_clash_refused`: a take whose pattern cannot unify with its row is refused.

**Predicate query controls.**
* `absence_refused_unknown`, `absence_refused_after_ground`, `absence_admitted_after_arrow`: the
  absence of `g : Ground` among the rows `{1 : x : X}` is refused under no knowledge and under the
  type-level `X ≐ Ground`, and admitted under the type-level `X ≐ Ground → Ground`. Its answer
  changes only through a type-level solution.
* `raw_not_reads`, `syntactic_collision`: the raw region "the row is literally `g : Ground`" does not
  read through solutions, so it is no predicate query of the step; under the heterogeneous knowledge
  `(x : X) ≐ (g : Ground)` the raw region sees no row, while the absence query is refused.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
namespace DependentFull.Controls

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentTwins

/-! ## Told equations are heterogeneous -/

section Heterogeneous

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head} (levels : LevelModel rules L)
  {O : Type} {s : State rules O}

/-- **A told equation is heterogeneous**: at a solution of the information, its types agree and its
terms are equal at the left type. -/
theorem tell_heterogeneous (f : Firing levels s) {Θ : Context rules} {τ : Θ ⟶ f.helpers.frame}
    (solved : (frames levels).Models τ f.information) {e : Equation (TotalTerm f.helpers.frame)}
    (told : e ∈ f.tells) :
    TypesAgree τ e ∧ Equal rules Θ.raw (subst τ.substitution e.1.2.code)
      (subst τ.substitution e.2.2.code) (subst τ.substitution e.1.1.code) :=
  (solves_iff levels τ e).mp (solved e (List.mem_append_right _ told))

/-- A firing with no helpers, takes, reads, makes or tells has the knowledge as its information. -/
theorem information_plain {Γ : Context rules} (K : EquationStore (TotalTerm Γ)) (present : Finset O)
    (label : O → TotalTerm Γ) (guards : EquationStore (TotalTerm Γ)) (queries : List (Query levels O Γ)) :
    (⟨.nil Γ, [], [], [], [], [], [], guards, queries⟩ :
      Firing levels (⟨Γ, K, present, label⟩ : State rules O)).information = K := by
  show (frames levels).applyStore (𝟙 Γ) K ++ ([] : EquationStore (TotalTerm Γ)) ++
    ([] : EquationStore (TotalTerm Γ)) ++ ([] : EquationStore (TotalTerm Γ)) = K
  simp only [List.append_nil]
  exact Frames.applyStore_id (X := frames levels) K

end Heterogeneous

/-! ## The package and its frames -/

abbrev setting := ContextualDependentWorklist.Controls.setting

theorem rigid : ∀ name, setting.roles name = .rigid := fun _ => rfl

def ground {n : Nat} : Tower.Tm n := .head .legacyGround

def arrow {n : Nat} : Tower.Tm n := .pi ground ground

theorem ground_typed {n : Nat} (Γ : Tower.Ctx n) :
    Typed Tower.rules Γ ground (.head (.sort Tower.zero)) :=
  .headType .legacyGround

theorem collapse : Tower.rules.cumulative (.sort (.max Tower.zero Tower.zero)) (.sort Tower.zero) := by
  change LevelTower.Cumulative (.sort (.max Tower.zero Tower.zero)) (.sort Tower.zero)
  intro valuation
  simp [LevelExpr.eval]

theorem arrow_typed {n : Nat} (Γ : Tower.Ctx n) :
    Typed Tower.rules Γ arrow (.head (.sort Tower.zero)) :=
  .cumul (.piForm (ground_typed Γ) (.sort _) (ground_typed _) (.sort _) (.sorts _ _)) collapse

/-- The small universe, as a formed type over any frame. -/
def smallUniverse (Γ : Context Tower.rules) : TypeOver Γ :=
  ⟨.head (.sort Tower.zero), .sort (.succ Tower.zero), .sort _, .headType (.sort _)⟩

/-- `Ground`, as a formed type over any frame. -/
def groundType (Γ : Context Tower.rules) : TypeOver Γ :=
  ⟨ground, .sort Tower.zero, .sort _, ground_typed _⟩

/-- The frame `X : U0`. -/
abbrev base : Context Tower.rules := extend (empty Tower.rules) (smallUniverse _)

/-- The type `X` over `X : U0`. -/
def xType : TypeOver base := ⟨.var 0, .sort Tower.zero, .sort _, Derivable.var 0⟩

/-- The frame `X : U0, x : X`. -/
abbrev pairFrame : Context Tower.rules := extend base xType

/-- The frame `X : U0, x : X, g : Ground`. -/
abbrev triple : Context Tower.rules := extend pairFrame (groundType _)

/-- The frame `p : Ground`, where solutions land. -/
abbrev point : Context Tower.rules := extend (empty Tower.rules) (groundType _)

/-- The row `x : X`. -/
def xRow : TotalTerm triple :=
  TotalTerm.reindex (⟨xType.reindex (projectionHom base xType), newest base xType⟩ : TotalTerm pairFrame)
    (projectionHom pairFrame (groundType _))

/-- The row `g : Ground`. -/
def gRow : TotalTerm triple :=
  ⟨(groundType pairFrame).reindex (projectionHom pairFrame (groundType _)), newest pairFrame (groundType _)⟩

/-- `X`, as a term of `U0`. -/
def xUniverse : TotalTerm triple := ⟨smallUniverse _, ⟨.var 2, Derivable.var 2⟩⟩

/-- `Ground`, as a term of `U0`. -/
def groundUniverse : TotalTerm triple := ⟨smallUniverse _, ⟨ground, ground_typed _⟩⟩

/-- `Ground → Ground`, as a term of `U0`. -/
def arrowUniverse : TotalTerm triple := ⟨smallUniverse _, ⟨arrow, arrow_typed _⟩⟩

/-- A substitution of `triple` by terms over `point`. -/
def into (bigX : Tower.Tm 1) (typedX : Typed Tower.rules point.raw bigX (.head (.sort Tower.zero)))
    (smallX : Tower.Tm 1) (typedx : Typed Tower.rules point.raw smallX bigX)
    (smallG : Tower.Tm 1) (typedg : Typed Tower.rules point.raw smallG ground) : point ⟶ triple :=
  pair (pair (pair (toEmpty point) ⟨bigX, typedX⟩) ⟨smallX, typedx⟩) ⟨smallG, typedg⟩

/-- `X ↦ Ground`, `x ↦ p`, `g ↦ p`. -/
def toGround : point ⟶ triple :=
  into ground (ground_typed _) (.var 0) (Derivable.var 0) (.var 0) (Derivable.var 0)

/-- `X ↦ Ground → Ground`, `x ↦ λy. y`, `g ↦ p`. -/
def toArrow : point ⟶ triple :=
  into arrow (arrow_typed _) (.lam (.var 0)) (.lamIntro (arrow_typed _) (.sort _) (Derivable.var 0))
    (.var 0) (Derivable.var 0)

/-- At `toGround`, the rows `x : X` and `g : Ground` are the same typed term. -/
theorem toGround_identifies : xRow.reindex toGround = gRow.reindex toGround :=
  totalTerm_ext (TypeOver.ext rfl rfl) rfl

theorem toGround_equates :
    (frames setting.levels).E ((frames setting.levels).act toGround gRow)
      ((frames setting.levels).act toGround xRow) := by
  show (frames setting.levels).E (gRow.reindex toGround) (xRow.reindex toGround)
  rw [toGround_identifies]
  exact ((frames setting.levels).equivalence _).refl _

/-! ## State typing: a made row whose type is refined by a solution -/

/-- The state `X : U0` with no knowledge and no rows. -/
def baseState : State Tower.rules Nat := ⟨base, [], ∅, fun _ => ⟨smallUniverse _, ⟨.var 0, Derivable.var 0⟩⟩⟩

/-- Make the helpers `x : X` and `g : Ground`, make the row `7 : x : X`, and tell
`(x : X) ≐ (g : Ground)`. -/
def refinedFiring : Firing setting.levels baseState where
  helpers := .cons xType (.cons (groundType _) (.nil _))
  taken := []
  read := []
  takes := []
  reads := []
  makes := [(7, Make.ofRow xRow)]
  tells := [(xRow, gRow)]
  guards := []
  queries := []

theorem refinedFiring_information : refinedFiring.information = [(xRow, gRow)] := rfl

/-- The told equation is heterogeneous: its types are `X` and `Ground`. -/
theorem refined_tell_heterogeneous : xRow.1.code ≠ gRow.1.code := by
  show (Tm.var 2 : Tower.Tm 3) ≠ .head .legacyGround
  exact fun same => by cases same

theorem refined_admitted : (step setting.levels Nat).Admits refinedFiring := by
  refine ⟨⟨List.nodup_nil, List.nodup_singleton _, rfl, rfl, fun m member => ?_⟩,
    (enabled_iff refinedFiring).mpr ⟨fun _ member => absurd member List.not_mem_nil,
      fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil,
      fun o _ inside => Finset.notMem_empty o inside⟩, ⟨point, toGround, ?_⟩, ?_⟩
  · obtain rfl := List.mem_singleton.mp member
    exact Make.ofRow_wellTyped _
  · rw [refinedFiring_information]
    intro e member
    obtain rfl := List.mem_singleton.mp member
    show (frames setting.levels).E (xRow.reindex toGround) (gRow.reindex toGround)
    rw [toGround_identifies]
    exact ((frames setting.levels).equivalence _).refl _
  · intro b τ _
    exact ⟨fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil⟩

theorem refined_label (admitted : (step setting.levels Nat).Admits refinedFiring) :
    ((step setting.levels Nat).result refinedFiring admitted).label 7 = xRow := rfl

/-- **The made row's type is refined by every solution**: it is `Ground` at every solution of the
information. -/
theorem refined_made_type (admitted : (step setting.levels Nat).Admits refinedFiring)
    {Θ : Context Tower.rules} (τ : Θ ⟶ refinedFiring.helpers.frame)
    (solved : (frames setting.levels).Models τ refinedFiring.information) :
    TypeEq Tower.rules Θ.raw
      (subst τ.substitution (((step setting.levels Nat).result refinedFiring admitted).label 7).1.code)
      ground := by
  rw [refined_label admitted]
  exact (tell_heterogeneous setting.levels refinedFiring solved (List.mem_singleton_self _)).1

/-- The made row's own type is the variable `X`, not `Ground`. -/
theorem refined_type_is_variable (admitted : (step setting.levels Nat).Admits refinedFiring) :
    (((step setting.levels Nat).result refinedFiring admitted).label 7).1.code ≠ ground := by
  rw [refined_label admitted]
  exact fun same => by cases same

/-! ## Refusals -/

/-- The empty frame with one row `0 : U0 : U1`. -/
def emptyState : State Tower.rules Nat :=
  ⟨empty Tower.rules, [], {0}, fun _ => ContextualDependentWorklist.Controls.universeCode⟩

/-- Make `U0` at the type `Ground`, in the empty frame. -/
def illTypedFiring : Firing setting.levels emptyState where
  helpers := .nil _
  taken := []
  read := []
  takes := []
  reads := []
  makes := [(1, ⟨groundType _, .head (.sort Tower.zero)⟩)]
  tells := []
  guards := []
  queries := []

/-- **An ill-typed make is refused**: nothing closed has type `Ground`. -/
theorem illTyped_refused : ¬ (step setting.levels Nat).Admits illTypedFiring := by
  rintro ⟨⟨-, -, -, -, typed⟩, -⟩
  exact ContextualDependentClosedBoundary.Controls.ground_uninhabited
    (typed _ (List.mem_singleton_self _))

/-- Tell the rigid clash `Ground ≐ U0`. -/
def clashFiring : Firing setting.levels emptyState where
  helpers := .nil _
  taken := []
  read := []
  takes := []
  reads := []
  makes := []
  tells := ContextualDependentWorklist.Controls.clash
  guards := []
  queries := []

/-- **A told equation whose types can never agree is refused**, by solvability. -/
theorem clash_refused : ¬ (step setting.levels Nat).Admits clashFiring :=
  fun admitted => ContextualDependentWorklist.Controls.clash_refuted admitted.2.2.1

/-- Take the row `0 : U0` with the pattern `Ground : U0`. -/
def takeClashFiring : Firing setting.levels emptyState where
  helpers := .nil _
  taken := [0]
  read := []
  takes := [ContextualDependentWorklist.Controls.groundCode]
  reads := []
  makes := []
  tells := []
  guards := []
  queries := []

/-- **A take that cannot unify with its row is refused**: the take constrains. -/
theorem take_clash_refused : ¬ (step setting.levels Nat).Admits takeClashFiring :=
  fun admitted => ContextualDependentWorklist.Controls.clash_refuted admitted.2.2.1

/-! ## An absence query answered by a type-level solution -/

/-- The frame `X : U0, x : X, g : Ground` with knowledge `K` and the row `1 : x : X`. -/
def queryState (K : EquationStore (TotalTerm triple)) : State Tower.rules Nat :=
  ⟨triple, K, {1}, fun _ => xRow⟩

/-- **Ask the absence of `g : Ground`** among the present rows, and nothing else. -/
def absenceFiring (K : EquationStore (TotalTerm triple)) : Firing setting.levels (queryState K) where
  helpers := .nil _
  taken := []
  read := []
  takes := []
  reads := []
  makes := []
  tells := []
  guards := []
  queries := [Query.absent setting.levels Nat gRow]

theorem absenceFiring_information (K : EquationStore (TotalTerm triple)) :
    (absenceFiring K).information = K :=
  information_plain setting.levels K {1} (fun _ => xRow) [] [Query.absent setting.levels Nat gRow]

theorem absenceFiring_row (K : EquationStore (TotalTerm triple)) (o : Nat) :
    (absenceFiring K).row o = xRow :=
  (frames setting.levels).act_id _

/-- Admission of the absence firing: solvable knowledge, and no row equated with `g : Ground` at
any solution. -/
theorem absence_admits_iff (K : EquationStore (TotalTerm triple)) :
    (step setting.levels Nat).Admits (absenceFiring K) ↔
      (frames setting.levels).Solvable K ∧
        (frames setting.levels).Entails K (fun _ τ =>
          ¬ (frames setting.levels).E ((frames setting.levels).act τ gRow) ((frames setting.levels).act τ xRow)) := by
  have info := absenceFiring_information K
  constructor
  · intro admitted
    obtain ⟨-, -, solvable, -, queries⟩ := (admits_iff (absenceFiring K)).mp admitted
    refine ⟨(congrArg (fun x => (frames setting.levels).Solvable x) info).mp solvable, fun b τ solved => ?_⟩
    have asked := (Query.absent_holds_iff _ _ _ τ).mp
      (queries _ (List.mem_singleton_self _) b τ
        ((congrArg (fun x => (frames setting.levels).Models τ x) info).mpr solved)) 1
      (Finset.mem_singleton_self 1)
    rwa [absenceFiring_row] at asked
  · rintro ⟨solvable, absent⟩
    refine (admits_iff (absenceFiring K)).mpr
      ⟨⟨List.nodup_nil, List.nodup_nil, rfl, rfl, fun _ member => absurd member List.not_mem_nil⟩,
      ⟨fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil,
        fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil⟩,
      (congrArg (fun x => (frames setting.levels).Solvable x) info).mpr solvable,
      fun _ _ _ _ member => absurd member List.not_mem_nil, ?_⟩
    intro q member b τ solved
    obtain rfl := List.mem_singleton.mp member
    refine (Query.absent_holds_iff _ _ _ τ).mpr fun o present => ?_
    rw [Finset.mem_singleton.mp present, absenceFiring_row]
    exact absent b τ ((congrArg (fun x => (frames setting.levels).Models τ x) info).mp solved)

/-- **Refused under no knowledge**: `X ↦ Ground`, `x, g ↦ p` equates the row with `g`. -/
theorem absence_refused_unknown : ¬ (step setting.levels Nat).Admits (absenceFiring []) := by
  intro admitted
  exact ((absence_admits_iff []).mp admitted).2 point toGround (Frames.models_nil _) toGround_equates

/-- **Refused under the type-level `X ≐ Ground`**, by the same solution. -/
theorem absence_refused_after_ground :
    ¬ (step setting.levels Nat).Admits (absenceFiring [(xUniverse, groundUniverse)]) := by
  intro admitted
  refine ((absence_admits_iff _).mp admitted).2 point toGround ?_ toGround_equates
  intro e member
  obtain rfl := List.mem_singleton.mp member
  show (frames setting.levels).E (xUniverse.reindex toGround) (groundUniverse.reindex toGround)
  rw [show xUniverse.reindex toGround = groundUniverse.reindex toGround from
    totalTerm_ext (TypeOver.ext rfl rfl) rfl]
  exact ((frames setting.levels).equivalence _).refl _

theorem ground_arrow_clash {n : Nat} {Γ : Tower.Ctx n} (formed : CtxFormed Tower.rules Γ) :
    ¬ TypeEq Tower.rules Γ ground arrow := by
  have clash : ContextualDependentRigid.shapeClashes setting.R (ground : Tower.Tm 0) arrow = true := by
    decide
  exact ContextualDependentRigid.not_typeEq_of_shapeClashes (S := setting) rigid TowerModel.facts
    TowerModel.complete formed (ContextualDependentRigid.shapeClashes_subst setting.R
      (fun i : Fin 0 => i.elim0) clash)

/-- **Admitted under the type-level `X ≐ Ground → Ground`**: no solution can equate a term of
type `X` with one of type `Ground`. -/
theorem absence_admitted_after_arrow :
    (step setting.levels Nat).Admits (absenceFiring [(xUniverse, arrowUniverse)]) := by
  refine (absence_admits_iff _).mpr ⟨⟨point, toArrow, ?_⟩, fun b τ solved equated => ?_⟩
  · intro e member
    obtain rfl := List.mem_singleton.mp member
    show (frames setting.levels).E (xUniverse.reindex toArrow) (arrowUniverse.reindex toArrow)
    rw [show xUniverse.reindex toArrow = arrowUniverse.reindex toArrow from
      totalTerm_ext (TypeOver.ext rfl rfl) rfl]
    exact ((frames setting.levels).equivalence _).refl _
  · have known := (solved _ (List.mem_singleton_self _)).2
    change Equal Tower.rules b.raw (subst τ.substitution (.var 2)) arrow (.head (.sort Tower.zero)) at known
    have typeX : TypeEq Tower.rules b.raw (subst τ.substitution (.var 2)) arrow :=
      ⟨.sort Tower.zero, .sort _, known⟩
    have rows := equated.1
    change TypeEq Tower.rules b.raw ground (subst τ.substitution (.var 2)) at rows
    exact ground_arrow_clash b.formed (rows.trans setting.levels typeX)

/-! ## The ordinary/reflection split: a syntactic collision -/

/-- The raw region "the row is literally `g : Ground`". -/
def rawRegion {Θ : Context Tower.rules} (_ : Θ ⟶ triple) (t : TotalTerm triple) : Prop := t = gRow

/-- **The raw region does not read through solutions**: `toGround` equates `x : X` with
`g : Ground`, and the raw region holds of one and not the other. It is a reflection query, not a
predicate query of the step. -/
theorem raw_not_reads :
    ¬ ∀ {Θ : Context Tower.rules} (τ : Θ ⟶ triple) {s t : TotalTerm triple},
      (frames setting.levels).E ((frames setting.levels).act τ s) ((frames setting.levels).act τ t) →
        (rawRegion τ s ↔ rawRegion τ t) := by
  intro reads
  have same := (reads toGround toGround_equates).mp rfl
  exact absurd (congrArg (fun t : TotalTerm triple => t.2.code) same) (by
    show ¬ ((.var 1 : Tower.Tm 3) = .var 0)
    exact fun h => by cases h)

/-- **The collision**: under the heterogeneous knowledge `(x : X) ≐ (g : Ground)`, the raw region
sees no present row, while the absence query, which reads through solutions, is refused. -/
theorem syntactic_collision :
    (∀ o ∈ (queryState [(xRow, gRow)]).present, ¬ rawRegion (𝟙 triple) ((queryState [(xRow, gRow)]).label o)) ∧
      ¬ (step setting.levels Nat).Admits (absenceFiring [(xRow, gRow)]) := by
  refine ⟨fun o _ same => ?_, fun admitted => ?_⟩
  · have codes := congrArg (fun t : TotalTerm triple => t.2.code) same
    exact absurd codes (by
      show ¬ ((.var 1 : Tower.Tm 3) = .var 0)
      exact fun h => by cases h)
  · refine ((absence_admits_iff _).mp admitted).2 point toGround ?_ toGround_equates
    intro e member
    obtain rfl := List.mem_singleton.mp member
    show (frames setting.levels).E (xRow.reindex toGround) (gRow.reindex toGround)
    rw [toGround_identifies]
    exact ((frames setting.levels).equivalence _).refl _

end DependentFull.Controls

#print axioms DependentFull.Controls.tell_heterogeneous
#print axioms DependentFull.Controls.refined_admitted
#print axioms DependentFull.Controls.refined_made_type
#print axioms DependentFull.Controls.refined_type_is_variable
#print axioms DependentFull.Controls.illTyped_refused
#print axioms DependentFull.Controls.clash_refused
#print axioms DependentFull.Controls.take_clash_refused
#print axioms DependentFull.Controls.absence_admits_iff
#print axioms DependentFull.Controls.absence_refused_unknown
#print axioms DependentFull.Controls.absence_refused_after_ground
#print axioms DependentFull.Controls.absence_admitted_after_arrow
#print axioms DependentFull.Controls.raw_not_reads
#print axioms DependentFull.Controls.syntactic_collision

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
