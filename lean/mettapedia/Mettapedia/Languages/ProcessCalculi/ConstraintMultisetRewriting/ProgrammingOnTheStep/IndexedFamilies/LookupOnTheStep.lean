import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgrammingOnTheStep.IndexedFamilies.AppendOnTheStep
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerVectorsLookup

/-!
# Lookup by a finite index on the dependent step, and the frame with no index

In the package with vectors, finite types and their eliminators (`TowerVectorsModel.rules`):

* **Lookup at the first index, as a firing** (`lookup_admitted`). The frame holds the equation's
  variables `A : U0, k : num, a : A, w : vec A k`, all open; the call row is
  `lookup A (succ k) (pair a w) fz : A`. The firing takes the call, makes the row `a : A`, and tells
  that the call equals it. It is admitted at the identity solution: the call computes to `a` in
  conversion (`call_meets_answer`).

* **The empty vector has no index** (`no_index_of_empty`): the frame `i : fin zero` has no closed
  point, so no closed call of lookup on the empty vector exists. Its positive twin: the frame
  `i : fin (succ zero)` has the closed point `fz` (`index_of_singleton`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ProgrammingOnTheStep.IndexedFamilies

open _root_.CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface.DependentFull

namespace Lookup

open TowerVectorsModel TowerVectorsLookup
open TowerNumbersModel (u)
open Eliminator (level1 pkg pkgLevels D u0Type numType ctxA ctxK)

/-! ## Lookup at the first index -/

/-- `a : A`, over `A : U0, k : num`. -/
def aType : TypeOver ctxK := ⟨.var 1, u, LevelTower.IsUniverse.sort _, Derivable.var (1 : Fin 2)⟩

abbrev ctxa : Context pkg := extend ctxK aType

/-- `w : vec A k`. -/
def wType : TypeOver ctxa :=
  ⟨vecC (.var 2) (.var 1), u, LevelTower.IsUniverse.sort _,
    D.vec_typed (Derivable.var (2 : Fin 3)) (Derivable.var (1 : Fin 3))⟩

/-- **The frame of the equation**: `A : U0, k : num, a : A, w : vec A k`, every variable open. -/
abbrev frame : Context pkg := extend ctxa wType

/-- The element type `A`, over the frame. -/
def elementType : TypeOver frame := ⟨.var 3, u, LevelTower.IsUniverse.sort _, Derivable.var (3 : Fin 4)⟩

/-- The call `lookup A (succ k) (pair a w) fz`. -/
abbrev callCode : Tower.Tm 4 := lookupTm (.var 3) (succC (.var 2)) (.pair (.var 1) (.var 0)) fzC

theorem call_typed : Typed pkg frame.raw callCode (.var 3) :=
  (Equal.typed (S := setting level1 fun _ => 0) (lookup_fz level1) (fzCtx_formed level1)).1

/-- **The call** `lookup A (succ k) (pair a w) fz : A`. -/
def callRow : TotalTerm frame := ⟨elementType, ⟨callCode, call_typed⟩⟩

/-- **Its answer** `a : A`. -/
def answerRow : TotalTerm frame := ⟨elementType, ⟨.var 1, Derivable.var (1 : Fin 4)⟩⟩

def callState : State pkg Nat := ⟨frame, [], {0}, fun _ => callRow⟩

/-- **The equation `lookup (succ k) (pair a w) fz = a`, firing on the call**: it takes the call,
makes the answer, and tells that the call equals it. -/
def lookupFiring : Firing pkgLevels callState where
  helpers := .nil _
  taken := [0]
  read := []
  takes := [callRow]
  reads := []
  makes := [(1, ⟨elementType, (.var 1 : Tower.Tm 4)⟩)]
  tells := [(callRow, answerRow)]
  guards := []
  queries := []

theorem lookupFiring_information :
    lookupFiring.information = [(callRow, lookupFiring.row 0), (callRow, answerRow)] := rfl

theorem take_identifies :
    callRow.reindex (𝟙 frame) = (lookupFiring.row 0).reindex (𝟙 frame) :=
  totalTerm_ext (TypeOver.ext rfl rfl) rfl

theorem call_reindex : callRow.reindex (𝟙 frame) = callRow := reindex_id _

theorem answer_reindex : answerRow.reindex (𝟙 frame) = answerRow := reindex_id _

/-- **The call equals its answer, in the knowledge**: the eliminator computes in conversion. -/
theorem call_meets_answer : (frames pkgLevels).E callRow answerRow :=
  (equivalent_iff pkgLevels _ _).mpr
    ⟨⟨u, LevelTower.IsUniverse.sort _, .refl (Derivable.var (3 : Fin 4))⟩, lookup_fz level1⟩

/-- **The lookup firing is admitted**, at the identity solution. -/
theorem lookup_admitted : (step pkgLevels Nat).Admits lookupFiring := by
  refine ⟨⟨List.nodup_singleton _, List.nodup_singleton _, rfl, rfl, fun m member => ?_⟩,
    (enabled_iff lookupFiring).mpr ⟨fun o member => ?_, fun _ member => absurd member List.not_mem_nil,
      fun _ _ readToo => absurd readToo List.not_mem_nil, fun o member inside => ?_⟩,
    ⟨frame, 𝟙 _, ?_⟩, ?_⟩
  · obtain rfl := List.mem_singleton.mp member
    exact Derivable.var (1 : Fin 4)
  · obtain rfl := List.mem_singleton.mp member
    exact Finset.mem_singleton_self 0
  · obtain rfl := List.mem_singleton.mp member
    exact absurd (Finset.mem_singleton.mp inside) (by decide)
  · rw [lookupFiring_information]
    intro e member
    rcases List.mem_cons.mp member with rfl | member
    · show (frames pkgLevels).E (callRow.reindex (𝟙 frame)) ((lookupFiring.row 0).reindex (𝟙 frame))
      rw [take_identifies]
      exact ((frames pkgLevels).equivalence _).refl _
    · obtain rfl := List.mem_singleton.mp member
      show (frames pkgLevels).E (callRow.reindex (𝟙 frame)) (answerRow.reindex (𝟙 frame))
      rw [call_reindex, answer_reindex]
      exact call_meets_answer
  · intro b τ _
    exact ⟨fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil⟩

/-- The made row is the answer `a`. -/
theorem lookup_result_row :
    (((step pkgLevels Nat).result lookupFiring lookup_admitted).label 1).2.code = (.var 1 : Tower.Tm 4) :=
  rfl

/-! ## The frame with no index -/

/-- `fin zero`, over the empty frame. -/
def finZero : TypeOver (empty pkg) :=
  ⟨finC zeroC, u, LevelTower.IsUniverse.sort _, fin_typed level1 D.zero_typed⟩

/-- The frame `i : fin zero`: an index of the empty vector. -/
abbrev emptyIndexFrame : Context pkg := extend (empty pkg) finZero

/-- **The empty vector has no index**: no closed substitution reaches the frame `i : fin zero`. -/
theorem no_index_of_empty : ¬ Nonempty (empty pkg ⟶ emptyIndexFrame) :=
  fun ⟨σ⟩ => fin_zero_empty level1 (σ.typed (0 : Fin 1))

/-- `fin (succ zero)`, over the empty frame. -/
def finOne : TypeOver (empty pkg) :=
  ⟨finC (succC zeroC), u, LevelTower.IsUniverse.sort _, fin_typed level1 (D.succ_typed D.zero_typed)⟩

/-- The frame `i : fin (succ zero)`. -/
abbrev singletonIndexFrame : Context pkg := extend (empty pkg) finOne

/-- **Positive control: a vector of one element has an index**, the closed point `fz`. -/
theorem index_of_singleton : Nonempty (empty pkg ⟶ singletonIndexFrame) :=
  ⟨pair (toEmpty (empty pkg)) ⟨fzC, fin_one_inhabited level1⟩⟩

end Lookup

end ProgrammingOnTheStep.IndexedFamilies

#print axioms ProgrammingOnTheStep.IndexedFamilies.Lookup.call_meets_answer
#print axioms ProgrammingOnTheStep.IndexedFamilies.Lookup.lookup_admitted
#print axioms ProgrammingOnTheStep.IndexedFamilies.Lookup.lookup_result_row
#print axioms ProgrammingOnTheStep.IndexedFamilies.Lookup.no_index_of_empty
#print axioms ProgrammingOnTheStep.IndexedFamilies.Lookup.index_of_singleton

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
