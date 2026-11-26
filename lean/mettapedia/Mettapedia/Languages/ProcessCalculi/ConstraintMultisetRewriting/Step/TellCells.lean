import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CellsFirstOrder
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DispatchControls

/-!
# Frame changes of tell cells

A nonempty round of pure tells is a cell exactly when the union of its
equations with the entry store has a model. A frame map that carries models
therefore preserves these cells. Reflection concerns the full joint store:
individual and pairwise licensing cannot guarantee reflection of a cube.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.TellCells

open AnnotatedRuns (Firing firstOrder firstOrderTransport Executable)
open Interface (Frames Transport)
open Interface.Translation (FrameMap)
open MeTTaCalculus.OccurrenceCommits (fire)

variable {T S O : Type*} [DecidableEq O]
variable (A : SubstitutionAction T S) (label : O → T)

def tell (equations : EquationStore T) : Firing T S O :=
  ⟨⟨[], [], equations, [], []⟩, [], ⟨[], [], []⟩⟩

@[simp] theorem tell_result (C : Configuration T O) (equations : EquationStore T) :
    (tell (S := S) equations).result label C = ⟨C.equations ++ equations, C.present⟩ := by
  simp [tell, Firing.result, Selection.result, Selection.problem, Selection.equations,
    Selection.commit, fire]

private theorem tell_permitted (C : Configuration T O) (equations : EquationStore T)
    (model : A.Consistent (C.equations ++ equations)) :
    (firstOrder A label).Admits (s := C) (tell equations) := by
  apply ((firstOrder A label).admits_iff (tell equations)).mpr
  refine ⟨⟨by simp [tell], by simp [tell], rfl, rfl, rfl⟩, ?_, ?_, ?_⟩
  · constructor <;> simp [firstOrder, tell, Selection.commit]
  · simpa [firstOrder, tell, Selection.problem, Selection.equations] using
      (Frames.ofSubstitution_solvable_iff A (C.equations ++ equations)).mpr model
  · intro b assignment solved
    simp [firstOrder, tell]

private theorem executable_model (C : Configuration T O) (round : List (EquationStore T))
    (run : Executable A label C (round.map tell)) :
    A.Consistent (C.equations ++ round.flatten) := by
  induction round generalizing C with
  | nil => simpa [Executable] using run
  | cons equations later ih =>
      have after := ih _ run.2
      simpa [tell_result, List.append_assoc] using after

private theorem cell_of_model (C : Configuration T O) (round : List (EquationStore T))
    (model : A.Consistent (C.equations ++ round.flatten)) :
    (firstOrderTransport A label).Cell C (round.map tell) := by
  obtain ⟨assignment, solved⟩ := model
  have entailed (i : Fin round.length) : A.Consistent (C.equations ++ round[i]) := by
    refine ⟨assignment, fun equation inside => solved equation ?_⟩
    rcases List.mem_append.mp inside with original | issued
    · exact List.mem_append_left _ original
    · exact List.mem_append_right _ (List.mem_flatten.mpr
        ⟨round[i], List.getElem_mem i.isLt, issued⟩)
  have admits : ∀ i : Fin (round.map (tell (T := T) (S := S) (O := O))).length,
      (firstOrder A label).Admits (s := C) (round.map tell)[i] := by
    intro i
    let source : Fin round.length := ⟨i, by simpa only [List.length_map] using i.isLt⟩
    have picked : (round.map (tell (T := T) (S := S) (O := O)))[i] = tell round[source] :=
      List.getElem_map _
    exact picked ▸ tell_permitted A label C round[source] (entailed source)
  refine .intro _ admits fun i => ?_
  let source : Fin round.length := ⟨i, by simpa only [List.length_map] using i.isLt⟩
  let after : Configuration T O := ⟨C.equations ++ round[source], C.present⟩
  have afterEq : (firstOrder A label).result (round.map tell)[i] (admits i) = after := by
    change (round.map tell)[i].result label C = after
    have picked : (round.map (tell (T := T) (S := S) (O := O)))[i] = tell round[source] :=
      List.getElem_map _
    rw [picked, tell_result]
  have faceEq : (((round.map (tell (T := T) (S := S) (O := O))).eraseIdx i).map
      ((firstOrderTransport A label).residual (round.map tell)[i] (admits i))) =
      (round.eraseIdx source).map tell := by
    change (((round.map tell).eraseIdx i).map id) = (round.eraseIdx source).map tell
    rw [List.map_id, List.eraseIdx_map]
  rw [afterEq, faceEq]
  apply cell_of_model after (round.eraseIdx source)
  refine ⟨assignment, fun equation inside => solved equation ?_⟩
  rcases List.mem_append.mp inside with earlier | remaining
  · rcases List.mem_append.mp earlier with entry | issued
    · exact List.mem_append_left _ entry
    · exact List.mem_append_right _ (List.mem_flatten.mpr
        ⟨round[source], List.getElem_mem source.isLt, issued⟩)
  · obtain ⟨part, partIn, issued⟩ := List.mem_flatten.mp remaining
    exact List.mem_append_right _ (List.mem_flatten.mpr
      ⟨part, List.eraseIdx_subset partIn, issued⟩)
termination_by round.length
decreasing_by
  have inside : (i : ℕ) < round.length := source.isLt
  rw [List.length_eraseIdx_of_lt inside]
  exact Nat.sub_lt (Nat.zero_lt_of_lt inside) (by decide)

theorem cell_iff_model (C : Configuration T O) (round : List (EquationStore T))
    (nonempty : round ≠ []) :
    (firstOrderTransport A label).Cell C (round.map tell) ↔
      A.Consistent (C.equations ++ round.flatten) := by
  refine ⟨fun cell => executable_model A label C round
    (AnnotatedRuns.jointly_executable A label cell.jointly (fun empty => nonempty (List.map_eq_nil_iff.mp empty))),
    cell_of_model A label C round⟩

section Map

variable {U R : Type*} (B : SubstitutionAction U R) (targetLabel : O → U)
  (map : FrameMap (Frames.ofSubstitution A) (Frames.ofSubstitution B))

private theorem store_flatten (round : List (EquationStore T)) :
    map.store (a := PUnit.unit) round.flatten =
      (round.map (map.store (a := PUnit.unit))).flatten := by
  induction round with
  | nil => rfl
  | cons first later ih =>
      simp only [List.flatten_cons, List.map_cons, FrameMap.store, List.map_append] at ih ⊢
      rw [ih]

/-- An action-preserving frame change carries every tell cell to a cell of
the same arity. The cube test is one joint model, even when every individual
and pairwise test accepts. -/
theorem map_cell (C : Configuration T O) (round : List (EquationStore T))
    (cell : (firstOrderTransport A label).Cell C (round.map tell)) :
    (firstOrderTransport B targetLabel).Cell ⟨map.store (a := PUnit.unit) C.equations, C.present⟩
      (round.map fun equations => tell (map.store (a := PUnit.unit) equations)) := by
  by_cases empty : round = []
  · subst round
    exact Transport.Cell.nil _
  · have solved := (cell_iff_model A label C round empty).mp cell
    let translated := round.map (fun equations => map.store (a := PUnit.unit) equations)
    have combined : map.store (a := PUnit.unit) (C.equations ++ round.flatten) =
        map.store (a := PUnit.unit) C.equations ++ translated.flatten := by
      have distribute : map.store (a := PUnit.unit) (C.equations ++ round.flatten) =
          map.store (a := PUnit.unit) C.equations ++ map.store (a := PUnit.unit) round.flatten :=
        List.map_append
      rw [distribute, store_flatten]
    have carried := map.solvable (a := PUnit.unit)
      ((Frames.ofSubstitution_solvable_iff _ _).mpr solved)
    rw [combined] at carried
    simpa only [translated, List.map_map, Function.comp_def] using
      cell_of_model B targetLabel ⟨map.store (a := PUnit.unit) C.equations, C.present⟩
        translated ((Frames.ofSubstitution_solvable_iff _ _).mp carried)

/-- Reflection of joint solvability gives reflection of cells. The
assumption is on the combined store itself, including the entry equations. -/
theorem cell_iff_licensed (C : Configuration T O) (round : List (EquationStore T))
    (licensed : map.LicensedAt (a := PUnit.unit) (C.equations ++ round.flatten)) :
    (firstOrderTransport B targetLabel).Cell ⟨map.store (a := PUnit.unit) C.equations, C.present⟩
      (round.map fun equations => tell (map.store (a := PUnit.unit) equations)) ↔
    (firstOrderTransport A label).Cell C (round.map tell) := by
  refine ⟨fun target => ?_, map_cell A label B targetLabel map C round⟩
  by_cases empty : round = []
  · subst round
    exact Transport.Cell.nil C
  · apply (cell_iff_model A label C round empty).mpr
    let translated := round.map (map.store (a := PUnit.unit))
    have targetCell : (firstOrderTransport B targetLabel).Cell
        ⟨map.store (a := PUnit.unit) C.equations, C.present⟩ (translated.map tell) := by
      simpa only [translated, List.map_map, Function.comp_def] using target
    have solved := (cell_iff_model B targetLabel _ translated
      (fun eq => empty (List.map_eq_nil_iff.mp eq))).mp targetCell
    have carried := (Frames.ofSubstitution_solvable_iff B _).mpr solved
    have distribute : map.store (a := PUnit.unit) (C.equations ++ round.flatten) =
        map.store (a := PUnit.unit) C.equations ++ map.store (a := PUnit.unit) round.flatten :=
      List.map_append
    apply (Frames.ofSubstitution_solvable_iff A _).mp
    apply licensed.reflects_solvable
    rw [distribute, store_flatten]
    exact carried

end Map

#print axioms cell_iff_model
#print axioms map_cell
#print axioms cell_iff_licensed

section Controls

open Mettapedia.Logic.LP
open Rational (RTree RSubst rationalAction ofStore liftConfig finiteToRational)
open Rational.Controls (ctlSig Sym X Y un r loop finite_occurs subst_r_var loop_solves)

private abbrev z : Term ctlSig := .var 2

private def links : List (EquationStore (Term ctlSig)) :=
  [[(X, Y)], [(Y, z)], [(z, un .f X)]]

private def entry : Configuration (Term ctlSig) Nat := ⟨[], ∅⟩

private def label₀ (_ : Nat) : Term ctlSig := .const true

private theorem finite_cycle_refuted :
    ¬ (FirstOrder.action ctlSig).Consistent links.flatten := by
  rintro ⟨σ, solved⟩
  have xy : σ.applyTerm X = σ.applyTerm Y := solved (X, Y) (by simp [links])
  have yz : σ.applyTerm Y = σ.applyTerm z := solved (Y, z) (by simp [links])
  have zx : σ.applyTerm z = σ.applyTerm (un .f X) := solved (z, un .f X) (by simp [links])
  apply finite_occurs
  refine ⟨σ, fun equation inside => ?_⟩
  obtain rfl := List.mem_singleton.mp inside
  exact xy.trans (yz.trans zx)

private theorem finite_pair_models (a b : Fin 3) (before : a < b) :
    (FirstOrder.action ctlSig).Consistent (links[a] ++ links[b]) := by
  have iCases : a = 0 ∨ a = 1 := by
    have aBound : a.val < 2 := by omega
    have h : a.val = 0 ∨ a.val = 1 := by omega
    rcases h with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  have jCases : b = 1 ∨ b = 2 := by
    have bBound : 0 < b.val := by omega
    have h : b.val = 1 ∨ b.val = 2 := by omega
    rcases h with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  rcases iCases with rfl | rfl <;> rcases jCases with rfl | rfl
  · refine ⟨fun _ => .const true, fun eq member => ?_⟩
    change eq ∈ [(X, Y), (Y, z)] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl
  · refine ⟨fun v => if v = 2 then un .f (.const true) else .const true, fun eq member => ?_⟩
    change eq ∈ [(X, Y), (z, un .f X)] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl
  · exact False.elim (lt_irrefl _ before)
  · refine ⟨fun v => if v = 0 then .const true else un .f (.const true), fun eq member => ?_⟩
    change eq ∈ [(Y, z), (z, un .f X)] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl

/-- A genuine hollow cube in the finite frame becomes filled over rational
trees. Each pair of its three tells has a finite model. Only the joint
equations force a variable to equal a proper extension of itself. -/
theorem rational_fills_hollow_cube :
    (∀ a b : Fin 3, a < b →
      (firstOrderTransport (FirstOrder.action ctlSig) label₀).Cell entry
        [tell links[a], tell links[b]]) ∧
    ¬ (firstOrderTransport (FirstOrder.action ctlSig) label₀).Cell entry (links.map tell) ∧
    (firstOrderTransport (rationalAction ctlSig) (RTree.ofTerm ∘ label₀)).Cell
      (liftConfig entry) (links.map fun equations => tell (ofStore equations)) := by
  refine ⟨fun a b before => cell_of_model (FirstOrder.action ctlSig) label₀ entry
    [links[a], links[b]] ?_, ?_, ?_⟩
  · simpa [entry] using finite_pair_models a b before
  · intro cube
    exact finite_cycle_refuted (by simpa [entry] using
      (cell_iff_model _ _ entry links (by simp [links])).mp cube)
  · have solved : (rationalAction ctlSig).Consistent (ofStore links.flatten) := by
      let assignment : RSubst ctlSig := fun _ => loop .f
      refine ⟨assignment, fun eq member => ?_⟩
      obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
      change original ∈ [(X, Y), (Y, z), (z, un .f X)] at present
      simp only [List.mem_cons, List.not_mem_nil, or_false] at present
      rcases present with rfl | rfl | rfl
      · change RTree.subst assignment (r X) = RTree.subst assignment (r Y)
        rw [subst_r_var, subst_r_var]
      · change RTree.subst assignment (r Y) = RTree.subst assignment (r z)
        rw [subst_r_var, subst_r_var]
      · change RTree.subst assignment (r z) = RTree.subst assignment (r (un .f X))
        have loopModel := loop_solves (r X, r (un .f X)) (by simp [Rational.Controls.loopStore])
        change RTree.subst assignment (r X) = RTree.subst assignment (r (un .f X)) at loopModel
        rw [subst_r_var] at loopModel ⊢
        exact loopModel
    have storeEq : ofStore links.flatten = (links.map ofStore).flatten :=
      store_flatten (FirstOrder.action ctlSig) (rationalAction ctlSig) (finiteToRational ctlSig) links
    rw [storeEq] at solved
    simpa only [List.map_map, Function.comp_def] using
      cell_of_model (rationalAction ctlSig) (RTree.ofTerm ∘ label₀) (liftConfig entry)
        (links.map ofStore) solved

end Controls

#print axioms rational_fills_hollow_cube

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.TellCells
