import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Characterization.Instances

/-!
# The congruence counts the unknowns a firing opens

At the one-frame first-order instance.

* `inline_separates`: the rule "tell `x = 5`, make `x`" and the rule "make `5`" are not congruent at
  the empty store. The first fires with a result whose knowledge is `w = 5` for the opened unknown
  `w`; every answer of the second has empty knowledge.
* `private_unknown_separates`: the states "knowledge `w = 5`, one row `w`" and "knowledge `w = w`, one
  row `5`" mention the same unknowns, have the same present rows and labels that are equal at every
  solution of the first; they are congruent beside no pair of programs. The clause that separates
  them is the one about solutions, and no hypothesis on the programs is used.
* `touch_result_not_static`: the result of every admitted firing of "take `x`, make `x`" is not
  statically equivalent to the state it fired at.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Characterization.Inlining

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open Mettapedia.Logic.LP
open RuleSyntax.Examples (Tm X E x c)
open RuleSyntax.Controls (atoms action)
open AtOneFrame (Sys Cong empty spawn)

/-! ## A told constant against the constant itself -/

/-- Tell `x = 5`, make `x`. -/
def bindMake : Rule Tm := ⟨PUnit.unit, ⟨[], [], [(x, c 5)], [], [x]⟩, []⟩

/-- The firing of `bindMake` at the empty store that opens `x` as the unknown `1`. -/
def bindFiring : Firing ℕ E ({bindMake} : Program Tm) empty.frame :=
  ⟨bindMake, Set.mem_singleton _, PUnit.unit, fun v => .var (1 + v), ⟨[], [], [0]⟩, []⟩

theorem bindFiring_admitted : bindFiring.Admits X empty := by
  refine (admits_iff bindFiring).mpr ⟨?_, ⟨List.nodup_nil, List.nodup_singleton _, rfl, rfl, rfl,
    rfl⟩, ?_, ?_, ?_, ?_⟩
  · refine fresh_shift bindFiring (N := 1) (fun t mentioned => ?_) fun v => rfl
    rcases mentioned with inside | inside | ⟨o, present, -⟩
    · exact absurd inside List.not_mem_nil
    · exact absurd inside List.not_mem_nil
    · exact absurd present (Finset.notMem_empty o)
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [bindFiring, Selection.commit]
    · simp [bindFiring, Selection.commit]
    · simp [bindFiring, Selection.commit]
    · simp [bindFiring, Selection.commit, empty]
    · intro q inside
      simp [bindFiring, Selection.commit] at inside
  · refine ⟨PUnit.unit, fun _ => c 5, fun e inside => ?_⟩
    have unfolded : e ∈ ([] : EquationStore (Term atoms)) ++ [] ++ [] ++
        [(Subst.applyTerm (fun v => .var (1 + v)) x, Subst.applyTerm (fun v => .var (1 + v)) (c 5))] :=
      inside
    simp only [List.nil_append, List.mem_singleton] at unfolded
    subst unfolded
    rfl
  · intro check inside
    exact absurd inside List.not_mem_nil
  · intro q inside
    exact absurd inside List.not_mem_nil

/-- **A told constant is not the constant**: "tell `x = 5`, make `x`" against "make `5`", at the
empty store. -/
theorem inline_separates : ¬ Cong ⟨{bindMake}, empty⟩ ⟨{spawn}, empty⟩ := by
  intro related
  obtain ⟨g, -, static⟩ := answers_of_congruent (bounded_singleton _) (bounded_singleton _) related
    bindFiring bindFiring_admitted
  obtain ⟨rule, member, ext, ι, selection, seen⟩ := g
  have isSpawn : rule = spawn := member
  subst isSpawn
  have rightKnowledge : (Firing.result X empty
      (⟨spawn, member, ext, ι, selection, seen⟩ : Firing ℕ E ({spawn} : Program Tm)
        empty.frame)).knowledge = [] := rfl
  have leftKnowledge : (bindFiring.result X empty).knowledge =
      [((Term.var 1 : Term atoms), c 5)] := rfl
  rcases (static_iff_clauses _ _).mp static with ⟨unsolvable, -⟩ | ⟨π, -, solutions, -, -⟩
  · exact unsolvable bindFiring_admitted.2.2.1
  · have right : X.Models (a := PUnit.unit) (b := PUnit.unit) (fun _ => c 0)
        (Firing.result X empty (⟨spawn, member, ext, ι, selection, seen⟩ :
          Firing ℕ E ({spawn} : Program Tm) empty.frame)).knowledge := by
      rw [rightKnowledge]
      intro e inside
      exact absurd inside List.not_mem_nil
    have left := (solutions (fun _ => c 0)).mpr right
    rw [leftKnowledge] at left
    have bad : (c 0 : Term atoms) = c 5 :=
      left ((Term.var 1 : Term atoms), c 5) (List.mem_singleton_self _)
    exact absurd (Term.const.inj bad) (by decide)

/-! ## An unknown that only one firing ever named -/

/-- Knowledge `w = 5`, one row `w`. -/
def boundRow : State Tm ℕ := ⟨PUnit.unit, [(Term.var 1, c 5)], {0}, fun _ => .var 1⟩

/-- Knowledge `w = w`, one row `5`. -/
def fiveRow : State Tm ℕ := ⟨PUnit.unit, [(Term.var 1, Term.var 1)], {0}, fun _ => c 5⟩

/-- **The same mentioned unknowns, the same rows, labels equal at every solution of the first, and
congruent beside no pair of programs.** No hypothesis on the programs. -/
theorem private_unknown_separates (P P' : Program Tm) :
    (∀ w, boundRow.Mentions (.var w) ↔ fiveRow.Mentions (.var w)) ∧
      boundRow.present = fiveRow.present ∧
      (∀ σ : Subst atoms, X.Models (a := PUnit.unit) (b := PUnit.unit) σ boundRow.knowledge →
        Subst.applyTerm σ (boundRow.label 0) = Subst.applyTerm σ (fiveRow.label 0)) ∧
      ¬ Cong ⟨P, boundRow⟩ ⟨P', fiveRow⟩ := by
  refine ⟨fun w => ⟨?_, ?_⟩, rfl, fun σ solved => solved _ (List.mem_singleton_self _), ?_⟩
  · rintro (inside | inside | ⟨o, -, same⟩)
    · exact Or.inl inside
    · have h : (Term.var w : Term atoms) = c 5 := List.mem_singleton.mp inside
      cases h
    · have h : (Term.var 1 : Term atoms) = .var w := same
      refine Or.inl ?_
      rw [← h]
      exact List.mem_singleton_self _
  · rintro (inside | inside | ⟨o, -, same⟩)
    · exact Or.inl inside
    · exact Or.inl inside
    · have h : (c 5 : Term atoms) = .var w := same
      cases h
  · intro related
    have equivalent := equivalent_of_congruent related
    have right : X.Models (a := PUnit.unit) (b := PUnit.unit) (fun _ => c 0) fiveRow.knowledge := by
      intro e inside
      have h : e = ((Term.var 1 : Term atoms), (Term.var 1 : Term atoms)) :=
        List.mem_singleton.mp inside
      subst h
      rfl
    have left := (equivalent PUnit.unit (fun _ => c 0)).mpr right
    have bad : (c 0 : Term atoms) = c 5 :=
      left ((Term.var 1 : Term atoms), c 5) (List.mem_singleton_self _)
    exact absurd (Term.const.inj bad) (by decide)

/-! ## Renewing a row leaves a trace -/

/-- **The result of a firing of touch is not statically equivalent to the state it fired at**: its
knowledge names the unknown the firing opened, which the state did not mention. -/
theorem touch_result_not_static {s : State Tm ℕ} (f : Firing ℕ E ({touch} : Program Tm) s.frame)
    (admitted : f.Admits X s) : ¬ Static (f.result X s) s := by
  intro static
  have solvable : X.Solvable (a := PUnit.unit) s.knowledge := solvable_of_admits admitted
  obtain ⟨rule, member, ext, ι, ⟨taken, read, made⟩, seen⟩ := f
  have isTouch : rule = touch := member
  subst isTouch
  obtain ⟨fresh, -, -, takeLength, -, -, -⟩ := admitted.1
  obtain ⟨o, rfl⟩ := List.length_eq_one_iff.mp takeLength.symm
  obtain ⟨w, opened, unmentioned⟩ := opening_var _ fresh (v := 0)
    (by simp [touch, Rule.terms, x])
  have opened' : ι 0 = .var w := opened
  refine not_static_of_mentions solvable (w := w) ?_ unmentioned (static_symm static)
  refine Or.inl (List.mem_map.mpr ⟨(Subst.applyTerm ι x, Subst.applyTerm (Subst.id atoms) (s.label o)),
    ?_, opened'⟩)
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
    (List.mem_singleton_self _)))

/-- Beside every program that leaves a constant unused, the state after touch and the state before
it are not congruent. -/
theorem touch_result_not_congruent {P : Program Tm} (bounded : Bounded P) {s : State Tm ℕ}
    (f : Firing ℕ E ({touch} : Program Tm) s.frame) (admitted : f.Admits X s) :
    ¬ Cong ⟨P, f.result X s⟩ ⟨P, s⟩ := fun related =>
  touch_result_not_static f admitted ((congruent_iff_static bounded _ _).mp related)

#print axioms bindFiring_admitted
#print axioms inline_separates
#print axioms private_unknown_separates
#print axioms touch_result_not_static
#print axioms touch_result_not_congruent

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Characterization.Inlining
