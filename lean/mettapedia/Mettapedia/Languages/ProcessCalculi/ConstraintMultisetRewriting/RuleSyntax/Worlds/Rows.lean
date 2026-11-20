import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope.Composition
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Examples

/-!
# Rows that arrive in what a world sees: a positive firing does not read them

Where worlds share located rows (a world's view holds the rows of a shared space, as in
`Hosting.Alternatives.Located.LState.view` and `Worlds.Tree.view`), a neighbour changes what a world
sees by adding a row to the shared space. Its knowledge stays at its own world.

* **`positive_admits_more_rows`**: at every frame action, a firing of a positive rule (equation
  checks only, no collect pattern: `Scope.Positive`) that is admitted at a state is admitted at the
  state with further rows, the old rows keeping their labels, when its opening is fresh there and its
  made identities are not among the new rows. Nothing is asked of any other world's knowledge.
* `consume_beside_a_row`: an instance of every hypothesis, on first-order atoms.

The control for positivity is `Worlds.Controls.shared_row_blocks`: a none check passes before a
row is shared and is refused after. So with located rows that checks read, a positive firing is
switched off by no row that arrives, and a firing with a none check can be.
-/

set_option autoImplicit false

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Examples
  (Tm X E c demo tokenState consume consumeFiring consume_admitted fresh_of_ground)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls (action)

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled)

universe uO uT uH uE uOcc

section General

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH} {O : Type uOcc}
  [DecidableEq O] {X : Frames Tm Hom} {E : Extensions.{uO, uH, uE} Hom} {P : Program Tm}

/-- **A positive firing does not read the rows it does not select**: admitted at a state, it is
admitted at the state with further rows, the old rows keeping their labels, when its opening is fresh
there and its made identities are not among the new rows. -/
theorem positive_admits_more_rows (s : State Tm O) (extra : Finset O) (label' : O → Tm s.frame)
    (same : ∀ o ∈ s.present, label' o = s.label o) (f : Firing O E P s.frame)
    (positive : Scope.Positive f.rule) (admitted : f.Admits X s)
    (fresh : Firing.Fresh X ⟨s.frame, s.knowledge, s.present ∪ extra, label'⟩ f)
    (new : ∀ o ∈ f.selection.made, o ∉ extra) :
    Firing.Admits X ⟨s.frame, s.knowledge, s.present ∪ extra, label'⟩ f := by
  obtain ⟨⟨-, shapes⟩, enabled, solvable, entails⟩ := admitted
  have rows : ∀ o, o ∈ f.selection.taken ∨ o ∈ f.selection.read →
      Firing.row X ⟨s.frame, s.knowledge, s.present ∪ extra, label'⟩ f o = f.row X s o := by
    intro o selected
    have inside : o ∈ s.present := by
      rcases selected with taken | read
      · exact enabled.taken_subset (List.mem_toFinset.mpr taken)
      · exact enabled.kept_subset (List.mem_toFinset.mpr read)
    show X.act (E.weaken f.ext) (label' o) = X.act (E.weaken f.ext) (s.label o)
    rw [same o inside]
  have takeEq := Scope.zipWith_congr_right
    (fun pattern o => (pattern, Firing.row X ⟨s.frame, s.knowledge, s.present ∪ extra, label'⟩ f o))
    (fun pattern o => (pattern, f.row X s o)) (f.opened X).take f.selection.taken
    (fun o member pattern => congrArg (Prod.mk pattern) (rows o (Or.inl member)))
  have readEq := Scope.zipWith_congr_right
    (fun pattern o => (pattern, Firing.row X ⟨s.frame, s.knowledge, s.present ∪ extra, label'⟩ f o))
    (fun pattern o => (pattern, f.row X s o)) (f.opened X).read f.selection.read
    (fun o member pattern => congrArg (Prod.mk pattern) (rows o (Or.inr member)))
  have info : Firing.information X ⟨s.frame, s.knowledge, s.present ∪ extra, label'⟩ f =
      f.information X s := by
    show X.applyStore (E.weaken f.ext) s.knowledge ++
        (f.opened X).take.zipWith (fun pattern o =>
          (pattern, Firing.row X ⟨s.frame, s.knowledge, s.present ∪ extra, label'⟩ f o))
          f.selection.taken ++
        (f.opened X).read.zipWith (fun pattern o =>
          (pattern, Firing.row X ⟨s.frame, s.knowledge, s.present ∪ extra, label'⟩ f o))
          f.selection.read ++ (f.opened X).tell = _
    rw [takeEq, readEq]
    rfl
  refine ⟨⟨fresh, shapes⟩, ?_, ?_, ?_⟩
  · refine ⟨fun o member => Finset.mem_union_left _ (enabled.taken_subset member),
      fun o member => Finset.mem_union_left _ (enabled.kept_subset member), enabled.apart, ?_,
      fun q member => by simp [Selection.commit] at member⟩
    show Disjoint _ (s.present ∪ extra)
    rw [Finset.disjoint_union_right]
    exact ⟨enabled.fresh,
      Finset.disjoint_left.mpr fun {o} made inExtra => new o (List.mem_toFinset.mp made) inExtra⟩
  · rw [info]
    exact solvable
  · intro b σ solved
    rw [info] at solved
    have holds := entails b σ solved
    refine ⟨fun check member => ?_, fun q member => ?_⟩
    · obtain ⟨c₀, inRule, rfl⟩ := List.mem_map.mp member
      obtain ⟨l, l', rfl⟩ := positive.1 c₀ inRule
      exact holds.1 _ (List.mem_map.mpr ⟨_, inRule, rfl⟩)
    · have empty : f.collectOpened X = [] := by
        show f.rule.collect.map (X.act f.opening) = []
        rw [positive.2]
        rfl
      rw [empty] at member
      exact absurd member (by simp)

end General

/-! ## An instance of every hypothesis -/

/-- The token state with one more row, `9`, at identity `5`. -/
def tokenAndNine : State Tm ℕ :=
  ⟨PUnit.unit, [], ({0} : Finset ℕ) ∪ {5}, fun o => if o = 5 then c 9 else c 1⟩

/-- **The token is taken beside the new row**: an instance of `positive_admits_more_rows`. -/
theorem consume_beside_a_row : consumeFiring.Admits X tokenAndNine := by
  refine positive_admits_more_rows (X := X) tokenState {5} (fun o => if o = 5 then c 9 else c 1) ?_
    consumeFiring ⟨fun check member => absurd member List.not_mem_nil, rfl⟩ consume_admitted ?_ ?_
  · intro o inside
    have isToken : o = 0 := Finset.mem_singleton.mp inside
    subst isToken
    rfl
  · apply fresh_of_ground action
    intro t member σ
    simp only [consumeFiring, consume, Rule.terms, List.map_nil, List.flatMap_nil, List.nil_append,
      List.append_nil, List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl
  · intro o made inExtra
    have isMade : o = 1 := List.mem_singleton.mp made
    have isNine : o = 5 := Finset.mem_singleton.mp inExtra
    exact absurd (isMade.symm.trans isNine) (by decide)

#print axioms positive_admits_more_rows
#print axioms consume_beside_a_row

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds
