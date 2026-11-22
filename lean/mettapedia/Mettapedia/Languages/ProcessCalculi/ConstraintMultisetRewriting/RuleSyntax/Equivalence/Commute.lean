import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Modulo

/-!
# Adding rows commutes with a step that asks no query

A firing **asks no query** (`QueryFree`) when its checks are equation guards and it has no collect query
patterns. For such a firing, admitted at a state, adding rows at identities absent from the state and
from the firing's made identities keeps it admitted, provided its opening is still fresh, and the
result is the old result with the same rows added, carried along the firing's extension
(`step_addRows_of_queryFree`, `reduces_addRows_of_queryFree`). This is the commutation of a context
with a step that a labelled semantics, or an up-to-context argument, uses.

Each side condition has its counterexample in the tree:

* **No query**: a row added inside an absence region refuses the firing
  (`RuleSyntax.Controls.row_in_region_refused`), and a two-row take or a counting rule is enabled or
  disabled by a context (`AtOneFrame.queryFree_count_separates`, `AtOneFrame.count_separates`).
* **Freshness at the new state**: an opening that captures an unknown the new rows mention is not
  fresh (`RuleSyntax.Examples.capture_not_fresh` is the same failure for the state's own unknown).
* **Made identities not among the new ones**: otherwise the firing would make a present identity, and
  is not enabled.

A tell is not covered: a firing with no query is switched off by a tell that contradicts its own
equations on an unknown it shares with the state.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)

universe uO uT uH uE uOcc

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} {E : Extensions.{uO, uH, uE} Hom}

/-- **A firing that asks no query**: its checks are equation guards and it has no collect pattern. -/
def QueryFree {P : Program Tm} {a : Obj} (f : Firing O E P a) : Prop :=
  (∀ c ∈ f.rule.body.checks, ∃ l t, c = Check.equal l t) ∧ f.rule.collect = []

theorem zipWith_congr_right {α : Type uT} {β : Type uOcc} {γ : Type uT} (g g' : β → γ) :
    ∀ (ps : List α) (os : List β), (∀ o ∈ os, g o = g' o) →
      ps.zipWith (fun p o => (p, g o)) os = ps.zipWith (fun p o => (p, g' o)) os
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | p :: ps, o :: os, same => by
      simp only [List.zipWith_cons_cons]
      rw [same o List.mem_cons_self, zipWith_congr_right g g' ps os
        (fun o' inside => same o' (List.mem_cons_of_mem _ inside))]

variable [DecidableEq O]

/-- **Adding rows commutes with a step that asks no query.** -/
theorem step_addRows_of_queryFree {P : Program Tm} {s : State Tm O} (f : Firing O E P s.frame)
    (queryFree : QueryFree f) (admitted : f.Admits X s) (ids : Finset O) (label : O → Tm s.frame)
    (apart : Disjoint ids s.present) (notMade : ∀ o ∈ f.selection.made, o ∉ ids)
    (fresh : f.Fresh X (addRows s ids label)) :
    f.Admits X (addRows s ids label) ∧
      f.result X (addRows s ids label) =
        addRows (f.result X s) ids (fun o => X.act (E.weaken f.ext) (label o)) := by
  obtain ⟨⟨-, shapes⟩, enabled, solvable, asks⟩ := admitted
  have takenPresent : ∀ o ∈ f.selection.taken, o ∈ s.present := fun o member =>
    enabled.taken_subset (by simpa [Selection.commit] using member)
  have readPresent : ∀ o ∈ f.selection.read, o ∈ s.present := fun o member =>
    enabled.kept_subset (by simpa [Selection.commit] using member)
  have madeAbsent : ∀ o ∈ f.selection.made, o ∉ s.present := fun o member present =>
    Finset.disjoint_left.mp enabled.fresh (by simpa [Selection.commit] using member) present
  have oldRow : ∀ o, o ∉ ids → f.row X (addRows s ids label) o = f.row X s o := by
    intro o notNew
    show X.act (E.weaken f.ext) (if o ∈ ids then label o else s.label o) = X.act (E.weaken f.ext) (s.label o)
    rw [if_neg notNew]
  have notNewOfPresent : ∀ o ∈ s.present, o ∉ ids := fun o present inside =>
    Finset.disjoint_left.mp apart inside present
  have info : f.information X (addRows s ids label) = f.information X s := by
    have take := zipWith_congr_right (f.row X (addRows s ids label)) (f.row X s) (f.opened X).take
      f.selection.taken (fun o member => oldRow o (notNewOfPresent o (takenPresent o member)))
    have read := zipWith_congr_right (f.row X (addRows s ids label)) (f.row X s) (f.opened X).read
      f.selection.read (fun o member => oldRow o (notNewOfPresent o (readPresent o member)))
    exact congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) rfl take) read) rfl
  -- The guard predicate does not read the rows: only equation guards, no collect query.
  have holds : ∀ {b : Obj} (σ : Hom (E.target f.ext) b),
      f.Holds X s σ → f.Holds X (addRows s ids label) σ := by
    intro b σ holdsS
    refine ⟨fun c member => ?_, fun q member => ?_⟩
    · obtain ⟨c₀, inside, rfl⟩ := List.mem_map.mp member
      obtain ⟨l, t, rfl⟩ := queryFree.1 c₀ inside
      exact holdsS.1 _ member
    · have inside := (List.of_mem_zip member).1
      unfold Firing.collectOpened at inside
      rw [queryFree.2] at inside
      exact absurd inside List.not_mem_nil
  refine ⟨⟨⟨fresh, shapes⟩, ?_, ?_, ?_⟩, ?_⟩
  · refine ⟨fun o member => ?_, fun o member => ?_, enabled.apart, ?_, fun q member => ?_⟩
    · exact Finset.mem_union_left _ (enabled.taken_subset member)
    · exact Finset.mem_union_left _ (enabled.kept_subset member)
    · rw [Finset.disjoint_left]
      intro o member present
      have made : o ∈ f.selection.made := by simpa [Selection.commit] using member
      rcases Finset.mem_union.mp present with old | new
      · exact madeAbsent o made old
      · exact notMade o made new
    · simp [Selection.commit] at member
  · rw [info]
    exact solvable
  · rw [info]
    intro b σ solved
    exact holds σ (asks b σ solved)
  · show (⟨E.target f.ext, f.information X (addRows s ids label),
        fire (s.present ∪ ids) (f.selection.commit (T := Unit)),
        relabel (f.row X (addRows s ids label)) f.selection.made (f.opened X).produce⟩ : State Tm O) =
      ⟨E.target f.ext, f.information X s, fire s.present (f.selection.commit (T := Unit)) ∪ ids,
        fun o => if o ∈ ids then X.act (E.weaken f.ext) (label o)
          else relabel (f.row X s) f.selection.made (f.opened X).produce o⟩
    have present : fire (s.present ∪ ids) (f.selection.commit (T := Unit)) =
        fire s.present (f.selection.commit (T := Unit)) ∪ ids := by
      ext o
      simp only [mem_fire, Finset.mem_union, Selection.commit, List.mem_toFinset]
      constructor
      · rintro (⟨old | new, notTaken⟩ | made)
        · exact Or.inl (Or.inl ⟨old, notTaken⟩)
        · exact Or.inr new
        · exact Or.inl (Or.inr made)
      · rintro ((⟨old, notTaken⟩ | made) | new)
        · exact Or.inl ⟨Or.inl old, notTaken⟩
        · exact Or.inr made
        · refine Or.inl ⟨Or.inr new, fun taken => ?_⟩
          exact notNewOfPresent o (takenPresent o taken) new
    rw [info, present]
    congr 1
    funext o
    by_cases new : o ∈ ids
    · have notMade' : o ∉ f.selection.made := fun made => notMade o made new
      have first : relabel (f.row X (addRows s ids label)) f.selection.made (f.opened X).produce o =
          f.row X (addRows s ids label) o := Firing.relabel_of_not_mem _ _ _ notMade'
      have second : f.row X (addRows s ids label) o = X.act (E.weaken f.ext) (label o) := by
        show X.act (E.weaken f.ext) (if o ∈ ids then label o else s.label o) =
          X.act (E.weaken f.ext) (label o)
        rw [if_pos new]
      exact (first.trans second).trans (if_pos new).symm
    · have lengths : f.selection.made.length = (f.opened X).produce.length := by
        rw [← shapes.2.2.2.2.1]
        exact (List.length_map _).symm
      have same : relabel (f.row X (addRows s ids label)) f.selection.made (f.opened X).produce o =
          relabel (f.row X s) f.selection.made (f.opened X).produce o := by
        by_cases made : o ∈ f.selection.made
        · exact relabel_eq_of_mem _ _ _ _ o lengths made
        · exact (Firing.relabel_of_not_mem _ _ _ made).trans
            ((oldRow o new).trans (Firing.relabel_of_not_mem _ _ _ made).symm)
      exact same.trans (if_neg new).symm

/-- **The reduction, beside the new rows.** -/
theorem reduces_addRows_of_queryFree {P : Program Tm} {s : State Tm O} (f : Firing O E P s.frame)
    (queryFree : QueryFree f) (admitted : f.Admits X s) (ids : Finset O) (label : O → Tm s.frame)
    (apart : Disjoint ids s.present) (notMade : ∀ o ∈ f.selection.made, o ∉ ids)
    (fresh : f.Fresh X (addRows s ids label)) :
    Reduces X O E ⟨P, addRows s ids label⟩
      ⟨P, addRows (f.result X s) ids (fun o => X.act (E.weaken f.ext) (label o))⟩ := by
  obtain ⟨admittedThere, result⟩ :=
    step_addRows_of_queryFree f queryFree admitted ids label apart notMade fresh
  exact ⟨rfl, f, admittedThere, result⟩

#print axioms zipWith_congr_right
#print axioms step_addRows_of_queryFree
#print axioms reduces_addRows_of_queryFree

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence
