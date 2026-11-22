import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Characterization.AbsorptionCore

/-!
# Answers across one more row `5`, by positive rules

Let `b₀ = fiveMore a d`: the state `a` with one more row `5` at the identity `d`.

* **Forward** (`answer_forward`): a firing of any rule at `a` is answered at `b₀` by the same rule
  without its checks and collect query, taking the extra row `5` as well (`plusFive`); the two results are
  statically equivalent.
* **Backward** (`answer_backward`, in `AbsorptionBack`): a firing of any rule at `b₀` is answered at
  `a` by the same rule without its checks and collect query, whose takes and reads of `d` become tells of `5`
  (`dropRow`), and which makes one row `5` when the firing kept `d`; the two results are statically
  equivalent.

Both answers are positive rules. So a program containing every positive rule never needs to count the
rows `5`: it contains a rule doing exactly what the other side's firing did, with one row `5` more or
less.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Characterization

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open Mettapedia.Logic.LP
open RuleSyntax.Examples (Tm X E x c fresh_of_ground)
open RuleSyntax.Controls (atoms action)
open AtOneFrame (Sys Cong Moves)

/-! ## Lists of pairs -/

theorem zip_map_pairs {α β γ : Type} (g : α → γ) :
    ∀ l : List (α × β), ((l.map Prod.fst).map g).zip (l.map Prod.snd) = l.map fun q => (g q.1, q.2)
  | [] => rfl
  | q :: l => by simp only [List.map_cons, List.zip_cons_cons, zip_map_pairs g l]

theorem zip_map_left' {α β γ : Type} (g : α → γ) :
    ∀ (ps : List α) (os : List β), (ps.map g).zip os = (ps.zip os).map fun q => (g q.1, q.2)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | p :: ps, o :: os => by simp only [List.map_cons, List.zip_cons_cons, zip_map_left' g ps os]

theorem map_one (W : Finset ℕ) : W.map (1 : Equiv.Perm ℕ).toEmbedding = W := by
  ext o
  rw [Finset.mem_map_equiv]
  exact Iff.rfl

/-- The pairs of a list away from `d`. -/
def keepAway (l : List (Term atoms × ℕ)) (d : ℕ) : List (Term atoms × ℕ) := l.filter fun q => q.2 ≠ d

/-- The pairs of a list at `d`. -/
def atRow (l : List (Term atoms × ℕ)) (d : ℕ) : List (Term atoms × ℕ) := l.filter fun q => q.2 = d

theorem mem_keepAway {l : List (Term atoms × ℕ)} {d : ℕ} {q : Term atoms × ℕ} :
    q ∈ keepAway l d ↔ q ∈ l ∧ q.2 ≠ d := by
  simp [keepAway]

theorem mem_atRow {l : List (Term atoms × ℕ)} {d : ℕ} {q : Term atoms × ℕ} :
    q ∈ atRow l d ↔ q ∈ l ∧ q.2 = d := by
  simp [atRow]

theorem nodup_keepAway {ps : List (Term atoms)} {T : List ℕ} (lengths : ps.length = T.length)
    (nodup : T.Nodup) (d : ℕ) : ((keepAway (ps.zip T) d).map Prod.snd).Nodup := by
  have sub : ((keepAway (ps.zip T) d).map Prod.snd).Sublist ((ps.zip T).map Prod.snd) :=
    (List.filter_sublist).map _
  rw [List.map_snd_zip (by omega)] at sub
  exact nodup.sublist sub

/-! ## Freshness carried over -/

theorem fresh_transfer {P P' : Program Tm} {s s' : State Tm ℕ} (f : Firing ℕ E P s.frame)
    (g : Firing ℕ E P' s'.frame) (fresh : f.Fresh X s)
    (opening : ∀ t : Term atoms, Subst.applyTerm g.opening t = Subst.applyTerm f.opening t)
    (mentions : ∀ t, s'.Mentions t → s.Mentions t ∨ IsConst t)
    (terms : ∀ t ∈ g.rule.terms, t ∈ f.rule.terms ∨ IsConst t) : g.Fresh X s' := by
  intro b g' h
  obtain ⟨u, state, rule⟩ := fresh b g' h
  refine ⟨u, fun t mentioned => ?_, fun t inside => ?_⟩
  · rcases mentions t mentioned with old | ⟨k, rfl⟩
    · exact state t old
    · rfl
  · rcases terms t inside with old | ⟨k, rfl⟩
    · have before := rule t old
      show Subst.applyTerm u (Subst.applyTerm g.opening t) = Subst.applyTerm h t
      rw [opening]
      exact before
    · rfl

/-! ## The rule without its checks, taking one more row `5` -/

/-- **The rule without its checks and collect query, taking one more row `5`.** -/
def plusFive (r : Rule Tm) : Rule Tm :=
  ⟨r.locals, ⟨r.body.take ++ [c 5], r.body.read, r.body.tell, [], r.body.produce⟩, []⟩

theorem terms_plusFive (r : Rule Tm) (t : Term atoms) (inside : t ∈ (plusFive r).terms) :
    t ∈ r.terms ∨ IsConst t := by
  simp only [plusFive, Rule.terms, List.mem_append, List.flatMap_nil, List.mem_singleton,
    List.not_mem_nil, or_false] at inside
  rcases inside with (((((take | five) | read) | tell) | tell) | made)
  · exact Or.inl (AtOneFrame.mem_terms (Or.inl take))
  · exact Or.inr ⟨5, five⟩
  · exact Or.inl (AtOneFrame.mem_terms (Or.inr (Or.inl read)))
  · exact Or.inl (AtOneFrame.mem_terms (Or.inr (Or.inr (Or.inl tell))))
  · exact Or.inl (AtOneFrame.mem_terms (Or.inr (Or.inr (Or.inr (Or.inl tell)))))
  · exact Or.inl (AtOneFrame.mem_terms (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl made)))))))

/-- The rows of `a` and of `fiveMore a d` agree away from `d`. -/
theorem label_fiveMore_of_ne {a : State Tm ℕ} {d o : ℕ} (other : o ≠ d) :
    (fiveMore a d).label o = a.label o := by
  show (if o ∈ ({d} : Finset ℕ) then c 5 else a.label o) = a.label o
  rw [if_neg (by simpa using other)]

theorem label_fiveMore_self (a : State Tm ℕ) (d : ℕ) : (fiveMore a d).label d = c 5 := by
  show (if d ∈ ({d} : Finset ℕ) then c 5 else a.label d) = c 5
  rw [if_pos (Finset.mem_singleton_self d)]

theorem mentions_fiveMore {a : State Tm ℕ} {d : ℕ} (t : Term atoms)
    (mentioned : (fiveMore a d).Mentions t) : a.Mentions t ∨ IsConst t := by
  rcases mentioned with inside | inside | ⟨o, present, rfl⟩
  · exact Or.inl (Or.inl inside)
  · exact Or.inl (Or.inr (Or.inl inside))
  · by_cases isD : o = d
    · subst isD
      exact Or.inr ⟨5, label_fiveMore_self a o⟩
    · have old : o ∈ a.present := by
        rcases Finset.mem_union.mp present with old | new
        · exact old
        · exact absurd (Finset.mem_singleton.mp new) isD
      exact Or.inl (Or.inr (Or.inr ⟨o, old, (label_fiveMore_of_ne isD).symm⟩))

/-- **Forward**: a firing of every rule at `a` is answered at `fiveMore a d`, for `d` absent from `a`
and not made by the firing, by a firing whose result is statically equivalent. -/
theorem answer_forward {a : State Tm ℕ} (f : Firing ℕ E everyRule a.frame) (admitted : f.Admits X a)
    {d : ℕ} (freshD : d ∉ a.present) (notMade : d ∉ f.selection.made) :
    ∃ g : Firing ℕ E everyRule (fiveMore a d).frame, g.rule ∈ positiveRules ∧
      g.Admits X (fiveMore a d) ∧ Static (f.result X a) (g.result X (fiveMore a d)) := by
  obtain ⟨⟨fresh, takenNodup, madeNodup, takeLength, readLength, produceLength, -⟩, enabled,
    solvable, -⟩ := admitted
  let b₀ := fiveMore a d
  let g : Firing ℕ E everyRule b₀.frame :=
    ⟨plusFive f.rule, Set.mem_univ _, f.ext, f.opening,
      ⟨f.selection.taken ++ [d], f.selection.read, f.selection.made⟩, []⟩
  have takenPresent : ∀ o ∈ f.selection.taken, o ∈ a.present := fun o member =>
    enabled.taken_subset (by simpa [Selection.commit] using member)
  have readPresent : ∀ o ∈ f.selection.read, o ∈ a.present := fun o member =>
    enabled.kept_subset (by simpa [Selection.commit] using member)
  have dNotTaken : d ∉ f.selection.taken := fun inside => freshD (takenPresent d inside)
  have dNotRead : d ∉ f.selection.read := fun inside => freshD (readPresent d inside)
  have madeApart : ∀ o ∈ f.selection.made, o ∉ a.present := fun o member present =>
    Finset.disjoint_left.mp enabled.fresh (by simpa [Selection.commit] using member) present
  -- Rows agree away from `d`.
  have rowAgree : ∀ o, o ≠ d → g.row X b₀ o = f.row X a o := fun o other => by
    show Subst.applyTerm (Subst.id atoms) (b₀.label o) = Subst.applyTerm (Subst.id atoms) (a.label o)
    rw [label_fiveMore_of_ne other]
  -- The equations of the answer are those of the firing and `5 = 5`.
  have infoIff : ∀ e, e ∈ g.information X b₀ ↔ e ∈ f.information X a ∨ e = (c 5, c 5) := by
    intro e
    rw [mem_information, mem_information, mem_matching, mem_matching, mem_matching, mem_matching]
    have takeZip : (g.opened X).take.zip g.selection.taken =
        (f.opened X).take.zip f.selection.taken ++ [(c 5, d)] := by
      show (List.map (Subst.applyTerm f.opening) (f.rule.body.take ++ [c 5])).zip
        (f.selection.taken ++ [d]) = _
      rw [List.map_append, List.zip_append (by simp [takeLength])]
      rfl
    rw [takeZip]
    constructor
    · rintro (old | ⟨p, o, paired, rfl⟩ | ⟨p, o, paired, rfl⟩ | told)
      · exact Or.inl (Or.inl old)
      · rcases List.mem_append.mp paired with old | new
        · have other : o ≠ d := fun same => dNotTaken (same ▸ (List.of_mem_zip old).2)
          exact Or.inl (Or.inr (Or.inl ⟨p, o, old, by rw [rowAgree o other]⟩))
        · obtain ⟨isFive, isD⟩ := Prod.mk.inj (List.mem_singleton.mp new)
          right
          rw [isFive, isD]
          show (c 5, Subst.applyTerm (Subst.id atoms) (b₀.label d)) = (c 5, c 5)
          rw [label_fiveMore_self]
          rfl
      · have other : o ≠ d := fun same => dNotRead (same ▸ (List.of_mem_zip paired).2)
        exact Or.inl (Or.inr (Or.inr (Or.inl ⟨p, o, paired, by rw [rowAgree o other]⟩)))
      · exact Or.inl (Or.inr (Or.inr (Or.inr told)))
    · rintro ((old | ⟨p, o, paired, rfl⟩ | ⟨p, o, paired, rfl⟩ | told) | rfl)
      · exact Or.inl old
      · have other : o ≠ d := fun same => dNotTaken (same ▸ (List.of_mem_zip paired).2)
        exact Or.inr (Or.inl ⟨p, o, List.mem_append_left _ paired, by rw [rowAgree o other]⟩)
      · have other : o ≠ d := fun same => dNotRead (same ▸ (List.of_mem_zip paired).2)
        exact Or.inr (Or.inr (Or.inl ⟨p, o, paired, by rw [rowAgree o other]⟩))
      · exact Or.inr (Or.inr (Or.inr told))
      · refine Or.inr (Or.inl ⟨c 5, d, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩)
        show (c 5, c 5) = (c 5, Subst.applyTerm (Subst.id atoms) (b₀.label d))
        rw [label_fiveMore_self]
        rfl
  have infoModels : ∀ σ : Subst atoms, X.Models (a := PUnit.unit) (b := PUnit.unit) σ
      (g.information X b₀) ↔ X.Models (a := PUnit.unit) (b := PUnit.unit) σ (f.information X a) := by
    intro σ
    constructor
    · intro solved e inside
      exact solved e ((infoIff e).mpr (Or.inl inside))
    · intro solved e inside
      rcases (infoIff e).mp inside with old | rfl
      · exact solved e old
      · rfl
  have admittedG : g.Admits X b₀ := by
    refine (admits_iff g).mpr ⟨?_, ⟨?_, madeNodup, ?_, readLength, produceLength, rfl⟩, ?_, ?_,
      fun check inside => absurd inside List.not_mem_nil,
      fun q inside => absurd inside List.not_mem_nil⟩
    · exact fresh_transfer f g fresh (fun _ => rfl) (fun t m => mentions_fiveMore t m)
        (terms_plusFive f.rule)
    · exact List.nodup_append.mpr ⟨takenNodup, List.nodup_singleton d, fun o inside o' same => by
        rw [List.mem_singleton] at same
        subst same
        exact fun equal => dNotTaken (equal ▸ inside)⟩
    · show (f.rule.body.take ++ [c 5]).length = (f.selection.taken ++ [d]).length
      simp [takeLength]
    · refine ⟨fun o inside => ?_, fun o inside => ?_, ?_, ?_, fun q inside => ?_⟩
      · simp only [g, Selection.commit, List.toFinset_append, Finset.mem_union, List.mem_toFinset,
          List.mem_singleton] at inside
        rcases inside with taken | rfl
        · exact Finset.mem_union_left _ (takenPresent o taken)
        · exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
      · have read : o ∈ f.selection.read := by simpa [g, Selection.commit] using inside
        exact Finset.mem_union_left _ (readPresent o read)
      · rw [Finset.disjoint_left]
        intro o inside inside'
        simp only [g, Selection.commit, List.toFinset_append, Finset.mem_union, List.mem_toFinset,
          List.mem_singleton] at inside inside'
        rcases inside with taken | rfl
        · exact Finset.disjoint_left.mp enabled.apart (by simpa [Selection.commit] using taken)
            (by simpa [Selection.commit] using inside')
        · exact dNotRead inside'
      · rw [Finset.disjoint_left]
        intro o inside present
        have made : o ∈ f.selection.made := by simpa [g, Selection.commit] using inside
        rcases Finset.mem_union.mp present with old | new
        · exact madeApart o made old
        · exact notMade (Finset.mem_singleton.mp new ▸ made)
      · simp [g, Selection.commit] at inside
    · obtain ⟨β, σ, solved⟩ := solvable
      cases β
      exact ⟨PUnit.unit, σ, (infoModels σ).mpr solved⟩
  refine ⟨g, positive_of_nil rfl rfl, admittedG,
    static_of_perm (fun _ σ => (infoModels σ).symm) ?_ 1 ?_ ?_⟩
  · intro w
    unfold KnowsVar
    constructor
    · rintro (inside | inside)
      · obtain ⟨e, member, same⟩ := List.mem_map.mp inside
        exact Or.inl (List.mem_map.mpr ⟨e, (infoIff e).mpr (Or.inl member), same⟩)
      · obtain ⟨e, member, same⟩ := List.mem_map.mp inside
        exact Or.inr (List.mem_map.mpr ⟨e, (infoIff e).mpr (Or.inl member), same⟩)
    · rintro (inside | inside)
      · obtain ⟨e, member, same⟩ := List.mem_map.mp inside
        rcases (infoIff e).mp member with old | rfl
        · exact Or.inl (List.mem_map.mpr ⟨e, old, same⟩)
        · cases same
      · obtain ⟨e, member, same⟩ := List.mem_map.mp inside
        rcases (infoIff e).mp member with old | rfl
        · exact Or.inr (List.mem_map.mpr ⟨e, old, same⟩)
        · cases same
  · show fire (a.present ∪ {d}) (g.selection.commit (T := Unit)) =
      (fire a.present (f.selection.commit (T := Unit))).map (1 : Equiv.Perm ℕ).toEmbedding
    rw [map_one]
    ext o
    rw [mem_fire, mem_fire]
    simp only [g, Selection.commit, List.toFinset_append, Finset.mem_union, List.mem_toFinset,
      List.mem_singleton, Finset.mem_singleton]
    constructor
    · rintro (⟨present, notTaken⟩ | made)
      · rcases present with old | isD
        · exact Or.inl ⟨old, fun taken => notTaken (Or.inl taken)⟩
        · exact absurd (Or.inr isD) notTaken
      · exact Or.inr made
    · rintro (⟨present, notTaken⟩ | made)
      · refine Or.inl ⟨Or.inl present, ?_⟩
        rintro (taken | isD)
        · exact notTaken taken
        · exact freshD (isD ▸ present)
      · exact Or.inr made
  · intro o inside
    show relabel (g.row X b₀) f.selection.made (g.opened X).produce o =
      relabel (f.row X a) f.selection.made (f.opened X).produce o
    have produceLength' : f.selection.made.length = (f.opened X).produce.length := by
      rw [← produceLength]
      exact (List.length_map _).symm
    by_cases made : o ∈ f.selection.made
    · exact relabel_eq_of_mem _ _ _ _ o produceLength' made
    · have old : o ∈ a.present := by
        rcases mem_fire.mp inside with ⟨old, -⟩ | isMade
        · exact old
        · exact absurd (by simpa [Selection.commit] using isMade) made
      rw [Firing.relabel_of_not_mem _ _ _ made, Firing.relabel_of_not_mem _ _ _ made]
      exact rowAgree o (fun same => freshD (same ▸ old))

#print axioms zip_map_pairs
#print axioms zip_map_left'
#print axioms map_one
#print axioms mem_keepAway
#print axioms mem_atRow
#print axioms nodup_keepAway
#print axioms fresh_transfer
#print axioms terms_plusFive
#print axioms label_fiveMore_of_ne
#print axioms label_fiveMore_self
#print axioms mentions_fiveMore
#print axioms answer_forward

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Characterization
