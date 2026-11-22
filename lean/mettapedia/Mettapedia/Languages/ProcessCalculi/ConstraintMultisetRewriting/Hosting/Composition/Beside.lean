import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.Restriction
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.Unmatched
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Alternatives.Chains

/-!
# A hosted program beside other rows: the step correspondence, firing by firing

A neighbour of a hosted program puts rows and knowledge into the state, and rules into the program. A
state of the step has one frame and one knowledge, so the neighbour's knowledge is part of the state's
knowledge and its rows are present rows of the state. The hosted program is then run **at that
state**: `Fires N P` is the same relation, from another start.

**The invariant** (`Beside N P n b w a others`). The state `w` represents the alternative `b` at its row
`a` **beside the rows `others`** when

* `hosted`: `w` with only the alternative's row and the equation rows present represents `b`
  (`Represents`, unchanged). Its clause on readings is taken under the whole knowledge of `w`: the
  alternative's row reads, under every solution of everything the state knows, exactly as the
  alternative under the solutions of its store. So the neighbour's knowledge may say nothing about the
  hosted rows that the alternative's store does not say, and must be solvable together with it;
* `present`, `apart`: the present rows are those and the rows `others`.

**The step theorems beside other rows.** Each direction asks one thing more of the other rows, and
neither asks what the other does.

* `simulation_beside`: every source move of the alternative is, for each live alternative it makes,
  one firing of the translated program at `w`, to a state that represents it beside the same rows. At a
  call that no equation matches, and only there, no other row may match the call (`NoMatchingRow`).
  Rows that read as alternatives' rows do not disturb this direction.
* `reflection_beside`: every firing of the translated program at `w` is a source move of the
  alternative, to a state that represents one of the alternatives the move makes beside the same rows,
  when no other row reads as an alternative's row `alt(…)` (`NeverReads (IsAlternative N)`); the
  condition holds again at the state reached. Nothing is asked of equation rows among the other rows:
  a row can refuse the unmatched call's firing, never add a firing.
* `beside_empty`: beside no row, the invariant is `Represents`, and the two theorems reduce to
  `simulation_arrows` and `reflection_arrows`.

`reflection_beside` is `reflection_arrows` at the state with fewer rows (`admits_restrict`).
`simulation_beside` fires the canonical firing at `w` itself and uses `represents_after` at the state
with fewer rows: an opening that is fresh where the state mentions less can be refused where it
mentions more (`RuleSyntax.Contextual.CouplingControls.coupling_admitted` against
`coupling_refused_when_mentioned`), so the firing that `simulation_arrows` gives cannot be carried
over, and the moves are told apart here once more.

**Other rows that stay as they are.** `NeverReads shape w others` (no row of `others` reads, at a
solution of the knowledge, as a term of the given shape) is kept by every firing that does not make a
row of `others` (`neverReads_after`): the readings of a row that stays can only become fewer.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} (N : Nodes S Γ star) {κ : Keys S}

/-! ## Rows that never read as a given shape -/

/-- **No row of `others` reads as a term of the given shape**, at any solution of the knowledge. -/
def NeverReads (shape : ∀ B : Interface.Frames.Frame S, Observation S B.arity → Prop) (w : HostState S)
    (others : Finset ℕ) : Prop :=
  ∀ o ∈ others, ∀ (B : Interface.Frames.Frame S) (σ : Assignment w.frame.arity B.arity),
    (Interface.Frames.contextual S).Models σ w.knowledge → ¬ shape B (instantiateObservation σ (w.label o))

/-- An alternative's row: `alt(x, y)`. -/
def IsAlternative (B : Interface.Frames.Frame S) (q : Observation S B.arity) : Prop :=
  ∃ x y : Term (signature S B.arity) Γ star, q = observe (altN N x y)

/-- An equation row: `eqn(x)`. -/
def IsEquationRow (B : Interface.Frames.Frame S) (q : Observation S B.arity) : Prop :=
  ∃ x : Term (signature S B.arity) Γ star, q = observe (eqnN N x)

/-- **Rows that stay keep what they never read as**: after any firing of any program that does not
make a row of `others`. -/
theorem neverReads_after {shape : ∀ B : Interface.Frames.Frame S, Observation S B.arity → Prop}
    {Prog : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)} {w : HostState S}
    (f : RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations S) Prog w.frame) {others : Finset ℕ}
    (quiet : NeverReads shape w others) (notMade : ∀ o ∈ others, o ∉ f.selection.made) :
    NeverReads shape (f.result (Interface.Frames.contextual S) w) others := by
  intro o inside B σ solved reads
  have known := RuleSyntax.Firing.knowledge_solved (X := Interface.Frames.contextual S) f solved
  rw [RuleSyntax.Firing.result_label_other f (notMade o inside)] at reads
  change shape B (instantiateObservation σ (instantiateObservation _ (w.label o))) at reads
  rw [instantiateObservation_comp] at reads
  exact quiet o inside B _ known reads

/-! ## The invariant -/

section Invariant

variable {Ty : Type}

/-- The hosted rows: the alternative's row and the equation rows. -/
abbrev hostedRows (P : SourceLanguage.Program κ Γ star Ty) (a : ℕ) : Finset ℕ :=
  insert a (Finset.range P.equations.length)

/-- **A state represents an alternative beside other rows.** -/
structure Beside (P : SourceLanguage.Program κ Γ star Ty) (n : ℕ) (b : Branch κ Γ star Ty) (w : HostState S)
    (a : ℕ) (others : Finset ℕ) : Prop where
  hosted : Represents N P n b (restrict w (hostedRows P a)) a
  present : w.present = hostedRows P a ∪ others
  apart : Disjoint (hostedRows P a) others

variable {P : SourceLanguage.Program κ Γ star Ty}

/-- **Beside no row, the invariant is the representation.** -/
theorem beside_empty {n : ℕ} {b : Branch κ Γ star Ty} {w : HostState S} {a : ℕ} :
    Beside N P n b w a ∅ ↔ Represents N P n b w a := by
  constructor
  · intro beside
    have same : restrict w (hostedRows P a) = w := by
      obtain ⟨frame, knowledge, present, label⟩ := w
      have h := beside.present
      simp only [Finset.union_empty] at h
      subst h
      rfl
    rw [← same]
    exact beside.hosted
  · intro rep
    have same : restrict w (hostedRows P a) = w := by
      obtain ⟨frame, knowledge, present, label⟩ := w
      have h := rep.present
      simp only at h
      subst h
      rfl
    exact ⟨by rw [same]; exact rep, by rw [Finset.union_empty]; exact rep.present,
      Finset.disjoint_empty_right _⟩

theorem Beside.rows_sub {n : ℕ} {b : Branch κ Γ star Ty} {w : HostState S} {a : ℕ} {others : Finset ℕ}
    (beside : Beside N P n b w a others) : hostedRows P a ⊆ w.present := by
  rw [beside.present]
  exact Finset.subset_union_left

theorem Beside.row_present {n : ℕ} {b : Branch κ Γ star Ty} {w : HostState S} {a : ℕ} {others : Finset ℕ}
    (beside : Beside N P n b w a others) : a ∈ w.present :=
  beside.rows_sub N (Finset.mem_insert_self _ _)

theorem Beside.row_not_other {n : ℕ} {b : Branch κ Γ star Ty} {w : HostState S} {a : ℕ} {others : Finset ℕ}
    (beside : Beside N P n b w a others) : a ∉ others :=
  fun inside => Finset.disjoint_left.mp beside.apart (Finset.mem_insert_self _ _) inside

theorem Beside.mono {n n' : ℕ} {b : Branch κ Γ star Ty} {w : HostState S} {a : ℕ} {others : Finset ℕ}
    (beside : Beside N P n b w a others) (le : n ≤ n') : Beside N P n' b w a others :=
  ⟨⟨beside.hosted.notRow, beside.hosted.present, beside.hosted.reads, beside.hosted.rows,
    beside.hosted.independent, beside.hosted.fresh.mono le, beside.hosted.noPending⟩,
    beside.present, beside.apart⟩

/-- **No other row matches the call**: no solution of the knowledge reads the alternative's row as a
call of `x` and another row as the equation row `eqn(x)`. -/
def NoMatchingRow (w : HostState S) (a : ℕ) (others : Finset ℕ) : Prop :=
  ∀ o ∈ others, ∀ (B : Interface.Frames.Frame S) (σ : Assignment w.frame.arity B.arity),
    (Interface.Frames.contextual S).Models σ w.knowledge → ∀ x y : Term (signature S B.arity) Γ star,
      instantiateObservation σ (w.label a) = observe (altN N (evalN N (applyN N x)) y) →
        instantiateObservation σ (w.label o) ≠ observe (eqnN N x)

/-- Rows that never read as an equation row match no call. -/
theorem noMatchingRow_of_neverReads {w : HostState S} {a : ℕ} {others : Finset ℕ}
    (quiet : NeverReads (IsEquationRow N) w others) : NoMatchingRow N w a others :=
  fun o inside B σ known x _ _ same => quiet o inside B σ known ⟨x, same⟩

end Invariant

/-! ## Every rule of a translation is absence-only -/

section Rules

variable {Ty : Type} {P : SourceLanguage.Program κ Γ star Ty}

theorem translate_absenceOnly {r : RuleSyntax.Rule (RuleSyntax.Contextual.Terms S)}
    (member : r ∈ translate N P) : AbsenceOnly r := by
  classical
  by_cases unmatched : r = unmatchedRule N
  · subst unmatched
    exact ⟨fun c inside => .inr ⟨_, List.mem_singleton.mp inside⟩, rfl⟩
  · exact absenceOnly_of_positive (positive_of_ne_unmatched N member unmatched)

/-- **Every firing of the translated program beside other rows takes the alternative's row**, when the
other rows never read as `alt(…)`: the equation rows read as `eqn(…)`. -/
theorem beside_takes {n : ℕ} {b : Branch κ Γ star Ty} {w : HostState S} {a : ℕ} {others : Finset ℕ}
    (beside : Beside N P n b w a others) (quiet : NeverReads (IsAlternative N) w others)
    {f : RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations S) (translate N P) w.frame}
    (admitted : f.Admits (Interface.Frames.contextual S) w) :
    ∃ a', f.selection.taken = [a] ∧ f.selection.read = [] ∧ f.selection.made = [a'] ∧ a' ∉ w.present := by
  obtain ⟨pat, out, simpleRule, altHead⟩ := Alternatives.translate_simple N f.member
  obtain ⟨shapes, enabled, solvable, _⟩ := admitted
  obtain ⟨_, _, _, takeLen, readLen, prodLen, _⟩ := shapes
  rw [simpleRule.take] at takeLen
  rw [simpleRule.noRead] at readLen
  rw [simpleRule.produce] at prodLen
  obtain ⟨o, taken⟩ := List.length_eq_one_iff.mp takeLen.symm
  obtain ⟨o', made⟩ := List.length_eq_one_iff.mp prodLen.symm
  have read : f.selection.read = [] := List.eq_nil_of_length_eq_zero readLen.symm
  have simple : Simple f o o' pat out := ⟨taken, read, made, simpleRule.take, simpleRule.noRead, simpleRule.produce⟩
  have oPresent : o ∈ w.present := enabled.taken_subset (by simp [Selection.commit, taken])
  have o'Fresh : o' ∉ w.present := by
    intro inside
    exact Finset.disjoint_left.mp enabled.fresh (by simp [Selection.commit, made]) inside
  obtain ⟨B, u, solved⟩ := solvable
  obtain ⟨known, _, matched⟩ := simple_restrict simple u solved
  obtain ⟨x, y, headed⟩ := altHead (Assignment.compose u f.opening)
  have isAlt : o = a := by
    rw [beside.present, Finset.mem_union, Finset.mem_insert, Finset.mem_range] at oPresent
    rcases oPresent with (same | small) | other
    · exact same
    · obtain ⟨θ, row⟩ := beside.hosted.rows B _ known o small
      have same := matched.trans row
      rw [headed] at same
      exact absurd (N.tag_eq (observe_injective same)) (by decide)
    · exact absurd ⟨x, y, matched.symm.trans headed⟩ (quiet o other B _ known)
  subst isAlt
  exact ⟨o', taken, read, made, o'Fresh⟩

end Rules

/-! ## Firing a rule at a state beside other rows -/

section Fire

variable {Ty : Type} {P : SourceLanguage.Program κ Γ star Ty}

/-- The rows after a firing that takes the alternative's row and makes one row. -/
theorem present_after {n : ℕ} {b : Branch κ Γ star Ty} {w : HostState S} {a a' : ℕ} {others : Finset ℕ}
    (beside : Beside N P n b w a others)
    {f : RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations S) (translate N P) w.frame}
    (taken : f.selection.taken = [a]) (made : f.selection.made = [a']) :
    (f.result (Interface.Frames.contextual S) w).present = hostedRows P a' ∪ others := by
  have aNotRow : ¬ a < P.equations.length := not_lt.mpr beside.hosted.notRow
  have aNotOther := beside.row_not_other N
  change fire w.present (f.selection.commit (T := Unit)) = _
  rw [beside.present]
  ext i
  simp only [fire, Selection.commit, taken, made, List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
    Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_insert, Finset.mem_range]
  constructor
  · rintro (⟨(same | small) | inO, other⟩ | same)
    · exact absurd same other
    · exact .inl (.inr small)
    · exact .inr inO
    · exact .inl (.inl same)
  · rintro ((same | small) | inO)
    · exact .inr same
    · exact .inl ⟨.inl (.inr small), fun same => aNotRow (same ▸ small)⟩
    · exact .inl ⟨.inr inO, fun same => aNotOther (same ▸ inO)⟩

/-- **After a firing that takes the alternative's row and makes a new one, the state is beside the
same rows**, once the state with fewer rows represents the next alternative. -/
theorem beside_after {n n' : ℕ} {b b' : Branch κ Γ star Ty} {w : HostState S} {a a' : ℕ} {others : Finset ℕ}
    (beside : Beside N P n b w a others)
    {f : RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations S) (translate N P) w.frame}
    (taken : f.selection.taken = [a]) (made : f.selection.made = [a']) (fresh : a' ∉ w.present)
    (rep : Represents N P n' b'
      (RuleSyntax.Firing.result (Interface.Frames.contextual S) (restrict w (hostedRows P a)) f) a') :
    Beside N P n' b' (f.result (Interface.Frames.contextual S) w) a' others := by
  refine ⟨?_, present_after N beside taken made, ?_⟩
  · rw [show restrict (f.result (Interface.Frames.contextual S) w) (hostedRows P a') = _ from
      restrict_result (Interface.Frames.contextual S) rep.present]
    exact rep
  · rw [Finset.disjoint_left]
    intro i inH inO
    rw [Finset.mem_insert, Finset.mem_range] at inH
    rcases inH with same | small
    · subst same
      exact fresh (by rw [beside.present]; exact Finset.mem_union_right _ inO)
    · exact Finset.disjoint_left.mp beside.apart (Finset.mem_insert_of_mem (Finset.mem_range.mpr small)) inO

/-- **Firing a rule beside other rows**: if the rule transforms the alternative's readings into a live
alternative's readings, its canonical firing at the state is admitted (given its guard there), the
result represents that alternative beside the same rows, and what the other rows never read as, they
still never read as. -/
theorem fire_beside {r : RuleSyntax.Rule (RuleSyntax.Contextual.Terms S)} (member : r ∈ translate N P)
    {pat out : Observation S r.locals.arity} (htake : r.body.take = [pat]) (hread : r.body.read = [])
    (hprod : r.body.produce = [out]) (hcollect : r.collect = [])
    {n n' : ℕ} {b b' : Branch κ Γ star Ty} {w : HostState S} {a : ℕ} {others : Finset ℕ}
    (beside : Beside N P n b w a others)
    (transfer : ∀ (B : Interface.Frames.Frame S) (q : Observation S B.arity),
      (∃ h : Assignment r.locals.arity B.arity, branchReads N b B (instantiateObservation h pat) ∧
        (Interface.Frames.contextual S).Models h r.body.tell ∧ instantiateObservation h out = q) ↔
      branchReads N b' B q)
    (live : Solvable b'.store)
    (guard : (Interface.Frames.contextual S).Entails
      ((canonicalAt w r member a).information (Interface.Frames.contextual S) w)
      (fun _ σ => (canonicalAt w r member a).Holds (Interface.Frames.contextual S) w σ))
    (fresh : BranchBelow n' b') (noPending : b'.pending = []) :
    ∃ w' a', Fires N P w w' ∧ Beside N P n' b' w' a' others ∧
      ∀ shape : ∀ B : Interface.Frames.Frame S, Observation S B.arity → Prop,
        NeverReads shape w others → NeverReads shape w' others := by
  have simple := canonical_simple (s := w) (member := member) (a := a) htake hread hprod
  have shapes := canonical_shapes (s := w) (member := member) (a := a) htake hread hprod hcollect
  have aPresent := beside.row_present N
  have solvable : (Interface.Frames.contextual S).Solvable
      ((canonicalAt w r member a).information (Interface.Frames.contextual S) w) := by
    obtain ⟨W, target, σ, solved⟩ := live
    have reads : branchReads N b' ⟨W, target⟩ (observe (encBranch N (instantiate σ) b')) := ⟨σ, solved, rfl⟩
    obtain ⟨h, readsB, told, _⟩ := (transfer _ _).mpr reads
    obtain ⟨g, known, matched⟩ := (beside.hosted.reads _ _).mpr readsB
    obtain ⟨u, solvedU, _⟩ := simple_amalgamate simple shapes.1 aPresent g h known told matched.symm
    exact ⟨_, u, solvedU⟩
  have madeFresh : freshId w ∉ (restrict w (hostedRows P a)).present :=
    fun inside => freshId_not_mem w (beside.rows_sub N inside)
  have simpleH : Simple (s := restrict w (hostedRows P a)) (canonicalAt w r member a) a (freshId w) pat out :=
    ⟨simple.taken, simple.noRead, simple.madeOne, simple.take, simple.noReadPattern, simple.produce⟩
  have rep := represents_after N (s := restrict w (hostedRows P a)) (f := canonicalAt w r member a)
    beside.hosted simpleH
    ⟨fresh_restrict (Interface.Frames.contextual S) (beside.rows_sub N) shapes.1, shapes.2⟩ madeFresh
    transfer fresh noPending
  refine ⟨_, freshId w,
    ⟨canonicalAt w r member a, ⟨shapes, enabled_single aPresent (freshId_not_mem w), solvable, guard⟩, rfl⟩,
    beside_after N beside rfl rfl (freshId_not_mem w) rep, ?_⟩
  intro shape quiet
  refine neverReads_after (canonicalAt w r member a) quiet ?_
  intro o inside isMade
  have same : o = freshId w := List.mem_singleton.mp isMade
  subst same
  exact freshId_not_mem w (by rw [beside.present]; exact Finset.mem_union_right _ inside)

/-- **The guard of the unmatched call beside other rows**: when no equation of the program matches the
call and no other row matches it, the absence check of the canonical unmatched firing holds at every
solution of its information. -/
theorem unmatched_guard_beside {n : ℕ} {K : List (Constraint κ Γ star)} {t : Data κ Γ star}
    {fs : List (SourceLanguage.Frame κ Γ star Ty)} {ps : List (Data κ Γ star × Comp κ Γ star Ty)}
    {w : HostState S} {a : ℕ} {others : Finset ℕ}
    (beside : Beside N P n ⟨K, .eval (.apply t), fs, ps⟩ w a others)
    (none : ∀ e ∈ P.equations, ¬ Solvable (K ++ [(instantiate (copyAt κ n) e.lhs, t)]))
    (noRow : NoMatchingRow N w a others) :
    (Interface.Frames.contextual S).Entails
      ((canonicalAt w (unmatchedRule N) (unmatchedRule_mem N P) a).information (Interface.Frames.contextual S) w)
      (fun _ σ => (canonicalAt w (unmatchedRule N) (unmatchedRule_mem N P) a).Holds
        (Interface.Frames.contextual S) w σ) := by
  have simple := canonical_simple (s := w) (r := unmatchedRule N) (member := unmatchedRule_mem N P) (a := a)
    (pat := observe (altN N (evalN N (applyN N (unk .datum))) (unk .stack)))
    (out := observe (altN N (valueN N (unk .datum)) (unk .stack))) rfl rfl rfl
  intro B u solved
  obtain ⟨checksH, _⟩ := unmatched_guard N beside.hosted none B u solved
  refine ⟨?_, ?_⟩
  · intro c member
    have atH := checksH c member
    change c ∈ [Check.predicate .none (instantiateObservation
      (canonicalAt w (unmatchedRule N) (unmatchedRule_mem N P) a).opening (unmatchedCheck N))] at member
    rw [List.mem_singleton] at member
    subst member
    intro o present equal
    rw [beside.present, Finset.mem_union] at present
    rcases present with inH | inO
    · exact atH o inH equal
    · obtain ⟨known, _, matched⟩ := simple_restrict simple u solved
      change instantiateObservation u (instantiateObservation _ (unmatchedCheck N)) =
        instantiateObservation u (instantiateObservation _ (w.label o)) at equal
      rw [instantiateObservation_comp, instantiateObservation_comp] at equal
      refine noRow o inO B _ known
        (instantiate (Assignment.compose u (canonicalAt w (unmatchedRule N) (unmatchedRule_mem N P) a).opening)
          (unk .datum))
        (instantiate (Assignment.compose u (canonicalAt w (unmatchedRule N) (unmatchedRule_mem N P) a).opening)
          (unk .stack)) ?_ ?_
      · rw [← matched]
        change observe (instantiate _ (altN N (evalN N (applyN N (unk .datum))) (unk .stack))) = _
        rw [instantiate_altN, instantiate_evalN, instantiate_applyN]
      · rw [← equal]
        change observe (instantiate _ (eqnN N (unk .datum))) = _
        rw [instantiate_eqnN]
        rfl
  · intro q member
    have empty : (canonicalAt w (unmatchedRule N) (unmatchedRule_mem N P) a).collectOpened
        (Interface.Frames.contextual S) = [] := rfl
    rw [empty] at member
    simp at member

/-- **At a call that no equation matches, the only rule that fires is the unmatched call's.** -/
theorem unmatched_rule_of_admitted {n : ℕ} {K : List (Constraint κ Γ star)} {t : Data κ Γ star}
    {fs : List (SourceLanguage.Frame κ Γ star Ty)} {ps : List (Data κ Γ star × Comp κ Γ star Ty)}
    {s : HostState S} {a : ℕ} (rep : Represents N P n ⟨K, .eval (.apply t), fs, ps⟩ s a)
    (none : ∀ e ∈ P.equations, ¬ Solvable (K ++ [(instantiate (copyAt κ n) e.lhs, t)]))
    {f : RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations S) (translate N P) s.frame}
    (admitted : f.Admits (Interface.Frames.contextual S) s) : f.rule = unmatchedRule N := by
  obtain ⟨rule, member, ext, opening, selection, seen⟩ := f
  rcases (mem_translate N).mp member with control | ⟨e, eMember, rfl⟩
  · rcases (mem_controlRules N).mp control with rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨_, _, _, B, h, reads, _⟩ := admitted_takes_alternative N rep admitted rfl rfl rfl
        (fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩)
      obtain ⟨_, focus⟩ := shape_ret N reads
      cases focus
    · rfl
    · obtain ⟨_, _, _, B, h, reads, _⟩ := admitted_takes_alternative N rep admitted rfl rfl rfl
        (fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩)
      obtain ⟨_, _, focus⟩ := shape_choice N reads
      cases focus
    · obtain ⟨_, _, _, B, h, reads, _⟩ := admitted_takes_alternative N rep admitted rfl rfl rfl
        (fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩)
      obtain ⟨_, _, focus⟩ := shape_choice N reads
      cases focus
    · obtain ⟨_, _, _, B, h, reads, _⟩ := admitted_takes_alternative N rep admitted rfl rfl rfl
        (fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩)
      obtain ⟨_, _, _, _, focus⟩ := shape_bindStart N reads
      cases focus
    · obtain ⟨_, _, _, B, h, reads, _⟩ := admitted_takes_alternative N rep admitted rfl rfl rfl
        (fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩)
      change branchReads N _ B (observe (instantiate h _)) at reads
      rw [instantiate_altN, instantiate_valueN] at reads
      obtain ⟨σ, _, same⟩ := (branchReads_observe N).mp reads
      obtain ⟨onFocus, _⟩ := alt_eq_encAlt N (instantiate σ) same.symm
      obtain ⟨_, focus, _⟩ := value_eq_encFocus N (instantiate σ) onFocus
      cases focus
  · obtain ⟨_, _, _, B, h, reads, _⟩ := admitted_takes_alternative N rep admitted rfl rfl rfl
      (fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩)
    change branchReads N _ B (observe (instantiate h _)) at reads
    rw [instantiate_altN, instantiate_evalN, instantiate_applyN, instantiate_asUnknowns] at reads
    obtain ⟨t', σ, focus, solved, onCall⟩ := shape_apply N reads
    simp only [Focus.eval.injEq, Comp.apply.injEq] at focus
    subst focus
    exact absurd ((solvable_copy_iff e.lhs rep.fresh.1
      (rep.fresh.2.1 t (by simp [focusData, Comp.data]))).mpr ⟨_, _, σ, _, solved, onCall.symm⟩)
      (none e eMember)

/-- **The unmatched call beside other rows, exactly.** A live alternative at a call that no equation of
the program matches, beside rows that never read as alternatives' rows, has a firing of the translated
program **exactly when no other row matches the call at any solution of the knowledge**
(`NoMatchingRow`). One row that matches the call at one solution switches it off; a row that matches it
at no solution does not, whatever it is. Whether a row matches depends on the unknowns it shares with
the call: an unknown of the row that the call does not mention is read as the match needs, one that the
call mentions is read as in the call (`Composition.UnmatchedControls.private_row_stuck`,
`Composition.UnmatchedControls.shared_row_fires`). -/
theorem unmatched_beside_iff {n : ℕ} {K : List (Constraint κ Γ star)} {t : Data κ Γ star}
    {fs : List (SourceLanguage.Frame κ Γ star Ty)} {ps : List (Data κ Γ star × Comp κ Γ star Ty)}
    {w : HostState S} {a : ℕ} {others : Finset ℕ}
    (beside : Beside N P n ⟨K, .eval (.apply t), fs, ps⟩ w a others)
    (quiet : NeverReads (IsAlternative N) w others)
    (none : ∀ e ∈ P.equations, ¬ Solvable (K ++ [(instantiate (copyAt κ n) e.lhs, t)])) (live : Solvable K) :
    (∃ w', Fires N P w w') ↔ NoMatchingRow N w a others := by
  constructor
  · rintro ⟨_, f, admitted, _⟩
    obtain ⟨a₁, taken, read, made, _⟩ := beside_takes N beside quiet admitted
    have selected : ∀ o, o ∈ f.selection.taken ∨ o ∈ f.selection.read → o ∈ hostedRows P a := by
      intro o inside
      rw [taken, read] at inside
      rcases inside with one | none'
      · rw [List.mem_singleton.mp one]
        exact Finset.mem_insert_self _ _
      · cases none'
    have admittedH := admits_restrict (Interface.Frames.contextual S) (beside.rows_sub N)
      (translate_absenceOnly N f.member) selected admitted
    have ruleEq := unmatched_rule_of_admitted N beside.hosted none admittedH
    obtain ⟨rule, member, ext, opening, selection, seen⟩ := f
    simp only at ruleEq taken read made
    subst ruleEq
    have simple : Simple (⟨unmatchedRule N, member, ext, opening, selection, seen⟩ :
        RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations S) (translate N P) w.frame) a a₁
        (observe (altN N (evalN N (applyN N (unk .datum))) (unk .stack)))
        (observe (altN N (valueN N (unk .datum)) (unk .stack))) := ⟨taken, read, made, rfl, rfl, rfl⟩
    intro o inO B σ known x y readsA sameRow
    have oPresent : o ∈ w.present := by rw [beside.present]; exact Finset.mem_union_right _ inO
    let h : Assignment (unknownArity Γ star) B.arity := fill x x x x y
    have matchedH : instantiateObservation h (observe (altN N (evalN N (applyN N (unk .datum))) (unk .stack))) =
        instantiateObservation σ (w.label a) := by
      rw [readsA]
      change observe (instantiate h _) = _
      rw [instantiate_altN, instantiate_evalN, instantiate_applyN, instantiate_unk, instantiate_unk]
      rfl
    obtain ⟨u, solvedU, _, onRows, onTerms⟩ :=
      simple_amalgamate simple admitted.1.1 (beside.row_present N) σ h known (fun _ inside => by cases inside)
        matchedH
    have holds := (admitted.2.2.2 B u solvedU).1
    have checkMember : (RuleSyntax.Firing.opened (Interface.Frames.contextual S)
        (⟨unmatchedRule N, member, ext, opening, selection, seen⟩ :
          RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations S) (translate N P) w.frame)).checks =
        [.predicate .none (instantiateObservation opening (unmatchedCheck N))] := rfl
    have absent := holds _ (by rw [checkMember]; exact List.mem_singleton_self _)
    apply absent o oPresent
    change instantiateObservation u (instantiateObservation opening (unmatchedCheck N)) =
      instantiateObservation u (RuleSyntax.Firing.row (Interface.Frames.contextual S) w _ o)
    rw [onTerms _ (by simp [RuleSyntax.Rule.terms, unmatchedRule, RuleSyntax.checkTerms]),
      onRows o oPresent, sameRow]
    change observe (instantiate h (eqnN N (unk .datum))) = _
    rw [instantiate_eqnN, instantiate_unk]
    rfl
  · intro noRow
    obtain ⟨w', _, fires, _⟩ := fire_beside N (unmatchedRule_mem N P) rfl rfl rfl rfl beside
      (fun B q => transfer_unmatched N rfl q) live (unmatched_guard_beside N beside none noRow)
      (branchBelow_focus beside.hosted.fresh rfl rfl (by simp [focusData, Comp.data])) beside.hosted.noPending
    exact ⟨w', fires⟩

end Fire

/-! ## Simulation and reflection beside other rows -/

section Steps

variable {D : Discipline S Γ star} {P : SourceLanguage.Program κ Γ star D.Ty} {supply : ℕ → Term S Γ star}

/-- **Simulation beside other rows**: one firing for each live alternative a source move makes. At a
call that no equation matches, and only there, no other row may match the call. -/
theorem simulation_beside (arrowP : ArrowProgram P) {v v' : World κ Γ star} {b : Branch κ Γ star D.Ty}
    {bs : Multiset (Branch κ Γ star D.Ty)} (move : Move D P supply v b v' bs)
    {w : HostState S} {a : ℕ} {others : Finset ℕ} (beside : Beside N P v.scope b w a others)
    (arrow : ArrowBranch b) (hygienic : Hygienic b)
    (noRow : ∀ t, b.focus = .eval (.apply t) →
      (∀ e ∈ P.equations, ¬ Solvable (b.store ++ [(instantiate (copyAt κ v.scope) e.lhs, t)])) →
        NoMatchingRow N w a others)
    {b' : Branch κ Γ star D.Ty} (child : b' ∈ bs) (live : Solvable b'.store) :
    ∃ w' a', Fires N P w w' ∧ Beside N P v'.scope b' w' a' others ∧
      (∀ shape : ∀ B : Interface.Frames.Frame S, Observation S B.arity → Prop,
        NeverReads shape w others → NeverReads shape w' others) ∧ ArrowBranch b' := by
  have rep := beside.hosted
  obtain ⟨frames, shape⟩ := arrow
  cases move
  case ret K t fs ps =>
    rw [Multiset.mem_singleton] at child
    subst child
    obtain ⟨w', a', fires, beside', kept⟩ := fire_beside N (retRule_mem N P) rfl rfl rfl rfl beside
      (fun B q => transfer_ret N rfl q) live (entails_of_no_checks rfl rfl)
      (branchBelow_focus rep.fresh rfl rfl (by simp [focusData, Comp.data])) rep.noPending
    exact ⟨w', a', fires, beside', kept,frames, .inr ⟨t, rfl⟩⟩
  case apply K t fs ps matched =>
    obtain ⟨e, eMember, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp child)
    obtain ⟨w', a', fires, beside', kept⟩ := fire_beside N (schema_mem N P eMember) rfl rfl rfl rfl beside
      (fun B q => transfer_schema N e rfl rep.fresh q) live (entails_of_no_checks rfl rfl)
      (branchBelow_call rep.fresh e) rep.noPending
    exact ⟨w', a', fires, beside', kept,frames, .inl ⟨_, rfl, arrowComp_mapData _ _ (arrowP e eMember)⟩⟩
  case unmatched K t fs ps none =>
    rw [Multiset.mem_singleton] at child
    subst child
    obtain ⟨w', a', fires, beside', kept⟩ := fire_beside N (unmatchedRule_mem N P) rfl rfl rfl rfl beside
      (fun B q => transfer_unmatched N rfl q) live (unmatched_guard_beside N beside none (noRow t rfl none))
      (branchBelow_focus rep.fresh rfl rfl (by simp [focusData, Comp.data])) rep.noPending
    exact ⟨w', a', fires, beside', kept,frames, .inr ⟨t, rfl⟩⟩
  case choice K c d fs ps =>
    have arrowCD : ArrowComp c ∧ ArrowComp d := arrow_eval shape
    rcases Multiset.mem_cons.mp child with rfl | other
    · obtain ⟨w', a', fires, beside', kept⟩ := fire_beside N (choiceLeftRule_mem N P) rfl rfl rfl rfl beside
        (fun B q => transfer_choiceLeft N rfl q) live (entails_of_no_checks rfl rfl)
        (branchBelow_focus rep.fresh rfl rfl
          (fun t' member => by simp only [focusData, Comp.data] at member ⊢; exact List.mem_append_left _ member))
        rep.noPending
      exact ⟨w', a', fires, beside', kept,frames, .inl ⟨c, rfl, arrowCD.1⟩⟩
    · rw [Multiset.mem_singleton] at other
      subst other
      obtain ⟨w', a', fires, beside', kept⟩ := fire_beside N (choiceRightRule_mem N P) rfl rfl rfl rfl beside
        (fun B q => transfer_choiceRight N rfl q) live (entails_of_no_checks rfl rfl)
        (branchBelow_focus rep.fresh rfl rfl
          (fun t' member => by simp only [focusData, Comp.data] at member ⊢; exact List.mem_append_right _ member))
        rep.noPending
      exact ⟨w', a', fires, beside', kept,frames, .inl ⟨d, rfl, arrowCD.2⟩⟩
  case fail K fs ps =>
    simp at child
  case letStart K s₁ p c k fs ps =>
    rw [Multiset.mem_singleton] at child
    subst child
    have arrowCK : ArrowComp c ∧ ArrowComp k := arrow_eval shape
    obtain ⟨w', a', fires, beside', kept⟩ := fire_beside N (bindStartRule_mem N P) rfl rfl rfl rfl beside
      (fun _ q => transfer_bindStart N rfl q) live (entails_of_no_checks rfl rfl)
      (branchBelow_letStart rep.fresh) rep.noPending
    exact ⟨w', a', fires, beside', kept,⟨arrowCK.2, frames⟩, .inl ⟨c, rfl, arrowCK.1⟩⟩
  case letBind K val s₁ p k fs ps =>
    rw [Multiset.mem_singleton] at child
    subst child
    obtain ⟨w', a', fires, beside', kept⟩ := fire_beside N (bindValueRule_mem N P) rfl rfl rfl rfl beside
      (fun _ q => transfer_bindValue N rep.fresh (hygienic K val s₁ p k fs ps rfl) q) live
      (entails_of_no_checks rfl rfl) (branchBelow_letBind rep.fresh) rep.noPending
    exact ⟨w', a', fires, beside', kept,frames.2, .inl ⟨_, rfl, arrowComp_mapData _ _ frames.1⟩⟩
  all_goals first
    | exact False.elim (arrow_eval shape)
    | exact False.elim frames

/-- **Reflection beside other rows**: every firing of the translated program at a state that
represents an alternative beside rows that never read as alternatives' rows is a source move of that
alternative, and what the rows never read as, they still never read as at the state reached. It is
`reflection_arrows` at the state with fewer rows. -/
theorem reflection_beside (arrowP : ArrowProgram P) {v : World κ Γ star} {b : Branch κ Γ star D.Ty}
    {w w' : HostState S} {a : ℕ} {others : Finset ℕ} (beside : Beside N P v.scope b w a others)
    (quiet : NeverReads (IsAlternative N) w others)
    (arrow : ArrowBranch b) (hygienic : Hygienic b) (fires : Fires N P w w') :
    ∃ v' bs b' a', Move D P supply v b v' bs ∧ b' ∈ bs ∧ Beside N P v'.scope b' w' a' others ∧
      (∀ shape : ∀ B : Interface.Frames.Frame S, Observation S B.arity → Prop,
        NeverReads shape w others → NeverReads shape w' others) ∧ ArrowBranch b' := by
  obtain ⟨f, admitted, rfl⟩ := fires
  obtain ⟨a₁, taken, read, made, fresh⟩ := beside_takes N beside quiet admitted
  have notMade : ∀ o ∈ others, o ∉ f.selection.made := by
    intro o inside isMade
    rw [made, List.mem_singleton] at isMade
    subst isMade
    exact fresh (by rw [beside.present]; exact Finset.mem_union_right _ inside)
  have selected : ∀ o, o ∈ f.selection.taken ∨ o ∈ f.selection.read → o ∈ hostedRows P a := by
    intro o inside
    rw [taken, read] at inside
    rcases inside with one | none
    · rw [List.mem_singleton.mp one]
      exact Finset.mem_insert_self _ _
    · cases none
  have admittedH := admits_restrict (Interface.Frames.contextual S) (beside.rows_sub N)
    (translate_absenceOnly N f.member) selected admitted
  obtain ⟨v', bs, b', a', move, child, rep', arrow'⟩ :=
    reflection_arrows N (supply := supply) arrowP beside.hosted arrow hygienic ⟨f, admittedH, rfl⟩
  have sameRow : a' = a₁ := by
    have inside : a' ∈ (RuleSyntax.Firing.result (Interface.Frames.contextual S)
        (restrict w (hostedRows P a)) f).present := by
      rw [rep'.present]
      exact Finset.mem_insert_self _ _
    change a' ∈ fire (hostedRows P a) (f.selection.commit (T := Unit)) at inside
    rcases mem_fire.mp inside with ⟨old, notTaken⟩ | isMade
    · rw [Finset.mem_insert, Finset.mem_range] at old
      rcases old with same | small
      · exact absurd (by simp [Selection.commit, taken, same]) notTaken
      · exact absurd small (not_lt.mpr rep'.notRow)
    · simpa [Selection.commit, made] using isMade
  subst sameRow
  exact ⟨v', bs, b', a', move, child, beside_after N beside taken made fresh rep',
    fun _ never => neverReads_after f never notMade, arrow'⟩

/-- A state with a firing beside other rows represents a live alternative. -/
theorem live_beside {n : ℕ} {b : Branch κ Γ star D.Ty} {w w' : HostState S} {a : ℕ} {others : Finset ℕ}
    (beside : Beside N P n b w a others) (fires : Fires N P w w') : Solvable b.store := by
  obtain ⟨f, admitted, _⟩ := fires
  obtain ⟨B, u, solved⟩ := admitted.2.2.1
  have known := RuleSyntax.Firing.knowledge_solved (X := Interface.Frames.contextual S) f solved
  obtain ⟨σ, solvedσ, _⟩ := (beside.hosted.reads B _).mp ⟨_, known, rfl⟩
  exact ⟨B.Names, B.arity, σ, solvedσ⟩

end Steps

#print axioms neverReads_after
#print axioms beside_empty
#print axioms translate_absenceOnly
#print axioms beside_takes
#print axioms beside_after
#print axioms fire_beside
#print axioms unmatched_guard_beside
#print axioms unmatched_rule_of_admitted
#print axioms unmatched_beside_iff
#print axioms simulation_beside
#print axioms reflection_beside
#print axioms live_beside

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition
