import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic.Firings
import Mettapedia.GSLT.Core.OperationalReadback

/-!
# Runs of any length: the step on states that read as bags of rows is rewriting by matching

The step is `RuleSyntax.step` at one frame over rows with unknowns (`Presentation.Schematic.schematicStep`).
`Presentation.Schematic.Firings` proves, at a state whose labels are ground rows and whose knowledge is
trivial, that the admitted firings are the firings by matching, and that a result is ground only modulo its
knowledge. Such states are not closed under the step: a result carries opened unknowns that its knowledge
binds. This module states the same correspondence on a class of states that is closed, so it holds along runs
of every length.

## The relation

* **A state reads as rows** (`Reads s rows`): its knowledge is solvable, and every solution reads each present
  label as the row of its identity. **A state reads as a bag** (`ReadsBag s bag`): it reads as rows whose bag
  over the present identities is the given one.
* It is the tree's `ReadsAs` with solvable knowledge (`readsBag_iff`): a principal solution of the knowledge
  reads every present label as a ground row, and every solution factors through it.
* Ground labels with trivial knowledge are an instance (`reads_of_ground`).

## Rewriting by matching

`Rewrites rules bag bag'`: a rule of the list, a ground instantiation `θ` of its unknowns and a rest such that
the instances of the takes beside the rest are the bag, each instance of a read is a row of the rest, the
instances of the two sides of each tell and equation guard are equal, and `bag'` is the instances of the made
rows beside the rest. This is `Presentation.Schematic.MatchFires` on bags, with its result.

## The correspondence, for range-restricted positive programs

* `rewrite_of_admitted`, `readsBag_backward`: **an admitted firing at a state that reads as a bag is one
  rewrite of the bag, and its result reads as the rewritten bag.** No other firing is admitted.
* `admitted_of_rewrite`, `readsBag_forward`: **every rewrite of the bag is an admitted firing whose result reads
  as the rewritten bag**, when identities are infinitely many. The opening renames the rule's unknowns beyond
  every unknown the state mentions (`shift (stateBound s)`, fresh: `shift_fresh_of_bound`).
* `correspondence`: the two directions as one `OperationalCorrespondence` from rewriting of bags
  (`rewriting rules`) to the step of the program (`stepSystem O rules`), related by `ReadsBag`. One rewrite is
  one firing in each direction; no firing is silent. It composes with every other correspondence of the tree by
  `OperationalCorrespondence.comp`.

The firing that answers a rewrite is determined up to the choice of the made identities and of the fresh
opening: every admitted firing at a state that reads as `bag` leads to a state that reads as a rewrite of
`bag` (`readsBag_backward`), and a state with solvable knowledge reads as at most one bag
(`Presentation.Schematic.readsAs_unique`).

Every bag of rows is read from a state (`exists_reads`: the state of a list of rows, `listState`; for one row,
`rowState`), so the statements about every state that reads as a bag are about something.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines

open Mettapedia.Logic.LP
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis (equalityGSLT)
open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open OneFrame (frames ext)
open NamesOnTheStep (Expr)
open LogicOverTheStep.StepSpan (Succ)
open Presentation (exists_taken exists_read exists_fresh bagOf_split val_union_of_disjoint toFinset_val_of_nodup)
open Presentation.Schematic

universe uO

/-! ## Reading a state as rows -/

section Reading

variable {O : Type uO} {rules : List SRule}

/-- **A state reads as rows**: its knowledge is solvable, and every solution reads each present label as the
row of its identity. -/
structure Reads (s : SState O) (rows : O → Expr) : Prop where
  solvable : A.Consistent s.knowledge
  reads : ∀ σ : Subst rowSig, A.Models σ s.knowledge → ∀ o ∈ s.present, σ.applyTerm (s.label o) = toTerm (rows o)

/-- **A state reads as a bag of rows**: it reads as rows whose bag over the present identities is the bag. -/
def ReadsBag (s : SState O) (bag : Multiset Expr) : Prop :=
  ∃ rows : O → Expr, Reads s rows ∧ s.present.val.map rows = bag

/-- **Ground labels with trivial knowledge read as their rows.** -/
theorem reads_of_ground {s : SState O} {rows : O → Expr} (ground : GroundLabels s rows)
    (trivial : TrivialKnowledge s.knowledge) : Reads s rows :=
  ⟨⟨Subst.id rowSig, fun e member => by
      show Subst.applyTerm _ e.1 = Subst.applyTerm _ e.2
      rw [trivial e member]⟩,
    fun σ _ o present => by rw [ground o present, applyTerm_toTerm]⟩

/-- A state that reads as a bag has solvable knowledge and reads as the bag in the tree's sense. -/
theorem ReadsBag.readsAs {s : SState O} {bag : Multiset Expr} (reads : ReadsBag s bag) :
    A.Consistent s.knowledge ∧ ReadsAs s bag := by
  obtain ⟨rows, reads, rfl⟩ := reads
  refine ⟨reads.solvable, fun σ solved => ?_⟩
  rw [Multiset.map_map]
  exact Multiset.map_congr rfl fun o member => reads.reads σ solved o (Finset.mem_val.mp member)

/-- **With solvable knowledge, reading as a bag in the tree's sense is reading as rows**: a principal
solution of the knowledge reads every present label as a ground row, and every solution factors through it. -/
theorem readsBag_of_readsAs {s : SState O} {bag : Multiset Expr} (solvable : A.Consistent s.knowledge)
    (readsAs : ReadsAs s bag) : ReadsBag s bag := by
  obtain ⟨μ, accepted⟩ := (FirstOrder.accepted_iff_consistent (signature := rowSig) s.knowledge).mpr solvable
  have principal := FirstOrder.accepted_principal (signature := rowSig) s.knowledge μ accepted
  have atPrincipal := readsAs μ principal.sound
  have ground : ∀ o, ∃ e, o ∈ s.present → μ.applyTerm (s.label o) = toTerm e := by
    intro o
    by_cases present : o ∈ s.present
    · have inside : μ.applyTerm (s.label o) ∈ bag.map toTerm := by
        rw [← atPrincipal]
        exact Multiset.mem_map_of_mem _ (Finset.mem_val.mpr present)
      obtain ⟨e, -, same⟩ := Multiset.mem_map.mp inside
      exact ⟨e, fun _ => same.symm⟩
    · exact ⟨.sym 0, fun inside => absurd inside present⟩
  choose rows rowsSpec using ground
  refine ⟨rows, ⟨solvable, fun σ solved o present => ?_⟩, ?_⟩
  · obtain ⟨residual, factors⟩ := principal.factors σ solved
    have through : σ.applyTerm (s.label o) = (residual.comp μ).applyTerm (s.label o) := factors (s.label o)
    rw [through, Subst.applyTerm_comp, rowsSpec o present, applyTerm_toTerm]
  · apply Multiset.map_injective toTerm_injective
    rw [← atPrincipal, Multiset.map_map]
    exact Multiset.map_congr rfl fun o member => (rowsSpec o (Finset.mem_val.mp member)).symm

/-- **Reading as a bag is the tree's `ReadsAs` with solvable knowledge.** -/
theorem readsBag_iff {s : SState O} {bag : Multiset Expr} :
    ReadsBag s bag ↔ A.Consistent s.knowledge ∧ ReadsAs s bag :=
  ⟨ReadsBag.readsAs, fun both => readsBag_of_readsAs both.1 both.2⟩

/-! ## An opening beyond every unknown the state mentions -/

/-- **A bound beyond every unknown a state mentions**, in its knowledge and in its present labels. -/
def stateBound (s : SState O) : ℕ :=
  knowledgeBound s.knowledge + s.present.sup (fun o => (Term.freeVars (σ := rowSig) (s.label o)).sup id + 1)

theorem lt_stateBound {s : SState O} {t : Tm} (mentioned : s.Mentions t) {v : ℕ}
    (vars : v ∈ Term.freeVars (σ := rowSig) t) : v < stateBound s := by
  unfold stateBound
  rcases mentioned with inFirst | inSecond | ⟨o, present, rfl⟩
  · obtain ⟨e, member, rfl⟩ := List.mem_map.mp inFirst
    exact lt_of_lt_of_le (lt_knowledgeBound member (Or.inl vars)) (Nat.le_add_right _ _)
  · obtain ⟨e, member, rfl⟩ := List.mem_map.mp inSecond
    exact lt_of_lt_of_le (lt_knowledgeBound member (Or.inr vars)) (Nat.le_add_right _ _)
  · have inSup : v ≤ (Term.freeVars (σ := rowSig) (s.label o)).sup id := Finset.le_sup (f := id) vars
    have inAll : (Term.freeVars (σ := rowSig) (s.label o)).sup id + 1 ≤
        s.present.sup (fun o => (Term.freeVars (σ := rowSig) (s.label o)).sup id + 1) :=
      Finset.le_sup (f := fun o => (Term.freeVars (σ := rowSig) (s.label o)).sup id + 1) present
    exact lt_of_lt_of_le (Nat.lt_succ_of_le inSup) (inAll.trans (Nat.le_add_left _ _))

/-- **Renaming the rule's unknowns beyond every unknown the state mentions is a fresh opening.** -/
theorem shift_fresh_of_bound {s : SState O} (g : Firing O E {r | r ∈ rules} s.frame)
    (opening : g.opening = shift (stateBound s)) : g.Fresh X s := by
  intro b (g' : Subst rowSig) (h : Subst rowSig)
  let u : Subst rowSig := fun v => if stateBound s ≤ v then h (v - stateBound s) else g' v
  refine ⟨u, ?_, ?_⟩
  · intro t mentioned
    show Subst.applyTerm u (Subst.applyTerm (Subst.id rowSig) t) = g'.applyTerm t
    rw [Subst.applyTerm_id]
    exact Subst.applyTerm_congr fun v vars => if_neg (Nat.not_le.mpr (lt_stateBound mentioned vars))
  · intro t _
    show Subst.applyTerm u (Subst.applyTerm g.opening t) = h.applyTerm t
    rw [opening, ← Subst.applyTerm_comp]
    congr 1
    funext x
    show (if stateBound s ≤ x + stateBound s then h (x + stateBound s - stateBound s)
      else g' (x + stateBound s)) = h x
    rw [if_pos (Nat.le_add_left _ _), Nat.add_sub_cancel]

/-- The solution that reads each renamed unknown as its row and every other unknown as a given solution does. -/
def mixedSolution (N : ℕ) (θ : ℕ → Expr) (σ₀ : Subst rowSig) : Subst rowSig :=
  fun v => if N ≤ v then toTerm (θ (v - N)) else σ₀ v

theorem mixed_reads (N : ℕ) (θ : ℕ → Expr) (σ₀ : Subst rowSig) (t : Tm) :
    (mixedSolution N θ σ₀).applyTerm ((shift N).applyTerm t) = toTerm (inst θ t) := by
  rw [← Subst.applyTerm_comp, ← applyTerm_lift]
  refine Subst.applyTerm_congr fun x _ => ?_
  show (if N ≤ x + N then toTerm (θ (x + N - N)) else σ₀ (x + N)) = toTerm (θ x)
  rw [if_pos (Nat.le_add_left _ _), Nat.add_sub_cancel]

theorem mixed_below (N : ℕ) (θ : ℕ → Expr) (σ₀ : Subst rowSig) {t : Tm}
    (below : ∀ v ∈ Term.freeVars (σ := rowSig) t, v < N) :
    (mixedSolution N θ σ₀).applyTerm t = σ₀.applyTerm t :=
  Subst.applyTerm_congr fun v vars => if_neg (Nat.not_le.mpr (below v vars))

/-! ## Solutions of a firing's information -/

/-- A solution of a firing's information solves the knowledge of the state. -/
theorem knowledge_of_information {s : SState O} (g : Firing O E {r | r ∈ rules} s.frame) {σ : Subst rowSig}
    (solved : A.Models σ (g.information X s)) : A.Models σ s.knowledge := by
  have known : X.applyStore ((ext A).weaken g.ext) s.knowledge = s.knowledge :=
    Frames.applyStore_id (X := X) s.knowledge
  intro e member
  apply solved
  unfold Firing.information
  rw [known]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ member))

/-- **Every solution of the information reads each unknown a take or read pattern binds as the match does**,
at a state that reads as rows. -/
theorem agree_of_reads {s : SState O} {rows : O → Expr} (reads : Reads s rows)
    (g : Firing O E {r | r ∈ rules} s.frame) (θ : ℕ → Expr)
    (takeLength : g.rule.body.take.length = g.selection.taken.length)
    (readLength : g.rule.body.read.length = g.selection.read.length)
    (takenPresent : ∀ o ∈ g.selection.taken, o ∈ s.present) (readPresent : ∀ o ∈ g.selection.read, o ∈ s.present)
    (takesMatch : ∀ x ∈ g.rule.body.take.zip g.selection.taken, inst θ x.1 = rows x.2)
    (readsMatch : ∀ x ∈ g.rule.body.read.zip g.selection.read, inst θ x.1 = rows x.2)
    {σ : Subst rowSig} (solved : A.Models σ (g.information X s)) :
    ∀ x, Bound g.rule x → σ.applyTerm (g.opening x) = toTerm (θ x) := by
  rintro x ⟨t, member, vars⟩
  have known := knowledge_of_information g solved
  have composed : ∀ {p : Tm} {o : O}, o ∈ s.present → inst θ p = rows o →
      σ.applyTerm (g.opening.applyTerm p) = σ.applyTerm (g.row X s o) → ∀ y ∈ p.freeVars,
        σ.applyTerm (g.opening y) = toTerm (θ y) := by
    intro p o present instantiated equation y vars
    rw [row_eq, reads.reads σ known o present, ← instantiated, ← applyTerm_lift,
      ← Subst.applyTerm_comp] at equation
    exact agree_of_applyTerm_eq p equation y vars
  rcases List.mem_append.mp member with taken | read
  · obtain ⟨o, inside⟩ := exists_zip_of_mem takeLength taken
    exact composed (takenPresent o (List.of_mem_zip inside).2) (takesMatch _ inside)
      (g.take_solved (b := PUnit.unit) solved (mem_zip_map_left inside)) x vars
  · obtain ⟨o, inside⟩ := exists_zip_of_mem readLength read
    exact composed (readPresent o (List.of_mem_zip inside).2) (readsMatch _ inside)
      (g.read_solved (b := PUnit.unit) solved (mem_zip_map_left inside)) x vars

/-- Lists of one length whose paired elements have equal images have equal images. -/
theorem map_eq_map_of_zip {α β γ : Type*} {f : α → γ} {g : β → γ} :
    ∀ {l₁ : List α} {l₂ : List β}, l₁.length = l₂.length → (∀ x ∈ l₁.zip l₂, f x.1 = g x.2) →
      l₁.map f = l₂.map g
  | [], [], _, _ => rfl
  | [], _ :: _, lengths, _ => by simp at lengths
  | _ :: _, [], lengths, _ => by simp at lengths
  | a :: as, b :: bs, lengths, each => by
      rw [List.map_cons, List.map_cons, each (a, b) List.mem_cons_self,
        map_eq_map_of_zip (Nat.succ.inj lengths) fun x member => each x (List.mem_cons_of_mem _ member)]

end Reading

/-! ## The rows after a firing -/

section Firing

variable {O : Type uO} [DecidableEq O] {rules : List SRule}

/-- **The rows after a firing**: the made identities carry the made instances, in order; every other identity
keeps its row. -/
def rowsAfter (rows : O → Expr) : List O → List Expr → O → Expr
  | o' :: rest, e :: es, o => if o = o' then e else rowsAfter rows rest es o
  | _, _, o => rows o

theorem rowsAfter_of_not_mem (rows : O → Expr) :
    ∀ (made : List O) (es : List Expr) {o : O}, o ∉ made → rowsAfter rows made es o = rows o
  | [], _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | o' :: rest, e :: es, o, missing => by
      have other : o ≠ o' := fun same => missing (List.mem_cons.mpr (Or.inl same))
      have later : o ∉ rest := fun inside => missing (List.mem_cons.mpr (Or.inr inside))
      simp only [rowsAfter, if_neg other]
      exact rowsAfter_of_not_mem rows rest es later

theorem rowsAfter_map (rows : O → Expr) :
    ∀ (made : List O) (es : List Expr), made.Nodup → made.length = es.length →
      made.map (rowsAfter rows made es) = es
  | [], [], _, _ => rfl
  | [], _ :: _, _, lengths => by simp at lengths
  | _ :: _, [], _, lengths => by simp at lengths
  | o' :: rest, e :: es, nodup, lengths => by
      have notIn : o' ∉ rest := (List.nodup_cons.mp nodup).1
      have tailEq : rest.map (rowsAfter rows (o' :: rest) (e :: es)) = rest.map (rowsAfter rows rest es) := by
        refine List.map_congr_left fun o member => ?_
        have other : o ≠ o' := fun same => notIn (same ▸ member)
        simp only [rowsAfter, if_neg other]
      have headEq : rowsAfter rows (o' :: rest) (e :: es) o' = e := by
        show (if o' = o' then e else rowsAfter rows rest es o') = e
        exact if_pos rfl
      rw [List.map_cons, tailEq, headEq,
        rowsAfter_map rows rest es (List.nodup_cons.mp nodup).2 (Nat.succ.inj lengths)]

/-- **The bag after a commit**: the rows not taken, beside the made rows. -/
theorem bag_after (W : Finset O) (rows : O → Expr) (sel : Selection O) {es : List Expr}
    (madeNodup : sel.made.Nodup) (lengths : sel.made.length = es.length)
    (madeFresh : Disjoint sel.made.toFinset W) :
    (fire W (sel.commit (T := Unit))).val.map (rowsAfter rows sel.made es) =
      (W \ sel.taken.toFinset).val.map rows + (es : Multiset Expr) := by
  have apart : Disjoint (W \ sel.taken.toFinset) sel.made.toFinset :=
    Finset.disjoint_of_subset_left Finset.sdiff_subset madeFresh.symm
  have restSame : (W \ sel.taken.toFinset).val.map (rowsAfter rows sel.made es) =
      (W \ sel.taken.toFinset).val.map rows :=
    Multiset.map_congr rfl fun o member => rowsAfter_of_not_mem rows sel.made es fun made =>
      Finset.disjoint_left.mp apart (Finset.mem_val.mp member) (List.mem_toFinset.mpr made)
  show ((W \ sel.taken.toFinset) ∪ sel.made.toFinset).val.map (rowsAfter rows sel.made es) = _
  rw [val_union_of_disjoint apart, Multiset.map_add, restSame, toFinset_val_of_nodup madeNodup,
    Multiset.map_coe, rowsAfter_map rows sel.made es madeNodup lengths]

/-- Where a solution reads the opened made rows as their instances and the old labels as their rows, it reads
the relabelled identities as the rows after the firing. -/
theorem relabel_reads {σ : Subst rowSig} (old : O → Tm) (rows : O → Expr) (opening : Tm → Tm)
    (val : Tm → Expr) {o : O} :
    ∀ (made : List O) (ps : List Tm), made.length = ps.length →
      (∀ p ∈ ps, σ.applyTerm (opening p) = toTerm (val p)) →
      (o ∉ made → σ.applyTerm (old o) = toTerm (rows o)) →
      σ.applyTerm (relabel (Tm := OneFrame.Terms Tm) (a := PUnit.unit) old made (ps.map opening) o) =
        toTerm (rowsAfter rows made (ps.map val) o)
  | [], [], _, _, other => other List.not_mem_nil
  | [], _ :: _, lengths, _, _ => by simp at lengths
  | _ :: _, [], lengths, _, _ => by simp at lengths
  | o' :: rest, p :: ps, lengths, each, other => by
      by_cases same : o = o'
      · simp only [relabel, rowsAfter, List.map_cons, if_pos same]
        exact each p List.mem_cons_self
      · simp only [relabel, rowsAfter, List.map_cons, if_neg same]
        exact relabel_reads old rows opening val rest ps (Nat.succ.inj lengths)
          (fun q member => each q (List.mem_cons_of_mem _ member))
          (fun missing => other fun inside => (List.mem_cons.mp inside).elim same missing)

/-- **The result of an admitted firing reads as the rows after it**, at a state that reads as rows. -/
theorem result_reads {s : SState O} {rows : O → Expr} (reads : Reads s rows)
    (g : Firing O E {r | r ∈ rules} s.frame) (admitted : (schematicStep O rules).Admits (s := s) g)
    (restricted : RangeRestricted g.rule) (θ : ℕ → Expr)
    (agree : ∀ σ : Subst rowSig, A.Models σ (g.information X s) →
      ∀ x, Bound g.rule x → σ.applyTerm (g.opening x) = toTerm (θ x)) :
    Reads ((schematicStep O rules).result g admitted)
      (rowsAfter rows g.selection.made (g.rule.body.produce.map (inst θ))) := by
  obtain ⟨-, ⟨-, -, -, -, produceLength, -⟩, -, solvable, -⟩ := (admits_iff g).mp admitted
  refine ⟨(Frames.ofSubstitution_solvable_iff A _).mp solvable, fun σ solved o present => ?_⟩
  have solved' : A.Models σ (g.information X s) := solved
  have inFire : o ∈ fire s.present (g.selection.commit (T := Unit)) := present
  exact relabel_reads (g.row X s) rows g.opening.applyTerm (inst θ) g.selection.made g.rule.body.produce
    produceLength.symm
    (fun p member => written_reads g (agree σ solved') fun x vars =>
      restricted p (mem_written_of_produce member) x vars)
    (fun notMade => by
      rcases mem_fire.mp inFire with ⟨inStore, -⟩ | made
      · rw [row_eq]
        exact reads.reads σ (knowledge_of_information g solved') o inStore
      · exact absurd (List.mem_toFinset.mp made) notMade)

/-! ## An admitted firing is a rewrite by matching -/

/-- **An admitted firing of a rule of the fragment, at a state that reads as rows, is a firing by matching**:
some ground instantiation of the rule's unknowns sends the takes and reads to the rows of the selected
identities and solves the rule's equations, and the result reads as the rows after the firing. -/
theorem rewrite_of_admitted {s : SState O} {rows : O → Expr} (reads : Reads s rows)
    (fragment : ∀ r ∈ rules, RangeRestrictedPositive r)
    (g : Firing O E {r | r ∈ rules} s.frame) (admitted : (schematicStep O rules).Admits (s := s) g) :
    ∃ θ : ℕ → Expr,
      g.rule.body.take.map (inst θ) = g.selection.taken.map rows ∧
      g.rule.body.read.map (inst θ) = g.selection.read.map rows ∧
      (∀ e ∈ equationsOf g.rule, inst θ e.1 = inst θ e.2) ∧
      Reads ((schematicStep O rules).result g admitted)
        (rowsAfter rows g.selection.made (g.rule.body.produce.map (inst θ))) := by
  obtain ⟨-, ⟨-, -, takeLength, readLength, -, -⟩, enabled, solvable, checks, -⟩ :=
    (admits_iff g).mp admitted
  have fragmentRule := fragment g.rule g.member
  obtain ⟨σ, solved⟩ := (Frames.ofSubstitution_solvable_iff A _).mp solvable
  have known := knowledge_of_information g solved
  let θ := groundPart (σ.comp g.opening)
  have takenPresent : ∀ o ∈ g.selection.taken, o ∈ s.present := fun o member =>
    enabled.taken_subset (List.mem_toFinset.mpr member)
  have readPresent : ∀ o ∈ g.selection.read, o ∈ s.present := fun o member =>
    enabled.kept_subset (List.mem_toFinset.mpr member)
  have matchedBy : ∀ {p : Tm} {o : O}, o ∈ s.present →
      σ.applyTerm (g.opening.applyTerm p) = σ.applyTerm (g.row X s o) → inst θ p = rows o := by
    intro p o present equation
    rw [row_eq, reads.reads σ known o present, ← Subst.applyTerm_comp] at equation
    exact (inst_groundPart _ p (rows o) equation).1
  have takesMatch : ∀ x ∈ g.rule.body.take.zip g.selection.taken, inst θ x.1 = rows x.2 := fun x inside =>
    matchedBy (takenPresent x.2 (List.of_mem_zip inside).2)
      (g.take_solved (b := PUnit.unit) solved (mem_zip_map_left inside))
  have readsMatch : ∀ x ∈ g.rule.body.read.zip g.selection.read, inst θ x.1 = rows x.2 := fun x inside =>
    matchedBy (readPresent x.2 (List.of_mem_zip inside).2)
      (g.read_solved (b := PUnit.unit) solved (mem_zip_map_left inside))
  have agree : ∀ σ' : Subst rowSig, A.Models σ' (g.information X s) →
      ∀ x, Bound g.rule x → σ'.applyTerm (g.opening x) = toTerm (θ x) := fun σ' solved' =>
    agree_of_reads reads g θ takeLength readLength takenPresent readPresent takesMatch readsMatch solved'
  have writes : ∀ σ' : Subst rowSig, A.Models σ' (g.information X s) → ∀ t : Tm,
      (∀ x ∈ t.freeVars, Bound g.rule x) →
      σ'.applyTerm (g.opening.applyTerm t) = toTerm (inst θ t) := fun σ' solved' t bound =>
    written_reads g (agree σ' solved') bound
  refine ⟨θ, map_eq_map_of_zip takeLength takesMatch, map_eq_map_of_zip readLength readsMatch, ?_,
    result_reads reads g admitted fragmentRule.2.2 θ agree⟩
  intro e member
  have written := mem_written_of_equation member
  have boundLeft : ∀ x ∈ e.1.freeVars, Bound g.rule x := fun x vars => fragmentRule.2.2 _ written.1 x vars
  have boundRight : ∀ x ∈ e.2.freeVars, Bound g.rule x := fun x vars => fragmentRule.2.2 _ written.2 x vars
  have equal : σ.applyTerm (g.opening.applyTerm e.1) = σ.applyTerm (g.opening.applyTerm e.2) := by
    rcases List.mem_append.mp member with told | guarded
    · exact g.tell_solved (b := PUnit.unit) solved (List.mem_map_of_mem (f := fun pair => (g.opening.applyTerm pair.1,
        g.opening.applyTerm pair.2)) told)
    · obtain ⟨c, inChecks, inGuard⟩ := List.mem_flatMap.mp guarded
      cases c with
      | equal l r =>
          rw [guardOf, List.mem_singleton] at inGuard
          subst inGuard
          exact checks (Check.map g.opening.applyTerm (.equal l r)) (List.mem_map_of_mem inChecks)
            PUnit.unit σ solved
      | predicate quantifier _ => simp [guardOf] at inGuard
      | count _ _ => simp [guardOf] at inGuard
  rw [writes σ solved e.1 boundLeft, writes σ solved e.2 boundRight] at equal
  exact toTerm_injective equal

/-! ## A rewrite by matching is an admitted firing -/

/-- **Every firing by matching at a state that reads as rows is an admitted firing of `RuleSyntax.step`**, and
its result reads as the made rows' instances beside the rest, when identities are infinitely many. -/
theorem admitted_of_rewrite [Infinite O] {s : SState O} {rows : O → Expr} (reads : Reads s rows)
    {r : SRule} (member : r ∈ rules) (fragmentRule : RangeRestrictedPositive r) {θ : ℕ → Expr}
    {restM : Multiset Expr}
    (split : (r.body.take.map (inst θ) : Multiset Expr) + restM = s.present.val.map rows)
    (readsIn : ∀ q ∈ r.body.read, inst θ q ∈ restM) (equations : ∀ e ∈ equationsOf r, inst θ e.1 = inst θ e.2) :
    ∃ (g : Firing O E {r | r ∈ rules} s.frame) (admitted : (schematicStep O rules).Admits (s := s) g),
      g.rule = r ∧ ∃ rows' : O → Expr, Reads ((schematicStep O rules).result g admitted) rows' ∧
        ((schematicStep O rules).result g admitted).present.val.map rows' =
          (r.body.produce.map (inst θ) : Multiset Expr) + restM := by
  obtain ⟨taken, takenNodup, takenIn, takenRows⟩ := exists_taken rows (r.body.take.map (inst θ)) s.present
    (show ((r.body.take.map (inst θ) : List Expr) : Multiset Expr) ≤ s.present.val.map rows from
      (le_add_right le_rfl).trans_eq split)
  have takenSub : taken.toFinset ⊆ s.present := fun o member => takenIn o (List.mem_toFinset.mp member)
  have restEq : restM = (s.present \ taken.toFinset).val.map rows := by
    have whole := bagOf_split rows (C := ⟨[], s.present⟩) takenNodup takenSub
    rw [takenRows] at whole
    exact add_left_cancel (split.trans whole)
  obtain ⟨read, readIn, readRows⟩ := exists_read rows (r.body.read.map (inst θ)) (s.present \ taken.toFinset)
    (fun x inside => by
      obtain ⟨q, inRead, rfl⟩ := List.mem_map.mp inside
      rw [← restEq]
      exact readsIn q inRead)
  obtain ⟨made, madeNodup, madeLength, madeFresh⟩ := exists_fresh s.present r.body.produce.length
  have collectEmpty : r.collect = [] := fragmentRule.1
  let g : Firing O E {r | r ∈ rules} s.frame :=
    ⟨r, member, PUnit.unit, shift (stateBound s), ⟨taken, read, made⟩, []⟩
  have takeLength : r.body.take.length = taken.length := by
    rw [← List.length_map (f := inst θ), ← takenRows, List.length_map]
  have readLength : r.body.read.length = read.length := by
    rw [← List.length_map (f := inst θ), ← readRows, List.length_map]
  have takenPresent : ∀ o ∈ taken, o ∈ s.present := takenIn
  have readPresent : ∀ o ∈ read, o ∈ s.present := fun o inside => (Finset.mem_sdiff.mp (readIn o inside)).1
  have takesMatch : ∀ x ∈ r.body.take.zip taken, inst θ x.1 = rows x.2 := pairs_of_map_eq takenRows.symm
  have readsMatch : ∀ x ∈ r.body.read.zip read, inst θ x.1 = rows x.2 := pairs_of_map_eq readRows.symm
  have agree : ∀ σ' : Subst rowSig, A.Models σ' (g.information X s) →
      ∀ x, Bound g.rule x → σ'.applyTerm (g.opening x) = toTerm (θ x) := fun σ' solved' =>
    agree_of_reads reads g θ takeLength readLength takenPresent readPresent takesMatch readsMatch solved'
  have known : X.applyStore ((ext A).weaken g.ext) s.knowledge = s.knowledge :=
    Frames.applyStore_id (X := X) s.knowledge
  obtain ⟨σ₀, solved₀⟩ := reads.solvable
  have labelRead : ∀ o ∈ s.present,
      (mixedSolution (stateBound s) θ σ₀).applyTerm (s.label o) = toTerm (rows o) := by
    intro o present
    rw [mixed_below (stateBound s) θ σ₀ (t := s.label o) fun v vars =>
      lt_stateBound (Or.inr (Or.inr ⟨o, present, rfl⟩)) vars]
    exact reads.reads σ₀ solved₀ o present
  have solved : A.Models (mixedSolution (stateBound s) θ σ₀) (g.information X s) := by
    intro e inside
    unfold Firing.information at inside
    rw [known] at inside
    simp only [List.mem_append] at inside
    rcases inside with ((old | taking) | reading) | told
    · show Subst.applyTerm _ e.1 = Subst.applyTerm _ e.2
      rw [mixed_below (stateBound s) θ σ₀ (t := e.1) fun v vars =>
          lt_stateBound (Or.inl (List.mem_map_of_mem old)) vars,
        mixed_below (stateBound s) θ σ₀ (t := e.2) fun v vars =>
          lt_stateBound (Or.inr (Or.inl (List.mem_map_of_mem old))) vars]
      exact solved₀ e old
    · obtain ⟨p, o, pair, rfl⟩ := mem_matching g taking
      show Subst.applyTerm _ (Subst.applyTerm (shift _) p) = Subst.applyTerm _ (s.label o)
      rw [mixed_reads, labelRead o (takenPresent o (List.of_mem_zip pair).2), takesMatch _ pair]
    · obtain ⟨p, o, pair, rfl⟩ := mem_matching g reading
      show Subst.applyTerm _ (Subst.applyTerm (shift _) p) = Subst.applyTerm _ (s.label o)
      rw [mixed_reads, labelRead o (readPresent o (List.of_mem_zip pair).2), readsMatch _ pair]
    · obtain ⟨pair, inTell, rfl⟩ := List.mem_map.mp told
      show Subst.applyTerm _ (Subst.applyTerm (shift _) pair.1) =
        Subst.applyTerm _ (Subst.applyTerm (shift _) pair.2)
      rw [mixed_reads, mixed_reads, equations pair (List.mem_append_left _ inTell)]
  have admitted : (schematicStep O rules).Admits (s := s) g := by
    refine (admits_iff g).mpr ⟨shift_fresh_of_bound g rfl, ⟨takenNodup, madeNodup, takeLength, readLength,
      madeLength.symm, by rw [collectEmpty]; rfl⟩, ?_,
      (Frames.ofSubstitution_solvable_iff A _).mpr ⟨_, solved⟩, ?_, ?_⟩
    · exact ⟨takenSub, fun o inside => readPresent o (List.mem_toFinset.mp inside),
        Finset.disjoint_left.mpr fun o taking reading =>
          (Finset.mem_sdiff.mp (readIn o (List.mem_toFinset.mp reading))).2 taking,
        Finset.disjoint_left.mpr fun o inside present => madeFresh o (List.mem_toFinset.mp inside) present,
        fun query inside => by simp [Selection.commit] at inside⟩
    · intro c inChecks b σ' solved'
      obtain ⟨c₀, inRule, rfl⟩ := List.mem_map.mp inChecks
      have isGuardC := List.all_eq_true.mp fragmentRule.2.1 c₀ inRule
      cases c₀ with
      | equal l r' =>
          have inEquations : (l, r') ∈ equationsOf r :=
            List.mem_append_right _ (List.mem_flatMap.mpr ⟨.equal l r', inRule, List.mem_singleton_self _⟩)
          have written := mem_written_of_equation inEquations
          show Subst.applyTerm σ' (Subst.applyTerm (shift _) l) = Subst.applyTerm σ' (Subst.applyTerm (shift _) r')
          rw [written_reads g (agree σ' solved') fun x vars => fragmentRule.2.2 _ written.1 x vars,
            written_reads g (agree σ' solved') fun x vars => fragmentRule.2.2 _ written.2 x vars,
            equations _ inEquations]
      | predicate quantifier _ => simp [isGuard] at isGuardC
      | count _ _ => simp [isGuard] at isGuardC
    · intro q inside
      have none : (g.collectOpened X).zip g.seen = [] := by
        simp [Firing.collectOpened, g, collectEmpty]
      rw [none] at inside
      exact absurd inside List.not_mem_nil
  have lengths : made.length = (r.body.produce.map (inst θ)).length := by
    rw [List.length_map]
    exact madeLength
  have fresh : Disjoint made.toFinset s.present :=
    Finset.disjoint_left.mpr fun o inside present => madeFresh o (List.mem_toFinset.mp inside) present
  refine ⟨g, admitted, rfl, rowsAfter rows made (r.body.produce.map (inst θ)),
    result_reads reads g admitted fragmentRule.2.2 θ agree, ?_⟩
  rw [restEq]
  exact (bag_after s.present rows g.selection madeNodup lengths fresh).trans (add_comm _ _)

/-! ## Rewriting of bags, and the correspondence -/

/-- **One rewrite of a bag of rows by matching**: a rule of the list, a ground instantiation of its unknowns
and a rest; the takes' instances beside the rest are the bag, each read's instance is a row of the rest, the
rule's equations hold at the instantiation, and the result is the made rows' instances beside the rest. -/
def Rewrites (rules : List SRule) (bag bag' : Multiset Expr) : Prop :=
  ∃ r ∈ rules, ∃ (θ : ℕ → Expr) (rest : Multiset Expr),
    (r.body.take.map (inst θ) : Multiset Expr) + rest = bag ∧
    (∀ q ∈ r.body.read, inst θ q ∈ rest) ∧
    (∀ e ∈ equationsOf r, inst θ e.1 = inst θ e.2) ∧
    bag' = (r.body.produce.map (inst θ) : Multiset Expr) + rest

/-- **An admitted firing at a state that reads as a bag is one rewrite of the bag, and its result reads as the
rewritten bag.** -/
theorem readsBag_backward (fragment : ∀ r ∈ rules, RangeRestrictedPositive r) {s : SState O}
    {bag : Multiset Expr} (reads : ReadsBag s bag) (g : Firing O E {r | r ∈ rules} s.frame)
    (admitted : (schematicStep O rules).Admits (s := s) g) :
    ∃ bag', Rewrites rules bag bag' ∧ ReadsBag ((schematicStep O rules).result g admitted) bag' := by
  obtain ⟨rows, reads, rfl⟩ := reads
  obtain ⟨θ, takes, readsMatch, equations, after⟩ := rewrite_of_admitted reads fragment g admitted
  obtain ⟨-, ⟨takenNodup, madeNodup, -, readLength, produceLength, -⟩, enabled, -⟩ :=
    (admits_iff g).mp admitted
  have lengths : g.selection.made.length = (g.rule.body.produce.map (inst θ)).length := by
    rw [List.length_map]
    exact produceLength.symm
  refine ⟨_, ⟨g.rule, g.member, θ, (s.present \ g.selection.taken.toFinset).val.map rows, ?_, ?_, equations,
    rfl⟩, ⟨_, after, (bag_after s.present rows g.selection madeNodup lengths enabled.fresh).trans
      (add_comm _ _)⟩⟩
  · have whole := bagOf_split rows (C := ⟨[], s.present⟩) takenNodup enabled.taken_subset
    rw [takes]
    exact whole.symm
  · intro q member
    obtain ⟨o, inside⟩ := exists_zip_of_mem readLength member
    have matched : inst θ q = rows o := pairs_of_map_eq readsMatch (q, o) inside
    rw [matched]
    refine Multiset.mem_map_of_mem _ (Finset.mem_val.mpr (Finset.mem_sdiff.mpr ⟨?_, fun taken => ?_⟩))
    · exact enabled.kept_subset (List.mem_toFinset.mpr (List.of_mem_zip inside).2)
    · exact Finset.disjoint_left.mp enabled.apart taken (List.mem_toFinset.mpr (List.of_mem_zip inside).2)

/-- **Every rewrite of the bag a state reads as is an admitted firing whose result reads as the rewritten
bag**, when identities are infinitely many. -/
theorem readsBag_forward [Infinite O] (fragment : ∀ r ∈ rules, RangeRestrictedPositive r) {s : SState O}
    {bag bag' : Multiset Expr} (reads : ReadsBag s bag) (rewrites : Rewrites rules bag bag') :
    ∃ (g : Firing O E {r | r ∈ rules} s.frame) (admitted : (schematicStep O rules).Admits (s := s) g),
      ReadsBag ((schematicStep O rules).result g admitted) bag' := by
  obtain ⟨rows, reads, rfl⟩ := reads
  obtain ⟨r, member, θ, rest, split, readsIn, equations, rfl⟩ := rewrites
  obtain ⟨g, admitted, -, rows', reads', bagEq⟩ :=
    admitted_of_rewrite reads member (fragment r member) split readsIn equations
  exact ⟨g, admitted, rows', reads', bagEq⟩

/-- **Rewriting of bags of rows by matching, as a system**: bags, equal when identical, under `Rewrites`. -/
def rewriting (rules : List SRule) : GSLT := equalityGSLT (Multiset Expr) (Rewrites rules)

/-- **The step of a program, as a system**: states, equal when identical, under the successor relation of
`RuleSyntax.step`. -/
def stepSystem (O : Type uO) [DecidableEq O] (rules : List SRule) : GSLT :=
  equalityGSLT (SState O) (Succ (schematicStep O rules).toStep)

/-- **The correspondence**: rewriting of bags and the step of a range-restricted positive program, related by
reading a state as a bag. A firing of the step is read back as one rewrite, and a rewrite is realized by one
firing. -/
def correspondence [Infinite O] (fragment : ∀ r ∈ rules, RangeRestrictedPositive r) :
    OperationalCorrespondence (rewriting rules) (stepSystem O rules) where
  related bag s := ReadsBag s bag
  readStep := by
    intro bag s s' reads stepped
    obtain ⟨g, admitted, rfl⟩ := stepped
    obtain ⟨bag', rewrites, reads'⟩ := readsBag_backward fragment reads g admitted
    exact Or.inr ⟨bag', rewrites, reads'⟩
  forward := by
    intro bag bag' s reads rewrites
    obtain ⟨g, admitted, reads'⟩ := readsBag_forward fragment reads rewrites
    exact ⟨_, (executionPath_nonempty_iff_multiStep (stepSystem O rules) _ _).mpr
      (.step ⟨g, admitted, rfl⟩ (.refl _)), reads'⟩

/-- **Reachability transfers both ways**: a bag with a property is reachable by rewriting exactly when a state
that reads as such a bag is reachable by the step. -/
theorem reachable_iff [Infinite O] (fragment : ∀ r ∈ rules, RangeRestrictedPositive r)
    (property : Multiset Expr → Prop) {s : SState O} {bag : Multiset Expr} (reads : ReadsBag s bag) :
    (∃ bag', (rewriting rules).MultiStep bag bag' ∧ property bag') ↔
      ∃ s', (stepSystem O rules).MultiStep s s' ∧ ∃ bag', ReadsBag s' bag' ∧ property bag' := by
  refine (correspondence (O := O) fragment).reachable_iff property (fun s' => ∃ bag', ReadsBag s' bag' ∧ property bag')
    (fun {origin current} related => ?_) reads
  have readsHere : ReadsBag current origin := related
  constructor
  · exact fun holds => ⟨origin, readsHere, holds⟩
  · rintro ⟨other, readsOther, holds⟩
    have same : origin = other :=
      readsAs_unique (ReadsBag.readsAs readsHere).1 (ReadsBag.readsAs readsHere).2
        (ReadsBag.readsAs readsOther).2
    rw [same]
    exact holds

end Firing

/-! ## One-row states -/

/-- **The one-row state of a row**: identity `0` labelled by the row, with no knowledge. -/
def rowState (e : Expr) : SState ℕ := ⟨PUnit.unit, [], {0}, fun _ => toTerm e⟩

/-- **The one-row state of a row reads as the row.** -/
theorem rowState_reads (e : Expr) : ReadsBag (rowState e) {e} :=
  ⟨fun _ => e, reads_of_ground (fun _ _ => rfl) (fun _ member => absurd member List.not_mem_nil), rfl⟩

/-- A rewrite by one rule of a list is a rewrite by the list. -/
theorem rewrites_of_mem {rules : List SRule} {r : SRule} (member : r ∈ rules) {bag bag' : Multiset Expr}
    (single : Rewrites [r] bag bag') : Rewrites rules bag bag' := by
  obtain ⟨r', inside, rewritten⟩ := single
  obtain rfl := List.mem_singleton.mp inside
  exact ⟨_, member, rewritten⟩

/-! ## States of lists of rows -/

/-- The row of a list at a position; a constant beyond its end. -/
def nthRow : List Expr → ℕ → Expr
  | [], _ => .sym 0
  | e :: _, 0 => e
  | _ :: l, i + 1 => nthRow l i

theorem map_nthRow_range : ∀ l : List Expr, (List.range l.length).map (nthRow l) = l
  | [] => rfl
  | e :: l => by
      rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
      exact congrArg (List.cons e) (map_nthRow_range l)

/-- **The state of a list of rows**: one identity per position, labelled by its row, with no knowledge. -/
def listState (l : List Expr) : SState ℕ :=
  ⟨PUnit.unit, [], Finset.range l.length, fun o => toTerm (nthRow l o)⟩

/-- **The state of a list of rows reads as the bag of the list.** -/
theorem listState_reads (l : List Expr) : ReadsBag (listState l) (l : Multiset Expr) :=
  ⟨nthRow l, reads_of_ground (fun _ _ => rfl) (fun _ member => absurd member List.not_mem_nil),
    congrArg (fun rows : List Expr => (rows : Multiset Expr)) (map_nthRow_range l)⟩

/-- **Every bag of rows is read from a state.** -/
theorem exists_reads (bag : Multiset Expr) : ∃ s : SState ℕ, ReadsBag s bag := by
  have reads := listState_reads bag.toList
  rw [Multiset.coe_toList] at reads
  exact ⟨_, reads⟩

/-- A one-row bag beside a rest that is a one-row bag: the rows are the same and the rest is empty. -/
theorem row_of_singleton {α : Type*} {a b : α} {rest : Multiset α}
    (same : (([a] : List α) : Multiset α) + rest = {b}) : a = b ∧ rest = 0 := by
  have inside : a ∈ ({b} : Multiset α) := by
    rw [← same]
    exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_coe.mpr List.mem_cons_self))
  have counted := congrArg Multiset.card same
  rw [Multiset.card_add, Multiset.coe_card, List.length_singleton, Multiset.card_singleton] at counted
  exact ⟨Multiset.mem_singleton.mp inside, Multiset.card_eq_zero.mp (by omega)⟩

#print axioms rowState_reads
#print axioms listState_reads
#print axioms exists_reads
#print axioms reads_of_ground
#print axioms readsBag_iff
#print axioms shift_fresh_of_bound
#print axioms rewrite_of_admitted
#print axioms admitted_of_rewrite
#print axioms readsBag_backward
#print axioms readsBag_forward
#print axioms correspondence
#print axioms reachable_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines
