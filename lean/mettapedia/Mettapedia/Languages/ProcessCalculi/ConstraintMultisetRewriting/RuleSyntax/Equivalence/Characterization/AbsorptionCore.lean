import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Characterization.EveryState
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Commute

/-!
# Tools for programs of many rules: one more row `5`

`everyRule` is the program of every rule, and `positiveRules` the program of every positive rule (its
checks are equation guards, and it has no collect query). A state `fiveMore a d` is `a` with one more row `5`,
at an identity `d` absent from `a`. This module proves the facts the candidate of `Absorption` uses:

* **Static equivalence from the rows** (`static_of_perm`, `static_of_rows`): equivalent knowledge with
  the same mentioned unknowns, and present rows that a permutation matches label for label (or the
  same multiset of labels), give `Static`.
* **One more row `5`** (`OneMore`): the same knowledge, a row `5` at the left, and the right's labels
  the left's with one more `5`. It is kept by every context (`oneMore_addRows`, `oneMore_tell`), the
  may-barbs do not see it (`mayBarb_oneMore`), and `fiveMore a d` is statically equivalent to every
  `b` with `OneMore a b` (`static_fiveMore`).

The answers themselves are in `AbsorptionMoves` (forward) and `AbsorptionBack` (backward); each answers
by a positive rule (`positive_of_nil`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Characterization

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open Mettapedia.Logic.LP
open RuleSyntax.Examples (Tm X E x c fresh_of_ground)
open RuleSyntax.Controls (atoms action)
open AtOneFrame (Sys Cong Moves extendState_eq_self)

/-! ## Static equivalence from the rows -/

/-- The unknowns the knowledge of a state mentions. -/
def KnowsVar (s : State Tm ℕ) (w : ℕ) : Prop :=
  (Term.var w : Term atoms) ∈ s.knowledge.map Prod.fst ∨ (Term.var w : Term atoms) ∈ s.knowledge.map Prod.snd

/-- **A permutation matching the rows, label for label, with equivalent knowledge mentioning the same
unknowns, gives the static equivalence.** -/
theorem static_of_perm {s t : State Tm ℕ}
    (equivalent : X.Equivalent (a := PUnit.unit) s.knowledge t.knowledge)
    (knows : ∀ w, KnowsVar s w ↔ KnowsVar t w) (π : Equiv.Perm ℕ)
    (present : t.present = s.present.map π.toEmbedding)
    (labels : ∀ o ∈ s.present, t.label (π o) = s.label o) : Static s t := by
  obtain ⟨tf, tk, tp, tl⟩ := t
  simp only at present
  subst present
  refine Or.inr ⟨π, tk, tl, ⟨equivalent, fun o inside b δ _ => ?_, fun b φ ψ => ?_⟩, rfl⟩
  · have back : π.symm o ∈ s.present := Finset.mem_map_equiv.mp inside
    have agree := labels (π.symm o) back
    rw [Equiv.apply_symm_apply] at agree
    show X.E (X.act δ (s.label (π.symm o))) (X.act δ (tl o))
    rw [show tl o = s.label (π.symm o) from agree]
    exact (X.equivalence b).refl _
  · cases b
    show Supports X (renameState π s) φ ψ ↔
      Supports X (⟨(renameState π s).frame, tk, (renameState π s).present, tl⟩ : State Tm ℕ) φ ψ
    rw [supports_iff_vars, supports_iff_vars]
    have sameMentions : ∀ w, (renameState π s).Mentions (.var w) ↔
        (⟨(renameState π s).frame, tk, (renameState π s).present, tl⟩ : State Tm ℕ).Mentions (.var w) := by
      intro w
      rw [mentions_renameState]
      constructor
      · rintro (inside | inside | ⟨o, present, same⟩)
        · rcases (knows w).mp (Or.inl inside) with left | right
          · exact Or.inl left
          · exact Or.inr (Or.inl right)
        · rcases (knows w).mp (Or.inr inside) with left | right
          · exact Or.inl left
          · exact Or.inr (Or.inl right)
        · refine Or.inr (Or.inr ⟨π o, Finset.mem_map_of_mem _ present, ?_⟩)
          have agree : tl (π o) = s.label o := labels o present
          show tl (π o) = .var w
          rw [agree]
          exact same
      · rintro (inside | inside | ⟨o, present, same⟩)
        · rcases (knows w).mpr (Or.inl inside) with left | right
          · exact Or.inl left
          · exact Or.inr (Or.inl right)
        · rcases (knows w).mpr (Or.inr inside) with left | right
          · exact Or.inl left
          · exact Or.inr (Or.inl right)
        · have back : π.symm o ∈ s.present := Finset.mem_map_equiv.mp present
          refine Or.inr (Or.inr ⟨π.symm o, back, ?_⟩)
          have agree := labels (π.symm o) back
          rw [Equiv.apply_symm_apply] at agree
          rw [← agree]
          exact same
    constructor
    · intro agree w mentions
      exact agree w ((sameMentions w).mpr mentions)
    · intro agree w mentions
      exact agree w ((sameMentions w).mp mentions)

/-- **The same multiset of labels, with equivalent knowledge mentioning the same unknowns, gives the
static equivalence.** -/
theorem static_of_rows {s t : State Tm ℕ}
    (equivalent : X.Equivalent (a := PUnit.unit) s.knowledge t.knowledge)
    (knows : ∀ w, KnowsVar s w ↔ KnowsVar t w)
    (rows : s.present.val.map s.label = t.present.val.map t.label) : Static s t := by
  obtain ⟨π, image, labels⟩ := exists_perm_of_map_eq s.label t.label s.present t.present rows
  exact static_of_perm equivalent knows π image.symm labels

/-! ## One more row `5` -/

/-- Every rule. -/
abbrev everyRule : Program Tm := Set.univ

/-- **A positive rule**: its checks are equation guards (no absence and no count query), and it has no
collect query. -/
def Positive (r : Rule Tm) : Prop :=
  (∀ check ∈ r.body.checks, ∃ left right, check = Check.equal left right) ∧ r.collect = []

/-- **The program of every positive rule.** -/
def positiveRules : Program Tm := {r | Positive r}

/-- A rule with no checks and no collect query is positive. -/
theorem positive_of_nil {r : Rule Tm} (checks : r.body.checks = []) (collect : r.collect = []) :
    r ∈ positiveRules := by
  refine ⟨fun check inside => ?_, collect⟩
  rw [checks] at inside
  simp at inside

/-- The state with one more row `5`, at the identity `d`. -/
def fiveMore (a : State Tm ℕ) (d : ℕ) : State Tm ℕ := addRows a {d} (fun _ => c 5)

/-- **One more row `5`**: the same knowledge, a row `5` at the left, and the labels of the right are
those of the left and one more `5`. -/
def OneMore (a b : State Tm ℕ) : Prop :=
  a.knowledge = b.knowledge ∧ (∃ o ∈ a.present, a.label o = c 5) ∧
    (b.present.val.map b.label : Multiset (Term atoms)) = c 5 ::ₘ a.present.val.map a.label

/-- The labels of rows added at fresh identities. -/
theorem addRows_val_map {s : State Tm ℕ} {ids : Finset ℕ} (ℓ : ℕ → Term atoms)
    (apart : Disjoint s.present ids) :
    ((addRows s ids ℓ).present.val.map (addRows s ids ℓ).label : Multiset (Term atoms)) =
      s.present.val.map s.label + ids.val.map ℓ := by
  show ((s.present ∪ ids).val.map fun o => if o ∈ ids then ℓ o else s.label o) = _
  rw [← Finset.disjUnion_eq_union s.present ids apart, Finset.disjUnion_val, Multiset.map_add]
  congr 1
  · apply Multiset.map_congr rfl
    intro o inside
    have notNew : o ∉ ids := Finset.disjoint_left.mp apart inside
    rw [if_neg notNew]
  · apply Multiset.map_congr rfl
    intro o inside
    rw [if_pos (show o ∈ ids from inside)]

theorem fiveMore_val_map {a : State Tm ℕ} {d : ℕ} (fresh : d ∉ a.present) :
    ((fiveMore a d).present.val.map (fiveMore a d).label : Multiset (Term atoms)) =
      c 5 ::ₘ a.present.val.map a.label := by
  rw [fiveMore, addRows_val_map _ (Finset.disjoint_singleton_right.mpr fresh)]
  simp only [Finset.singleton_val, Multiset.map_singleton]
  rw [add_comm, Multiset.singleton_add]

theorem oneMore_fiveMore {a : State Tm ℕ} (five : ∃ o ∈ a.present, a.label o = c 5) {d : ℕ}
    (fresh : d ∉ a.present) : OneMore a (fiveMore a d) :=
  ⟨rfl, five, fiveMore_val_map fresh⟩

/-- **The may-barbs do not see one more row `5`.** -/
theorem mayBarb_oneMore {a b : State Tm ℕ} (more : OneMore a b) (p : Pattern Tm) :
    MayBarb X p a ↔ MayBarb X p b := by
  obtain ⟨known, ⟨o₀, present₀, five⟩, labels⟩ := more
  constructor
  · rintro ⟨o, present, β, σ, h, solved, equated⟩
    have inB : a.label o ∈ (b.present.val.map b.label : Multiset (Term atoms)) := by
      rw [labels]
      exact Multiset.mem_cons_of_mem (Multiset.mem_map_of_mem _ present)
    obtain ⟨o', present', same⟩ := Multiset.mem_map.mp inB
    refine ⟨o', present', β, σ, h, known ▸ solved, ?_⟩
    show X.E (X.act σ (b.label o')) (X.act h p.term)
    rw [show b.label o' = a.label o from same]
    exact equated
  · rintro ⟨o', present', β, σ, h, solved, equated⟩
    have inB : b.label o' ∈ (b.present.val.map b.label : Multiset (Term atoms)) :=
      Multiset.mem_map_of_mem _ present'
    rw [labels] at inB
    rcases Multiset.mem_cons.mp inB with isFive | inA
    · refine ⟨o₀, present₀, β, σ, h, known ▸ solved, ?_⟩
      show X.E (X.act σ (a.label o₀)) (X.act h p.term)
      rw [five, ← isFive]
      exact equated
    · obtain ⟨o, present, same⟩ := Multiset.mem_map.mp inA
      refine ⟨o, present, β, σ, h, known ▸ solved, ?_⟩
      show X.E (X.act σ (a.label o)) (X.act h p.term)
      rw [show a.label o = b.label o' from same]
      exact equated

/-- **Adding rows keeps one more row `5`**, at fresh identities on each side carrying the same
labels. -/
theorem oneMore_addRows {a b : State Tm ℕ} (more : OneMore a b) {ids ids' : Finset ℕ}
    (ℓ ℓ' : ℕ → Term atoms) (apart : Disjoint a.present ids) (apart' : Disjoint b.present ids')
    (same : (ids.val.map ℓ : Multiset (Term atoms)) = ids'.val.map ℓ') :
    OneMore (addRows a ids ℓ) (addRows b ids' ℓ') := by
  obtain ⟨known, ⟨o₀, present₀, five⟩, labels⟩ := more
  refine ⟨known, ⟨o₀, Finset.mem_union_left _ present₀, ?_⟩, ?_⟩
  · show (if o₀ ∈ ids then ℓ o₀ else a.label o₀) = c 5
    rw [if_neg (Finset.disjoint_left.mp apart present₀)]
    exact five
  · rw [addRows_val_map ℓ apart, addRows_val_map ℓ' apart', labels, same, Multiset.cons_add]

theorem oneMore_tell {a b : State Tm ℕ} (more : OneMore a b) (L : EquationStore (Term atoms)) :
    OneMore (tellState a L) (tellState b L) := by
  obtain ⟨known, five, labels⟩ := more
  exact ⟨by show a.knowledge ++ L = b.knowledge ++ L; rw [known], five, labels⟩

/-- **The state with one more row `5` is statically equivalent to every state one row `5` above.** -/
theorem static_fiveMore {a b : State Tm ℕ} (more : OneMore a b) {d : ℕ} (fresh : d ∉ a.present) :
    Static (fiveMore a d) b := by
  obtain ⟨known, five, labels⟩ := more
  refine static_of_rows ?_ ?_ ?_
  · intro β σ
    show X.Models σ a.knowledge ↔ X.Models σ b.knowledge
    rw [known]
  · intro w
    show KnowsVar a w ↔ KnowsVar b w
    unfold KnowsVar
    rw [known]
  · rw [labels, fiveMore_val_map fresh]

#print axioms static_of_perm
#print axioms static_of_rows
#print axioms positive_of_nil
#print axioms addRows_val_map
#print axioms fiveMore_val_map
#print axioms oneMore_fiveMore
#print axioms mayBarb_oneMore
#print axioms oneMore_addRows
#print axioms oneMore_tell
#print axioms static_fiveMore

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Characterization
