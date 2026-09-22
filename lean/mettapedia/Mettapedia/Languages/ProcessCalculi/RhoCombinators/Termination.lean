import Mettapedia.Languages.ProcessCalculi.RhoCombinators.Occupancy

/-!
# Termination without the opener, and the weight the bound needs

Without the opener every reduction sequence is finite, and the bound is a count
of the atoms sitting at the top level.  This module proves that, and fixes the
count.

The natural measure — *the number of non-message atoms* — does not work, and
`nonMessageCount_not_strictly_decreasing` exhibits the rule that defeats it:
the two re-addressing routers and the synchroniser consume themselves and
produce a forwarder, so they replace one non-message atom with another and the
count is unchanged.  Every other rule but the opener's does consume one and
produce none.

`weight` repairs it by charging two for the three atoms that produce a
forwarder and one for every other non-message atom.  Then every rule but the
opener's strictly decreases the weight (`weight_lt_of_step`), and a reduction
sequence is no longer than the weight it starts from
(`chain_length_le_weight`).

The hypotheses are where this connects to the expressiveness lattice: the bound
holds of a term that *occupies a rule-closed point omitting the opener*.
Occupancy is decidable by one traversal (`Occupancy.occ_par`) and reduction
keeps a term inside a rule-closed point (`Occupancy.occ_step`), so the
occupancy check is itself the certificate that reduction from the checked term
terminates — and, being a bound rather than an abstract finiteness claim, it
says in how many steps.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCombinators

open Comb

/-! ## Two counts -/

/-- The number of atoms at the top level that are not messages.  This is the
measure that does not work. -/
def nonMessageCount : Comb → Nat
  | nil => 0
  | par p q => nonMessageCount p + nonMessageCount q
  | mm _ _ => 0
  | dd _ _ _ => 1
  | kk _ => 1
  | fw _ _ => 1
  | bl _ _ => 1
  | br _ _ => 1
  | sy _ _ _ => 1
  | ev _ => 1
  | qq _ _ => 1
  | consPar _ _ _ => 1
  | consMsg _ _ _ => 1
  | consDup _ _ _ _ => 1
  | consSyn _ _ _ _ => 1

/-- **The weight.**  Two for the atoms whose rule produces a forwarder, one for
every other non-message atom, nothing for a message.  A message's payload is
not charged, so the weight is a property of the top level only. -/
def weight : Comb → Nat
  | nil => 0
  | par p q => weight p + weight q
  | mm _ _ => 0
  | dd _ _ _ => 1
  | kk _ => 1
  | fw _ _ => 1
  | bl _ _ => 2
  | br _ _ => 2
  | sy _ _ _ => 2
  | ev _ => 1
  | qq _ _ => 1
  | consPar _ _ _ => 1
  | consMsg _ _ _ => 1
  | consDup _ _ _ _ => 1
  | consSyn _ _ _ _ => 1

/-- Structural congruence preserves the weight, the monoid laws being exactly
the laws of addition the weight uses. -/
theorem weight_cong {p q : Comb} (h : Cong p q) : weight p = weight q := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | parNil p => simp [weight]
  | parComm p q => simp [weight, Nat.add_comm]
  | parAssoc p q r => simp [weight, Nat.add_assoc]
  | parLeft q _ ih => simp [weight, ih]
  | parRight p _ ih => simp [weight, ih]

/-! ## The natural measure fails -/

/-- **A rule that leaves the non-message atom count alone.**  The outward
binder consumes itself and produces a forwarder, so one non-message atom
becomes one non-message atom.  The same happens for the inward binder and the
synchroniser, so a bound on reduction length cannot be the count of
non-message atoms. -/
theorem nonMessageCount_not_strictly_decreasing :
    ∃ p q : Comb, Step Cong p q ∧ nonMessageCount q = nonMessageCount p := by
  refine ⟨par (br nil nil) (mm nil nil), fw nil nil, ?_, by decide⟩
  exact Step.ofMinus (StepMinus.bindOut nil nil (Cong.refl nil))

/-- And likewise for the inward binder. -/
theorem nonMessageCount_not_strictly_decreasing_bindIn :
    ∃ p q : Comb, Step Cong p q ∧ nonMessageCount q = nonMessageCount p := by
  refine ⟨par (bl nil nil) (mm nil nil), fw nil nil, ?_, by decide⟩
  exact Step.ofMinus (StepMinus.bindIn nil nil (Cong.refl nil))

/-- And for the synchroniser. -/
theorem nonMessageCount_not_strictly_decreasing_sync :
    ∃ p q : Comb, Step Cong p q ∧ nonMessageCount q = nonMessageCount p := by
  refine ⟨par (sy nil nil nil) (mm nil nil), fw nil nil, ?_, by decide⟩
  exact Step.ofMinus (StepMinus.synchronise nil nil nil (Cong.refl nil))

/-! ## The weight strictly decreases -/

/-- Occupancy of a point omitting the opener rules out the opening rule, which
is the one rule whose right-hand side is an arbitrary process. -/
theorem not_occ_ev {admitted : Finset Shape} (noOpener : Shape.ev ∉ admitted)
    {a : Comb} (occupied : Occ admitted (ev a)) : False := by
  cases occupied with
  | ev shape _ => exact noOpener shape

theorem weight_lt_of_stepMinus {admitted : Finset Shape} (noOpener : Shape.ev ∉ admitted)
    {p q : Comb} (occupied : Occ admitted p) (step : StepMinus Cong p q) :
    weight q < weight p := by
  induction step with
  | duplicate b c v _ => simp [weight]
  | discard v _ => simp [weight]
  | forward b v _ => simp [weight]
  | bindOut b v _ => simp [weight]
  | bindIn b v _ => simp [weight]
  | synchronise b c v _ => simp [weight]
  | opening p _ =>
      exact absurd ((occ_par _ _ _).mp occupied).1 (fun h => not_occ_ev noOpener h)
  | release b p _ => simp [weight]
  | parLeft r _ ih =>
      have parts := (occ_par _ _ _).mp occupied
      simp only [weight]
      exact Nat.add_lt_add_right (ih parts.1) _
  | congruent hc₁ _ hc₂ ih =>
      rw [weight_cong hc₁, ← weight_cong hc₂]
      exact ih (occ_cong hc₁ occupied)

/-- **Every rule but the opener's strictly decreases the weight.**  The three
atoms that produce a forwarder pay two and leave one behind; every other rule
consumes a non-message atom and produces only messages. -/
theorem weight_lt_of_step {admitted : Finset Shape} (noOpener : Shape.ev ∉ admitted)
    {p q : Comb} (occupied : Occ admitted p) (step : Step Cong p q) :
    weight q < weight p := by
  induction step with
  | ofMinus minus => exact weight_lt_of_stepMinus noOpener occupied minus
  | buildPar c p q _ _ => simp [weight]
  | buildMsg c u v _ _ => simp [weight]
  | buildDup e p q r _ _ _ => simp [weight]
  | buildSyn e p q r _ _ _ => simp [weight]
  | parLeft r _ ih =>
      have parts := (occ_par _ _ _).mp occupied
      simp only [weight]
      exact Nat.add_lt_add_right (ih parts.1) _
  | congruent hc₁ _ hc₂ ih =>
      rw [weight_cong hc₁, ← weight_cong hc₂]
      exact ih (occ_cong hc₁ occupied)

/-! ## The bound -/

/-- A reduction sequence of a stated length. -/
inductive Chain : Comb → Nat → Prop where
  | nil (p : Comb) : Chain p 0
  | cons {p q : Comb} {n : Nat} : Step Cong p q → Chain q n → Chain p (n + 1)

/-- **Reduction terminates, with a bound.**  From a term occupying a
rule-closed point that omits the opener, no reduction sequence is longer than
the term's weight.  So the occupancy check on that point is the certificate
that reduction from the checked term stops, and it says when. -/
theorem chain_length_le_weight {admitted : Finset Shape}
    (closed : RuleClosed admitted) (noOpener : Shape.ev ∉ admitted)
    {p : Comb} {n : Nat} (occupied : Occ admitted p) (chain : Chain p n) :
    n ≤ weight p := by
  induction chain with
  | nil p => exact Nat.zero_le _
  | cons step rest ih =>
      have next := occ_step closed occupied step
      have drop := weight_lt_of_step noOpener occupied step
      exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (ih next) drop)

/-- The opener is what the bound excludes, and it is excluded for a reason: its
right-hand side is an arbitrary process, so nothing about the redex bounds what
replaces it. -/
theorem opener_unbounds {a p : Comb} :
    StepMinus Cong (par (ev a) (mm a p)) p :=
  StepMinus.opening p (Cong.refl a)

/-! ## Controls -/

namespace TerminationControls

open Controls (openerPoint)

/-- A point of the lattice omitting the opener, and closed under reduction. -/
def boundedPoint : Finset Shape :=
  latticePoint ∅ {Shape.consPar}

theorem boundedPoint_ruleClosed : RuleClosed boundedPoint := by decide

theorem boundedPoint_omits_opener : Shape.ev ∉ boundedPoint := by decide

/-- The weight charges the outward binder two and the forwarder it becomes
one, which is the whole content of the repair. -/
theorem weight_binder_exceeds_forwarder :
    weight (br nil nil) = 2 ∧ weight (fw nil nil) = 1 := by
  exact ⟨by decide, by decide⟩

/-- The two counts disagree exactly there. -/
theorem counts_disagree_on_binder :
    nonMessageCount (br nil nil) = 1 ∧ weight (br nil nil) = 2 := by
  exact ⟨by decide, by decide⟩

/-- A relay occupying the bounded point admits no sequence longer than its
weight. -/
theorem relay_bounded {n : Nat}
    (chain : Chain (par (br nil nil) (mm nil nil)) n) : n ≤ 2 := by
  have occupied : Occ boundedPoint (par (br nil nil) (mm nil nil)) := by decide
  have bound := chain_length_le_weight boundedPoint_ruleClosed
    boundedPoint_omits_opener occupied chain
  simpa [weight] using bound

end TerminationControls

end Mettapedia.Languages.ProcessCalculi.RhoCombinators

#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.weight_cong
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.nonMessageCount_not_strictly_decreasing
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.weight_lt_of_step
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.chain_length_le_weight
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.TerminationControls.relay_bounded
