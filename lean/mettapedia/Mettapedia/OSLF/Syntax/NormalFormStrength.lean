import Mettapedia.OSLF.Syntax.ObservationClosure
import Mathlib.Algebra.Order.Group.Nat

/-!
# One canonical form, three relations, and which of them licenses deciding equality

"Normal form" names three services, and conflating them is how a rewrite system
comes to be described as deciding a theory it does not decide.  They are not
three structures: they are one structure -- a section of a quotient -- indexed by
*which relation the representative is canonical for*.

    SemanticNF E              a representative for each class of `E`
    SyntacticNF rw  =  SemanticNF (EqvGen rw)      canonical for a rewrite
                                                   system's own conversion
    SampleNF S      =  SemanticNF (sampleEq S)     canonical only with respect
                                                   to a finite sample of
                                                   observations

Naming the index is what makes the comparisons statable, because the strictness
results below are statements about *relations* and so survive the collapse
unchanged.  `SemanticNF.transport` carries a section along a two-sided
refinement, and each tier is that lemma at a particular relation.

**Canonicity for conversion does not establish canonicity for an intended
theory.** The conversion index above states the required guarantee; it does not
construct a normalizer. The positive example below proves directed reachability
and uniqueness. The negative half uses that same system with unique
normal forms whose intended theory is strictly coarser -- and strictly coarser
without being the one-point quotient, so that the failure is a fact about this
rewrite system rather than about a degenerate choice of target.

**A sample is weaker again.**  A sample blind to a distinction forces any
representative to collapse it, so a sample-canonical function need not even be a
normal form for the rewriting; the sample has to travel with the representative
rather than be discarded once one is computed.

**What the tier does *not* say.**  Classically every equivalence admits a
section, so `SemanticNF E` is never empty; its content is that a *given*
function is one, which is why the negative results below ask for `N.rep = nf`
rather than for non-existence.  And `rel_iff_rep_eq` is a reduction of the
relation to equality of representatives, not a decision procedure: deciding also
needs the representative computable and equality on the carrier decidable.

The conversion-indexed section does not itself certify directed reachability
or irreducibility. The subtract-four example supplies those separately, and a
different section of the same conversion has reducible representatives. Thus
canonicalization must not be silently used as execution normalization.

Stability is taken from the observation ladder, so the sample tier is indexed by
the same notion of observation the equational layer uses rather than a second
one.
-/

namespace Mettapedia.OSLF.Syntax.NormalFormStrength

open Relation
open Mettapedia.OSLF.Syntax.ObservationClosure

set_option autoImplicit false

universe u

variable {α : Type u}

/-! ## One structure -/

/-- A representative for each class of `E`, shared by `E`-equal elements: a
section of the quotient. -/
structure SemanticNF (E : α → α → Prop) where
  /-- The chosen representative. -/
  rep : α → α
  /-- Each element is related to its representative. -/
  sound : ∀ x, E x (rep x)
  /-- Related elements choose the same one. -/
  complete : ∀ x y, E x y → rep x = rep y

/-- Idempotence follows from the section laws; it is not an additional field. -/
theorem SemanticNF.idempotent {E : α → α → Prop} (N : SemanticNF E) :
    ∀ x, N.rep (N.rep x) = N.rep x :=
  fun x => (N.complete x (N.rep x) (N.sound x)).symm

/-- **The relation reduces to equality of representatives.**  Not yet a decision
procedure: that needs `rep` computable and equality on `α` decidable. -/
theorem SemanticNF.rel_iff_rep_eq {E : α → α → Prop} (hE : Equivalence E)
    (N : SemanticNF E) (x y : α) : E x y ↔ N.rep x = N.rep y := by
  constructor
  · exact N.complete x y
  · intro h
    exact hE.trans (N.sound x) (hE.symm (h ▸ N.sound y))

/-- **And then it is decidable.**  This is what the tier buys, and it is the
step the word "decides" actually names. -/
@[instance_reducible]
def SemanticNF.decidableRel [DecidableEq α] {E : α → α → Prop}
    (hE : Equivalence E) (N : SemanticNF E) : DecidableRel E :=
  fun x y => decidable_of_iff _ (N.rel_iff_rep_eq hE x y).symm

/-- **A section transports along a two-sided refinement.**  Soundness needs the
target relation coarser, completeness needs it finer; the two tiers below are
this lemma at `EqvGen rw` and at `sampleEq S`. -/
def SemanticNF.transport {E F : α → α → Prop} (N : SemanticNF E)
    (hle : ∀ x y, E x y → F x y) (hge : ∀ x y, F x y → E x y) : SemanticNF F where
  rep := N.rep
  sound x := hle _ _ (N.sound x)
  complete x y h := N.complete x y (hge x y h)

/-! ## The two indices that name the weaker services -/

/-- The relation a finite sample of observations induces: indistinguishability
by the sample. -/
def sampleEq (S : List (α → Prop)) : α → α → Prop :=
  fun x y => ∀ P ∈ S, (P x ↔ P y)

/-- A canonical representative for a rewrite system's conversion. Directed
reachability and irreducibility are separate normalization requirements. -/
abbrev SyntacticNF (rw : α → α → Prop) := SemanticNF (EqvGen rw)

/-- Canonical with respect to a sample is a section of the sample's relation. -/
abbrev SampleNF (S : List (α → Prop)) := SemanticNF (sampleEq S)

/-- **A semantic normal form is a sample one** when the sample's observations are
stable under the theory and the sample separates its classes.  The two
hypotheses are exactly the two inclusions between `E` and `sampleEq S`. -/
def SemanticNF.toSample {E : α → α → Prop} (N : SemanticNF E)
    (S : List (α → Prop)) (hS : ∀ P ∈ S, Stable E P)
    (hsep : ∀ x y, sampleEq S x y → E x y) : SampleNF S :=
  N.transport (fun x y h P hP => hS P hP x y h) hsep

/-! ## A rule system whose normal form is not a canonical form

Subtracting four while at least four.  Its conversion is congruence mod four and
`n % 4` is its normal form.  The intended theory is congruence mod two: strictly
coarser, and *not* the one-point quotient, so the failure below is a fact about
this rewrite system rather than about a degenerate target. -/

namespace Coarser

/-- Subtract four. -/
def rw4 : ℕ → ℕ → Prop := fun m n => 4 ≤ m ∧ n = m - 4

/-- Its normal form. -/
def nf4 : ℕ → ℕ := fun n => n % 4

/-- The intended theory: congruence mod two. -/
def intended : ℕ → ℕ → Prop := fun m n => m % 2 = n % 2

theorem intended_equivalence : Equivalence intended where
  refl _ := rfl
  symm h := h.symm
  trans h₁ h₂ := h₁.trans h₂

/-- It is not the one-point quotient, so it is a real target. -/
theorem intended_not_total : ¬ intended 0 1 := by
  intro h
  simp only [intended] at h
  omega

theorem rw4_intended {m n : ℕ} (h : rw4 m n) : intended m n := by
  obtain ⟨h4, rfl⟩ := h
  simp only [intended]
  omega

/-- **The rules are sound for the intended theory**, and this has content: every
conversion step preserves parity. -/
theorem eqvGen_rw4_intended : ∀ m n : ℕ, EqvGen rw4 m n → intended m n := by
  intro m n h
  induction h with
  | rel a b hab => exact rw4_intended hab
  | refl _ => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem rw4_parity {m n : ℕ} (h : rw4 m n) : nf4 m = nf4 n := by
  obtain ⟨h4, rfl⟩ := h
  simp only [nf4]
  omega

/-- The representative is reached by forward rules, not merely conversion. -/
theorem directed_reaches4 : ∀ n : ℕ, ReflTransGen rw4 n (nf4 n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      by_cases h : 4 ≤ n
      · have step : rw4 n (n - 4) := ⟨h, rfl⟩
        have hlt : n - 4 < n := by omega
        have hsame : nf4 (n - 4) = nf4 n := by simp only [nf4]; omega
        exact (ReflTransGen.single step).trans (hsame ▸ ih (n - 4) hlt)
      · have hfix : nf4 n = n := by simp only [nf4]; omega
        simpa only [hfix] using (ReflTransGen.refl : ReflTransGen rw4 n n)

theorem reaches4 (n : ℕ) : EqvGen rw4 n (nf4 n) :=
  EqvGen.reflTransGen_le_eqvGen rw4 _ _ (directed_reaches4 n)

theorem irreducible4_iff (n : ℕ) : (∀ m, ¬ rw4 n m) ↔ n < 4 := by
  constructor
  · intro normal
    by_contra notSmall
    exact normal (n - 4) ⟨Nat.le_of_not_gt notSmall, rfl⟩
  · intro small m step
    exact Nat.not_le_of_gt small step.1

/-- The directed reduction really ends at an irreducible term. -/
theorem nf4_irreducible (n : ℕ) : ∀ m, ¬ rw4 (nf4 n) m :=
  (irreducible4_iff (nf4 n)).mpr (Nat.mod_lt n (by decide))

theorem joins4 : ∀ m n : ℕ, EqvGen rw4 m n → nf4 m = nf4 n := by
  intro m n h
  induction h with
  | rel a b hab => exact rw4_parity hab
  | refl _ => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The rule system does have unique normal forms, hence is canonical for its
own conversion. -/
def syntactic4 : SyntacticNF rw4 where
  rep := nf4
  sound := reaches4
  complete := joins4

/-- Every reachable irreducible has the same result as the normalizer. -/
theorem reachable_irreducible4_unique (n q : ℕ)
    (reached : ReflTransGen rw4 n q) (normal : ∀ m, ¬ rw4 q m) : q = nf4 n := by
  have same := joins4 n q (EqvGen.reflTransGen_le_eqvGen rw4 _ _ reached)
  have fixed : nf4 q = q := Nat.mod_eq_of_lt ((irreducible4_iff q).mp normal)
  exact fixed.symm.trans same.symm

/-- A genuine section of the same conversion with reducible representatives. -/
def shiftedCanonical4 : SyntacticNF rw4 where
  rep n := nf4 n + 4
  sound n := by
    refine EqvGen.trans _ _ _ (reaches4 n) (EqvGen.symm _ _ ?_)
    exact EqvGen.rel _ _ ⟨by omega, by omega⟩
  complete n m equal := congrArg (fun k => k + 4) (joins4 n m equal)

/-- Conversion canonicity alone does not establish irreducibility. -/
theorem shifted_representative_reduces (n : ℕ) :
    rw4 (shiftedCanonical4.rep n) (nf4 n) := by
  constructor <;> simp only [shiftedCanonical4] <;> omega

/-- But it is not complete for the intended theory: two intended-equal numbers
that the rules keep apart. -/
theorem intended_zero_two : intended 0 2 := by simp only [intended]

theorem nf4_separates_zero_two : nf4 0 ≠ nf4 2 := by
  simp only [nf4]
  omega

/-- A representative for the intended theory must identify them. -/
theorem semanticNF_intended_identifies (N : SemanticNF intended) :
    N.rep 0 = N.rep 2 := N.complete 0 2 intended_zero_two

/-- **So the rule system's normal form is not a canonical form for the intended
theory.**  Confluence and termination give unique normal forms and nothing more:
the normal form separates terms the theory identifies, so it is the
representative of no section of the intended quotient -- and the target is a
genuine two-class theory, not the one-point one. -/
theorem nf4_not_semantic_for_intended :
    ¬ ∃ N : SemanticNF intended, N.rep = nf4 := by
  rintro ⟨N, hN⟩
  refine nf4_separates_zero_two ?_
  rw [← hN]
  exact semanticNF_intended_identifies N

end Coarser

/-! ## And a sample is weaker still -/

namespace Sample

open Coarser

/-- A sample that only asks whether a number is zero. -/
def sample2 : List (ℕ → Prop) := [fun n => n = 0]

theorem sample2_blind : sampleEq sample2 1 2 := by
  intro P hP
  simp only [sample2, List.mem_singleton] at hP
  subst hP
  simp

/-- **Any sample normal form collapses `1` and `2`.** -/
theorem sampleNF_conflates (N : SampleNF sample2) : N.rep 1 = N.rep 2 :=
  N.complete 1 2 sample2_blind

/-- While the rule system's own normal form separates them. -/
theorem nf4_separates_one_two : nf4 1 ≠ nf4 2 := by
  simp only [nf4]
  omega

/-- **So a sample-canonical function need not be a normal form for the
rewriting**, and the sample has to travel with the representative rather than be
discarded once one is computed. -/
theorem sampleNF_not_nf4 : ¬ ∃ N : SampleNF sample2, N.rep = nf4 := by
  rintro ⟨N, hN⟩
  refine nf4_separates_one_two ?_
  rw [← hN]
  exact sampleNF_conflates N

end Sample

end Mettapedia.OSLF.Syntax.NormalFormStrength
