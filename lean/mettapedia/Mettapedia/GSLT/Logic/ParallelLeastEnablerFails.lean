import Mettapedia.GSLT.Logic.AdmissibleContextCongruence
import Mathlib.Algebra.Order.Group.Multiset
import Mathlib.Data.Multiset.UnionInter

/-!
# Parallel contexts do not compose least enablers

`AdmissibleContextCongruence` derives a class-relative congruence from one
obligation on a theory: `LeastEnablerComposes`, that being a least enabler at
`C[p]` is being a least enabler at `p` after composition with `C`.  For rho the
contexts of interest are parallel remainders, and the obligation was left open
with a redex-relative-pushout construction named as what would discharge it.

It cannot be discharged, and the reason is structural rather than a gap in any
construction.  A parallel context is a bag of siblings, and composing with one
*adds* siblings.  A least enabler at `C[p]` is the smallest bag that, together
with `C`, completes a redex; composing it with `C` afterwards re-adds every
sibling of `C`, including the ones the rule never needed.  The result is not
least at `p`, because the bag without those siblings already enables.

This module exhibits that, at the smallest theory where the phenomenon exists:
bags of naturals, one rule, firing when a `0` and a `1` are present.  The
counterexample is a genuine parallel context — an unrelated sibling — so it is
not avoided by restricting the admissible class to rho's contexts, which include
exactly such siblings.

**Two different failures.**  `RedexRelativeEnabling` already shows this
interface failing another way: a source completed in two incomparable ways has
no least enabling context at all, so the labelled system is blind there.  That
leaves open the reading that `LeastEnablerComposes` is true wherever least
enablers exist, and merely hard to prove.  It is not.  Here they exist at every
source, by `least_enabler_exists`, and the obligation is still false.

**What this means for the congruence.**  The congruence rho needs is not lost;
it is obtained by the other road, through idem pushouts
(`RedexRelativeCongruence.ipoBisimilar_comp`, and for parallel contexts
`BagRelativePushout.congruence`), which asks a square to be a pushout in a slice
rather than asking least enablers to compose.  What this module closes is the
question of whether the `MinimalEnablingContext` obligation could be discharged
for parallel contexts.  It could not, and the reason is not a missing
construction.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ParallelLeastEnablerFails

open Mettapedia.GSLT
open Mettapedia.GSLT.MinimalEnablingContext
open Mettapedia.GSLT.AdmissibleContextCongruence

/-! ## The smallest theory with a parallel context -/

/-- The two tokens a firing consumes. -/
def redex : Multiset ℕ := {0, 1}

/-- A sibling the rule never needs. -/
def bystander : Multiset ℕ := {2}

theorem redex_le_iff (bag : Multiset ℕ) :
    redex ≤ bag ↔ 1 ≤ bag.count 0 ∧ 1 ≤ bag.count 1 := by
  rw [Multiset.le_iff_count]
  constructor
  · intro counts
    exact ⟨by simpa [redex] using counts 0, by simpa [redex] using counts 1⟩
  · rintro ⟨zeroCount, oneCount⟩ token
    match token with
    | 0 => simpa [redex] using zeroCount
    | 1 => simpa [redex] using oneCount
    | (_ + 2) => simp [redex]

/-- Bags of tokens, with one rule: when a `0` and a `1` are both present they
are consumed together. -/
@[reducible] def bagGSLT : GSLT where
  Term := Multiset ℕ
  equations := ⟨Eq, ⟨fun _ => rfl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun source target => redex ≤ source ∧ target = source - redex
  rewrites_resp_left := by
    rintro source source' target same ⟨present, shape⟩
    exact ⟨source' - redex, ⟨same ▸ present, rfl⟩,
      show target = source' - redex by rw [shape, same]⟩
  rewrites_resp_right := by
    rintro source target target' step same
    exact same ▸ step

/-- Its contexts are the bags of siblings, composed by union.  Every plug law
is an equation of the monoid, so none of them carries a side condition — which
is what makes this the fair test of the obligation. -/
@[reducible] def bagRules : MinimalEnablingContext.ContextualRules bagGSLT where
  Context := Multiset ℕ
  identity := 0
  compose := fun outer inner => outer + inner
  plug := fun context term => context + term
  plug_identity := fun term => zero_add term
  plug_compose := fun outer inner term => add_assoc outer inner term
  plug_resp := by rintro context left right same; exact congrArg _ same
  Rule := Unit
  fires := fun _ source target => redex ≤ source ∧ target = source - redex
  fires_resp_left := by
    rintro rule left right target same ⟨present, shape⟩
    exact ⟨right - redex, ⟨same ▸ present, rfl⟩,
      show target = right - redex by rw [shape, same]⟩
  fires_resp_right := by
    rintro rule source target target' step same
    exact same ▸ step
  fires_step := fun step => step

/-- Every bag of siblings is admissible: a parallel remainder is exactly what
rho's class admits, so the counterexample is not avoided by narrowing it. -/
def everyContext : AdmissibleClass bagRules where
  Admissible := fun _ => True
  identity_mem := trivial
  compose_mem := fun _ _ => trivial

/-! ## Factoring is containment -/

theorem factors_iff {inner outer : Multiset ℕ} :
    bagRules.Factors inner outer ↔ inner ≤ outer := by
  constructor
  · rintro ⟨residual, law⟩
    have atEmpty : outer + (0 : Multiset ℕ) = residual + (inner + 0) := law 0
    rw [add_zero, add_zero] at atEmpty
    exact atEmpty ▸ Multiset.le_add_left inner residual
  · intro below
    obtain ⟨residual, shape⟩ := Multiset.le_iff_exists_add.mp below
    refine ⟨residual, fun term => ?_⟩
    show outer + term = residual + (inner + term)
    rw [shape, add_comm inner residual, add_assoc]

/-! ## Least enablers exist here, everywhere

`RedexRelativeEnabling.no_least_enabler` exhibits the other failure of this
interface: a source completed in two incomparable ways has no least enabling
context at all.  That one could be read as a theory too poor to carry the
universal property.  This one cannot: below, *every* source attains it, and the
obligation is false anyway. -/

/-- The tokens a source is missing.  It enables, and it is below every context
that enables, so it is the least enabler — at every source, with no hypothesis. -/
theorem least_enabler_exists (source : Multiset ℕ) :
    bagRules.IsLeastEnabler (redex - source) source () := by
  constructor
  · refine ⟨(redex - source) + source - redex, ?_, rfl⟩
    show redex ≤ (redex - source) + source
    exact le_tsub_add
  · rintro other ⟨target, present, -⟩
    refine factors_iff.mpr (tsub_le_iff_right.mpr ?_)
    exact present

/-! ## The failure

The redex is least beside a bystander, because the bystander supplies neither
token.  Composed with the bystander it is no longer least at the empty bag,
because the redex alone already enables there. -/

theorem redex_enables_empty : bagRules.Enables redex 0 () := by
  refine ⟨redex + 0 - redex, ?_, rfl⟩
  show redex ≤ redex + 0
  exact Multiset.le_add_right redex 0

/-- **The redex is a least enabler beside a bystander.** -/
theorem redex_isLeastEnabler_beside_bystander :
    bagRules.IsLeastEnabler redex (bagRules.plug bystander 0) () := by
  constructor
  · refine ⟨redex + (bystander + 0) - redex, ?_, rfl⟩
    exact Multiset.le_add_right redex (bystander + 0)
  · rintro other ⟨target, present, -⟩
    refine factors_iff.mpr ?_
    have present' : redex ≤ other + bystander := by
      have shape : other + (bystander + 0) = other + bystander := by rw [add_zero]
      exact shape ▸ present
    obtain ⟨zeroCount, oneCount⟩ := (redex_le_iff _).mp present'
    refine (redex_le_iff other).mpr ⟨?_, ?_⟩
    · simpa [bystander] using zeroCount
    · simpa [bystander] using oneCount

/-- **But composed with that bystander it is not least at the empty bag**, since
the redex alone already enables there and the composite is strictly larger. -/
theorem composed_not_isLeastEnabler :
    ¬ bagRules.IsLeastEnabler (bagRules.compose redex bystander) 0 () := by
  rintro ⟨-, least⟩
  have contained : redex + bystander ≤ redex :=
    factors_iff.mp (least redex redex_enables_empty)
  have counts := (Multiset.le_iff_count).mp contained 2
  simp [redex, bystander] at counts

/-- **So least enablers do not compose for parallel contexts.**  The obligation
`AdmissibleContextCongruence` derives its congruence from cannot be discharged
here.  The class being maximal does not by itself rule out sub-classes -- and
does not: `AdmissibleContextCongruence.identityOnly_composes` discharges the
obligation at the class `{identity}`.  What rules out rho's class is that it
contains parallel remainders, and the bystander below is one. -/
theorem leastEnablerComposes_fails : ¬ everyContext.LeastEnablerComposes := by
  intro composes
  exact composed_not_isLeastEnabler
    ((composes trivial trivial).mp redex_isLeastEnabler_beside_bystander)

/-- **And the phenomenon is exactly the re-added sibling.**  Without the
bystander the two statements agree: the redex is least at the empty bag both
before and after composing with the identity context. -/
theorem identity_composes :
    bagRules.IsLeastEnabler redex (bagRules.plug 0 0) () ↔
      bagRules.IsLeastEnabler (bagRules.compose redex 0) 0 () := by
  have plugged : bagRules.plug 0 (0 : Multiset ℕ) = 0 := by
    show (0 : Multiset ℕ) + 0 = 0
    rw [add_zero]
  have composed : bagRules.compose redex (0 : Multiset ℕ) = redex := by
    show redex + 0 = redex
    rw [add_zero]
  rw [plugged, composed]

end Mettapedia.GSLT.ParallelLeastEnablerFails
