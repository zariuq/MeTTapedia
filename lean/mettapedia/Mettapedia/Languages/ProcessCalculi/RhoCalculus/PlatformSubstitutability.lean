import Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformPresentation
import Mettapedia.OSLF.Framework.SubstitutabilityTheorem1

/-!
# Substitutability parity on the platform, and the logical metric

Two halves, and they behave differently under a change of enumeration.

**Parity.**  Theorem 1's two sides — behavioural equivalence and sameness of
native types — are related on the platform presentation's own step relation.
The forward direction holds outright.  The converse is the image-finite
instance, and its two hypotheses are not on the same footing: the platform's
successors are computed into a list, so forward image-finiteness is a theorem
rather than an assumption, while backward image-finiteness is not supplied by
anything the platform provides — and is not merely unproved.  The step relation
here is visibly many-to-one: a continuation that ignores what it receives sends
every choice of transmitted value to the same successor, and
`Backward.distinct_sources_one_target` exhibits two such sources.  So the
converse is stated as the conditional it is, with the condition named, and it is
not instantiated at this presentation.

**The metric.**  A logical metric ranks a pair by the first formula of an
enumeration that separates them.  The relation it induces — being separated at
all — does not depend on the enumeration, and is proved not to.  The rank does,
and is proved to: the same two formulas listed in the other order give the same
pair a different rank.  So the *equivalence* Theorem 1 is about is an invariant
of the logic, while any metric refining it is an artefact of how the formulas
were listed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformSubstitutability

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.DistinctionGraph
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformPresentation

/-! ## The platform's step relation -/

/-- The platform's one-step relation at a fixed fuel and relation environment:
a successor is one the engine computes. -/
def platformStep (relEnv : RelationEnv) (arities : List Nat) (fuel : Nat)
    (source target : Pattern) : Prop :=
  target ∈ rewriteAt (engineBasePremises relEnv) (rhoPlatform arities) fuel source

/-- **Forward image-finiteness is free here.**  The platform computes its
successors into a list, so the successor set of any term is finite — no
hypothesis, and no appeal to a property of rho. -/
theorem platformStep_imageFinite (relEnv : RelationEnv) (arities : List Nat)
    (fuel : Nat) (source : Pattern) :
    Set.Finite {target : Pattern | platformStep relEnv arities fuel source target} :=
  List.finite_toSet _

/-! ## Theorem 1 on the platform -/

/-- **Parity, forward.**  On the platform's own step relation, behavioural
equivalence implies sameness of native types.  Unconditional. -/
theorem platform_substitutability_forward (relEnv : RelationEnv) (arities : List Nat)
    (fuel : Nat) (I : Mettapedia.OSLF.Formula.AtomSem) {source target : Pattern}
    (equivalent :
      theorem1_behaviorEq (platformStep relEnv arities fuel) I source target) :
    theorem1_sameNativeTypes (platformStep relEnv arities fuel) I source target :=
  theorem1_substitutability_forward equivalent

/-- **Parity, both ways, with the one hypothesis that is not free.**  Forward
image-finiteness is supplied by the platform itself; backward image-finiteness
is the hypothesis, and it is named rather than assumed quietly. -/
theorem platform_substitutability_of_predFinite (relEnv : RelationEnv)
    (arities : List Nat) (fuel : Nat) (I : Mettapedia.OSLF.Formula.AtomSem)
    (predFinite : ∀ target : Pattern,
      Set.Finite {source : Pattern | platformStep relEnv arities fuel source target}) :
    Theorem1SubstitutabilityEquiv (platformStep relEnv arities fuel) I :=
  theorem1_substitutability_imageFinite
    (platformStep_imageFinite relEnv arities fuel) predFinite

/-! ### Why the backward hypothesis is not available here -/

namespace Backward

open Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformPresentation.Guard

/-- A continuation that discards what it receives. -/
def discarding : Pattern := .lambda none (.apply stopDeclaration.label [])

/-- Two boards differing only in a transmitted value. -/
def sourceWithP : Pattern := .collection .hashBag
  [ .apply (joinLabel 2) [channelA, channelB, discarding]
  , .apply outLabel [channelA, valueP]
  , .apply outLabel [channelB, valueQ] ] none

def sourceWithQ : Pattern := .collection .hashBag
  [ .apply (joinLabel 2) [channelA, channelB, discarding]
  , .apply outLabel [channelA, valueQ]
  , .apply outLabel [channelB, valueQ] ] none

/-- They are different processes. -/
theorem sources_distinct : sourceWithP ≠ sourceWithQ := by decide

/-- **And they have the same successor.**  The value the join transmits is
consumed by a continuation that discards it, so it cannot be recovered from the
result.  Nothing about the platform bounds how many sources share a successor,
which is exactly what backward image-finiteness would have to assert. -/
theorem distinct_sources_one_target :
    rewriteAt (engineBasePremises admitsOnce) (rhoPlatform [2]) 6 sourceWithP =
      rewriteAt (engineBasePremises admitsOnce) (rhoPlatform [2]) 6 sourceWithQ := by
  decide +kernel

/-- Both do step, so this is a genuine collision rather than two dead ends. -/
theorem sources_step :
    (rewriteAt (engineBasePremises admitsOnce) (rhoPlatform [2]) 6 sourceWithP).length = 1 := by
  decide +kernel

end Backward

/-! ## Parity, met

Theorem 1's converse needs backward image-finiteness, which this presentation's
step relation does not have: `Backward` above exhibits two distinct sources with
one successor, and nothing bounds how many share it.  On a **bounded** domain
both directions hold for the same reason — a subset of a finite set is finite —
so the parity is met there rather than left conditional.  That is not a
weakening chosen for convenience: a reachable domain is what a running system
has, and `CostCanonicalReachableDomain` is the tree's carrier for exactly that
idea. -/

/-- The platform's step relation, confined to a finite domain. -/
def boundedStep (relEnv : RelationEnv) (arities : List Nat) (fuel : Nat)
    (domain : List Pattern) (source target : Pattern) : Prop :=
  source ∈ domain ∧ target ∈ domain ∧ platformStep relEnv arities fuel source target

/-- Forward image-finiteness, because successors stay in the domain. -/
theorem boundedStep_imageFinite (relEnv : RelationEnv) (arities : List Nat) (fuel : Nat)
    (domain : List Pattern) (source : Pattern) :
    Set.Finite {target : Pattern | boundedStep relEnv arities fuel domain source target} := by
  refine Set.Finite.subset (List.finite_toSet domain) ?_
  rintro target ⟨-, member, -⟩
  exact member

/-- And backward, for the same reason — which is what the unrestricted relation
cannot supply. -/
theorem boundedStep_predFinite (relEnv : RelationEnv) (arities : List Nat) (fuel : Nat)
    (domain : List Pattern) (target : Pattern) :
    Set.Finite {source : Pattern | boundedStep relEnv arities fuel domain source target} := by
  refine Set.Finite.subset (List.finite_toSet domain) ?_
  rintro source ⟨member, -, -⟩
  exact member

/-- **Parity, both directions, with nothing assumed.**  Behavioural equivalence
and sameness of native types coincide on the platform's step relation confined
to a finite domain. -/
theorem platform_substitutability_bounded (relEnv : RelationEnv) (arities : List Nat)
    (fuel : Nat) (domain : List Pattern) (I : Mettapedia.OSLF.Formula.AtomSem) :
    Theorem1SubstitutabilityEquiv (boundedStep relEnv arities fuel domain) I :=
  theorem1_substitutability_imageFinite
    (boundedStep_imageFinite relEnv arities fuel domain)
    (boundedStep_predFinite relEnv arities fuel domain)

/-! ### And the bounded relation is not empty -/

namespace Bounded

open Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformPresentation.Guard

/-- What the board becomes. -/
def successor : Pattern :=
  .collection .hashBag
    [.apply quoteLabel [.apply (tupleLabel 2) [valueP, valueQ]]] none

/-- The reachable domain: the board and its successor. -/
def domain : List Pattern := [board, successor]

theorem board_steps :
    boundedStep admitsOnce [2] 6 domain board successor := by
  refine ⟨by decide, by decide, ?_⟩
  show successor ∈ rewriteAt (engineBasePremises admitsOnce) (rhoPlatform [2]) 6 board
  decide +kernel

/-- **So parity holds on a domain that actually carries a reaction.** -/
theorem parity (I : Mettapedia.OSLF.Formula.AtomSem) :
    Theorem1SubstitutabilityEquiv (boundedStep admitsOnce [2] 6 domain) I :=
  platform_substitutability_bounded admitsOnce [2] 6 domain I

end Bounded

/-! ## The logical metric

A metric refining logical equivalence has to say *how far apart* two terms are,
and the usual way is to ask which formula separates them first.  "First" is
relative to a listing, and that is the whole issue. -/

/-- The rank of a pair under an enumeration: the least index below the bound
whose formula separates them, if any.  `separates` is the pair's separation
test, abstracted so the statement does not depend on how it is computed. -/
def logicalRank (separates : Mettapedia.OSLF.Formula.OSLFFormula → Bool)
    (enumeration : Nat → Mettapedia.OSLF.Formula.OSLFFormula) (bound : Nat) :
    Option Nat :=
  (List.range bound).find? fun index => separates (enumeration index)

/-- A pair is ranked exactly when some listed formula separates it. -/
theorem logicalRank_isSome_iff
    (separates : Mettapedia.OSLF.Formula.OSLFFormula → Bool)
    (enumeration : Nat → Mettapedia.OSLF.Formula.OSLFFormula) (bound : Nat) :
    (logicalRank separates enumeration bound).isSome = true ↔
      ∃ index, index < bound ∧ separates (enumeration index) = true := by
  rw [logicalRank, List.find?_isSome]
  simp only [List.mem_range]

/-- **The relation is enumeration-independent.**  Two listings of the same
formulas rank exactly the same pairs, whatever order they use — so *being*
logically distinguishable is a property of the logic. -/
theorem logicalRank_isSome_congr
    {separates : Mettapedia.OSLF.Formula.OSLFFormula → Bool}
    {first second : Nat → Mettapedia.OSLF.Formula.OSLFFormula} {bound : Nat}
    (forward : ∀ index, index < bound →
      ∃ image, image < bound ∧ second image = first index)
    (backward : ∀ index, index < bound →
      ∃ image, image < bound ∧ first image = second index) :
    (logicalRank separates first bound).isSome =
      (logicalRank separates second bound).isSome := by
  have equivalence :
      (∃ index, index < bound ∧ separates (first index) = true) ↔
        ∃ index, index < bound ∧ separates (second index) = true := by
    constructor
    · rintro ⟨index, bounded, separated⟩
      obtain ⟨image, imageBounded, sameFormula⟩ := forward index bounded
      exact ⟨image, imageBounded, by rw [sameFormula]; exact separated⟩
    · rintro ⟨index, bounded, separated⟩
      obtain ⟨image, imageBounded, sameFormula⟩ := backward index bounded
      exact ⟨image, imageBounded, by rw [sameFormula]; exact separated⟩
  have iffFirst := logicalRank_isSome_iff separates first bound
  have iffSecond := logicalRank_isSome_iff separates second bound
  cases hfirst : (logicalRank separates first bound).isSome with
  | false =>
      cases hsecond : (logicalRank separates second bound).isSome with
      | false => rfl
      | true =>
          exact absurd (iffFirst.mpr (equivalence.mpr (iffSecond.mp hsecond)))
            (by simp [hfirst])
  | true =>
      cases hsecond : (logicalRank separates second bound).isSome with
      | false =>
          exact absurd (iffSecond.mpr (equivalence.mp (iffFirst.mp hfirst)))
            (by simp [hsecond])
      | true => rfl

/-! ### And the rank is not

The same two formulas, listed the other way round.  One of them separates the
pair and the other does not, so the first index that separates is different —
and a metric built on that index differs with it. -/

namespace Enumeration

/-- A formula that does not separate the pair. -/
def quiet : Mettapedia.OSLF.Formula.OSLFFormula := .top

/-- A formula that does. -/
def loud : Mettapedia.OSLF.Formula.OSLFFormula := .atom "separating"

/-- The separation test of the pair in question. -/
def separates : Mettapedia.OSLF.Formula.OSLFFormula → Bool :=
  fun formula => formula == loud

/-- One listing. -/
def listedQuietFirst : Nat → Mettapedia.OSLF.Formula.OSLFFormula
  | 0 => quiet
  | 1 => loud
  | _ => quiet

/-- The other, with the two swapped. -/
def listedLoudFirst : Nat → Mettapedia.OSLF.Formula.OSLFFormula
  | 0 => loud
  | 1 => quiet
  | _ => quiet

/-- The two listings list the same formulas. -/
theorem same_formulas :
    (∀ index, index < 2 → ∃ image, image < 2 ∧ listedLoudFirst image = listedQuietFirst index) ∧
      ∀ index, index < 2 → ∃ image, image < 2 ∧ listedQuietFirst image = listedLoudFirst index := by
  constructor
  · intro index bounded
    interval_cases index
    · exact ⟨1, by norm_num, rfl⟩
    · exact ⟨0, by norm_num, rfl⟩
  · intro index bounded
    interval_cases index
    · exact ⟨1, by norm_num, rfl⟩
    · exact ⟨0, by norm_num, rfl⟩

/-- **So they rank the same pairs** — the relation does not move. -/
theorem same_pairs_ranked :
    (logicalRank separates listedQuietFirst 2).isSome =
      (logicalRank separates listedLoudFirst 2).isSome :=
  logicalRank_isSome_congr same_formulas.1 same_formulas.2

/-- **But they give different ranks.**  A metric refining logical equivalence is
therefore an artefact of the listing, not an invariant of the logic. -/
theorem rank_depends_on_enumeration :
    logicalRank separates listedQuietFirst 2 ≠
      logicalRank separates listedLoudFirst 2 := by
  decide

/-- Concretely: one listing finds the separating formula second, the other
finds it first. -/
theorem ranks_computed :
    logicalRank separates listedQuietFirst 2 = some 1 ∧
      logicalRank separates listedLoudFirst 2 = some 0 := by
  constructor <;> decide

end Enumeration

/-! ## The metric, computed

`logicalRank` above takes its separation test and its enumeration as parameters,
which is right for the invariance statements but leaves the metric abstract: no
distance between two actual terms of this presentation is computed by it.  Here
both parameters are supplied by the presentation itself, and a rank is computed.

The separation test is read off the semantics rather than posited beside it.  At
an atomic formula the semantics *is* the atom reading, so a decidable atom
reading decides separation exactly — in both directions, which a bounded
checker does not give, since it is sound for satisfaction and silent otherwise.
Keeping the enumeration atomic is what buys that exactness, and it is the reason
the catalogue below is a list of constructor names rather than of formulas. -/

namespace ConcreteMetric

open Mettapedia.OSLF.Formula

/-- A decidable atom reading: the atom names a declared constructor, and it holds
of a term headed by it. -/
def headedBy (label : String) : Pattern → Bool
  | .apply name _ => name == label
  | _ => false

/-- The atom reading, as the logic's own atom semantics. -/
def atomSem : AtomSem := fun name term => headedBy name term = true

/-- **The semantics decides an atom exactly**, which is what makes the test below
derived rather than posited. -/
theorem sem_atom_iff (step : Pattern → Pattern → Prop) (name : String) (term : Pattern) :
    sem step atomSem (.atom name) term ↔ headedBy name term = true :=
  Iff.rfl

/-- **The separation test, read off the semantics.** -/
def separates (first second : Pattern) : OSLFFormula → Bool
  | .atom name => headedBy name first != headedBy name second
  | _ => false

/-- And it is sound both ways: when it fires, one term satisfies the formula in
the logic and the other does not. -/
theorem separates_sound (step : Pattern → Pattern → Prop) {first second : Pattern}
    {name : String} (fires : separates first second (.atom name) = true) :
    (sem step atomSem (.atom name) first ∧ ¬ sem step atomSem (.atom name) second) ∨
      (sem step atomSem (.atom name) second ∧ ¬ sem step atomSem (.atom name) first) := by
  simp only [separates, bne_iff_ne, ne_eq] at fires
  rcases hfirst : headedBy name first with _ | _ <;>
    rcases hsecond : headedBy name second with _ | _ <;>
      simp only [hfirst, hsecond] at fires ⊢ <;>
        simp_all [sem_atom_iff]

/-- The catalogue: the presentation's own formers, in a fixed order. -/
def catalogue : List String :=
  [quoteLabel, outLabel, stopDeclaration.label, parDeclaration.label]

/-- The enumeration the rank is taken against. -/
def enumeration : Nat → OSLFFormula :=
  fun index => .atom (catalogue.getD index stopDeclaration.label)

/-- The same catalogue with its first two entries exchanged. -/
def swappedCatalogue : List String :=
  [outLabel, quoteLabel, stopDeclaration.label, parDeclaration.label]

def swappedEnumeration : Nat → OSLFFormula :=
  fun index => .atom (swappedCatalogue.getD index stopDeclaration.label)

/-! ### Two terms of this presentation -/

/-- The terminated process. -/
def stopTerm : Pattern := .apply stopDeclaration.label []

/-- An output on the terminated process's quote. -/
def outTerm : Pattern :=
  .apply outLabel [.apply quoteLabel [stopTerm], stopTerm]

/-- **A computed rank.**  The two terms are separated, and the enumeration says
where: the first listed former that tells them apart. -/
theorem rank_computed :
    logicalRank (separates outTerm stopTerm) enumeration 4 = some 1 := by
  decide

/-- **And the rank moves with the listing**, while the pair stays separated —
the abstract statements above, met at two terms of this presentation. -/
theorem swapped_rank_computed :
    logicalRank (separates outTerm stopTerm) swappedEnumeration 4 = some 0 := by
  decide

theorem rank_depends_on_catalogue :
    logicalRank (separates outTerm stopTerm) enumeration 4 ≠
      logicalRank (separates outTerm stopTerm) swappedEnumeration 4 := by
  decide

/-- The two listings list the same formulas, so the *relation* does not move. -/
theorem catalogues_agree :
    (∀ index, index < 4 → ∃ image, image < 4 ∧
        swappedEnumeration image = enumeration index) ∧
      ∀ index, index < 4 → ∃ image, image < 4 ∧
        enumeration image = swappedEnumeration index := by
  constructor <;> intro index bounded <;> interval_cases index
  · exact ⟨1, by norm_num, rfl⟩
  · exact ⟨0, by norm_num, rfl⟩
  · exact ⟨2, by norm_num, rfl⟩
  · exact ⟨3, by norm_num, rfl⟩
  · exact ⟨1, by norm_num, rfl⟩
  · exact ⟨0, by norm_num, rfl⟩
  · exact ⟨2, by norm_num, rfl⟩
  · exact ⟨3, by norm_num, rfl⟩

theorem same_pairs_ranked :
    (logicalRank (separates outTerm stopTerm) enumeration 4).isSome =
      (logicalRank (separates outTerm stopTerm) swappedEnumeration 4).isSome :=
  logicalRank_isSome_congr catalogues_agree.1 catalogues_agree.2

/-- **And the separation is one the logic makes**: the formula the rank points
at holds at one term and fails at the other, in the semantics rather than in the
test. -/
theorem rank_witness_separates (step : Pattern → Pattern → Prop) :
    (sem step atomSem (enumeration 1) outTerm ∧
        ¬ sem step atomSem (enumeration 1) stopTerm) ∨
      (sem step atomSem (enumeration 1) stopTerm ∧
        ¬ sem step atomSem (enumeration 1) outTerm) :=
  separates_sound step (by decide)

end ConcreteMetric

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformSubstitutability
