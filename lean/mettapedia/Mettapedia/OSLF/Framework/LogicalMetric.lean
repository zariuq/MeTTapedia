import Mathlib.Topology.MetricSpace.PiNat
import Mettapedia.GSLT.Logic.LogicalMetric
import Mettapedia.OSLF.Framework.EnumeratedAdequacy

/-!
# Logical observation metrics and behavioral equivalence classes

The source fixes an enumeration of the formulae of its context-decorated logic,
ordered so that smaller contexts come earlier, and sets the distance between two
terms to be two to the minus the least index at which they disagree, zero when
they agree everywhere.  It then states that this is an ultrametric, and reads the
statement as a locality principle: terms separated only by expensive contexts are
closer than terms separated by cheap ones.

That construction is the first-difference ultrametric on sequences, which is
already in Mathlib as `PiNat`.  So the logical metric is not built here, it is
**pulled back**: a term is read as the sequence of its answers to the enumerated
formulae, and the distance is the ambient one along that reading.  The
ultrametric inequality is then Mathlib's, transported, rather than a second proof
of the same fact.

Two things the source's statement leaves implicit are made explicit.

*The locality principle is a theorem, not a gloss.*  `distance_lt_of_rank_lt`
says that a pair whose first disagreement comes later is strictly closer, which
is exactly the reading the source gives its proposition.

*The source's metric is an instance.*  Enumerating the context-decorated formulae
of a theory gives an observation scheme (`hmlScheme`).  When the enumeration
covers every formula, distance zero is HML equivalence, and for a theory whose
successor classes are enumerable it is contextual bisimilarity
(`hmlScheme_distance_eq_zero_iff_bisimilar`).  Modal-depth locality uses a
different, explicitly identified observation scheme: its answer at depth `n`
is the term's equivalence class for the entire depth-`n` fragment.  This does
not require an enumeration of formulae, nor a depth-monotone enumeration
(there are infinitely many syntactically distinct depth-zero formulae).
`depthScheme_agreement_iff_lt_separatingRank` identifies its first disagreement
with the least separating modal depth.

Every scheme has a metric space on its indistinguishability quotient.  Its
reading is well-defined and injective there; metric separation is therefore
proved on actual equivalence classes, not merely asserted about a distance on
representatives.  For the depth scheme, the quotient identifies precisely HML
equivalence, and hence contextual bisimilarity under the adequacy hypotheses.

*The metric depends on the enumeration, not only on the set of formulae.*  The
source fixes an ordering and moves on.  `enumeration_matters` exhibits two
schemes that ask the same questions in a different order and assign the same pair
of terms different distances -- so the ordering is a parameter of the
construction, and a statement about the metric that does not name it is
incomplete.
-/

namespace Mettapedia.OSLF.Framework.LogicalMetric

attribute [local instance] PiNat.dist

set_option autoImplicit false

universe u v

/-- A sequence of observations.  The answer type may depend on the index:
Boolean formula satisfaction and whole-fragment equivalence classes are
instances of the same first-difference construction. -/
structure ObservationScheme (α : Type u) (Answer : ℕ → Type v) where
  /-- The observation of a term at this index. -/
  satisfies : (index : ℕ) → α → Answer index

namespace ObservationScheme

variable {α : Type u} {Answer : ℕ → Type v} (scheme : ObservationScheme α Answer)

/-- A term read as the sequence of its answers. -/
def reading (u : α) : (index : ℕ) → Answer index := fun index => scheme.satisfies index u

/-- Two terms are indistinguishable when no enumerated formula separates them. -/
def Indistinguishable (u v : α) : Prop := scheme.reading u = scheme.reading v

/-- The least index at which two terms disagree. -/
noncomputable def separatingRank (u v : α) : ℕ :=
  PiNat.firstDiff (scheme.reading u) (scheme.reading v)

/-- **The logical metric.**  Two to the minus the separating rank, and zero when
nothing separates. -/
noncomputable def distance (u v : α) : ℝ :=
  dist (scheme.reading u) (scheme.reading v)

@[simp] theorem distance_self (u : α) : scheme.distance u u = 0 :=
  PiNat.dist_self _

theorem distance_comm (u v : α) : scheme.distance u v = scheme.distance v u :=
  PiNat.dist_comm _ _

theorem distance_nonneg (u v : α) : 0 ≤ scheme.distance u v :=
  PiNat.dist_nonneg _ _

/-- On a separated pair the distance is two to the minus the separating rank,
which is the source's formula. -/
theorem distance_eq (u v : α) (separated : ¬ scheme.Indistinguishable u v) :
    scheme.distance u v = (1 / 2 : ℝ) ^ scheme.separatingRank u v :=
  PiNat.dist_eq_of_ne separated

/-- **Proposition 16.1.**  The logical metric is an ultrametric: the strong
triangle inequality holds, with the maximum in place of the sum. -/
theorem distance_triangle_nonarch (u v w : α) :
    scheme.distance u w ≤ max (scheme.distance u v) (scheme.distance v w) :=
  PiNat.dist_triangle_nonarch _ _ _

/-- The ordinary triangle inequality follows, so nothing is lost by the
strengthening. -/
theorem distance_triangle (u v w : α) :
    scheme.distance u w ≤ scheme.distance u v + scheme.distance v w := by
  refine (scheme.distance_triangle_nonarch u v w).trans ?_
  rcases max_cases (scheme.distance u v) (scheme.distance v w) with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]; linarith [scheme.distance_nonneg v w]
  · rw [h]; linarith [scheme.distance_nonneg u v]

/-- Distance zero is exactly indistinguishability, so the metric is genuine once
terms are taken modulo the logic rather than on the nose. -/
theorem distance_eq_zero_iff (u v : α) :
    scheme.distance u v = 0 ↔ scheme.Indistinguishable u v := by
  constructor
  · intro hzero
    by_contra separated
    have := scheme.distance_eq u v separated
    rw [hzero] at this
    exact absurd this.symm (by positivity)
  · intro same
    show dist (scheme.reading u) (scheme.reading v) = 0
    rw [same]
    exact PiNat.dist_self _

/-- The kernel of the observation reading. -/
def setoid : Setoid α where
  r := scheme.Indistinguishable
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- Actual observation-equivalence classes. -/
def Space := Quotient scheme.setoid

/-- The reading descends without choosing representatives. -/
def quotientReading : scheme.Space → (index : ℕ) → Answer index :=
  Quotient.lift scheme.reading (fun _ _ h => h)

theorem quotientReading_injective : Function.Injective scheme.quotientReading := by
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro u v same
  exact Quotient.sound same

/-- The first-difference metric on the observation quotient. -/
@[instance_reducible]
noncomputable def quotientMetricSpace : MetricSpace scheme.Space where
  dist x y := dist (scheme.quotientReading x) (scheme.quotientReading y)
  dist_self _ := PiNat.dist_self _
  dist_comm _ _ := PiNat.dist_comm _ _
  dist_triangle _ _ _ := PiNat.dist_triangle _ _ _
  eq_of_dist_eq_zero h := scheme.quotientReading_injective (PiNat.eq_of_dist_eq_zero _ _ h)

/-- Strong triangle inequality on equivalence classes, using the same reading. -/
theorem quotient_distance_triangle_nonarch (x y z : scheme.Space) :
    @dist _ scheme.quotientMetricSpace.toDist x z ≤
      max (@dist _ scheme.quotientMetricSpace.toDist x y)
        (@dist _ scheme.quotientMetricSpace.toDist y z) :=
  PiNat.dist_triangle_nonarch _ _ _

theorem space_mk_eq_iff (u v : α) :
    Quotient.mk scheme.setoid u = Quotient.mk scheme.setoid v ↔
      scheme.Indistinguishable u v := Quotient.eq

/-! ## The locality principle, as a theorem -/

/-- **Terms separated only by expensive formulae are closer.**  A later first
disagreement is a strictly smaller distance, which is the reading the source
gives its proposition. -/
theorem distance_lt_of_rank_lt {u v x y : α}
    (separatedFar : ¬ scheme.Indistinguishable u v)
    (separatedNear : ¬ scheme.Indistinguishable x y)
    (later : scheme.separatingRank x y < scheme.separatingRank u v) :
    scheme.distance u v < scheme.distance x y := by
  rw [scheme.distance_eq u v separatedFar, scheme.distance_eq x y separatedNear]
  exact pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) later

end ObservationScheme

/-! ## The context-decorated logic of a theory -/

section ContextDecoratedLogic

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.OSLF.Framework.EnumeratedAdequacy
open Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor.EffectiveStructure

variable (S : GSLT) [HasMinimalContexts S]

/-- The observation scheme of an enumeration of context-decorated formulae. -/
noncomputable def hmlScheme (enumerate : ℕ → HMLFormula S) :
    ObservationScheme S.Term (fun _ => Bool) where
  satisfies index term := by
    classical
    exact decide (HMLFormula.satisfies S term (enumerate index))

/-- With an enumeration of every formula, indistinguishability is HML
equivalence. -/
theorem hmlScheme_indistinguishable_iff (enumerate : ℕ → HMLFormula S)
    (surjective : Function.Surjective enumerate) (u v : S.Term) :
    (hmlScheme S enumerate).Indistinguishable u v ↔ HMLFormula.hmlEquiv S u v := by
  classical
  constructor
  · intro same formula
    obtain ⟨index, rfl⟩ := surjective formula
    have answers := congrFun same index
    simpa [ObservationScheme.reading, hmlScheme] using answers
  · intro equivalent
    funext index
    simp [ObservationScheme.reading, hmlScheme, equivalent (enumerate index)]

/-- **Definition 16.3.**  For a theory whose successor classes are enumerable, the
logical metric of an enumeration of every formula vanishes exactly on
contextually bisimilar terms. -/
theorem hmlScheme_distance_eq_zero_iff_bisimilar (enumerate : ℕ → HMLFormula S)
    (surjective : Function.Surjective enumerate) (plugResp : PlugRespectsEquiv S)
    (enumeration : SuccessorClassEnumeration S) (u v : S.Term) :
    (hmlScheme S enumerate).distance u v = 0 ↔
      contextBisimilar plugResp u v :=
  ((hmlScheme S enumerate).distance_eq_zero_iff u v).trans
    ((hmlScheme_indistinguishable_iff S enumerate surjective u v).trans
      (contextBisimilar_iff_hmlEquiv_of_enumeration plugResp enumeration u v).symm)

/-- Agreement on an entire modal-depth fragment is an equivalence relation. -/
def depthSetoid (n : ℕ) : Setoid S.Term where
  r := HMLFormula.hmlEquivUpTo n
  iseqv := ⟨HMLFormula.hmlEquivUpTo_refl n,
    fun h => HMLFormula.hmlEquivUpTo_symm h,
    fun h₁ h₂ => HMLFormula.hmlEquivUpTo_trans h₁ h₂⟩

/-- One quotient-valued answer per modal depth, independent of any formula
enumeration or countability assumption on context labels. -/
def depthScheme : ObservationScheme S.Term (fun n => Quotient (depthSetoid S n)) where
  satisfies n term := Quotient.mk (depthSetoid S n) term

theorem depthScheme_answer_eq_iff (n : ℕ) (u v : S.Term) :
    (depthScheme S).reading u n = (depthScheme S).reading v n ↔
      HMLFormula.hmlEquivUpTo (S := S) n u v := Quotient.eq

theorem depthScheme_indistinguishable_iff (u v : S.Term) :
    (depthScheme S).Indistinguishable u v ↔ HMLFormula.hmlEquiv S u v := by
  constructor
  · intro same formula
    exact ((depthScheme_answer_eq_iff S formula.modalDepth u v).mp
      (congrFun same formula.modalDepth)) formula (Nat.le_refl _)
  · intro equivalent
    funext n
    exact (depthScheme_answer_eq_iff S n u v).mpr
      (HMLFormula.hmlEquiv_implies_hmlEquivUpTo equivalent n)

/-- The separating rank is exactly the least modal depth at which agreement
fails.  No syntactic enumeration is assumed. -/
theorem depthScheme_agreement_iff_lt_separatingRank {u v : S.Term}
    (separated : ¬ (depthScheme S).Indistinguishable u v) (n : ℕ) :
    HMLFormula.hmlEquivUpTo (S := S) n u v ↔
      n < (depthScheme S).separatingRank u v := by
  constructor
  · intro agree
    by_contra earlier
    have atRank := HMLFormula.hmlEquivUpTo_mono (not_lt.mp earlier) agree
    exact PiNat.apply_firstDiff_ne separated
      ((depthScheme_answer_eq_iff S _ u v).mpr atRank)
  · intro earlier
    exact (depthScheme_answer_eq_iff S n u v).mp
      (PiNat.apply_eq_of_lt_firstDiff earlier)

/-- A separated pair has a genuine distinguishing formula at its separating
rank; the rank is not merely an index of unequal quotient encodings. -/
theorem depthScheme_distinguishingWitness {u v : S.Term}
    (separated : ¬ (depthScheme S).Indistinguishable u v) :
    HMLFormula.DistinguishingWitness (S := S)
      ((depthScheme S).separatingRank u v) u v := by
  apply (HMLFormula.not_hmlEquivUpTo_iff _ u v).mp
  intro agree
  have := (depthScheme_agreement_iff_lt_separatingRank S separated _).mp agree
  exact (Nat.lt_irrefl _) this

theorem depthScheme_distance_eq_zero_iff_bisimilar (plugResp : PlugRespectsEquiv S)
    (enumeration : SuccessorClassEnumeration S) (u v : S.Term) :
    (depthScheme S).distance u v = 0 ↔ contextBisimilar plugResp u v :=
  ((depthScheme S).distance_eq_zero_iff u v).trans
    ((depthScheme_indistinguishable_iff S u v).trans
      (contextBisimilar_iff_hmlEquiv_of_enumeration plugResp enumeration u v).symm)

/-- Under contextual adequacy, the actual metric quotient identifies precisely
contextually bisimilar representatives. -/
theorem depthScheme_classes_eq_iff_bisimilar (plugResp : PlugRespectsEquiv S)
    (enumeration : SuccessorClassEnumeration S) (u v : S.Term) :
    Quotient.mk (depthScheme S).setoid u = Quotient.mk (depthScheme S).setoid v ↔
      contextBisimilar plugResp u v :=
  ((depthScheme S).space_mk_eq_iff u v).trans
    ((depthScheme_indistinguishable_iff S u v).trans
      (contextBisimilar_iff_hmlEquiv_of_enumeration plugResp enumeration u v).symm)

private def negatedTop : ℕ → HMLFormula S
  | 0 => .top
  | n + 1 => .neg (negatedTop n)

private def leadingNegations : HMLFormula S → ℕ
  | .neg formula => leadingNegations formula + 1
  | _ => 0

private theorem leadingNegations_negatedTop (n : ℕ) :
    leadingNegations S (negatedTop S n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [negatedTop, leadingNegations] using congrArg Nat.succ ih

private theorem negatedTop_depth (n : ℕ) : (negatedTop S n).modalDepth = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

/-- A depth-monotone enumeration cannot cover the actual formula syntax:
infinitely many distinct depth-zero formulae would have to precede a depth-one
formula in a finite initial segment.  This is a negative control for the
enumeration-based locality hypothesis, not a restriction on HML. -/
theorem no_depthMonotone_surjective_enumeration (enumerate : ℕ → HMLFormula S)
    (surjective : Function.Surjective enumerate) :
    ¬ Monotone (fun index => (enumerate index).modalDepth) := by
  classical
  intro monotone
  choose position equation using fun n => surjective (negatedTop S n)
  obtain ⟨bound, atBound⟩ := surjective (.diamond MinimalContext.id .top)
  have bounded (n : ℕ) : position n < bound := by
    by_contra later
    have order := monotone (not_lt.mp later)
    change (enumerate bound).modalDepth ≤ (enumerate (position n)).modalDepth at order
    rw [atBound, equation n, negatedTop_depth] at order
    exact Nat.not_succ_le_zero 0 order
  let embed (n : ℕ) : Fin bound := ⟨position n, bounded n⟩
  have injective : Function.Injective embed := by
    intro n m same
    have positions := congrArg Fin.val same
    have formulas : negatedTop S n = negatedTop S m :=
      (equation n).symm.trans ((congrArg enumerate positions).trans (equation m))
    simpa only [leadingNegations_negatedTop] using congrArg (leadingNegations S) formulas
  exact (Finite.of_injective embed injective : Finite ℕ).false

end ContextDecoratedLogic

/-! ## The enumeration is a parameter

Both schemes below ask the same two questions of the same two terms.  They
differ only in which question is asked first, and they assign the pair different
distances.  So a claim about the logical metric that does not name its
enumeration has not fixed the metric. -/

/-- Reading a Boolean at place zero, and answering yes everywhere else. -/
def cheapFirst : ObservationScheme Bool (fun _ => Bool) where
  satisfies index term := if index = 0 then term else true

/-- The same question, asked at place one instead. -/
def cheapSecond : ObservationScheme Bool (fun _ => Bool) where
  satisfies index term := if index = 1 then term else true

private theorem firstDiff_eq_zero {x y : ℕ → Bool} (differ : x 0 ≠ y 0) :
    PiNat.firstDiff x y = 0 := by
  by_contra hne
  exact differ (PiNat.apply_eq_of_lt_firstDiff (Nat.pos_of_ne_zero hne))

private theorem firstDiff_eq_one {x y : ℕ → Bool}
    (agree : x 0 = y 0) (differ : x 1 ≠ y 1) : PiNat.firstDiff x y = 1 := by
  have distinct : x ≠ y := fun h => differ (by rw [h])
  have notZero : PiNat.firstDiff x y ≠ 0 := by
    intro h
    exact PiNat.apply_firstDiff_ne distinct (by rw [h]; exact agree)
  have lt_two : PiNat.firstDiff x y < 2 := by
    by_contra hge
    exact differ (PiNat.apply_eq_of_lt_firstDiff (by omega))
  omega

theorem cheapFirst_rank : cheapFirst.separatingRank true false = 0 :=
  firstDiff_eq_zero (by simp [ObservationScheme.reading, cheapFirst])

theorem cheapSecond_rank : cheapSecond.separatingRank true false = 1 :=
  firstDiff_eq_one (by simp [ObservationScheme.reading, cheapSecond])
    (by simp [ObservationScheme.reading, cheapSecond])

theorem cheapFirst_separates : ¬ cheapFirst.Indistinguishable true false := by
  intro same
  have := congrFun same 0
  simp [ObservationScheme.reading, cheapFirst] at this

theorem cheapSecond_separates : ¬ cheapSecond.Indistinguishable true false := by
  intro same
  have := congrFun same 1
  simp [ObservationScheme.reading, cheapSecond] at this

/-- **The metric depends on the enumeration.**  One pair of terms, one pair of
questions, two orderings, two distances. -/
theorem enumeration_matters :
    cheapFirst.distance true false = 1
      ∧ cheapSecond.distance true false = 1 / 2
      ∧ cheapFirst.distance true false ≠ cheapSecond.distance true false := by
  have first : cheapFirst.distance true false = 1 := by
    rw [cheapFirst.distance_eq _ _ cheapFirst_separates, cheapFirst_rank]
    norm_num
  have second : cheapSecond.distance true false = 1 / 2 := by
    rw [cheapSecond.distance_eq _ _ cheapSecond_separates, cheapSecond_rank]
    norm_num
  exact ⟨first, second, by rw [first, second]; norm_num⟩

end Mettapedia.OSLF.Framework.LogicalMetric
