import Mettapedia.PLN.RuleFamilies.QuantaleSemantics.DoubleNegationCorners

/-!
# Two negations on evidence: strong and intuitionistic

The lattice order of `BinaryEvidence` is the information order.  The same carrier has
a second order, the **truth order**: more evidence for is better and more evidence
against is worse (`TruthLE`).  Its meet and join are the evidential conjunction and
disjunction (`tmeet`, `tjoin`).  With the exchange of channels `cdNeg` as negation
and the implication `timp`, whose positive channel is the Gödel implication of the
positive channels and whose negative channel is the positive channel of the
antecedent met with the negative channel of the consequent, the carrier is the twist
structure over the chain `[0, ∞]`: the algebraic semantics of Nelson's constructive
logic with strong negation (N4, with gluts; N3 on consistent evidence).

* **Strong negation** `∼` is involutive, reverses the truth order and preserves the
  information order (`truthLE_cdNeg_iff`, `cdNeg_le_cdNeg_iff`), satisfies De Morgan's
  laws (`cdNeg_tmeet`, `cdNeg_tjoin`), and refutes an implication by its antecedent
  together with a refutation of its consequent (`cdNeg_timp`).  It is paraconsistent
  and paracomplete: `both` and its strong negation are both supported, `neither` and
  its strong negation are both unsupported (`both_and_cdNeg_supported`,
  `neither_and_cdNeg_unsupported`).
* **Intuitionistic negation** `inot a := timp a falsum` reads present absence: it is
  saturated support exactly when `a` has no support, and it is refuted by the support
  of `a` (`inot_apply`).  It obeys non-contradiction and excluded middle at the level
  of support (`not_supported_tmeet_inot`, `supported_tjoin_inot`).  Its double keeps
  only two values: some support gives `true`, none gives `false`
  (`inot_inot_apply`); `both` becomes `true` and `neither` becomes `false`
  (`inot_inot_both`, `inot_inot_neither`).  This is the closed-world reading of
  double negation, whereas the double complement of the information order keeps all
  four corners (`DoubleNegationCorners.compl_compl_eq_saturatedCorner`).
* **How the two negations relate.**  Strong negation entails intuitionistic negation
  in the truth order exactly on consistent evidence, where one channel is empty
  (`cdNeg_truthLE_inot_iff`).  Intuitionistic negation entails strong negation
  exactly when absence of support comes with saturated evidence against
  (`inot_truthLE_cdNeg_iff`), that is, when no support counts as full refutation.

* **The negative tetralemma.**  The four corners of a claim stated with strong
  negation (`corners`) all lack support, and their intuitionistic negations all have
  support, exactly when the claim has neither support nor refutation
  (`corners_unsupported_iff`, `corners_denied_iff`).

Reading.  Indian grammarians and logicians distinguish implicative negation
(*paryudāsa*), which negates a term and affirms something else in its place, from
non-implicative negation (*prasajya-pratiṣedha*), which denies without affirming
anything; on Westerhoff's reading the first keeps the presuppositions of what it
negates (choice negation) and the second can reject them (exclusion negation).
Strong negation is implicative in this sense: supporting `∼a` requires positive
evidence against `a`, as calling something non-red requires it to have some other
colour.  Intuitionistic negation is non-implicative: it is supported by the bare
absence of support.  The first entails the second on consistent evidence, and the
second entails the first exactly when absence of support guarantees refutation,
that is, when the presupposition is secured.  When it fails, all four corners are
rejected together, which is the presupposition reading of the negative tetralemma.
The present-absence reading agrees with native negation in a presheaf topos only
under a reflection condition (`GSLT.Topos.PresheafEventAbsence.absent_iff_present`),
which is the condition Dharmakīrti places on inference from non-perception: the
absent thing must be one that would have been perceived.

References: D. Nelson, *Constructible falsity*, JSL 14 (1949); D. Vakarelov, *Notes on
N-lattices and constructive logic with strong negation*, Studia Logica 36 (1977);
S. Odintsov, *Constructive Negations and Paraconsistency* (2008); M. Busaniche,
N. Galatos and M. Marcos, *Twist structures and Nelson conuclei* (2021);
J. Westerhoff, *Nāgārjuna's Madhyamaka: A Philosophical Investigation*, PhD thesis,
SOAS, University of London (2007), ch. 4.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.RuleFamilies.QuantaleSemantics.TwistNegation

open Mettapedia.PLN.Evidence
open Mettapedia.PLN.RuleFamilies.QuantaleSemantics.PBit
open Mettapedia.PLN.RuleFamilies.QuantaleSemantics.CDLogic
open scoped ENNReal

/-! ## The truth order and its operations -/

/-- The truth order: at least as much evidence for and at most as much against. -/
def TruthLE (a b : BinaryEvidence) : Prop :=
  a.pos ≤ b.pos ∧ b.neg ≤ a.neg

/-- Evidential conjunction, the meet of the truth order. -/
def tmeet (a b : BinaryEvidence) : BinaryEvidence :=
  ⟨min a.pos b.pos, max a.neg b.neg⟩

/-- Evidential disjunction, the join of the truth order. -/
def tjoin (a b : BinaryEvidence) : BinaryEvidence :=
  ⟨max a.pos b.pos, min a.neg b.neg⟩

/-- The twist implication: Gödel implication on the positive channel; refuted by
support for the antecedent together with refutation of the consequent. -/
noncomputable def timp (a b : BinaryEvidence) : BinaryEvidence :=
  ⟨if a.pos ≤ b.pos then ⊤ else b.pos, min a.pos b.neg⟩

/-- The false constant: no support, saturated refutation. -/
def falsum : BinaryEvidence := ⟨0, ⊤⟩

/-- Intuitionistic negation: implication into the false constant. -/
noncomputable def inot (a : BinaryEvidence) : BinaryEvidence :=
  timp a falsum

/-- A value is supported when its positive channel is nonzero. -/
def Supported (a : BinaryEvidence) : Prop :=
  a.pos ≠ 0

theorem truthLE_refl (a : BinaryEvidence) : TruthLE a a :=
  ⟨le_refl _, le_refl _⟩

theorem tmeet_truthLE_left (a b : BinaryEvidence) : TruthLE (tmeet a b) a :=
  ⟨min_le_left _ _, le_max_left _ _⟩

theorem tmeet_truthLE_right (a b : BinaryEvidence) : TruthLE (tmeet a b) b :=
  ⟨min_le_right _ _, le_max_right _ _⟩

theorem truthLE_tmeet {a b c : BinaryEvidence} (left : TruthLE c a) (right : TruthLE c b) :
    TruthLE c (tmeet a b) :=
  ⟨le_min left.1 right.1, max_le left.2 right.2⟩

theorem truthLE_tjoin_left (a b : BinaryEvidence) : TruthLE a (tjoin a b) :=
  ⟨le_max_left _ _, min_le_left _ _⟩

theorem truthLE_tjoin_right (a b : BinaryEvidence) : TruthLE b (tjoin a b) :=
  ⟨le_max_right _ _, min_le_right _ _⟩

theorem tjoin_truthLE {a b c : BinaryEvidence} (left : TruthLE a c) (right : TruthLE b c) :
    TruthLE (tjoin a b) c :=
  ⟨max_le left.1 right.1, le_min left.2 right.2⟩

/-! ## Strong negation -/

/-- Strong negation reverses the truth order. -/
theorem truthLE_cdNeg_iff (a b : BinaryEvidence) : TruthLE (∼a) (∼b) ↔ TruthLE b a := by
  simp only [TruthLE, cdNeg]
  exact And.comm

/-- Strong negation preserves the information order. -/
theorem cdNeg_le_cdNeg_iff (a b : BinaryEvidence) : ∼a ≤ ∼b ↔ a ≤ b := by
  simp only [BinaryEvidence.le_def, cdNeg]
  exact And.comm

theorem cdNeg_tmeet (a b : BinaryEvidence) : ∼(tmeet a b) = tjoin (∼a) (∼b) := rfl

theorem cdNeg_tjoin (a b : BinaryEvidence) : ∼(tjoin a b) = tmeet (∼a) (∼b) := rfl

/-- **Support of a refuted implication**: `∼(a ⇒ b)` and `a ∧ ∼b` have the same
support.  This is the Nelson law, an equivalence in the weak sense: the two values
are verified together (positive channels agree, `cdNeg_timp_pos`) but are refuted
differently (`cdNeg_timp_ne_tmeet`). -/
theorem cdNeg_timp_pos (a b : BinaryEvidence) : (∼(timp a b)).pos = (tmeet a (∼b)).pos := rfl

/-- Control: the refutations of `∼(a ⇒ b)` and of `a ∧ ∼b` differ. -/
theorem cdNeg_timp_ne_tmeet :
    ∼(timp ⟨0, 1⟩ ⟨0, 0⟩) ≠ tmeet ⟨0, 1⟩ (∼⟨0, 0⟩) := by
  intro equal
  have neg := congrArg BinaryEvidence.neg equal
  simp [cdNeg, timp, tmeet] at neg

/-- Modus ponens on support: the support of `a ∧ (a ⇒ b)` is at most that of `b`. -/
theorem tmeet_timp_pos_le (a b : BinaryEvidence) : (tmeet a (timp a b)).pos ≤ b.pos := by
  show min a.pos (if a.pos ≤ b.pos then ⊤ else b.pos) ≤ b.pos
  by_cases le : a.pos ≤ b.pos
  · rw [if_pos le]
    exact (min_le_left _ _).trans le
  · rw [if_neg le]
    exact min_le_right _ _

/-- Strong negation is paraconsistent: `both` and its strong negation are both
supported. -/
theorem both_and_cdNeg_supported : Supported pBoth ∧ Supported (∼pBoth) := by
  simp [Supported, pBoth, cdNeg]

/-- Strong negation is paracomplete: `neither` and its strong negation are both
unsupported. -/
theorem neither_and_cdNeg_unsupported : ¬ Supported pNeither ∧ ¬ Supported (∼pNeither) := by
  simp [Supported, pNeither, cdNeg]

/-! ## Intuitionistic negation -/

/-- **Intuitionistic negation reads present absence**: saturated support exactly
when there is no support, refuted by the support that there is. -/
theorem inot_apply (a : BinaryEvidence) :
    inot a = ⟨if a.pos = 0 then ⊤ else 0, a.pos⟩ := by
  ext
  · show (if a.pos ≤ 0 then ⊤ else 0) = _
    simp only [nonpos_iff_eq_zero]
  · show min a.pos ⊤ = a.pos
    exact min_top_right a.pos

/-- **The double keeps two values**: some support gives `true`, none gives
`false`. -/
theorem inot_inot_apply (a : BinaryEvidence) :
    inot (inot a) = ⟨if a.pos = 0 then 0 else ⊤, if a.pos = 0 then ⊤ else 0⟩ := by
  rw [inot_apply (inot a), inot_apply a]
  by_cases zero : a.pos = 0 <;> simp [zero]

theorem inot_inot_both : inot (inot pBoth) = ⟨⊤, 0⟩ := by
  rw [inot_inot_apply]
  simp [pBoth]

theorem inot_inot_neither : inot (inot pNeither) = ⟨0, ⊤⟩ := by
  rw [inot_inot_apply]
  simp [pNeither]

/-- The double intuitionistic negation is never in the `both` or the `neither`
quadrant. -/
theorem quadrant_inot_inot (a : BinaryEvidence) :
    quadrant (inot (inot a)) = if a.pos = 0 then .false else .true := by
  rw [inot_inot_apply]
  by_cases zero : a.pos = 0 <;> simp [zero, quadrant]

/-- **The two double negations differ on `both`**: the double complement of the
information order keeps the corner, the double intuitionistic negation sends it to
`true`. -/
theorem double_negations_differ_on_both :
    pBothᶜᶜ = ⟨⊤, ⊤⟩ ∧ inot (inot pBoth) = ⟨⊤, 0⟩ := by
  refine ⟨?_, inot_inot_both⟩
  rw [DoubleNegationCorners.compl_compl_apply]
  simp [pBoth]

/-- Non-contradiction at the level of support. -/
theorem not_supported_tmeet_inot (a : BinaryEvidence) : ¬ Supported (tmeet a (inot a)) := by
  rw [inot_apply]
  by_cases zero : a.pos = 0 <;> simp [Supported, tmeet, zero]

/-- Excluded middle at the level of support. -/
theorem supported_tjoin_inot (a : BinaryEvidence) : Supported (tjoin a (inot a)) := by
  rw [inot_apply]
  by_cases zero : a.pos = 0 <;> simp [Supported, tjoin, zero]

/-- Control: intuitionistic negation is not involutive. -/
theorem inot_inot_one_zero_ne : inot (inot ⟨1, 0⟩) ≠ ⟨1, 0⟩ := by
  rw [inot_inot_apply]
  intro equal
  have pos := congrArg BinaryEvidence.pos equal
  simp at pos

/-! ## How the two negations relate -/

/-- **Strong negation entails intuitionistic negation exactly on consistent
evidence**, where one channel is empty. -/
theorem cdNeg_truthLE_inot_iff (a : BinaryEvidence) :
    TruthLE (∼a) (inot a) ↔ a.pos = 0 ∨ a.neg = 0 := by
  rw [inot_apply]
  simp only [TruthLE, cdNeg, le_refl, and_true]
  by_cases zero : a.pos = 0
  · simp [zero]
  · simp [zero]

/-- **Intuitionistic negation entails strong negation exactly when absence of support
counts as full refutation.** -/
theorem inot_truthLE_cdNeg_iff (a : BinaryEvidence) :
    TruthLE (inot a) (∼a) ↔ (a.pos = 0 → a.neg = ⊤) := by
  rw [inot_apply]
  simp only [TruthLE, cdNeg, le_refl, and_true]
  by_cases zero : a.pos = 0
  · simp [zero]
  · simp [zero]

/-- Control: on the `both` corner strong negation does not entail intuitionistic
negation. -/
theorem not_cdNeg_truthLE_inot_both : ¬ TruthLE (∼pBoth) (inot pBoth) := by
  rw [cdNeg_truthLE_inot_iff]
  simp [pBoth]

/-- Control: on unsupported, unrefuted evidence intuitionistic negation does not
entail strong negation. -/
theorem not_inot_truthLE_cdNeg_neither : ¬ TruthLE (inot pNeither) (∼pNeither) := by
  rw [inot_truthLE_cdNeg_iff]
  simp [pNeither]

/-! ## The negative tetralemma

The four corners of a claim `a`, written with strong negation, are `a`, `∼a`,
`a ∧ ∼a` and `∼a ∧ ∼∼a`.  All four lack support, and the intuitionistic negations of
all four have support, exactly when `a` has neither support nor refutation.  Read
with the presupposition account of the two negations, this is the rejection of all
four corners when the claim's presupposition fails: every corner stated with the
presupposing negation is unsupported, and every corner is denied by the
non-presupposing one. -/

/-- The four corners of a claim, stated with strong negation. -/
def corners (a : BinaryEvidence) : List BinaryEvidence :=
  [a, ∼a, tmeet a (∼a), tmeet (∼a) (∼(∼a))]

/-- Intuitionistic negation is supported exactly when its argument is not. -/
theorem supported_inot_iff (a : BinaryEvidence) : Supported (inot a) ↔ ¬ Supported a := by
  rw [inot_apply]
  by_cases zero : a.pos = 0 <;> simp [Supported, zero]

/-- **All four corners lack support exactly on the `neither` corner.** -/
theorem corners_unsupported_iff (a : BinaryEvidence) :
    (∀ corner ∈ corners a, ¬ Supported corner) ↔ isNeither a := by
  simp only [corners, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    Supported, isNeither, tmeet, cdNeg, ne_eq, not_not]
  constructor
  · rintro ⟨pos, neg, -, -⟩
    exact ⟨pos, neg⟩
  · rintro ⟨pos, neg⟩
    simp [pos, neg]

/-- **The non-presupposing negation denies all four corners exactly there.** -/
theorem corners_denied_iff (a : BinaryEvidence) :
    (∀ corner ∈ corners a, Supported (inot corner)) ↔ isNeither a := by
  rw [← corners_unsupported_iff]
  exact forall₂_congr fun corner _ => supported_inot_iff corner

/-- On the `neither` corner both statements hold together. -/
theorem negative_tetralemma_neither :
    (∀ corner ∈ corners pNeither, ¬ Supported corner) ∧
      (∀ corner ∈ corners pNeither, Supported (inot corner)) :=
  ⟨(corners_unsupported_iff pNeither).mpr pNeither_isNeither,
    (corners_denied_iff pNeither).mpr pNeither_isNeither⟩

/-- Control: on the `both` corner the first corner is supported. -/
theorem corners_both_not_unsupported : ¬ ∀ corner ∈ corners pBoth, ¬ Supported corner := by
  rw [corners_unsupported_iff]
  exact fun neither => isNeither_not_isBoth pBoth neither pBoth_isBoth

end Mettapedia.PLN.RuleFamilies.QuantaleSemantics.TwistNegation
