import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipPlainTypeProofs

/-!
# Past modalities and quantifiers over a type as core sentences of set theory

A past modality at a set ranges over the hereditarily finite sets containing it, and a quantifier over a type over all
hereditarily finite sets of the type. As core sentences, both quantify over the sets and relativize to hereditary
finiteness (`hfFormula`):

- `⧫ψ` about `x` is `∃ y. y is hereditarily finite ∧ x ∈ y ∧ ψ(y)`, and `■ψ` is `∀ y. y is hereditarily finite →
  x ∈ y → ψ(y)`, for a member step; other labels give `⊥` and `⊤`.
- `∃ T. ψ` is `∃ y. y is hereditarily finite ∧ y has type T ∧ ψ(y)`, and `∀ T. ψ` is its dual.
- Every other formula is its native formula (`pastFormula`). The sentence of a formula at a term says some set the
  term describes has it (`pastSentence`).
- **They mean the hereditarily finite sets' native types** (`denote_pastSentence`): for a plain modal body, the
  sentence at a hereditary term is true in the model of the sets exactly when the term's set has the type among the
  hereditarily finite sets.
- **A type is a plain formula** (`typePlain`): a base type holds everywhere or nowhere, and a set type holds where every
  member has the element type, so `typedFormula` is the native formula of `typePlain` (`typedFormula_eq`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Logic.HOL (Ty Ctx Var Term ClosedFormula weaken rename subst instantiate Subst Rename)
open Mettapedia.Logic.HOL.ImpredicativeConnectives (truth falsity conjunctionFormula disjunctionFormula
  existentialInline)
open Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation (Symbol model member)

/-! ## Types as plain formulas -/

/-- **A type as a plain formula.** -/
def typePlain : TypeExpr → PlainFormula
  | .base sort => if sort = "Set" then .top else .bot
  | .collection kind element => if kind = .hashSet then .necessarily .any (typePlain element) else .bot
  | .arrow _ _ => .bot
  | .multiBinder _ => .bot

theorem typedFormula_eq : ∀ (type : TypeExpr) {Γ : Ctx Unit} (x : Term Symbol Γ setTy),
    typedFormula type x = plainAt (typePlain type) x
  | .base sort, _, _ => by
    by_cases named : sort = "Set"
    · simp only [typedFormula, typePlain, if_pos named]
      rfl
    · simp only [typedFormula, typePlain, if_neg named]
      rfl
  | .collection kind element, _, x => by
    by_cases set : kind = .hashSet
    · simp only [typedFormula, typePlain, if_pos set]
      rw [plainAt_necessarily (show memberLabel .any from trivial), typedFormula_eq element]
    · simp only [typedFormula, typePlain, if_neg set]
      rfl
  | .arrow _ _, _, _ => rfl
  | .multiBinder _, _, _ => rfl

theorem typePlain_eval_iff : ∀ (type : TypeExpr) {term : Pattern}, IsHF term →
    ((typePlain type).eval term = true ↔ SetTyped (zfOf term) type)
  | .base sort, _, _ => by
    simp only [typePlain, SetTyped]
    by_cases named : sort = "Set"
    · rw [if_pos named]
      exact iff_of_true rfl named
    · rw [if_neg named]
      exact iff_of_false Bool.false_ne_true named
  | .collection kind element, term, holds => by
    simp only [typePlain, SetTyped]
    by_cases set : kind = .hashSet
    · rw [if_pos set]
      simp only [PlainFormula.eval, set, true_and, show decide (memberLabel StepLabel.any) = true from rfl,
        Bool.not_true, Bool.false_or, List.all_eq_true]
      constructor
      · intro every member inside
        obtain ⟨value, valueMember, rfl⟩ := (mem_zfOf_hf holds).mp inside
        exact (typePlain_eval_iff element (hf_members holds value valueMember)).mp (every value valueMember)
      · intro every value valueMember
        exact (typePlain_eval_iff element (hf_members holds value valueMember)).mpr
          (every _ ((mem_zfOf_hf holds).mpr ⟨value, valueMember, rfl⟩))
    · rw [if_neg set]
      exact iff_of_false Bool.false_ne_true fun found => set found.1
  | .arrow _ _, _, _ => iff_of_false Bool.false_ne_true id
  | .multiBinder _, _, _ => iff_of_false Bool.false_ne_true id

theorem typePlain_plain : ∀ type : TypeExpr, (typePlain type).toFormula.plainModal = true
  | .base sort => by
    by_cases named : sort = "Set"
    · simp only [typePlain, if_pos named]
      rfl
    · simp only [typePlain, if_neg named]
      rfl
  | .collection kind element => by
    by_cases set : kind = .hashSet
    · simp only [typePlain, if_pos set, PlainFormula.toFormula, Formula.plainModal, typePlain_plain element]
      rfl
    · simp only [typePlain, if_neg set]
      rfl
  | .arrow _ _ => rfl
  | .multiBinder _ => rfl

/-! ## The sentences -/

variable {Γ : Ctx Unit}

/-- **A past modality or a quantifier over a type, about the set term `x`**, over the hereditarily finite sets. Every
other formula is its native formula. -/
def pastFormula : Formula 0 → Term Symbol Γ setTy → Term Symbol Γ .prop
  | .sometimeBefore label inner, x =>
    if memberLabel label then
      existentialInline (σ := setTy) (conjunctionFormula (hfFormula (.var .vz))
        (conjunctionFormula (member (weaken x) (.var .vz)) (nativeFormula inner (.var .vz) Fin.elim0)))
    else falsity
  | .alwaysBefore label inner, x =>
    if memberLabel label then
      .all (σ := setTy) (.imp (hfFormula (.var .vz))
        (.imp (member (weaken x) (.var .vz)) (nativeFormula inner (.var .vz) Fin.elim0)))
    else truth
  | .someOf type inner, _ =>
    existentialInline (σ := setTy) (conjunctionFormula (hfFormula (.var .vz))
      (conjunctionFormula (typedFormula type (.var .vz)) (nativeFormula inner (.var .vz) Fin.elim0)))
  | .everyOf type inner, _ =>
    .all (σ := setTy) (.imp (hfFormula (.var .vz))
      (.imp (typedFormula type (.var .vz)) (nativeFormula inner (.var .vz) Fin.elim0)))
  | formula, x => nativeFormula formula x Fin.elim0

/-- **The sentence of a formula at a term**: some set the term describes has it. -/
def pastSentence (formula : Formula 0) (term : Pattern) : ClosedFormula Symbol :=
  existentialInline (σ := setTy) (conjunctionFormula (describes term (.var .vz)) (pastFormula formula (.var .vz)))

/-- **Past modalities and quantifiers over a type with plain modal bodies.** -/
def _root_.Mettapedia.OSLF.NativeTypes.GeneratedLogic.Formula.pastPlain : Formula 0 → Bool
  | .sometimeBefore _ inner | .alwaysBefore _ inner | .someOf _ inner | .everyOf _ inner => inner.plainModal
  | _ => false

/-! ## What they mean -/

theorem envAgrees_elim0 (valuation : model.{0}.Valuation Γ) :
    EnvAgrees valuation (Fin.elim0 : Fin 0 → Term Symbol Γ predTy) Env.closed :=
  fun index => index.elim0

theorem denote_plainBody {inner : Formula 0} (plain : inner.plainModal = true) (valuation : model.{0}.Valuation Γ)
    (y : ZFSet.{0}) :
    (model.denote (nativeFormula inner (.var .vz) Fin.elim0) (model.extend (σ := setTy) valuation y)).down ↔
      extensional.sat Env.closed inner y :=
  denote_nativeFormula_regional inner (Formula.regional_of_plainModal inner plain) _ (.var .vz) Fin.elim0 Env.closed
    (envAgrees_elim0 _)

/-- **A past modality or quantifier over a type with a plain modal body is true exactly where the hereditarily
finite sets have it.** -/
theorem denote_pastFormula : ∀ {formula : Formula 0}, formula.pastPlain = true →
    ∀ (valuation : model.{0}.Valuation Γ) (x : Term Symbol Γ setTy) (finite : IsHFSet (setValue x valuation)),
      (model.denote (pastFormula formula x) valuation).down ↔
        HFSets.sat Env.closed formula ⟨setValue x valuation, finite⟩ := by
  intro formula past valuation x finite
  cases formula
  case sometimeBefore label inner =>
    have plain : inner.plainModal = true := past
    by_cases labelled : memberLabel label
    · simp only [pastFormula, if_pos labelled]
      rw [denote_existentialInline]
      change (∃ y : ZFSet.{0}, True ∧ (model.denote (conjunctionFormula (hfFormula (.var .vz))
        (conjunctionFormula (member (weaken x) (.var .vz)) (nativeFormula inner (.var .vz) Fin.elim0)))
          (model.extend (σ := setTy) valuation y)).down) ↔ _
      simp only [true_and, denote_conjunctionFormula, denote_hfFormula, denote_member, setValue_newest,
        setValue_weaken_set, denote_plainBody plain]
      constructor
      · rintro ⟨y, yFinite, inside, holds⟩
        exact ⟨⟨y, yFinite⟩, ⟨labelled, inside⟩, (hfSets_sat_iff plain ⟨y, yFinite⟩).mpr holds⟩
      · rintro ⟨previous, ⟨_, inside⟩, holds⟩
        exact ⟨previous.1, previous.2, inside, (hfSets_sat_iff plain previous).mp holds⟩
    · simp only [pastFormula, if_neg labelled]
      exact (denote_falsity valuation).trans (iff_of_false id fun ⟨_, ⟨found, _⟩, _⟩ => labelled found)
  case alwaysBefore label inner =>
    have plain : inner.plainModal = true := past
    by_cases labelled : memberLabel label
    · simp only [pastFormula, if_pos labelled]
      change (∀ y : ZFSet.{0}, True → (model.denote (hfFormula (.var .vz)) (model.extend (σ := setTy) valuation y)).down →
        (model.denote (member (weaken x) (.var .vz)) (model.extend (σ := setTy) valuation y)).down →
          (model.denote (nativeFormula inner (.var .vz) Fin.elim0) (model.extend (σ := setTy) valuation y)).down) ↔ _
      simp only [true_implies, denote_hfFormula, denote_member, setValue_newest, setValue_weaken_set,
        denote_plainBody plain]
      constructor
      · intro every previous ⟨_, inside⟩
        exact (hfSets_sat_iff plain previous).mpr (every previous.1 previous.2 inside)
      · intro every y yFinite inside
        exact (hfSets_sat_iff plain ⟨y, yFinite⟩).mp (every ⟨y, yFinite⟩ ⟨labelled, inside⟩)
    · simp only [pastFormula, if_neg labelled]
      exact iff_of_true (denote_truth valuation) fun _ step => absurd step.1 labelled
  case someOf type inner =>
    have plain : inner.plainModal = true := past
    simp only [pastFormula]
    rw [denote_existentialInline]
    change (∃ y : ZFSet.{0}, True ∧ (model.denote (conjunctionFormula (hfFormula (.var .vz))
      (conjunctionFormula (typedFormula type (.var .vz)) (nativeFormula inner (.var .vz) Fin.elim0)))
        (model.extend (σ := setTy) valuation y)).down) ↔ _
    simp only [true_and, denote_conjunctionFormula, denote_hfFormula, denote_typedFormula, setValue_newest,
      denote_plainBody plain]
    constructor
    · rintro ⟨y, yFinite, typed, holds⟩
      exact ⟨⟨y, yFinite⟩, typed, (hfSets_sat_iff plain ⟨y, yFinite⟩).mpr holds⟩
    · rintro ⟨witness, typed, holds⟩
      exact ⟨witness.1, witness.2, typed, (hfSets_sat_iff plain witness).mp holds⟩
  case everyOf type inner =>
    have plain : inner.plainModal = true := past
    simp only [pastFormula]
    change (∀ y : ZFSet.{0}, True → (model.denote (hfFormula (.var .vz)) (model.extend (σ := setTy) valuation y)).down →
      (model.denote (typedFormula type (.var .vz)) (model.extend (σ := setTy) valuation y)).down →
        (model.denote (nativeFormula inner (.var .vz) Fin.elim0) (model.extend (σ := setTy) valuation y)).down) ↔ _
    simp only [true_implies, denote_hfFormula, denote_typedFormula, setValue_newest, denote_plainBody plain]
    constructor
    · intro every witness typed
      exact (hfSets_sat_iff plain witness).mpr (every witness.1 witness.2 typed)
    · intro every y yFinite typed
      exact (hfSets_sat_iff plain ⟨y, yFinite⟩).mp (every ⟨y, yFinite⟩ typed)
  all_goals simp [Formula.pastPlain] at past

/-- **The sentence of a past modality or quantifier over a type with a plain modal body, at a hereditary term, is
true in the model of the sets exactly when the term's set has the type among the hereditarily finite sets.** -/
theorem denote_pastSentence {formula : Formula 0} (past : formula.pastPlain = true) {term : Pattern}
    (holds : IsHF term) (valuation : model.{0}.Valuation []) :
    (model.denote (pastSentence formula term) valuation).down ↔ HFSets.sat Env.closed formula (hfOf holds) := by
  rw [pastSentence, denote_existentialInline]
  change (∃ z : ZFSet.{0}, True ∧ (model.denote (conjunctionFormula (describes term (.var .vz))
    (pastFormula formula (.var .vz))) (model.extend (σ := setTy) valuation z)).down) ↔ _
  simp only [true_and, denote_conjunctionFormula, denote_describes holds, setValue_newest]
  constructor
  · rintro ⟨z, rfl, inside⟩
    exact (denote_pastFormula past _ (.var .vz) ⟨term, holds, rfl⟩).mp inside
  · intro inside
    exact ⟨zfOf term, rfl, (denote_pastFormula past _ (.var .vz) ⟨term, holds, rfl⟩).mpr inside⟩

theorem models_pastSentence {formula : Formula 0} (past : formula.pastPlain = true) {term : Pattern}
    (holds : IsHF term) : model.{0}.models (pastSentence formula term) ↔ HFSets.sat Env.closed formula (hfOf holds) :=
  denote_pastSentence past holds _


/-! ## Regional bodies -/

/-- **Past modalities and quantifiers over a type with regional bodies.** -/
def _root_.Mettapedia.OSLF.NativeTypes.GeneratedLogic.Formula.pastRegional : Formula 0 → Bool
  | .sometimeBefore _ inner | .alwaysBefore _ inner | .someOf _ inner | .everyOf _ inner => inner.regional
  | _ => false

theorem hfSets_sat_iff_regional {formula : Formula 0} (regional : formula.regional = true) (element : HF) :
    HFSets.sat Env.closed formula element ↔ extensional.sat Env.closed formula element.1 :=
  (NativeStructure.Generated.inclusion hfSets_generated).sat_iff formula (Formula.forward_of_regional formula regional)
    (BoundedMorphism.envPreimage_closed _) element

theorem denote_regionalBody {inner : Formula 0} (regional : inner.regional = true) (valuation : model.{0}.Valuation Γ)
    (y : ZFSet.{0}) :
    (model.denote (nativeFormula inner (.var .vz) Fin.elim0) (model.extend (σ := setTy) valuation y)).down ↔
      extensional.sat Env.closed inner y :=
  denote_nativeFormula_regional inner regional _ (.var .vz) Fin.elim0 Env.closed (envAgrees_elim0 _)

/-- **A past modality or quantifier over a type with a regional body is true exactly where the hereditarily finite
sets have it.** -/
theorem denote_pastFormula_regional : ∀ {formula : Formula 0}, formula.pastRegional = true →
    ∀ (valuation : model.{0}.Valuation Γ) (x : Term Symbol Γ setTy) (finite : IsHFSet (setValue x valuation)),
      (model.denote (pastFormula formula x) valuation).down ↔
        HFSets.sat Env.closed formula ⟨setValue x valuation, finite⟩ := by
  intro formula past valuation x finite
  cases formula
  case sometimeBefore label inner =>
    have regional : inner.regional = true := past
    by_cases labelled : memberLabel label
    · simp only [pastFormula, if_pos labelled]
      rw [denote_existentialInline]
      change (∃ y : ZFSet.{0}, True ∧ (model.denote (conjunctionFormula (hfFormula (.var .vz))
        (conjunctionFormula (member (weaken x) (.var .vz)) (nativeFormula inner (.var .vz) Fin.elim0)))
          (model.extend (σ := setTy) valuation y)).down) ↔ _
      simp only [true_and, denote_conjunctionFormula, denote_hfFormula, denote_member, setValue_newest,
        setValue_weaken_set, denote_regionalBody regional]
      constructor
      · rintro ⟨y, yFinite, inside, holds⟩
        exact ⟨⟨y, yFinite⟩, ⟨labelled, inside⟩, (hfSets_sat_iff_regional regional ⟨y, yFinite⟩).mpr holds⟩
      · rintro ⟨previous, ⟨_, inside⟩, holds⟩
        exact ⟨previous.1, previous.2, inside, (hfSets_sat_iff_regional regional previous).mp holds⟩
    · simp only [pastFormula, if_neg labelled]
      exact (denote_falsity valuation).trans (iff_of_false id fun ⟨_, ⟨found, _⟩, _⟩ => labelled found)
  case alwaysBefore label inner =>
    have regional : inner.regional = true := past
    by_cases labelled : memberLabel label
    · simp only [pastFormula, if_pos labelled]
      change (∀ y : ZFSet.{0}, True → (model.denote (hfFormula (.var .vz)) (model.extend (σ := setTy) valuation y)).down →
        (model.denote (member (weaken x) (.var .vz)) (model.extend (σ := setTy) valuation y)).down →
          (model.denote (nativeFormula inner (.var .vz) Fin.elim0) (model.extend (σ := setTy) valuation y)).down) ↔ _
      simp only [true_implies, denote_hfFormula, denote_member, setValue_newest, setValue_weaken_set,
        denote_regionalBody regional]
      constructor
      · intro every previous ⟨_, inside⟩
        exact (hfSets_sat_iff_regional regional previous).mpr (every previous.1 previous.2 inside)
      · intro every y yFinite inside
        exact (hfSets_sat_iff_regional regional ⟨y, yFinite⟩).mp (every ⟨y, yFinite⟩ ⟨labelled, inside⟩)
    · simp only [pastFormula, if_neg labelled]
      exact iff_of_true (denote_truth valuation) fun _ step => absurd step.1 labelled
  case someOf type inner =>
    have regional : inner.regional = true := past
    simp only [pastFormula]
    rw [denote_existentialInline]
    change (∃ y : ZFSet.{0}, True ∧ (model.denote (conjunctionFormula (hfFormula (.var .vz))
      (conjunctionFormula (typedFormula type (.var .vz)) (nativeFormula inner (.var .vz) Fin.elim0)))
        (model.extend (σ := setTy) valuation y)).down) ↔ _
    simp only [true_and, denote_conjunctionFormula, denote_hfFormula, denote_typedFormula, setValue_newest,
      denote_regionalBody regional]
    constructor
    · rintro ⟨y, yFinite, typed, holds⟩
      exact ⟨⟨y, yFinite⟩, typed, (hfSets_sat_iff_regional regional ⟨y, yFinite⟩).mpr holds⟩
    · rintro ⟨witness, typed, holds⟩
      exact ⟨witness.1, witness.2, typed, (hfSets_sat_iff_regional regional witness).mp holds⟩
  case everyOf type inner =>
    have regional : inner.regional = true := past
    simp only [pastFormula]
    change (∀ y : ZFSet.{0}, True → (model.denote (hfFormula (.var .vz)) (model.extend (σ := setTy) valuation y)).down →
      (model.denote (typedFormula type (.var .vz)) (model.extend (σ := setTy) valuation y)).down →
        (model.denote (nativeFormula inner (.var .vz) Fin.elim0) (model.extend (σ := setTy) valuation y)).down) ↔ _
    simp only [true_implies, denote_hfFormula, denote_typedFormula, setValue_newest, denote_regionalBody regional]
    constructor
    · intro every witness typed
      exact (hfSets_sat_iff_regional regional witness).mpr (every witness.1 witness.2 typed)
    · intro every y yFinite typed
      exact (hfSets_sat_iff_regional regional ⟨y, yFinite⟩).mp (every ⟨y, yFinite⟩ typed)
  all_goals simp [Formula.pastRegional] at past

/-- **The sentence of a past modality or quantifier over a type with a regional body, at a hereditary term, is true
in the model of the sets exactly when the term's set has the type among the hereditarily finite sets.** -/
theorem denote_pastSentence_regional {formula : Formula 0} (past : formula.pastRegional = true) {term : Pattern}
    (holds : IsHF term) (valuation : model.{0}.Valuation []) :
    (model.denote (pastSentence formula term) valuation).down ↔ HFSets.sat Env.closed formula (hfOf holds) := by
  rw [pastSentence, denote_existentialInline]
  change (∃ z : ZFSet.{0}, True ∧ (model.denote (conjunctionFormula (describes term (.var .vz))
    (pastFormula formula (.var .vz))) (model.extend (σ := setTy) valuation z)).down) ↔ _
  simp only [true_and, denote_conjunctionFormula, denote_describes holds, setValue_newest]
  constructor
  · rintro ⟨z, rfl, inside⟩
    exact (denote_pastFormula_regional past _ (.var .vz) ⟨term, holds, rfl⟩).mp inside
  · intro inside
    exact ⟨zfOf term, rfl, (denote_pastFormula_regional past _ (.var .vz) ⟨term, holds, rfl⟩).mpr inside⟩

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings
