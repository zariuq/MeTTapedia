import Mettapedia.Languages.OpenTheory.DerivedRulesEquality
import Mettapedia.Languages.OpenTheory.DefinedConnectives

/-!
# Natural-deduction rules for the defined connectives

HOL Light's `bool.ml` derives the natural-deduction rules of its connectives
from the equational kernel.  This module derives them for the OpenTheory
primitive kernel, on the interface `KernelProvable` of
`DerivedRulesEquality.lean`, with every connective given by its HOL Light
definition inlined as a lambda term:

* `T = ((λp. p) = (λp. p))`, `∀ = λP. P = (λx. T)`,
  `∧ = λp q. (λf. f p q) = (λf. f T T)`, `⇒ = λp q. (p ∧ q) = p`,
  `F = ∀p. p`, `¬ = λp. p ⇒ F`, `∨ = λp q. ∀r. (p ⇒ r) ⇒ (q ⇒ r) ⇒ r`,
  `∃ = λP. ∀q. (∀x. P x ⇒ q) ⇒ q`.

The rules hold for every axiom policy and carry HOL Light's hypothesis-set
bookkeeping: `conj`, `mp`, `impAntisym` and `disjCases` take unions, `disch`
removes the discharged hypothesis, `undisch` inserts it, `choose` removes the
witness instance, and every other rule keeps the hypotheses of its premise.

* conjunction: `conj`, `conjunct1`, `conjunct2`;
* implication: `mp`, `disch`, `undisch`;
* universal quantifier: `spec`, `specApp`, `gen`;
* existential quantifier: `existsIntro`, `existsIntroApp`, `choose`,
  `chooseApp`, `chooseOfImp`;
* disjunction: `disj1`, `disj2`, `disjCases`;
* negation and falsity: `notElim`, `notIntro`, `contr`;
* Boolean equality: `impAntisym`, `eqImpRuleLeft`, `eqImpRuleRight`.

Each connective application beta-reduces to its body (`forallAppDB_beta`,
`andAppDB_beta`, `impAppDB_beta`, `notAppDB_beta`, `orAppDB_beta`,
`existsAppDB_beta`).

Controls: `⊢ T`, `p ∧ q ⊢ q ∧ p`, `⊢ p ⇒ p` and `p ∨ q ⊢ q ∨ p` are provable
without axioms; GEN's freshness condition carries weight
(`gen_freshness_needed`): `x = y ⊢ ∀x. x = y` is not provable, since the
two-point model satisfies its hypothesis and refutes its conclusion.

Where HOL Light instantiates a schematic theorem by `INST`, the derivations
here are carried out directly for the given terms; the schematic variables
that HOL Light abstracts (`f` in `CONJ`, `t` in `DISJ1`, `Q` in `EXISTS`)
become variables chosen fresh for the hypotheses and the terms involved
(`exists_fresh_var`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.OpenTheory

open Mettapedia.Logic
open CanonicalTerm (equalityDB)
open DBTerm (instantiateAt closeFreeAt FreeOccurrence inferType_app_of inferType_abs_of
  inferType_equalityDB inferType_equalityDB_iff instantiateAt_closed)
open ExcludedMiddle (andDB impDB impAppDB forallDB notDB orDB falsityDefinitionDB
  boolBinaryTy)
open PrimitiveSentences (truthDB identityBool)

namespace DerivedRules

/-! ## Applications of the defined connectives -/

/-- `p ∧ q`. -/
def andAppDB (p q : DBTerm) : DBTerm := .app (.app andDB p) q

/-- `p ∨ q`. -/
def orAppDB (p q : DBTerm) : DBTerm := .app (.app orDB p) q

/-- `¬ p`. -/
def notAppDB (p : DBTerm) : DBTerm := .app notDB p

/-- `∀ P` for a predicate `P : A → bool`. -/
def forallAppDB (A : Ty) (predicate : DBTerm) : DBTerm := .app (forallDB A) predicate

/-- `∃ P` for a predicate `P : A → bool`. -/
def existsAppDB (A : Ty) (predicate : DBTerm) : DBTerm :=
  .app (DefinedConnectives.existsDB A) predicate

/-- The body of `p ∧ q`: `(λf. f p q) = (λf. f T T)`. -/
def andBodyDB (p q : DBTerm) : DBTerm :=
  equalityDB (.function boolBinaryTy Ty.bool)
    (.abs boolBinaryTy (.app (.app (.bound 0) p) q))
    (.abs boolBinaryTy (.app (.app (.bound 0) truthDB) truthDB))

/-- The body of `p ∨ q`: `∀r. (p ⇒ r) ⇒ (q ⇒ r) ⇒ r`. -/
def orBodyDB (p q : DBTerm) : DBTerm :=
  forallAppDB Ty.bool (.abs Ty.bool
    (impAppDB (impAppDB p (.bound 0)) (impAppDB (impAppDB q (.bound 0)) (.bound 0))))

/-- The body of `∃ P`: `∀q. (∀x. P x ⇒ q) ⇒ q`. -/
def existsBodyDB (A : Ty) (predicate : DBTerm) : DBTerm :=
  forallAppDB Ty.bool (.abs Ty.bool
    (impAppDB (forallAppDB A (.abs A (impAppDB (.app predicate (.bound 0)) (.bound 1))))
      (.bound 0)))

/-- `λa b. a`. -/
def selectFirstDB : DBTerm := .abs Ty.bool (.abs Ty.bool (.bound 1))

/-- `λa b. b`. -/
def selectSecondDB : DBTerm := .abs Ty.bool (.abs Ty.bool (.bound 0))

/-! ## Typing -/

section Typing

variable {context : List Ty}

theorem inferType_forallDB (A : Ty) :
    (forallDB A).inferType context = some (.function (.function A Ty.bool) Ty.bool) :=
  DBTerm.inferType_weaken_empty (DefinedConnectives.forallDB_inferType A) _

theorem inferType_andDB : andDB.inferType context = some boolBinaryTy :=
  DBTerm.inferType_weaken_empty DefinedConnectives.andDB_inferType _

theorem inferType_impDB : impDB.inferType context = some boolBinaryTy :=
  DBTerm.inferType_weaken_empty DefinedConnectives.impDB_inferType _

theorem inferType_existsDB (A : Ty) :
    (DefinedConnectives.existsDB A).inferType context =
      some (.function (.function A Ty.bool) Ty.bool) :=
  DBTerm.inferType_weaken_empty (DefinedConnectives.existsDB_inferType A) _

theorem inferType_bound_zero (ty : Ty) (rest : List Ty) :
    (DBTerm.bound 0).inferType (ty :: rest) = some ty := by
  simp

theorem inferType_bound_one (ty ty' : Ty) (rest : List Ty) :
    (DBTerm.bound 1).inferType (ty' :: ty :: rest) = some ty := by
  simp

/-- Application of a closed binary Boolean connective. -/
theorem inferType_binary_iff {connective p q : DBTerm}
    (hconnective : connective.inferType [] = some boolBinaryTy) {ty : Ty} :
    (DBTerm.app (.app connective p) q).inferType context = some ty ↔
      p.inferType context = some Ty.bool ∧ q.inferType context = some Ty.bool ∧
        ty = Ty.bool := by
  constructor
  · intro h
    obtain ⟨d₁, houter, hq⟩ := DBTerm.inferType_app_eq_some_iff.mp h
    obtain ⟨d₀, hc, hp⟩ := DBTerm.inferType_app_eq_some_iff.mp houter
    rw [DBTerm.inferType_weaken_empty hconnective _] at hc
    obtain ⟨rfl, hrest⟩ := Ty.function_inj (Option.some.inj hc)
    obtain ⟨rfl, rfl⟩ := Ty.function_inj hrest
    exact ⟨hp, hq, rfl⟩
  · rintro ⟨hp, hq, rfl⟩
    exact inferType_app_of
      (inferType_app_of (DBTerm.inferType_weaken_empty hconnective _) hp) hq

theorem inferType_impAppDB {p q : DBTerm} (hp : p.inferType context = some Ty.bool)
    (hq : q.inferType context = some Ty.bool) :
    (impAppDB p q).inferType context = some Ty.bool :=
  (inferType_binary_iff DefinedConnectives.impDB_inferType).mpr ⟨hp, hq, rfl⟩

theorem inferType_andAppDB {p q : DBTerm} (hp : p.inferType context = some Ty.bool)
    (hq : q.inferType context = some Ty.bool) :
    (andAppDB p q).inferType context = some Ty.bool :=
  (inferType_binary_iff DefinedConnectives.andDB_inferType).mpr ⟨hp, hq, rfl⟩

theorem inferType_forallAppDB_iff {A : Ty} {predicate : DBTerm} {ty : Ty} :
    (forallAppDB A predicate).inferType context = some ty ↔
      predicate.inferType context = some (.function A Ty.bool) ∧ ty = Ty.bool := by
  constructor
  · intro h
    obtain ⟨d, hforall, hpredicate⟩ := DBTerm.inferType_app_eq_some_iff.mp h
    rw [inferType_forallDB] at hforall
    obtain ⟨rfl, rfl⟩ := Ty.function_inj (Option.some.inj hforall)
    exact ⟨hpredicate, rfl⟩
  · rintro ⟨hpredicate, rfl⟩
    exact inferType_app_of (inferType_forallDB A) hpredicate

theorem inferType_existsAppDB_iff {A : Ty} {predicate : DBTerm} {ty : Ty} :
    (existsAppDB A predicate).inferType context = some ty ↔
      predicate.inferType context = some (.function A Ty.bool) ∧ ty = Ty.bool := by
  constructor
  · intro h
    obtain ⟨d, hexists, hpredicate⟩ := DBTerm.inferType_app_eq_some_iff.mp h
    rw [inferType_existsDB] at hexists
    obtain ⟨rfl, rfl⟩ := Ty.function_inj (Option.some.inj hexists)
    exact ⟨hpredicate, rfl⟩
  · rintro ⟨hpredicate, rfl⟩
    exact inferType_app_of (inferType_existsDB A) hpredicate

theorem inferType_falsityDefinitionDB : falsityDefinitionDB.inferType context = some Ty.bool :=
  inferType_app_of (inferType_forallDB Ty.bool) inferType_identityBool

theorem inferType_notDB : notDB.inferType context = some (.function Ty.bool Ty.bool) :=
  inferType_abs_of (inferType_impAppDB (inferType_bound_zero _ _) inferType_falsityDefinitionDB)

theorem inferType_notAppDB_iff {p : DBTerm} {ty : Ty} :
    (notAppDB p).inferType context = some ty ↔
      p.inferType context = some Ty.bool ∧ ty = Ty.bool := by
  constructor
  · intro h
    obtain ⟨d, hnot, hp⟩ := DBTerm.inferType_app_eq_some_iff.mp h
    rw [inferType_notDB] at hnot
    obtain ⟨rfl, rfl⟩ := Ty.function_inj (Option.some.inj hnot)
    exact ⟨hp, rfl⟩
  · rintro ⟨hp, rfl⟩
    exact inferType_app_of inferType_notDB hp

theorem inferType_orDB : orDB.inferType context = some boolBinaryTy := by
  refine inferType_abs_of (inferType_abs_of
    (inferType_app_of (inferType_forallDB Ty.bool) (inferType_abs_of ?_)))
  exact inferType_impAppDB
    (inferType_impAppDB (by simp) (inferType_bound_zero _ _))
    (inferType_impAppDB (inferType_impAppDB (by simp) (inferType_bound_zero _ _))
      (inferType_bound_zero _ _))

theorem inferType_orAppDB {p q : DBTerm} (hp : p.inferType context = some Ty.bool)
    (hq : q.inferType context = some Ty.bool) :
    (orAppDB p q).inferType context = some Ty.bool :=
  (inferType_binary_iff inferType_orDB).mpr ⟨hp, hq, rfl⟩

theorem inferType_selectFirstDB : selectFirstDB.inferType context = some boolBinaryTy :=
  inferType_abs_of (inferType_abs_of (inferType_bound_one _ _ _))

theorem inferType_selectSecondDB : selectSecondDB.inferType context = some boolBinaryTy :=
  inferType_abs_of (inferType_abs_of (inferType_bound_zero _ _))

end Typing

/-! ## Instantiation and abstraction through the connectives -/

section Syntax

variable (replacement : DBTerm) (depth : Nat)

@[simp] theorem instantiateAt_truthDB : instantiateAt replacement depth truthDB = truthDB :=
  instantiateAt_closed inferType_truthDB replacement depth

@[simp] theorem instantiateAt_identityBool :
    instantiateAt replacement depth identityBool = identityBool :=
  instantiateAt_closed inferType_identityBool replacement depth

@[simp] theorem instantiateAt_forallDB (A : Ty) :
    instantiateAt replacement depth (forallDB A) = forallDB A :=
  instantiateAt_closed (inferType_forallDB A) replacement depth

@[simp] theorem instantiateAt_andDB : instantiateAt replacement depth andDB = andDB :=
  instantiateAt_closed inferType_andDB replacement depth

@[simp] theorem instantiateAt_impDB : instantiateAt replacement depth impDB = impDB :=
  instantiateAt_closed inferType_impDB replacement depth

@[simp] theorem instantiateAt_falsityDefinitionDB :
    instantiateAt replacement depth falsityDefinitionDB = falsityDefinitionDB :=
  instantiateAt_closed inferType_falsityDefinitionDB replacement depth

@[simp] theorem instantiateAt_existsDB (A : Ty) :
    instantiateAt replacement depth (DefinedConnectives.existsDB A) =
      DefinedConnectives.existsDB A :=
  instantiateAt_closed (inferType_existsDB A) replacement depth

@[simp] theorem instantiateAt_impAppDB (p q : DBTerm) :
    instantiateAt replacement depth (impAppDB p q) =
      impAppDB (instantiateAt replacement depth p) (instantiateAt replacement depth q) := by
  simp [impAppDB, instantiateAt]

@[simp] theorem instantiateAt_forallAppDB (A : Ty) (predicate : DBTerm) :
    instantiateAt replacement depth (forallAppDB A predicate) =
      forallAppDB A (instantiateAt replacement depth predicate) := by
  simp [forallAppDB, instantiateAt]

variable (sourceVar : SourceVar)

theorem freeNames_truthDB : truthDB.freeNames = ∅ := by
  simp [DBTerm.freeNames, truthDB, identityBool, equalityDB]

theorem freeNames_forallDB (A : Ty) : (forallDB A).freeNames = ∅ := by
  simp [DBTerm.freeNames, forallDB, equalityDB, freeNames_truthDB]

theorem freeNames_andDB : andDB.freeNames = ∅ := by
  simp [DBTerm.freeNames, andDB, equalityDB, freeNames_truthDB]

theorem freeNames_impDB : impDB.freeNames = ∅ := by
  simp [DBTerm.freeNames, impDB, equalityDB, freeNames_andDB]

theorem freeNames_existsDB (A : Ty) : (DefinedConnectives.existsDB A).freeNames = ∅ := by
  simp [DBTerm.freeNames, DefinedConnectives.existsDB, impAppDB, freeNames_forallDB,
    freeNames_impDB]

@[simp] theorem closeFreeAt_truthDB : closeFreeAt sourceVar depth truthDB = truthDB :=
  DBTerm.closeFreeAt_of_not_freeOccurrence
    (DBTerm.not_freeOccurrence_of_freeNames_eq_empty freeNames_truthDB _) depth

@[simp] theorem closeFreeAt_forallDB (A : Ty) :
    closeFreeAt sourceVar depth (forallDB A) = forallDB A :=
  DBTerm.closeFreeAt_of_not_freeOccurrence
    (DBTerm.not_freeOccurrence_of_freeNames_eq_empty (freeNames_forallDB A) _) depth

@[simp] theorem closeFreeAt_impDB : closeFreeAt sourceVar depth impDB = impDB :=
  DBTerm.closeFreeAt_of_not_freeOccurrence
    (DBTerm.not_freeOccurrence_of_freeNames_eq_empty freeNames_impDB _) depth

@[simp] theorem closeFreeAt_impAppDB (p q : DBTerm) :
    closeFreeAt sourceVar depth (impAppDB p q) =
      impAppDB (closeFreeAt sourceVar depth p) (closeFreeAt sourceVar depth q) := by
  simp [impAppDB, closeFreeAt]

@[simp] theorem closeFreeAt_forallAppDB (A : Ty) (predicate : DBTerm) :
    closeFreeAt sourceVar depth (forallAppDB A predicate) =
      forallAppDB A (closeFreeAt sourceVar depth predicate) := by
  simp [forallAppDB, closeFreeAt]

theorem not_freeOccurrence_impAppDB {sourceVar : SourceVar} {p q : DBTerm}
    (hp : ¬ FreeOccurrence sourceVar p) (hq : ¬ FreeOccurrence sourceVar q) :
    ¬ FreeOccurrence sourceVar (impAppDB p q) := by
  intro occurrence
  cases occurrence with
  | appFunction occurrence =>
      cases occurrence with
      | appFunction occurrence =>
          exact DBTerm.not_freeOccurrence_of_freeNames_eq_empty freeNames_impDB _ occurrence
      | appArgument occurrence => exact hp occurrence
  | appArgument occurrence => exact hq occurrence

end Syntax

end DerivedRules

namespace KernelProvable

open DerivedRules

variable {policy : AxiomPolicy}

/-! ## Beta conversion to the connective bodies -/

/-- BETA_CONV with the contractum given up to equality. -/
theorem betaConv_of_instantiateAt_eq {domain ty : Ty} {body argument result : DBTerm}
    (checked : (DBTerm.app (.abs domain body) argument).inferType [] = some ty)
    (hresult : instantiateAt argument 0 body = result) :
    KernelProvable policy ∅ (equalityDB ty (.app (.abs domain body) argument) result) :=
  hresult ▸ betaConv checked

/-- Two beta conversions with the contractum given up to equality. -/
theorem betaConvTwice_of_instantiateAt_eq {first second ty : Ty} {body left right result : DBTerm}
    (checked : (DBTerm.app (.app (.abs first (.abs second body)) left) right).inferType [] =
      some ty)
    (hresult : instantiateAt right 0 (instantiateAt left 1 body) = result) :
    KernelProvable policy ∅
      (equalityDB ty (.app (.app (.abs first (.abs second body)) left) right) result) :=
  hresult ▸ betaConvTwice checked

/-- `⊢ ∀ P = (P = λx. T)`. -/
theorem forallAppDB_beta {A : Ty} {predicate : DBTerm}
    (hpredicate : predicate.inferType [] = some (.function A Ty.bool)) :
    KernelProvable policy ∅ (equalityDB Ty.bool (forallAppDB A predicate)
      (equalityDB (.function A Ty.bool) predicate (.abs A truthDB))) :=
  betaConv_of_instantiateAt_eq (inferType_forallAppDB_iff.mpr ⟨hpredicate, rfl⟩)
    (by simp [instantiateAt, equalityDB])

/-- `⊢ (p ∧ q) = ((λf. f p q) = (λf. f T T))`. -/
theorem andAppDB_beta {p q : DBTerm} (hp : p.inferType [] = some Ty.bool)
    (hq : q.inferType [] = some Ty.bool) :
    KernelProvable policy ∅ (equalityDB Ty.bool (andAppDB p q) (andBodyDB p q)) :=
  betaConvTwice_of_instantiateAt_eq (inferType_andAppDB hp hq)
    (by simp [instantiateAt, equalityDB, instantiateAt_closed hp, andBodyDB])

/-- `⊢ (p ⇒ q) = ((p ∧ q) = p)`. -/
theorem impAppDB_beta {p q : DBTerm} (hp : p.inferType [] = some Ty.bool)
    (hq : q.inferType [] = some Ty.bool) :
    KernelProvable policy ∅
      (equalityDB Ty.bool (impAppDB p q) (equalityDB Ty.bool (andAppDB p q) p)) :=
  betaConvTwice_of_instantiateAt_eq (inferType_impAppDB hp hq)
    (by simp [instantiateAt, equalityDB, instantiateAt_closed hp, andAppDB])

/-- `⊢ ¬ p = (p ⇒ F)`. -/
theorem notAppDB_beta {p : DBTerm} (hp : p.inferType [] = some Ty.bool) :
    KernelProvable policy ∅
      (equalityDB Ty.bool (notAppDB p) (impAppDB p falsityDefinitionDB)) :=
  betaConv_of_instantiateAt_eq (inferType_notAppDB_iff.mpr ⟨hp, rfl⟩)
    (by simp [instantiateAt, impAppDB])

/-- `⊢ (p ∨ q) = ∀r. (p ⇒ r) ⇒ (q ⇒ r) ⇒ r`. -/
theorem orAppDB_beta {p q : DBTerm} (hp : p.inferType [] = some Ty.bool)
    (hq : q.inferType [] = some Ty.bool) :
    KernelProvable policy ∅ (equalityDB Ty.bool (orAppDB p q) (orBodyDB p q)) :=
  betaConvTwice_of_instantiateAt_eq (inferType_orAppDB hp hq)
    (by simp [instantiateAt, instantiateAt_closed hp, orBodyDB, forallAppDB])

/-- `⊢ ∃ P = ∀q. (∀x. P x ⇒ q) ⇒ q`. -/
theorem existsAppDB_beta {A : Ty} {predicate : DBTerm}
    (hpredicate : predicate.inferType [] = some (.function A Ty.bool)) :
    KernelProvable policy ∅
      (equalityDB Ty.bool (existsAppDB A predicate) (existsBodyDB A predicate)) :=
  betaConv_of_instantiateAt_eq (inferType_existsAppDB_iff.mpr ⟨hpredicate, rfl⟩)
    (by simp [instantiateAt, existsBodyDB, forallAppDB])

/-! ## Conjunction -/

/-- CONJ: from `A ⊢ p` and `B ⊢ q` derive `A ∪ B ⊢ p ∧ q`. -/
theorem conj {hyp hyp' : Finset CanonicalTerm} {p q : DBTerm}
    (hp : KernelProvable policy hyp p) (hq : KernelProvable policy hyp' q) :
    KernelProvable policy (hyp ∪ hyp') (andAppDB p q) := by
  obtain ⟨⟨name, _⟩, rfl, fresh, freshTerms⟩ :=
    exists_fresh_var boolBinaryTy (hyp ∪ hyp') [p, q]
  have absentP := freshTerms p (by simp)
  have absentQ := freshTerms q (by simp)
  have hselector : (DBTerm.free ⟨name, boolBinaryTy⟩).inferType [] = some boolBinaryTy := by
    simp
  have hpair := abs _ (mkComb (apTerm hselector (eqtIntro hp)) (eqtIntro hq)) fresh
  simp only [closeFreeAt, DBTerm.closeFreeAt_of_not_freeOccurrence absentP,
    DBTerm.closeFreeAt_of_not_freeOccurrence absentQ, sourceVarSame_eq_true_iff,
    if_true, closeFreeAt_truthDB] at hpair
  exact convRule (sym (andAppDB_beta hp.inferType hq.inferType)) hpair

/-- `⊢ (λf. f p q) s = s p q`. -/
theorem pairAppDB_beta {p q selector : DBTerm} (hp : p.inferType [] = some Ty.bool)
    (hq : q.inferType [] = some Ty.bool)
    (hselector : selector.inferType [] = some boolBinaryTy) :
    KernelProvable policy ∅
      (equalityDB Ty.bool (.app (.abs boolBinaryTy (.app (.app (.bound 0) p) q)) selector)
        (.app (.app selector p) q)) :=
  betaConv_of_instantiateAt_eq
    (inferType_app_of (inferType_abs_of (inferType_app_of (inferType_app_of
      (inferType_bound_zero _ _) (DBTerm.inferType_weaken_empty hp _))
      (DBTerm.inferType_weaken_empty hq _)))
      hselector)
    (by simp [instantiateAt, instantiateAt_closed hp, instantiateAt_closed hq])

/-- `⊢ (λa b. a) p q = p`. -/
theorem selectFirstDB_beta {p q : DBTerm} (hp : p.inferType [] = some Ty.bool)
    (hq : q.inferType [] = some Ty.bool) :
    KernelProvable policy ∅ (equalityDB Ty.bool (.app (.app selectFirstDB p) q) p) :=
  betaConvTwice_of_instantiateAt_eq
    ((inferType_binary_iff inferType_selectFirstDB).mpr ⟨hp, hq, rfl⟩)
    (by simp [instantiateAt_closed hp])

/-- `⊢ (λa b. b) p q = q`. -/
theorem selectSecondDB_beta {p q : DBTerm} (hp : p.inferType [] = some Ty.bool)
    (hq : q.inferType [] = some Ty.bool) :
    KernelProvable policy ∅ (equalityDB Ty.bool (.app (.app selectSecondDB p) q) q) :=
  betaConvTwice_of_instantiateAt_eq
    ((inferType_binary_iff inferType_selectSecondDB).mpr ⟨hp, hq, rfl⟩)
    (by simp [instantiateAt])

/-- From `A ⊢ p ∧ q` and a selector `s` with `⊢ s p q = r` and `⊢ s T T = T`,
derive `A ⊢ r`. -/
private theorem conjunct_of_selector {hyp : Finset CanonicalTerm} {p q result selector : DBTerm}
    (h : KernelProvable policy hyp (andAppDB p q))
    (hselector : selector.inferType [] = some boolBinaryTy)
    (hselect : KernelProvable policy ∅ (equalityDB Ty.bool (.app (.app selector p) q) result))
    (hselectTruth : KernelProvable policy ∅
      (equalityDB Ty.bool (.app (.app selector truthDB) truthDB) truthDB)) :
    KernelProvable policy hyp result := by
  obtain ⟨hp, hq, -⟩ := (inferType_binary_iff DefinedConnectives.andDB_inferType).mp h.inferType
  have hbody := apThm (convRule (andAppDB_beta hp hq) h) hselector
  have hleft := trans (pairAppDB_beta (policy := policy) hp hq hselector) hselect
  have hright := trans (pairAppDB_beta (policy := policy) inferType_truthDB
    inferType_truthDB hselector) hselectTruth
  exact eqtElim ((trans (trans (sym hleft) hbody) hright).congr_hyp (by simp))

/-- CONJUNCT1: from `A ⊢ p ∧ q` derive `A ⊢ p`. -/
theorem conjunct1 {hyp : Finset CanonicalTerm} {p q : DBTerm}
    (h : KernelProvable policy hyp (andAppDB p q)) : KernelProvable policy hyp p := by
  obtain ⟨hp, hq, -⟩ := (inferType_binary_iff DefinedConnectives.andDB_inferType).mp h.inferType
  exact conjunct_of_selector h inferType_selectFirstDB (selectFirstDB_beta hp hq)
    (selectFirstDB_beta inferType_truthDB inferType_truthDB)

/-- CONJUNCT2: from `A ⊢ p ∧ q` derive `A ⊢ q`. -/
theorem conjunct2 {hyp : Finset CanonicalTerm} {p q : DBTerm}
    (h : KernelProvable policy hyp (andAppDB p q)) : KernelProvable policy hyp q := by
  obtain ⟨hp, hq, -⟩ := (inferType_binary_iff DefinedConnectives.andDB_inferType).mp h.inferType
  exact conjunct_of_selector h inferType_selectSecondDB (selectSecondDB_beta hp hq)
    (selectSecondDB_beta inferType_truthDB inferType_truthDB)

/-! ## Implication -/

/-- MP: from `A ⊢ p ⇒ q` and `B ⊢ p` derive `A ∪ B ⊢ q`. -/
theorem mp {hyp hyp' : Finset CanonicalTerm} {p q : DBTerm}
    (himp : KernelProvable policy hyp (impAppDB p q)) (hp : KernelProvable policy hyp' p) :
    KernelProvable policy (hyp ∪ hyp') q := by
  obtain ⟨hpType, hqType, -⟩ :=
    (inferType_binary_iff DefinedConnectives.impDB_inferType).mp himp.inferType
  exact conjunct2 (eqMp (sym (convRule (impAppDB_beta hpType hqType) himp)) hp)

/-- DISCH: from `A ⊢ q` derive `A - {p} ⊢ p ⇒ q` for a Boolean term `p`. -/
theorem disch {hyp : Finset CanonicalTerm} {q : DBTerm} (p : CanonicalTerm) (hbool : p.IsBool)
    (h : KernelProvable policy hyp q) :
    KernelProvable policy (hyp.erase p) (impAppDB p.term q) := by
  have hpType : p.term.inferType [] = some Ty.bool := hbool ▸ p.checked
  let conjunction : CanonicalTerm :=
    ⟨andAppDB p.term q, Ty.bool, inferType_andAppDB hpType h.inferType⟩
  have hanti := deductAntisym conjunction p (conj (assume p hbool) h)
    (conjunct1 (assume conjunction rfl))
  refine (convRule (sym (impAppDB_beta hpType h.inferType)) hanti).congr_hyp ?_
  ext term
  simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton]
  tauto

/-- UNDISCH: from `A ⊢ p ⇒ q` derive `A ∪ {p} ⊢ q`. -/
theorem undisch {hyp : Finset CanonicalTerm} {q : DBTerm} (p : CanonicalTerm)
    (h : KernelProvable policy hyp (impAppDB p.term q)) :
    KernelProvable policy (insert p hyp) q := by
  obtain ⟨hpType, -, -⟩ :=
    (inferType_binary_iff DefinedConnectives.impDB_inferType).mp h.inferType
  have hbool : p.IsBool := DBTerm.inferType_unique p.checked hpType
  exact (mp h (assume p hbool)).congr_hyp (by rw [Finset.union_comm, ← Finset.insert_eq])

/-! ## Universal quantifier -/

/-- SPEC for a predicate: from `A ⊢ ∀ P` derive `A ⊢ P x`. -/
theorem specApp {hyp : Finset CanonicalTerm} {A : Ty} {predicate argument : DBTerm}
    (h : KernelProvable policy hyp (forallAppDB A predicate))
    (hargument : argument.inferType [] = some A) :
    KernelProvable policy hyp (.app predicate argument) := by
  obtain ⟨hpredicate, -⟩ := inferType_forallAppDB_iff.mp h.inferType
  have happ := apThm (convRule (forallAppDB_beta hpredicate) h) hargument
  have hbeta : KernelProvable policy ∅
      (equalityDB Ty.bool (.app (.abs A truthDB) argument) truthDB) :=
    betaConv_of_instantiateAt_eq (inferType_app_of (inferType_abs_of inferType_truthDB) hargument)
      (instantiateAt_truthDB argument 0)
  exact eqtElim ((trans happ hbeta).congr_hyp (Finset.union_empty hyp))

/-- SPEC: from `A ⊢ ∀x. t` derive `A ⊢ t[u/x]`. -/
theorem spec {hyp : Finset CanonicalTerm} {A : Ty} {body argument : DBTerm}
    (h : KernelProvable policy hyp (forallAppDB A (.abs A body)))
    (hargument : argument.inferType [] = some A) :
    KernelProvable policy hyp (instantiateAt argument 0 body) := by
  have happ := specApp h hargument
  exact convRule (betaConv happ.inferType) happ

/-- GEN: from `A ⊢ t`, with `x` not free in `A`, derive `A ⊢ ∀x. t`. -/
theorem gen {hyp : Finset CanonicalTerm} {body : DBTerm} (sourceVar : SourceVar)
    (h : KernelProvable policy hyp body) (fresh : ¬ FreeInHypotheses sourceVar hyp) :
    KernelProvable policy hyp
      (forallAppDB sourceVar.ty (.abs sourceVar.ty (closeFreeAt sourceVar 0 body))) := by
  have habs := abs sourceVar (eqtIntro h) fresh
  rw [closeFreeAt_truthDB] at habs
  exact convRule (sym (forallAppDB_beta (inferType_equality_operands habs).1)) habs


/-! ## Existential quantifier -/

/-- EXISTS for a predicate: from `A ⊢ P u` derive `A ⊢ ∃ P`. -/
theorem existsIntroApp {hyp : Finset CanonicalTerm} {A : Ty} {predicate argument : DBTerm}
    (h : KernelProvable policy hyp (.app predicate argument))
    (hargument : argument.inferType [] = some A) :
    KernelProvable policy hyp (existsAppDB A predicate) := by
  obtain ⟨A', hpredicate, hargument'⟩ := DBTerm.inferType_app_eq_some_iff.mp h.inferType
  obtain rfl := DBTerm.inferType_unique hargument hargument'
  obtain ⟨⟨name, _⟩, rfl, fresh, freshTerms⟩ :=
    exists_fresh_var Ty.bool hyp [predicate, argument]
  have absentPredicate := freshTerms predicate (by simp)
  have hconclusion : (DBTerm.free ⟨name, Ty.bool⟩).inferType [] = some Ty.bool := by simp
  have hpremise :=
    inferType_forallAppDB_iff.mpr ⟨inferType_abs_of (context := []) (domain := A)
      (body := impAppDB (.app predicate (.bound 0)) (.free ⟨name, Ty.bool⟩))
      (inferType_impAppDB (inferType_app_of (DBTerm.inferType_weaken_empty hpredicate _)
        (inferType_bound_zero _ _)) (DBTerm.inferType_weaken_empty hconclusion _)), rfl⟩
  obtain ⟨premise, hpremiseTerm⟩ : ∃ premise : CanonicalTerm, premise.term =
      forallAppDB A (.abs A (impAppDB (.app predicate (.bound 0)) (.free ⟨name, Ty.bool⟩))) :=
    ⟨⟨_, Ty.bool, hpremise⟩, rfl⟩
  have hpremiseBool : premise.IsBool :=
    DBTerm.inferType_unique premise.checked (hpremiseTerm ▸ hpremise)
  have hassume := assume (policy := policy) premise hpremiseBool
  rw [hpremiseTerm] at hassume
  have hinstance := spec hassume hargument
  simp only [instantiateAt_impAppDB, instantiateAt, instantiateAt_closed hpredicate,
    DBTerm.instantiateAt_target] at hinstance
  have hdisch := disch premise hpremiseBool (mp hinstance h)
  rw [hpremiseTerm] at hdisch
  have hsubset : ({premise} ∪ hyp).erase premise ⊆ hyp := by
    intro term hterm
    simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_singleton] at hterm
    tauto
  have hgen := gen _ hdisch fun occurs => fresh (freeInHypotheses_mono hsubset occurs)
  simp only [closeFreeAt_impAppDB, closeFreeAt_forallAppDB, closeFreeAt,
    DBTerm.closeFreeAt_of_not_freeOccurrence absentPredicate, sourceVarSame_eq_true_iff,
    if_true] at hgen
  exact weaken (convRule (sym (existsAppDB_beta hpredicate)) hgen) hsubset h.hyp_isBool

/-- EXISTS: from `A ⊢ t[u/x]` derive `A ⊢ ∃x. t`. -/
theorem existsIntro {hyp : Finset CanonicalTerm} {A : Ty} {body argument : DBTerm}
    (h : KernelProvable policy hyp (instantiateAt argument 0 body))
    (hargument : argument.inferType [] = some A) :
    KernelProvable policy hyp (existsAppDB A (.abs A body)) := by
  have hbody : body.inferType [A] = some Ty.bool := by
    simpa using DBTerm.inferType_of_inferType_instantiateAt hargument body [] h.inferType
  exact existsIntroApp
    (convRule (sym (betaConv (inferType_app_of (inferType_abs_of hbody) hargument))) h) hargument

/-- The common core of CHOOSE: from `A ⊢ ∃ P` and `B ⊢ P v ⇒ t`, with `v` not
free in `P`, `t` or `B`, derive `A ∪ B ⊢ t`. -/
theorem chooseOfImp {hyp hyp' : Finset CanonicalTerm} {predicate concl : DBTerm}
    (sourceVar : SourceVar)
    (hexists : KernelProvable policy hyp (existsAppDB sourceVar.ty predicate))
    (himp : KernelProvable policy hyp'
      (impAppDB (.app predicate (.free sourceVar)) concl))
    (absentPredicate : ¬ FreeOccurrence sourceVar predicate)
    (absentConcl : ¬ FreeOccurrence sourceVar concl)
    (fresh : ¬ FreeInHypotheses sourceVar hyp') :
    KernelProvable policy (hyp ∪ hyp') concl := by
  obtain ⟨hpredicate, -⟩ := inferType_existsAppDB_iff.mp hexists.inferType
  obtain ⟨-, hconcl, -⟩ :=
    (inferType_binary_iff DefinedConnectives.impDB_inferType).mp himp.inferType
  have hgen := gen sourceVar himp fresh
  simp only [closeFreeAt_impAppDB, closeFreeAt, sourceVarSame_eq_true_iff, if_true,
    DBTerm.closeFreeAt_of_not_freeOccurrence absentPredicate,
    DBTerm.closeFreeAt_of_not_freeOccurrence absentConcl] at hgen
  have hinstance := spec (convRule (existsAppDB_beta hpredicate) hexists) hconcl
  simp only [instantiateAt_impAppDB, instantiateAt_forallAppDB, instantiateAt,
    instantiateAt_closed hpredicate, DBTerm.instantiateAt_target] at hinstance
  exact mp hinstance hgen

/-- CHOOSE for a predicate: from `A ⊢ ∃ P` and `B ⊢ t`, with `v` not free in
`P`, `t` or `B - {P v}`, derive `A ∪ (B - {P v}) ⊢ t`. -/
theorem chooseApp {hyp hyp' : Finset CanonicalTerm} {predicate concl : DBTerm}
    (sourceVar : SourceVar) (witness : CanonicalTerm)
    (hwitness : witness.term = .app predicate (.free sourceVar))
    (hexists : KernelProvable policy hyp (existsAppDB sourceVar.ty predicate))
    (h : KernelProvable policy hyp' concl)
    (absentPredicate : ¬ FreeOccurrence sourceVar predicate)
    (absentConcl : ¬ FreeOccurrence sourceVar concl)
    (fresh : ¬ FreeInHypotheses sourceVar (hyp'.erase witness)) :
    KernelProvable policy (hyp ∪ hyp'.erase witness) concl := by
  obtain ⟨hpredicate, -⟩ := inferType_existsAppDB_iff.mp hexists.inferType
  have hwitnessBool : witness.IsBool := DBTerm.inferType_unique witness.checked
    (hwitness ▸ inferType_app_of hpredicate (by simp))
  have himp := disch witness hwitnessBool h
  rw [hwitness] at himp
  exact chooseOfImp sourceVar hexists himp absentPredicate absentConcl fresh

/-- CHOOSE: from `A ⊢ ∃x. s` and `B ⊢ t`, with `v` not free in `∃x. s`, `t` or
`B - {s[v/x]}`, derive `A ∪ (B - {s[v/x]}) ⊢ t`. -/
theorem choose {hyp hyp' : Finset CanonicalTerm} {body concl : DBTerm}
    (sourceVar : SourceVar) (witness : CanonicalTerm)
    (hwitness : witness.term = instantiateAt (.free sourceVar) 0 body)
    (hexists : KernelProvable policy hyp
      (existsAppDB sourceVar.ty (.abs sourceVar.ty body)))
    (h : KernelProvable policy hyp' concl)
    (absentPredicate : ¬ FreeOccurrence sourceVar (.abs sourceVar.ty body))
    (absentConcl : ¬ FreeOccurrence sourceVar concl)
    (fresh : ¬ FreeInHypotheses sourceVar (hyp'.erase witness)) :
    KernelProvable policy (hyp ∪ hyp'.erase witness) concl := by
  obtain ⟨hpredicate, -⟩ := inferType_existsAppDB_iff.mp hexists.inferType
  obtain ⟨codomain, hbody, hfunction⟩ := DBTerm.inferType_abs_eq_some_iff.mp hpredicate
  obtain ⟨-, rfl⟩ := Ty.function_inj hfunction
  have hvar : (DBTerm.free sourceVar).inferType [] = some sourceVar.ty := by simp
  have hredex : (DBTerm.app (.abs sourceVar.ty body) (.free sourceVar)).inferType [] =
      some Ty.bool := inferType_app_of hpredicate hvar
  have hwitnessBool : witness.IsBool := DBTerm.inferType_unique witness.checked
    (hwitness ▸ DBTerm.inferType_instantiateAt _ body _ hvar [] (by simpa using hbody))
  have himp := disch witness hwitnessBool h
  rw [hwitness] at himp
  have hcongruence :=
    apThm (apTerm (inferType_impDB (context := [])) (betaConv (policy := policy) hredex))
      h.inferType
  exact chooseOfImp sourceVar hexists (convRule (sym hcongruence) himp) absentPredicate
    absentConcl fresh

/-! ## Disjunction -/

/-- The fresh-variable core of DISJ1 and DISJ2: from `B ⊢ (p ⇒ r) ⇒ (q ⇒ r) ⇒ r`
for a variable `r` free in neither `p`, `q` nor `B`, derive `B ⊢ p ∨ q`. -/
private theorem orAppDB_of_matrix {hyp : Finset CanonicalTerm} {p q : DBTerm}
    (sourceVar : SourceVar) (hbool : sourceVar.ty = Ty.bool)
    (h : KernelProvable policy hyp (impAppDB (impAppDB p (.free sourceVar))
      (impAppDB (impAppDB q (.free sourceVar)) (.free sourceVar))))
    (absentP : ¬ FreeOccurrence sourceVar p) (absentQ : ¬ FreeOccurrence sourceVar q)
    (fresh : ¬ FreeInHypotheses sourceVar hyp) :
    KernelProvable policy hyp (orAppDB p q) := by
  obtain ⟨hleft, hright, -⟩ :=
    (inferType_binary_iff DefinedConnectives.impDB_inferType).mp h.inferType
  obtain ⟨hp, -, -⟩ := (inferType_binary_iff DefinedConnectives.impDB_inferType).mp hleft
  obtain ⟨hright', -, -⟩ := (inferType_binary_iff DefinedConnectives.impDB_inferType).mp hright
  obtain ⟨hq, -, -⟩ := (inferType_binary_iff DefinedConnectives.impDB_inferType).mp hright'
  obtain ⟨name, ty⟩ := sourceVar
  subst hbool
  have hgen := gen _ h fresh
  simp only [closeFreeAt_impAppDB, closeFreeAt, sourceVarSame_eq_true_iff, if_true,
    DBTerm.closeFreeAt_of_not_freeOccurrence absentP,
    DBTerm.closeFreeAt_of_not_freeOccurrence absentQ] at hgen
  exact convRule (sym (orAppDB_beta hp hq)) hgen

/-- A checked Boolean term with a given canonical syntax. -/
private theorem exists_canonical_bool {term : DBTerm} (checked : term.inferType [] = some Ty.bool) :
    ∃ canonical : CanonicalTerm, canonical.term = term ∧ canonical.IsBool :=
  ⟨⟨term, Ty.bool, checked⟩, rfl, rfl⟩

/-- DISJ1: from `A ⊢ p` derive `A ⊢ p ∨ q`. -/
theorem disj1 {hyp : Finset CanonicalTerm} {p q : DBTerm} (h : KernelProvable policy hyp p)
    (hq : q.inferType [] = some Ty.bool) :
    KernelProvable policy hyp (orAppDB p q) := by
  have hp := h.inferType
  obtain ⟨⟨name, _⟩, rfl, fresh, freshTerms⟩ := exists_fresh_var Ty.bool hyp [p, q]
  have hr : (DBTerm.free ⟨name, Ty.bool⟩).inferType [] = some Ty.bool := by simp
  obtain ⟨left, hleft, hleftBool⟩ := exists_canonical_bool (inferType_impAppDB hp hr)
  obtain ⟨right, hright, hrightBool⟩ := exists_canonical_bool (inferType_impAppDB hq hr)
  have hassume := assume (policy := policy) left hleftBool
  rw [hleft] at hassume
  have hmatrix := disch left hleftBool (disch right hrightBool (mp hassume h))
  rw [hleft, hright] at hmatrix
  have hsubset : (({left} ∪ hyp).erase right).erase left ⊆ hyp := by
    intro term hterm
    simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_singleton] at hterm
    tauto
  exact weaken (orAppDB_of_matrix _ rfl hmatrix (freshTerms p (by simp))
    (freshTerms q (by simp)) fun occurs => fresh (freeInHypotheses_mono hsubset occurs))
    hsubset h.hyp_isBool

/-- DISJ2: from `A ⊢ q` derive `A ⊢ p ∨ q`. -/
theorem disj2 {hyp : Finset CanonicalTerm} {p q : DBTerm} (hp : p.inferType [] = some Ty.bool)
    (h : KernelProvable policy hyp q) :
    KernelProvable policy hyp (orAppDB p q) := by
  have hq := h.inferType
  obtain ⟨⟨name, _⟩, rfl, fresh, freshTerms⟩ := exists_fresh_var Ty.bool hyp [p, q]
  have hr : (DBTerm.free ⟨name, Ty.bool⟩).inferType [] = some Ty.bool := by simp
  obtain ⟨left, hleft, hleftBool⟩ := exists_canonical_bool (inferType_impAppDB hp hr)
  obtain ⟨right, hright, hrightBool⟩ := exists_canonical_bool (inferType_impAppDB hq hr)
  have hassume := assume (policy := policy) right hrightBool
  rw [hright] at hassume
  have hmatrix := disch left hleftBool (disch right hrightBool (mp hassume h))
  rw [hleft, hright] at hmatrix
  have hsubset : (({right} ∪ hyp).erase right).erase left ⊆ hyp := by
    intro term hterm
    simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_singleton] at hterm
    tauto
  exact weaken (orAppDB_of_matrix _ rfl hmatrix (freshTerms p (by simp))
    (freshTerms q (by simp)) fun occurs => fresh (freeInHypotheses_mono hsubset occurs))
    hsubset h.hyp_isBool

/-- DISJ_CASES: from `A ⊢ p ∨ q`, `B ⊢ r` and `C ⊢ r` derive
`A ∪ (B - {p}) ∪ (C - {q}) ⊢ r`. -/
theorem disjCases {hyp hypLeft hypRight : Finset CanonicalTerm} {concl : DBTerm}
    (p q : CanonicalTerm) (h : KernelProvable policy hyp (orAppDB p.term q.term))
    (hleft : KernelProvable policy hypLeft concl)
    (hright : KernelProvable policy hypRight concl) :
    KernelProvable policy (hyp ∪ hypLeft.erase p ∪ hypRight.erase q) concl := by
  obtain ⟨hp, hq, -⟩ := (inferType_binary_iff inferType_orDB).mp h.inferType
  have hinstance := spec (convRule (orAppDB_beta hp hq) h) hleft.inferType
  simp only [instantiateAt_impAppDB, instantiateAt_closed hp, instantiateAt_closed hq,
    DBTerm.instantiateAt_target] at hinstance
  exact mp (mp hinstance (disch p (DBTerm.inferType_unique p.checked hp) hleft))
    (disch q (DBTerm.inferType_unique q.checked hq) hright)

/-! ## Negation and falsity -/

/-- NOT_ELIM: from `A ⊢ ¬p` derive `A ⊢ p ⇒ F`. -/
theorem notElim {hyp : Finset CanonicalTerm} {p : DBTerm}
    (h : KernelProvable policy hyp (notAppDB p)) :
    KernelProvable policy hyp (impAppDB p falsityDefinitionDB) :=
  convRule (notAppDB_beta (inferType_notAppDB_iff.mp h.inferType).1) h

/-- NOT_INTRO: from `A ⊢ p ⇒ F` derive `A ⊢ ¬p`. -/
theorem notIntro {hyp : Finset CanonicalTerm} {p : DBTerm}
    (h : KernelProvable policy hyp (impAppDB p falsityDefinitionDB)) :
    KernelProvable policy hyp (notAppDB p) :=
  convRule (sym (notAppDB_beta
    ((inferType_binary_iff DefinedConnectives.impDB_inferType).mp h.inferType).1)) h

/-- CONTR: from `A ⊢ F` derive `A ⊢ p` for a Boolean term `p`. -/
theorem contr {hyp : Finset CanonicalTerm} {p : DBTerm}
    (h : KernelProvable policy hyp falsityDefinitionDB) (hp : p.inferType [] = some Ty.bool) :
    KernelProvable policy hyp p := by
  have happ := specApp (A := Ty.bool) (predicate := identityBool) h hp
  exact convRule (betaConv_of_instantiateAt_eq (domain := Ty.bool) (body := .bound 0) happ.inferType
    (DBTerm.instantiateAt_target p 0)) happ


/-! ## Equivalence -/

/-- IMP_ANTISYM_RULE: from `A ⊢ p ⇒ q` and `B ⊢ q ⇒ p` derive `A ∪ B ⊢ p = q`. -/
theorem impAntisym {hyp hyp' : Finset CanonicalTerm} (p q : CanonicalTerm)
    (hpq : KernelProvable policy hyp (impAppDB p.term q.term))
    (hqp : KernelProvable policy hyp' (impAppDB q.term p.term)) :
    KernelProvable policy (hyp ∪ hyp') (equalityDB Ty.bool p.term q.term) := by
  have hanti := deductAntisym p q (undisch q hqp) (undisch p hpq)
  refine weaken hanti ?_ (fun term hterm => ?_)
  · intro term hterm
    simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hterm ⊢
    tauto
  · rcases Finset.mem_union.mp hterm with hterm | hterm
    · exact hpq.hyp_isBool term hterm
    · exact hqp.hyp_isBool term hterm

/-- EQ_IMP_RULE, first half: from `A ⊢ p = q` derive `A ⊢ p ⇒ q`. -/
theorem eqImpRuleLeft {hyp : Finset CanonicalTerm} {q : DBTerm} (p : CanonicalTerm)
    (h : KernelProvable policy hyp (equalityDB Ty.bool p.term q)) :
    KernelProvable policy hyp (impAppDB p.term q) := by
  have hbool : p.IsBool := DBTerm.inferType_unique p.checked (inferType_equality_operands h).1
  refine weaken (disch p hbool (eqMp h (assume p hbool))) ?_ h.hyp_isBool
  intro term hterm
  simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_singleton] at hterm
  tauto

/-- EQ_IMP_RULE, second half: from `A ⊢ p = q` derive `A ⊢ q ⇒ p`. -/
theorem eqImpRuleRight {hyp : Finset CanonicalTerm} {p : DBTerm} (q : CanonicalTerm)
    (h : KernelProvable policy hyp (equalityDB Ty.bool p q.term)) :
    KernelProvable policy hyp (impAppDB q.term p) :=
  eqImpRuleLeft q (sym h)

end KernelProvable

/-! ## Controls -/

namespace DerivedRulesExamples

open KernelProvable DerivedRules BindingExamples SequentExamples

/-- Positive control: `⊢ T` in the axiom-free kernel. -/
theorem truth_provable : KernelProvable emptyAxiomPolicy ∅ truthDB := truth

/-- The free Boolean variables `p` and `q`. -/
def pTerm : CanonicalTerm := boolVariable "p"
def qTerm : CanonicalTerm := boolVariable "q"

/-- The checked term `p ∧ q`. -/
def pAndQ : CanonicalTerm :=
  ⟨andAppDB pTerm.term qTerm.term, Ty.bool,
    inferType_andAppDB (by simp [pTerm, boolVariable]) (by simp [qTerm, boolVariable])⟩

/-- Positive control: `p ∧ q ⊢ q ∧ p` in the axiom-free kernel. -/
theorem and_comm_provable :
    KernelProvable emptyAxiomPolicy {pAndQ} (andAppDB qTerm.term pTerm.term) :=
  (conj (conjunct2 (assume pAndQ rfl)) (conjunct1 (assume pAndQ rfl))).congr_hyp
    (Finset.union_self _)

/-- Positive control: `⊢ p ⇒ p`; the discharged hypothesis is removed. -/
theorem imp_refl_provable :
    KernelProvable emptyAxiomPolicy ∅ (impAppDB pTerm.term pTerm.term) :=
  (disch pTerm rfl (assume pTerm rfl)).congr_hyp (Finset.erase_singleton pTerm)

/-- The checked term `p ∨ q`. -/
def pOrQ : CanonicalTerm :=
  ⟨orAppDB pTerm.term qTerm.term, Ty.bool,
    inferType_orAppDB (by simp [pTerm, boolVariable]) (by simp [qTerm, boolVariable])⟩

/-- Positive control: `p ∨ q ⊢ q ∨ p` in the axiom-free kernel; each case
discharges its own hypothesis. -/
theorem or_comm_provable :
    KernelProvable emptyAxiomPolicy {pOrQ} (orAppDB qTerm.term pTerm.term) := by
  have hp : pTerm.term.inferType [] = some Ty.bool := by simp [pTerm, boolVariable]
  have hq : qTerm.term.inferType [] = some Ty.bool := by simp [qTerm, boolVariable]
  refine (disjCases pTerm qTerm (assume pOrQ rfl) (disj2 hq (assume pTerm rfl))
    (disj1 (assume qTerm rfl) hp)).congr_hyp ?_
  simp

/-- The checked term `x = y` for individual variables `x` and `y`. -/
def xEqYTerm : CanonicalTerm :=
  ⟨equalityDB Examples.individual (.free xIndividual) (.free yIndividual), Ty.bool,
    inferType_equalityDB (by simp [xIndividual]) (by simp [yIndividual])⟩

/-- `∀x. x = y`, what GEN over `x` would produce from `x = y ⊢ x = y` without
its freshness condition. -/
def forallXEqYDB : DBTerm :=
  forallAppDB xIndividual.ty (.abs xIndividual.ty (closeFreeAt xIndividual 0 xEqYTerm.term))

theorem forallXEqYDB_eq :
    forallXEqYDB = forallAppDB Examples.individual
      (.abs Examples.individual
        (equalityDB Examples.individual (.bound 0) (.free yIndividual))) := by
  have different : xIndividual ≠ yIndividual := by
    simp [xIndividual, yIndividual, Name.global]
  have hty : xIndividual.ty = Examples.individual := rfl
  simp [forallXEqYDB, xEqYTerm, equalityDB, closeFreeAt, different, hty]

/-- The target formula `∀x. x = y`, with the defined universal quantifier. -/
def forallXEqYFormula : HOL.ClosedFormula Symbol :=
  .app (ExcludedMiddle.forallTerm Examples.individual.toHOL)
    (.lam (.eq (.var .vz) (.const (Symbol.ofVar yIndividual))))

theorem forallXEqYDB_translates : Translates [] forallXEqYDB .prop forallXEqYFormula := by
  rw [forallXEqYDB_eq]
  exact .app rfl (ExcludedMiddle.forallDB_translates [] rfl)
    (.abs rfl (.equalityApp (equalityOperand?_equality _) rfl (.bound .vz) (.free rfl)))

theorem xEqYTerm_translates :
    Translates [] xEqYTerm.term .prop
      (.eq (.const (Symbol.ofVar xIndividual)) (.const (Symbol.ofVar yIndividual))) :=
  .equalityApp (equalityOperand?_equality _) rfl (.free rfl) (.free rfl)

theorem individual_toHOL_base : ∃ base, Examples.individual.toHOL = .base base := by
  refine ⟨_, Ty.toHOL_of_isAtomic ⟨rfl, ?_⟩⟩
  exact Bool.eq_false_iff.mpr fun h => by
    simp [Ty.isBool_eq_true_iff, Examples.individual, Ty.bool, TypeOp.bool, Name.global] at h

/-- In the two-point model a variable of a base type is not equal to every
value. -/
theorem twoPointModel_not_models_forall_eq_const {τ : HOL.Ty AtomicTy} (symbol : Symbol τ)
    (base : ∃ b, τ = .base b) :
    ¬ twoPointModel.models
      (.app (ExcludedMiddle.forallTerm τ) (.lam (.eq (.var .vz) (.const symbol)))) := by
  obtain ⟨b, rfl⟩ := base
  intro holds
  have atTrue := holds (ULift.up true) trivial
  exact Bool.noConfusion (congrArg ULift.down (atTrue.mpr fun _ _ => Iff.rfl))

/-- Soundness of `KernelProvable` in the two-point model, for any policy whose
axioms are translated-provable from no background sentences. -/
theorem twoPointModel_of_kernelProvable {policy : AxiomPolicy}
    (policyProvable : ∀ sequent, policy sequent → TranslatedProvable ∅ sequent)
    {hyp : Finset CanonicalTerm} {concl : DBTerm} (h : KernelProvable policy hyp concl) :
    ∃ φ, Translates [] concl .prop φ ∧
      ((∀ ψ ∈ translatedHypotheses hyp, twoPointModel.models ψ) →
        twoPointModel.models φ) := by
  obtain ⟨out, hout, rfl, rfl⟩ := h
  exact translatedProvable_twoPointModel
    (derives_translatedProvable_of_policy variableFreeSubstitutionClosed_empty policyProvable hout)

/-- **Negative control: the freshness condition of GEN carries weight.**  For
every policy whose axioms are translated-provable, `x = y ⊢ x = y` is provable
and `x` is free in its hypothesis, while `x = y ⊢ ∀x. x = y`, the result of GEN
over `x` without its freshness condition, is not provable: in the two-point
model the hypothesis holds and the conclusion fails. -/
theorem gen_freshness_needed {policy : AxiomPolicy}
    (policyProvable : ∀ sequent, policy sequent → TranslatedProvable ∅ sequent) :
    KernelProvable policy {xEqYTerm} xEqYTerm.term ∧
      FreeInHypotheses xIndividual {xEqYTerm} ∧
      ¬ KernelProvable policy {xEqYTerm} forallXEqYDB := by
  refine ⟨assume xEqYTerm rfl,
    ⟨xEqYTerm, Finset.mem_singleton_self _, .appFunction (.appArgument .here)⟩, ?_⟩
  intro h
  obtain ⟨φ, hφ, holds⟩ := twoPointModel_of_kernelProvable policyProvable h
  rw [hφ.unique_eq forallXEqYDB_translates] at holds
  refine twoPointModel_not_models_forall_eq_const (Symbol.ofVar yIndividual)
    individual_toHOL_base (holds ?_)
  rintro ψ ⟨term, hterm, htranslation⟩
  rw [Finset.mem_singleton.mp hterm] at htranslation
  rw [htranslation.unique_eq xEqYTerm_translates]
  exact HOL.PreModel.eqv_refl _ trivial

end DerivedRulesExamples

end Mettapedia.Languages.OpenTheory

