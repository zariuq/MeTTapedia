import Mettapedia.GSLT.LanguageDef.ScopePolicies.Core

/-!
# What the static equivalence of the core keeps of an observation

Two observations of the core are statically equivalent when a chain of bags
links them, consecutive bags being renamings, result by result, of one bag of
the identity model.  This module says what such a chain keeps.

* The number of results (`coreEquiv_done_length`, in `ScopePolicies.Core`).
* Result by result, in order (`coreEquiv_done_firstOrder`): one result has a
  first-order answer exactly when the other has, and then the two results
  match up to a one-to-one correspondence of names (`IdSlot.FOMatch`): the
  answers have the same symbols in the same shape, with corresponding names;
  corresponding names hold the same value in the two stores; and every name
  that either store binds has a partner.  So the answers with their
  multiplicity, the stores, and which names share a cell are kept.

`FOEquiv` is that relation on results; it is an equivalence relation
(`FOEquiv.refl`, `FOEquiv.symm`, `FOEquiv.trans`), which is why it passes
along a chain.  For results whose answer is not first-order (a lambda, a
quotation, contextual code) nothing more than the count is proved here.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ScopePolicies

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline
open Mettapedia.GSLT.LanguageDef.TemplateScope
open Mettapedia.GSLT.LanguageDef.TemplateScope.IdSlot

universe u v

variable {S : Type u}

/-! ## Correspondence of first-order terms -/

section Correspondence

variable {Y₁ Y₂ Y₃ : Type v}

/-- Corresponding terms are first-order. -/
theorem FOCorr.firstOrder {related : Nm Y₁ → Nm Y₂ → Prop} {t₁ : Tm S Y₁} :
    ∀ {t₂ : Tm S Y₂}, FOCorr related t₁ t₂ → t₁.FirstOrder = true ∧ t₂.FirstOrder = true := by
  induction t₁ with
  | sym s =>
      intro t₂ corresponds
      cases t₂ <;> first | exact ⟨rfl, rfl⟩ | exact corresponds.elim
  | var n =>
      intro t₂ corresponds
      cases t₂ <;> first | exact ⟨rfl, rfl⟩ | exact corresponds.elim
  | app f a ihf iha =>
      intro t₂ corresponds
      cases t₂ with
      | app f' a' =>
          obtain ⟨functions, arguments⟩ := corresponds
          simp only [Tm.FirstOrder, Bool.and_eq_true]
          exact ⟨⟨(ihf functions).1, (iha arguments).1⟩, (ihf functions).2, (iha arguments).2⟩
      | sym _ | fn _ | var _ | pvar _ | lam _ _ _ | quote _ | ctx _ _ | pquote _ | letP _ _ _
        | alt _ _ => exact corresponds.elim
  | fn _ | pvar _ | lam _ _ _ | quote _ | ctx _ _ | pquote _ | letP _ _ _ | alt _ _ =>
      intro t₂ corresponds
      cases t₂ <;> exact corresponds.elim

/-- A first-order term corresponds to itself, name by name. -/
theorem FOCorr.refl : ∀ {t : Tm S Y₁}, t.FirstOrder = true → FOCorr (fun n m => n = m) t t
  | .sym _, _ => rfl
  | .var _, _ => rfl
  | .app f a, isFirstOrder => by
      simp only [Tm.FirstOrder, Bool.and_eq_true] at isFirstOrder
      exact ⟨FOCorr.refl isFirstOrder.1, FOCorr.refl isFirstOrder.2⟩
  | .fn _, h => by simp [Tm.FirstOrder] at h
  | .pvar _, h => by simp [Tm.FirstOrder] at h
  | .lam _ _ _, h => by simp [Tm.FirstOrder] at h
  | .quote _, h => by simp [Tm.FirstOrder] at h
  | .ctx _ _, h => by simp [Tm.FirstOrder] at h
  | .pquote _, h => by simp [Tm.FirstOrder] at h
  | .letP _ _ _, h => by simp [Tm.FirstOrder] at h
  | .alt _ _, h => by simp [Tm.FirstOrder] at h

/-- Correspondence read the other way. -/
theorem FOCorr.flip {related : Nm Y₁ → Nm Y₂ → Prop} {t₁ : Tm S Y₁} :
    ∀ {t₂ : Tm S Y₂}, FOCorr related t₁ t₂ → FOCorr (fun m n => related n m) t₂ t₁ := by
  induction t₁ with
  | sym s =>
      intro t₂ corresponds
      cases t₂ with
      | sym s' => exact (show s = s' from corresponds).symm
      | fn _ | var _ | pvar _ | lam _ _ _ | app _ _ | quote _ | ctx _ _ | pquote _ | letP _ _ _
        | alt _ _ => exact corresponds.elim
  | var n =>
      intro t₂ corresponds
      cases t₂ with
      | var m => exact corresponds
      | sym _ | fn _ | pvar _ | lam _ _ _ | app _ _ | quote _ | ctx _ _ | pquote _ | letP _ _ _
        | alt _ _ => exact corresponds.elim
  | app f a ihf iha =>
      intro t₂ corresponds
      cases t₂ with
      | app f' a' => exact ⟨ihf corresponds.1, iha corresponds.2⟩
      | sym _ | fn _ | var _ | pvar _ | lam _ _ _ | quote _ | ctx _ _ | pquote _ | letP _ _ _
        | alt _ _ => exact corresponds.elim
  | fn _ | pvar _ | lam _ _ _ | quote _ | ctx _ _ | pquote _ | letP _ _ _ | alt _ _ =>
      intro t₂ corresponds
      cases t₂ <;> exact corresponds.elim

/-- Correspondences compose. -/
theorem FOCorr.comp {first : Nm Y₁ → Nm Y₂ → Prop} {second : Nm Y₂ → Nm Y₃ → Prop}
    {t₁ : Tm S Y₁} :
    ∀ {t₂ : Tm S Y₂} {t₃ : Tm S Y₃}, FOCorr first t₁ t₂ → FOCorr second t₂ t₃ →
      FOCorr (fun n k => ∃ m, first n m ∧ second m k) t₁ t₃ := by
  induction t₁ with
  | sym s =>
      intro t₂ t₃ firstCorr secondCorr
      cases t₂ with
      | sym s' =>
          cases t₃ with
          | sym s'' => exact (show s = s' from firstCorr).trans secondCorr
          | fn _ | var _ | pvar _ | lam _ _ _ | app _ _ | quote _ | ctx _ _ | pquote _
            | letP _ _ _ | alt _ _ => exact secondCorr.elim
      | fn _ | var _ | pvar _ | lam _ _ _ | app _ _ | quote _ | ctx _ _ | pquote _ | letP _ _ _
        | alt _ _ => exact firstCorr.elim
  | var n =>
      intro t₂ t₃ firstCorr secondCorr
      cases t₂ with
      | var m =>
          cases t₃ with
          | var k => exact ⟨m, firstCorr, secondCorr⟩
          | sym _ | fn _ | pvar _ | lam _ _ _ | app _ _ | quote _ | ctx _ _ | pquote _
            | letP _ _ _ | alt _ _ => exact secondCorr.elim
      | sym _ | fn _ | pvar _ | lam _ _ _ | app _ _ | quote _ | ctx _ _ | pquote _ | letP _ _ _
        | alt _ _ => exact firstCorr.elim
  | app f a ihf iha =>
      intro t₂ t₃ firstCorr secondCorr
      cases t₂ with
      | app f' a' =>
          cases t₃ with
          | app f'' a'' =>
              exact ⟨ihf firstCorr.1 secondCorr.1, iha firstCorr.2 secondCorr.2⟩
          | sym _ | fn _ | var _ | pvar _ | lam _ _ _ | quote _ | ctx _ _ | pquote _
            | letP _ _ _ | alt _ _ => exact secondCorr.elim
      | sym _ | fn _ | var _ | pvar _ | lam _ _ _ | quote _ | ctx _ _ | pquote _ | letP _ _ _
        | alt _ _ => exact firstCorr.elim
  | fn _ | pvar _ | lam _ _ _ | quote _ | ctx _ _ | pquote _ | letP _ _ _ | alt _ _ =>
      intro t₂ t₃ firstCorr _
      cases t₂ <;> exact firstCorr.elim

end Correspondence

/-! ## Matching of results -/

variable {X : Type v}

/-- A result with a first-order answer matches itself. -/
theorem FOMatch.refl {result : Tm S (Slot X) × GStore S (Slot X)}
    (isFirstOrder : result.1.FirstOrder = true) : FOMatch result result :=
  ⟨fun n m => n = m, fun _ _ _ first second => first.symm.trans second,
    fun _ _ _ first second => first.trans second.symm, FOCorr.refl isFirstOrder,
    fun _ _ same => same ▸ rfl, fun n _ => ⟨n, rfl⟩, fun m _ => ⟨m, rfl⟩⟩

/-- Matching is symmetric. -/
theorem FOMatch.symm {first second : Tm S (Slot X) × GStore S (Slot X)}
    (isMatch : FOMatch first second) : FOMatch second first := by
  obtain ⟨related, functional, injective, corresponds, stores, leftTotal, rightTotal⟩ := isMatch
  exact ⟨fun m n => related n m, fun m n n' one other => injective n n' m one other,
    fun m m' n one other => functional n m m' one other, FOCorr.flip corresponds,
    fun m n one => (stores n m one).symm, rightTotal, leftTotal⟩

/-- Matching is transitive. -/
theorem FOMatch.trans {first second third : Tm S (Slot X) × GStore S (Slot X)}
    (firstMatch : FOMatch first second) (secondMatch : FOMatch second third) :
    FOMatch first third := by
  obtain ⟨related, functional, injective, corresponds, stores, leftTotal, rightTotal⟩ := firstMatch
  obtain ⟨related', functional', injective', corresponds', stores', leftTotal', rightTotal'⟩ :=
    secondMatch
  refine ⟨fun n k => ∃ m, related n m ∧ related' m k, ?_, ?_, FOCorr.comp corresponds corresponds',
    ?_, ?_, ?_⟩
  · rintro n k k' ⟨m, one, other⟩ ⟨m', one', other'⟩
    have same := functional n m m' one one'
    subst same
    exact functional' m k k' other other'
  · rintro n n' k ⟨m, one, other⟩ ⟨m', one', other'⟩
    have same := injective' m m' k other other'
    subst same
    exact injective n n' m one one'
  · rintro n k ⟨m, one, other⟩
    exact (stores n m one).trans (stores' m k other)
  · intro n bound
    obtain ⟨m, one⟩ := leftTotal n bound
    have boundMiddle : second.2 m ≠ none := by
      rw [← stores n m one]
      exact bound
    obtain ⟨k, other⟩ := leftTotal' m boundMiddle
    exact ⟨k, m, one, other⟩
  · intro k bound
    obtain ⟨m, other⟩ := rightTotal' k bound
    have boundMiddle : second.2 m ≠ none := by
      rw [stores' m k other]
      exact bound
    obtain ⟨n, one⟩ := rightTotal m boundMiddle
    exact ⟨n, m, one, other⟩

/-- A match has first-order answers on both sides. -/
theorem FOMatch.firstOrder {first second : Tm S (Slot X) × GStore S (Slot X)}
    (isMatch : FOMatch first second) :
    first.1.FirstOrder = true ∧ second.1.FirstOrder = true := by
  obtain ⟨_, -, -, corresponds, -, -, -⟩ := isMatch
  exact FOCorr.firstOrder corresponds

/-- **What the static equivalence keeps of one result**: the two answers are
first-order together, and then the results match up to a one-to-one
correspondence of names. -/
def FOEquiv (first second : Tm S (Slot X) × GStore S (Slot X)) : Prop :=
  (first.1.FirstOrder = true ↔ second.1.FirstOrder = true) ∧
    (first.1.FirstOrder = true → FOMatch first second)

theorem FOEquiv.refl (result : Tm S (Slot X) × GStore S (Slot X)) : FOEquiv result result :=
  ⟨Iff.rfl, FOMatch.refl⟩

theorem FOEquiv.symm {first second : Tm S (Slot X) × GStore S (Slot X)}
    (equivalent : FOEquiv first second) : FOEquiv second first :=
  ⟨equivalent.1.symm, fun isFirstOrder =>
    FOMatch.symm (equivalent.2 (equivalent.1.mpr isFirstOrder))⟩

theorem FOEquiv.trans {first second third : Tm S (Slot X) × GStore S (Slot X)}
    (firstSecond : FOEquiv first second) (secondThird : FOEquiv second third) :
    FOEquiv first third :=
  ⟨firstSecond.1.trans secondThird.1, fun isFirstOrder =>
    FOMatch.trans (firstSecond.2 isFirstOrder)
      (secondThird.2 (firstSecond.1.mp isFirstOrder))⟩

theorem forall₂_foEquiv_refl : ∀ bag : Result S (Slot X), List.Forall₂ FOEquiv bag bag
  | [] => .nil
  | result :: rest => .cons (FOEquiv.refl result) (forall₂_foEquiv_refl rest)

theorem forall₂_foEquiv_symm : ∀ {bag bag' : Result S (Slot X)},
    List.Forall₂ FOEquiv bag bag' → List.Forall₂ FOEquiv bag' bag
  | _, _, .nil => .nil
  | _, _, .cons head tail => .cons head.symm (forall₂_foEquiv_symm tail)

theorem forall₂_foEquiv_trans : ∀ {first second third : Result S (Slot X)},
    List.Forall₂ FOEquiv first second → List.Forall₂ FOEquiv second third →
      List.Forall₂ FOEquiv first third
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons head tail, .cons head' tail' =>
      .cons (head.trans head') (forall₂_foEquiv_trans tail tail')

/-- What two terms of the core share when they are statically equivalent:
nothing is said of two judgments; two observations are equivalent result by
result. -/
def Observes : Core S X → Core S X → Prop
  | .done bag, .done bag' => List.Forall₂ FOEquiv bag bag'
  | .run _ _ _, .run _ _ _ => True
  | _, _ => False

theorem Observes.refl : ∀ term : Core S X, Observes term term
  | .run _ _ _ => trivial
  | .done bag => forall₂_foEquiv_refl bag

theorem Observes.symm : ∀ {first second : Core S X}, Observes first second → Observes second first
  | .run _ _ _, .run _ _ _, _ => trivial
  | .done _, .done _, observed => forall₂_foEquiv_symm observed
  | .run _ _ _, .done _, impossible => impossible.elim
  | .done _, .run _ _ _, impossible => impossible.elim

theorem Observes.trans : ∀ {first second third : Core S X},
    Observes first second → Observes second third → Observes first third
  | .run _ _ _, .run _ _ _, .run _ _ _, _, _ => trivial
  | .done _, .done _, .done _, one, other => forall₂_foEquiv_trans one other
  | .run _ _ _, .done _, _, impossible, _ => impossible.elim
  | .done _, .run _ _ _, _, impossible, _ => impossible.elim
  | .run _ _ _, .run _ _ _, .done _, _, impossible => impossible.elim
  | .done _, .done _, .run _ _ _, _, impossible => impossible.elim

variable [DecidableEq X]

/-- Two results renamed into one result of the identity model are equivalent
in this sense. -/
theorem FOEquiv.of_renamed {first second : Tm S (Slot X) × GStore S (Slot X)}
    {common : Tm S (BId X) × GStore S (BId X)} (firstRenamed : Renamed first common)
    (secondRenamed : Renamed second common) : FOEquiv first second := by
  have forward : first.1.FirstOrder = true → FOMatch first second :=
    fomatch_of_renamed firstRenamed secondRenamed
  have backward : second.1.FirstOrder = true → FOMatch second first :=
    fomatch_of_renamed secondRenamed firstRenamed
  exact ⟨⟨fun isFirstOrder => (FOMatch.firstOrder (forward isFirstOrder)).2,
    fun isFirstOrder => (FOMatch.firstOrder (backward isFirstOrder)).2⟩, forward⟩

/-! ## Along a chain of bags -/

/-- Two bags renamed into one bag of the identity model are equivalent result
by result. -/
theorem forall₂_foEquiv_of_renamed : ∀ {bag bag' : Result S (Slot X)}
    {common : Result S (BId X)}, List.Forall₂ Renamed bag common →
      List.Forall₂ Renamed bag' common → List.Forall₂ FOEquiv bag bag'
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons head tail, .cons head' tail' =>
      .cons (FOEquiv.of_renamed head head') (forall₂_foEquiv_of_renamed tail tail')

theorem CoreLink.observes {first second : Core S X} (link : CoreLink first second) :
    Observes first second := by
  cases link with
  | run _ _ => trivial
  | done renamed renamed' => exact forall₂_foEquiv_of_renamed renamed renamed'

/-- Statically equivalent terms of the core share their observations. -/
theorem CoreEquiv.observes {first second : Core S X} (equivalent : CoreEquiv first second) :
    Observes first second := by
  induction equivalent with
  | rel first second link => exact link.observes
  | refl first => exact Observes.refl first
  | symm first second _ ih => exact ih.symm
  | trans first middle second _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **What the static equivalence keeps of an observation.**  Result by
result, in order: the answers are first-order together, and then the two
results have the same answer, the same store and the same sharing of cells,
up to a one-to-one correspondence of names. -/
theorem coreEquiv_done_firstOrder {bag bag' : Result S (Slot X)}
    (equivalent : CoreEquiv (.done bag : Core S X) (.done bag')) :
    List.Forall₂ FOEquiv bag bag' :=
  equivalent.observes

/-- Positive: two equal bags. -/
theorem foEquiv_same (bag : Result S (Slot X)) : List.Forall₂ FOEquiv bag bag :=
  coreEquiv_done_firstOrder (.refl _)

/-- **Negative: two answers with different symbols are apart.** -/
theorem done_apart_of_symbols {s s' : S} (differ : s ≠ s') (σ σ' : GStore S (Slot X)) :
    ¬ CoreEquiv (.done [(.sym s, σ)] : Core S X) (.done [(.sym s', σ')]) := by
  intro equivalent
  have observed := coreEquiv_done_firstOrder equivalent
  cases observed with
  | cons head _ =>
      obtain ⟨_, -, -, corresponds, -, -, -⟩ := head.2 rfl
      exact differ corresponds

/-- Negative: a symbol and an unbound name are apart. -/
theorem done_apart_symbol_name (s : S) (n : Nm (Slot X)) (σ σ' : GStore S (Slot X)) :
    ¬ CoreEquiv (.done [(.sym s, σ)] : Core S X) (.done [(.var n, σ')]) := by
  intro equivalent
  have observed := coreEquiv_done_firstOrder equivalent
  cases observed with
  | cons head _ =>
      obtain ⟨_, -, -, corresponds, -, -, -⟩ := head.2 rfl
      exact corresponds

#print axioms FOMatch.trans
#print axioms coreEquiv_done_firstOrder
#print axioms done_apart_of_symbols

end Mettapedia.GSLT.LanguageDef.ScopePolicies
