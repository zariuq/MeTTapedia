import Mettapedia.Algebra.Collections.TermBagUnifiers
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sets

/-!
# Deciding generality between families of term-bag answers

`general` is more general than `specific` when some substitution sends the
element terms of `general` to those of `specific` and sends the base of each
rest slot into the corresponding base of `specific`, the two remainders being
one common bag (`checks_iff`).

On a finite set of variables the relation is decidable by a finite search
(`check_iff`): every substitution that witnesses it can be clipped to one whose
values are subterms of the terms of `specific`, or variables, without changing
any term it acts on (`clipped_checks`). A substitution's value at a variable
of a term is a subterm of the term's image (`image_mem_subterms`), so the
values that matter already occur in `specific`. The search ranges over the
finitely many such substitutions; constants and function symbols need only
decidable equality.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.Collections.TermBagSubsumption

open Mettapedia.Logic.LP (LPSignature Term Subst)
open TermBagUnifiers (Answer Family instantiate genericAnswer MoreGeneral)
open FlatBagUnifiers (RestSlot)

variable {σ : LPSignature} [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]

/-! ## Subterms -/

omit [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
/-- Substitutions that agree on the variables of a term agree on the term. -/
theorem applyTerm_congr {first second : Subst σ} :
    ∀ t : Term σ, (∀ v ∈ t.freeVars, first v = second v) → first.applyTerm t = second.applyTerm t
  | .var v, agree => agree v (by simp [Term.freeVars])
  | .const _, _ => rfl
  | .app f ts, agree => by
      simp only [Subst.applyTerm_app]
      congr 1
      funext i
      exact applyTerm_congr (ts i) fun v member => agree v (by
        simp only [Term.freeVars, Finset.mem_biUnion, Finset.mem_univ, true_and]
        exact ⟨i, member⟩)

/-- The subterms of a term, itself included. -/
def subterms : Term σ → Finset (Term σ)
  | .var v => {.var v}
  | .const c => {.const c}
  | .app f ts => insert (.app f ts) (Finset.univ.biUnion fun i => subterms (ts i))

theorem mem_subterms_self : ∀ t : Term σ, t ∈ subterms t
  | .var _ => by simp [subterms]
  | .const _ => by simp [subterms]
  | .app _ _ => by simp [subterms]

theorem subterms_mono : ∀ (t s : Term σ), s ∈ subterms t → subterms s ⊆ subterms t
  | .var v, s, member => by
      simp only [subterms, Finset.mem_singleton] at member
      subst member
      exact Finset.Subset.refl _
  | .const c, s, member => by
      simp only [subterms, Finset.mem_singleton] at member
      subst member
      exact Finset.Subset.refl _
  | .app f ts, s, member => by
      simp only [subterms, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ, true_and] at member
      rcases member with rfl | ⟨i, inside⟩
      · exact Finset.Subset.refl _
      · intro r within
        have deeper := subterms_mono (ts i) s inside within
        simp only [subterms, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ, true_and]
        exact Or.inr ⟨i, deeper⟩

/-- **A substitution's value at a variable of a term is a subterm of the
term's image.** -/
theorem image_mem_subterms (assignment : Subst σ) :
    ∀ (t : Term σ) (v : σ.vars), v ∈ t.freeVars → assignment v ∈ subterms (assignment.applyTerm t)
  | .var w, v, member => by
      simp only [Term.freeVars, Finset.mem_singleton] at member
      subst member
      exact mem_subterms_self _
  | .const _, v, member => by simp [Term.freeVars] at member
  | .app f ts, v, member => by
      simp only [Term.freeVars, Finset.mem_biUnion, Finset.mem_univ, true_and] at member
      obtain ⟨i, inside⟩ := member
      have deeper := image_mem_subterms assignment (ts i) v inside
      simp only [Subst.applyTerm_app, subterms, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ,
        true_and]
      exact Or.inr ⟨i, deeper⟩

/-! ## The algebraic condition -/

def mapped (family : Family σ) (assignment : Subst σ) (slot : RestSlot) : Multiset (Term σ) :=
  (family.base slot).map assignment.applyTerm

/-- The element terms factor and the rest bases embed with one common
remainder. -/
def Checks (general specific : Family σ) (assignment : Subst σ) : Prop :=
  (∀ name, specific.elements name = assignment.applyTerm (general.elements name)) ∧
    mapped general assignment .left ≤ specific.base .left ∧
    mapped general assignment .right ≤ specific.base .right ∧
    specific.base .left - mapped general assignment .left =
      specific.base .right - mapped general assignment .right

theorem checks_iff (general specific : Family σ) (assignment : Subst σ) :
    Checks general specific assignment ↔ ∃ common, genericAnswer specific = instantiate general assignment common := by
  constructor
  · rintro ⟨elements, left, right, equalRemainders⟩
    refine ⟨specific.base .left - mapped general assignment .left, ?_⟩
    apply Answer.ext
    · exact funext elements
    · funext slot
      cases slot with
      | left => exact (add_tsub_cancel_of_le left).symm
      | right =>
          change specific.base .right = mapped general assignment .right +
            (specific.base .left - mapped general assignment .left)
          rw [equalRemainders]
          exact (add_tsub_cancel_of_le right).symm
  · rintro ⟨common, represented⟩
    have elements := congrArg Answer.elements represented
    have rests := congrArg Answer.rest represented
    have restEq (slot : RestSlot) : specific.base slot = mapped general assignment slot + common :=
      congrFun rests slot
    refine ⟨fun name => congrFun elements name, ?_, ?_, ?_⟩
    · rw [restEq]
      exact Multiset.le_add_right _ _
    · rw [restEq]
      exact Multiset.le_add_right _ _
    · rw [restEq .left, restEq .right, add_tsub_cancel_left, add_tsub_cancel_left]

/-! ## Clipping a witness -/

variable [Fintype σ.vars]

/-- The terms of a family: its element terms and its rest bases. -/
def roots (specific : Family σ) : Finset (Term σ) :=
  Finset.univ.image specific.elements ∪ (specific.base .left).toFinset ∪ (specific.base .right).toFinset

/-- The candidate values of a witness: subterms of the family's terms, and
variables. -/
def target (specific : Family σ) : Finset (Term σ) :=
  (roots specific).biUnion subterms ∪ Finset.univ.image Term.var

theorem mem_target_of_root {specific : Family σ} {root t : Term σ} (isRoot : root ∈ roots specific)
    (inside : t ∈ subterms root) : t ∈ target specific :=
  Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨root, isRoot, inside⟩)

theorem variable_mem_target (specific : Family σ) (v : σ.vars) : Term.var v ∈ target specific :=
  Finset.mem_union_right _ (Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩)

/-- A witness with every value outside the target replaced by its variable. -/
def clip (specific : Family σ) (assignment : Subst σ) : σ.vars → ↑(target specific) :=
  fun v => if member : assignment v ∈ target specific then ⟨assignment v, member⟩
    else ⟨.var v, variable_mem_target specific v⟩

/-- The substitution named by a choice of target values. -/
def realize (specific : Family σ) (encoded : σ.vars → ↑(target specific)) : Subst σ := fun v => (encoded v).val

def clipped (specific : Family σ) (assignment : Subst σ) : Subst σ := realize specific (clip specific assignment)

/-- Clipping changes no term whose image is a term of the family. -/
theorem clipped_applyTerm {specific : Family σ} {assignment : Subst σ} {root : Term σ}
    (isRoot : root ∈ roots specific) (t : Term σ) (image : assignment.applyTerm t = root) :
    (clipped specific assignment).applyTerm t = assignment.applyTerm t := by
  apply applyTerm_congr t
  intro v member
  have inside : assignment v ∈ subterms root := image ▸ image_mem_subterms assignment t v member
  have kept := mem_target_of_root isRoot inside
  simp [clipped, realize, clip, kept]

theorem element_root (specific : Family σ) (name : σ.vars) : specific.elements name ∈ roots specific :=
  Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ name)))

theorem base_root (specific : Family σ) (slot : RestSlot) {t : Term σ} (member : t ∈ specific.base slot) :
    t ∈ roots specific := by
  cases slot <;> simp [roots, member]

/-- **A clipped witness still witnesses generality.** -/
theorem clipped_checks (general specific : Family σ) (assignment : Subst σ) (common : Multiset (Term σ))
    (represented : genericAnswer specific = instantiate general assignment common) :
    Checks general specific (clipped specific assignment) := by
  have checked := (checks_iff general specific assignment).mpr ⟨common, represented⟩
  have restEq (slot : RestSlot) : specific.base slot = mapped general assignment slot + common :=
    congrFun (congrArg Answer.rest represented) slot
  have elements (name : σ.vars) :
      (clipped specific assignment).applyTerm (general.elements name) =
        assignment.applyTerm (general.elements name) :=
    clipped_applyTerm (element_root specific name) _ (checked.1 name).symm
  have prefixes (slot : RestSlot) : mapped general (clipped specific assignment) slot = mapped general assignment slot := by
    apply Multiset.map_congr rfl
    intro t member
    apply clipped_applyTerm (base_root specific slot (t := assignment.applyTerm t) ?_) t rfl
    rw [restEq]
    exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_map_of_mem _ member))
  refine ⟨fun name => (checked.1 name).trans (elements name).symm, ?_, ?_, ?_⟩
  · rw [prefixes]; exact checked.2.1
  · rw [prefixes]; exact checked.2.2.1
  · rw [prefixes, prefixes]; exact checked.2.2.2

instance decidableChecks (general specific : Family σ) (assignment : Subst σ) :
    Decidable (Checks general specific assignment) :=
  haveI : Decidable (∀ name, specific.elements name = assignment.applyTerm (general.elements name)) :=
    @Fintype.decidableForallFintype σ.vars _ (fun _ => decEq _ _) _
  instDecidableAnd

/-- Every substitution into the target that passes the algebraic condition. -/
def candidates (general specific : Family σ) : Finset (σ.vars → ↑(target specific)) :=
  Finset.univ.filter fun encoded => Checks general specific (realize specific encoded)

def check (general specific : Family σ) : Bool := decide (candidates general specific).Nonempty

theorem check_sound (general specific : Family σ) (accepted : check general specific = true) :
    MoreGeneral general specific := by
  obtain ⟨encoded, member⟩ : (candidates general specific).Nonempty := of_decide_eq_true accepted
  obtain ⟨common, represented⟩ := (checks_iff general specific _).mp (Finset.mem_filter.mp member).2
  exact ⟨realize specific encoded, common, represented⟩

theorem check_complete (general specific : Family σ) (covers : MoreGeneral general specific) :
    check general specific = true := by
  obtain ⟨assignment, common, represented⟩ := covers
  apply decide_eq_true_eq.mpr
  exact ⟨clip specific assignment, Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, clipped_checks general specific assignment common represented⟩⟩

/-- **The checker decides generality.** -/
theorem check_iff (general specific : Family σ) : check general specific = true ↔ MoreGeneral general specific :=
  ⟨check_sound general specific, check_complete general specific⟩

instance decidableMoreGeneral : DecidableRel (MoreGeneral : Family σ → Family σ → Prop) :=
  fun general specific => decidable_of_iff (check general specific = true) (check_iff general specific)

end Mettapedia.Algebra.Collections.TermBagSubsumption
