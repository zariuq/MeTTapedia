import Mettapedia.Languages.OpenTheory.DerivedRulesEta
import Mettapedia.Languages.OpenTheory.ReverseTranslation

/-!
# Eta-expanding bare equality in the OpenTheory kernel

The forward translation sends an occurrence of primitive equality that is not
the head of a full application to `λ x y. x = y`, so the reverse translation
returns a translated term with those occurrences eta-expanded
(`ReverseTranslation.expandBareEquality`).  With the eta axiom the kernel
proves the expansion equal to the original:

* `KernelProvable.equalityConst_eq_equalityLambdaDB`: `⊢ (=) = (λ x y. x = y)`,
  by ETA at `(=) x` under ABS, ETA at `(=)`, and symmetry;
* `KernelProvable.eq_expandBareEquality`: `⊢ t = expandBareEquality t` for
  every closed well-typed term `t`, by congruence, with each binder opened at
  a fresh variable and closed again by ABS.

`KernelProvable.of_forall_mem_provable` discharges a whole hypothesis set at
once: if every hypothesis of `A ⊢ c` is provable from a Boolean set `B`, then
`B ⊢ c`.

Syntactic support: `DBTerm.nodeCount` measures terms so that instantiating a
bound index by a free variable preserves the measure;
`expandBareEquality_instantiateAt_free` and
`closeFreeAt_instantiateAt_free` commute expansion with opening a binder and
close it again.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.OpenTheory

open Mettapedia.Logic
open CanonicalTerm (equalityDB)
open DBTerm (instantiateAt closeFreeAt FreeOccurrence inferType_app_of)
open ReverseTranslation (expandBareEquality equalityLambdaDB)

namespace DBTerm

/-- The number of constructor nodes of a term. -/
def nodeCount : DBTerm → Nat
  | .const _ _ => 1
  | .free _ => 1
  | .bound _ => 1
  | .app function argument => nodeCount function + nodeCount argument + 1
  | .abs _ body => nodeCount body + 1

theorem nodeCount_pos (term : DBTerm) : 0 < nodeCount term := by
  cases term <;> simp [nodeCount]

/-- Instantiating a bound index by a free variable keeps the node count. -/
theorem nodeCount_instantiateAt_free (sourceVar : SourceVar) :
    ∀ (depth : Nat) (term : DBTerm),
      nodeCount (instantiateAt (.free sourceVar) depth term) = nodeCount term
  | _, .const _ _ => by simp [instantiateAt, nodeCount]
  | _, .free _ => by simp [instantiateAt, nodeCount]
  | depth, .bound index => by
      by_cases h : index = depth <;> simp [instantiateAt, nodeCount, h]
  | depth, .app function argument => by
      simp only [instantiateAt, nodeCount]
      rw [nodeCount_instantiateAt_free sourceVar depth function,
        nodeCount_instantiateAt_free sourceVar depth argument]
  | depth, .abs _ body => by
      simp only [instantiateAt, nodeCount]
      rw [nodeCount_instantiateAt_free sourceVar (depth + 1) body]

/-- Closing an absent free variable after opening a binder by it restores the
term. -/
theorem closeFreeAt_instantiateAt_free {sourceVar : SourceVar} :
    ∀ {depth : Nat} {term : DBTerm}, ¬ FreeOccurrence sourceVar term →
      closeFreeAt sourceVar depth (instantiateAt (.free sourceVar) depth term) = term
  | _, .const _ _, _ => by simp [instantiateAt, closeFreeAt]
  | _, .free other, absent => by
      have different : sourceVar ≠ other := by
        rintro rfl
        exact absent .here
      simp only [instantiateAt]
      exact closeFreeAt_other sourceVar other _ different
  | depth, .bound index, _ => by
      by_cases h : index = depth
      · subst h
        simp
      · simp [instantiateAt, closeFreeAt, h]
  | depth, .app function argument, absent => by
      simp only [instantiateAt, closeFreeAt]
      rw [closeFreeAt_instantiateAt_free (fun h => absent (.appFunction h)),
        closeFreeAt_instantiateAt_free (fun h => absent (.appArgument h))]
  | depth, .abs _ body, absent => by
      simp only [instantiateAt, closeFreeAt]
      rw [closeFreeAt_instantiateAt_free (term := body) (fun h => absent (.absBody h))]

end DBTerm

namespace ReverseTranslation

theorem looseBelow_zero_equalityLambdaDB (operand : Ty) :
    DBTerm.LooseBelow 0 (equalityLambdaDB operand) := by
  simp [equalityLambdaDB, CanonicalTerm.equalityDB, DBTerm.LooseBelow]

theorem instantiateAt_equalityLambdaDB (replacement : DBTerm) (depth : Nat) (operand : Ty) :
    instantiateAt replacement depth (equalityLambdaDB operand) = equalityLambdaDB operand :=
  DBTerm.instantiateAt_of_looseBelow replacement
    (DBTerm.LooseBelow.mono (looseBelow_zero_equalityLambdaDB operand) (Nat.zero_le depth))

/-- Opening a binder by a free variable neither creates nor destroys a full
application of a constant. -/
theorem instantiateAt_free_ne_const_app {sourceVar : SourceVar} {depth : Nat}
    {function : DBTerm}
    (shape : ∀ (constant : Const) (annotation : Ty) (left : DBTerm),
      function = .app (.const constant annotation) left → False)
    (constant : Const) (annotation : Ty) (left : DBTerm) :
    instantiateAt (.free sourceVar) depth function = .app (.const constant annotation) left →
      False := by
  intro h
  match function, shape, h with
  | .const _ _, _, h => simp [instantiateAt] at h
  | .free _, _, h => simp [instantiateAt] at h
  | .bound index, _, h =>
      by_cases hindex : index = depth <;> simp [instantiateAt, hindex] at h
  | .app (.const constant' annotation') left', shape, _ =>
      exact shape constant' annotation' left' rfl
  | .app (.free _) _, _, h => simp [instantiateAt] at h
  | .app (.bound index) _, _, h =>
      by_cases hindex : index = depth <;> simp [instantiateAt, hindex] at h
  | .app (.app _ _) _, _, h => simp [instantiateAt] at h
  | .app (.abs _ _) _, _, h => simp [instantiateAt] at h
  | .abs _ _, _, h => simp [instantiateAt] at h

/-- Expansion of bare equality commutes with opening a binder by a free
variable. -/
theorem expandBareEquality_instantiateAt_free (sourceVar : SourceVar) (term : DBTerm) :
    ∀ depth : Nat,
      expandBareEquality (instantiateAt (.free sourceVar) depth term) =
        instantiateAt (.free sourceVar) depth (expandBareEquality term) := by
  induction term using expandBareEquality.induct with
  | case1 constant annotation operand recognized =>
      intro depth
      simp only [instantiateAt, expandBareEquality, recognized]
      exact (instantiateAt_equalityLambdaDB _ depth operand).symm
  | case2 constant annotation unrecognized =>
      intro depth
      simp [instantiateAt, expandBareEquality, unrecognized]
  | case3 other =>
      intro depth
      simp [instantiateAt, expandBareEquality]
  | case4 index =>
      intro depth
      by_cases h : index = depth <;> simp [instantiateAt, expandBareEquality, h]
  | case5 constant annotation left right leftIH rightIH =>
      intro depth
      simp only [instantiateAt]
      rw [expandBareEquality.eq_4, expandBareEquality.eq_4, leftIH, rightIH]
      simp [instantiateAt]
  | case6 function argument shape functionIH argumentIH =>
      intro depth
      simp only [instantiateAt]
      rw [expandBareEquality.eq_5 _ _ (instantiateAt_free_ne_const_app shape),
        expandBareEquality.eq_5 _ _ shape, functionIH, argumentIH]
      simp [instantiateAt]
  | case7 domain body bodyIH =>
      intro depth
      simp only [instantiateAt]
      rw [expandBareEquality.eq_6, expandBareEquality.eq_6, bodyIH]
      simp [instantiateAt]

end ReverseTranslation

namespace KernelProvable

open ReverseTranslation

variable {policy : AxiomPolicy}

/-- `⊢ (λ x y. x = y) = (=)` at every operand type, from the eta axiom. -/
theorem equalityLambdaDB_eq_equalityConst (admitted : policy EtaAxiom.sequent) (operand : Ty) :
    KernelProvable policy ∅
      (equalityDB (.function operand (.function operand Ty.bool)) (equalityLambdaDB operand)
        (.const Const.equality (Ty.equality operand))) := by
  let bound : SourceVar := ⟨Name.global "x", operand⟩
  have hconst := DBTerm.inferType_equality_const [] operand
  have hpartial : (DBTerm.app (.const Const.equality (Ty.equality operand)) (.free bound)).inferType
      [] = some (.function operand Ty.bool) :=
    inferType_app_of hconst (by simp [bound])
  have hinner := abs bound (eta admitted hpartial)
    (fun ⟨_, member, _⟩ => absurd member (Finset.notMem_empty _))
  simp only [closeFreeAt, DBTerm.closeFreeAt_exact] at hinner
  have houter := eta admitted hconst
  exact (trans hinner houter).congr_hyp (Finset.union_empty ∅)

/-- `⊢ (=) = (λ x y. x = y)` at every operand type, from the eta axiom. -/
theorem equalityConst_eq_equalityLambdaDB (admitted : policy EtaAxiom.sequent) (operand : Ty) :
    KernelProvable policy ∅
      (equalityDB (.function operand (.function operand Ty.bool))
        (.const Const.equality (Ty.equality operand)) (equalityLambdaDB operand)) :=
  sym (equalityLambdaDB_eq_equalityConst admitted operand)

private theorem eq_expandBareEquality_of_nodeCount_le (admitted : policy EtaAxiom.sequent) :
    ∀ (count : Nat) (term : DBTerm), DBTerm.nodeCount term ≤ count →
      ∀ {ty : Ty}, term.inferType [] = some ty →
        KernelProvable policy ∅ (equalityDB ty term (expandBareEquality term))
  | 0, term, bounded, _, _ => absurd bounded (Nat.not_le.mpr (DBTerm.nodeCount_pos term))
  | _ + 1, .const constant annotation, _, ty, typed => by
      cases recognized : equalityOperand? constant annotation with
      | none =>
          rw [expandBareEquality_const_of_equalityOperand?_eq_none recognized]
          exact refl typed
      | some operand =>
          obtain ⟨rfl, rfl⟩ := (equalityOperand?_eq_some_iff _ _ _).mp recognized
          rw [expandBareEquality.eq_1, recognized]
          obtain rfl := DBTerm.inferType_unique typed (DBTerm.inferType_equality_const [] operand)
          exact equalityConst_eq_equalityLambdaDB admitted operand
  | _ + 1, .free _, _, _, typed => by
      rw [expandBareEquality.eq_2]
      exact refl typed
  | _ + 1, .bound _, _, _, typed => by
      simp at typed
  | count + 1, .app function argument, bounded, ty, typed => by
      obtain ⟨domain, hfunction, hargument⟩ := DBTerm.inferType_app_eq_some_iff.mp typed
      simp only [DBTerm.nodeCount] at bounded
      have hargumentEq := eq_expandBareEquality_of_nodeCount_le admitted count argument
        (by omega) hargument
      by_cases shape : ∃ (constant : Const) (annotation : Ty) (left : DBTerm),
          function = .app (.const constant annotation) left
      · obtain ⟨constant, annotation, left, rfl⟩ := shape
        obtain ⟨leftTy, hconst, hleft⟩ := DBTerm.inferType_app_eq_some_iff.mp hfunction
        simp only [DBTerm.nodeCount] at bounded
        have hleftEq := eq_expandBareEquality_of_nodeCount_le admitted count left
          (by omega) hleft
        rw [expandBareEquality.eq_4]
        exact (mkComb (apTerm hconst hleftEq) hargumentEq).congr_hyp (Finset.union_empty ∅)
      · have shape' : ∀ (constant : Const) (annotation : Ty) (left : DBTerm),
            function = .app (.const constant annotation) left → False :=
          fun constant annotation left h => shape ⟨constant, annotation, left, h⟩
        have hfunctionEq := eq_expandBareEquality_of_nodeCount_le admitted count function
          (by omega) hfunction
        rw [expandBareEquality.eq_5 _ _ shape']
        exact (mkComb hfunctionEq hargumentEq).congr_hyp (Finset.union_empty ∅)
  | count + 1, .abs domain body, bounded, ty, typed => by
      obtain ⟨codomain, hbody, hty⟩ := DBTerm.inferType_abs_eq_some_iff.mp typed
      subst hty
      simp only [DBTerm.nodeCount] at bounded
      obtain ⟨sourceVar, hsourceVar, -, absent⟩ :=
        exists_fresh_var domain ∅ [body, expandBareEquality body]
      have hopened : (instantiateAt (.free sourceVar) 0 body).inferType [] = some codomain :=
        DBTerm.inferType_instantiateAt (.free sourceVar) body domain (by simp [hsourceVar]) []
          (by simpa using hbody)
      have hopenedEq := eq_expandBareEquality_of_nodeCount_le admitted count
        (instantiateAt (.free sourceVar) 0 body)
        (by rw [DBTerm.nodeCount_instantiateAt_free]; omega) hopened
      rw [expandBareEquality_instantiateAt_free] at hopenedEq
      have habs := abs sourceVar hopenedEq
        (fun ⟨_, member, _⟩ => absurd member (Finset.notMem_empty _))
      rw [DBTerm.closeFreeAt_instantiateAt_free (absent body (by simp)),
        DBTerm.closeFreeAt_instantiateAt_free (absent (expandBareEquality body) (by simp)),
        hsourceVar] at habs
      rw [expandBareEquality.eq_6]
      exact habs

/-- **Bare equality expansion is provable.**  Under every axiom policy
admitting the eta sequent, `⊢ t = expandBareEquality t` for every closed
well-typed term `t`. -/
theorem eq_expandBareEquality (admitted : policy EtaAxiom.sequent) {term : DBTerm} {ty : Ty}
    (typed : term.inferType [] = some ty) :
    KernelProvable policy ∅ (equalityDB ty term (expandBareEquality term)) :=
  eq_expandBareEquality_of_nodeCount_le admitted _ term le_rfl typed

/-- **Discharging a hypothesis set.**  If every hypothesis of `A ⊢ c` is
provable from a Boolean set `B`, then `B ⊢ c`. -/
theorem of_forall_mem_provable {hyp hyp' : Finset CanonicalTerm} {concl : DBTerm}
    (h : KernelProvable policy hyp concl) (hbool : ∀ term ∈ hyp', term.IsBool)
    (provable : ∀ term ∈ hyp, KernelProvable policy hyp' term.term) :
    KernelProvable policy hyp' concl := by
  classical
  have hypBool := h.hyp_isBool
  suffices remove : ∀ remaining : Finset CanonicalTerm, remaining ⊆ hyp →
      KernelProvable policy (remaining ∪ hyp') concl → KernelProvable policy hyp' concl by
    refine remove hyp subset_rfl (weaken h Finset.subset_union_left fun term member => ?_)
    rcases Finset.mem_union.mp member with member | member
    · exact hypBool term member
    · exact hbool term member
  intro remaining
  induction remaining using Finset.induction_on with
  | empty => exact fun _ h => h.congr_hyp (Finset.empty_union hyp')
  | insert first rest _ ih =>
      intro subset hprovable
      refine ih (fun term member => subset (Finset.mem_insert_of_mem member)) ?_
      refine weaken (proveHyp first (provable first (subset (Finset.mem_insert_self _ _)))
        hprovable) ?_ fun term member => ?_
      · intro term member
        simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at member ⊢
        tauto
      · rcases Finset.mem_union.mp member with member | member
        · exact hypBool term (subset (Finset.mem_insert_of_mem member))
        · exact hbool term member

end KernelProvable

end Mettapedia.Languages.OpenTheory
