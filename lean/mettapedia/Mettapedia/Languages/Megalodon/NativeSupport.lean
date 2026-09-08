import Mettapedia.Languages.Megalodon.MathdataKernel
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Insert

/-!
# Finite support of native Megalodon terms and proofs

Support records the environment entries mentioned by existing native syntax.
It does not expand declarations or identify names by their denotations. Term
and type substitution, and successful beta/eta normalization, introduce no
dependencies beyond their input support. Dependency closure through definitions
and known propositions is a separate environment-level obligation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.NativeSupport

open MathdataKernel

/-- Three independently looked-up forms of native environmental dependency. -/
inductive Dependency where
  | termName (name : Name)
  | primitive (index : Nat)
  | knownName (name : Name)
deriving DecidableEq, Repr

abbrev Support := Finset Dependency

/-- Direct environmental dependencies of a term, including prefix syntax. -/
def termSupport : Tm → Support
  | .db _ => ∅
  | .named name => {.termName name}
  | .prim index => {.primitive index}
  | .app function argument | .imp function argument =>
      termSupport function ∪ termSupport argument
  | .lam _ body | .all _ body | .typeApp body _ | .typeLam body | .typeAll body =>
      termSupport body

/-- Direct environmental dependencies of a proof. The rejected `gpa` syntax
conservatively retains its name; no acceptance claim follows from membership. -/
def proofSupport : Pf → Support
  | .hyp _ => ∅
  | .gpa name | .known name => {.knownName name}
  | .termApp proof argument => proofSupport proof ∪ termSupport argument
  | .proofApp function argument => proofSupport function ∪ proofSupport argument
  | .proofLam proposition body => termSupport proposition ∪ proofSupport body
  | .termLam _ body | .typeApp body _ | .typeLam body => proofSupport body

@[simp] theorem termSupport_shift (cutoff amount : Nat) (term : Tm) :
    termSupport (Tm.shift cutoff amount term) = termSupport term := by
  induction term generalizing cutoff <;> simp_all [Tm.shift, termSupport]
  split <;> rfl

@[simp] theorem termSupport_typeShift (cutoff amount : Nat) (term : Tm) :
    termSupport (Tm.typeShift cutoff amount term) = termSupport term := by
  induction term generalizing cutoff <;> simp_all [Tm.typeShift, termSupport]

@[simp] theorem termSupport_typeInstantiateAt (depth : Nat) (replacement : Tp) (term : Tm) :
    termSupport (Tm.typeInstantiateAt depth replacement term) = termSupport term := by
  induction term generalizing depth <;> simp_all [Tm.typeInstantiateAt, termSupport]

@[simp] theorem termSupport_typeInstantiate (replacement : Tp) (term : Tm) :
    termSupport (Tm.typeInstantiate replacement term) = termSupport term :=
  termSupport_typeInstantiateAt 0 replacement term

/-- Capture-avoiding term instantiation uses only body and replacement dependencies. -/
theorem termSupport_instantiateAt_subset (depth : Nat) (replacement body : Tm) :
    termSupport (Tm.instantiateAt depth replacement body) ⊆
      termSupport replacement ∪ termSupport body := by
  induction body generalizing depth with
  | db index =>
      simp only [Tm.instantiateAt]
      split
      · simp [termSupport]
      · split <;> simp [termSupport]
  | named name | prim index => simp [Tm.instantiateAt, termSupport]
  | app function argument ihf iha | imp function argument ihf iha =>
      simp only [Tm.instantiateAt, termSupport]
      exact Finset.union_subset
        (ihf depth |>.trans (Finset.union_subset_union_right Finset.subset_union_left))
        (iha depth |>.trans (Finset.union_subset_union_right Finset.subset_union_right))
  | lam type body ih | all type body ih => exact ih (depth + 1)
  | typeApp function type ih | typeLam function ih | typeAll function ih => exact ih depth

theorem termSupport_instantiate_subset (replacement body : Tm) :
    termSupport (Tm.instantiate replacement body) ⊆
      termSupport replacement ∪ termSupport body :=
  termSupport_instantiateAt_subset 0 replacement body

/-- Dropping an unused term variable preserves every environmental dependency. -/
theorem termSupport_dropAt? {cutoff : Nat} {term result : Tm}
    (dropped : Tm.dropAt? cutoff term = some result) :
    termSupport result = termSupport term := by
  induction term generalizing cutoff result with
  | db index =>
      simp only [Tm.dropAt?] at dropped
      split at dropped
      · cases dropped; rfl
      · split at dropped
        · cases dropped
        · cases dropped; rfl
  | named name | prim index => cases dropped; rfl
  | app function argument ihf iha | imp function argument ihf iha =>
      cases hf : Tm.dropAt? cutoff function <;> cases ha : Tm.dropAt? cutoff argument <;>
        simp_all [Tm.dropAt?, termSupport]
      all_goals subst result; simp [termSupport, ihf hf, iha ha]
  | lam type body ih | all type body ih =>
      cases hb : Tm.dropAt? (cutoff + 1) body <;> simp_all [Tm.dropAt?, termSupport]
      subst result; simp [termSupport, ih hb]
  | typeApp function type ih | typeLam function ih | typeAll function ih =>
      cases hb : Tm.dropAt? cutoff function <;> simp_all [Tm.dropAt?, termSupport]
      all_goals subst result; simp [termSupport, ih hb]

/-- Dropping an unused type variable changes annotations but not dependencies. -/
theorem termSupport_typeDropAt? {cutoff : Nat} {term result : Tm}
    (dropped : Tm.typeDropAt? cutoff term = some result) :
    termSupport result = termSupport term := by
  induction term generalizing cutoff result with
  | db index | named name | prim index => cases dropped; rfl
  | app function argument ihf iha | imp function argument ihf iha =>
      cases hf : Tm.typeDropAt? cutoff function <;> cases ha : Tm.typeDropAt? cutoff argument <;>
        simp_all [Tm.typeDropAt?, termSupport]
      all_goals subst result; simp [termSupport, ihf hf, iha ha]
  | lam type body ih | all type body ih =>
      cases ht : Tp.dropAt? cutoff type <;> cases hb : Tm.typeDropAt? cutoff body <;>
        simp_all [Tm.typeDropAt?, termSupport]
      all_goals subst result; simp [termSupport, ih hb]
  | typeApp function type ih =>
      cases hf : Tm.typeDropAt? cutoff function <;> cases ht : Tp.dropAt? cutoff type <;>
        simp_all [Tm.typeDropAt?, termSupport]
      subst result; simp [termSupport, ih hf]
  | typeLam body ih | typeAll body ih =>
      cases hb : Tm.typeDropAt? (cutoff + 1) body <;> simp_all [Tm.typeDropAt?, termSupport]
      all_goals subst result; simp [termSupport, ih hb]

/-- One bottom-up beta/eta pass introduces no environmental dependency. -/
theorem termSupport_normalizeOne_subset (term : Tm) :
    termSupport (Tm.normalizeOne term).1 ⊆ termSupport term := by
  induction term with
  | db index | named name | prim index => exact Finset.Subset.refl _
  | app function argument ihf iha =>
      generalize hf : Tm.normalizeOne function = normalizedFunction at *
      generalize ha : Tm.normalizeOne argument = normalizedArgument at *
      rcases normalizedFunction with ⟨functionResult, functionStable⟩
      rcases normalizedArgument with ⟨argumentResult, argumentStable⟩
      simp only [Tm.normalizeOne, hf, ha]
      cases functionResult with
      | lam type body =>
          exact (termSupport_instantiate_subset argumentResult body).trans
            (by simpa [termSupport, Finset.union_comm] using Finset.union_subset_union iha ihf)
      | _ => exact Finset.union_subset_union ihf iha
  | lam type body ih =>
      generalize hb : Tm.normalizeOne body = normalizedBody at *
      rcases normalizedBody with ⟨bodyResult, bodyStable⟩
      simp only [Tm.normalizeOne, hb]
      split
      next _ function =>
        cases hd : Tm.dropAt? 0 function with
        | none => simpa [hd, termSupport] using ih
        | some contracted =>
            change termSupport contracted ⊆ termSupport body
            rw [termSupport_dropAt? hd]
            exact Finset.subset_union_left.trans ih
      next => exact ih
  | typeApp function type ih =>
      generalize hf : Tm.normalizeOne function = normalizedFunction at *
      rcases normalizedFunction with ⟨functionResult, functionStable⟩
      simp only [Tm.normalizeOne, hf]
      cases functionResult with
      | typeLam body => simpa only [Prod.fst, termSupport_typeInstantiate, termSupport] using ih
      | _ => exact ih
  | typeLam body ih =>
      generalize hb : Tm.normalizeOne body = normalizedBody at *
      rcases normalizedBody with ⟨bodyResult, bodyStable⟩
      simp only [Tm.normalizeOne, hb]
      split
      next _ function =>
        cases hd : Tm.typeDropAt? 0 function with
        | none => simpa [hd, termSupport] using ih
        | some contracted =>
            change termSupport contracted ⊆ termSupport body
            rw [termSupport_typeDropAt? hd]
            simpa [termSupport] using ih
      next => exact ih
  | imp domain codomain ihd ihc => exact Finset.union_subset_union ihd ihc
  | all type body ih | typeAll body ih => exact ih

/-- Every successful bounded beta/eta normalization shrinks native support. -/
theorem termSupport_normalize_subset {fuel : Nat} {term result : Tm}
    (normalized : Tm.normalize fuel term = some result) :
    termSupport result ⊆ termSupport term := by
  induction fuel generalizing term result with
  | zero =>
      simp only [Tm.normalize] at normalized
      split at normalized
      · cases normalized
        exact termSupport_normalizeOne_subset term
      · cases normalized
  | succ fuel ih =>
      simp only [Tm.normalize] at normalized
      split at normalized
      · cases normalized
        exact termSupport_normalizeOne_subset term
      · exact (ih normalized).trans (termSupport_normalizeOne_subset term)

namespace Examples

/-- A real beta contraction retains its surviving constant and removes the
discarded argument's primitive dependency. -/
def discardArgument : Tm := .app (.lam .prop (.named "kept")) (.prim 7)

theorem discardArgument_normalizes :
    Tm.normalize 1 discardArgument = some (.named "kept") := rfl

theorem discarded_dependency_present :
    Dependency.primitive 7 ∈ termSupport discardArgument := by decide

theorem discarded_dependency_absent :
    Dependency.primitive 7 ∉ termSupport (.named "kept") := by decide

theorem normalization_support_not_always_equal :
    ¬ (∀ fuel term result, Tm.normalize fuel term = some result →
      termSupport result = termSupport term) := by
  intro preserves
  have equal := preserves 1 discardArgument (.named "kept") discardArgument_normalizes
  exact discarded_dependency_absent (equal ▸ discarded_dependency_present)

/-- The support distinguishes a known proof from a term with the same spelling. -/
theorem proof_and_term_names_distinct :
    proofSupport (.known "p") ≠ termSupport (.named "p") := by decide

end Examples

#print axioms termSupport_instantiate_subset
#print axioms termSupport_dropAt?
#print axioms termSupport_typeDropAt?
#print axioms termSupport_normalizeOne_subset
#print axioms termSupport_normalize_subset
#print axioms Examples.normalization_support_not_always_equal

end Mettapedia.Languages.Megalodon.NativeSupport
