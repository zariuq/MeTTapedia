import Mettapedia.Logic.TierZero.Adequacy.MM0ContextualSupport
import Mettapedia.Languages.MM0.Kernel.AdmissibleSubstitution
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ScopedApplication

/-!
# MM0 theorem-argument admission through native support masks

Argument sorting is the independent MM0 sorting check. Dependency checks use
the actual shared ABT support representation. The combined executable check
accepts exactly MM0's independent `Substitution.Admissible` judgment.

Only forbidden images of bound formals are excluded. Other ambient variables
remain available. This is argument admission, not full MM0 proof adequacy.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.MM0ContextualSupport

open Mettapedia.Languages.MM0.Kernel
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings

/-- Retain every available position except the bound variable forbidden by this pair. -/
def excluding (width forbidden : Nat) : Thin :=
  ScopedApplication.mask (Finset.univ.filter fun i : Fin width => i.val ≠ forbidden)

theorem excluding_bit {width index : Nat} (within : index < width) (forbidden : Nat) :
    Thin.bit (excluding width forbidden) index = true ↔ index ≠ forbidden := by
  simpa [excluding] using
    (show Thin.bit (ScopedApplication.mask
      (Finset.univ.filter fun i : Fin width => i.val ≠ forbidden)) (⟨index, within⟩ : Fin width).val = true ↔
      (⟨index, within⟩ : Fin width) ∈ (Finset.univ.filter fun i : Fin width => i.val ≠ forbidden) from by
        rw [ScopedApplication.mask_bit, decide_eq_true_eq])

theorem exclusion_check_exact (used : Thin) (forbidden : Nat) :
    ContextualMatching.subCheck used (excluding used.length forbidden) = true ↔
      Thin.bit used forbidden = false := by
  rw [ContextualMatching.subCheck_iff]
  constructor
  · intro included
    cases usedHere : Thin.bit used forbidden with
    | false => rfl
    | true =>
      have impossible := (excluding_bit (Scope.lt_length_of_bit usedHere) forbidden).mp
        (included forbidden usedHere)
      exact False.elim (impossible rfl)
  · intro absent index usedHere
    apply (excluding_bit (Scope.lt_length_of_bit usedHere) forbidden).mpr
    intro same
    subst index
    rw [absent] at usedHere
    cases usedHere

def checkPairNative (store : Store Head) (target : Context)
    (formalBound targetBound : Nat) (other : Substitution.Entry) : Bool :=
  if other.1.1.DependsOn other.2 formalBound then true
  else
    let reference := (encodeR store (encode target other.1.2)).2
    ContextualMatching.subCheck reference.thin (excluding reference.thin.length targetBound)

theorem checkPairNative_iff {store : Store Head} (canonical : Canonical store)
    {target : Context} {formalBound targetBound : Nat} {other : Substitution.Entry}
    {support : Finset Nat} (supported : Preterm.Supports target other.1.2 support) :
    checkPairNative store target formalBound targetBound other = true ↔
      Substitution.PairIndependent target formalBound targetBound other := by
  by_cases depends : other.1.1.DependsOn other.2 formalBound
  · simp [checkPairNative, Substitution.PairIndependent, depends]
  · simp only [checkPairNative, depends, ↓reduceIte, Substitution.PairIndependent,
      exclusion_check_exact]
    have occurrence := reference_hasVar supported store canonical targetBound
    cases used : Thin.bit (encodeR store (encode target other.1.2)).2.thin targetBound <;>
      simp_all

theorem checkPairNative_eq {store : Store Head} (canonical : Canonical store)
    {target : Context} {formalBound targetBound : Nat} {other : Substitution.Entry}
    {support : Finset Nat} (supported : Preterm.Supports target other.1.2 support) :
    checkPairNative store target formalBound targetBound other =
      Substitution.checkPair target formalBound targetBound other := by
  apply Bool.eq_iff_iff.mpr
  rw [checkPairNative_iff canonical supported, Substitution.checkPair_iff supported]

def checkRowNative (store : Store Head) (target : Context)
    (allEntries : List Substitution.Entry) (entry : Substitution.Entry) : Bool :=
  match entry.1 with
  | (.bound _, .var image) => allEntries.all (checkPairNative store target entry.2 image)
  | _ => true

theorem checkRowNative_eq {store : Store Head} (canonical : Canonical store)
    {target : Context} {allEntries : List Substitution.Entry} (entry : Substitution.Entry)
    (supported : ∀ other ∈ allEntries, ∃ support, Preterm.Supports target other.1.2 support) :
    checkRowNative store target allEntries entry = Substitution.checkRow target allEntries entry := by
  rcases entry with ⟨⟨binder, expression⟩, position⟩
  cases binder with
  | regular sort dependencies => rfl
  | bound sort =>
    cases expression with
    | term symbol => rfl
    | app function argument => rfl
    | var image =>
      change allEntries.all (checkPairNative store target position image) =
        allEntries.all (Substitution.checkPair target position image)
      apply Bool.eq_iff_iff.mpr
      simp only [List.all_eq_true]
      apply forall_congr'
      intro other
      apply forall_congr'
      intro member
      obtain ⟨support, valid⟩ := supported other member
      rw [checkPairNative_eq canonical valid]

def checkAdmissibleNative (store : Store Head) (signature : TermSignature)
    (formal target : Context) (expressions : List Preterm) : Bool :=
  Substitution.checkArguments signature target expressions formal &&
    (Substitution.entries formal expressions).all
      (checkRowNative store target (Substitution.entries formal expressions))

/-- Exact agreement is proved from the independent typing/support judgments. -/
theorem checkAdmissibleNative_eq {store : Store Head} (canonical : Canonical store)
    (signature : TermSignature) (formal target : Context) (expressions : List Preterm) :
    checkAdmissibleNative store signature formal target expressions =
      Substitution.checkAdmissible signature formal target expressions := by
  unfold checkAdmissibleNative Substitution.checkAdmissible
  cases checked : Substitution.checkArguments signature target expressions formal with
  | false => rfl
  | true =>
    simp only [Bool.true_and]
    apply List.all_congr rfl
    intro entry
    exact checkRowNative_eq canonical entry
      (Substitution.typed_entry_support ((Substitution.checkArguments_iff _ _ _ _).mp checked))

/-- Executable argument admission with native masks is precisely MM0 admissibility. -/
theorem checkAdmissibleNative_iff {store : Store Head} (canonical : Canonical store)
    (signature : TermSignature) (formal target : Context) (expressions : List Preterm) :
    checkAdmissibleNative store signature formal target expressions = true ↔
      Substitution.Admissible signature formal target expressions := by
  rw [checkAdmissibleNative_eq canonical, Substitution.checkAdmissible_iff]

namespace AdmissionControls

def noSymbols : TermSignature := fun _ => none
def formals : Context := [.bound 0, .regular 0 ∅]

theorem native_admits_other_ambient_variables :
    checkAdmissibleNative [] noSymbols formals Controls.independentContext [.var 0, .var 2] = true := by
  rw [checkAdmissibleNative_eq canonical_nil]
  decide

theorem native_refuses_forbidden_dependency :
    checkAdmissibleNative [] noSymbols formals Controls.dependentContext [.var 0, .var 2] = false := by
  rw [checkAdmissibleNative_eq canonical_nil]
  decide

theorem native_retains_sort_check :
    checkAdmissibleNative [] noSymbols [.bound 0] [.bound 1] [.var 0] = false := by
  rw [checkAdmissibleNative_eq canonical_nil]
  decide

theorem native_refuses_undefined_argument :
    checkAdmissibleNative [] noSymbols [.regular 0 ∅] [] [.var 0] = false := by
  rw [checkAdmissibleNative_eq canonical_nil]
  decide

theorem native_refuses_missing_argument :
    checkAdmissibleNative [] noSymbols formals Controls.independentContext [.var 0] = false := by
  rw [checkAdmissibleNative_eq canonical_nil]
  decide

end AdmissionControls

end Mettapedia.Logic.TierZero.Adequacy.MM0ContextualSupport
