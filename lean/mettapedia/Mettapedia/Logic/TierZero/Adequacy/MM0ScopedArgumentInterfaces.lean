import Mettapedia.Logic.TierZero.Adequacy.MM0ContextualPatterns
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ContextualScopeBodies

/-!
# MM0 formal dependencies become actual contextual argument interfaces

An interface is computed from declaration metadata and the images of bound
formals, independently of the expression being admitted. A formal may use its
declared dependency images and every other ambient variable. Each undeclared
bound-formal image is absent from its spine.

The common body-recovery operation constructs a term in that smaller context.
Exactness is proved against MM0's complete occurrence-independence judgment.
Definition-body free-variable admission is a separate binder-sensitive judgment
and is not replaced by this theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.MM0ScopedArgumentInterfaces

open Mettapedia.Languages.MM0.Kernel
open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings
open MM0ContextualSupport

def sourceAllows (source other : Substitution.Entry) (targetIndex : Nat) : Bool :=
  match source.1 with
  | (.bound _, .var image) => decide (targetIndex = image → other.1.1.DependsOn other.2 source.2)
  | _ => true

theorem sourceAllows_iff (source other : Substitution.Entry) (targetIndex : Nat) :
    sourceAllows source other targetIndex = true ↔
      ∀ sort image, source.1 = (.bound sort, .var image) →
        targetIndex = image → other.1.1.DependsOn other.2 source.2 := by
  rcases source with ⟨⟨binder, expression⟩, position⟩
  cases binder with
  | regular sort dependencies => simp [sourceAllows]
  | bound sort =>
      cases expression <;> simp [sourceAllows]
      exact imp_iff_not_or.symm

def permitted (entries : List Substitution.Entry) (other : Substitution.Entry) (targetIndex : Nat) : Bool :=
  entries.all (fun source => sourceAllows source other targetIndex)

theorem permitted_iff (entries : List Substitution.Entry) (other : Substitution.Entry) (targetIndex : Nat) :
    permitted entries other targetIndex = true ↔
      ∀ source ∈ entries, ∀ sort image, source.1 = (.bound sort, .var image) →
        targetIndex = image → other.1.1.DependsOn other.2 source.2 := by
  simp [permitted, List.all_eq_true, sourceAllows_iff]

/-- The local interface contains every ambient index except images forbidden
by the declaration's own bound-variable dependency relation. -/
def interface (width : Nat) (entries : List Substitution.Entry) (other : Substitution.Entry) : Thin :=
  List.ofFn fun index : Fin width => permitted entries other index.val

theorem interface_length (width : Nat) (entries : List Substitution.Entry) (other : Substitution.Entry) :
    (interface width entries other).length = width := by simp [interface]

theorem interface_bit {width targetIndex : Nat} (inside : targetIndex < width)
    (entries : List Substitution.Entry) (other : Substitution.Entry) :
    Thin.bit (interface width entries other) targetIndex = true ↔
      ∀ source ∈ entries, ∀ sort image, source.1 = (.bound sort, .var image) →
        targetIndex = image → other.1.1.DependsOn other.2 source.2 := by
  simpa [ScopedApplication.bit_eq_get, interface, inside] using permitted_iff entries other targetIndex

def occurrence (width : Nat) (entries : List Substitution.Entry) (entry : Substitution.Entry) :
    ContextualPatterns.Occurrence Head Nat :=
  let allowed := interface width entries entry
  ⟨entry.2, Thin.ones allowed, ContextualScopeBodies.arguments allowed⟩

theorem occurrence_is_an_input (width : Nat) (entries : List Substitution.Entry) (entry : Substitution.Entry) :
    (occurrence width entries entry).Input := by
  refine ⟨ContextualScopeBodies.indices (interface width entries entry), rfl, ?_,
    ContextualScopeBodies.indices_distinct _⟩
  exact (ContextualScopeBodies.indices_length _).symm

def recoverEntry (target : Context) (entries : List Substitution.Entry) (entry : Substitution.Entry) :
    Option (Term Head) :=
  ContextualScopeBodies.recover (interface target.length entries entry) (encode target entry.1.2)

theorem recoverEntry_grafts {target : Context} {entries : List Substitution.Entry}
    {entry : Substitution.Entry} {body : Term Head} (recovered : recoverEntry target entries entry = some body) :
    Mettapedia.GSLT.LanguageDef.SignatureIndexedABT.ScopedApplication.graft
      (occurrence target.length entries entry).arity (occurrence target.length entries entry).arguments body =
      some (encode target entry.1.2) :=
  ContextualScopeBodies.recover_sound recovered

/-- The exact pairwise dependency judgment is represented by existence of a
body in the actual restricted interface. No free-variable approximation is used. -/
theorem recoverEntry_iff {target : Context} {entries : List Substitution.Entry}
    {entry : Substitution.Entry} {support : Finset Nat}
    (supported : Preterm.Supports target entry.1.2 support)
    (scopedTerm : Term.supportedAt target.length (encode target entry.1.2) = true) :
    (recoverEntry target entries entry).isSome = true ↔
      ∀ source ∈ entries, ∀ sort image, source.1 = (.bound sort, .var image) →
        Substitution.PairIndependent target source.2 image entry := by
  rw [recoverEntry, ContextualScopeBodies.recover_isSome_iff]
  constructor
  · intro allAllowed source member sort image bound independent occurs
    have used := (hasVar_exact supported image).mpr occurs
    have inside := (Scope.supportedAt_iff _ _).mp scopedTerm image used
    have allowed := (interface_bit inside entries entry).mp (allAllowed image used)
    exact independent (allowed source member sort image bound rfl)
  · intro independent targetIndex used
    have inside := (Scope.supportedAt_iff _ _).mp scopedTerm targetIndex used
    apply (interface_bit inside entries entry).mpr
    intro source member sort image bound same
    by_contra excluded
    subst targetIndex
    exact independent source member sort image bound excluded ((hasVar_exact supported image).mp used)

end Mettapedia.Logic.TierZero.Adequacy.MM0ScopedArgumentInterfaces
