import Mettapedia.Logic.TierZero.Adequacy.MM0ScopedArgumentInterfaces

/-!
# Exact MM0 argument admission by constructing restricted contextual bodies

Sorting remains the independent finite argument check. Dependency eligibility
is realized by constructing each argument's body in its declaration-derived
contextual interface with the common recovery/graft operations. A body with
an undeclared outer occurrence cannot be constructed.

The resulting admission is equivalent to independent MM0 admissible
substitution. It does not call the old pairwise dependency Boolean checker.
Binder-sensitive definition-body and dummy obligations remain separate.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.MM0ScopedArgumentAdmission

open Mettapedia.Languages.MM0.Kernel
open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings
open MM0ContextualSupport
open MM0ScopedArgumentInterfaces

private theorem collect_isSome_iff {A B : Type} (function : A → Option B) (inputs : List A) :
    (inputs.mapM function).isSome = true ↔ ∀ input ∈ inputs, (function input).isSome = true := by
  induction inputs with
  | nil => simp
  | cons input inputs earlier =>
      cases head : function input <;> cases tail : inputs.mapM function <;>
        simp_all [List.mapM_cons]

private theorem collect_iff {A B : Type} (function : A → Option B) (inputs : List A) (outputs : List B) :
    inputs.mapM function = some outputs ↔ List.Forall₂ (fun input output => function input = some output) inputs outputs := by
  induction inputs generalizing outputs with
  | nil => cases outputs <;> simp
  | cons input inputs earlier =>
      cases outputs with
      | nil =>
          cases head : function input <;> cases tail : inputs.mapM function <;>
            simp [List.mapM_cons, head, tail]
      | cons output outputs =>
          cases head : function input <;> cases tail : inputs.mapM function <;>
            simp [List.mapM_cons, head, tail, ← earlier]

def recoverBodies (formal target : Context) (expressions : List Preterm) : Option (List (Term Head)) :=
  let entries := Substitution.entries formal expressions
  entries.mapM (recoverEntry target entries)

theorem recoverBodies_iff (formal target : Context) (expressions : List Preterm) (bodies : List (Term Head)) :
    recoverBodies formal target expressions = some bodies ↔
      List.Forall₂ (fun entry body => recoverEntry target (Substitution.entries formal expressions) entry = some body)
        (Substitution.entries formal expressions) bodies :=
  collect_iff _ _ _

theorem recoverBodies_isSome_iff {sorts : SortSignature} {signature : TermSignature}
    {formal target : Context} {expressions : List Preterm}
    (formed : Context.WellFormed sorts target)
    (typed : List.Forall₂ (Preterm.FitsBinder signature target) expressions formal) :
    (recoverBodies formal target expressions).isSome = true ↔
      ∀ source ∈ Substitution.entries formal expressions,
        Substitution.RowIndependent target (Substitution.entries formal expressions) source := by
  rw [recoverBodies, collect_isSome_iff]
  have exactEntry : ∀ entry ∈ Substitution.entries formal expressions,
      (recoverEntry target (Substitution.entries formal expressions) entry).isSome = true ↔
        ∀ source ∈ Substitution.entries formal expressions, ∀ sort image,
          source.1 = (.bound sort, .var image) → Substitution.PairIndependent target source.2 image entry := by
    intro entry member
    obtain ⟨support, supported⟩ := Substitution.typed_entry_support typed entry member
    exact recoverEntry_iff supported (encode_supported formed supported)
  constructor
  · intro recovered source present sort image bound other otherPresent
    exact (exactEntry other otherPresent).mp (recovered other otherPresent) source present sort image bound
  · intro independent other present
    apply (exactEntry other present).mpr
    intro source sourcePresent sort image bound
    exact independent source sourcePresent sort image bound other present

def construct (signature : TermSignature) (formal target : Context) (expressions : List Preterm) :
    Option (List (Term Head)) :=
  if Substitution.checkArguments signature target expressions formal then recoverBodies formal target expressions else none

theorem construct_isSome_iff {sorts : SortSignature} (signature : TermSignature) (formal target : Context)
    (formed : Context.WellFormed sorts target) (expressions : List Preterm) :
    (construct signature formal target expressions).isSome = true ↔
      Substitution.Admissible signature formal target expressions := by
  constructor
  · intro accepted
    unfold construct at accepted
    split at accepted
    · rename_i sorted
      have typed := (Substitution.checkArguments_iff _ _ _ _).mp sorted
      exact ⟨typed, (recoverBodies_isSome_iff formed typed).mp accepted⟩
    · cases accepted
  · intro admitted
    have sorted := (Substitution.checkArguments_iff _ _ _ _).mpr admitted.typed
    rw [construct, if_pos sorted]
    exact (recoverBodies_isSome_iff formed admitted.typed).mpr admitted.independent

theorem construct_reconstructs {signature : TermSignature} {formal target : Context}
    {expressions : List Preterm} {bodies : List (Term Head)}
    (constructed : construct signature formal target expressions = some bodies) :
    List.Forall₂ (fun entry body =>
      Mettapedia.GSLT.LanguageDef.SignatureIndexedABT.ScopedApplication.graft
        (occurrence target.length (Substitution.entries formal expressions) entry).arity
        (occurrence target.length (Substitution.entries formal expressions) entry).arguments body =
        some (encode target entry.1.2)) (Substitution.entries formal expressions) bodies := by
  unfold construct at constructed
  split at constructed
  · exact ((recoverBodies_iff formal target expressions bodies).mp constructed).imp
      (fun _ _ recovered => recoverEntry_grafts recovered)
  · cases constructed

theorem construct_body_count {signature : TermSignature} {formal target : Context}
    {expressions : List Preterm} {bodies : List (Term Head)}
    (constructed : construct signature formal target expressions = some bodies) :
    bodies.length = formal.length := by
  unfold construct at constructed
  split at constructed
  · rename_i sorted
    have typed := (Substitution.checkArguments_iff _ _ _ _).mp sorted
    have count := ((recoverBodies_iff formal target expressions bodies).mp constructed).length_eq
    simpa [Substitution.entries, List.length_zipIdx, List.length_zip, typed.length_eq] using count.symm
  · cases constructed

end Mettapedia.Logic.TierZero.Adequacy.MM0ScopedArgumentAdmission
