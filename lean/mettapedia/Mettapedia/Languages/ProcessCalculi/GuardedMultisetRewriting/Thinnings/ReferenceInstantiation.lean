import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.SharedApplication
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.Matching
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ContextualPatterns

/-!
# Contextual instantiation with reference assignments

Occurrence argument syntax is encoded by the existing field encoder; assigned
parameter bodies stay as references and are instantiated by the shared graft.
Both success and refusal retain an explicit canonical store extension.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ContextualPatterns

open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT.ScopedApplication
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources

variable {Head V : Type} [DecidableEq Head]

def argumentFields : List (Term Head) → Fields Head
  | [] => .nil
  | term :: rest => .cons 0 term (argumentFields rest)

def encodeArguments (store : Store Head) (arguments : List (Term Head)) : Store Head × List Ref :=
  let result := encodeFieldsR store (argumentFields arguments)
  (result.1, result.2.map Prod.snd)

theorem encodeArguments_spec (store : Store Head) (canonical : Canonical store)
    (arguments : List (Term Head)) :
    store <+: (encodeArguments store arguments).1 ∧ Canonical (encodeArguments store arguments).1 ∧
      (∀ r ∈ (encodeArguments store arguments).2, CanonRef (encodeArguments store arguments).1 r) ∧
      (encodeArguments store arguments).2.map (unfold (encodeArguments store arguments).1) = arguments := by
  induction arguments generalizing store with
  | nil => exact ⟨List.prefix_refl _, canonical, by simp [encodeArguments, argumentFields, encodeFieldsR], rfl⟩
  | cons term rest ih =>
    obtain ⟨grows, nextCanonical, headValid, _⟩ := encodeR_spec store canonical term
    obtain ⟨more, finalCanonical, tailValid, tailTerms⟩ := ih _ nextCanonical
    refine ⟨grows.trans more, finalCanonical, ?_, ?_⟩
    · intro r member
      change r ∈ (encodeR store term).2 :: (encodeArguments (encodeR store term).1 rest).2 at member
      rcases List.mem_cons.mp member with rfl | member
      · exact headValid.prefix more
      · exact tailValid r member
    · change ((encodeR store term).2 :: (encodeArguments (encodeR store term).1 rest).2).map
        (unfold (encodeArguments (encodeR store term).1 rest).1) = term :: rest
      rw [List.map_cons, tailTerms, unfold_prefix nextCanonical.topo more headValid.valid,
        encodeR_unfold canonical]

def atOccurrenceR (store : Store Head) (assignment : Subst V Ref) (occurrence : Occurrence Head V) :
    Store Head × Option Ref :=
  match assignment occurrence.name with
  | none => (store, none)
  | some body =>
      let prepared := encodeArguments store occurrence.arguments
      match SharedApplication.graftR prepared.1 occurrence.arity prepared.2 body with
      | none => (prepared.1, none)
      | some result => (result.1, some result.2)

theorem atOccurrenceR_spec (store : Store Head) (canonical : Canonical store)
    (assignment : Subst V Ref) (validAssignment : CanonSubst store assignment)
    (occurrence : Occurrence Head V) :
    store <+: (atOccurrenceR store assignment occurrence).1 ∧
      Canonical (atOccurrenceR store assignment occurrence).1 ∧
      (∀ r, (atOccurrenceR store assignment occurrence).2 = some r →
        CanonRef (atOccurrenceR store assignment occurrence).1 r) ∧
      (atOccurrenceR store assignment occurrence).2.map (unfold (atOccurrenceR store assignment occurrence).1) =
        Pattern.atOccurrence (unfoldSubst store assignment) occurrence := by
  cases assigned : assignment occurrence.name with
  | none =>
    simp only [atOccurrenceR, assigned]
    refine ⟨List.prefix_refl _, canonical, ?_, ?_⟩
    · intro r impossible; cases impossible
    · simp [Pattern.atOccurrence, unfoldSubst, assigned]
  | some body =>
    have validBody := validAssignment occurrence.name body assigned
    obtain ⟨grows, nextCanonical, arguments, values⟩ := encodeArguments_spec store canonical occurrence.arguments
    have expected := SharedApplication.graftR_spec (encodeArguments store occurrence.arguments).1
      nextCanonical occurrence.arity (encodeArguments store occurrence.arguments).2 body
      (validBody.prefix grows) arguments
    rw [values, unfold_prefix canonical.topo grows validBody.valid] at expected
    simp only [atOccurrenceR, assigned]
    cases applied : SharedApplication.graftR (encodeArguments store occurrence.arguments).1 occurrence.arity
        (encodeArguments store occurrence.arguments).2 body with
    | none =>
      refine ⟨grows, nextCanonical, ?_, ?_⟩
      · intro r impossible; cases impossible
      · simpa [applied, Pattern.atOccurrence, unfoldSubst, assigned] using expected
    | some result =>
      obtain ⟨more, finalCanonical, finalBody⟩ :=
        SharedApplication.graftR_canonical nextCanonical (validBody.prefix grows) arguments applied
      refine ⟨grows.trans more, finalCanonical, ?_, ?_⟩
      · intro r same
        cases same
        exact finalBody
      · simpa [applied, Pattern.atOccurrence, unfoldSubst, assigned] using expected

end Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ContextualPatterns
