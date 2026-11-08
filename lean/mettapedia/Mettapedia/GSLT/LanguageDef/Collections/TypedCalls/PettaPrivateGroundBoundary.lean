import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaRowTypeCodec

/-!
# Computed row isolation at the actual caller guard boundary

The admitted input check produces exactly one concrete caller refinement.
Its effect on every other nonconstant request is derived from occurrence
counting and the row codec. Any later substitution leaves the ground subject
and its recorded range unchanged, so the actual return query and join are
readonly. This theorem does not assert that an arbitrary body transition is
a substitution extension; source-run transport must provide that link.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaPrivateGroundBoundary

open Mettapedia.Logic.LP (Term Subst)
open Mettapedia.Logic.LP.ConjunctiveUnification (applyTerm_of_isGround)
open Mettapedia.Languages.MeTTa.PeTTa
open IntrinsicTypeFacts (TypeTerm signature Declaration)
open IndependentTypeOutput (Path)
open StableGroundTypeQueries (GroundUninterpreted groundSchema admitted_is_ground schema_is_ground)
open PettaContractRowIsolation (Parameter recognizes)
open PettaRowTypeCodec (encode)

def entered (caller : Subst signature) (name : Nat) (subject : TypeTerm) : Subst signature :=
  Subst.comp (Subst.single name (groundSchema (caller.applyTerm subject))) caller

theorem entered_subject_unchanged (library : List Declaration) (caller : Subst signature)
    (name : Nat) (subject : TypeTerm)
    (admitted : GroundUninterpreted library (caller.applyTerm subject)) :
    (entered caller name subject).applyTerm subject = caller.applyTerm subject := by
  rw [entered, Subst.applyTerm_comp]
  exact applyTerm_of_isGround _ (admitted_is_ground _ _ admitted)

theorem entered_range_assigned (caller : Subst signature) (name : Nat) (subject expected : TypeTerm)
    (unbound : caller.applyTerm expected = .var name) :
    (entered caller name subject).applyTerm expected = groundSchema (caller.applyTerm subject) := by
  rw [entered, Subst.applyTerm_comp, unbound]
  exact Subst.single_eq (σ := signature) name _

/-- No value-only recursive result is supplied: this is the actual query
and actual incremental first-order join after an arbitrary refinement of
the successful input record. -/
theorem refined_return_is_readonly (library : List Declaration) (caller later : Subst signature)
    (name : Nat) (subject expected : TypeTerm) (fuel : Nat) (path : Path)
    (unbound : caller.applyTerm expected = .var name)
    (admitted : GroundUninterpreted library (caller.applyTerm subject))
    (enough : (caller.applyTerm subject).size ≤ fuel) :
    StableGroundGuardDischarge.check library fuel path
      (Subst.comp later (entered caller name subject)) subject expected =
      some [Subst.comp later (entered caller name subject)] := by
  have unchanged : (Subst.comp later (entered caller name subject)).applyTerm subject =
      caller.applyTerm subject := by
    rw [Subst.applyTerm_comp, entered_subject_unchanged library caller name subject admitted]
    exact applyTerm_of_isGround later (admitted_is_ground _ _ admitted)
  apply StableGroundGuardDischarge.return_guard_readonly
  · rw [unchanged]
    exact admitted
  · rw [unchanged]
    exact enough
  · rw [unchanged, Subst.applyTerm_comp, entered_range_assigned caller name subject expected unbound]
    exact applyTerm_of_isGround later (schema_is_ground _ _ admitted)

variable {V : Type} [DecidableEq V] [BEq V] [LawfulBEq V]

/-- Native row recognition plus the actual reached row encoding gives the
complete local input/return guard pair, not merely equality of type erasures.
The one caller substitution is retained, with all branch multiplicity. -/
theorem recognized_ground_pair
    (before : List (Parameter V)) (current : Parameter V) (after : List (Parameter V))
    (authoredRange : Ty String) (resolvedRange : Ty V) (name : V)
    (recognized : recognizes before current after authoredRange resolvedRange = some name)
    (sourceNames : String → Nat) (residualNames : V → Nat)
    (injective : Function.Injective residualNames) (instance_ : String → Ty V)
    (caller : Subst signature)
    (reads : ∀ variableName, caller (sourceNames variableName) = encode residualNames (instance_ variableName))
    (resolved : ∀ parameter ∈ before ++ after, parameter.constant = false →
      parameter.authored.bind instance_ = parameter.resolved)
    (library : List Declaration) (subject expected : TypeTerm) (fuel : Nat) (path : Path)
    (unbound : caller.applyTerm expected = .var (residualNames name))
    (admitted : GroundUninterpreted library (caller.applyTerm subject))
    (enough : (caller.applyTerm subject).size ≤ fuel) :
    StableGroundGuardDischarge.check library fuel path caller subject expected =
        some [entered caller (residualNames name) subject] ∧
    (∀ parameter ∈ before ++ after, parameter.constant = false →
      (entered caller (residualNames name) subject).applyTerm (encode sourceNames parameter.authored) =
        caller.applyTerm (encode sourceNames parameter.authored)) ∧
    (∀ later : Subst signature,
      StableGroundGuardDischarge.check library fuel path
        (Subst.comp later (entered caller (residualNames name) subject)) subject expected =
      some [Subst.comp later (entered caller (residualNames name) subject)]) := by
  refine ⟨StableGroundGuardDischarge.input_guard_single_refinement library fuel path caller
    subject expected (residualNames name) unbound admitted enough, ?_, ?_⟩
  · exact PettaRowTypeCodec.recognized_pair_preserves_source_requests before current after
      authoredRange resolvedRange name recognized sourceNames residualNames injective instance_
      caller reads resolved _
  · intro later
    exact refined_return_is_readonly library caller later (residualNames name) subject expected fuel path
      unbound admitted enough

namespace Controls

def subject : TypeTerm := .const (.number "7")

theorem input_records_private_type_once :
    StableGroundGuardDischarge.check [] 1 [] (Subst.id signature) subject (.var 3) =
      some [entered (Subst.id signature) 3 subject] := by
  exact StableGroundGuardDischarge.input_guard_single_refinement [] 1 [] (Subst.id signature)
    subject (.var 3) 3 rfl (by trivial) (by decide +kernel)

/-- Interpreted bindings made later do not invalidate a ground protected
value. This does not authorize the corresponding open-value rule. -/
theorem arbitrary_later_interpreted_binding_preserves_return :
    StableGroundGuardDischarge.check [] 1 []
      (Subst.comp (Subst.single 19 (.const (.symbol "Known")))
        (entered (Subst.id signature) 3 subject)) subject (.var 3) =
      some [Subst.comp (Subst.single (σ := signature) 19 (.const (.symbol "Known")))
        (entered (Subst.id signature) 3 subject)] := by
  exact refined_return_is_readonly [] (Subst.id signature) _ 3 subject (.var 3) 1 [] rfl
    (by trivial) (by decide +kernel)

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaPrivateGroundBoundary
