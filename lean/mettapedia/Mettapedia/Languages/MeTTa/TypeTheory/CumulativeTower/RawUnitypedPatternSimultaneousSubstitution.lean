import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.RawUnitypedPatternBoundary

/-!
# Simultaneous substitution on the exact canonical Pattern image

The raw unityped CwF already carries simultaneous substitutions as ordered
families of intrinsically scoped terms.  This module gives that existing
action an executable boundary over canonical MeTTaIL `Pattern` data.

The boundary carrier is an indexed vector, not a proposed surface syntax or
wire format.  Its index retains source arity, while decoding every component
at one declared target arity enforces common scope.  Order and duplicates are
therefore preserved rather than quotiented away.

The adapter proves identity and composition on the exact canonical image and
reflects every successful result to an intrinsic substitution.  Failure means
that an input lies outside the declared scoped image; it is not refutation of
the represented computation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace RawUnitypedPatternSimultaneousSubstitution

open RawUnitypedErasure
open RawUnitypedPatternBoundary
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwareSubstitutionBoundary
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## An arity-indexed boundary carrier -/

/-- An ordered vector of encoded substitution components.  The index is the
source arity.  Target scope is checked when the vector is decoded. -/
inductive EncodedSubstitution : Nat → Type where
  | nil : EncodedSubstitution 0
  | cons {source : Nat} : Pattern → EncodedSubstitution source →
      EncodedSubstitution (Nat.succ source)
  deriving Repr

/-- Encode an intrinsic simultaneous substitution component by component,
newest variable first. -/
def encodeSubstitution : {source target : Nat} →
    Sub Tower.Head source target → EncodedSubstitution source
  | 0, _, _ => .nil
  | Nat.succ _source, _, substitution =>
      .cons (encodeRawTerm (substitution 0))
        (encodeSubstitution (fun index => substitution index.succ))

/-- Decode every component at one declared target arity.  A component with a
different scope makes the whole vector fail closed. -/
def decodeSubstitution? (target : Nat) :
    {source : Nat} → EncodedSubstitution source →
      Option (Sub Tower.Head source target)
  | 0, .nil => some Fin.elim0
  | Nat.succ _, .cons first rest => do
      let firstTerm ← decodeRawTerm? target first
      let restSubstitution ← decodeSubstitution? target rest
      pure (consSub firstTerm restSubstitution)

/-- Every intrinsic simultaneous substitution round-trips. -/
@[simp] theorem decodeSubstitution?_encodeSubstitution
    {source target : Nat} (substitution : Sub Tower.Head source target) :
    decodeSubstitution? target (encodeSubstitution substitution) =
      some substitution := by
  induction source with
  | zero =>
      have substitutionEmpty : substitution = Fin.elim0 := by
        funext index
        exact Fin.elim0 index
      subst substitution
      rfl
  | succ prior ih =>
      rw [show encodeSubstitution substitution =
          .cons (encodeRawTerm (substitution 0))
            (encodeSubstitution (fun index => substitution index.succ)) by
        rfl]
      simp only [decodeSubstitution?, decodeRawTerm?_encodeRawTerm,
        ih (fun index => substitution index.succ)]
      exact congrArg some (consSub_eta substitution)

/-- Canonical substitution encoding loses neither order nor multiplicity. -/
theorem encodeSubstitution_injective (source target : Nat) :
    Function.Injective
      (encodeSubstitution : Sub Tower.Head source target →
        EncodedSubstitution source) := by
  intro first second equality
  have decodedEquality := congrArg (decodeSubstitution? target) equality
  simpa using decodedEquality

/-! ## Executable action and reflection -/

/-- Apply a decoded simultaneous substitution to a decoded canonical term and
return the exact canonical result. -/
def substituteEncoded? {source : Nat} (target : Nat)
    (substitution : EncodedSubstitution source) (term : Pattern) :
    Option Pattern := do
  let decodedSubstitution ← decodeSubstitution? target substitution
  let decodedTerm ← decodeRawTerm? source term
  pure (encodeRawTerm (subst decodedSubstitution decodedTerm))

/-- Canonical inputs compute to intrinsic simultaneous substitution. -/
@[simp] theorem substituteEncoded?_encode
    {source target : Nat} (substitution : Sub Tower.Head source target)
    (term : Tower.Tm source) :
    substituteEncoded? target (encodeSubstitution substitution)
        (encodeRawTerm term) =
      some (encodeRawTerm (subst substitution term)) := by
  simp [substituteEncoded?]

/-- Every successful result is the encoding of an intrinsic scoped term under
an intrinsic simultaneous substitution.  The adapter cannot invent an
unrelated target. -/
theorem substituteEncoded?_reflects
    {source target : Nat} {substitution : EncodedSubstitution source}
    {term result : Pattern}
    (accepted : substituteEncoded? target substitution term = some result) :
    ∃ decodedSubstitution : Sub Tower.Head source target,
      ∃ decodedTerm : Tower.Tm source,
        decodeSubstitution? target substitution = some decodedSubstitution ∧
        decodeRawTerm? source term = some decodedTerm ∧
        result = encodeRawTerm (subst decodedSubstitution decodedTerm) := by
  cases substitutionDecoded : decodeSubstitution? target substitution with
  | none =>
      simp [substituteEncoded?, substitutionDecoded] at accepted
  | some decodedSubstitution =>
      cases termDecoded : decodeRawTerm? source term with
      | none =>
          simp [substituteEncoded?, substitutionDecoded, termDecoded] at accepted
      | some decodedTerm =>
          simp [substituteEncoded?, substitutionDecoded, termDecoded] at accepted
          exact
            ⟨decodedSubstitution, decodedTerm, rfl, rfl, accepted.symm⟩

/-- Every successful output decodes to the exact intrinsic substituted term. -/
theorem substituteEncoded?_output_decodes
    {source target : Nat} {substitution : EncodedSubstitution source}
    {term result : Pattern}
    (accepted : substituteEncoded? target substitution term = some result) :
    ∃ decodedSubstitution : Sub Tower.Head source target,
      ∃ decodedTerm : Tower.Tm source,
        decodeSubstitution? target substitution = some decodedSubstitution ∧
        decodeRawTerm? source term = some decodedTerm ∧
        decodeRawTerm? target result =
          some (subst decodedSubstitution decodedTerm) := by
  obtain ⟨decodedSubstitution, decodedTerm, substitutionDecoded, termDecoded,
      resultEncoded⟩ := substituteEncoded?_reflects accepted
  subst result
  exact
    ⟨decodedSubstitution, decodedTerm, substitutionDecoded, termDecoded,
      decodeRawTerm?_encodeRawTerm _⟩

/-! ## Identity and composition -/

/-- Decode two adjacent substitutions, compose them intrinsically, and
re-encode the ordered result. -/
def composeEncoded? {source middle : Nat} (target : Nat)
    (later : EncodedSubstitution middle)
    (earlier : EncodedSubstitution source) :
    Option (EncodedSubstitution source) := do
  let decodedLater ← decodeSubstitution? target later
  let decodedEarlier ← decodeSubstitution? middle earlier
  pure (encodeSubstitution (subComp decodedLater decodedEarlier))

/-- Composition is exact on canonical substitution vectors. -/
@[simp] theorem composeEncoded?_encode
    {source middle target : Nat}
    (later : Sub Tower.Head middle target)
    (earlier : Sub Tower.Head source middle) :
    composeEncoded? target (encodeSubstitution later)
        (encodeSubstitution earlier) =
      some (encodeSubstitution (subComp later earlier)) := by
  simp [composeEncoded?]

/-- Every successful encoded composition reflects to two decoded intrinsic
substitutions and their exact intrinsic composite. -/
theorem composeEncoded?_reflects
    {source middle target : Nat}
    {later : EncodedSubstitution middle}
    {earlier result : EncodedSubstitution source}
    (accepted : composeEncoded? target later earlier = some result) :
    ∃ decodedLater : Sub Tower.Head middle target,
      ∃ decodedEarlier : Sub Tower.Head source middle,
        decodeSubstitution? target later = some decodedLater ∧
        decodeSubstitution? middle earlier = some decodedEarlier ∧
        result = encodeSubstitution (subComp decodedLater decodedEarlier) := by
  cases laterDecoded : decodeSubstitution? target later with
  | none =>
      simp [composeEncoded?, laterDecoded] at accepted
  | some decodedLater =>
      cases earlierDecoded : decodeSubstitution? middle earlier with
      | none =>
          simp [composeEncoded?, laterDecoded, earlierDecoded] at accepted
      | some decodedEarlier =>
          simp [composeEncoded?, laterDecoded, earlierDecoded] at accepted
          exact
            ⟨decodedLater, decodedEarlier, rfl, rfl, accepted.symm⟩

/-- Every successfully composed vector itself decodes to the intrinsic
composite it claims to represent. -/
theorem composeEncoded?_output_decodes
    {source middle target : Nat}
    {later : EncodedSubstitution middle}
    {earlier result : EncodedSubstitution source}
    (accepted : composeEncoded? target later earlier = some result) :
    ∃ decodedLater : Sub Tower.Head middle target,
      ∃ decodedEarlier : Sub Tower.Head source middle,
        decodeSubstitution? target later = some decodedLater ∧
        decodeSubstitution? middle earlier = some decodedEarlier ∧
        decodeSubstitution? target result =
          some (subComp decodedLater decodedEarlier) := by
  obtain ⟨decodedLater, decodedEarlier, laterDecoded, earlierDecoded,
      resultEncoded⟩ := composeEncoded?_reflects accepted
  subst result
  exact
    ⟨decodedLater, decodedEarlier, laterDecoded, earlierDecoded,
      decodeSubstitution?_encodeSubstitution _⟩

/-- Encoded identity acts as identity on every canonical term. -/
theorem substituteEncoded?_identity
    {arity : Nat} (term : Tower.Tm arity) :
    substituteEncoded? arity
        (encodeSubstitution (ids : Sub Tower.Head arity arity))
        (encodeRawTerm term) = some (encodeRawTerm term) := by
  simp [substituteEncoded?_encode]

/-- Left identity for encoded substitution composition on the canonical
image. -/
theorem composeEncoded?_identity_left
    {source target : Nat} (substitution : Sub Tower.Head source target) :
    composeEncoded? target
        (encodeSubstitution (ids : Sub Tower.Head target target))
        (encodeSubstitution substitution) =
      some (encodeSubstitution substitution) := by
  simp

/-- Right identity for encoded substitution composition on the canonical
image. -/
theorem composeEncoded?_identity_right
    {source target : Nat} (substitution : Sub Tower.Head source target) :
    composeEncoded? target (encodeSubstitution substitution)
        (encodeSubstitution (ids : Sub Tower.Head source source)) =
      some (encodeSubstitution substitution) := by
  simp

/-- Applying an encoded composite equals applying its two components in
sequence on every canonical input. -/
theorem substituteEncoded?_composition
    {source middle target : Nat}
    (later : Sub Tower.Head middle target)
    (earlier : Sub Tower.Head source middle)
    (term : Tower.Tm source) :
    (do
        let composed ← composeEncoded? target
          (encodeSubstitution later) (encodeSubstitution earlier)
        substituteEncoded? target composed (encodeRawTerm term)) =
      (do
        let intermediate ← substituteEncoded? middle
          (encodeSubstitution earlier) (encodeRawTerm term)
        substituteEncoded? target (encodeSubstitution later) intermediate) := by
  simp
  change encodeRawTerm (subst (subComp later earlier) term) =
    encodeRawTerm (subst (subComp later earlier) term)
  rfl

/-- Strong composition law: the two execution orders agree for arbitrary
external vectors and terms, not only values freshly produced by the encoder.
If any input is outside its declared scope both sides fail with `none`; if all
decode, the intrinsic CwF composition law identifies their results. -/
theorem substituteEncoded?_composeEncoded
    {source middle : Nat} (target : Nat)
    (later : EncodedSubstitution middle)
    (earlier : EncodedSubstitution source)
    (term : Pattern) :
    (do
        let composed ← composeEncoded? target later earlier
        substituteEncoded? target composed term) =
      (do
        let intermediate ← substituteEncoded? middle earlier term
        substituteEncoded? target later intermediate) := by
  cases laterDecoded : decodeSubstitution? target later with
  | none =>
      simp [composeEncoded?, substituteEncoded?, laterDecoded]
  | some decodedLater =>
      cases earlierDecoded : decodeSubstitution? middle earlier with
      | none =>
          simp [composeEncoded?, substituteEncoded?, laterDecoded,
            earlierDecoded]
      | some decodedEarlier =>
          cases termDecoded : decodeRawTerm? source term with
          | none =>
              simp [composeEncoded?, substituteEncoded?, laterDecoded,
                earlierDecoded, termDecoded]
          | some decodedTerm =>
              simp [composeEncoded?, substituteEncoded?, laterDecoded,
                earlierDecoded, termDecoded]
              change encodeRawTerm
                  (subst (subComp decodedLater decodedEarlier) decodedTerm) =
                encodeRawTerm
                  (subst (subComp decodedLater decodedEarlier) decodedTerm)
              rfl

/-! ## Order, multiplicity, and scope controls -/

/-- A substitution with two identical components. -/
def duplicateClosedSubstitution : Sub Tower.Head 2 0 :=
  Fin.cases closedArgument (fun _ => closedArgument)

/-- Positive multiplicity control: both duplicate components remain present
and ordered in the boundary carrier. -/
theorem encode_duplicateClosedSubstitution :
    encodeSubstitution duplicateClosedSubstitution =
      .cons (encodeRawTerm closedArgument)
        (.cons (encodeRawTerm closedArgument) .nil) :=
  rfl

/-- An encoded component that is valid at arity one but not at arity zero. -/
def targetScopeMismatch : EncodedSubstitution 1 :=
  .cons (encodeRawTerm openVariable) .nil

/-- Negative scope control: source length alone cannot launder a component
whose target variable is out of scope. -/
theorem targetScopeMismatch_rejected :
    decodeSubstitution? 0 targetScopeMismatch = none := by
  have rejected :
      decodeRawTerm? 0 (encodeRawTerm openVariable) = none :=
    Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwarePatternCodec.outOfScopeVariable_rejected
  simp [targetScopeMismatch, decodeSubstitution?, rejected]

/-- The same mismatch prevents term application; failure does not produce a
fabricated result. -/
theorem targetScopeMismatch_application_rejected :
    substituteEncoded? 0 targetScopeMismatch
      (encodeRawTerm (Tm.var (Head := Tower.Head) (0 : Fin 1))) = none := by
  simp [substituteEncoded?, targetScopeMismatch_rejected]

#print axioms decodeSubstitution?_encodeSubstitution
#print axioms encodeSubstitution_injective
#print axioms substituteEncoded?_encode
#print axioms substituteEncoded?_reflects
#print axioms substituteEncoded?_output_decodes
#print axioms composeEncoded?_encode
#print axioms composeEncoded?_reflects
#print axioms composeEncoded?_output_decodes
#print axioms substituteEncoded?_identity
#print axioms composeEncoded?_identity_left
#print axioms composeEncoded?_identity_right
#print axioms substituteEncoded?_composition
#print axioms substituteEncoded?_composeEncoded
#print axioms encode_duplicateClosedSubstitution
#print axioms targetScopeMismatch_rejected
#print axioms targetScopeMismatch_application_rejected

end RawUnitypedPatternSimultaneousSubstitution
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
