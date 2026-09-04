import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.RawUnitypedErasure
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwareSubstitutionBoundary

/-!
# The boundary between raw unityped terms and MeTTaIL Pattern

The declaration-aware term codec is an exact embedding into MeTTaIL
`Pattern`, but its variables are deliberately encoded as tagged data.  This
module connects that codec to the raw unityped CwF and records the precise
operational consequence:

* canonical encoding is injective and scope-checked;
* typed-term erasure followed by canonical encoding remains injective inside
  each fixed typing fibre;
* intrinsic binder substitution is available through an exact
  decode/substitute/re-encode adapter;
* generic `Pattern` binder substitution does not implement that adapter.

Therefore the exact data codec is a conservative syntax embedding, not a CwF
morphism into the existing generic `Pattern` substitution action.  A final
Prime surface must either expose binders in its chosen view, retain an
authored substitution route, or prove a different contextual comparison.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace RawUnitypedPatternBoundary

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwarePatternCodec
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwareSubstitutionBoundary
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open RawUnitypedErasure
open SyntacticContextual

/-! ## Exact canonical syntax embedding -/

/-- The canonical `Pattern` encoding, restricted to one fibre of the raw
unityped syntax. -/
def encodeRawTerm {arity : Nat} : (rawUcwf Tower.Head).Tm arity → Pattern :=
  encodeTm towerHeadCodec

/-- The corresponding scope-checking partial decoder. -/
def decodeRawTerm? (arity : Nat) : Pattern → Option ((rawUcwf Tower.Head).Tm arity) :=
  decodeTm? towerHeadCodec arity

/-- Every intrinsically scoped raw term round-trips through `Pattern`. -/
@[simp] theorem decodeRawTerm?_encodeRawTerm {arity : Nat}
    (term : (rawUcwf Tower.Head).Tm arity) :
    decodeRawTerm? arity (encodeRawTerm term) = some term :=
  decodeTm?_encodeTm towerHeadCodec term

/-- The canonical embedding loses no raw term distinction. -/
theorem encodeRawTerm_injective (arity : Nat) :
    Function.Injective
      (encodeRawTerm : (rawUcwf Tower.Head).Tm arity → Pattern) :=
  (tmCodec towerHeadCodec arity).encode_injective

/-- A typed occurrence can be embedded by first applying the strict raw
erasure and then the canonical `Pattern` codec. -/
def encodeTypedTerm {rules : Rules Tower.Head}
    {context : FormedContext rules} {type : TypeOver context}
    (term : Term context type) : Pattern :=
  encodeRawTerm term.code

/-- The composite typed-to-raw-to-Pattern map reflects exact raw term syntax
inside every fixed typing fibre. -/
theorem encodeTypedTerm_injective {rules : Rules Tower.Head}
    {context : FormedContext rules} {type : TypeOver context} :
    Function.Injective (encodeTypedTerm (rules := rules) (type := type)) := by
  intro left right equality
  apply RawUnitypedErasure.mapTerm_injective_at_fixed_type rules
  exact encodeRawTerm_injective context.arity equality

/-! ## Exact authored binder adapter -/

/-- Decode canonical data at the declared arities, perform the intrinsic
newest-variable substitution, and re-encode the exact result.

Failure means that at least one input is outside the canonical scoped image;
it is not a refutation of the represented term. -/
def canonicalInstantiate? (ambient : Nat)
    (replacement body : Pattern) : Option Pattern := do
  let replacementTerm ← decodeRawTerm? ambient replacement
  let bodyTerm ← decodeRawTerm? (ambient + 1) body
  pure (encodeRawTerm (inst0 replacementTerm bodyTerm))

/-- The adapter is total and exact on the canonical image. -/
@[simp] theorem canonicalInstantiate?_encode
    {ambient : Nat} (replacement : Tower.Tm ambient)
    (body : Tower.Tm (ambient + 1)) :
    canonicalInstantiate? ambient (encodeRawTerm replacement)
        (encodeRawTerm body) =
      some (encodeRawTerm (inst0 replacement body)) := by
  simp [canonicalInstantiate?, decodeRawTerm?, encodeRawTerm]

/-- An encoded variable that lies outside the declared body arity is rejected
by decoding.  The adapter does not trust an externally supplied arity label. -/
def outOfScopeBody : Pattern :=
  encodeTm towerHeadCodec
    (Tm.var (Head := Tower.Head) (1 : Fin 2))

/-- Negative scope control for the authored adapter. -/
theorem canonicalInstantiate?_rejects_outOfScopeBody :
    canonicalInstantiate? 0
        (encodeRawTerm DeclarationAwareSubstitutionBoundary.closedArgument)
        outOfScopeBody = none := by
  rfl

/-! ## The generic Pattern binder is a different operation -/

/-- On the standard discriminator, the authored adapter returns the intrinsic
opening result. -/
theorem canonicalInstantiate?_openVariable :
    canonicalInstantiate? 0
        (encodeRawTerm DeclarationAwareSubstitutionBoundary.closedArgument)
        (encodeRawTerm DeclarationAwareSubstitutionBoundary.openVariable) =
      some
        (encodeRawTerm
          (inst0 DeclarationAwareSubstitutionBoundary.closedArgument
            DeclarationAwareSubstitutionBoundary.openVariable)) := by
  exact canonicalInstantiate?_encode
    DeclarationAwareSubstitutionBoundary.closedArgument
    DeclarationAwareSubstitutionBoundary.openVariable

/-- Negative operational control: the existing generic `Pattern` binder
operation is not the result selected by the exact canonical adapter.  The
failure is caused by binder opacity, not an encoding collision. -/
theorem genericBinder_not_canonicalAdapterResult :
    instantiateBVar
        (encodeRawTerm DeclarationAwareSubstitutionBoundary.closedArgument)
        (encodeRawTerm DeclarationAwareSubstitutionBoundary.openVariable) ≠
      encodeRawTerm
        (inst0 DeclarationAwareSubstitutionBoundary.closedArgument
          DeclarationAwareSubstitutionBoundary.openVariable) :=
  canonicalData_genericBinder_doesNotCommute

/-- The complete positive/negative receipt: the authored adapter succeeds on
the canonical image, while generic binder instantiation selects a different
pattern. -/
theorem canonicalAdapter_exact_genericBinder_distinct :
    canonicalInstantiate? 0
          (encodeRawTerm DeclarationAwareSubstitutionBoundary.closedArgument)
          (encodeRawTerm DeclarationAwareSubstitutionBoundary.openVariable) =
        some
          (encodeRawTerm
            (inst0 DeclarationAwareSubstitutionBoundary.closedArgument
              DeclarationAwareSubstitutionBoundary.openVariable)) ∧
      instantiateBVar
          (encodeRawTerm DeclarationAwareSubstitutionBoundary.closedArgument)
          (encodeRawTerm DeclarationAwareSubstitutionBoundary.openVariable) ≠
        encodeRawTerm
          (inst0 DeclarationAwareSubstitutionBoundary.closedArgument
            DeclarationAwareSubstitutionBoundary.openVariable) :=
  ⟨canonicalInstantiate?_openVariable,
    genericBinder_not_canonicalAdapterResult⟩

#print axioms decodeRawTerm?_encodeRawTerm
#print axioms encodeRawTerm_injective
#print axioms encodeTypedTerm_injective
#print axioms canonicalInstantiate?_encode
#print axioms canonicalInstantiate?_rejects_outOfScopeBody
#print axioms genericBinder_not_canonicalAdapterResult
#print axioms canonicalAdapter_exact_genericBinder_distinct

end RawUnitypedPatternBoundary
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
