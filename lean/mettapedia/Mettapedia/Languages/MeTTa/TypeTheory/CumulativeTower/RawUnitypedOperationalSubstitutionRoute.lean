import Mettapedia.GSLT.LanguageDef.GSLTILContextualProfileComparison
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.RawUnitypedPatternSimultaneousSubstitution

/-!
# Raw unityped substitution as a represented operational route

Intrinsic simultaneous substitution is total on intrinsically scoped raw
terms.  It therefore determines a companion route in the proof-relevant
GSLT-IL equipment.  Composition of those routes selects exactly the existing
CwF substitution composition.

The Pattern adapter has a different domain.  Decoding can fail outside the
canonical scoped image, so its successful-output relation is partial and is
not a represented contextual substitution on all `Pattern` values.  A total
outcome route is available by retaining `Option Pattern`; its `none` outcome
records non-admission to the image and is not logical refutation.

This separates the deterministic contextual action from its partial external
codec without introducing a second evaluator or declaring a final wire
format.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace RawUnitypedOperationalSubstitutionRoute

open Mettapedia.GSLT.LooseRelationEquipment
open Mettapedia.GSLT.LanguageDef.GSLTIL.ContextualProfileComparison
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwareSubstitutionBoundary
open Mettapedia.OSLF.MeTTaIL.Syntax
open RawUnitypedPatternBoundary
open RawUnitypedPatternSimultaneousSubstitution

/-! ## The intrinsic represented route -/

/-- The total raw-term map selected by one simultaneous substitution. -/
def rawSubstitutionMap {source target : Nat}
    (substitution : Sub Tower.Head source target) :
    Tower.Tm source → Tower.Tm target :=
  fun term => subst substitution term

/-- Intrinsic substitution as the companion of its total raw-term map. -/
def rawSubstitutionRoute {source target : Nat}
    (substitution : Sub Tower.Head source target) :
    Loose (Tower.Tm source) (Tower.Tm target) :=
  substitutionRoute (rawSubstitutionMap substitution)

/-- The canonical proof-relevant representation license. -/
def rawSubstitutionRepresentation {source target : Nat}
    (substitution : Sub Tower.Head source target) :
    Representation (rawSubstitutionRoute substitution) :=
  substitutionRouteRepresentation (rawSubstitutionMap substitution)

/-- The representation selects intrinsic substitution itself. -/
@[simp] theorem rawSubstitutionRepresentation_map
    {source target : Nat}
    (substitution : Sub Tower.Head source target) :
    (rawSubstitutionRepresentation substitution).map =
      rawSubstitutionMap substitution :=
  rfl

/-- Every scoped raw term has its exact intrinsic result and route witness. -/
def rawSubstitutionRouteWitness {source target : Nat}
    (substitution : Sub Tower.Head source target)
    (term : Tower.Tm source) :
    rawSubstitutionRoute substitution term (subst substitution term) :=
  ⟨⟨rfl⟩⟩

/-- The selected map of horizontally composed routes is exactly simultaneous
substitution composition. -/
theorem rawSubstitution_horizontalComp_map
    {source middle target : Nat}
    (later : Sub Tower.Head middle target)
    (earlier : Sub Tower.Head source middle) :
    (Representation.horizontalComp
        (rawSubstitutionRepresentation earlier)
        (rawSubstitutionRepresentation later)).map =
      rawSubstitutionMap (subComp later earlier) := by
  funext term
  exact subst_subComp later earlier term

/-- Identity substitution selects the identity raw-term map. -/
theorem rawSubstitution_identity_map (arity : Nat) :
    rawSubstitutionMap (ids : Sub Tower.Head arity arity) = id := by
  funext term
  exact subst_ids term

/-! ## The encoded boundary commutes on its admitted image -/

/-- The exact Pattern adapter realizes the map selected by the represented
intrinsic route on every canonical input. -/
theorem encodedBoundary_commutes
    {source target : Nat}
    (substitution : Sub Tower.Head source target)
    (term : Tower.Tm source) :
    substituteEncoded? target (encodeSubstitution substitution)
        (encodeRawTerm term) =
      some (encodeRawTerm
        ((rawSubstitutionRepresentation substitution).map term)) := by
  exact substituteEncoded?_encode substitution term

/-- Composition commutes through both the represented route and the encoded
boundary. -/
theorem encodedBoundary_composition_commutes
    {source middle target : Nat}
    (later : Sub Tower.Head middle target)
    (earlier : Sub Tower.Head source middle)
    (term : Tower.Tm source) :
    substituteEncoded? target
        (encodeSubstitution (subComp later earlier))
        (encodeRawTerm term) =
      some (encodeRawTerm
        ((Representation.horizontalComp
          (rawSubstitutionRepresentation earlier)
          (rawSubstitutionRepresentation later)).map term)) := by
  rw [rawSubstitution_horizontalComp_map]
  exact substituteEncoded?_encode (subComp later earlier) term

/-! ## Partial success versus total outcomes -/

/-- The proof-relevant relation of successful external substitution.  It is
partial because arbitrary Patterns need not decode into the declared image. -/
def encodedSuccessRoute {source : Nat} (target : Nat)
    (substitution : EncodedSubstitution source) : Loose Pattern Pattern :=
  fun input output =>
    EqWitness (substituteEncoded? target substitution input) (some output)

/-- The total outcome map retains codec failure as `none`. -/
def encodedOutcomeRoute {source : Nat} (target : Nat)
    (substitution : EncodedSubstitution source) :
    Loose Pattern (Option Pattern) :=
  companion (substituteEncoded? target substitution)

/-- Retaining the optional outcome yields a represented route on all Pattern
inputs. -/
def encodedOutcomeRepresentation {source : Nat} (target : Nat)
    (substitution : EncodedSubstitution source) :
    Representation (encodedOutcomeRoute target substitution) :=
  Representation.companionSelf (substituteEncoded? target substitution)

/-- A canonical term produces a witness in the successful-output route. -/
def canonicalInput_has_successWitness
    {source target : Nat}
    (substitution : Sub Tower.Head source target)
    (term : Tower.Tm source) :
    encodedSuccessRoute target (encodeSubstitution substitution)
      (encodeRawTerm term) (encodeRawTerm (subst substitution term)) :=
  ⟨⟨substituteEncoded?_encode substitution term⟩⟩

/-- Even an intrinsically valid substitution is partial on the whole Pattern
carrier: a noncanonical external value has no successful output. -/
theorem noncanonicalInput_has_no_successOutput
    (output : Pattern) :
    ¬ Nonempty
      (encodedSuccessRoute 0
        (encodeSubstitution (ids : Sub Tower.Head 0 0))
        (.fvar "outside-canonical-term-image") output) := by
  rintro ⟨witness⟩
  have impossible :
      substituteEncoded? 0
          (encodeSubstitution (ids : Sub Tower.Head 0 0))
          (.fvar "outside-canonical-term-image") = some output :=
    witness.down.down
  simp [substituteEncoded?, decodeRawTerm?,
    Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwarePatternCodec.decodeTm?]
    at impossible

/-- Negative non-collapse control: the partial successful-output relation on
all Patterns cannot be licensed as a represented contextual substitution. -/
theorem encodedSuccessRoute_not_representable :
    ¬ Nonempty
      (Representation
        (encodedSuccessRoute 0
          (encodeSubstitution (ids : Sub Tower.Head 0 0)))) := by
  rintro ⟨representation⟩
  obtain ⟨⟨output, witness⟩⟩ :=
    representation.total (.fvar "outside-canonical-term-image")
  exact noncanonicalInput_has_no_successOutput output ⟨witness⟩

/-- The totalized outcome route returns `none` on the same input.  This is a
retained outcome value, not a proof of object-language falsehood. -/
theorem noncanonicalInput_outcome_is_none :
    (encodedOutcomeRepresentation 0
      (encodeSubstitution (ids : Sub Tower.Head 0 0))).map
        (.fvar "outside-canonical-term-image") = none := by
  rfl

#print axioms rawSubstitutionRepresentation
#print axioms rawSubstitutionRouteWitness
#print axioms rawSubstitution_horizontalComp_map
#print axioms rawSubstitution_identity_map
#print axioms encodedBoundary_commutes
#print axioms encodedBoundary_composition_commutes
#print axioms canonicalInput_has_successWitness
#print axioms noncanonicalInput_has_no_successOutput
#print axioms encodedSuccessRoute_not_representable
#print axioms noncanonicalInput_outcome_is_none

end RawUnitypedOperationalSubstitutionRoute
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
