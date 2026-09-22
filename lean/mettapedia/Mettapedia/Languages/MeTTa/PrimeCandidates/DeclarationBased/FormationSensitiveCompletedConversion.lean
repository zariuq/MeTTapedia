import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveCompletedRelatorPreservation
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeRelatorCompatibility

/-!
# Entirely formed conversion in the completed native relation

On terms admitted at the same displayed type, authored conversion is exactly
the equivalence closure of completed parallel development between admitted
states. Every intermediate in the latter relation carries the actual refined
judgment, including its formed context. The converse follows through a typed
common reduct, without subject expansion.

This changes neither authored execution nor its certificates. It reconstructs
the existence of a formed completed path, not a literal lift of every supplied
raw receipt or preservation of its route identity. The auxiliary parallel
relation need not be one authored runtime step. No normalization, decision
procedure for conversion search, or full semantic model is asserted.
-/

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace FormationSensitiveCompletedConversion

open Presentation Presentation.Declaration Presentation.FormationSensitive
open NativeRelatorConversionParallel
open FormationSensitiveCompletedRelatorPreservation

variable {signature : Signature Tower.Head} {n m : Nat}

/-- A native term at its actual refined displayed judgment. -/
abbrev Admitted (signature : Signature Tower.Head) (context : Tower.Ctx n)
    (type : Tower.Tm n) :=
  { term : Tower.Tm n // Judgment (OpaqueRelatorExtension.rules signature) context term type }

/-- Parallel development has the same syntax; only its endpoint carrier is
restricted here. Intermediate admission is supplied by subject reduction. -/
def Development {context : Tower.Ctx n} {type : Tower.Tm n}
    (left right : Admitted signature context type) : Prop := Par left.val right.val

def Conversion {context : Tower.Ctx n} {type : Tower.Tm n}
    (left right : Admitted signature context type) : Prop :=
  Relation.EqvGen Development left right

theorem conversion_sound (opac : OpaqueRelatorExtension.Opacity signature)
    {context : Tower.Ctx n} {type : Tower.Tm n}
    {left right : Admitted signature context type} (converted : Conversion left right) :
    Conv (OpaqueRelatorExtension.rules signature).headEq left.val right.val
      (OpaqueRelatorExtension.rules signature).computation := by
  induction converted with
  | rel _ _ developed => exact (OpaqueRelatorExtension.conversion_iff opac).mpr developed.sound
  | refl _ => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ first second => exact .trans _ _ _ first second

/-- Every intermediate on a finite forward development inherits the original
displayed type; no reversed step has to manufacture formation. -/
theorem development_path (opac : OpaqueRelatorExtension.Opacity signature)
    {context : Tower.Ctx n} {type : Tower.Tm n}
    (left right : Admitted signature context type) (path : ParStar left.val right.val) :
    Relation.ReflTransGen Development left right := by
  have liftPath {source target : Tower.Tm n} (steps : ParStar source target) :
      ∀ (sourceTyped : Judgment (OpaqueRelatorExtension.rules signature) context source type)
        (targetTyped : Judgment (OpaqueRelatorExtension.rules signature) context target type),
        Relation.ReflTransGen Development
          (⟨source, sourceTyped⟩ : Admitted signature context type) ⟨target, targetTyped⟩ := by
    induction steps with
    | refl => intro sourceTyped targetTyped; exact .refl
    | @tail middle target earlier last ih =>
        intro sourceTyped targetTyped
        have middleTyped := parallel_steps_preserve opac sourceTyped earlier
        exact .tail (ih sourceTyped middleTyped) last
  exact liftPath path left.property right.property

theorem conversion_of_development_path {context : Tower.Ctx n} {type : Tower.Tm n}
    {left right : Admitted signature context type}
    (path : Relation.ReflTransGen Development left right) : Conversion left right := by
  induction path with
  | refl => exact .refl _
  | tail _ step ih => exact .trans _ _ _ ih (.rel _ _ step)

/-- Authored conversion can be represented by a wholly formed completed
path. The original raw path is not claimed to have formed intermediates. -/
theorem conversion_complete (opac : OpaqueRelatorExtension.Opacity signature)
    {context : Tower.Ctx n} {type : Tower.Tm n}
    (left right : Admitted signature context type)
    (converted : Conv (OpaqueRelatorExtension.rules signature).headEq left.val right.val
      (OpaqueRelatorExtension.rules signature).computation) : Conversion left right := by
  obtain ⟨common, first, second, commonTyped, _⟩ :=
    conversion_typed_join opac left.property right.property converted
  let middle : Admitted signature context type := ⟨common, commonTyped⟩
  exact .trans _ _ _
    (conversion_of_development_path (development_path opac left middle first))
    (.symm _ _ (conversion_of_development_path (development_path opac right middle second)))

theorem conversion_iff (opac : OpaqueRelatorExtension.Opacity signature)
    {context : Tower.Ctx n} {type : Tower.Tm n}
    (left right : Admitted signature context type) :
    Conversion left right ↔
      Conv (OpaqueRelatorExtension.rules signature).headEq left.val right.val
        (OpaqueRelatorExtension.rules signature).computation :=
  ⟨conversion_sound opac, conversion_complete opac left right⟩

/-- The unchanged native certificate checker recognizes existence of this
formed completed conversion when the endpoints are independently admitted.
It does not itself check those endpoint judgments. -/
theorem conversion_iff_checked (opac : OpaqueRelatorExtension.Opacity signature)
    {context : Tower.Ctx n} {type : Tower.Tm n}
    (left right : Admitted signature context type) :
    Conversion left right ↔
      ∃ code, NativeRelatorConversionChecking.check code left.val right.val = true :=
  (conversion_iff opac left right).trans (OpaqueRelatorExtension.checked_conversion_iff opac)

/-- Substitution acts on the actual native term and refined judgment, not on
a separately reconstructed pure syntax. -/
def substitute {context : Tower.Ctx n} {target : Tower.Ctx m} {type : Tower.Tm n}
    {sigma : Sub Tower.Head n m}
    (formed : ContextFormation (OpaqueRelatorExtension.rules signature) target)
    (typed : Presentation.FormationSensitive.CtxMor
      (OpaqueRelatorExtension.rules signature) context target sigma)
    (term : Admitted signature context type) : Admitted signature target (subst sigma type) :=
  ⟨subst sigma term.val, term.property.substitute formed typed⟩

theorem conversion_substitute (opac : OpaqueRelatorExtension.Opacity signature)
    {context : Tower.Ctx n} {target : Tower.Ctx m} {type : Tower.Tm n}
    {sigma : Sub Tower.Head n m}
    (formed : ContextFormation (OpaqueRelatorExtension.rules signature) target)
    (typed : Presentation.FormationSensitive.CtxMor
      (OpaqueRelatorExtension.rules signature) context target sigma)
    {left right : Admitted signature context type} (converted : Conversion left right) :
    Conversion (substitute formed typed left) (substitute formed typed right) :=
  conversion_complete opac _ _ ((conversion_sound opac converted).substitute sigma)

/-! ## Controls in the actual mixed declaration environment -/

namespace Controls

open HOLNativeRelatorCompatibility

/-- This source combines a native list of represented HOL sequences with
real wire data. Its projection is a non-reflexive formed conversion. -/
theorem mixed_projection (wire : NativeWireData.Wire) :
    ∃ (source target : Admitted HOLNativeRelatorCompatibility.signature
      .nil NativeWireData.dataType),
      source.val = .snd (mixedPayload wire) ∧ target.val = NativeWireData.encode wire ∧
      Conversion source target := by
  let source : Admitted HOLNativeRelatorCompatibility.signature .nil NativeWireData.dataType :=
    ⟨.snd (mixedPayload wire), ⟨.nil, Typing.sndElim (mixed_payload_typed .nil wire)⟩⟩
  let target : Admitted HOLNativeRelatorCompatibility.signature .nil NativeWireData.dataType :=
    ⟨NativeWireData.encode wire, mixed_projection_admitted wire⟩
  refine ⟨source, target, rfl, rfl, ?_⟩
  exact conversion_complete opacity source target
    (.rel _ _ (.betaSigmaSnd holSequenceSingleton (NativeWireData.encode wire)))

def missingName : DeclName := `CompletedConversionBoundary.undeclared

theorem missing_not_admitted (type : Tower.Tm 0) :
    ¬ Judgment rules .nil (.const missingName) type := by
  intro admitted
  obtain ⟨declaredType, sortHead, known, _, _⟩ := admitted.typing.constFormation
  have absent : rules.constantType missingName = none := by decide
  rw [absent] at known
  cases known

/-- Reflexive raw conversion has a valid finite certificate even for a
missing declaration. It cannot create a point in the admitted carrier. -/
theorem checked_conversion_does_not_supply_admission :
    (∃ code, NativeRelatorConversionChecking.check code
      (.const missingName : Tower.Tm 0) (.const missingName) = true) ∧
      ¬ ∃ type : Tower.Tm 0, Judgment rules .nil (.const missingName) type := by
  refine ⟨(OpaqueRelatorExtension.checked_conversion_iff opacity).mp (.refl _), ?_⟩
  rintro ⟨type, admitted⟩
  exact missing_not_admitted type admitted

end Controls

#print axioms conversion_sound
#print axioms development_path
#print axioms conversion_complete
#print axioms conversion_iff
#print axioms conversion_iff_checked
#print axioms conversion_substitute
#print axioms Controls.mixed_projection
#print axioms Controls.checked_conversion_does_not_supply_admission

end FormationSensitiveCompletedConversion
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
