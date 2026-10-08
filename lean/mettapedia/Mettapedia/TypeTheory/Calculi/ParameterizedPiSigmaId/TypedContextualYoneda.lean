import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedContextualCwf
import Mettapedia.TypeTheory.CwfYonedaCoherence

/-!
# Native presheaf interpretation of typed dependent classes

The actual typed context category supplies the native context presheaves.
A formed type is interpreted by the fibres of its represented display map,
and a supplied typed term becomes a natural section. Equality of these
sections is exactly the heterogeneous typed relation on supplied terms;
certificate and annotation choices cannot change that section.

Every fibre and every natural section of a represented type has an actually
admitted typed representative. Substitution uses the canonical comprehension
comparison and recovers the substituted class. These are properties of the
represented image, not arbitrary-model interpretation or a classifying
universal property. No additional type-former preservation is asserted.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedContextual.NativePresheaf

open _root_.CategoryTheory Opposite
open TypedEquality TypedEquality.Normalization
open Mettapedia.TypeTheory.DisplayedPresheafTransport

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
variable (levels : LevelModel rules L)

abbrev context (source : Context rules) := (quotientProjection rules).obj source

noncomputable abbrev family {source : Context rules} (type : QType levels source) :=
  CwfYoneda.family (QuotientCwf.cwf levels) (Γ := context source) type

/-- Admit the supplied typed subject at its quotient type without replacing
its code by a semantic value or an untyped representative. -/
def suppliedAt {source : Context rules} {type : TypeOver source}
    (term : Term source type) {target : QType levels source}
    (atType : QType.mk levels type = target) :
    QuotientCwf.Tm levels (context source) target := ⟨QTerm.mk levels term, atType⟩

def supplied {source : Context rules} {type : TypeOver source}
    (term : Term source type) : QuotientCwf.Tm levels (context source) (QType.mk levels type) :=
  suppliedAt levels term rfl

noncomputable def nativeSectionAt {source : Context rules} {type : TypeOver source}
    (term : Term source type) {target : QType levels source}
    (atType : QType.mk levels type = target) : (family levels target).sections :=
  CwfYoneda.interpretTerm (QuotientCwf.cwf levels) (suppliedAt levels term atType)

noncomputable def nativeSection {source : Context rules} {type : TypeOver source}
    (term : Term source type) : (family levels (QType.mk levels type)).sections :=
  nativeSectionAt levels term rfl

/-- The native interpretation reflects, as well as preserves, the actual
typed equations on subjects and their independently supplied annotations. -/
theorem nativeSectionAt_eq_iff {source : Context rules} {first second : TypeOver source}
    (left : Term source first) (right : Term source second) {target : QType levels source}
    (leftAt : QType.mk levels first = target) (rightAt : QType.mk levels second = target) :
    nativeSectionAt levels left leftAt = nativeSectionAt levels right rightAt ↔
      TypeEq rules source.raw first.code second.code ∧
        Equal rules source.raw left.code right.code first.code := by
  constructor
  · intro same
    have suppliedSame := (CwfYoneda.termSectionEquiv (QuotientCwf.cwf levels) target).injective same
    exact (QTerm.mk_eq_iff levels left right).mp (congrArg Subtype.val suppliedSame)
  · intro same
    apply congrArg (CwfYoneda.interpretTerm (QuotientCwf.cwf levels))
    apply Subtype.ext
    exact (QTerm.mk_eq_iff levels left right).mpr same

theorem section_eq_iff {source : Context rules} {type : TypeOver source}
    (left right : Term source type) :
    nativeSection levels left = nativeSection levels right ↔
      Equal rules source.raw left.code right.code type.code := by
  rw [nativeSection, nativeSection, nativeSectionAt_eq_iff]
  exact and_iff_right type.isType.refl

/-- Formation and typing witnesses with one supplied subject code have the
same native section, even when their raw type annotations differ. -/
theorem nativeSectionAt_same_code {source : Context rules} {first second : TypeOver source}
    (left : Term source first) (right : Term source second) {target : QType levels source}
    (leftAt : QType.mk levels first = target) (rightAt : QType.mk levels second = target)
    (sameCode : left.code = right.code) :
    nativeSectionAt levels left leftAt = nativeSectionAt levels right rightAt := by
  apply (nativeSectionAt_eq_iff levels left right leftAt rightAt).mpr
  refine ⟨(QType.mk_eq_iff levels first second).mp (leftAt.trans rightAt.symm), ?_⟩
  rw [← sameCode]
  exact .refl left.typed

/-- Actual typed conversion changes the admission annotation while retaining
the natural native certificate at the original type class. -/
theorem section_convertType {source : Context rules} {first : TypeOver source}
    (term : Term source first) (second : TypeOver source)
    (same : TypeEq rules source.raw first.code second.code) :
    nativeSectionAt levels (term.convertType second same)
        ((QType.mk_eq_iff levels second first).mpr same.symm) = nativeSection levels term :=
  nativeSectionAt_same_code levels (term.convertType second same) term _ rfl rfl

/-- Pulling the natural section back along a supplied admitted substitution
agrees with substitution into the original syntax and its type annotation. -/
theorem section_reindex {source target : Context rules} {type : TypeOver target}
    (term : Term target type) (morphism : source ⟶ target) :
    nativeSection levels (term.reindex morphism) =
      CwfYoneda.substituteSection (QuotientCwf.cwf levels) (QuotientCwf.project morphism)
        (nativeSection levels term) := by
  exact (CwfYoneda.substituteSection_interpret (QuotientCwf.cwf levels)
    (QuotientCwf.project morphism) (supplied levels term)).symm

/-- At each actual contextual point, decoding the emitted native fibre
recovers precisely the substituted typed subject class. -/
theorem section_readout {source target : Context rules} {type : TypeOver target}
    (term : Term target type) (morphism : source ⟶ target) :
    (CwfYoneda.decodeTerm (QuotientCwf.cwf levels) (QType.mk levels type)
      (QuotientCwf.project morphism)
      ((nativeSection levels term).val
        ⟨op (CwfYoneda.context (QuotientCwf.cwf levels) (context source)),
          QuotientCwf.project morphism⟩)).val = QTerm.mk levels (term.reindex morphism) := by
  exact congrArg Subtype.val (CwfYoneda.decode_encode (QuotientCwf.cwf levels)
    (QType.mk levels type) (QuotientCwf.project morphism)
    ((QuotientCwf.cwf levels).tmSub (supplied levels term) (QuotientCwf.project morphism)))

/-- An arbitrary native fibre of this represented type has a typed syntax
representative at the actual supplied substituted annotation. -/
theorem fibre_has_typed_representative {source target : Context rules}
    (type : TypeOver target) (morphism : source ⟶ target)
    (receipt : (family levels (QType.mk levels type)).obj
      ⟨op (CwfYoneda.context (QuotientCwf.cwf levels) (context source)),
        QuotientCwf.project morphism⟩) :
    ∃ term : Term source (type.reindex morphism),
      CwfYoneda.encodeTerm (QuotientCwf.cwf levels) (QType.mk levels type)
          (QuotientCwf.project morphism) (supplied levels term) = receipt := by
  let decoded := CwfYoneda.decodeTerm (QuotientCwf.cwf levels) (QType.mk levels type)
    (QuotientCwf.project morphism) receipt
  let term := QuotientCwf.termRepresentative (type.reindex morphism) decoded.val decoded.property
  have suppliedSame : supplied levels term = decoded :=
    Subtype.ext (QuotientCwf.termRepresentative_class (type.reindex morphism) decoded.val decoded.property)
  refine ⟨term, ?_⟩
  exact (congrArg (CwfYoneda.encodeTerm (QuotientCwf.cwf levels) (QType.mk levels type)
    (QuotientCwf.project morphism)) suppliedSame).trans
      (CwfYoneda.encode_decode (QuotientCwf.cwf levels) (QType.mk levels type)
        (QuotientCwf.project morphism) receipt)

/-- All natural sections of the represented family, including independently
supplied ones, come from genuinely typed syntax at the supplied annotation. -/
theorem section_has_typed_representative {source : Context rules} (type : TypeOver source)
    (certificate : (family levels (QType.mk levels type)).sections) :
    ∃ term : Term source type, nativeSection levels term = certificate := by
  let decoded := CwfYoneda.recoverTerm (QuotientCwf.cwf levels) certificate
  let term := QuotientCwf.termRepresentative type decoded.val decoded.property
  have suppliedSame : supplied levels term = decoded :=
    Subtype.ext (QuotientCwf.termRepresentative_class type decoded.val decoded.property)
  refine ⟨term, ?_⟩
  change CwfYoneda.interpretTerm (QuotientCwf.cwf levels) (supplied levels term) = certificate
  exact (congrArg (CwfYoneda.interpretTerm (QuotientCwf.cwf levels)) suppliedSame).trans
    (CwfYoneda.interpret_recover (QuotientCwf.cwf levels) certificate)

end TypedContextual.NativePresheaf
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
