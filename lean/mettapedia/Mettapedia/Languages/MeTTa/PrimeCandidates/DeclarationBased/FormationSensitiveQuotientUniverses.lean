import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveQuotientCwf
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeQuotientCwfControls
import Mettapedia.TypeTheory.CwfTarskiUniverseHierarchy

/-!
# Native universe codes in the formed conversion-class model

The universe carrier, its codes, and decoding use the same native formed
syntax as the contextual model. A code is an admitted term at an actual
universe annotation, not an arbitrary raw expression. Decoding respects
conversion, and native cumulativity changes its universe admission without
changing the decoded type. These operations commute with actual typed
substitution and its quotient.

This is a syntactic Tarski hierarchy. It is neither a set-theoretic model
nor a comparison with a Hofmann--Streicher presheaf universe. In particular,
its construction does not settle consistency strength or a runtime policy
for observing codes.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace FormationSensitiveContextual.QuotientUniverses

open _root_.CategoryTheory FormationSensitive
open Mettapedia.TypeTheory.CwfTarskiUniverseHierarchy
open QuotientCwf

noncomputable section

variable {signature : Declaration.Signature Tower.Head}

abbrev NativeContext (signature : Declaration.Signature Tower.Head) :=
  QContext (OpaqueRelatorExtension.rules signature)

/-- The native universe has its next universe as its formed annotation. -/
def universeType (context : Context (OpaqueRelatorExtension.rules signature))
    (level : LevelExpr Nat) : TypeOver context where
  code := sortTm level
  level := .sort (.succ level)
  universeWitness := .sort _
  formed := .headType (.sort level)

def univ (context : NativeContext signature) (level : LevelExpr Nat) : Ty context :=
  QType.mk (universeType context.as level)

abbrev Code (context : NativeContext signature) (level : LevelExpr Nat) :=
  QuotientCwf.Tm context (univ context level)

def rawCode {context : NativeContext signature} {level : LevelExpr Nat}
    (code : Code context level) : Term context.as (universeType context.as level) :=
  termRepresentative (universeType context.as level) code.val code.property

theorem rawCode_class {context : NativeContext signature} {level : LevelExpr Nat}
    (code : Code context level) : QTerm.mk (rawCode code) = code.val :=
  termRepresentative_class _ code.val code.property

/-- Native admission of a universe term is the formation proof of its
decoded type. No evaluation or proposition-truth test is substituted for it. -/
def decodedType {context : Context (OpaqueRelatorExtension.rules signature)}
    {level : LevelExpr Nat} (code : Term context (universeType context level)) :
    TypeOver context where
  code := code.code
  level := .sort level
  universeWitness := .sort level
  formed := code.typed

def decode {context : NativeContext signature} {level : LevelExpr Nat}
    (code : Code context level) : Ty context := QType.mk (decodedType (rawCode code))

/-- Decoding is independent of the selected admitted representative. -/
theorem decode_representative {context : NativeContext signature} {level : LevelExpr Nat}
    (code : Code context level) (raw : Term context.as (universeType context.as level))
    (same : QTerm.mk raw = code.val) : decode code = QType.mk (decodedType raw) := by
  apply (QType.mk_eq_iff _ _).mpr
  exact ((QTerm.mk_eq_iff (rawCode code) raw).mp
    ((rawCode_class code).trans same.symm)).2

def ofFormed {context : NativeContext signature} (level : LevelExpr Nat)
    (type : Tower.Tm context.as.arity)
    (formed : Typing (OpaqueRelatorExtension.rules signature) context.as.raw type (sortTm level)) :
    Code context level := ⟨QTerm.mk (⟨type, formed⟩ : Term context.as (universeType context.as level)), rfl⟩

theorem decode_ofFormed {context : NativeContext signature} (level : LevelExpr Nat)
    (type : Tower.Tm context.as.arity)
    (formed : Typing (OpaqueRelatorExtension.rules signature) context.as.raw type (sortTm level)) :
    decode (ofFormed level type formed) =
      QType.mk (⟨type, .sort level, .sort level, formed⟩ : TypeOver context.as) :=
  decode_representative _ ⟨type, formed⟩ rfl

/-- Every admitted type at a specified universe is represented by an actual
code in that universe. The level witness is not guessed from a quotient. -/
theorem code_coverage {context : NativeContext signature} {level : LevelExpr Nat}
    (type : TypeOver context.as) (atLevel : type.level = .sort level) :
    ∃ code : Code context level, decode code = QType.mk type := by
  have formed : Typing (OpaqueRelatorExtension.rules signature) context.as.raw
      type.code (sortTm level) := by
    have original := type.formed
    rw [atLevel] at original
    exact original
  refine ⟨ofFormed level type.code formed, ?_⟩
  exact (decode_ofFormed level type.code formed).trans
    ((QType.mk_eq_iff _ _).mpr (.refl _))

/-- Code coverage is exactly membership at the requested level; mere
membership somewhere in the hierarchy does not supply that admission. -/
theorem code_exists_iff_atUniverse {context : NativeContext signature}
    (level : LevelExpr Nat) (type : Ty context) :
    (∃ code : Code context level, decode code = type) ↔ type.AtUniverse (.sort level) := by
  constructor
  · rintro ⟨code, rfl⟩
    exact ⟨decodedType (rawCode code), rfl, rfl⟩
  · rintro ⟨formed, same, atLevel⟩
    obtain ⟨code, decoded⟩ := code_coverage formed atLevel
    exact ⟨code, decoded.trans same⟩

theorem every_type_has_code {context : NativeContext signature} (type : Ty context) :
    ∃ level, ∃ code : Code context level, decode code = type := by
  let formed := typeRepresentative type
  have levelShape : ∀ {head : Tower.Head}, Tower.IsUniverse head → ∃ level, head = .sort level := by
    intro head member
    cases member with
    | sort level => exact ⟨level, rfl⟩
  obtain ⟨level, atLevel⟩ := levelShape formed.universeWitness
  obtain ⟨code, decoded⟩ := code_coverage formed atLevel
  exact ⟨level, code, decoded.trans (typeRepresentative_class type)⟩

/-- Within a fixed universe, decoding reflects this model's authored code
conversion. This is not an injectivity claim about every semantic model. -/
theorem decode_injective {context : NativeContext signature} {level : LevelExpr Nat} :
    Function.Injective (@decode signature context level) := by
  intro first second same
  have converted := (QType.mk_eq_iff _ _).mp same
  have codeSame : QTerm.mk (rawCode first) = QTerm.mk (rawCode second) :=
    (QTerm.mk_eq_iff _ _).mpr ⟨.refl _, converted⟩
  exact Subtype.ext ((rawCode_class first).symm.trans
    (codeSame.trans (rawCode_class second)))

theorem formed_codes_equal_iff {context : NativeContext signature} {level : LevelExpr Nat}
    {first second : Tower.Tm context.as.arity}
    (firstFormed : Typing (OpaqueRelatorExtension.rules signature) context.as.raw first (sortTm level))
    (secondFormed : Typing (OpaqueRelatorExtension.rules signature) context.as.raw second (sortTm level)) :
    ofFormed level first firstFormed = ofFormed level second secondFormed ↔
      Conv (OpaqueRelatorExtension.rules signature).headEq first second
        (OpaqueRelatorExtension.rules signature).computation := by
  constructor
  · intro same
    exact ((QTerm.mk_eq_iff _ _).mp (congrArg Subtype.val same)).2
  · intro converted
    exact Subtype.ext ((QTerm.mk_eq_iff _ _).mpr ⟨.refl _, converted⟩)

def hierarchy (signature : Declaration.Signature Tower.Head) :
    TarskiUniverseFamily (LevelExpr Nat) (cwf (OpaqueRelatorExtension.rules signature)) where
  univ := univ
  el := decode

theorem universeType_reindex {source target : Context (OpaqueRelatorExtension.rules signature)}
    (level : LevelExpr Nat) (morphism : source ⟶ target) :
    (universeType target level).reindex morphism = universeType source level := rfl

theorem univ_sub {source target : NativeContext signature} (level : LevelExpr Nat)
    (morphism : source ⟶ target) : tySub (univ target level) morphism = univ source level := by
  induction morphism using Quot.inductionOn with
  | h raw => rfl

/-- Reindex the code through the same typed contextual action as all terms. -/
def reindex {source target : NativeContext signature} {level : LevelExpr Nat}
    (code : Code target level) (morphism : source ⟶ target) : Code source level :=
  ⟨totalSub code.val morphism, (totalSub_type code.val morphism).trans
    ((congrArg (fun type => tySub type morphism) code.property).trans (univ_sub level morphism))⟩

theorem reindex_class {source target : NativeContext signature} {level : LevelExpr Nat}
    (code : Code target level) (morphism : source ⟶ target) :
    (reindex code morphism).val = totalSub code.val morphism := rfl

theorem decode_sub {source target : NativeContext signature} {level : LevelExpr Nat}
    (code : Code target level) (morphism : source ⟶ target) :
    decode (reindex code morphism) = tySub (decode code) morphism := by
  induction morphism using Quot.inductionOn with
  | h raw =>
    let representative : Term source.as (universeType source.as level) := (rawCode code).reindex raw
    have represented : QTerm.mk representative = (reindex code (project raw)).val :=
      congrArg (fun term : QTerm target.as => term.reindex raw) (rawCode_class code)
    exact decode_representative _ representative represented

theorem castTm_val {context : NativeContext signature} {first second : Ty context}
    (same : first = second) (term : QuotientCwf.Tm context first) :
    (TarskiUniverseFamily.castTm (C := cwf (OpaqueRelatorExtension.rules signature))
      same term).val = term.val := by
  cases same
  rfl

theorem substitutionStable (signature : Declaration.Signature Tower.Head) :
    (hierarchy signature).SubstitutionStable where
  univ_sub := univ_sub
  el_sub := by
    intro source target level code morphism
    have castSame : TarskiUniverseFamily.castTm (C := cwf (OpaqueRelatorExtension.rules signature))
        (univ_sub level morphism)
        (tmSub code morphism) = reindex code morphism := by
      apply Subtype.ext
      exact castTm_val (univ_sub level morphism) (tmSub code morphism)
    exact (congrArg decode castSame).trans (decode_sub code morphism)

/-- This is the authored semantic order on level expressions, not a
runtime budget or a new universe axiom. -/
def Below (lower upper : LevelExpr Nat) : Prop :=
  Tower.Cumulative (.sort lower) (.sort upper)

def liftCode {context : NativeContext signature} {lower upper : LevelExpr Nat}
    (below : Below lower upper) (code : Code context lower) : Code context upper :=
  ofFormed upper (rawCode code).code (.cumul (rawCode code).typed below)

theorem decode_liftCode {context : NativeContext signature} {lower upper : LevelExpr Nat}
    (below : Below lower upper) (code : Code context lower) :
    decode (liftCode below code) = decode code := by
  exact (decode_ofFormed upper (rawCode code).code (.cumul (rawCode code).typed below)).trans
    ((QType.mk_eq_iff _ _).mpr (.refl _))

def cumulative (signature : Declaration.Signature Tower.Head) :
    (hierarchy signature).StrictlyCumulative Below where
  liftCode := by
    intro lower upper below context code
    exact liftCode below code
  el_liftCode := by
    intro lower upper below context code
    exact decode_liftCode below code

/-- The next universe contains a code for the current native universe. -/
def sortCode (context : NativeContext signature) (level : LevelExpr Nat) :
    Code context (.succ level) := ofFormed (.succ level) (sortTm level) (.headType (.sort level))

theorem decode_sortCode (context : NativeContext signature) (level : LevelExpr Nat) :
    decode (sortCode context level) = univ context level :=
  decode_ofFormed (.succ level) (sortTm level) (.headType (.sort level))

theorem lift_sub {source target : NativeContext signature} {lower upper : LevelExpr Nat}
    (below : Below lower upper) (code : Code target lower) (morphism : source ⟶ target) :
    reindex (liftCode below code) morphism = liftCode below (reindex code morphism) := by
  apply decode_injective
  rw [decode_sub, decode_liftCode, decode_liftCode, decode_sub]

theorem sort_sub {source target : NativeContext signature} (level : LevelExpr Nat)
    (morphism : source ⟶ target) :
    reindex (sortCode target level) morphism = sortCode source level := by
  apply decode_injective
  rw [decode_sub, decode_sortCode, decode_sortCode, univ_sub]

theorem reindex_id {context : NativeContext signature} {level : LevelExpr Nat}
    (code : Code context level) : reindex code (𝟙 context) = code := by
  apply Subtype.ext
  exact totalSub_id code.val

theorem reindex_comp {first middle last : NativeContext signature} {level : LevelExpr Nat}
    (code : Code last level) (earlier : first ⟶ middle) (later : middle ⟶ last) :
    reindex code (earlier ≫ later) = reindex (reindex code later) earlier := by
  apply Subtype.ext
  exact totalSub_comp code.val earlier later

theorem lift_refl {context : NativeContext signature} {level : LevelExpr Nat}
    (below : Below level level) (code : Code context level) : liftCode below code = code :=
  decode_injective (decode_liftCode below code)

theorem lift_trans {context : NativeContext signature} {first middle last : LevelExpr Nat}
    (earlier : Below first middle) (later : Below middle last)
    (composed : Below first last) (code : Code context first) :
    liftCode later (liftCode earlier code) = liftCode composed code := by
  apply decode_injective
  rw [decode_liftCode, decode_liftCode, decode_liftCode]

/-- Raising an admitted code is lossless at the selected conversion-class
view. This does not reconstruct its finer raw syntax or proof provenance. -/
theorem lift_injective {context : NativeContext signature} {lower upper : LevelExpr Nat}
    (below : Below lower upper) : Function.Injective (@liftCode signature context lower upper below) := by
  intro first second same
  apply decode_injective
  exact (decode_liftCode below first).symm.trans
    ((congrArg decode same).trans (decode_liftCode below second))

/-- A downward move exists exactly when the decoded type is admitted at
the requested smaller universe. An upper-level code alone does not supply
the missing lower-level formation evidence. -/
theorem descends_iff_atUniverse {context : NativeContext signature} {lower upper : LevelExpr Nat}
    (below : Below lower upper) (code : Code context upper) :
    (∃ lowerCode : Code context lower, liftCode below lowerCode = code) ↔
      (decode code).AtUniverse (.sort lower) := by
  constructor
  · rintro ⟨lowerCode, rfl⟩
    apply (code_exists_iff_atUniverse lower _).mp
    exact ⟨lowerCode, (decode_liftCode below lowerCode).symm⟩
  · intro admitted
    obtain ⟨lowerCode, same⟩ := (code_exists_iff_atUniverse lower (decode code)).mpr admitted
    exact ⟨lowerCode, decode_injective ((decode_liftCode below lowerCode).trans same)⟩

private theorem parallel_sort_meaning {n : Nat} {level : LevelExpr Nat} {target : Tower.Tm n}
    (steps : NativeRelatorConversionParallel.ParStar (sortTm level) target) :
    ∃ finalLevel, target = sortTm finalLevel ∧
      ∀ valuation, LevelExpr.eval valuation finalLevel = LevelExpr.eval valuation level := by
  induction steps with
  | refl => exact ⟨level, rfl, fun _ => rfl⟩
  | tail previous step ih =>
    obtain ⟨middle, rfl, same⟩ := ih
    cases step with
    | head _ => exact ⟨middle, rfl, same⟩
    | @headRel _ _ right related =>
      cases right with
      | legacyGround => cases related
      | sort finalLevel =>
        exact ⟨finalLevel, rfl, fun valuation => (related valuation).symm.trans (same valuation)⟩

/-- The existing common-reduct theorem for opaque native extensions
separates universes with different valuation meanings. -/
theorem sort_conversion_iff (opacity : OpaqueRelatorExtension.Opacity signature)
    {n : Nat} (first second : LevelExpr Nat) :
    Conv (OpaqueRelatorExtension.rules signature).headEq
        (sortTm (n := n) first) (sortTm second)
        (OpaqueRelatorExtension.rules signature).computation ↔
      ∀ valuation, LevelExpr.eval valuation first = LevelExpr.eval valuation second := by
  constructor
  · intro converted
    obtain ⟨common, firstSteps, secondSteps⟩ :=
      NativeRelatorConversionParallel.conversion_join
        ((OpaqueRelatorExtension.conversion_iff opacity).mp converted)
    obtain ⟨firstEnd, firstShape, firstMeaning⟩ := parallel_sort_meaning firstSteps
    obtain ⟨secondEnd, secondShape, secondMeaning⟩ := parallel_sort_meaning secondSteps
    have ends : firstEnd = secondEnd := LevelTower.Head.sort.inj
      (Presentation.Tm.head.inj (firstShape.symm.trans secondShape))
    intro valuation
    exact (firstMeaning valuation).symm.trans
      ((congrArg (LevelExpr.eval valuation) ends).trans (secondMeaning valuation))
  · intro same
    exact .rel _ _ (.head same)

theorem universes_equal_iff (opacity : OpaqueRelatorExtension.Opacity signature)
    (context : NativeContext signature) (first second : LevelExpr Nat) :
    univ context first = univ context second ↔
      ∀ valuation, LevelExpr.eval valuation first = LevelExpr.eval valuation second :=
  (QType.mk_eq_iff _ _).trans (sort_conversion_iff opacity first second)

theorem universe_successor_distinct (opacity : OpaqueRelatorExtension.Opacity signature)
    (context : NativeContext signature) (level : LevelExpr Nat) :
    univ context level ≠ univ context (.succ level) := by
  intro same
  have impossible := (universes_equal_iff opacity context level (.succ level)).mp same (fun _ => 0)
  simp only [LevelExpr.eval] at impossible
  exact Nat.ne_add_one _ impossible

namespace Controls

abbrev context : NativeContext HOLNativeRelatorCompatibility.signature :=
  (quotientProjection HOLNativeRelatorCompatibility.rules).obj Common.context

def wireCode : Code context Tower.zero :=
  ofFormed Tower.zero Common.wireType.code Common.wireType.formed

theorem wire_decoded : decode wireCode = QType.mk Common.wireType :=
  decode_ofFormed _ _ _

theorem wire_cumulative :
    decode (liftCode (upper := .succ Tower.zero) (fun _ => Nat.le_succ _) wireCode) =
      QType.mk Common.wireType :=
  (decode_liftCode _ wireCode).trans wire_decoded

/-- Native computation inside a dependent type is visible to the same
universe's code equality. Literal syntax inspection is a finer observer. -/
theorem computed_identity_codes :
    ofFormed (context := context) Tower.zero (FibreControls.projectedIdentity (.natural 7)).code
        (FibreControls.projectedIdentity (.natural 7)).formed =
      ofFormed Tower.zero (FibreControls.resultIdentity (.natural 7)).code
        (FibreControls.resultIdentity (.natural 7)).formed :=
  (formed_codes_equal_iff _ _).mpr
    ((QType.mk_eq_iff _ _).mp (FibreControls.dependent_mixed_reindex (.natural 7)).2.2.1)

theorem computed_codes_not_literal :
    (FibreControls.projectedIdentity (.natural 7)).code ≠
      (FibreControls.resultIdentity (.natural 7)).code :=
  FibreControls.dependent_codes_differ.1

/-- An independently checked finite conversion path for the two endpoints
of the computed dependent type. -/
def mixedIdentityConversion : NativeRelatorConversionChecking.Code 0 :=
  .trans
    (.single (.congIdLeft NativeWireData.dataType
      (.betaSigmaSnd HOLNativeRelatorCompatibility.holSequenceSingleton
        (NativeWireData.encode (.natural 7))) (Common.projected (.natural 7)).code))
    (.single (.congIdRight NativeWireData.dataType (NativeWireData.encode (.natural 7))
      (.betaSigmaSnd HOLNativeRelatorCompatibility.holSequenceSingleton
        (NativeWireData.encode (.natural 7)))))

private theorem identity_substitution_code (term : Term Common.context Common.wireType) :
    (ComparisonControls.variableIdentity.reindex (Common.sectionHom term)).code =
      .id NativeWireData.dataType term.code term.code := by
  have newestCode := Term.cast_code Common.wireType.reindex_id.symm term
  change Presentation.Tm.id NativeWireData.dataType
      (term.cast Common.wireType.reindex_id.symm).code
      (term.cast Common.wireType.reindex_id.symm).code = _
  rw [newestCode]

theorem mixed_identity_conversion_checked :
    NativeRelatorConversionChecking.check mixedIdentityConversion
      (FibreControls.projectedIdentity (.natural 7)).code
      (FibreControls.resultIdentity (.natural 7)).code = true := by
  simp only [FibreControls.projectedIdentity, FibreControls.resultIdentity,
    identity_substitution_code]
  simp [NativeRelatorConversionChecking.check, mixedIdentityConversion,
    StructuralConversionCode.Code.check, StructuralConversionCode.Code.decode,
    StructuralConversionCode.StepCode.decode, StructuralConversionCode.mapEndpoints,
    StructuralConversionCode.joinEndpoints, Common.projected, Common.result,
    HOLNativeRelatorCompatibility.mixedPayload]
  exact ⟨rfl, rfl⟩

theorem changed_identity_endpoint_rejected :
    NativeRelatorConversionChecking.check mixedIdentityConversion
      (FibreControls.projectedIdentity (.natural 7)).code
      (FibreControls.resultIdentity (.natural 8)).code = false := by
  simp only [FibreControls.projectedIdentity, FibreControls.resultIdentity,
    identity_substitution_code]
  simp [NativeRelatorConversionChecking.check, mixedIdentityConversion,
    StructuralConversionCode.Code.check, StructuralConversionCode.Code.decode,
    StructuralConversionCode.StepCode.decode, StructuralConversionCode.mapEndpoints,
    StructuralConversionCode.joinEndpoints, Common.projected, Common.result,
    HOLNativeRelatorCompatibility.mixedPayload, NativeWireData.encode]
  intro _ same
  have endpoint := (Presentation.Tm.id.inj (congrArg Prod.snd same)).2.1
  have numeral := (Lean.Name.num.inj (Presentation.Tm.const.inj endpoint)).2
  cases numeral

theorem no_universe_collapse : univ context Tower.zero ≠ univ context (.succ Tower.zero) :=
  universe_successor_distinct HOLNativeRelatorCompatibility.opacity context Tower.zero

theorem no_lowering : ¬ Below (.succ (.param 0)) (.param 0) := by
  change ¬ Tower.Cumulative (.sort (.succ (.param 0))) (.sort (.param 0))
  decide

end Controls

#print axioms hierarchy
#print axioms substitutionStable
#print axioms cumulative
#print axioms code_exists_iff_atUniverse
#print axioms every_type_has_code
#print axioms decode_injective
#print axioms lift_sub
#print axioms lift_injective
#print axioms descends_iff_atUniverse
#print axioms sort_conversion_iff
#print axioms Controls.computed_identity_codes
#print axioms Controls.mixed_identity_conversion_checked
#print axioms Controls.changed_identity_endpoint_rejected
#print axioms Controls.no_universe_collapse
#print axioms Controls.no_lowering

end

end FormationSensitiveContextual.QuotientUniverses
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
