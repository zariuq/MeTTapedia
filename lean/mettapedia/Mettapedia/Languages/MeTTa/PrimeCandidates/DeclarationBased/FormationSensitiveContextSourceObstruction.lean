import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeRelatorCompatibility
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypingGeneration

/-!
# Typed substitutions do not recover their raw source context

The actual common native rules admit a substitution from an unformed raw
telescope into the formed empty context. Specializing an abstract type to
a dependent-function type can make a previously ill-formed application
annotation well formed. Refined component typing and universe regularity
therefore do not supply source-context formation.

Both source formation and target formation remain necessary indices for
the formed-context interpretation interface. This obstruction changes no
typing, conversion, declaration, universe or evaluation rule.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace FormationSensitiveContextSourceObstruction

open FormationSensitive

abbrev rules := HOLNativeRelatorCompatibility.rules

def annotationLevel : LevelExpr := .max Tower.zero (.succ Tower.zero)

def dataFunctionType {n : Nat} : Tower.Tm n :=
  .pi NativeWireData.dataType (sortTm Tower.zero)

def dataFunction {n : Nat} : Tower.Tm n := .lam NativeWireData.dataType

def wire {n : Nat} : Tower.Tm n := NativeWireData.encode (.natural 0)

def telescopePrefix : Tower.Ctx 2 := .snoc (.snoc .nil (sortTm annotationLevel)) (.var 0)

def source : Tower.Ctx 3 := .snoc telescopePrefix (.app (.var 0) wire)

def substitution : Sub Tower.Head 3 0 :=
  Fin.cases wire (Fin.cases dataFunction (Fin.cases dataFunctionType Fin.elim0))

theorem data_function_type_formed {n : Nat} (context : Tower.Ctx n) :
    Typing rules context dataFunctionType (sortTm annotationLevel) :=
  .piForm (HOLNativeRelatorCompatibility.wire_typing (NativeWireData.dataType_formed context))
    (.sort Tower.zero) (.headType (.sort Tower.zero)) (.sort (.succ Tower.zero))
    (.sorts Tower.zero (.succ Tower.zero))

theorem data_function_typed {n : Nat} (context : Tower.Ctx n) :
    Typing rules context dataFunction dataFunctionType :=
  .lamIntro (data_function_type_formed context) (.sort annotationLevel)
    (HOLNativeRelatorCompatibility.wire_typing (NativeWireData.dataType_formed _))

theorem wire_typed {n : Nat} (context : Tower.Ctx n) :
    Typing rules context wire NativeWireData.dataType :=
  HOLNativeRelatorCompatibility.wire_typing (NativeWireData.encode_typing context (.natural 0))

theorem instantiated_annotation_formed :
    Typing rules .nil (.app dataFunction wire) (sortTm Tower.zero) :=
  .appElim (data_function_typed .nil) (wire_typed .nil)

theorem instantiated_annotation_converts :
    Conv rules.headEq (.app (dataFunction : Tower.Tm 0) wire) NativeWireData.dataType
      rules.computation :=
  .rel _ _ (.betaPi NativeWireData.dataType wire)

theorem substitution_typed : FormationSensitive.CtxMor rules source .nil substitution := by
  intro index
  refine Fin.cases ?_ (fun remaining => Fin.cases ?_
    (fun last => Fin.cases ?_ (fun impossible => Fin.elim0 impossible) last) remaining) index
  · simpa only [source, Ctx.lookup_snoc_zero, substitution, Fin.cases_zero,
      subst, rename, wk, Fin.cases_succ, wire, NativeWireData.encode] using
      (Typing.conv (wire_typed .nil) instantiated_annotation_formed (.sort Tower.zero)
        instantiated_annotation_converts.symm)
  · change Typing rules .nil dataFunction dataFunctionType
    exact data_function_typed .nil
  · change Typing rules .nil dataFunctionType (sortTm annotationLevel)
    exact data_function_type_formed .nil

theorem telescope_prefix_formed : ContextFormation rules telescopePrefix :=
  .snoc (.snoc .nil (.headType (.sort annotationLevel)) (.sort (.succ annotationLevel)))
    (.var 0) (.sort annotationLevel)

/-- In the unspecialized prefix, `f : A` cannot be used as a function.
Substitution of a universe head into a purported Pi conversion contradicts
the existing native Pi/head separation theorem. -/
theorem source_unformed : ¬ ContextFormation rules source := by
  intro formed
  cases formed with
  | snoc _ annotation _ =>
      obtain ⟨domain, codomain, function, _, _⟩ := HasType.appGeneration annotation.toRaw
      have boundary := OpaqueRelatorExtension.pi_conversion_boundary HOLNativeRelatorCompatibility.opacity
      have converted := (HasType.variableAdjustment function).toConvOfPiTarget boundary
      change Conv rules.headEq (.var (1 : Fin 2)) (.pi domain codomain) rules.computation at converted
      have specialized := converted.substitute (fun _ => (sortTm Tower.zero : Tower.Tm 0))
      exact boundary.headDisjoint specialized.symm

/-- The target is genuinely formed, all substitution components are
refined-typed, and the actual universe rules satisfy regularity. -/
theorem regular_typed_substitution_from_unformed_source :
    UniverseRegularity rules ∧ ContextFormation rules (.nil : Tower.Ctx 0) ∧
      FormationSensitive.CtxMor rules source .nil substitution ∧ ¬ ContextFormation rules source :=
  ⟨OpaqueRelatorExtension.universes, .nil, substitution_typed, source_unformed⟩

theorem no_source_formation_recovery :
    ¬ (∀ {n m : Nat} {source : Tower.Ctx n} {target : Tower.Ctx m}
        {sigma : Sub Tower.Head n m},
      ContextFormation rules target → FormationSensitive.CtxMor rules source target sigma →
        ContextFormation rules source) := by
  intro recover
  exact source_unformed (recover .nil substitution_typed)

end FormationSensitiveContextSourceObstruction
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
