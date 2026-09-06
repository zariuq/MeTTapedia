import Mettapedia.GSLT.LanguageDef.CertificateGSLTHeterogeneousAuthority
import Mettapedia.GSLT.LanguageDef.StructuralPatternBindingNaturality

/-!
# Binding-aware semantic authority maps for CertificateGSLTs

A ground `JudgmentEmbedding` maps claims and implements primitive rules by
proof-relevant open derivations.  This file identifies the upstream
presentation morphism that can generate such an embedding without forgetting
binding structure.

A binding-aware map contains:

* a structural morphism of the complete flat calculus languages;
* injective actions on object constructors and outer judgment heads; and
* a target open derivation implementing every source rule over the ordered,
  mapped premise occurrences.

The claim action is not arbitrary: it is exactly the structural action of the
calculus-language morphism.  The binding naturality theorems therefore follow
from the locally nameless structural action, while proof-hole substitution is
inherited from `JudgmentEmbedding.mapOpen_bind`.  Independent semantic
preservation remains a separate field and induces the existing exact NIK
authority translation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLT

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.GSLT.LanguageDef.InferenceChecker

/-- A binding-aware, proof-relevant translation of two CertificateGSLT
presentations. -/
structure BindingJudgmentEmbedding (source target : Object) where
  structural : CalculusStructuralMorphism source.definition target.definition
  constructor_injective : Function.Injective structural.symbols.constructor
  judgment_injective : Function.Injective structural.symbols.judgment
  onRule :
    ∀ (ruleInstance : RuleInstance) {premises : List Pattern}
      {conclusion : Pattern},
      RuleApplication source.definition ruleInstance premises conclusion →
        OpenDerivation target.definition
          (premises.map (mapJudgmentPattern structural.symbols))
          (mapJudgmentPattern structural.symbols conclusion)

namespace BindingJudgmentEmbedding

/-- Forget the authored structural origin while retaining its exact ground
action and proof-relevant rule implementation. -/
def toJudgmentEmbedding {source target : Object}
    (embedding : BindingJudgmentEmbedding source target) :
    JudgmentEmbedding source target where
  mapClaim := mapJudgmentPattern embedding.structural.symbols
  mapClaim_injective :=
    mapJudgmentPattern_injective embedding.structural.symbols
      embedding.constructor_injective embedding.judgment_injective
  onRule := embedding.onRule

@[simp] theorem toJudgmentEmbedding_mapClaim
    {source target : Object}
    (embedding : BindingJudgmentEmbedding source target)
    (claim : Pattern) :
    embedding.toJudgmentEmbedding.mapClaim claim =
      mapJudgmentPattern embedding.structural.symbols claim :=
  rfl

/-- Binding-aware identity uses the exact structural identity and a single
native rule node with one proof hole for every ordered premise occurrence. -/
def identity (object : Object) : BindingJudgmentEmbedding object object where
  structural := CalculusStructuralMorphism.id object.definition
  constructor_injective := by
    intro left right equality
    exact equality
  judgment_injective := by
    intro left right equality
    exact equality
  onRule := by
    intro ruleInstance premises conclusion application
    change OpenDerivation object.definition
      (premises.map (mapJudgmentPattern CalculusLanguageSymbols.id))
      (mapJudgmentPattern CalculusLanguageSymbols.id conclusion)
    have contextEquality :
        premises.map (mapJudgmentPattern CalculusLanguageSymbols.id) =
          premises := by
      calc
        premises.map (mapJudgmentPattern CalculusLanguageSymbols.id) =
            premises.map _root_.id := by
          apply List.map_congr_left
          intro premise _
          exact mapJudgmentPattern_id premise
        _ = premises := List.map_id premises
    rw [contextEquality, mapJudgmentPattern_id]
    exact OpenDerivation.byRule ruleInstance application
      (assumptionEnvironment object.definition premises)

@[simp] theorem identity_mapClaim (object : Object) (claim : Pattern) :
    (identity object).toJudgmentEmbedding.mapClaim claim = claim := by
  exact mapJudgmentPattern_id claim

/-- Binding-aware translations compose by structural language composition
and proof substitution. -/
def comp {first middle last : Object}
    (earlier : BindingJudgmentEmbedding first middle)
    (later : BindingJudgmentEmbedding middle last) :
    BindingJudgmentEmbedding first last where
  structural :=
    CalculusStructuralMorphism.comp earlier.structural later.structural
  constructor_injective := by
    intro left right equality
    apply earlier.constructor_injective
    apply later.constructor_injective
    exact equality
  judgment_injective := by
    intro left right equality
    apply earlier.judgment_injective
    apply later.judgment_injective
    exact equality
  onRule := by
    intro ruleInstance premises conclusion application
    change OpenDerivation last.definition
      (premises.map
        (mapJudgmentPattern
          (earlier.structural.symbols.comp later.structural.symbols)))
      (mapJudgmentPattern
        (earlier.structural.symbols.comp later.structural.symbols) conclusion)
    convert later.toJudgmentEmbedding.mapOpen
        (earlier.onRule ruleInstance application) using 1
    · rw [List.map_map]
      apply List.map_congr_left
      intro premise _
      simpa only [Function.comp_apply, toJudgmentEmbedding_mapClaim] using
        mapJudgmentPattern_comp earlier.structural.symbols
          later.structural.symbols premise
    · exact mapJudgmentPattern_comp earlier.structural.symbols
        later.structural.symbols conclusion

/-- The ground claim action of a composite is exactly the composite claim
action; no additional representation map appears at generation time. -/
theorem comp_mapClaim {first middle last : Object}
    (earlier : BindingJudgmentEmbedding first middle)
    (later : BindingJudgmentEmbedding middle last)
    (claim : Pattern) :
    (comp earlier later).toJudgmentEmbedding.mapClaim claim =
      later.toJudgmentEmbedding.mapClaim
        (earlier.toJudgmentEmbedding.mapClaim claim) := by
  exact mapJudgmentPattern_comp earlier.structural.symbols
    later.structural.symbols claim

/-- Within a judgment-shaped claim, opening commutes with the binding-aware
translation.  The replacement is object-language data and is therefore
translated through the constructor namespace. -/
theorem mapClaim_openBVar {source target : Object}
    (embedding : BindingJudgmentEmbedding source target)
    (index : Nat) (replacement : Pattern)
    (head : String) (arguments : List Pattern) :
    embedding.toJudgmentEmbedding.mapClaim
        (openBVar index replacement (.apply head arguments)) =
      openBVar index
        (mapPattern embedding.structural.symbols.toLanguageDefSymbolMap
          replacement)
        (embedding.toJudgmentEmbedding.mapClaim (.apply head arguments)) :=
  mapJudgmentPattern_openBVar embedding.structural.symbols index replacement
    head arguments

/-- Binder-eliminating substitution has the same mixed-namespace naturality
law on judgment-shaped claims. -/
theorem mapClaim_instantiateBVarAt {source target : Object}
    (embedding : BindingJudgmentEmbedding source target)
    (depth : Nat) (replacement : Pattern)
    (head : String) (arguments : List Pattern) :
    embedding.toJudgmentEmbedding.mapClaim
        (instantiateBVarAt depth replacement (.apply head arguments)) =
      instantiateBVarAt depth
        (mapPattern embedding.structural.symbols.toLanguageDefSymbolMap
          replacement)
        (embedding.toJudgmentEmbedding.mapClaim (.apply head arguments)) :=
  mapJudgmentPattern_instantiateBVarAt embedding.structural.symbols depth
    replacement head arguments

/-- Translation of open derivations remains natural with respect to plugging
ordered proof holes after the binding structure is forgotten. -/
theorem mapOpen_bind {source target : Object}
    (embedding : BindingJudgmentEmbedding source target)
    {sourceContext targetContext : List Pattern} {goal : Pattern}
    (derivation :
      OpenDerivation source.definition sourceContext goal)
    (environment :
      OpenDerivationList source.definition targetContext sourceContext) :
    embedding.toJudgmentEmbedding.mapOpen
        (derivation.bind environment) =
      (embedding.toJudgmentEmbedding.mapOpen derivation).bind
        (embedding.toJudgmentEmbedding.mapOpenList environment) :=
  JudgmentEmbedding.mapOpen_bind embedding.toJudgmentEmbedding derivation
    environment

end BindingJudgmentEmbedding

end Mettapedia.GSLT.LanguageDef.CertificateGSLT

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLTBindingAuthority

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.NIKHeterogeneousTheory
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.CertificateGSLTHeterogeneousAuthority

/-- A binding-aware presentation map with an independently authored semantic
preservation theorem. -/
structure BindingSemanticEmbedding
    (source target : SemanticPresentation) where
  proof : BindingJudgmentEmbedding source.object target.object
  meaning_preserved : ∀ claim,
    source.Meaning claim →
      target.Meaning (proof.toJudgmentEmbedding.mapClaim claim)

namespace BindingSemanticEmbedding

/-- Forget the structural origin and retain the heterogeneous semantic map
consumed by exact authority generation. -/
def toSemanticEmbedding {source target : SemanticPresentation}
    (embedding : BindingSemanticEmbedding source target) :
    SemanticEmbedding source target where
  proof := embedding.proof.toJudgmentEmbedding
  meaning_preserved := embedding.meaning_preserved

/-- Semantic identity is induced by binding-aware structural identity. -/
def identity (presentation : SemanticPresentation) :
    BindingSemanticEmbedding presentation presentation where
  proof := BindingJudgmentEmbedding.identity presentation.object
  meaning_preserved := by
    intro claim meaningful
    simpa only [BindingJudgmentEmbedding.identity_mapClaim] using meaningful

/-- Binding-aware semantic maps compose without changing their independent
meaning predicates. -/
def comp {first middle last : SemanticPresentation}
    (earlier : BindingSemanticEmbedding first middle)
    (later : BindingSemanticEmbedding middle last) :
    BindingSemanticEmbedding first last where
  proof := BindingJudgmentEmbedding.comp earlier.proof later.proof
  meaning_preserved := by
    intro claim meaningful
    rw [BindingJudgmentEmbedding.comp_mapClaim]
    exact later.meaning_preserved _
      (earlier.meaning_preserved claim meaningful)

/-- A binding-aware semantic presentation map generates the same exact NIK
authority translation as its ground action. -/
def map {source target : SemanticPresentation}
    (embedding : BindingSemanticEmbedding source target) :
    CertifiedTranslation (contract source) (contract target) :=
  CertificateGSLTHeterogeneousAuthority.map embedding.toSemanticEmbedding

/-- Exact checker replay, including rejection, is inherited by the generated
binding-aware authority translation. -/
theorem map_check_commutes {source target : SemanticPresentation}
    (embedding : BindingSemanticEmbedding source target)
    (claim : Pattern) (certificate : (contract source).Certificate ()) :
    ((contract target).checker ()).check
        (embedding.proof.toJudgmentEmbedding.mapClaim claim)
        ((map embedding).mapCertificate () certificate) =
      ((contract source).checker ()).check claim certificate :=
  (map embedding).check_commutes () claim certificate

/-- Independent meaning is preserved at the exact structurally translated
claim. -/
theorem map_meaning_preserved {source target : SemanticPresentation}
    (embedding : BindingSemanticEmbedding source target)
    (claim : Pattern) (meaningful : source.Meaning claim) :
    target.Meaning
      (embedding.proof.toJudgmentEmbedding.mapClaim claim) :=
  (map embedding).meaning_preserved () claim meaningful

end BindingSemanticEmbedding

#print axioms BindingSemanticEmbedding.comp
#print axioms BindingSemanticEmbedding.map
#print axioms BindingSemanticEmbedding.map_check_commutes
#print axioms BindingSemanticEmbedding.map_meaning_preserved

end Mettapedia.GSLT.LanguageDef.CertificateGSLTBindingAuthority
