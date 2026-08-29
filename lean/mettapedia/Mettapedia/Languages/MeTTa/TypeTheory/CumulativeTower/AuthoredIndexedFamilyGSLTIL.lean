import Mettapedia.GSLT.Core.LooseRelationCompanions
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.NativeIndexedFamilySource

/-!
# Authored indexed families as a represented GSLT-IL route

Prime's authored declaration document elaborates to an ordered finite
inventory and then interprets to an extensional declaration signature.  The
forward direction is functional, but it should not forget the intermediate
inventory merely to obtain that fact.  This module presents elaboration and
interpretation as one proof-relevant loose arrow, proves that it is represented
by the existing direct interpretation map, and identifies the opposite
direction as genuinely relational.

The reverse relation is not representable by one source-producing function:
different authored documents can have the same semantic signature.  Thus the
equipment retains all source worlds rather than selecting an arbitrary one.
This closes the derived source-to-semantics direction without making GSLT-IL a
premise of native family formation or computation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace AuthoredIndexedFamilyGSLTIL

open AuthoredDeclarationSignature
open Mettapedia.GSLT.LooseRelationEquipment
open Presentation
open Presentation.Declaration

/-! ## The proof-relevant authored interpretation route -/

/-- One exact source-to-signature route.  The intermediate declaration list is
retained as route evidence rather than recomputed from the target signature. -/
def AuthoredInterpretation :
    Loose SourceDocument (Signature Tower.Head) :=
  fun source signature =>
    Sigma fun declarations : List SourceDeclaration =>
      EqWitness (elaborate source) declarations ×
        EqWitness (semanticSignature declarations) signature

instance authoredInterpretationSubsingleton
    (source : SourceDocument) (signature : Signature Tower.Head) :
    Subsingleton (AuthoredInterpretation source signature) where
  allEq first second := by
    rcases first with ⟨firstDeclarations, firstSource, firstTarget⟩
    rcases second with ⟨secondDeclarations, secondSource, secondTarget⟩
    have declarationsEqual : firstDeclarations = secondDeclarations :=
      firstSource.down.down.symm.trans secondSource.down.down
    cases declarationsEqual
    have sourceEqual : firstSource = secondSource :=
      (instSubsingletonEqWitness _ _).allEq _ _
    cases sourceEqual
    have targetEqual : firstTarget = secondTarget :=
      (instSubsingletonEqWitness _ _).allEq _ _
    cases targetEqual
    rfl

/-- The retained two-stage route is represented exactly by direct semantic
interpretation.  Admission may therefore execute `interpret` without searching
through declaration inventories, while the loose witness remains available to
proof-relevant consumers. -/
def authoredInterpretationRepresentation :
    Representation AuthoredInterpretation where
  map := interpret
  exact source signature :=
    { toFun := fun witness => by
        rcases witness with ⟨declarations, sourceEquation, targetEquation⟩
        exact
          ⟨⟨(congrArg semanticSignature sourceEquation.down.down).trans
            targetEquation.down.down⟩⟩
      invFun := fun witness =>
        ⟨elaborate source, ⟨⟨rfl⟩⟩, by
          simpa [companion, interpret] using witness⟩
      left_inv := fun witness => Subsingleton.elim _ _
      right_inv := fun witness =>
        (instSubsingletonEqWitness _ _).allEq _ _ }

/-- Canonical route witness for one authored document. -/
def AuthoredInterpretation.canonical (source : SourceDocument) :
    AuthoredInterpretation source (interpret source) :=
  (authoredInterpretationRepresentation.exact source (interpret source)).symm
    ⟨⟨rfl⟩⟩

/-! ## The multiworld converse -/

/-- All authored source worlds compatible with one extensional signature. -/
def AuthoredSourceWorlds :
    Loose (Signature Tower.Head) SourceDocument :=
  fun signature source => AuthoredInterpretation source signature

/-- Semantic interpretation genuinely forgets authored distinctions.  The
proof reduces any hypothetical injectivity to the already established
non-injectivity of finite semantic signatures. -/
theorem interpret_not_injective : ¬ Function.Injective interpret := by
  intro interpretInjective
  apply semanticSignature_not_injective
  intro first second sameSignature
  have sameQuotedInterpretation :
      interpret (sourceCodec.quote first) =
        interpret (sourceCodec.quote second) := by
    simpa using sameSignature
  have sameDocuments := interpretInjective sameQuotedInterpretation
  have sameElaborations := congrArg elaborate sameDocuments
  simpa using sameElaborations

/-- If the converse route had a companion, its proof-relevant determinism
would make `interpret` injective.  The source-world relation is therefore a
genuine loose arrow: it may be explored or refined, but it cannot be replaced
globally by one exact source-selection function. -/
theorem authoredSourceWorlds_not_representable :
    ¬ Nonempty (Representation AuthoredSourceWorlds) := by
  rintro ⟨represented⟩
  apply interpret_not_injective
  intro first second sameInterpretation
  let firstWitness :
      AuthoredSourceWorlds (interpret first) first :=
    AuthoredInterpretation.canonical first
  let secondWitness :
      AuthoredSourceWorlds (interpret first) second := by
    rw [sameInterpretation]
    exact AuthoredInterpretation.canonical second
  have pairEqual :
      (⟨first, firstWitness⟩ :
          Sigma fun source => AuthoredSourceWorlds (interpret first) source) =
        ⟨second, secondWitness⟩ :=
    (represented.deterministic (interpret first)).allEq _ _
  exact congrArg Sigma.fst pairEqual

/-! ## Native List/identity witness -/

/-- The existing native List/identity source inhabits the generic authored
route to its independently defined native signature. -/
def nativeListIdentityRoute :
    AuthoredInterpretation NativeIndexedFamilySource.source
      NativeIndexedFamilies.Intrinsic.rawSignature := by
  refine
    ⟨NativeIndexedFamilySource.authoredDeclarations,
      ⟨⟨NativeIndexedFamilySource.source_elaborates_exactly⟩⟩, ⟨⟨?_⟩⟩⟩
  calc
    semanticSignature NativeIndexedFamilySource.authoredDeclarations =
        interpret NativeIndexedFamilySource.source := by
      simp [interpret,
        NativeIndexedFamilySource.source_elaborates_exactly]
    _ = NativeIndexedFamilies.Intrinsic.rawSignature :=
      NativeIndexedFamilySource.interpret_source_eq_rawSignature

/-! ## Axiom audit -/

#print axioms authoredInterpretationRepresentation
#print axioms AuthoredInterpretation.canonical
#print axioms interpret_not_injective
#print axioms authoredSourceWorlds_not_representable
#print axioms nativeListIdentityRoute

end AuthoredIndexedFamilyGSLTIL
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
