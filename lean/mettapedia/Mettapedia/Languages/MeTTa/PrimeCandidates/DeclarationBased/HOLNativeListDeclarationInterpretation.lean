import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeListLength
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLLeibnizMapFusionNative

/-!
# Interpreting the actual HOL declaration package by native List programs

Every source declaration receives an independently typed closed image. The
generic typed constant-interpretation theorem then transports the original
compiled map-fusion proof into the unchanged mixed presentation. Its five
ordered proof inputs remain explicit here; this module does not replace them
by axioms or claim that this conditional proof has discharged them.
-/

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace HOLNativeListDeclarationInterpretation

open Presentation Presentation.Declaration Presentation.FormationSensitive
open Presentation.SchemaElaboration ConstantExpansion FormationSensitiveHOLInterface
open HOLNativeListConstantBodies NativeIndexedFamilies IntrinsicMaps
open Mettapedia.Logic HOL.UniformListInduction

private theorem typeAt_arrow (types : TypeInterpretation BaseSort) (n : Nat)
    (a b : HOL.Ty BaseSort) :
    typeAt types n (.arr a b) = arrow (typeAt types n a) (typeAt types n b) := by
  rw [arrow, typeAt_rename]
  rfl

private theorem liftClosed_empty (term : Tower.Tm 0) : (liftClosed term : Tower.Tm 0) = term := by
  have same : (Fin.elim0 : Ren 0 0) = id := by funext index; exact Fin.elim0 index
  exact (congrArg (fun rho => rename rho term) same).trans (rename_id term)

private theorem ofList_member {entries : List (DeclName × Entry Tower.Head)}
    {name : DeclName} {entry : Entry Tower.Head}
    (known : (Signature.ofList entries).entries name = some entry) :
    (name, entry) ∈ entries := by
  induction entries with
  | nil => cases known
  | cons first rest ih =>
      by_cases equal : name = first.1
      · have entryEqual : first.2 = entry := by
          simpa only [Signature.ofList, List.foldr, Signature.insert, if_pos equal,
            Option.some.injEq] using known
        exact List.mem_cons.mpr (Or.inl (Prod.ext equal entryEqual.symm))
      · have prior : (Signature.ofList rest).entries name = some entry := by
          simpa only [Signature.ofList, List.foldr, Signature.insert, if_neg equal] using known
        exact List.mem_cons.mpr (Or.inr (ih prior))

theorem constant_images {element : Tower.Tm 0}
    (elementTyped : Typing .nil element (sortTm Tower.zero))
    {name : DeclName} {type : Tower.Tm 0}
    (known : FormationSensitiveHOLProofFamily.rules.constantType name = some type) :
    Typing .nil (bodies element name) (expand (bodies element) type) := by
  change (FormationSensitiveHOLProofFamily.declarations.entries name).map Entry.type = some type at known
  obtain ⟨entry, entryKnown, rfl⟩ := Option.map_eq_some_iff.mp known
  by_cases equal : name = FormationSensitiveHOLProofFamily.proofName
  · subst name
    have entryEqual : entry = ⟨FormationSensitiveHOLProofFamily.proofType, none⟩ := by
      exact Option.some.inj entryKnown.symm
    subst entry
    simpa [bodies, expand, FormationSensitiveHOLProofFamily.proofType,
      FormationSensitiveHOLProofFamily.proofName, liftClosed, rename, sortTm] using
      FormationSensitiveHOLProofListIntegration.proof_typed
        (FormationSensitiveHOLProofFamily.proofConstant_typed .nil)
  have sourceKnown : FormationSensitiveHOLUniformList.declarations.entries name = some entry := by
    simpa only [FormationSensitiveHOLProofFamily.declarations, Signature.insert, if_neg equal] using entryKnown
  have member := ofList_member sourceKnown
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
  rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  ·
    exact proposition_typed .nil
  ·
    exact elementTyped
  ·
    exact list_typed elementTyped
  ·
    exact count_typed .nil
  ·
    exact FormationSensitiveHOLProofListIntegration.proof_typed
      (FormationSensitiveHOLProofFamily.include_typed
        FormationSensitiveHOLUniformList.signature.implication_typed)
  ·
    apply FormationSensitiveHOLProofListIntegration.proof_typed
    apply FormationSensitiveHOLProofFamily.include_typed
    exact .const (by decide) FormationSensitiveHOLUniformList.universal_type_formed
      (.sort (.max (.succ Tower.zero) Tower.zero))
  ·
    apply FormationSensitiveHOLProofListIntegration.proof_typed
    apply FormationSensitiveHOLProofFamily.include_typed
    exact .const (by decide)
      (equalityDeclarationType_formed FormationSensitiveHOLUniformList.declarations
        FormationSensitiveHOLUniformList.types.proposition
        (FormationSensitiveHOLUniformList.proposition_formed .nil))
      (.sort (.max (.succ Tower.zero) Tower.zero))
  ·
    change Typing .nil (bodies element `HOLUniformList.nil)
      (expand (bodies element) (typeAt Source.types 0 sequence))
    rw [bodies_nil, expand_typeAt]
    simpa only [typeAt, types, liftClosed_empty] using nil_typed elementTyped
  ·
    change Typing .nil (bodies element `HOLUniformList.cons)
      (expand (bodies element) (typeAt Source.types 0 (.arr HOL.UniformListInduction.element (.arr sequence sequence))))
    rw [bodies_cons, expand_typeAt]
    simp only [typeAt_arrow]
    simpa only [typeAt, types, liftClosed_empty] using cons_typed elementTyped
  ·
    change Typing .nil (bodies element `HOLUniformList.map)
      (expand (bodies element) (typeAt Source.types 0 (.arr mapping (.arr sequence sequence))))
    rw [bodies_map, expand_typeAt]
    simp only [mapping, typeAt_arrow]
    simpa only [typeAt, types, liftClosed_empty] using map_typed elementTyped
  ·
    change Typing .nil (bodies element `HOLUniformList.length)
      (expand (bodies element) (typeAt Source.types 0 (.arr sequence count)))
    rw [bodies_length, expand_typeAt]
    simp only [typeAt_arrow]
    simpa only [typeAt, types, liftClosed_empty] using HOLNativeListLength.length_typed elementTyped
  ·
    exact zero_typed .nil
  ·
    exact successor_typed .nil

/-- Actual declaration images and actual decoder-root conversions instantiate
the generic derivation-preservation theorem. -/
theorem interpretation {element : Tower.Tm 0}
    (elementTyped : Typing .nil element (sortTm Tower.zero)) :
    TypedInterpretation FormationSensitiveHOLProofFamily.rules rules (bodies element) where
  headTyping := fun h => h
  isUniverse := fun h => h
  join := fun h => h
  cumulative := fun h => h
  headEq := rfl
  constant := constant_images elementTyped
  root := root_conversion element

def interpretedProof (element : Tower.Tm 0) : Tower.Tm 0 :=
  expand (bodies element) HOLLeibnizMapFusionNative.nativeProof

/-- The proof being interpreted is the compiler's actual output on the
retained original HOL proof tree, with precisely its original five inputs. -/
theorem original_compiled_judgment {element : Tower.Tm 0}
    (elementTyped : Typing .nil element (sortTm Tower.zero)) :
    ∃ proposition : Tower.Tm 0,
      HOLLeibnizNativeProofTranslation.represent HOLLeibnizMapFusionNative.closedClaim =
        some proposition ∧
      Judgment rules .nil (interpretedProof element)
        (expand (bodies element) (FormationSensitiveHOLProofFamily.proof proposition)) := by
  obtain ⟨proposition, represented, admitted⟩ := HOLLeibnizMapFusionNative.native_judgment
  exact ⟨proposition, represented, (interpretation elementTyped).judgment admitted⟩

#print axioms constant_images
#print axioms interpretation
#print axioms original_compiled_judgment

end HOLNativeListDeclarationInterpretation
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
