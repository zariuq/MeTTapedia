import Mettapedia.GSLT.LanguageDef.Cost.FiniteDeclarationInventory
import Mettapedia.GSLT.LanguageDef.LambdaContinuedInteraction
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.SynchronousDecoration

/-!
# Authored finite declaration inventories

Lambda and synchronous rho instantiate the same cut-derived inventory. The
synchronous output keeps both of its selected process slots and the receiver
keeps its local binder. Principals remain structural region boundaries.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.FiniteDeclarationInventoryControls
open Mettapedia.OSLF.MeTTaIL.Syntax StructuralMorphism
open ContinuationDecorationProfile LambdaContinuedInteraction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Synchronous

theorem lambda_profile_constructed :
    ofRetypingPlan lambdaContinuationRetyping =
      withNonprincipalInventory (cut := lambdaInteractionCut) [] [] :=
  ofRetypingPlan_eq_withNonprincipalInventory lambdaContinuationRetyping

/-- The extra sent-process slot is retained by the declaration construction. -/
theorem synchronous_profile_constructed : communicationDecoration =
    withNonprincipalInventory (cut := rhoSyncInteractionCut) [] [sentProcessSlot] := rfl

theorem lambda_inventory_exact (constructor : DeclaredConstructor lambdaValidatedLanguageDef) :
    constructor ∈ (ofRetypingPlan lambdaContinuationRetyping).constructorClosure ↔
      constructor ≠ lambdaInteractionCut.program.constructor ∧
        constructor ≠ lambdaInteractionCut.environment.constructor :=
  withNonprincipalInventory_mem (cut := lambdaInteractionCut) [] [] constructor

theorem synchronous_inventory_exact
    (constructor : DeclaredConstructor rhoSyncValidatedLanguageDef) :
    constructor ∈ communicationDecoration.constructorClosure ↔
      constructor ≠ rhoSyncInteractionCut.program.constructor ∧
        constructor ≠ rhoSyncInteractionCut.environment.constructor :=
  withNonprincipalInventory_mem [] [sentProcessSlot] constructor

theorem lambda_inventory_nodup :
    (ofRetypingPlan lambdaContinuationRetyping).constructorClosure.Nodup :=
  withNonprincipalInventory_nodup [] []

theorem synchronous_inventory_nodup : communicationDecoration.constructorClosure.Nodup :=
  withNonprincipalInventory_nodup [] [sentProcessSlot]

/-- Exact names and order are obtained from the authored six-row language. -/
theorem synchronous_inventory_names : communicationDecoration.wrappedLabels =
    ["PZero", "PDrop", "NQuote", "PPar"] := by decide +kernel

/-- The lambda source has only its two principals. Its empty static
constructor inventory must not be advertised as a compiler of arbitrary
lambda code; those constructors require structural retained frames. -/
theorem lambda_static_inventory_empty :
    (ofRetypingPlan lambdaContinuationRetyping).constructorClosure = [] := by decide +kernel

/-- The exact finite intrinsic inventory accounts for every generated row. -/
theorem synchronous_rows_exact :
    communicationDecoration.declaredCostConstructors.map
      communicationDecoration.materializeDeclaredCostConstructor =
      communicationDecoration.costCoreLanguage.terms :=
  communicationDecoration.declaredCostConstructors_materialize

theorem synchronous_rows_nodup : communicationDecoration.declaredCostConstructors.Nodup :=
  communicationDecoration.declaredCostConstructors_nodup synchronous_inventory_nodup

/-- The materialized output has both process-valued continuation positions,
including the additional transmitted payload. -/
theorem synchronous_output_row :
    (communicationDecoration.materializeDeclaredCostConstructor
      ⟨.base rhoSyncOutputConstructor, trivial⟩).params =
      [.simple "n" (.base (costBaseSortName "Name")),
       .simple "q" (.base costWrappedSortName),
       .simple "k" (.base costWrappedSortName)] :=
  communicationDecoration_output_parameters

/-- The input retains its authored local name binder and wrapped body. -/
theorem synchronous_input_row :
    (communicationDecoration.materializeDeclaredCostConstructor
      ⟨.base rhoSyncInputConstructor, trivial⟩).params =
      [.simple "n" (.base (costBaseSortName "Name")),
       .abstraction "p" (.arrow (.base (costBaseSortName "Name")) (.base costWrappedSortName))] :=
  communicationDecoration_input_parameters

theorem synchronous_quote_role :
    communicationDecoration.declaredCostConstructorRole
      ⟨.base rhoSyncQuoteConstructor, trivial⟩ = .static .base := by decide +kernel

theorem synchronous_quote_lookup : communicationDecoration.decodeDeclaredCostConstructor
    (costBaseConstructorName "NQuote") = some ⟨.base rhoSyncQuoteConstructor, trivial⟩ :=
  communicationDecoration.decodeDeclaredCostConstructor_render ⟨.base rhoSyncQuoteConstructor, trivial⟩

/-- The additional output slot does not turn the active introduction into
an equation-bearing static constructor. -/
theorem synchronous_output_role :
    communicationDecoration.declaredCostConstructorRole
      ⟨.base rhoSyncOutputConstructor, trivial⟩ = .interactionPrincipal := by decide +kernel

theorem synchronous_wrapped_output_rejected :
    ¬ communicationDecoration.IsDeclaredCostConstructor (.wrapped rhoSyncOutputConstructor) := by
  change rhoSyncOutputConstructor ∉ communicationDecoration.constructorClosure
  rw [synchronous_inventory_exact]
  intro excluded
  exact excluded.2 rfl

theorem synchronous_wrapped_output_lookup_rejected : communicationDecoration.decodeDeclaredCostConstructor
    (costWrappedConstructorName "POutputK") = none := by decide +kernel

/-- Exact commitments inhabit the apparatus role and cannot be mistaken
for source static structure by a prefix-based classifier. -/
theorem commitment_role : communicationDecoration.declaredCostConstructorRole
    ⟨.apparatus .signatureCommit, trivial⟩ = .apparatus .signatureCommit := rfl

theorem commitment_lookup : communicationDecoration.decodeDeclaredCostConstructor
    costSignatureCommitConstructorName = some ⟨.apparatus .signatureCommit, trivial⟩ :=
  communicationDecoration.decodeDeclaredCostConstructor_render ⟨.apparatus .signatureCommit, trivial⟩

theorem commitment_not_static (color : CostStaticColor) :
    communicationDecoration.declaredCostConstructorRole
      ⟨.apparatus .signatureCommit, trivial⟩ ≠ .static color := by
  simp [declaredCostConstructorRole]

end Mettapedia.GSLT.LanguageDef.FiniteDeclarationInventoryControls
