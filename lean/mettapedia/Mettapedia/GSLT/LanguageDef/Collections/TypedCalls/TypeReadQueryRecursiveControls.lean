import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadQueryRecursive
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadQueryControls
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeFreshReadControls
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeCurrentReader

/-! # Recursive coordinate controls on the actual source driver -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadQueryRecursiveControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open NativeTypeCallGraph TypeReadQueryWorlds
open TypeReadSupply (Supply)

def initialWorld : Coordinates := ⟨Equiv.refl String, []⟩

theorem supplies_protected (first second : Supply) : Protected initialWorld first second := by
  constructor <;> simp [initialWorld]

theorem identity_normalizers : TypeReadQueryRows.Normalizers id id :=
  ⟨fun _ safe => safe, fun _ _ _ member => member, fun _ _ _ => rfl⟩

theorem repeated_polymorphic_result :
    (NativeTypeScopedReads.evaluate NativeTypeCurrentReader.currentOps NativeTypeFreshReadControls.source
      NativeTypeCurrentReader.external 4 NativeTypeFreshReadControls.call ⟨[], 0⟩).1 =
      some (.types [.symbol "R"]) := by cbv

theorem arbitrary_prior_allocation_preserves_polymorphic_result (supply : Supply) :
    (NativeTypeScopedReads.evaluate NativeTypeCurrentReader.currentOps NativeTypeFreshReadControls.source
      NativeTypeCurrentReader.external 4 NativeTypeFreshReadControls.call supply).1 =
      some (.types [.symbol "R"]) :=
  TypeReadQueryRecursive.retained_evaluate_equal NativeTypeFreshReadControls.source NativeTypeCurrentReader.external
    NativeTypeFreshReadControls.resource_safety_does_not_supply_freshness
    TypeNormalizationNames.equality_equivariant id id identity_normalizers (fun _ => []) (fun _ => [])
    4 initialWorld NativeTypeFreshReadControls.call ⟨[], 0⟩ supply
    ⟨by simp [questionNames, NativeTypeFreshReadControls.call, NativeTypeRecursiveControls.expr,
      NativeTypeRecursiveControls.sym, atomVariables, atomListVariables],
     by simp [questionNames, NativeTypeFreshReadControls.call, NativeTypeRecursiveControls.expr,
      NativeTypeRecursiveControls.sym, atomVariables, atomListVariables]⟩
    (supplies_protected _ _) [.symbol "R"] repeated_polymorphic_result (by decide)

theorem annotated_source_safe : NativeTypeSourcePorts.Safe NativeTypeCurrentReader.source := by
  unfold NativeTypeSourcePorts.Safe
  decide

theorem arbitrary_prior_allocation_keeps_prefix_and_duplicate_arrows (supply : Supply) :
    (NativeTypeScopedReads.evaluate NativeTypeCurrentReader.currentOps NativeTypeCurrentReader.source
      NativeTypeCurrentReader.external 4 (.infer true NativeTypeCurrentReader.twice) supply).1 =
      some (.types [.symbol "Claimed", .symbol "Parent", .symbol "Actual", .symbol "Actual"]) :=
  TypeReadQueryRecursive.retained_evaluate_equal NativeTypeCurrentReader.source NativeTypeCurrentReader.external
    annotated_source_safe TypeNormalizationNames.equality_equivariant id id identity_normalizers
    (fun _ => []) (fun _ => []) 4 initialWorld (.infer true NativeTypeCurrentReader.twice) ⟨[], 0⟩ supply
    ⟨by simp [questionNames, NativeTypeCurrentReader.twice, NativeTypeCurrentReader.number,
      atomVariables, atomListVariables],
     by simp [questionNames, NativeTypeCurrentReader.twice, NativeTypeCurrentReader.number,
      atomVariables, atomListVariables]⟩
    (supplies_protected _ _) _ NativeTypeCurrentReader.different_arrows_keep_duplicate_derived_answers (by decide)

theorem open_recursive_answers_need_coordinates :
    (NativeTypeScopedReads.evaluate NativeTypeCurrentReader.currentOps TypeReadQueryControls.source
      NativeTypeCurrentReader.external 3 (.infer true (.symbol "K")) ⟨[], 0⟩).1 ≠
    (NativeTypeScopedReads.evaluate NativeTypeCurrentReader.currentOps TypeReadQueryControls.source
      NativeTypeCurrentReader.external 3 (.infer true (.symbol "K")) ⟨[], 7⟩).1 := by
  cbv
  simp

theorem exhausted_closure_stays_unfinished :
    (NativeTypeScopedReads.evaluate NativeTypeCurrentReader.currentOps
      { NativeTypeCurrentReader.source with subtypeBudget := 0 } NativeTypeCurrentReader.external
      4 (.infer true NativeTypeCurrentReader.twice) ⟨[], 0⟩).1 = none ∧
    (NativeTypeScopedReads.evaluate NativeTypeCurrentReader.currentOps
      { NativeTypeCurrentReader.source with subtypeBudget := 0 } NativeTypeCurrentReader.external
      4 (.infer true NativeTypeCurrentReader.twice) ⟨["retained"], 7⟩).1 = none := by cbv

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadQueryRecursiveControls
