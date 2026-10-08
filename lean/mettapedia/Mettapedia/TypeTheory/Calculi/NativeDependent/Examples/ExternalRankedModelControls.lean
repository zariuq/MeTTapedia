import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalRankedSoundness
import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalSyntacticModel
import Mettapedia.TypeTheory.Calculi.NativeDependent.Examples.ExternalModelControls

/-!
# Earlier-header interpretation and retained primitive source meanings

A later family has an incompatible supplied parameter context. Formation of
an earlier function header still interprets using only the scalar declaration.
The bounded qualifier cannot imply realization of that later declaration.
The generated model's primitive meanings are also read back at their original
headers through the actual presentation comparisons.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External.RankedModelControls

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Mettapedia.TypeTheory.ContextualTypeOperations
open Contextual

abbrev wrongFunctionParameters : Context ModelControls.familyModel 1 :=
  (Context.nil ModelControls.familyModel).snoc ModelControls.scalar

noncomputable def partialModel : ModelData Controls.symbols ModelControls.familyModel where
  products := ModelControls.products
  sums := ModelControls.sums
  typeParameters
    | .scalar => Context.nil ModelControls.familyModel
    | .fibre => wrongFunctionParameters
    | .pairMotive => ModelControls.declarations.pairContext
  typeFamily
    | .scalar => ModelControls.scalar
    | .fibre => fun _ => PUnit
    | .pairMotive => ModelControls.declarations.motive
  termParameters := fun _ => ModelControls.declarations.componentContext
  termType := fun _ => ModelControls.model.termType .fullBranch
  termValue := fun _ => ModelControls.model.termValue .fullBranch

theorem only_earlier_headers : BoundedRealization partialModel Controls.signature 2 where
  typeHeader symbol earlier := by
    cases symbol with
    | scalar => rfl
    | fibre => exact False.elim ((by decide : ¬ (2 < 2)) earlier)
    | pairMotive => exact False.elim ((by decide : ¬ (4 < 2)) earlier)
  termHeader symbol earlier := by
    cases symbol
    exact False.elim ((by decide : ¬ (5 < 2)) earlier)
  termResult symbol earlier := by
    cases symbol
    exact False.elim ((by decide : ¬ (5 < 2)) earlier)

theorem earlier_function_header_interpreted :
    Interprets partialModel (.context (Controls.signature.typeParameters .fibre)) :=
  (Controls.headers.typeHeader .fibre).sound_before partialModel only_earlier_headers
    Families.products_substitution
    (PiOperations.ofQualified_beta ContextualProductComparison.familiesProducts) ModelControls.products_eta
    (Controls.headers.typeHeader_before .fibre)

theorem actual_function_header_read :
    partialModel.evaluateContext (Controls.signature.typeParameters .fibre) =
      some ModelControls.declarations.functionContext :=
  ModelControls.declarations.function_header_read

theorem later_header_realization_fails : ¬ SignatureRealization partialModel Controls.signature := by
  intro realized
  have contexts := Option.some.inj (actual_function_header_read.symm.trans (realized.typeHeader .fibre))
  have sizes := congrArg (fun context => Nat.card context.1) contexts
  change Nat.card (Σ _ : PUnit, Bool → Bool) = Nat.card (Σ _ : PUnit, Bool) at sizes
  norm_num [Nat.card_eq_fintype_card] at sizes

noncomputable abbrev sourceData := Contextual.SyntacticModel.data Controls.headers

theorem primitive_family_is_retained :
    (Contextual.SyntacticModel.C Controls.signature).toCwf.tySub (sourceData.typeFamily .fibre)
      (Contextual.SyntacticModel.parameterComparison
        (Contextual.SyntacticModel.typeHeader Controls.headers .fibre)).inv =
      QType.mk (Contextual.SyntacticModel.originalFamily Controls.headers .fibre) :=
  Contextual.SyntacticModel.family_at_original_header Controls.headers .fibre

theorem supplied_primitive_section_is_retained :
    ((Contextual.SyntacticModel.C Controls.signature).toCwf.tmSub (sourceData.termValue .fullBranch)
      (Contextual.SyntacticModel.parameterComparison
        (Contextual.SyntacticModel.termHeader Controls.headers .fullBranch)).inv).val =
      QTerm.mk (Contextual.SyntacticModel.originalPrimitive Controls.headers .fullBranch) :=
  Contextual.SyntacticModel.primitive_at_original_header Controls.headers .fullBranch

theorem complete_pair_result_keeps_generic_components :
    (Contextual.SyntacticModel.originalResult Controls.headers .fullBranch).code =
      .family .pairMotive (fun _ => genericPair (Controls.domain 0) (Controls.body 0)) := rfl

end Mettapedia.TypeTheory.Calculi.NativeDependent.External.RankedModelControls
