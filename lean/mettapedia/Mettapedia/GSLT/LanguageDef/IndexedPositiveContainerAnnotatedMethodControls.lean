import Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerAnnotatedMethods
import Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerGuestControls
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.Elaboration
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeNaturalVectorProfileControls

/-!
# Annotated mixed constructor telescope controls

The existing authored mixed constructor has five original fields and three
queued induction arguments. Its Vector bundle retains the original arity
across an intervening payload. The annotation pass is used here for its
proved syntactic erasure law; these controls establish traversal and ordering.
Guarded application and source typing have separate retained-value controls.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerAnnotatedMethodControls

open Mettapedia.TypeTheory.IndexedPositiveContainer
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation TypedEquality.Annotated
open IndexedPositiveContainerGuestTypes IndexedPositiveContainerGuestPlans
open IndexedPositiveContainerGuestMethodSpecialization
open IndexedPositiveContainerGuestControls.Vectors

abbrev code := Mixed.code

def fields : Fin (fieldCount code) → CTm Tower.Head 7 :=
  ![.var 4, .var 3, .var 2, .var 1, .var 0]

def motive : Tower.Tm 7 := .var 6
def constructor : Tower.Tm 7 := .var 5

def rawMethod : Tower.Tm 7 :=
  methodBody indexing containers code types PUnit.unit motive constructor []

def method : CTm Tower.Head 7 :=
  (elaborate (NativeNaturalVectorFamilies.Programs.Annotated.church
    NativeNaturalVectorProfile.Controls.profile).constantType Knowledge.empty none none rawMethod).1

theorem method_erases : method.erase = rawMethod := erase_elab _ _ _ _ _

def expectedHypotheses : List (Tower.Tm 7) :=
  [.app motive (.var 3), NativeVectorAll.allType PositiveInductiveVectorTreeGuest.treeTm
    motive (.var 4) (.var 1), .app motive (.var 0)]

def expectedConclusion : Tower.Tm 7 := .app motive
  (.app (.app (.app (.app (.app constructor (.var 4)) (.var 3)) (.var 2)) (.var 1)) (.var 0))

theorem five_original_fields : fieldCount code = 5 := rfl

theorem three_complete_hypotheses :
    hypothesisTypes indexing containers code types PUnit.unit motive (fun i => (fields i).erase) =
      expectedHypotheses := by decide +kernel

theorem conclusion_exact :
    conclusion indexing code PUnit.unit motive constructor (fun i => (fields i).erase) =
      expectedConclusion := by decide +kernel

theorem full_original_telescope :
    ∃ residual, IndexedPositiveContainerAnnotatedMethods.instantiateFields code fields method = some residual ∧
      residual.erase = hypotheses expectedHypotheses expectedConclusion := by
  obtain ⟨residual, accepted, exactType⟩ := IndexedPositiveContainerAnnotatedMethods.methodBody_specialize
    indexing containers code types PUnit.unit motive constructor [] fields method method_erases
  exact ⟨residual, accepted, by
    simpa only [List.nil_append, three_complete_hypotheses, conclusion_exact] using exactType⟩

def wrongFields : Fin (fieldCount code) → CTm Tower.Head 7 :=
  ![.var 2, .var 3, .var 4, .var 1, .var 0]

theorem moving_payload_into_arity_changes_bundle :
    hypothesisTypes indexing containers code types PUnit.unit motive (fun i => (wrongFields i).erase) ≠
      expectedHypotheses := by decide +kernel

theorem reversed_hypotheses_differ : expectedHypotheses.reverse ≠ expectedHypotheses := by decide +kernel

theorem missing_product_refused :
    IndexedPositiveContainerAnnotatedMethods.instantiateFields code fields
      (.pi (.const NativeNaturalVectorFamilies.natName) (.head .legacyGround)) = none := by
  decide +kernel

theorem non_function_refused :
    IndexedPositiveContainerAnnotatedMethods.instantiateFields code fields
      (.const NativeNaturalVectorFamilies.natName) = none := by decide +kernel

#print axioms full_original_telescope
#print axioms moving_payload_into_arity_changes_bundle
#print axioms missing_product_refused

end Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerAnnotatedMethodControls
