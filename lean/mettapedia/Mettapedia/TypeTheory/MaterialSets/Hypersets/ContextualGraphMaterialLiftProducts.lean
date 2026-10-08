import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialLiftSums
import Mettapedia.TypeTheory.ContextualSmallFamilyNativeAdjunction

/-!
# Complete future products across the material universe embedding

Upper products are independently formed from the raised domain and body.
The native comparison retains every future context, arrow and argument.
Application readings and the full material function bodies are compared
using their actual ordered pairs.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialLiftProducts

open CategoryTheory Mettapedia.TypeTheory ContextualWitnessCover
open ContextualSmallFamilyUniverse ContextualSmallFamilyComprehension
open ContextualGraphDiagrams ContextualRealizedGraphs
open ContextualGraphMaterialFamilies ContextualGraphMaterialProducts
open ContextualGraphMaterialLift WiderPresheafDependentFunctions

universe u
variable {D : Type u} [Category.{u} D] {original : D ⥤ Type u}
variable (domain : Family original) (body : Family (total domain.native))

abbrev upper := pi (raise domain) (raisedBody domain body)
abbrev retained := raise (pi domain body)

abbrev lowerBody := indexedBody domain.native body.native
abbrev upperBody := indexedBody (native domain) (raisedBody domain body).native

def lowerNative (point : (base original).Elements)
    (function : DependentSection (native domain) (upperBody domain body) point) :
    DependentSection domain.native (lowerBody domain body) ((elementsDown original).obj point) where
  app next arrow argument :=
    (function.app ((elementsUp original).obj next) ((elementsUp original).map arrow) (ULift.up argument)).down
  naturality step arrival argument := congrArg ULift.down
    (function.naturality ((elementsUp original).map step) ((elementsUp original).map arrival) (ULift.up argument))

def raiseNative (point : (base original).Elements)
    (function : DependentSection domain.native (lowerBody domain body) ((elementsDown original).obj point)) :
    DependentSection (native domain) (upperBody domain body) point where
  app next arrow argument := ULift.up
    (function.app ((elementsDown original).obj next) ((elementsDown original).map arrow) argument.down)
  naturality step arrival argument := congrArg ULift.up
    (function.naturality ((elementsDown original).map step) ((elementsDown original).map arrival) argument.down)

theorem lower_raise (point : (base original).Elements)
    (function : DependentSection domain.native (lowerBody domain body) ((elementsDown original).obj point)) :
    lowerNative domain body point (raiseNative domain body point function) = function := by
  apply DependentSection.ext
  intro _ _ _
  rfl

theorem raise_lower (point : (base original).Elements)
    (function : DependentSection (native domain) (upperBody domain body) point) :
    raiseNative domain body point (lowerNative domain body point function) = function := by
  apply DependentSection.ext
  intro _ _ _
  rfl

theorem lower_restrict {first second : (base original).Elements} (step : first ⟶ second)
    (function : DependentSection (native domain) (upperBody domain body) first) :
    lowerNative domain body second
        (DependentSection.restrict (native domain) (upperBody domain body) step function) =
      DependentSection.restrict domain.native (lowerBody domain body) ((elementsDown original).map step)
        (lowerNative domain body first function) := by
  apply DependentSection.ext
  intro _ _ _
  rfl

theorem raise_restrict {first second : (base original).Elements} (step : first ⟶ second)
    (function : DependentSection domain.native (lowerBody domain body) ((elementsDown original).obj first)) :
    raiseNative domain body second
        (DependentSection.restrict domain.native (lowerBody domain body) ((elementsDown original).map step) function) =
      DependentSection.restrict (native domain) (upperBody domain body) step
        (raiseNative domain body first function) := by
  apply DependentSection.ext
  intro _ _ _
  rfl

def futureEquiv (point : (base original).Elements) :
    DependentSection (native domain) (upperBody domain body) point ≃
      DependentSection domain.native (lowerBody domain body) ((elementsDown original).obj point) where
  toFun := lowerNative domain body point
  invFun := raiseNative domain body point
  left_inv := raise_lower domain body point
  right_inv := lower_raise domain body point

def smallEquiv (point : (base original).Elements) :
    (upper domain body).native.obj point ≃ (pi domain body).native.obj ((elementsDown original).obj point) :=
  (ContextualSmallFamilyNativeAdjunction.nativeSmallEquiv (native domain) (upperBody domain body) point).symm.trans
    ((futureEquiv domain body point).trans
      (ContextualSmallFamilyNativeAdjunction.nativeSmallEquiv domain.native (lowerBody domain body)
        ((elementsDown original).obj point)))

def nativeEquiv (point : (base original).Elements) :
    (upper domain body).native.obj point ≃ (retained domain body).native.obj point :=
  (smallEquiv domain body point).trans Equiv.ulift.symm

def decompressed : NaturalHom (upper domain body).native
    (dependentFunctions (native domain) (upperBody domain body)) where
  app := (ContextualSmallFamilyNativeAdjunction.smallToNative (native domain) (upperBody domain body)).app
  naturality := (ContextualSmallFamilyNativeAdjunction.smallToNative (native domain) (upperBody domain body)).naturality

def lowerCompressed : NaturalHom (dependentFunctions (native domain) (upperBody domain body))
    (retained domain body).native where
  app point function := ULift.up
    ((ContextualSmallFamilyNativeAdjunction.nativeToSmall domain.native (lowerBody domain body)).app
      ((elementsDown original).obj point) (lowerNative domain body point function))
  naturality {first second} step function := by
    apply ULift.ext
    have natural := (ContextualSmallFamilyNativeAdjunction.nativeToSmall domain.native (lowerBody domain body)).naturality
      ((elementsDown original).map step) (lowerNative domain body first function)
    exact natural.trans (congrArg
      ((ContextualSmallFamilyNativeAdjunction.nativeToSmall domain.native (lowerBody domain body)).app
        ((elementsDown original).obj second)) (lower_restrict domain body step function).symm)

def forward : NaturalHom (upper domain body).native (retained domain body).native :=
  (decompressed domain body).comp (lowerCompressed domain body)

theorem forward_value (point : (base original).Elements) (function : (upper domain body).native.obj point) :
    (forward domain body).app point function = nativeEquiv domain body point function := rfl

def backward : NaturalHom (retained domain body).native (upper domain body).native where
  app point := (nativeEquiv domain body point).symm
  naturality {first second} step function := by
    apply (nativeEquiv domain body second).injective
    have natural := (forward domain body).naturality step ((nativeEquiv domain body first).symm function)
    exact natural.symm.trans (congrArg ((retained domain body).native.map step)
      ((nativeEquiv domain body first).apply_symm_apply function)) |>.trans
        ((nativeEquiv domain body second).apply_symm_apply _).symm

theorem forward_backward : (forward domain body).comp (backward domain body) =
    ContextualSmallMapConstructions.identity (upper domain body).native := by
  apply NaturalHom.ext
  intro point function
  exact (nativeEquiv domain body point).symm_apply_apply function

theorem backward_forward : (backward domain body).comp (forward domain body) =
    ContextualSmallMapConstructions.identity (retained domain body).native := by
  apply NaturalHom.ext
  intro point function
  exact (nativeEquiv domain body point).apply_symm_apply function

theorem evaluation (point : (base original).Elements)
    (function : (upper domain body).native.obj point) (argument : (native domain).obj point) :
    (evaluated (raise domain) (raisedBody domain body) point function argument).down =
      evaluated domain body ((elementsDown original).obj point)
        ((forward domain body).app point function).down argument.down := by
  let raw := (decompressed domain body).app point function
  have upstairs := ContextualSmallFamilyNativeAdjunction.evaluation_compression
    (native domain) (upperBody domain body) point raw argument
  have inverse := (ContextualSmallFamilyNativeAdjunction.nativeSmallEquiv
    (native domain) (upperBody domain body) point).apply_symm_apply function
  change evaluated (raise domain) (raisedBody domain body) point
    ((ContextualSmallFamilyNativeAdjunction.nativeSmallEquiv
      (native domain) (upperBody domain body) point) raw) argument = raw.app point (𝟙 point) argument at upstairs
  have normalized : (ContextualSmallFamilyNativeAdjunction.nativeSmallEquiv
    (native domain) (upperBody domain body) point) raw = function := inverse
  have fixed := (congrArg (fun term =>
    evaluated (raise domain) (raisedBody domain body) point term argument) normalized).symm.trans upstairs
  have downstairs := ContextualSmallFamilyNativeAdjunction.evaluation_compression domain.native
    (lowerBody domain body) ((elementsDown original).obj point) (lowerNative domain body point raw) argument.down
  exact (congrArg ULift.down fixed).trans downstairs.symm

def functionParameterChange : NaturalHom (total (upper domain body).native)
    (base (total (pi domain body).native)) where
  app point receipt := ULift.up
    ⟨receipt.1.down, ((forward domain body).app ⟨point, receipt.1⟩ receipt.2).down⟩
  naturality {first second} arrival receipt := by
    apply ULift.ext
    exact congrArg (fun function : (retained domain body).native.obj
        ⟨second, (base original).map arrival receipt.1⟩ =>
      (⟨original.map arrival.down receipt.1.down, function.down⟩ :
        (total (pi domain body).native).obj second.down)) ((forward domain body).naturality
      (CategoryOfElements.homMk (F := base original) ⟨first, receipt.1⟩
        ⟨second, (base original).map arrival receipt.1⟩ arrival rfl) receipt.2)

abbrev applicationFamily (first : Family original) (second : Family (total first.native)) :=
  ContextualGraphMaterialSubstitution.applicationFamily first second

abbrev retainedApplication := substitute (raise (applicationFamily domain body))
  (functionParameterChange domain body)

def argumentsForward : NaturalHom
    (arguments (raise domain) (raisedBody domain body)) (retainedApplication domain body).native where
  app _ argument := argument
  naturality _ _ := rfl

def argumentsBackward : NaturalHom (retainedApplication domain body).native
    (arguments (raise domain) (raisedBody domain body)) where
  app _ argument := argument
  naturality _ _ := rfl

def applicationsComparison (point : (total (upper domain body).native).Elements)
    (argument : (arguments (raise domain) (raisedBody domain body)).obj point) :
    Equal
      (termValue (ContextualGraphMaterialSubstitution.applicationFamily
        (raise domain) (raisedBody domain body)) point argument)
      (termValue (retainedApplication domain body) point argument) := by
  let parameter : (base original).Elements := ⟨point.1, point.2.1⟩
  have results := congrArg (fun result => ContextualGraphOrderedPairs.orderedPair
    (termValue domain ((elementsDown original).obj parameter) argument.down)
    (termValue body ⟨point.1.down, ⟨point.2.1.down, argument.down⟩⟩ result))
    (evaluation domain body parameter point.2.2 argument)
  exact (ContextualGraphUniverseLiftPairs.orderedPairComparison
    (termValue domain ((elementsDown original).obj parameter) argument.down)
    (termValue body ⟨point.1.down, ⟨point.2.1.down, argument.down⟩⟩
      (evaluated (raise domain) (raisedBody domain body) parameter point.2.2 argument).down)).symm.trans
        (Equal.ofEq (congrArg ContextualGraphUniverseLift.value results))

def readingComparison (point : (base original).Elements) (function : (upper domain body).native.obj point) :
    Equal (termValue (upper domain body) point function)
      (termValue (retained domain body) point ((forward domain body).app point function)) :=
  (ContextualGraphMaterialSubstitution.carrierCongr
    (ContextualGraphMaterialSubstitution.applicationFamily (raise domain) (raisedBody domain body))
    (retainedApplication domain body)
    (argumentsForward domain body) (argumentsBackward domain body)
    (applicationsComparison domain body)
    (fun point argument => (applicationsComparison domain body point argument).symm)
    ⟨point.1, ⟨point.2, function⟩⟩).trans
      ((ContextualGraphMaterialSubstitution.carrierUnder (raise (applicationFamily domain body))
        (functionParameterChange domain body) ⟨point.1, ⟨point.2, function⟩⟩).trans
          (ContextualGraphMaterialLift.carrierComparison (applicationFamily domain body) point.1
            ⟨point.2.down, ((forward domain body).app point function).down⟩).symm)

def carrierComparison (point : (base original).Elements) :
    Equal (ContextualGraphUniverseLift.value
      ((carrier (pi domain body)).app point.1.down point.2.down))
      ((carrier (upper domain body)).app point.1 point.2) :=
  (ContextualGraphMaterialLift.carrierComparison (pi domain body) point.1 point.2.down).trans
    (ContextualGraphMaterialSubstitution.carrierCongr (upper domain body) (retained domain body)
      (forward domain body) (backward domain body) (readingComparison domain body)
      (fun point function =>
        (Equal.ofEq (congrArg (termValue (retained domain body) point)
          ((nativeEquiv domain body point).apply_symm_apply function))).symm.trans
            (readingComparison domain body point ((backward domain body).app point function)).symm) point).symm

def sectionComparison : (upper domain body).native.sections ≃ (retained domain body).native.sections where
  toFun := (forward domain body).mapSection
  invFun := (backward domain body).mapSection
  left_inv term := by
    apply Subtype.ext
    funext point
    exact (nativeEquiv domain body point).symm_apply_apply (term.val point)
  right_inv term := by
    apply Subtype.ext
    funext point
    exact (nativeEquiv domain body point).apply_symm_apply (term.val point)

def literalSectionComparison : (literal (upper domain body)).sections ≃
    (literal (retained domain body)).sections :=
  (sectionDecoder (upper domain body)).trans
    ((sectionComparison domain body).trans (sectionDecoder (retained domain body)).symm)

theorem literal_evaluation (term : (literal (upper domain body)).sections)
    (point : (base original).Elements) (argument : (native domain).obj point) :
    (evaluated (raise domain) (raisedBody domain body) point
      ((sectionDecoder (upper domain body) term).val point) argument).down =
      evaluated domain body ((elementsDown original).obj point)
        ((sectionDecoder (retained domain body)
          (literalSectionComparison domain body term)).val point).down argument.down :=
  evaluation domain body point ((sectionDecoder (upper domain body) term).val point) argument

theorem result_value (point : (base original).Elements)
    (function : (upper domain body).native.obj point) (argument : (native domain).obj point) :
    resultValue (raise domain) (raisedBody domain body) point function argument =
      ContextualGraphUniverseLift.value
        (resultValue domain body ((elementsDown original).obj point)
          ((forward domain body).app point function).down argument.down) :=
  congrArg (fun result => ContextualGraphUniverseLift.value
    (termValue body ⟨point.1.down, ⟨point.2.down, argument.down⟩⟩ result))
    (evaluation domain body point function argument)

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialLiftProducts
