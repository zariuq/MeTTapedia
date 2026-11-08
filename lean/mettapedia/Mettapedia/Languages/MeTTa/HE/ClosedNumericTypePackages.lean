import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Exact

/-!
# Independent closed numeric application packages

The inference evidence uses the source package judgment, its actual ordered
declarations, freshening contract and argument-matching matrix. It contains
no executable reader equality. Direct expression annotations are explicitly
excluded; this does not identify internal inference with public get-type.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Exact.ClosedNumeric

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

def arrow (range : String) : Atom :=
  .expression [.symbol "->", .symbol "Number", .symbol "Number", .symbol range]

def call (head : String) (left right : Int) : Atom :=
  .expression [.symbol head, .grounded (.int left), .grounded (.int right)]

theorem number_match : CorePlusR2TypePresentationMatchRel [] (.symbol "Number") (.symbol "Number") [] :=
  .reduced (by decide) (by decide) (by decide) (by decide)
    (.ordinary (by decide) (by decide) (by trivial) rfl rfl (.identical [] _))

theorem closed_variant (avoid : List String) (value : Atom) (closed : TypeSubst.typeVars value = []) :
    TypeCandidateAlphaVariantRel avoid value value := by
  exact ⟨id, Function.injective_id, (ScopeObservation.renameTypeVars_id value).symm, by simp [closed]⟩

/-- One actual declared arrow on two integer operands earns exactly one
source inference package. Neither the package nor the cell match is assumed. -/
theorem binary (space : Space) (head range : String) (left right : Int)
    (notState : head ≠ "StateValue")
    (declared : AnnotationTypesRel (.symbol head) space.atoms [arrow range])
    (unannotated : AnnotationTypesRel (call head left right) space.atoms []) :
    RuntimeTypePackagesRel space (call head left right) [publishedPackage (.symbol range)] := by
  let avoid := inferenceAvoidNames space (call head left right)
    ([arrow range] ++ [[Atom.symbol "Number"], [Atom.symbol "Number"]].flatten)
  apply RuntimeTypePackagesRel.expressionInferred
    (operatorPackages := [publishedPackage (arrow range)])
    (argumentPackageLists := [[publishedPackage (.symbol "Number")], [publishedPackage (.symbol "Number")]])
    (rawArgumentLists := [[.symbol "Number"], [.symbol "Number"]])
    (rawOperators := [arrow range]) (avoid := avoid)
    (freshArgumentChoices := [[.symbol "Number", .symbol "Number"]])
    (freshOperators := [arrow range])
  · intro value
    exact Or.inl (by simpa using notState)
  · exact unannotated
  · exact .symbolKnown declared (by simp)
  · exact .cons (.grounded (.int left)) (.cons (.grounded (.int right)) .nil)
  · rfl
  · rfl
  · rfl
  · exact .cons (.cons (closed_variant _ _ rfl) (.cons (closed_variant _ _ rfl) (.nil _))) .nil
  · exact .cons (closed_variant _ _ rfl) .nil
  · simp [ApplicationPackageScopesSeparated, Freshness.FreshFamiliesSeparated,
      Freshness.AtomsAvoid, arrow, TypeSubst.typeVars, TypeSubst.typeVarsList]
  · apply ApplicationPackageMatrixRel.singleton_success
    simpa [inferredPackage, publishedPackage, RuntimeTypePackage.published, TypeSubst.apply] using
      ApplicationPackageSuccessRel.mk (operatorType := arrow range) (returnType := .symbol range)
        (expectedTypes := [.symbol "Number", .symbol "Number"])
        (actualTypes := [.symbol "Number", .symbol "Number"]) (substitution := []) rfl
        (.cons number_match (.cons number_match (.nil [])))
  · simp

end Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Exact.ClosedNumeric
