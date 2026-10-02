import Mettapedia.GSLT.LanguageDef.BindingCollectionEquationFamily

/-!
# Intrinsic provenance of the derived collection equations

Each generator is one of the seven authored collection operations on typed
inputs, at any finite arity and ordered context. Its raw boundary receipt is
obtained from the existing producer. This distinguishes generated intrinsic
equations from the stronger family admitting every alternative elaboration
of equal erased endpoints.

All intended operations remain available. No equation is obtained by guessing
the declaration or the type of an erased collection.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.BindingSyntax.CollectionEquationGenerators

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Binding
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open CollectionEquationFamily

/-- The actual collection row and its exact self-sorted parameter. -/
structure Row (language : LanguageDef) (kind : CollType) where
  rule : GrammarRule
  member : rule ∈ language.terms
  parameter : String
  shape : rule.params = [.simple parameter (.collection kind (.base rule.category))]

abbrev Values {language : LanguageDef} {kind : CollType} (row : Row language kind)
    (Γ : List TypeExpr) := List (Term (signatureOf language) Γ (.base row.rule.category))

/-- Only the existing typed producer operations generate this intrinsic
presentation. Arbitrary contexts, counts and typed child terms are retained. -/
inductive Generator (language : LanguageDef) : Type where
  | bagPermutation (row : Row language .hashBag) {Γ : List TypeExpr}
      (first second : Values row Γ) (permutation : first.Perm second)
  | setPermutation (row : Row language .hashSet) {Γ : List TypeExpr}
      (first second : Values row Γ) (permutation : first.Perm second)
  | setDeduplication (row : Row language .hashSet) {Γ : List TypeExpr}
      (value : Term (signatureOf language) Γ (.base row.rule.category)) (rest : Values row Γ)
  | flattening {kind : CollType} (row : Row language kind) (algebra : CollectionAlgebra)
      (declaration : AlgebraRule language row.rule kind algebra) (enabled : algebra.flatten = true)
      {Γ : List TypeExpr} (pre inner post : Values row Γ)
  | singletonCollapse {kind : CollType} (row : Row language kind) (algebra : CollectionAlgebra)
      (declaration : AlgebraRule language row.rule kind algebra) (enabled : algebra.flatten = true)
      {Γ : List TypeExpr} (value : Term (signatureOf language) Γ (.base row.rule.category))
  | unitElimination {kind : CollType} (row : Row language kind) (algebra : CollectionAlgebra)
      (declaration : AlgebraRule language row.rule kind algebra)
      (unit : String) (selected : algebra.unit = some unit)
      {Γ : List TypeExpr} (pre post : Values row Γ)
  | emptyUnit {kind : CollType} (row : Row language kind) (algebra : CollectionAlgebra)
      (declaration : AlgebraRule language row.rule kind algebra)
      (unit : String) (selected : algebra.unit = some unit) (Γ : List TypeExpr)

/-- The complete raw witness is produced from the supplied typed inputs,
rather than used to select arbitrary intrinsic endpoint elaborations. -/
noncomputable def Generator.declaration {language : LanguageDef} :
    Generator language → DeclaredAxiom language
  | .bagPermutation row first second permutation =>
      CollectionEquationFamily.bagPermutation row.rule row.member row.parameter row.shape
        first second permutation
  | .setPermutation row first second permutation =>
      CollectionEquationFamily.setPermutation row.rule row.member row.parameter row.shape
        first second permutation
  | .setDeduplication row value rest =>
      CollectionEquationFamily.setDeduplication row.rule row.member row.parameter row.shape value rest
  | .flattening row algebra declaration enabled pre inner post =>
      CollectionEquationFamily.flattening row.rule _ algebra declaration row.parameter row.shape
        enabled pre inner post
  | .singletonCollapse row algebra declaration enabled value =>
      CollectionEquationFamily.singletonCollapse row.rule _ algebra declaration row.parameter row.shape
        enabled value
  | .unitElimination row algebra declaration unit selected pre post =>
      CollectionEquationFamily.unitElimination row.rule _ algebra declaration row.parameter row.shape
        unit selected pre post
  | .emptyUnit row algebra declaration unit selected Γ =>
      CollectionEquationFamily.emptyUnit (Γ := Γ) row.rule _ algebra declaration row.parameter row.shape
        unit selected

def family (language : LanguageDef) (equation : EqAxiom (signatureOf language) []) : Prop :=
  ∃ generator : Generator language, generator.declaration.toAxiom = equation

theorem generated_admitted {language : LanguageDef} (generator : Generator language) :
    family language generator.declaration.toAxiom := ⟨generator, rfl⟩

/-- Every generated intrinsic law has its already checked declaring-rule and
raw operational boundary evidence. The converse is not asserted. -/
theorem included_in_boundary_family {language : LanguageDef}
    {equation : EqAxiom (signatureOf language) []} (admitted : family language equation) :
    CollectionEquationFamily.family language equation := by
  obtain ⟨generator, rfl⟩ := admitted
  exact declared_admitted generator.declaration

end Mettapedia.GSLT.LanguageDef.BindingSyntax.CollectionEquationGenerators
