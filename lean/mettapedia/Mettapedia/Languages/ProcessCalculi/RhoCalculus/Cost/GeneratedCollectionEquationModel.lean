import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.GeneratedEquationPresentation
import Mettapedia.GSLT.LanguageDef.BindingCollectionEquationFamily

/-!
# Generated rho source equations and collection laws in one binding model

The actual generated base and wrapped parallel rows supply all finite-arity
permutation, flattening, singleton and unit instances. Together with both
compiled QuoteDrop rows they determine a full contextual binding quotient.
Raw declaring-rule witnesses remain separate evidence; the quotient may
identify different literal collection shapes.

This is a model of these intrinsic static equations. It is not the Cost
transformer, does not interpret purse affordability or R1, and does not identify
ordinary clone substitution with quote-sealing receiver substitution. No
signature unit/product equations are added.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.GeneratedCollectionEquationModel

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Binding
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.BindingSyntax
open Mettapedia.GSLT.LanguageDef.BindingSyntax.CollectionEquationFamily
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

abbrev language := GeneratedEquationPresentation.language

def parallelRule : CostStaticColor → GrammarRule
  | .base => costBaseConstructor rhoCIGSLT.cut rhoCalc.terms[3]
  | .wrapped => costWrappedConstructor (theory := rhoCIGSLT.theory) rhoCalc.terms[3]

def unitRule : CostStaticColor → GrammarRule
  | .base => costBaseConstructor rhoCIGSLT.cut rhoCalc.terms[0]
  | .wrapped => costWrappedConstructor (theory := rhoCIGSLT.theory) rhoCalc.terms[0]

def unitName : CostStaticColor → String
  | .base => costBaseConstructorName "PZero"
  | .wrapped => costWrappedConstructorName "PZero"

def parallelAlgebra (color : CostStaticColor) : CollectionAlgebra :=
  ⟨true, some (unitName color)⟩

theorem parallel_member (color : CostStaticColor) : parallelRule color ∈ language.terms := by
  cases color <;> decide +kernel

theorem unit_member (color : CostStaticColor) : unitRule color ∈ language.terms := by
  cases color <;> decide +kernel

theorem parallel_shape (color : CostStaticColor) :
    (parallelRule color).params =
      [.simple "ps" (.collection .hashBag (.base (parallelRule color).category))] := by
  cases color <;> rfl

theorem parallelDeclaration (color : CostStaticColor) :
    AlgebraRule language (parallelRule color) .hashBag (parallelAlgebra color) where
  authored := parallel_member color
  declared := by cases color <;> rfl
  selfSorted := ⟨"ps", parallel_shape color⟩
  unitAuthored := by
    intro name selected
    have same : unitName color = name := Option.some.inj selected
    subst name
    refine ⟨unitRule color, unit_member color, ?_, ?_, ?_⟩ <;> cases color <;> rfl

/-- The family contains both actual source rows and the declaring-rule-pinned
derived collection family. The latter includes every finite arity. -/
def family (equation : EqAxiom (signatureOf language) []) : Prop :=
  equation ∈ GeneratedEquationPresentation.equations ∨
    CollectionEquationFamily.family language equation

noncomputable abbrev algebra := BindingEquationFamilyModel.algebra family

theorem full_contextual_satisfaction : BindingEquationFamilyModel.Satisfies algebra family :=
  BindingEquationFamilyModel.algebra_satisfies family

theorem source_rows_supported :
    BindingEquationFamilyCongruence.Supported family GeneratedEquationPresentation.equations :=
  fun _ member => Or.inl member

theorem source_rows_satisfied :
    BindingEquationInterpretation.Satisfies algebra GeneratedEquationPresentation.equations :=
  BindingEquationFamilyModel.satisfies_fragment _ full_contextual_satisfaction source_rows_supported

noncomputable def sourcePresheafInterpretation :=
  BindingEquationFamilyModel.presheafInterpretation family GeneratedEquationPresentation.equations
    source_rows_supported

def permutationAxiom (color : CostStaticColor) {Γ : List TypeExpr}
    (first second : List (Term (signatureOf language) Γ (.base (parallelRule color).category)))
    (permutation : first.Perm second) : DeclaredAxiom language :=
  bagPermutation (parallelRule color) (parallel_member color) "ps" (parallel_shape color)
    first second permutation

def flattenAxiom (color : CostStaticColor) {Γ : List TypeExpr}
    (pre inner post : List (Term (signatureOf language) Γ (.base (parallelRule color).category))) :
    DeclaredAxiom language :=
  flattening (parallelRule color) .hashBag (parallelAlgebra color) (parallelDeclaration color)
    "ps" (parallel_shape color) rfl pre inner post

def singletonAxiom (color : CostStaticColor) {Γ : List TypeExpr}
    (value : Term (signatureOf language) Γ (.base (parallelRule color).category)) :
    DeclaredAxiom language :=
  singletonCollapse (parallelRule color) .hashBag (parallelAlgebra color) (parallelDeclaration color)
    "ps" (parallel_shape color) rfl value

noncomputable def unitEliminationAxiom (color : CostStaticColor) {Γ : List TypeExpr}
    (pre post : List (Term (signatureOf language) Γ (.base (parallelRule color).category))) :
    DeclaredAxiom language :=
  unitElimination (parallelRule color) .hashBag (parallelAlgebra color) (parallelDeclaration color)
    "ps" (parallel_shape color) (unitName color) rfl pre post

noncomputable def emptyUnitAxiom (color : CostStaticColor) (Γ : List TypeExpr) :
    DeclaredAxiom language :=
  emptyUnit (Γ := Γ) (parallelRule color) .hashBag (parallelAlgebra color)
    (parallelDeclaration color) "ps" (parallel_shape color) (unitName color) rfl

/-- Every declared collection law has a full contextual semantic instance;
in particular its ordinary replacements may themselves contain accounts. -/
theorem declared_satisfied (declaration : DeclaredAxiom language) :
    BindingEquationInterpretation.Satisfies algebra [declaration.toAxiom] :=
  BindingEquationFamilyModel.satisfies_fragment _ full_contextual_satisfaction
    (by
      intro equation member
      obtain rfl := List.mem_singleton.mp member
      exact Or.inr (declared_admitted declaration))

theorem project_declared (declaration : DeclaredAxiom language) :
    BindingEquationFamilyModel.project family declaration.left =
      BindingEquationFamilyModel.project family declaration.right := by
  apply Quotient.sound
  let bodies : ContextualAssignment (signatureOf language) [] [] := fun position =>
    Fin.elim0 position
  let ambient : Sub (signatureOf language) [] declaration.context := fun _ position => nomatch position
  have primitive := EqClosure.ax (E := [declaration.toAxiom]) ⟨0, by simp⟩ bodies ambient
    (fun _ position => Term.var position)
  refine ⟨[declaration.toAxiom], ?_, ?_⟩
  · intro equation member
    obtain rfl := List.mem_singleton.mp member
    exact Or.inr (declared_admitted declaration)
  · simpa only [List.get_eq_getElem, List.getElem_cons_zero, DeclaredAxiom.toAxiom,
      ContextualAssignment.instantiate_embed, bind_id] using primitive

/-- A real source variable and its singleton parallel container are different
raw terms, while the authored quotient correctly identifies them. -/
theorem singleton_raw_distinct_and_projected (color : CostStaticColor) :
    let value : Term (signatureOf language) [.base (parallelRule color).category]
        (.base (parallelRule color).category) := .var .zero
    (singletonAxiom color value).left ≠ value ∧
      BindingEquationFamilyModel.project family (singletonAxiom color value).left =
        BindingEquationFamilyModel.project family value := by
  dsimp only
  constructor
  · intro same
    cases same
  · exact project_declared (singletonAxiom color (.var .zero))

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.GeneratedCollectionEquationModel
