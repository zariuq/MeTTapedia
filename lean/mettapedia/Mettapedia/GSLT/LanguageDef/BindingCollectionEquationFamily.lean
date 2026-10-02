import Mettapedia.GSLT.LanguageDef.BindingSignature
import Mettapedia.GSLT.LanguageDef.EquationOccurrence
import Mettapedia.OSLF.Syntax.BindingEquationFamilyModel

/-!
# Collection equations from actual authored declaration witnesses

The equation family retains the declaring grammar row, its exact category,
and the existing proof-relevant derived-law witness. Its generators range
over every finite collection size and every intrinsic ambient context. Their
closure and full quotient-valued model use the checked equation-family core.
The family adds no signature monoid laws and carries no runtime authority.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.BindingSyntax.CollectionEquationFamily

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Binding
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics

def declaringRule {language : LanguageDef} {left right : Pattern} :
    DerivedGeneratorWitness language left right → GrammarRule
  | .bagPerm rule _ _ _ _ _ => rule
  | .setPerm rule _ _ _ _ _ => rule
  | .setDedup rule _ _ _ _ => rule
  | .flatten rule _ _ _ _ _ _ _ _ => rule
  | .singleton rule _ _ _ _ _ _ => rule
  | .unitElim rule _ _ _ _ _ _ _ _ => rule
  | .emptyUnit rule _ _ _ _ _ _ => rule

/-- Sorted intrinsic endpoints and the exact authored derived-law occurrence.
The category equation prevents a differently coloured declaration from
supplying the law merely by choosing another existential raw typing context. -/
structure DeclaredAxiom (language : LanguageDef) where
  context : List TypeExpr
  category : String
  left : Term (signatureOf language) context (.base category)
  right : Term (signatureOf language) context (.base category)
  source : Pattern
  target : Pattern
  leftErases : erase left = source
  rightErases : erase right = target
  witness : DerivedGeneratorWitness language source target
  sameCategory : (declaringRule witness).category = category

def DeclaredAxiom.toAxiom {language : LanguageDef} (declaration : DeclaredAxiom language) :
    EqAxiom (signatureOf language) [] :=
  ⟨declaration.context, .base declaration.category, embed declaration.left, embed declaration.right⟩

def family (language : LanguageDef) (equation : EqAxiom (signatureOf language) []) : Prop :=
  ∃ declaration : DeclaredAxiom language, declaration.toAxiom = equation

theorem declared_admitted {language : LanguageDef} (declaration : DeclaredAxiom language) :
    family language declaration.toAxiom := ⟨declaration, rfl⟩

/-- The actual variadic row is used at the input list's exact finite size. -/
def homogeneousArguments {language : LanguageDef} {Γ : List TypeExpr} {sort : TypeExpr} :
    (values : List (Term (signatureOf language) Γ sort)) →
      Args (signatureOf language) (List.replicate values.length ([], sort)) Γ
  | [] => .nil
  | head :: tail => .cons head (homogeneousArguments tail)

theorem erase_homogeneousArguments {language : LanguageDef}
    {Γ : List TypeExpr} {sort : TypeExpr}
    (values : List (Term (signatureOf language) Γ sort)) :
    eraseArguments (homogeneousArguments values) = values.map erase := by
  induction values with
  | nil => rfl
  | cons head tail ih => exact congrArg (List.cons (erase head)) ih

def node {language : LanguageDef} (rule : GrammarRule) (member : rule ∈ language.terms)
    (parameter : String) (kind : CollType)
    (shape : rule.params = [.simple parameter (.collection kind (.base rule.category))])
    {Γ : List TypeExpr} (values : List (Term (signatureOf language) Γ (.base rule.category))) :
    Term (signatureOf language) Γ (.base rule.category) :=
  .op (.collectionConstructor rule member parameter kind (.base rule.category) shape values.length)
    (homogeneousArguments values)

theorem erase_node {language : LanguageDef} (rule : GrammarRule)
    (member : rule ∈ language.terms) (parameter : String) (kind : CollType)
    (shape : rule.params = [.simple parameter (.collection kind (.base rule.category))])
    {Γ : List TypeExpr} (values : List (Term (signatureOf language) Γ (.base rule.category))) :
    erase (node rule member parameter kind shape values) =
      .collection kind (values.map erase) none := erase_homogeneousArguments values |>
        congrArg (fun elements => Pattern.collection kind elements none)

theorem sorted_node {language : LanguageDef} (rule : GrammarRule)
    (member : rule ∈ language.terms) (parameter : String) (kind : CollType)
    (shape : rule.params = [.simple parameter (.collection kind (.base rule.category))])
    {Γ : List TypeExpr} (values : List (Term (signatureOf language) Γ (.base rule.category))) :
    SortedAt language (.collection kind (values.map erase) none) rule.category := by
  refine ⟨FreeTypeContext.empty, Γ, ?_⟩
  rw [← erase_node rule member parameter kind shape values]
  exact erase_typed _

def bagPermutation {language : LanguageDef} (rule : GrammarRule)
    (member : rule ∈ language.terms) (parameter : String)
    (shape : rule.params = [.simple parameter (.collection .hashBag (.base rule.category))])
    {Γ : List TypeExpr} (first second : List (Term (signatureOf language) Γ (.base rule.category)))
    (permutation : first.Perm second) : DeclaredAxiom language where
  context := Γ
  category := rule.category
  left := node rule member parameter .hashBag shape first
  right := node rule member parameter .hashBag shape second
  source := .collection .hashBag (first.map erase) none
  target := .collection .hashBag (second.map erase) none
  leftErases := erase_node _ _ _ _ _ _
  rightErases := erase_node _ _ _ _ _ _
  witness := .bagPerm rule _ _ ⟨member, ⟨parameter, _, shape⟩⟩
    (sorted_node rule member parameter .hashBag shape first) (permutation.map erase)
  sameCategory := rfl

def setPermutation {language : LanguageDef} (rule : GrammarRule)
    (member : rule ∈ language.terms) (parameter : String)
    (shape : rule.params = [.simple parameter (.collection .hashSet (.base rule.category))])
    {Γ : List TypeExpr} (first second : List (Term (signatureOf language) Γ (.base rule.category)))
    (permutation : first.Perm second) : DeclaredAxiom language where
  context := Γ
  category := rule.category
  left := node rule member parameter .hashSet shape first
  right := node rule member parameter .hashSet shape second
  source := .collection .hashSet (first.map erase) none
  target := .collection .hashSet (second.map erase) none
  leftErases := erase_node _ _ _ _ _ _
  rightErases := erase_node _ _ _ _ _ _
  witness := .setPerm rule _ _ ⟨member, ⟨parameter, _, shape⟩⟩
    (sorted_node rule member parameter .hashSet shape first) (permutation.map erase)
  sameCategory := rfl

def setDeduplication {language : LanguageDef} (rule : GrammarRule)
    (member : rule ∈ language.terms) (parameter : String)
    (shape : rule.params = [.simple parameter (.collection .hashSet (.base rule.category))])
    {Γ : List TypeExpr} (value : Term (signatureOf language) Γ (.base rule.category))
    (rest : List (Term (signatureOf language) Γ (.base rule.category))) : DeclaredAxiom language where
  context := Γ
  category := rule.category
  left := node rule member parameter .hashSet shape (value :: value :: rest)
  right := node rule member parameter .hashSet shape (value :: rest)
  source := .collection .hashSet (erase value :: erase value :: rest.map erase) none
  target := .collection .hashSet (erase value :: rest.map erase) none
  leftErases := by rw [erase_node]; rfl
  rightErases := by rw [erase_node]; rfl
  witness := .setDedup rule _ _ ⟨member, ⟨parameter, _, shape⟩⟩
    (by simpa only [List.map_cons] using
      sorted_node rule member parameter .hashSet shape (value :: value :: rest))
  sameCategory := rfl

def flattening {language : LanguageDef} (rule : GrammarRule) (kind : CollType)
    (algebra : CollectionAlgebra) (declaration : AlgebraRule language rule kind algebra)
    (parameter : String)
    (shape : rule.params = [.simple parameter (.collection kind (.base rule.category))])
    (enabled : algebra.flatten = true) {Γ : List TypeExpr}
    (pre inner post : List (Term (signatureOf language) Γ (.base rule.category))) :
    DeclaredAxiom language where
  context := Γ
  category := rule.category
  left := node rule declaration.authored parameter kind shape
    (pre ++ node rule declaration.authored parameter kind shape inner :: post)
  right := node rule declaration.authored parameter kind shape (pre ++ inner ++ post)
  source := .collection kind
    (pre.map erase ++ .collection kind (inner.map erase) none :: post.map erase) none
  target := .collection kind (pre.map erase ++ inner.map erase ++ post.map erase) none
  leftErases := by simp only [erase_node, List.map_append, List.map_cons]
  rightErases := by simp only [erase_node, List.map_append]
  witness := .flatten rule kind algebra _ _ _ declaration enabled
    (by simpa only [List.map_append, List.map_cons, erase_node] using
      (sorted_node rule declaration.authored parameter kind shape
        (pre ++ node rule declaration.authored parameter kind shape inner :: post)))
  sameCategory := rfl

def singletonCollapse {language : LanguageDef} (rule : GrammarRule) (kind : CollType)
    (algebra : CollectionAlgebra) (declaration : AlgebraRule language rule kind algebra)
    (parameter : String)
    (shape : rule.params = [.simple parameter (.collection kind (.base rule.category))])
    (enabled : algebra.flatten = true) {Γ : List TypeExpr}
    (value : Term (signatureOf language) Γ (.base rule.category)) : DeclaredAxiom language where
  context := Γ
  category := rule.category
  left := node rule declaration.authored parameter kind shape [value]
  right := value
  source := .collection kind [erase value] none
  target := erase value
  leftErases := by rw [erase_node]; rfl
  rightErases := rfl
  witness := .singleton rule kind algebra _ declaration enabled
    (by simpa only [List.map_cons, List.map_nil] using
      sorted_node rule declaration.authored parameter kind shape [value])
  sameCategory := rfl

/-- The declared unit constructor is rebuilt from its actual nullary row. -/
def nullary {language : LanguageDef} (rule : GrammarRule) (member : rule ∈ language.terms)
    (empty : rule.params = []) {Γ : List TypeExpr} :
    Term (signatureOf language) Γ (.base rule.category) :=
  .op (.constructor rule member
    (by simp only [UsesBareCollection, empty]; simp)
    (by rw [empty]; exact ParameterScopes.nil)) .nil

theorem eraseConstructorArguments_empty {language : LanguageDef} {Γ : List TypeExpr}
    {parameters : List TermParam} (scopes : ParameterScopes parameters []) :
    eraseConstructorArguments (language := language) (bound := Γ) scopes .nil = [] := by
  cases scopes
  rfl

theorem erase_nullary {language : LanguageDef} (rule : GrammarRule)
    (member : rule ∈ language.terms) (empty : rule.params = []) {Γ : List TypeExpr} :
    erase (nullary (Γ := Γ) rule member empty) = .apply rule.label [] := by
  unfold nullary
  simp only [erase]
  congr 1
  exact eraseConstructorArguments_empty _

theorem erase_type_cast {language : LanguageDef} {Γ : List TypeExpr}
    {first second : TypeExpr} (same : first = second)
    (value : Term (signatureOf language) Γ first) :
    erase (same ▸ value) = erase value := by
  subst second
  rfl

noncomputable def declaredUnit {language : LanguageDef} (rule : GrammarRule) (kind : CollType)
    (algebra : CollectionAlgebra) (declaration : AlgebraRule language rule kind algebra)
    (unit : String) (isUnit : algebra.unit = some unit) {Γ : List TypeExpr} :
    Term (signatureOf language) Γ (.base rule.category) :=
  let found := declaration.unitAuthored unit isUnit
  let unitRule := Classical.choose found
  let data := Classical.choose_spec found
  congrArg TypeExpr.base data.2.2.1 ▸ nullary unitRule data.1 data.2.2.2

theorem erase_declaredUnit {language : LanguageDef} (rule : GrammarRule) (kind : CollType)
    (algebra : CollectionAlgebra) (declaration : AlgebraRule language rule kind algebra)
    (unit : String) (isUnit : algebra.unit = some unit) {Γ : List TypeExpr} :
    erase (declaredUnit (Γ := Γ) rule kind algebra declaration unit isUnit) = .apply unit [] := by
  unfold declaredUnit
  rw [erase_type_cast, erase_nullary, (Classical.choose_spec
    (declaration.unitAuthored unit isUnit)).2.1]

noncomputable def unitElimination {language : LanguageDef} (rule : GrammarRule) (kind : CollType)
    (algebra : CollectionAlgebra) (declaration : AlgebraRule language rule kind algebra)
    (parameter : String)
    (shape : rule.params = [.simple parameter (.collection kind (.base rule.category))])
    (unit : String) (isUnit : algebra.unit = some unit) {Γ : List TypeExpr}
    (pre post : List (Term (signatureOf language) Γ (.base rule.category))) :
    DeclaredAxiom language where
  context := Γ
  category := rule.category
  left := node rule declaration.authored parameter kind shape
    (pre ++ declaredUnit rule kind algebra declaration unit isUnit :: post)
  right := node rule declaration.authored parameter kind shape (pre ++ post)
  source := .collection kind (pre.map erase ++ .apply unit [] :: post.map erase) none
  target := .collection kind (pre.map erase ++ post.map erase) none
  leftErases := by simp only [erase_node, List.map_append, List.map_cons, erase_declaredUnit]
  rightErases := by simp only [erase_node, List.map_append]
  witness := .unitElim rule kind algebra unit _ _ declaration isUnit
    (by simpa only [List.map_append, List.map_cons, erase_declaredUnit] using
      (sorted_node rule declaration.authored parameter kind shape
        (pre ++ declaredUnit rule kind algebra declaration unit isUnit :: post)))
  sameCategory := rfl

noncomputable def emptyUnit {language : LanguageDef} (rule : GrammarRule) (kind : CollType)
    (algebra : CollectionAlgebra) (declaration : AlgebraRule language rule kind algebra)
    (parameter : String)
    (shape : rule.params = [.simple parameter (.collection kind (.base rule.category))])
    (unit : String) (isUnit : algebra.unit = some unit) {Γ : List TypeExpr} :
    DeclaredAxiom language where
  context := Γ
  category := rule.category
  left := node rule declaration.authored parameter kind shape []
  right := declaredUnit rule kind algebra declaration unit isUnit
  source := .collection kind [] none
  target := .apply unit []
  leftErases := by rw [erase_node]; rfl
  rightErases := erase_declaredUnit _ _ _ _ _ _
  witness := .emptyUnit rule kind algebra unit declaration isUnit
    (sorted_node (Γ := Γ) rule declaration.authored parameter kind shape [])
  sameCategory := rfl

/-- Every declaring-rule-certified family axiom has its full contextual law
in the actual constructed binding quotient. -/
noncomputable abbrev algebra (language : LanguageDef) :=
  BindingEquationFamilyModel.algebra (family language)

theorem full_contextual_satisfaction (language : LanguageDef) :
    BindingEquationFamilyModel.Satisfies (algebra language) (family language) :=
  BindingEquationFamilyModel.algebra_satisfies (family language)

end Mettapedia.GSLT.LanguageDef.BindingSyntax.CollectionEquationFamily
