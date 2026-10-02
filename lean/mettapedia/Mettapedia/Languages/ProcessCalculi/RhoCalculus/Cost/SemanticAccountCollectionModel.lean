import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.SemanticAccountOccurrenceModel
import Mettapedia.OSLF.Syntax.BindingPureContextualInterpretation
import Mettapedia.OSLF.Syntax.SecondOrderBindingModelRestriction

/-!
# Native occurrence accounts satisfy the intrinsic collection generators

The model retains arbitrary full contextual values and ordered account words
within each process occurrence. This module uses the actual declaring rows
and the typed producer operations, rather than selecting alternative endpoint
elaborations by their erased spelling. Inclusion into the broader raw-boundary
family is a separate comparison and does not assert equality of presentations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.SemanticAccountCollectionModel

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Binding
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.BindingSyntax
open Mettapedia.GSLT.LanguageDef.Cost
open CollectionEquationFamily
open FreeBindingTerms
open SemanticAccountOccurrenceModel
open _root_.CategoryTheory

abbrev markObject : SecondOrderContext.Object (signatureOf language) :=
  ⟨SemanticAccountSignature.declarations signatureSort wrappedSort⟩

abbrev originalAlgebra := SecondOrderContext.restrictAlgebra markObject algebra

abbrev interpret {Γ : List TypeExpr} {sort : TypeExpr}
    (value : Term (signatureOf language) Γ sort) :=
  BindingCloneFoldSubstitution.interpret originalAlgebra value

theorem homogeneous_values {Γ : List TypeExpr} {sort : TypeExpr}
    (values : List (Term (signatureOf language) Γ sort))
    (stage : Type) (above : stage ⟶ PUnit)
    (environment : (SemanticAccountValuation.model constructors signatureSort wrappedSort markMeaning).Env
      stage Γ) (point : stage) :
    Valuation.listArguments language Base sort values.length
      (SemanticAccountValuation.toOriginalFamily signatureSort wrappedSort _
        ((SemanticAccountValuation.model constructors signatureSort wrappedSort markMeaning).tupleArgs
          (SecondOrderContext.toAmbientArgs ⟨[]⟩
            (SecondOrderContext.toAmbientArgs markObject
              (BindingCloneFoldSubstitution.interpretArgs originalAlgebra
                (homogeneousArguments values)))) stage above environment point)) =
      values.map (fun value => (interpret value).value stage above environment point) := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      change _ :: _ = _ :: _
      apply congrArg₂ List.cons
      · exact congrArg (fun f => f (PUnit.unit, point))
          ((interpret head).natural (TypeCat.ofHom (Prod.snd : PUnit × stage → stage)) above environment)
      · exact ih

theorem node_value (color : CostStaticColor) {Γ : List TypeExpr}
    (values : List (Term (signatureOf language) Γ
      (.base (GeneratedCollectionEquationModel.parallelRule color).category)))
    (stage : Type) (above : stage ⟶ PUnit)
    (environment : (SemanticAccountValuation.model constructors signatureSort wrappedSort markMeaning).Env
      stage Γ) (point : stage) :
    processRead color ((interpret (node (GeneratedCollectionEquationModel.parallelRule color)
      (GeneratedCollectionEquationModel.parallel_member color) "ps" .hashBag
      (GeneratedCollectionEquationModel.parallel_shape color) values)).value
        stage above environment point) =
      (values.map (fun value => processRead color
        ((interpret value).value stage above environment point))).sum := by
  cases color
  all_goals
    exact congrArg (fun inputs : List Occurrences => inputs.sum)
      (homogeneous_values values stage above environment point)

/-- All collection rows of this actual signature are the two coloured bag
rows. Their exact parameter name and kind are recovered from the row receipt. -/
theorem row_classification {kind : CollType}
    (row : CollectionEquationGenerators.Row language kind) :
    ∃ color : CostStaticColor, row.rule = GeneratedCollectionEquationModel.parallelRule color ∧
      row.parameter = "ps" ∧ kind = .hashBag := by
  have filtered : row.rule ∈ language.terms.filter GeneratedAtomicSignatureReadout.bareCollection :=
    List.mem_filter.mpr ⟨row.member, by rw [GeneratedAtomicSignatureReadout.bareCollection, row.shape]⟩
  rw [GeneratedAtomicSignatureReadout.bare_inventory] at filtered
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at filtered
  rcases filtered with same | same
  · refine ⟨.base, same, ?_⟩
    have types := (GeneratedCollectionEquationModel.parallel_shape .base).symm.trans
      (same ▸ row.shape)
    simp only [List.cons.injEq, TermParam.simple.injEq,
      TypeExpr.collection.injEq, and_true] at types
    exact ⟨types.1.symm, types.2.symm⟩
  · refine ⟨.wrapped, same, ?_⟩
    have types := (GeneratedCollectionEquationModel.parallel_shape .wrapped).symm.trans
      (same ▸ row.shape)
    simp only [List.cons.injEq, TermParam.simple.injEq,
      TypeExpr.collection.injEq, and_true] at types
    exact ⟨types.1.symm, types.2.symm⟩

theorem unit_row_unique (color : CostStaticColor) (rule : GrammarRule)
    (member : rule ∈ language.terms) (label : rule.label = GeneratedCollectionEquationModel.unitName color) :
    rule = GeneratedCollectionEquationModel.unitRule color := by
  have inventory : language.terms.filter (fun row => decide
      (row.label = GeneratedCollectionEquationModel.unitName color)) =
      [GeneratedCollectionEquationModel.unitRule color] := by
    cases color <;> decide +kernel
  have selected : rule ∈ language.terms.filter (fun row => decide
      (row.label = GeneratedCollectionEquationModel.unitName color)) :=
    List.mem_filter.mpr ⟨member, by simpa only [decide_eq_true_eq] using label⟩
  rw [inventory] at selected
  exact List.mem_singleton.mp selected

theorem parallel_algebra_unique (color : CostStaticColor) (account : CollectionAlgebra)
    (declaration : AlgebraRule language (GeneratedCollectionEquationModel.parallelRule color)
      .hashBag account) : account = GeneratedCollectionEquationModel.parallelAlgebra color := by
  have actual : (GeneratedCollectionEquationModel.parallelRule color).algebra? =
      some (GeneratedCollectionEquationModel.parallelAlgebra color) := by
    cases color <;> rfl
  exact Option.some.inj (declaration.declared.symm.trans actual)

theorem nullary_transport {first second : GrammarRule} {category : String}
    (same : first = second) (firstMember : first ∈ language.terms)
    (secondMember : second ∈ language.terms) (firstEmpty : first.params = [])
    (secondEmpty : second.params = []) (firstCategory : first.category = category)
    (secondCategory : second.category = category) {Γ : List TypeExpr} :
    congrArg TypeExpr.base firstCategory ▸ nullary (Γ := Γ) first firstMember firstEmpty =
      congrArg TypeExpr.base secondCategory ▸ nullary second secondMember secondEmpty := by
  subst second
  rfl

theorem declared_unit_eq (color : CostStaticColor)
    (declaration : AlgebraRule language (GeneratedCollectionEquationModel.parallelRule color)
      .hashBag (GeneratedCollectionEquationModel.parallelAlgebra color)) {Γ : List TypeExpr} :
    declaredUnit (Γ := Γ) (GeneratedCollectionEquationModel.parallelRule color) .hashBag
      (GeneratedCollectionEquationModel.parallelAlgebra color) declaration
      (GeneratedCollectionEquationModel.unitName color) rfl =
        (show (.base (GeneratedCollectionEquationModel.unitRule color).category : TypeExpr) =
          .base (GeneratedCollectionEquationModel.parallelRule color).category from
            by cases color <;> rfl) ▸
        nullary (GeneratedCollectionEquationModel.unitRule color)
          (GeneratedCollectionEquationModel.unit_member color) (by cases color <;> rfl) := by
  have same := unit_row_unique color
    (Classical.choose (declaration.unitAuthored (GeneratedCollectionEquationModel.unitName color) rfl))
    (Classical.choose_spec
      (declaration.unitAuthored (GeneratedCollectionEquationModel.unitName color) rfl)).1
    (Classical.choose_spec
      (declaration.unitAuthored (GeneratedCollectionEquationModel.unitName color) rfl)).2.1
  dsimp only [declaredUnit]
  exact nullary_transport same
    (Classical.choose_spec
      (declaration.unitAuthored (GeneratedCollectionEquationModel.unitName color) rfl)).1
    (GeneratedCollectionEquationModel.unit_member color)
    (Classical.choose_spec
      (declaration.unitAuthored (GeneratedCollectionEquationModel.unitName color) rfl)).2.2.2
    (by cases color <;> rfl)
    (Classical.choose_spec
      (declaration.unitAuthored (GeneratedCollectionEquationModel.unitName color) rfl)).2.2.1
    (by cases color <;> rfl)

theorem process_ext (color : CostStaticColor) {Γ : List TypeExpr}
    (left right : originalAlgebra.substitution.Carrier Γ
      (.base (GeneratedCollectionEquationModel.parallelRule color).category))
    (same : ∀ (stage : Type) (above : stage ⟶ PUnit)
      (environment : (SemanticAccountValuation.model constructors signatureSort wrappedSort markMeaning).Env
        stage Γ) (point : stage),
        processRead color (left.value stage above environment point) =
          processRead color (right.value stage above environment point)) : left = right := by
  cases color
  all_goals
    apply CategoricalBindingModel.Model.ElemOver.ext
    funext stage above environment
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext point
    exact same stage above environment point

theorem permutation_fold (color : CostStaticColor) {Γ : List TypeExpr}
    (first second : List (Term (signatureOf language) Γ
      (.base (GeneratedCollectionEquationModel.parallelRule color).category)))
    (permutation : first.Perm second) :
    interpret (node (GeneratedCollectionEquationModel.parallelRule color)
      (GeneratedCollectionEquationModel.parallel_member color) "ps" .hashBag
      (GeneratedCollectionEquationModel.parallel_shape color) first) =
    interpret (node (GeneratedCollectionEquationModel.parallelRule color)
      (GeneratedCollectionEquationModel.parallel_member color) "ps" .hashBag
      (GeneratedCollectionEquationModel.parallel_shape color) second) := by
  apply process_ext color
  intro stage above environment point
  rw [node_value, node_value]
  exact (permutation.map (fun value => processRead color
    ((interpret value).value stage above environment point))).sum_eq

theorem flatten_fold (color : CostStaticColor) {Γ : List TypeExpr}
    (pre inner post : List (Term (signatureOf language) Γ
      (.base (GeneratedCollectionEquationModel.parallelRule color).category))) :
    interpret (node (GeneratedCollectionEquationModel.parallelRule color)
      (GeneratedCollectionEquationModel.parallel_member color) "ps" .hashBag
      (GeneratedCollectionEquationModel.parallel_shape color)
      (pre ++ node (GeneratedCollectionEquationModel.parallelRule color)
        (GeneratedCollectionEquationModel.parallel_member color) "ps" .hashBag
        (GeneratedCollectionEquationModel.parallel_shape color) inner :: post)) =
    interpret (node (GeneratedCollectionEquationModel.parallelRule color)
      (GeneratedCollectionEquationModel.parallel_member color) "ps" .hashBag
      (GeneratedCollectionEquationModel.parallel_shape color) (pre ++ inner ++ post)) := by
  apply process_ext color
  intro stage above environment point
  rw [node_value, node_value]
  simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons, add_assoc]
  exact congrArg (fun occurrences =>
    (pre.map (fun value => processRead color ((interpret value).value stage above environment point))).sum +
      (occurrences +
        (post.map (fun value => processRead color ((interpret value).value stage above environment point))).sum))
    (node_value color inner stage above environment point)

theorem singleton_fold (color : CostStaticColor) {Γ : List TypeExpr}
    (value : Term (signatureOf language) Γ
      (.base (GeneratedCollectionEquationModel.parallelRule color).category)) :
    interpret (node (GeneratedCollectionEquationModel.parallelRule color)
      (GeneratedCollectionEquationModel.parallel_member color) "ps" .hashBag
      (GeneratedCollectionEquationModel.parallel_shape color) [value]) = interpret value := by
  apply process_ext color
  intro stage above environment point
  rw [node_value]
  exact add_zero _

theorem nullary_unit_value (color : CostStaticColor) {Γ : List TypeExpr}
    (stage : Type) (above : stage ⟶ PUnit)
    (environment : (SemanticAccountValuation.model constructors signatureSort wrappedSort markMeaning).Env
      stage Γ) (point : stage) :
    processRead color ((interpret ((show
      (.base (GeneratedCollectionEquationModel.unitRule color).category : TypeExpr) =
        TypeExpr.base (GeneratedCollectionEquationModel.parallelRule color).category from
          by cases color <;> rfl) ▸
      nullary (GeneratedCollectionEquationModel.unitRule color)
        (GeneratedCollectionEquationModel.unit_member color) (by cases color <;> rfl))).value
        stage above environment point) = 0 := by
  cases color <;> rfl

theorem declared_unit_value (color : CostStaticColor)
    (declaration : AlgebraRule language (GeneratedCollectionEquationModel.parallelRule color)
      .hashBag (GeneratedCollectionEquationModel.parallelAlgebra color)) {Γ : List TypeExpr}
    (stage : Type) (above : stage ⟶ PUnit)
    (environment : (SemanticAccountValuation.model constructors signatureSort wrappedSort markMeaning).Env
      stage Γ) (point : stage) :
    processRead color ((interpret (declaredUnit (GeneratedCollectionEquationModel.parallelRule color)
      .hashBag (GeneratedCollectionEquationModel.parallelAlgebra color) declaration
      (GeneratedCollectionEquationModel.unitName color) rfl)).value stage above environment point) = 0 := by
  exact (congrArg (fun value => processRead color
      ((interpret value).value stage above environment point)) (declared_unit_eq color declaration)).trans
    (nullary_unit_value color stage above environment point)

theorem unit_elimination_fold (color : CostStaticColor)
    (declaration : AlgebraRule language (GeneratedCollectionEquationModel.parallelRule color)
      .hashBag (GeneratedCollectionEquationModel.parallelAlgebra color)) {Γ : List TypeExpr}
    (pre post : List (Term (signatureOf language) Γ
      (.base (GeneratedCollectionEquationModel.parallelRule color).category))) :
    interpret (node (GeneratedCollectionEquationModel.parallelRule color)
      (GeneratedCollectionEquationModel.parallel_member color) "ps" .hashBag
      (GeneratedCollectionEquationModel.parallel_shape color)
      (pre ++ declaredUnit (GeneratedCollectionEquationModel.parallelRule color)
        .hashBag (GeneratedCollectionEquationModel.parallelAlgebra color) declaration
        (GeneratedCollectionEquationModel.unitName color) rfl :: post)) =
    interpret (node (GeneratedCollectionEquationModel.parallelRule color)
      (GeneratedCollectionEquationModel.parallel_member color) "ps" .hashBag
      (GeneratedCollectionEquationModel.parallel_shape color) (pre ++ post)) := by
  apply process_ext color
  intro stage above environment point
  rw [node_value, node_value]
  simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons]
  have unit := declared_unit_value color declaration stage above environment point
  rw [unit, zero_add]

theorem empty_unit_fold (color : CostStaticColor)
    (declaration : AlgebraRule language (GeneratedCollectionEquationModel.parallelRule color)
      .hashBag (GeneratedCollectionEquationModel.parallelAlgebra color)) (Γ : List TypeExpr) :
    interpret (node (GeneratedCollectionEquationModel.parallelRule color)
      (GeneratedCollectionEquationModel.parallel_member color) "ps" .hashBag
      (GeneratedCollectionEquationModel.parallel_shape color) (Γ := Γ) []) =
    interpret (declaredUnit (GeneratedCollectionEquationModel.parallelRule color)
      .hashBag (GeneratedCollectionEquationModel.parallelAlgebra color) declaration
      (GeneratedCollectionEquationModel.unitName color) rfl) := by
  apply process_ext color
  intro stage above environment point
  rw [node_value]
  exact (declared_unit_value color declaration stage above environment point).symm

/-- Every intrinsic producer law holds before substituting an arbitrary full
semantic environment. No coherence of alternative erased elaborations is used. -/
theorem generator_fold (generator : CollectionEquationGenerators.Generator language) :
    interpret generator.declaration.left = interpret generator.declaration.right := by
  cases generator with
  | bagPermutation row first second permutation =>
      rcases row with ⟨rule, member, parameter, shape⟩
      obtain ⟨color, same, name, _⟩ := row_classification ⟨rule, member, parameter, shape⟩
      change rule = _ at same
      change parameter = "ps" at name
      subst rule parameter
      exact permutation_fold color first second permutation
  | setPermutation row first second permutation =>
      obtain ⟨_, _, _, impossible⟩ := row_classification row
      cases impossible
  | setDeduplication row value rest =>
      obtain ⟨_, _, _, impossible⟩ := row_classification row
      cases impossible
  | flattening row account declaration enabled pre inner post =>
      rcases row with ⟨rule, member, parameter, shape⟩
      obtain ⟨color, same, name, kind⟩ := row_classification ⟨rule, member, parameter, shape⟩
      change rule = _ at same
      change parameter = "ps" at name
      subst rule parameter
      cases kind
      exact flatten_fold color pre inner post
  | singletonCollapse row account declaration enabled value =>
      rcases row with ⟨rule, member, parameter, shape⟩
      obtain ⟨color, same, name, kind⟩ := row_classification ⟨rule, member, parameter, shape⟩
      change rule = _ at same
      change parameter = "ps" at name
      subst rule parameter
      cases kind
      exact singleton_fold color value
  | unitElimination row account declaration unit selected pre post =>
      rcases row with ⟨rule, member, parameter, shape⟩
      obtain ⟨color, same, name, kind⟩ := row_classification ⟨rule, member, parameter, shape⟩
      change rule = _ at same
      change parameter = "ps" at name
      subst rule parameter
      cases kind
      have sameAccount := parallel_algebra_unique color account declaration
      subst account
      have sameUnit : GeneratedCollectionEquationModel.unitName color = unit := Option.some.inj selected
      subst unit
      exact unit_elimination_fold color declaration pre post
  | emptyUnit row account declaration unit selected context =>
      rcases row with ⟨rule, member, parameter, shape⟩
      obtain ⟨color, same, name, kind⟩ := row_classification ⟨rule, member, parameter, shape⟩
      change rule = _ at same
      change parameter = "ps" at name
      subst rule parameter
      cases kind
      have sameAccount := parallel_algebra_unique color account declaration
      subst account
      have sameUnit : GeneratedCollectionEquationModel.unitName color = unit := Option.some.inj selected
      subst unit
      exact empty_unit_fold color declaration context

/-- The law survives arbitrary ordinary substitutions, including supplied
functions and account-bearing values under the actual declared binders. -/
theorem full_collection_laws : BindingEquationFamilyModel.Satisfies originalAlgebra
    (CollectionEquationGenerators.family language) := by
  intro equation admitted Θ Γ valuation ambient ordinary
  obtain ⟨generator, rfl⟩ := admitted
  change SemanticContextualMetavariables.interpretSchema originalAlgebra valuation ambient ordinary
      (embed generator.declaration.left) =
    SemanticContextualMetavariables.interpretSchema originalAlgebra valuation ambient ordinary
      (embed generator.declaration.right)
  exact (BindingPureContextualInterpretation.interpret_embed originalAlgebra valuation ambient ordinary
    generator.declaration.left).trans
    ((congrArg (originalAlgebra.substitution.substitute ordinary) (generator_fold generator)).trans
      (BindingPureContextualInterpretation.interpret_embed originalAlgebra valuation ambient ordinary
        generator.declaration.right).symm)

/-- Name is explicitly a one-point observation in this account model, even
when the surrounding environment supplies arbitrary mixed function values. -/
theorem name_subsingleton (Γ : List TypeExpr) :
    Subsingleton (originalAlgebra.substitution.Carrier Γ GeneratedEquationPresentation.nameSort) := by
  constructor
  intro left right
  apply CategoricalBindingModel.Model.ElemOver.ext
  funext stage above environment
  apply TypeCat.Hom.ext
  apply TypeCat.Fun.ext
  funext point
  change @Eq PUnit _ _
  exact Subsingleton.elim _ _

/-- The source rows remain separate from the provenance-indexed collection
laws. This does not replace the broader erased-boundary presentation. -/
def originalFamily (equation : EqAxiom (signatureOf language) []) : Prop :=
  equation ∈ GeneratedEquationPresentation.equations ∨
    CollectionEquationGenerators.family language equation

theorem included_in_boundary_family {equation : EqAxiom (signatureOf language) []}
    (admitted : originalFamily equation) : GeneratedCollectionEquationModel.family equation := by
  rcases admitted with source | collection
  · exact Or.inl source
  · exact Or.inr (CollectionEquationGenerators.included_in_boundary_family collection)

theorem full_original_laws : BindingEquationFamilyModel.Satisfies originalAlgebra originalFamily := by
  intro equation admitted Θ Γ valuation ambient ordinary
  rcases admitted with source | collection
  · simp only [GeneratedEquationPresentation.equations, List.mem_cons,
      List.mem_nil_iff, or_false] at source
    rcases source with rfl | rfl
    all_goals exact (name_subsingleton Γ).elim _ _
  · exact full_collection_laws equation collection valuation ambient ordinary

noncomputable abbrev originalQuotient := BindingEquationFamilyModel.algebra originalFamily

/-- The quotient maps into an independently specified occurrence model;
this descent is justified by the full contextual satisfaction theorem. -/
noncomputable def readout : FreeBindingClone.Hom originalQuotient originalAlgebra :=
  BindingEquationFamilyModel.interpretHom originalFamily originalAlgebra full_original_laws

theorem readout_project {Γ : List TypeExpr} {sort : TypeExpr}
    (value : Term (signatureOf language) Γ sort) :
    readout.raw.map (BindingEquationFamilyModel.project originalFamily value) = interpret value := rfl

theorem readout_substitute {Γ Δ : List TypeExpr} {sort : TypeExpr}
    (environment : BindingSubstitutionAlgebra.Environment (signatureOf language)
      originalQuotient.substitution.Carrier Γ Δ)
    (value : originalQuotient.substitution.Carrier Γ sort) :
    readout.raw.map (originalQuotient.substitution.substitute environment value) =
      originalAlgebra.substitution.substitute
        (fun type position => readout.raw.map (environment type position)) (readout.raw.map value) :=
  readout.map_substitute environment value

/-- Provenance generators also map to the already existing broader quotient.
No inverse or adequacy of arbitrary erased endpoint elaborations is inferred. -/
noncomputable def toBoundaryQuotient :
    FreeBindingClone.Hom originalQuotient GeneratedCollectionEquationModel.algebra :=
  BindingEquationFamilyModel.interpretHom originalFamily GeneratedCollectionEquationModel.algebra
    (fun equation admitted {_ _} valuation ambient ordinary =>
      GeneratedCollectionEquationModel.full_contextual_satisfaction equation
        (included_in_boundary_family admitted) valuation ambient ordinary)

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.SemanticAccountCollectionModel
