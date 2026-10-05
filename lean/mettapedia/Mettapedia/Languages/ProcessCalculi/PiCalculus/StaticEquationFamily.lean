import Mettapedia.Languages.ProcessCalculi.PiCalculus.StaticEquations
import Mettapedia.Languages.ProcessCalculi.PiCalculus.AuthoredSemantics
import Mettapedia.GSLT.LanguageDef.BindingCollectionEquationGenerators

/-!
# Scope equations and generated parallel laws in one binding family

The four typed static schemas and the actual collection generators of
`piCalc` inhabit one equation family. A generated declaration supplies its
own typed endpoints, context, and result category; embedding those endpoints
uses ordinary variables and leaves the static schemas' metavariables unused.
The established finite-fragment congruence and binding-family model therefore
combine both kinds of laws without changing their instantiation machinery.

This is an intrinsic static presentation. It does not change the live raw
equations, compile binding schemas into the executor, or establish comparison
with the full named structural-congruence quotient.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PiCalculus.StaticEquationFamily

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.BindingEquationFamilyCongruence
open Mettapedia.GSLT.LanguageDef.BindingSyntax
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance
open StaticEquations

universe u

/-- The producer's exact intrinsic endpoints are embedded into the same
metavariable signature as the four scope and unfolding schemas. -/
noncomputable def collectionAxiom (generator : CollectionEquationGenerators.Generator piCalc) :
    EqAxiom signature metavariables where
  ctx := generator.declaration.context
  sort := .base generator.declaration.category
  lhs := embed generator.declaration.left
  rhs := embed generator.declaration.right

/-- Only the four declared schemas and actual collection producers supply
axioms; alternative intrinsic elaborations of an erased endpoint do not. -/
def family (equation : EqAxiom signature metavariables) : Prop :=
  equation ∈ StaticEquations.equations ∨
    ∃ generator : CollectionEquationGenerators.Generator piCalc,
      collectionAxiom generator = equation

theorem static_admitted {equation : EqAxiom signature metavariables}
    (member : equation ∈ StaticEquations.equations) : family equation := .inl member

theorem generated_admitted (generator : CollectionEquationGenerators.Generator piCalc) :
    family (collectionAxiom generator) := .inr ⟨generator, rfl⟩

/-- Existing contextual derivations use their original finite list unchanged. -/
theorem of_static {Γ : Ctx signature} {sort : TypeExpr}
    {left right : Term signature Γ sort}
    (proof : EqClosure StaticEquations.equations left right) : Related family left right :=
  ⟨StaticEquations.equations, fun _ member => static_admitted member, proof⟩

/-- Every admitted schema instance enters the established family relation
through one supported axiom fragment. -/
theorem admitted_instance (equation : EqAxiom signature metavariables)
    (admitted : family equation) {Θ Γ : Ctx signature}
    (body : ContextualAssignment signature metavariables Θ)
    (ambient : Sub signature Θ Γ) (ordinary : Sub signature equation.ctx Γ) :
    Related family
      (ContextualAssignment.instantiate body ambient ordinary equation.lhs)
      (ContextualAssignment.instantiate body ambient ordinary equation.rhs) := by
  refine ⟨[equation], ?_, ?_⟩
  · intro candidate member
    obtain rfl := List.mem_singleton.mp member
    exact admitted
  · exact EqClosure.ax (E := [equation]) ⟨0, by simp⟩ body ambient ordinary

/-- A generated declaration's embedded endpoints commute with the ordinary
substitution and do not inspect either kind of metavariable environment. -/
theorem generated_interpretation
    (generator : CollectionEquationGenerators.Generator piCalc) {Θ Γ : Ctx signature}
    (body : ContextualAssignment signature metavariables Θ)
    (ambient : Sub signature Θ Γ)
    (ordinary : Sub signature generator.declaration.context Γ) :
    ContextualAssignment.instantiate body ambient ordinary (collectionAxiom generator).lhs =
        bind ordinary generator.declaration.left ∧
      ContextualAssignment.instantiate body ambient ordinary (collectionAxiom generator).rhs =
        bind ordinary generator.declaration.right :=
  ⟨ContextualAssignment.instantiate_embed body ambient ordinary _,
    ContextualAssignment.instantiate_embed body ambient ordinary _⟩

/-- Every actual generated collection declaration has all ordinary-variable
instances, in arbitrary target contexts. -/
theorem generated_instance
    (generator : CollectionEquationGenerators.Generator piCalc) {Γ : Ctx signature}
    (ordinary : Sub signature generator.declaration.context Γ) :
    Related family (bind ordinary generator.declaration.left)
      (bind ordinary generator.declaration.right) := by
  let body : ContextualAssignment signature metavariables Γ :=
    assignment nilTerm nilTerm nilTerm nilTerm
  have proof := admitted_instance (collectionAxiom generator) (generated_admitted generator)
    body (fun _ position => .var position) ordinary
  obtain ⟨left, right⟩ := generated_interpretation generator body
    (fun _ position => .var position) ordinary
  exact Eq.mp (congrArg₂ (fun first second => Related family first second) left right) proof

theorem generated_law (generator : CollectionEquationGenerators.Generator piCalc) :
    Related family generator.declaration.left generator.declaration.right := by
  simpa only [bind_id] using generated_instance generator (fun _ position => .var position)

theorem restrict_inaction (Γ : Ctx signature) :
    Related family (restrictionTerm (nilTerm (Γ := processSort :: Γ)))
      (nilTerm (Γ := Γ)) :=
  of_static (StaticEquations.restrict_inaction Γ)

theorem exchange_scopes {Γ : Ctx signature}
    (body : Term signature (processSort :: processSort :: Γ) processSort) :
    Related family (restrictionTerm (restrictionTerm body))
      (restrictionTerm (restrictionTerm (rename exchangeRestrictions body))) :=
  of_static (StaticEquations.exchange_scopes body)

theorem extrude_scope {Γ : Ctx signature}
    (inside : Term signature (processSort :: Γ) processSort)
    (outside : Term signature Γ processSort) :
    Related family
      (restrictionTerm (parallelTerm inside (weaken outside)))
      (parallelTerm (restrictionTerm inside) outside) :=
  of_static (StaticEquations.extrude_scope inside outside)

theorem unfold_guarded {Γ : Ctx signature}
    (channel : Term signature Γ processSort)
    (body : Term signature (processSort :: Γ) processSort) :
    Related family (replicationTerm channel body)
      (parallelTerm (inputTerm channel body) (replicationTerm channel body)) :=
  of_static (StaticEquations.unfold_guarded channel body)

/-- Both parts of the combined family use the existing binder-preserving
substitution action on their entire congruence. -/
theorem substitution {Γ Δ : Ctx signature} {sort : TypeExpr}
    {left right : Term signature Γ sort} (ordinary : Sub signature Γ Δ)
    (proof : Related family left right) :
    Related family (bind ordinary left) (bind ordinary right) :=
  Related.bind ordinary proof

theorem rename_relation {Γ Δ : Ctx signature} {sort : TypeExpr}
    {left right : Term signature Γ sort} (rho : Ren signature Γ Δ)
    (proof : Related family left right) :
    Related family (rename rho left) (rename rho right) :=
  Related.rename rho proof

def parallelRow : CollectionEquationGenerators.Row piCalc .hashBag where
  rule := piCalc.terms[1]
  member := List.getElem_mem (by decide)
  parameter := "ps"
  shape := rfl

/-- A collection producer cannot obtain authority from a different row or
collection kind in the authored pi signature. -/
theorem collection_row_exact {kind : CollType}
    (row : CollectionEquationGenerators.Row piCalc kind) :
    row.rule = piCalc.terms[1] ∧ kind = .hashBag :=
  piBagTheory.carrier ⟨row.member, ⟨row.parameter, _, row.shape⟩⟩

theorem no_set_row : ¬ Nonempty (CollectionEquationGenerators.Row piCalc .hashSet) := by
  rintro ⟨row⟩
  have impossible := (collection_row_exact row).2
  cases impossible

/-- The actual authored parallel row at the supplied finite arity. -/
def parallelBag {Γ : Ctx signature} (components : List (Term signature Γ processSort)) :
    Term signature Γ processSort :=
  CollectionEquationFamily.node parallelRow.rule parallelRow.member
    parallelRow.parameter .hashBag parallelRow.shape components

@[simp] theorem parallelBag_pair {Γ : Ctx signature}
    (left right : Term signature Γ processSort) :
    parallelBag [left, right] = parallelTerm left right := rfl

theorem parallel_permutation {Γ : Ctx signature}
    (first second : List (Term signature Γ processSort)) (permutation : first.Perm second) :
    Related family (parallelBag first) (parallelBag second) :=
  generated_law (.bagPermutation parallelRow first second permutation)

theorem parallel_comm {Γ : Ctx signature} (left right : Term signature Γ processSort) :
    Related family (parallelTerm left right) (parallelTerm right left) :=
  parallel_permutation [left, right] [right, left] (.swap right left [])

theorem parallel_flatten {Γ : Ctx signature}
    (pre inner post : List (Term signature Γ processSort)) :
    Related family (parallelBag (pre ++ parallelBag inner :: post))
      (parallelBag (pre ++ inner ++ post)) :=
  generated_law (.flattening parallelRow { flatten := true, unit := some "PiNil" }
    piBagTheory.bagAlgebraRule rfl pre inner post)

theorem parallel_assoc {Γ : Ctx signature}
    (first second third : Term signature Γ processSort) :
    Related family (parallelTerm (parallelTerm first second) third)
      (parallelTerm first (parallelTerm second third)) := by
  have left := parallel_flatten (Γ := Γ) [] [first, second] [third]
  have right := parallel_flatten (Γ := Γ) [first] [second, third] []
  exact Related.trans left (Related.symm right)

/-- Permute inside a restriction using the actual bag generator, then apply
the freshness-enforcing static extrusion schema in the same congruence. -/
theorem extrude_after_permutation {Γ : Ctx signature}
    (inside : Term signature (processSort :: Γ) processSort)
    (outside : Term signature Γ processSort) :
    Related family (restrictionTerm (parallelTerm (weaken outside) inside))
      (parallelTerm (restrictionTerm inside) outside) := by
  have rearranged := Related.operation restrictionOperator
    (RelatedArgs.cons (parallel_comm (weaken outside) inside) .nil)
  exact Related.trans rearranged (extrude_scope inside outside)

/-- The combined presentation uses the existing full binding-family model. -/
noncomputable abbrev algebra := BindingEquationFamilyModel.algebra family

theorem full_contextual_satisfaction :
    BindingEquationFamilyModel.Satisfies algebra family :=
  BindingEquationFamilyModel.algebra_satisfies family

theorem project_eq_of_related {Γ : Ctx signature} {sort : TypeExpr}
    {left right : Term signature Γ sort} (proof : Related family left right) :
    BindingEquationFamilyModel.project family left = BindingEquationFamilyModel.project family right :=
  Quotient.sound proof

/-- The quotient identifies a term using both the generated parallel law and
the binder-aware scope law, rather than interpreting each in a separate model. -/
theorem extruded_permutation_projects_equal {Γ : Ctx signature}
    (inside : Term signature (processSort :: Γ) processSort)
    (outside : Term signature Γ processSort) :
    BindingEquationFamilyModel.project family
        (restrictionTerm (parallelTerm (weaken outside) inside)) =
      BindingEquationFamilyModel.project family (parallelTerm (restrictionTerm inside) outside) :=
  project_eq_of_related (extrude_after_permutation inside outside)

end Mettapedia.Languages.ProcessCalculi.PiCalculus.StaticEquationFamily
