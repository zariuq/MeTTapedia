import Mettapedia.GSLT.LanguageDef.CertificateGSLTSemanticFunctionObject
import Mettapedia.GSLT.Topos.PresheafPredicateReification

/-!
# Function predicates on contextual certificate programs

An open certificate map from a context extended by input premises is an
actual source program. The existing internal-hom comparison interprets it
as a semantic function. This file identifies semantic evaluation with
source proof substitution and pulls the total-category function predicate
back to these programs. Membership is characterized by preservation of
the input predicate under every contextual substitution, not by a test at
one environment.

This uses the existing certificate syntax and its ordered context product.
It does not add a function-type constructor to that syntax or assert that
the semantic internal hom is represented by an authored context.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLT

open CategoryTheory MonoidalCategory
open Mettapedia.GSLT.Topos

variable {definition : ValidatedCalculusLanguageDef}

/-- Interpreting a contextual source program and evaluating it at an
argument is exactly substitution of the environment and argument into its
ordered premise context. -/
theorem contextualFunction_evaluation
    (context input output : ClassifyingContext definition)
    (body : ClassifyingContext.concat context input ⟶ output)
    (stage : ClassifyingContext definition)
    (environment : stage ⟶ context) (argument : stage ⟶ input) :
    (((contextualFunctionObjectEquiv context input output).symm body).app
        (Opposite.op stage) (Quiver.Hom.op environment)) argument =
      ClassifyingContext.pair environment argument ≫ body := by
  change ClassifyingContext.pair
      ((𝟙 (Opposite.op context) ≫ Quiver.Hom.op environment).unop)
      argument ≫ body = _
  rw [Category.id_comp, Quiver.Hom.unop_op]

/-- The function predicate on the actual presheaf of open certificate
programs, using the established natural isomorphism rather than assuming
a representation witness. -/
noncomputable def contextualFunctionPredicate
    (input output : ClassifyingContext definition)
    (source : Subfunctor (yoneda.obj input))
    (target : Subfunctor (yoneda.obj output)) :
    Subfunctor (contextualFunctionFace definition input output) :=
  (expPredicate (totalOfPredicate (yoneda.obj input) source)
    (totalOfPredicate (yoneda.obj output) target)).preimage
      (contextualFunctionFaceIso definition input output).inv

/-- The abstract exponential predicate says exactly that every source
proof satisfying the argument contract is taken to a proof satisfying the
result contract, after any substitution of the program's environment. -/
theorem mem_contextualFunctionPredicate
    (context input output : ClassifyingContext definition)
    (source : Subfunctor (yoneda.obj input))
    (target : Subfunctor (yoneda.obj output))
    (body : ClassifyingContext.concat context input ⟶ output) :
    body ∈ (contextualFunctionPredicate input output source target).obj
        (Opposite.op context) ↔
      ∀ (stage : ClassifyingContext definition)
        (environment : stage ⟶ context) (argument : stage ⟶ input),
        argument ∈ source.obj (Opposite.op stage) →
          ClassifyingContext.pair environment argument ≫ body ∈
            target.obj (Opposite.op stage) := by
  refine (mem_expPredicate (totalOfPredicate (yoneda.obj input) source)
    (totalOfPredicate (yoneda.obj output) target) (Opposite.op context)
    ((contextualFunctionFaceIso definition input output).inv.app
      (Opposite.op context) body)).trans ?_
  constructor
  · intro held stage environment argument accepted
    have result := held (Opposite.op stage) (Quiver.Hom.op environment)
      argument accepted
    change (((contextualFunctionObjectEquiv context input output).symm body).app
      (Opposite.op stage) (Quiver.Hom.op environment ≫ 𝟙 _)) argument ∈ _ at result
    rw [Category.comp_id, contextualFunction_evaluation] at result
    exact result
  · intro held stage environment argument accepted
    change (((contextualFunctionObjectEquiv context input output).symm body).app
      stage (environment ≫ 𝟙 _)) argument ∈ _
    rw [Category.comp_id]
    have result := held stage.unop environment.unop argument accepted
    rw [← contextualFunction_evaluation] at result
    simpa only [Quiver.Hom.op_unop] using result

/-- Reindexing is precisely the existing extension of a proof substitution
over the untouched input block. Function-contract evidence survives it. -/
theorem contextualFunctionPredicate_substitution
    (input output : ClassifyingContext definition)
    (source : Subfunctor (yoneda.obj input))
    (target : Subfunctor (yoneda.obj output))
    {context context' : ClassifyingContext definition}
    (substitution : context' ⟶ context)
    (body : ClassifyingContext.concat context input ⟶ output)
    (held : body ∈ (contextualFunctionPredicate input output source target).obj
      (Opposite.op context)) :
    extendContextRight input substitution ≫ body ∈
      (contextualFunctionPredicate input output source target).obj
        (Opposite.op context') :=
  (contextualFunctionPredicate input output source target).map
    (Quiver.Hom.op substitution) held

/-- The program returning its input proof preserves any predicate on that
proof, independently of the surrounding environment. -/
theorem argument_program_preserves_predicate
    (context input : ClassifyingContext definition)
    (predicate : Subfunctor (yoneda.obj input)) :
    ClassifyingContext.sndProjection context input ∈
      (contextualFunctionPredicate input input predicate predicate).obj
        (Opposite.op context) := by
  rw [mem_contextualFunctionPredicate]
  intro stage environment argument held
  simpa only [ClassifyingContext.pair_snd] using held

/-- Compose two open certificate programs, retaining the shared
environment while passing the first program's output to the second. -/
def composeContextualPrograms
    {context input middle output : ClassifyingContext definition}
    (first : ClassifyingContext.concat context input ⟶ middle)
    (second : ClassifyingContext.concat context middle ⟶ output) :
    ClassifyingContext.concat context input ⟶ output :=
  ClassifyingContext.pair (ClassifyingContext.fstProjection context input)
    first ≫ second

@[simp] theorem composeContextualPrograms_right_identity
    {context input output : ClassifyingContext definition}
    (body : ClassifyingContext.concat context input ⟶ output) :
    composeContextualPrograms body
        (ClassifyingContext.sndProjection context output) = body :=
  ClassifyingContext.pair_snd _ _

@[simp] theorem composeContextualPrograms_left_identity
    {context input output : ClassifyingContext definition}
    (body : ClassifyingContext.concat context input ⟶ output) :
    composeContextualPrograms
        (ClassifyingContext.sndProjection context input) body = body := by
  have projections : ClassifyingContext.pair
      (ClassifyingContext.fstProjection context input)
      (ClassifyingContext.sndProjection context input) =
        𝟙 (ClassifyingContext.concat context input) := by
    simpa using ClassifyingContext.pair_eta
      (𝟙 (ClassifyingContext.concat context input))
  rw [composeContextualPrograms, projections, Category.id_comp]

/-- Source program composition is associative with the environment shared
at every stage. -/
theorem composeContextualPrograms_assoc
    {context input middle next output : ClassifyingContext definition}
    (first : ClassifyingContext.concat context input ⟶ middle)
    (second : ClassifyingContext.concat context middle ⟶ next)
    (third : ClassifyingContext.concat context next ⟶ output) :
    composeContextualPrograms (composeContextualPrograms first second) third =
      composeContextualPrograms first (composeContextualPrograms second third) := by
  simp only [composeContextualPrograms, ← Category.assoc,
    ClassifyingContext.comp_pair, ClassifyingContext.pair_fst]

/-- Substituting a shared environment commutes with source composition. -/
theorem composeContextualPrograms_substitution
    {context context' input middle output : ClassifyingContext definition}
    (substitution : context' ⟶ context)
    (first : ClassifyingContext.concat context input ⟶ middle)
    (second : ClassifyingContext.concat context middle ⟶ output) :
    extendContextRight input substitution ≫
        composeContextualPrograms first second =
      composeContextualPrograms (extendContextRight input substitution ≫ first)
        (extendContextRight middle substitution ≫ second) := by
  simp only [composeContextualPrograms, extendContextRight, ← Category.assoc,
    ClassifyingContext.comp_pair, ClassifyingContext.pair_fst,
    ClassifyingContext.pair_snd]

/-- Source composition evaluates by feeding the exact intermediate
certificate to the second program. -/
theorem composeContextualPrograms_evaluation
    {context input middle output stage : ClassifyingContext definition}
    (first : ClassifyingContext.concat context input ⟶ middle)
    (second : ClassifyingContext.concat context middle ⟶ output)
    (environment : stage ⟶ context) (argument : stage ⟶ input) :
    ClassifyingContext.pair environment argument ≫
        composeContextualPrograms first second =
      ClassifyingContext.pair environment
        (ClassifyingContext.pair environment argument ≫ first) ≫ second := by
  simp only [composeContextualPrograms, ← Category.assoc,
    ClassifyingContext.comp_pair, ClassifyingContext.pair_fst]

/-- The semantic function contracts are closed under composition of
actual source programs. -/
theorem contextualFunctionPredicate_composition
    {context input middle output : ClassifyingContext definition}
    (source : Subfunctor (yoneda.obj input))
    (intermediate : Subfunctor (yoneda.obj middle))
    (target : Subfunctor (yoneda.obj output))
    (first : ClassifyingContext.concat context input ⟶ middle)
    (second : ClassifyingContext.concat context middle ⟶ output)
    (firstHeld : first ∈
      (contextualFunctionPredicate input middle source intermediate).obj
        (Opposite.op context))
    (secondHeld : second ∈
      (contextualFunctionPredicate middle output intermediate target).obj
        (Opposite.op context)) :
    composeContextualPrograms first second ∈
      (contextualFunctionPredicate input output source target).obj
        (Opposite.op context) := by
  rw [mem_contextualFunctionPredicate] at firstHeld secondHeld ⊢
  intro stage environment argument held
  rw [composeContextualPrograms_evaluation]
  exact secondHeld stage environment _ (firstHeld stage environment argument held)

/-- Evaluate a predicate on source programs against a predicate on input
proofs, via the established source-to-internal-hom isomorphism. -/
noncomputable def applyContextualPredicate
    (input output : ClassifyingContext definition)
    (programs : Subfunctor (contextualFunctionFace definition input output))
    (arguments : Subfunctor (yoneda.obj input)) :
    Subfunctor (yoneda.obj output) :=
  applyPred (totalOfPredicate (yoneda.obj input) ⊤)
    (totalOfPredicate (yoneda.obj output) ⊤)
    (programs.image (contextualFunctionFaceIso definition input output).inv)
    arguments

/-- The evaluation transformer contains precisely the outputs of admitted
source programs on admitted arguments at the same stage. Both witnesses
are retained in this characterization, and evaluation is source substitution. -/
theorem mem_applyContextualPredicate
    (input output stage : ClassifyingContext definition)
    (programs : Subfunctor (contextualFunctionFace definition input output))
    (arguments : Subfunctor (yoneda.obj input))
    (result : stage ⟶ output) :
    result ∈ (applyContextualPredicate input output programs arguments).obj
        (Opposite.op stage) ↔
      ∃ (argument : stage ⟶ input)
        (body : ClassifyingContext.concat stage input ⟶ output),
        argument ∈ arguments.obj (Opposite.op stage) ∧
        body ∈ programs.obj (Opposite.op stage) ∧
        ClassifyingContext.pair (𝟙 stage) argument ≫ body = result := by
  constructor
  · rintro ⟨⟨argument, function⟩, ⟨argumentHeld, ⟨body, bodyHeld, same⟩⟩, value⟩
    change (contextualFunctionFaceIso definition input output).inv.app
      (Opposite.op stage) body = function at same
    subst function
    refine ⟨argument, body, argumentHeld, bodyHeld, ?_⟩
    change (((contextualFunctionObjectEquiv stage input output).symm body).app
      (Opposite.op stage) (𝟙 _)) argument = result at value
    have evaluation := contextualFunction_evaluation stage input output body
      stage (𝟙 stage) argument
    rw [op_id] at evaluation
    exact evaluation.symm.trans value
  · rintro ⟨argument, body, argumentHeld, bodyHeld, value⟩
    refine ⟨(argument,
      (contextualFunctionFaceIso definition input output).inv.app
        (Opposite.op stage) body),
      ⟨argumentHeld, ⟨body, bodyHeld, rfl⟩⟩, ?_⟩
    change (((contextualFunctionObjectEquiv stage input output).symm body).app
      (Opposite.op stage) (𝟙 _)) argument = result
    have evaluation := contextualFunction_evaluation stage input output body
      stage (𝟙 stage) argument
    rw [op_id] at evaluation
    exact evaluation.trans value

/-- Reify a predicate transformer into a predicate on actual contextual
source programs, rather than on an unspecified semantic function carrier. -/
noncomputable def reifyContextualPredicate
    (input output : ClassifyingContext definition)
    (transformer : Subfunctor (yoneda.obj input) → Subfunctor (yoneda.obj output)) :
    Subfunctor (contextualFunctionFace definition input output) :=
  (reifyPred (totalOfPredicate (yoneda.obj input) ⊤)
    (totalOfPredicate (yoneda.obj output) ⊤) transformer).preimage
      (contextualFunctionFaceIso definition input output).inv

/-- The full reification adjunction now applies to predicates of authored
open certificate programs. Both sides use the same concrete interpretation. -/
theorem contextual_reify_adjunction
    (input output : ClassifyingContext definition)
    (programs : Subfunctor (contextualFunctionFace definition input output))
    (transformer : Subfunctor (yoneda.obj input) → Subfunctor (yoneda.obj output)) :
    (∀ arguments, applyContextualPredicate input output programs arguments ≤
      transformer arguments) ↔
      programs ≤ reifyContextualPredicate input output transformer := by
  exact (reify_adjunction (totalOfPredicate (yoneda.obj input) ⊤)
    (totalOfPredicate (yoneda.obj output) ⊤) _ transformer).trans
      (Subfunctor.image_le_iff _ _ _)

/-- Reification is exactly the conjunction of the corresponding function
contracts; no extra obligation is inserted at the source boundary. -/
theorem mem_reifyContextualPredicate
    (context input output : ClassifyingContext definition)
    (transformer : Subfunctor (yoneda.obj input) → Subfunctor (yoneda.obj output))
    (body : ClassifyingContext.concat context input ⟶ output) :
    body ∈ (reifyContextualPredicate input output transformer).obj
        (Opposite.op context) ↔
      ∀ predicate : Subfunctor (yoneda.obj input),
        body ∈ (contextualFunctionPredicate input output predicate
          (transformer predicate)).obj (Opposite.op context) := by
  change ((contextualFunctionFaceIso definition input output).inv.app
      (Opposite.op context) body) ∈
    (⨅ predicate : Subfunctor (yoneda.obj input),
      (show Subfunctor ((yoneda.obj input).functorHom (yoneda.obj output)) from
        expPredicate (totalOfPredicate (yoneda.obj input) predicate)
          (totalOfPredicate (yoneda.obj output) (transformer predicate)))).obj
          (Opposite.op context) ↔ _
  rw [Subfunctor.iInf_obj, Set.mem_iInter]
  rfl

/-- The argument program satisfies the nonconstant transformer requiring
preservation of every predicate, not just one selected contract. -/
theorem argument_program_preserves_all_predicates
    (context input : ClassifyingContext definition) :
    ClassifyingContext.sndProjection context input ∈
      (reifyContextualPredicate input input id).obj (Opposite.op context) := by
  rw [mem_reifyContextualPredicate]
  exact argument_program_preserves_predicate context input

#print axioms contextualFunction_evaluation
#print axioms mem_contextualFunctionPredicate
#print axioms contextualFunctionPredicate_substitution
#print axioms argument_program_preserves_predicate
#print axioms composeContextualPrograms_left_identity
#print axioms composeContextualPrograms_right_identity
#print axioms composeContextualPrograms_assoc
#print axioms composeContextualPrograms_substitution
#print axioms composeContextualPrograms_evaluation
#print axioms contextualFunctionPredicate_composition
#print axioms mem_applyContextualPredicate
#print axioms contextual_reify_adjunction
#print axioms mem_reifyContextualPredicate
#print axioms argument_program_preserves_all_predicates

end Mettapedia.GSLT.LanguageDef.CertificateGSLT
