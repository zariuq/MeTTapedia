import Mettapedia.OSLF.Syntax.SemanticContextualMetavariables

/-!
# Interpreting contextual equation instances

The existing contextual semantic fold supplies separate environments for
declared dependency arguments, captured ambient variables and ordinary schema
variables. Its naturality along the actual free binding-clone homomorphism
compares syntactic contextual instantiation with interpretation in every
binding-clone algebra. No additional term traversal is defined here.

Contextual equation satisfaction quantifies over all captured ambient values
and ordinary environments. Its instance soundness uses this comparison;
dependency-only equation satisfaction is a separate condition.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.BindingContextualEquationInterpretation

open Mettapedia.OSLF.Binding.FreeBindingTerms
open Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra (Environment)
open Mettapedia.OSLF.Binding.BindingCloneFoldSubstitution (interpret)
open Mettapedia.OSLF.Binding.BindingEquationalModels (argsEnvironment)
open Mettapedia.OSLF.Binding.SemanticContextualMetavariables

universe u

variable {S : Signature} {M : List (MetaArity S)}

/-- Interpret a syntactic environment using the existing free-clone map. -/
def interpretEnvironment (A : BindingCloneAlgebra.Algebra.{u} S)
    {Γ Δ : Ctx S} (env : Sub S Γ Δ) :
    Environment S A.substitution.Carrier Γ Δ :=
  fun sort x => interpret A (env sort x)

/-- Interpret every contextual body, preserving both blocks of its context. -/
def interpretAssignment (A : BindingCloneAlgebra.Algebra.{u} S)
    {Γ : Ctx S} (body : ContextualAssignment S M Γ) : Valuation (M := M) A Γ :=
  mapValuation (FreeBindingClone.interpretHom A) body

/-- The dependency part of the shared join reads its supplied argument. -/
theorem joinEnvironment_prefix {F : Ctx S → S.Srt → Type u} {Γ Δ : Ctx S} :
    ∀ (dependencies : Ctx S) (arguments : Environment S F dependencies Δ)
      (ambient : Environment S F Γ Δ) (sort : S.Srt) (x : Var dependencies sort),
      joinEnvironment arguments ambient sort (injPrefix dependencies x) =
        arguments sort x
  | [], _, _, _, x => nomatch x
  | _ :: _, _, _, _, .zero => rfl
  | _ :: dependencies, arguments, ambient, sort, .succ x =>
      joinEnvironment_prefix dependencies (fun s v => arguments s (.succ v)) ambient sort x

/-- The captured ambient part of the shared join reads its ambient value. -/
theorem joinEnvironment_ambient {F : Ctx S → S.Srt → Type u} {Γ Δ : Ctx S} :
    ∀ (dependencies : Ctx S) (arguments : Environment S F dependencies Δ)
      (ambient : Environment S F Γ Δ) (sort : S.Srt) (x : Var Γ sort),
      joinEnvironment arguments ambient sort (weakenVar dependencies x) =
        ambient sort x
  | [], _, _, _, _ => rfl
  | _ :: dependencies, arguments, ambient, sort, x =>
      joinEnvironment_ambient dependencies (fun s v => arguments s (.succ v)) ambient sort x

/-- Folding the syntactic join agrees with the one shared semantic join. -/
theorem interpret_joinSub (A : BindingCloneAlgebra.Algebra.{u} S)
    {dependencies Γ Δ : Ctx S} (arguments : Sub S dependencies Δ) (ambient : Sub S Γ Δ) :
    interpretEnvironment A (ContextualAssignment.joinSub arguments ambient) =
      joinEnvironment (interpretEnvironment A arguments) (interpretEnvironment A ambient) := by
  funext sort x
  have mapped := joinEnvironment_map (FreeBindingClone.interpretHom A)
    dependencies arguments ambient sort x
  exact (congrArg (interpret A)
    (congrFun (congrFun (joinEnvironment_terms dependencies arguments ambient) sort) x).symm).trans
      mapped.symm

/-- Syntactic ambient weakening folds to semantic weakening under every
binder list; the captured environment's source remains the ambient context. -/
theorem interpret_weakenSub (A : BindingCloneAlgebra.Algebra.{u} S)
    {Γ Δ : Ctx S} (binders : Ctx S) (ambient : Sub S Γ Δ) :
    interpretEnvironment A (ContextualAssignment.weakenSub binders ambient) =
      weakenEnvironment A binders (interpretEnvironment A ambient) := by
  have mapped := weakenEnvironment_map (FreeBindingClone.interpretHom A) binders ambient
  rw [weakenEnvironment_terms] at mapped
  exact mapped

/-- Ordinary variables use the established binder lift, including the new
projections; it differs from weakening the captured ambient environment. -/
theorem interpret_liftSub (A : BindingCloneAlgebra.Algebra.{u} S)
    {Γ Δ : Ctx S} (ordinary : Sub S Γ Δ) (binders : Ctx S) :
    interpretEnvironment A (liftSub ordinary binders) =
      A.substitution.liftEnvironment (interpretEnvironment A ordinary) binders := by
  funext sort x
  exact (BindingCloneFoldSubstitution.liftedInterpretation_apply A ordinary
    binders sort x).symm

/-- One contextual application commutes with the free-clone interpretation,
with arbitrary argument and ambient substitutions. -/
theorem interpret_apply (A : BindingCloneAlgebra.Algebra.{u} S)
    {Γ Δ : Ctx S} (body : ContextualAssignment S M Γ) (i : Fin M.length)
    (arguments : Sub S (M.get i).1 Δ) (ambient : Sub S Γ Δ) :
    interpret A (ContextualAssignment.apply body i arguments ambient) =
      apply A (interpretAssignment A body i)
        (interpretEnvironment A arguments) (interpretEnvironment A ambient) :=
  (congrArg (FreeBindingClone.interpretHom A).raw.map
    (apply_terms body i arguments ambient).symm).trans
      (apply_map (FreeBindingClone.interpretHom A) (body i) arguments ambient)

/-- Interpreting syntactic contextual instantiation equals the existing
semantic contextual fold at arbitrary ordinary and ambient environments. -/
theorem interpret_instantiate (A : BindingCloneAlgebra.Algebra.{u} S)
    {Γ Ξ Δ : Ctx S} (body : ContextualAssignment S M Γ)
    (ambient : Sub S Γ Δ) (ordinary : Sub S Ξ Δ)
    {sort : S.Srt} (term : Term (withMetas S M) Ξ sort) :
    interpret A (ContextualAssignment.instantiate body ambient ordinary term) =
      interpretSchema A (interpretAssignment A body)
        (interpretEnvironment A ambient) (interpretEnvironment A ordinary) term :=
  (congrArg (FreeBindingClone.interpretHom A).raw.map
    (interpretSchema_terms body ambient ordinary term).symm).trans
      (interpretSchema_map (FreeBindingClone.interpretHom A) body ambient ordinary term)

/-- Every ordered argument, including heads under their declared binders,
has the same syntactic-to-semantic comparison. -/
theorem interpretArgs_instantiateArgs (A : BindingCloneAlgebra.Algebra.{u} S)
    {Γ Ξ Δ : Ctx S} (body : ContextualAssignment S M Γ)
    (ambient : Sub S Γ Δ) (ordinary : Sub S Ξ Δ)
    {arity : List (List S.Srt × S.Srt)} (args : Args (withMetas S M) arity Ξ) :
    BindingCloneFoldSubstitution.interpretArgs A
        (ContextualAssignment.instantiateArgs body ambient ordinary args) =
      interpretArgs A (interpretAssignment A body)
        (interpretEnvironment A ambient) (interpretEnvironment A ordinary) args := by
  have source := congrArg (FamilyArgs.map (FreeBindingClone.interpretHom A).raw.map)
    (interpretArgs_terms body ambient ordinary args).symm
  exact (FreeBindingTerms.homArgs_eq_foldArgs A.toRaw
    (FreeBindingClone.interpretHom A).raw
    (ContextualAssignment.instantiateArgs body ambient ordinary args)).symm.trans
      (source.trans (interpretArgs_map (FreeBindingClone.interpretHom A)
        body ambient ordinary args))

/-- The ordered syntactic argument spine supplies precisely the semantic
dependency environment, without interchanging dependency positions. -/
theorem interpret_argsToSub (A : BindingCloneAlgebra.Algebra.{u} S)
    {dependencies Δ : Ctx S}
    (args : Args S (dependencies.map (fun sort => ([], sort))) Δ) :
    interpretEnvironment A (argsToSub args) =
      argsEnvironment A (BindingCloneFoldSubstitution.interpretArgs A args) := by
  funext sort x
  exact (congrArg (interpret A)
    (argsEnvironment_syntaxToFamily args sort x).symm).trans
      ((BindingEquationInterpretation.argsEnvironment_map
        (FreeBindingClone.interpretHom A) (syntaxToFamily args) sort x).symm.trans
          (congrArg (fun values => argsEnvironment A values sort x)
            (FreeBindingTerms.homArgs_eq_foldArgs A.toRaw
              (FreeBindingClone.interpretHom A).raw args)))

/-- Contextual instantiation and its semantic argument fold give the same
complete environment at every declared dependency position. -/
theorem interpret_contextualArgumentEnvironment (A : BindingCloneAlgebra.Algebra.{u} S)
    {Γ Ξ Δ dependencies : Ctx S} (body : ContextualAssignment S M Γ)
    (ambient : Sub S Γ Δ) (ordinary : Sub S Ξ Δ)
    (args : Args (withMetas S M) (dependencies.map (fun sort => ([], sort))) Ξ) :
    interpretEnvironment A (argsToSub (ContextualAssignment.instantiateArgs body ambient ordinary args)) =
      argsEnvironment A (interpretArgs A (interpretAssignment A body)
        (interpretEnvironment A ambient) (interpretEnvironment A ordinary) args) :=
  (interpret_argsToSub A (ContextualAssignment.instantiateArgs body ambient ordinary args)).trans
    (congrArg (argsEnvironment A) (interpretArgs_instantiateArgs A body ambient ordinary args))

/-- Contextual satisfaction includes arbitrary semantic captured bodies,
ambient environments and ordinary environments. -/
def Satisfies (A : BindingCloneAlgebra.Algebra.{u} S)
    (equations : List (EqAxiom S M)) : Prop :=
  ∀ (i : Fin equations.length) {Γ Δ : Ctx S}
    (body : Valuation (M := M) A Γ)
    (ambient : Environment S A.substitution.Carrier Γ Δ)
    (ordinary : Environment S A.substitution.Carrier (equations.get i).ctx Δ),
    interpretSchema A body ambient ordinary (equations.get i).lhs =
      interpretSchema A body ambient ordinary (equations.get i).rhs

/-- Contextual satisfaction makes the interpretation of every actual
contextual syntactic instance equal, including arbitrary closing values. -/
theorem Satisfies.interpret_instance {A : BindingCloneAlgebra.Algebra.{u} S}
    {equations : List (EqAxiom S M)} (satisfies : Satisfies A equations)
    (i : Fin equations.length) {Γ Δ : Ctx S} (body : ContextualAssignment S M Γ)
    (ambient : Sub S Γ Δ) (ordinary : Sub S (equations.get i).ctx Δ) :
    interpret A (ContextualAssignment.instantiate body ambient ordinary (equations.get i).lhs) =
      interpret A (ContextualAssignment.instantiate body ambient ordinary (equations.get i).rhs) :=
  (interpret_instantiate A body ambient ordinary (equations.get i).lhs).trans
    ((satisfies i (interpretAssignment A body) (interpretEnvironment A ambient)
      (interpretEnvironment A ordinary)).trans
        (interpret_instantiate A body ambient ordinary (equations.get i).rhs).symm)

/-- A declared dependency projection observes the corresponding argument. -/
theorem apply_dependency_projection (A : BindingCloneAlgebra.Algebra.{u} S)
    {dependencies Γ Δ : Ctx S} {sort : S.Srt} (x : Var dependencies sort)
    (arguments : Environment S A.substitution.Carrier dependencies Δ)
    (ambient : Environment S A.substitution.Carrier Γ Δ) :
    apply A (A.substitution.injectVar (injPrefix dependencies x)) arguments ambient =
      arguments sort x :=
  (A.substitution.substitute_var (joinEnvironment arguments ambient) _).trans
    (joinEnvironment_prefix dependencies arguments ambient sort x)

/-- A captured ambient projection observes the ambient value, retaining
its separation from the declared dependency arguments. -/
theorem apply_ambient_projection (A : BindingCloneAlgebra.Algebra.{u} S)
    {dependencies Γ Δ : Ctx S} {sort : S.Srt} (x : Var Γ sort)
    (arguments : Environment S A.substitution.Carrier dependencies Δ)
    (ambient : Environment S A.substitution.Carrier Γ Δ) :
    apply A (A.substitution.injectVar (weakenVar dependencies x)) arguments ambient =
      ambient sort x :=
  (A.substitution.substitute_var (joinEnvironment arguments ambient) _).trans
    (joinEnvironment_ambient dependencies arguments ambient sort x)

namespace Controls

/-- In the existing term clone the two environment blocks can carry
distinct same-sort projections. Captured ambient data does not become the
declared dependency argument. -/
theorem application_blocks_distinct (sort : S.Srt) :
    let arguments : Sub S [sort] [sort, sort] :=
      fun _ x => .var (injPrefix [sort] x)
    let ambient : Sub S [sort] [sort, sort] :=
      fun _ x => .var (weakenVar [sort] x)
    apply (BindingCloneAlgebra.terms S) (.var (.zero : Var [sort, sort] sort)) arguments ambient =
        (.var .zero : Term S [sort, sort] sort) ∧
      apply (BindingCloneAlgebra.terms S) (.var (.succ .zero : Var [sort, sort] sort))
          arguments ambient = (.var (.succ .zero) : Term S [sort, sort] sort) ∧
        apply (BindingCloneAlgebra.terms S) (.var (.zero : Var [sort, sort] sort)) arguments ambient ≠
          apply (BindingCloneAlgebra.terms S) (.var (.succ .zero : Var [sort, sort] sort))
            arguments ambient := by
  intro arguments ambient
  have dependency := apply_dependency_projection (BindingCloneAlgebra.terms S)
    (.zero : Var [sort] sort) arguments ambient
  have captured := apply_ambient_projection (BindingCloneAlgebra.terms S)
    (.zero : Var [sort] sort) arguments ambient
  refine ⟨dependency, captured, ?_⟩
  intro same
  have impossible : (.var .zero : Term S [sort, sort] sort) = .var (.succ .zero) :=
    dependency.symm.trans (same.trans captured)
  cases impossible

end Controls

end Mettapedia.OSLF.Binding.BindingContextualEquationInterpretation
