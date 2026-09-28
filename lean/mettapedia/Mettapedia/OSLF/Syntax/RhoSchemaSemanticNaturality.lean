import Mettapedia.OSLF.Syntax.SemanticSchemaNaturality
import Mettapedia.OSLF.Syntax.RhoCommunicationSchema

/-!
# Semantic endpoint transport for authored rho communication

The communication declaration applies a continuation metavariable with a
name dependency below the input binder. Its two endpoints obey the general
schema naturality law in every binding-clone interpretation. This is the
endpoint part of transporting a firing event; preservation of the individual
event witness is a separate operational requirement.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoSchemaSemanticNaturality

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.BindingEquationInterpretation
open Mettapedia.OSLF.Binding.BindingEquationalModels
open Mettapedia.OSLF.Binding.RhoSchema

universe u v

/-- A model morphism transports both endpoints of the authored communication
schema, including the continuation beneath `inp` and its later application
to the quoted payload. -/
theorem comm_endpoints_map
    {A : BindingCloneAlgebra.Algebra.{u} sig}
    {B : BindingCloneAlgebra.Algebra.{v} sig}
    (h : FreeBindingClone.Hom A B)
    (continuation : MetaValuation A metas)
    {Δ : Ctx sig}
    (env : BindingSubstitutionAlgebra.Environment sig A.substitution.Carrier G Δ) :
    h.raw.map (A.substitution.substitute env
      (interpretSchema A continuation commLhs)) =
        B.substitution.substitute (fun s x => h.raw.map (env s x))
          (interpretSchema B (mapMetaValuation h continuation) commLhs) ∧
    h.raw.map (A.substitution.substitute env
      (interpretSchema A continuation commRhs)) =
        B.substitution.substitute (fun s x => h.raw.map (env s x))
          (interpretSchema B (mapMetaValuation h continuation) commRhs) := by
  exact positionedRewrite_endpoints_map h continuation comm env

#print axioms comm_endpoints_map

end Mettapedia.OSLF.Binding.RhoSchemaSemanticNaturality
