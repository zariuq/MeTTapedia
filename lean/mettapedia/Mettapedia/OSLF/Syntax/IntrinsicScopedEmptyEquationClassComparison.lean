import Mettapedia.OSLF.Syntax.FreeBindingEquationModel

/-!
# The empty equation quotient keeps every original term

The two genuine initiality theorems construct inverse binding-clone maps.
This comparison preserves all contexts, substitutions and binder operations,
without a second term traversal or an assumption of quotient injectivity.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedEmptyEquationClassComparison

variable {S : Signature} (schema : List (MetaArity S))

abbrev equations : List (EqAxiom S schema) := []
abbrev algebra := BindingEquationQuotientModel.algebra (equations schema)

/-- Original terms satisfy the actual empty contextual equation presentation. -/
def rawModel : FreeBindingEquationModel.Model (equations schema) where
  algebra := BindingCloneAlgebra.terms S
  satisfies := by
    intro index
    exact Fin.elim0 index

/-- The genuine quotient interpretation into original terms. -/
def decode : FreeBindingClone.Hom (algebra schema) (BindingCloneAlgebra.terms S) :=
  FreeBindingEquationModel.interpretHom (rawModel schema)

/-- Projecting original terms and decoding them is the identity binding-clone map. -/
theorem projection_decode :
    FreeBindingClone.Hom.comp (BindingEquationQuotientModel.projection (equations schema))
      (decode schema) = FreeBindingClone.Hom.id (BindingCloneAlgebra.terms S) :=
  (FreeBindingClone.hom_unique _ _).trans (FreeBindingClone.hom_unique _ _).symm

/-- Decoding the empty quotient and projecting back is the identity on classes. -/
theorem decode_projection :
    FreeBindingClone.Hom.comp (decode schema)
      (BindingEquationQuotientModel.projection (equations schema)) =
        FreeBindingClone.Hom.id (algebra schema) :=
  (FreeBindingEquationModel.hom_unique (FreeBindingEquationModel.presented (equations schema)) _).trans
    (FreeBindingEquationModel.hom_unique (FreeBindingEquationModel.presented (equations schema)) _).symm

/-- Every original term is recovered, including open terms under arbitrary binders. -/
theorem decode_term {Γ : Ctx S} {s : S.Srt} (term : Term S Γ s) :
    (decode schema).raw.map
      ((BindingEquationQuotientModel.projection (equations schema)).raw.map term) = term :=
  congrArg (fun map : FreeBindingClone.Hom (BindingCloneAlgebra.terms S)
    (BindingCloneAlgebra.terms S) => map.raw.map term) (projection_decode schema)

/-- Empty-equation program classes are exactly the original contextual term carriers. -/
def carrierEquiv (Γ : Ctx S) (s : S.Srt) :
    (algebra schema).substitution.Carrier Γ s ≃ Term S Γ s where
  toFun := (decode schema).raw.map
  invFun := (BindingEquationQuotientModel.projection (equations schema)).raw.map
  left_inv value := congrArg (fun map : FreeBindingClone.Hom (algebra schema) (algebra schema) =>
    map.raw.map value) (decode_projection schema)
  right_inv := decode_term schema

end Mettapedia.OSLF.Binding.IntrinsicScopedEmptyEquationClassComparison
