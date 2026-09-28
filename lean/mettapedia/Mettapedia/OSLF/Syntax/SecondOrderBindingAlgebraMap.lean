import Mettapedia.OSLF.Syntax.SecondOrderEquationUniversal
import Mettapedia.OSLF.Syntax.SemanticSchemaNaturality
import Mettapedia.OSLF.Syntax.SignatureMorphismMetas

/-!
# Second-order substitution as a binding-algebra map

Terms with a freely adjoining list of contextual metavariables carry the
original signature's binding operators and simultaneous substitution.
Instantiating those metavariables preserves all of that structure. This map
connects the second-order context category to the existing semantic
naturality theorem for authored higher-order schemas.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.SecondOrderContext

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FreeBindingTerms

variable {S : Signature}

/-- The full extended term carrier, viewed as a substitution algebra over
the original sorts. The signature parameter of the record changes, so its
laws are transported field by field. -/
def restrictedSubstitution (X : Object S) :
    BindingSubstitutionAlgebra.Algebra S where
  Carrier := fun Γ sort => Term (withMetas S X.arities) Γ sort
  injectVar := fun v => Term.var (S := withMetas S X.arities) v
  substitute := fun environment term =>
    bind (S := withMetas S X.arities) environment term
  substitute_var := by intro Γ Δ environment sort index; rfl
  substitute_identity := by intro Γ sort term; exact bind_id term
  substitute_comp := by
    intro Γ Δ Θ sort first second term
    exact bind_comp first second term

/-- Repackage an argument vector of the base signature as the same ordered
syntactic arguments over its metavariable extension. -/
def toSyntax (X : Object S) :
    ∀ {arities : List (List S.Srt × S.Srt)} {Γ : Ctx S},
      FamilyArgs S (restrictedSubstitution X).Carrier arities Γ →
      Args (withMetas S X.arities) arities Γ
  | _, _, .nil => .nil
  | _, _, .cons head tail => .cons head (toSyntax X tail)

/-- Semantic lifting for the restricted algebra is the existing syntactic
capture-avoiding lift; the signature restriction changes no variable scopes. -/
theorem restricted_liftEnvironment (X : Object S) {Γ Δ : Ctx S}
    (environment : Sub (withMetas S X.arities) Γ Δ)
    : ∀ (binders : List S.Srt),
      (restrictedSubstitution X).liftEnvironment environment binders =
        liftSub environment binders
  | [] => rfl
  | _ :: binders => by
      funext sort index
      cases index with
      | zero => rfl
      | succ old =>
          change bind (fun _ v => Term.var (.succ v))
              ((restrictedSubstitution X).liftEnvironment environment binders sort old) =
            weaken (liftSub environment binders sort old)
          rw [restricted_liftEnvironment X environment binders]
          exact bind_var_eq_rename (fun _ v => Var.succ v) _

/-- Repackaging commutes with semantic substitution of each argument,
including the extended local context under its binder list. -/
theorem toSyntax_substituteArgs (X : Object S) {Γ Δ : Ctx S}
    (environment : Sub (withMetas S X.arities) Γ Δ) :
    ∀ {arities : List (List S.Srt × S.Srt)}
      (args : FamilyArgs S (restrictedSubstitution X).Carrier arities Γ),
      toSyntax X ((restrictedSubstitution X).substituteArgs environment args) =
        bindArgs environment (toSyntax X args)
  | _, .nil => rfl
  | _, .cons (bs := binders) head tail => by
      simp only [BindingSubstitutionAlgebra.Algebra.substituteArgs,
        toSyntax, bindArgs]
      rw [restricted_liftEnvironment X environment binders]
      exact congrArg (Args.cons (bind (liftSub environment binders) head))
        (toSyntax_substituteArgs X environment tail)

/-- The free metavariables enlarge the term carrier, while the interpreted
operator signature remains the originally authored one. -/
def termAlgebra (X : Object S) : BindingCloneAlgebra.Algebra S where
  substitution := restrictedSubstitution X
  operation := fun op args =>
    Term.op (S := withMetas S X.arities) (Sum.inl op) (toSyntax X args)
  operation_substitute := by
    intro Γ Δ sort environment op args
    change bind environment
      (Term.op (S := withMetas S X.arities) (Sum.inl op) (toSyntax X args)) =
      Term.op (S := withMetas S X.arities) (Sum.inl op)
        (toSyntax X ((restrictedSubstitution X).substituteArgs environment args))
    exact congrArg
      (Term.op (S := withMetas S X.arities) (Sum.inl op))
      (toSyntax_substituteArgs X (fun s v => environment s v) args).symm

mutual

/-- Folding an original authored term into the enlarged term algebra is
exactly the syntactic inclusion of its operations and bound variables. -/
theorem termAlgebra_interpret (X : Object S) :
    ∀ {Γ : Ctx S} {sort : S.Srt} (term : Term S Γ sort),
      BindingCloneFoldSubstitution.interpret (termAlgebra X) term =
        embed (M := X.arities) term
  | _, _, .var _ => rfl
  | _, _, .op op args => by
      change Term.op (S := withMetas S X.arities) (Sum.inl op)
        (toSyntax X
          (BindingCloneFoldSubstitution.interpretArgs (termAlgebra X) args)) =
        Term.op (S := withMetas S X.arities) (Sum.inl op)
          (embedArgs (M := X.arities) args)
      exact congrArg
        (Term.op (S := withMetas S X.arities) (Sum.inl op))
        (termAlgebra_interpretArgs X args)

/-- The fold comparison extends into every operator argument, including
arguments in their binder-extended local contexts. -/
theorem termAlgebra_interpretArgs (X : Object S) :
    ∀ {arities : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (args : Args S arities Γ),
      toSyntax X
        (BindingCloneFoldSubstitution.interpretArgs (termAlgebra X) args) =
        embedArgs (M := X.arities) args
  | _, _, .nil => rfl
  | _, _, .cons head tail => by
      exact congrArg₂ Args.cons
        (termAlgebra_interpret X head)
        (termAlgebra_interpretArgs X tail)

end

/-- Packaging semantic argument vectors as syntax commutes with
metavariable instantiation, including each binder-extended head context. -/
theorem familyToSyntax_instInto {X Y : Object S}
    (assignment : X ⟶ Y) :
    ∀ {arities : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (args : FamilyArgs S (restrictedSubstitution Y).Carrier arities Γ),
      instIntoArgs assignment (toSyntax Y args) =
        toSyntax X (FamilyArgs.map (instInto assignment) args)
  | _, _, .nil => rfl
  | _, _, .cons head tail => by
      simp only [toSyntax, instIntoArgs, FamilyArgs.map]
      congr 1
      exact familyToSyntax_instInto assignment tail

/-- Every second-order context arrow is a full binding-clone morphism on
the underlying base-signature algebras. In particular, it respects
capture-avoiding substitution, not just raw term constructors. -/
def instIntoHom {X Y : Object S} (assignment : X ⟶ Y) :
    FreeBindingClone.Hom (termAlgebra Y) (termAlgebra X) where
  raw := {
    map := instInto assignment
    map_variable := by intros; rfl
    map_operation := by
      intro Γ sort op args
      change instInto assignment
        (Term.op (S := withMetas S Y.arities) (Sum.inl op) (toSyntax Y args)) =
        Term.op (S := withMetas S X.arities) (Sum.inl op)
          (toSyntax X (FamilyArgs.map (instInto assignment) args))
      exact congrArg (Term.op (S := withMetas S X.arities) (Sum.inl op))
        (familyToSyntax_instInto assignment args) }
  map_substitute := by
    intro Γ Δ sort environment term
    exact instInto_bind assignment environment term

/-- An authored higher-order schema commutes with any second-order context
assignment. Its metavariables can have nonempty dependency contexts, and its
operators may bind variables in their arguments. -/
theorem interpretSchema_instInto {M : List (MetaArity S)}
    {X Y : Object S} (assignment : X ⟶ Y)
    (valuation : BindingEquationalModels.MetaValuation (termAlgebra Y) M)
    {Γ : Ctx S} {sort : S.Srt}
    (schema : Term (withMetas S M) Γ sort) :
    instInto assignment
        (BindingEquationInterpretation.interpretSchema
          (termAlgebra Y) valuation schema) =
      BindingEquationInterpretation.interpretSchema
        (termAlgebra X)
        (fun i => instInto assignment (valuation i)) schema :=
  BindingEquationInterpretation.interpretSchema_map
    (instIntoHom assignment) valuation schema

/-- The naturality law also transports ordinary closing environments, so it
applies to complete instances of authored equations. -/
theorem interpretSchema_closed_instInto {M : List (MetaArity S)}
    {X Y : Object S} (assignment : X ⟶ Y)
    (valuation : BindingEquationalModels.MetaValuation (termAlgebra Y) M)
    {Γ Δ : Ctx S} {sort : S.Srt}
    (environment : BindingSubstitutionAlgebra.Environment S
      (termAlgebra Y).substitution.Carrier Γ Δ)
    (schema : Term (withMetas S M) Γ sort) :
    instInto assignment
      ((termAlgebra Y).substitution.substitute environment
        (BindingEquationInterpretation.interpretSchema
          (termAlgebra Y) valuation schema)) =
      (termAlgebra X).substitution.substitute
        (fun s v => instInto assignment (environment s v))
        (BindingEquationInterpretation.interpretSchema
          (termAlgebra X)
          (fun i => instInto assignment (valuation i)) schema) :=
  BindingEquationInterpretation.interpretSchema_closed_map
    (instIntoHom assignment) valuation environment schema

/-- The signature inclusion preserves each metavariable's full arity, not
only its result sort. -/
theorem metaInclusion_get_mapMetas (X : Object S)
    {M : List (MetaArity S)} (index : Fin M.length) :
    ((metaInclusion S X.arities).mapMetas M).get
        ((metaInclusion S X.arities).mapMetaIndex index) = M.get index := by
  simpa [metaInclusion, mapArity, mapSorts_id]
    using (metaInclusion S X.arities).get_mapMetas index

/-- A semantic schema valuation is reindexed to the declaration positions
of the signature-morphism translation into an ambient meta-context. The
arity cast only transports sorts; it never merges declaration positions. -/
def mappedSchemaBody (X : Object S) {M : List (MetaArity S)}
    (valuation : BindingEquationalModels.MetaValuation (termAlgebra X) M)
    (index : Fin ((metaInclusion S X.arities).mapMetas M).length) :
    Term (withMetas S X.arities)
      (((metaInclusion S X.arities).mapMetas M).get index).1
      (((metaInclusion S X.arities).mapMetas M).get index).2 :=
  let inclusion := metaInclusion S X.arities
  castMetaBody
    (metaInclusion_get_mapMetas X (inclusion.unmapMetaIndex index)).symm
    (valuation (inclusion.unmapMetaIndex index))

/-- Reading back a translated metavariable position recovers exactly its
semantic body. -/
theorem mappedSchemaBody_at (X : Object S) {M : List (MetaArity S)}
    (valuation : BindingEquationalModels.MetaValuation (termAlgebra X) M)
    (index : Fin M.length) :
    castMetaBody (metaInclusion_get_mapMetas X index)
      (mappedSchemaBody X valuation
        ((metaInclusion S X.arities).mapMetaIndex index)) =
      valuation index := by
  unfold mappedSchemaBody
  simp only [SigMor.unmap_mapMetaIndex]
  exact castMetaBody_symm (metaInclusion_get_mapMetas X index) _

/-- Transporting a metavariable body's arity is natural under second-order
instantiation because the instantiation leaves the base sorts unchanged. -/
theorem instInto_castMetaBody {X Y : Object S} (assignment : X ⟶ Y)
    {a b : MetaArity S} (equality : a = b)
    (body : Term (withMetas S Y.arities) a.1 a.2) :
    instInto assignment
      (castMetaBody (V := withMetas S Y.arities) equality body) =
    castMetaBody (V := withMetas S X.arities) equality
      (instInto assignment body) := by
  cases equality
  rfl

/-- Reindexing a translated schema valuation agrees with translating the
reindexed semantic valuation. This keeps the original declaration positions
across arbitrary ambient metavariable contexts. -/
theorem mappedSchemaBody_instInto {M : List (MetaArity S)}
    {X Y : Object S} (assignment : X ⟶ Y)
    (valuation : BindingEquationalModels.MetaValuation (termAlgebra Y) M)
    (index : Fin ((metaInclusion S X.arities).mapMetas M).length) :
    mappedSchemaBody X
        (fun k => instInto assignment (valuation k)) index =
      instInto assignment (mappedSchemaBody Y valuation index) := by
  unfold mappedSchemaBody
  let position := (metaInclusion S X.arities).unmapMetaIndex index
  let arityEquality := (metaInclusion_get_mapMetas X position).symm
  change castMetaBody (V := withMetas S X.arities) arityEquality
      (instInto assignment (valuation position)) =
    instInto assignment
      (castMetaBody (V := withMetas S Y.arities) arityEquality
        (valuation position))
  exact (instInto_castMetaBody assignment arityEquality
    (valuation position)).symm

end Mettapedia.OSLF.Binding.SecondOrderContext

#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.instIntoHom
#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.interpretSchema_instInto
#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.interpretSchema_closed_instInto
