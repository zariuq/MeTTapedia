import Mettapedia.OSLF.Syntax.FreeBindingEquationModel
import Mathlib.Algebra.FreeMonoid.Basic

/-!
# Account words induced by genuine source substitution

An atom is a complete source semantic value at a selected source sort.  The
account monoid at each context is its free word monoid.  Simultaneous source
substitution induces monoid homomorphisms, with identity and composition
proved from the existing binding clone.  Atoms need not remain constant under
substitution.  An equation-model instance uses its actual quotient carrier.

This constructs the source account family, not an accounted binding carrier
or the authored Cost transformer.  The comparison from a LanguageDef's
authored equations to the binding equation presentation is a separate step.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Cost.SourceAccountSubstitution

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra

universe u

variable {S : Signature} (Q : BindingCloneAlgebra.Algebra.{u} S) (accountSort : S.Srt)

/-- Complete typed source values supply the account atoms at a context. -/
abbrev Account (Γ : Ctx S) := FreeMonoid (Q.substitution.Carrier Γ accountSort)

/-- Actual simultaneous source substitution acts on every account atom. -/
def substitute {Γ Δ : Ctx S}
    (env : Environment S Q.substitution.Carrier Γ Δ) :
    Account Q accountSort Γ →* Account Q accountSort Δ :=
  FreeMonoid.map (Q.substitution.substitute env)

theorem substitute_identity {Γ : Ctx S} :
    substitute Q accountSort (fun _ v => Q.substitution.injectVar v) =
      MonoidHom.id (Account Q accountSort Γ) := by
  apply MonoidHom.ext
  intro word
  have identity : (Q.substitution.substitute
      (fun _ v => Q.substitution.injectVar v) :
      Q.substitution.Carrier Γ accountSort → Q.substitution.Carrier Γ accountSort) = id := by
    funext atom
    exact Q.substitution.substitute_identity atom
  simp only [substitute, identity, FreeMonoid.map_id, MonoidHom.id_apply]

theorem substitute_comp {Γ Δ Θ : Ctx S}
    (first : Environment S Q.substitution.Carrier Γ Δ)
    (second : Environment S Q.substitution.Carrier Δ Θ) :
    (substitute Q accountSort second).comp (substitute Q accountSort first) =
      substitute Q accountSort
        (fun sort v => Q.substitution.substitute second (first sort v)) := by
  apply FreeMonoid.hom_eq
  intro atom
  change FreeMonoid.of (Q.substitution.substitute second
      (Q.substitution.substitute first atom)) =
    FreeMonoid.of (Q.substitution.substitute
      (fun sort v => Q.substitution.substitute second (first sort v)) atom)
  exact congrArg FreeMonoid.of (Q.substitution.substitute_comp first second atom)

/-- Substitution changes account atoms but preserves their ordered word
positions and multiplicities. -/
theorem substitute_length {Γ Δ : Ctx S}
    (env : Environment S Q.substitution.Carrier Γ Δ)
    (word : Account Q accountSort Γ) :
    (substitute Q accountSort env word).length = word.length := by
  exact List.length_map _

/-- A genuine source clone morphism induces a map of account words. -/
def map {R : BindingCloneAlgebra.Algebra.{u} S} (morphism : FreeBindingClone.Hom Q R)
    (Γ : Ctx S) : Account Q accountSort Γ →* Account R accountSort Γ :=
  FreeMonoid.map morphism.raw.map

theorem map_substitute {R : BindingCloneAlgebra.Algebra.{u} S}
    (morphism : FreeBindingClone.Hom Q R) {Γ Δ : Ctx S}
    (env : Environment S Q.substitution.Carrier Γ Δ) :
    (map Q accountSort morphism Δ).comp (substitute Q accountSort env) =
      (substitute R accountSort (fun sort v => morphism.raw.map (env sort v))).comp
        (map Q accountSort morphism Γ) := by
  apply FreeMonoid.hom_eq
  intro atom
  change FreeMonoid.of (morphism.raw.map (Q.substitution.substitute env atom)) =
    FreeMonoid.of (R.substitution.substitute
      (fun sort v => morphism.raw.map (env sort v)) (morphism.raw.map atom))
  exact congrArg FreeMonoid.of (morphism.map_substitute env atom)

/-- Context-dependent account atoms from an independently specified source
equation model.  The source class is not replaced by a digest. -/
abbrev ofEquationModel {M : List (MetaArity S)} {E : List (EqAxiom S M)}
    (model : FreeBindingEquationModel.Model.{u} E) (Γ : Ctx S) :=
  Account model.algebra accountSort Γ

/-- Swap the two actual variables at a repeated source sort. -/
def swapEnvironment (sort : S.Srt) : Sub S [sort, sort] [sort, sort] :=
  fun _ v => match v with
    | .zero => .var (.succ .zero)
    | .succ .zero => .var .zero
    | .succ (.succ impossible) => nomatch impossible

/-- Whole-source atoms are not immutable constants under substitution. -/
theorem swap_changes_account_atom (sort : S.Srt) :
    substitute (BindingCloneAlgebra.terms S) sort (swapEnvironment sort)
      (FreeMonoid.of (.var .zero : Term S [sort, sort] sort)) ≠
        FreeMonoid.of (.var .zero : Term S [sort, sort] sort) := by
  intro same
  have atoms := congrArg FreeMonoid.toList same
  change [Term.var (Var.succ Var.zero)] = [Term.var Var.zero] at atoms
  cases List.cons.inj atoms |>.1

end Mettapedia.GSLT.LanguageDef.Cost.SourceAccountSubstitution
