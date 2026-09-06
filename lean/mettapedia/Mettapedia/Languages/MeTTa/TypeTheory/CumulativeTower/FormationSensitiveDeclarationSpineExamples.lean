import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FormationSensitiveTelescopeSpine
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FormationSensitivePreservationInstances
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DefinitionalExpansionExamples

/-!
# Declaration-spine recovery with a qualified nonempty signature

The polymorphic identity's two arguments are recovered from any observed
application, including a result displayed through a transparent alias.
A lambda cannot be supplied where its declared ground argument is required.
In contrast, raw lambdas can have incomparable function types, so the
declaration-derived principal-spine hypothesis is substantive.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace FormationSensitive.DeclarationSpineExamples

open ConstantExpansion.Examples
open Dependencies.Examples (extraName valueName ground)

variable {n : Nat}

def identityContext : Tower.Ctx 2 :=
  .snoc (.snoc .nil (sortTm Tower.zero)) (.var 0)

def identityArguments (type term : Tower.Tm n) : Sub Tower.Head 2 n :=
  consSub term (consSub type Fin.elim0)

theorem identitySpine (context : Tower.Ctx n) :
    DeclarationSpine rules context (.const extraName)
      (Examples.polymorphicIdentityType Tower.zero) := by
  apply DeclarationSpine.constant
    (declared := Examples.polymorphicIdentityType (n := 0) Tower.zero) (u := .sort _)
  · decide
  · exact (Examples.polymorphicIdentityType_formed .nil Tower.zero).includeSignature signature
  · exact .sort _

/-- No unproved conversion or typing-coherence hypothesis remains for
this actual qualified signature. -/
theorem recover_identity_arguments {context : Tower.Ctx n}
    (formed : ContextFormation rules context) {type term displayed : Tower.Tm n}
    (observed : Typing rules context (.app (.app (.const extraName) type) term) displayed) :
    Typing rules context type (sortTm Tower.zero) ∧ Typing rules context term type := by
  obtain ⟨typed, _, _, _⟩ := DeclarationSpine.recoverTelescope universes pi_boundary formed
    identityContext (.var 1) (identityArguments type term) (identitySpine context) observed
  exact ⟨typed (1 : Fin 2), typed (0 : Fin 2)⟩

/-- The observed result is displayed at ground, while the recovered
argument requirement retains the original named type alias. -/
theorem converted_application_recovers_alias :
    Typing rules .nil (.const valueName : Tower.Tm 0) (.const secondAliasName) :=
  (recover_identity_arguments .nil (specialize_typed (identity_constant_typed .nil))).2

theorem rejects_lambda_argument {context : Tower.Ctx n}
    (formed : ContextFormation rules context) (displayed : Tower.Tm n) :
    ¬ Typing rules context
      (.app (.app (.const extraName) ground) (.lam (.var 0))) displayed := by
  intro observed
  have argument := (recover_identity_arguments formed observed).2
  obtain ⟨_, _, _, _, _, _, adjustment⟩ := argument.lamGeneration
  exact pi_boundary.headDisjoint
    (adjustment.toConvOfSourceDisjointHeads (fun _ => pi_boundary.headDisjoint))

def arrowGround : Tower.Tm n := .pi ground ground

theorem arrowGround_formed (context : Tower.Ctx n) :
    Typing Tower.rules context arrowGround (sortTm (.max Tower.zero Tower.zero)) :=
  .piForm (.headType .legacyGround) (.sort _) (.headType .legacyGround) (.sort _) (.sorts _ _)

/-- The same raw lambda has two formed but nonconvertible function types.
This refutes extending declaration-spine coherence to arbitrary raw terms. -/
theorem raw_lambda_has_incomparable_function_types (context : Tower.Ctx n) :
    Typing Tower.rules context (.lam (.var 0)) arrowGround ∧
      Typing Tower.rules context (.lam (.var 0))
        (.pi arrowGround (rename wk arrowGround)) ∧
      ¬ Conv Tower.HeadEq (arrowGround : Tower.Tm n)
        (.pi arrowGround (rename wk arrowGround)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact BetaExamples.polymorphic_identity_beta_direct (.headType .legacyGround)
  · exact BetaExamples.polymorphic_identity_beta_direct (arrowGround_formed context)
  · intro conversion
    have domains := (Tower.piConversionBoundary.components conversion).1
    exact Tower.piConversionBoundary.headDisjoint (.symm _ _ domains)

#print axioms identitySpine
#print axioms recover_identity_arguments
#print axioms converted_application_recovers_alias
#print axioms rejects_lambda_argument
#print axioms arrowGround_formed
#print axioms raw_lambda_has_incomparable_function_types

end FormationSensitive.DeclarationSpineExamples
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
