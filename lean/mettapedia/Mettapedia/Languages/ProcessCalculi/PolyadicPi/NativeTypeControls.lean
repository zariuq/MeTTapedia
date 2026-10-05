import Mettapedia.Languages.ProcessCalculi.PolyadicPi.NativeTypes
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingLambdaControls

/-!
# Native observations of the name-passing compiler

The identity call reaches its actual return protocol in the generated native
logic. A definition with a variable body exposes the complementary boundary:
its translated server has a native successor, while the abridged source has
none. Thus the comparison is neither empty nor unrestricted backward transport.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.NativeTypeControls

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.Languages.LambdaCalculus
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingLambda
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.NativeTypes

abbrev context : Ctx sig := [.nm, .nm]
def argument : Var context .nm := .zero
def result : Var context .nm := .succ .zero
def identityBody : Expr (.nm :: context) := .var .zero
def identityCall : Expr context := .app (.lam identityBody) argument

/-- A concrete beta computation is seen by the generated native diamond as
the expected reference/return-channel protocol, modulo target equations. -/
theorem identity_native_return :
    (semanticDiamond (operationalTheory context)
      (classPredicate (out1 (.var argument) (.var result)))).1
      (translate identityCall result) := by
  apply headStep_nativeDiamond (.root (.beta identityBody argument))
    (fun _ name => name) result
  exact .refl _

/-- There is an actual authored target firing, while the corresponding
source definition is inert in the explicitly supported head calculus. -/
theorem definition_native_gap {Γ : Ctx sig} (value : Expr Γ) (returnName : Var Γ .nm) :
    (semanticDiamond (operationalTheory Γ)
      (⟨fun _ => True, by intro _ _ _; rfl⟩)).1
      (translate (.defn value (.var .zero)) returnName) ∧
    ¬ (semanticDiamond (headTheory Γ)
      (⟨fun _ => True, by intro _ _ _; rfl⟩)).1 (.defn value (.var .zero)) := by
  constructor
  · exact (nativeDiamond_iff _ _).mpr
      ⟨_, definition_fetch value (fun _ name => name) returnName, trivial⟩
  · intro possible
    obtain ⟨target, step, _⟩ := (gsltDiamond_spec (headTheory Γ) _ _).mp possible
    exact NamePassing.defn_variable_no_head_step value .zero step

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.NativeTypeControls
