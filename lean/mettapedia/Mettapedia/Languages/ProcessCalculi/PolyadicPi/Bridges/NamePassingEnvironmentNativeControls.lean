import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingEnvironmentNative
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingEnvironmentControls

/-!
# Native environment path and account controls

The closed self-application example returns to its initial configuration
after a fetch and a call. The supplied compiler preserves that exact loop,
and its communication account distinguishes the loop from the empty run.
An endpoint alone therefore cannot recover the account.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingEnvironmentNativeControls

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.NativeTypes
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingLambda
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingEnvironmentControls
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingEnvironmentNative

def sourceLoop : ExecutionPath (environmentTheory []) loopingDefinition loopingDefinition :=
  .cons ⟨⟨.environmentFetch, first_fetch⟩⟩
    (.cons ⟨⟨.beta, retained_reference_called⟩⟩ (.refl _))

/-- The translated loop retains its intermediate released function call. -/
def compiledLoop : ExecutionPath (operationalTheory [Srt.nm])
    (compile loopingDefinition closedNames returnName)
    (compile loopingDefinition closedNames returnName) :=
  (compiler closedNames returnName).mapRoute sourceLoop

theorem supplied_loop_has_two_communications : compiledLoop.length = 2 :=
  OperationalTranslation.mapRoute_length _ sourceLoop

theorem account_counts_both_firings :
    (compiledAccount closedNames returnName).of sourceLoop = Multiplicative.ofAdd 2 :=
  compiledAccount_exact closedNames returnName sourceLoop

def repeatedLoop : (count : Nat) →
    ExecutionPath (environmentTheory []) loopingDefinition loopingDefinition
  | 0 => .refl _
  | count + 1 => sourceLoop.append (repeatedLoop count)

theorem repeatedLoop_length (count : Nat) : (repeatedLoop count).length = 2 * count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      calc
        _ = sourceLoop.length + (repeatedLoop count).length :=
          Route.length_append sourceLoop (repeatedLoop count)
        _ = 2 + 2 * count := congrArg (fun n => 2 + n) ih
        _ = 2 * (count + 1) := by rw [Nat.mul_succ, Nat.add_comm]

/-- Reuse is unbounded; each finite supplied prefix has its exact target account. -/
theorem repeated_account (count : Nat) :
    (compiledAccount closedNames returnName).of (repeatedLoop count) =
      Multiplicative.ofAdd (2 * count) := by
  exact (compiledAccount_exact closedNames returnName (repeatedLoop count)).trans
    (congrArg Multiplicative.ofAdd (repeatedLoop_length count))

/-- Equal current configurations cannot determine accumulated communication. -/
theorem no_endpoint_communication_account :
    ¬ ∃ readout : Proc [Srt.nm] → Proc [Srt.nm] → Nat,
      ∀ path : ExecutionPath (environmentTheory []) loopingDefinition loopingDefinition,
        readout (compile loopingDefinition closedNames returnName)
            (compile loopingDefinition closedNames returnName) =
          Multiplicative.toAdd ((compiledAccount closedNames returnName).of path) := by
  rintro ⟨readout, recovers⟩
  have empty := recovers (repeatedLoop 0)
  have running := recovers (repeatedLoop 1)
  rw [repeated_account] at empty running
  have impossible : (0 : Nat) = 2 := empty.symm.trans running
  cases impossible

/-- The environment execution reaches a genuine generated native predicate. -/
theorem fetch_has_native_observation :
    (semanticDiamond (operationalTheory [Srt.nm])
      (classPredicate (compile releasedCall closedNames returnName))).1
      (compile loopingDefinition closedNames returnName) :=
  step_nativeDiamond first_fetch closedNames returnName _ (.refl _)

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingEnvironmentNativeControls
