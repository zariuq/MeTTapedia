import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingOperationalCorrespondence
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingFetchOwnershipControls
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingScopeControls

/-!
# Controls for actual compiler-image readback

A private persistent definition is fetched and called, retaining its server
while returning a lambda value. Its actual execution starts and finishes in
noncanonical static representatives and has two real communications. The
same result channel as the free argument is allowed. An unbound reference is
blocked but is not a returned value; collapsed references and the old source
without application scope equations remain discriminating negative fixtures.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingCompilerReadback.Controls

open Mettapedia.OSLF.Binding
open Mettapedia.GSLT
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.Languages.LambdaCalculus
open Mettapedia.Languages.LambdaCalculus.NamePassing
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open NamePassingLambda NamePassingEnvironmentEquationsNative

abbrev names : Ctx sig := [Srt.nm]
def identityEnvironment : Ren sig names names := fun _ name => name
def publicName : Var names .nm := .zero
def stored : Expr names := .lam (.lam (.var .zero))
def start : Expr names := .defn stored (.app (.var .zero) (.succ publicName))
def fetched : Expr names := .defn stored (.app (NamePassing.weaken stored) (.succ publicName))
def returned : Expr names := .defn stored (.lam (.var .zero))

theorem names_faithful : Function.Injective (identityEnvironment .nm) := fun _ _ same => same

theorem no_fresh_result_needed : identityEnvironment .nm publicName = publicName := rfl

def fetchCertificate : Environment.EventCertificate .environmentFetch start fetched :=
  .environmentFetch stored (.app (.succ publicName) (.here .zero (NamePassing.weaken stored)))

theorem actual_source_beta : Environment.Step .beta fetched returned := by
  simpa only [fetched, returned, stored, NamePassing.weaken, NamePassing.instantiate,
    NamePassing.rename, NamePassing.plugName, liftRen] using
    (Environment.Step.defn stored (Environment.Step.beta
      (.lam (.var .zero) : Expr (.nm :: .nm :: names)) (.succ publicName)))

def initial : Proc names := par nil (compile start identityEnvironment publicName)
def final : Proc names := nu (weaken (compile returned identityEnvironment publicName))

theorem initial_related :
    (NamePassingOperationalCorrespondence.readback identityEnvironment names_faithful publicName).related start initial :=
  (StructuralEq.parComm _ _).trans (.parUnit _)

theorem first_actual : StepModulo initial (compile fetched identityEnvironment publicName) :=
  NamePassingEnvironment.modulo_congr initial_related
    (NamePassingEnvironment.step_preserved fetchCertificate.sound identityEnvironment publicName)
    (.refl _)

theorem second_actual : StepModulo (compile fetched identityEnvironment publicName) final :=
  NamePassingEnvironment.modulo_congr (.refl _)
    (NamePassingEnvironment.step_preserved actual_source_beta identityEnvironment publicName)
    (.symm (.nuUnused _))

def actualPrefix : ExecutionPath (NativeTypes.operationalTheory names) initial final :=
  .cons ⟨first_actual⟩ (.cons ⟨second_actual⟩ (.refl final))

theorem exact_two_communications : actualPrefix.length = 2 := rfl

/-- Readback consumes that supplied noncanonical target prefix, rather than
substituting a canonical forward execution for it. -/
theorem actual_prefix_has_exact_source_receipt :
    ∃ successor, ∃ reflected : ExecutionPath (sourceTheory names) start successor,
      StructuralEq final (compile successor identityEnvironment publicName) ∧ reflected.length = 2 := by
  obtain ⟨successor, reflected, related, length⟩ :=
    NamePassingOperationalCorrespondence.prefix_readback identityEnvironment names_faithful publicName
      initial_related actualPrefix
  exact ⟨successor, reflected, related, length.trans exact_two_communications⟩

theorem returned_is_a_value : Nonempty (Environment.ReturningLambda returned) :=
  ⟨.defn stored (.lam (.var .zero))⟩

def freeReference : Expr names := .var publicName

theorem free_reference_target_is_blocked (target : Proc names) :
    ¬ StepModulo (compile freeReference identityEnvironment publicName) target :=
  ActiveHeaderInvariant.no_step_of_no_inputs _ (by simp [freeReference, compile, out1, ActiveHeaderInvariant.visible])
    (by simp [freeReference, compile, out1, ActiveHeaderInvariant.visible]) target

theorem free_reference_source_is_blocked :
    ¬ ∃ action successor, Environment.StepModulo action freeReference successor := by
  intro active
  obtain ⟨target, firing⟩ :=
    (enabled_iff freeReference identityEnvironment names_faithful publicName).mp active
  exact free_reference_target_is_blocked target firing

theorem free_reference_is_not_a_value : ¬ Nonempty (Environment.ReturningLambda freeReference) := by
  rintro ⟨returning⟩
  cases returning

theorem collapsed_fixture_is_not_faithful :
    ¬ Function.Injective (NamePassingFetchOwnership.Controls.collapsed .nm) :=
  NamePassingFetchOwnership.Controls.collapsed_references_are_not_faithful

theorem old_source_cannot_supply_global_readback :
    ¬ (∀ term : Expr [Srt.nm, Srt.nm], ∀ endpoint : Proc [Srt.nm, Srt.nm, Srt.nm],
      StepModulo (compile term NamePassingScopeControls.names NamePassingScopeControls.result) endpoint →
        ∃ action next, Environment.Step action term next ∧
          StructuralEq endpoint (compile next NamePassingScopeControls.names NamePassingScopeControls.result)) :=
  NamePassingScopeControls.directed_source_global_reflection_is_false

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingCompilerReadback.Controls
