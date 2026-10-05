import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolPublicRoles

/-!
# Source-arity and subject-faithfulness controls

Unary and binary servers retain their actual source body and persistence.
A role-typed pair on different source channels demonstrates why injectivity
of the transported public subject is an additional requirement: identifying
the channels enables a real lowered communication of the wrong source arity.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.PublicRoles.Controls

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open NamePassingChannelRoles

abbrev twoNames : Ctx sig := [.nm, .nm]
abbrev oneName : Ctx sig := [.nm]
def reference : Var twoNames .nm := .succ .zero
def call : Var twoNames .nm := .zero
def roles : Roles twoNames := canonicalRoles [.nm]
def identity : Ren sig twoNames twoNames := fun _ name => name

theorem unary_server_preserved :
    ∃ body : Proc (.nm :: twoNames),
      ActiveGuardedBodies.input1 (7 : Nat) (.var reference) (lower nil) identity =
        ActiveGuardedBodies.input1 7 (.var reference) (lower body) identity ∧
      Typed (extendRole .call roles) body ∧
      (rep (inp1 (.var reference) nil) = inp1 (.var reference) body ∨
        rep (inp1 (.var reference) nil) = rep (inp1 (.var reference) body)) :=
  reference_input 7 identity (fun _ _ equal => equal) roles reference rfl
    (.server1 _ nil) (.rep (.inp1 _ rfl (.nil _))) rfl rfl

def binaryBody : Proc (.nm :: .nm :: twoNames) :=
  out1 (.var .zero) (.var (.succ .zero))

/-- The recovered continuation uses its reference field first and its call
field second, and the actual provider remains a replicated binary listener. -/
theorem binary_server_preserved :
    ∃ body : Proc (.nm :: .nm :: twoNames),
      ActiveGuardedBodies.input1 (8 : Nat) (.var call) (decoderBody binaryBody) identity =
        ActiveGuardedBodies.input1 8 (.var call) (decoderBody body) identity ∧
      Typed (pairRoles roles) body ∧
      (rep (inp2 (.var call) binaryBody) = inp2 (.var call) body ∨
        rep (inp2 (.var call) binaryBody) = rep (inp2 (.var call) body)) :=
  binary_output_receiver 8 identity (fun _ _ equal => equal) roles call reference call
    (.out2 _ _ _ rfl rfl rfl) (.server2 _ binaryBody)
    (.rep (.inp2 _ rfl (.out1 _ _ rfl rfl))) rfl rfl

def collapsed : Ren sig twoNames oneName := fun _ name => by
  cases name with
  | zero => exact .zero
  | succ old =>
      cases old with
      | zero => exact .zero
      | succ absent => cases absent

theorem collapsed_subjects_match :
    (ActiveGuardedBodies.input1 (9 : Nat) (.var call) (decoderBody (nil : Proc (.nm :: .nm :: twoNames)))
      collapsed).header.channel =
      (ActiveGuardedBodies.output1 9 (.var reference) (.var call) collapsed).header.channel := rfl

theorem collapsed_is_not_faithful : ¬ Function.Injective (collapsed .nm) := by
  intro faithful
  have same : reference = call := faithful rfl
  cases same

def separatedPair : Proc twoNames :=
  par (out1 (.var reference) (.var call)) (inp2 (.var call) nil)

theorem separated_source_is_typed : Typed roles separatedPair :=
  .par (.out1 _ _ rfl rfl) (.inp2 _ rfl (.nil _))

theorem separated_source_cannot_communicate {endpoint : Proc twoNames} :
    ¬ Step separatedPair endpoint := by
  intro firing
  cases firing with
  | parL _ impossible => cases impossible
  | parR _ impossible => cases impossible

/-- Transport identifying different roles creates an actual target firing.
This shows that source typing alone does not authorize an arbitrary public
subject map, even when each source prefix is individually well typed. -/
theorem collapsed_lowering_communicates :
    Step (rename collapsed (lower separatedPair))
      (inst (rename (liftRen collapsed [.nm]) (decoderBody (nil : Proc (.nm :: .nm :: twoNames))))
        (.var .zero)) := by
  simp only [separatedPair, lower_par, lower_out1, lower_inp2, receivePair,
    rename_par, rename_out1, rename_inp1]
  exact .comm1 _ _ _

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.PublicRoles.Controls
