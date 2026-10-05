import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedOpeningExecution

/-!
# Private-scope opening controls

The controls use real binary communication and retained unary servers, with
an extra unused scope in the supplied endpoint. Two independent used marked
restrictions violate the single-origin condition, and an autonomous private
replication violates the guarded-server qualification.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedOpeningControls

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveMarking
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveHeaderInvariant
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedActiveFrontier
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedCommunicationInversion
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedOpening

def binaryBody : Proc [.nm] :=
  par (out2 (.var .zero) (.var .zero) (.var .zero))
    (inp2 (.var .zero) (out1 (.var .zero) (.var (.succ .zero))))

def binaryReturned : Proc [.nm] := out1 (.var .zero) (.var .zero)

def binaryInvocation : Exposure (nu binaryBody) (nu binaryReturned) where
  world := [.nm]
  scope := .bind .nil
  redex := binaryBody
  reduct := binaryReturned
  selected := .binary (.var .zero) (.var .zero) (.var .zero)
    (out1 (.var .zero) (.var (.succ .zero)))
  frame := nil
  before := .nu (.symm (.parUnit binaryBody))
  after := .nu (.parUnit binaryReturned)

theorem binary_safe : Safe binaryBody := by simp only [binaryBody, par, out2, inp2, Safe, and_self]

theorem binary_supplied_endpoint :
    ∃ (returned : Proc [.nm]) (opened : Exposure binaryBody returned),
      inputHeader opened.selected = .input2 ∧
      StructuralEq (nu (weaken (nu binaryReturned))) (nu returned) := by
  let supplied := binaryInvocation.changeTarget (.symm (.nuUnused (nu binaryReturned)))
  obtain ⟨returned, opened, arity, endpoint⟩ :=
    open_restriction_exposure binaryBody supplied binary_safe
  exact ⟨returned, opened, arity, endpoint⟩

def unaryGuard : Proc [.nm, .nm] := out1 (.var .zero) (.var (.succ .zero))

def serverBody : Proc [.nm] :=
  par (out1 (.var .zero) (.var .zero)) (rep (inp1 (.var .zero) unaryGuard))

def serverReturned : Proc [.nm] :=
  par (out1 (.var .zero) (.var .zero)) (rep (inp1 (.var .zero) unaryGuard))

def serverInvocation : Exposure (nu serverBody) (nu serverReturned) where
  world := [.nm]
  scope := .bind .nil
  redex := par (out1 (.var .zero) (.var .zero)) (inp1 (.var .zero) unaryGuard)
  reduct := out1 (.var .zero) (.var .zero)
  selected := .unary (.var .zero) (.var .zero) unaryGuard
  frame := rep (inp1 (.var .zero) unaryGuard)
  before := .nu ((StructuralEq.par (.refl _) (.repUnfold _)).trans
    (.symm (.parAssoc _ _ _)))
  after := .refl _

theorem server_safe : Safe serverBody := by
  simp only [serverBody, par, out1, rep, inp1, Safe, Vacuous, and_self]

theorem retained_server_opening :
    ∃ (returned : Proc [.nm]) (opened : Exposure serverBody returned),
      inputHeader opened.selected = .input1 ∧ StructuralEq (nu serverReturned) (nu returned) := by
  obtain ⟨returned, opened, arity, endpoint⟩ :=
    open_restriction_exposure serverBody serverInvocation server_safe
  exact ⟨returned, opened, arity, endpoint⟩

def twoPrivateComponents : Proc [] :=
  par (nu (out1 (.var .zero) (.var .zero)))
    (nu (inp1 (.var .zero) nil))

def twoPrivateMarks : ActiveMarking.Tree Bool :=
  .par (.nu true (.out1 true)) (.nu true (.inp1 true .nil))

theorem two_private_origins : markedCount twoPrivateMarks twoPrivateComponents = 2 := by
  simp only [twoPrivateMarks, twoPrivateComponents, par, nu, out1, inp1, nil, markedCount,
    contribution, countVar, countVarArgs, weakenVar, ↓reduceIte, Nat.add_zero]
  rfl

theorem two_private_not_single : ¬ markedCount twoPrivateMarks twoPrivateComponents ≤ 1 := by
  rw [two_private_origins]
  omega

theorem autonomous_private_excluded :
    ¬ Safe (rep (nu (out1 (.var .zero) (.var .zero))) : Proc []) := by
  simp only [rep, nu, out1, Safe, Vacuous, countVar, countVarArgs, weakenVar,
    Nat.add_zero, sameVar_self, ↓reduceIte, and_true]
  omega

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedOpeningControls
