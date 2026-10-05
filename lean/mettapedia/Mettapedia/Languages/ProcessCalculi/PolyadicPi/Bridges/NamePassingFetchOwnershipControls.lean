import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingFetchOwnership
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingEnvironment

/-!
# Faithful references and real unary authorizations

A concrete one-shot call has a source certificate and an actual compiled
communication. Identifying distinct free references creates a communication
where the original source has no event. This separates injective reference
transport from the compiler's weaker reference/call role discipline.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingFetchOwnership.Controls

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.LambdaCalculus.NamePassing
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open NamePassingLambda

abbrev names : Ctx sig := [Srt.nm, Srt.nm]
def first : Var names Srt.nm := .zero
def second : Var names Srt.nm := .succ .zero
def identity : Expr names := .lam (.var .zero)
def valid : Expr names := .carrier first identity (.var first)
def mismatched : Expr names := .carrier first identity (.var second)

def unchanged : Ren sig names names := fun _ name => name

/-- Distinct source references are deliberately collapsed for the negative
control; the return name remains separately supplied. -/
def collapsed : Ren sig names names := fun _ name => by
  cases name with
  | zero => exact .zero
  | succ old => cases old with
      | zero => exact .zero
      | succ impossible => cases impossible

theorem actual_one_shot_source_certificate :
    Nonempty (Environment.EventCertificate .carrierFetch valid identity) :=
  ⟨.carrierFetch first identity (.here first identity)⟩

theorem actual_one_shot_target_communication :
    Step (compile valid unchanged second) (compile identity unchanged second) :=
  fetch_preserved first identity unchanged second

theorem collapsed_references_create_target_communication :
    Step (compile mismatched collapsed second) (compile identity collapsed second) := by
  change Step
    (par (out1 (.var first) (.var second))
      (inp1 (.var first) (compile identity (push collapsed) .zero))) _
  rw [← fetch_endpoint identity collapsed second]
  exact .comm1 _ _ _

theorem mismatched_source_has_no_event (kind : Environment.Action) (target : Expr names) :
    ¬ Environment.Step kind mismatched target := by
  intro event
  cases event with
  | carrierFetch name value fetch =>
      have same := (Environment.fetch_variable_iff first second identity target).mp fetch
      cases same.1
  | carrier name value event => cases event

theorem collapsed_references_are_not_faithful :
    ¬ Function.Injective (collapsed Srt.nm) := by
  intro faithful
  have impossible : first = second := faithful (show collapsed Srt.nm first = collapsed Srt.nm second from rfl)
  cases impossible

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingFetchOwnership.Controls
