import Mettapedia.Languages.ProcessCalculi.PolyadicPi.ActiveObservation
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedActiveFrontier

/-!
# Subject separation and public native observations

An existence observation of a header depends only on which channel equals
the queried subject. Other channel keys and ordered fields may be retained
by stronger observations, but are irrelevant to this one. A two-color
interpretation therefore computes the same public observation. The private
color remains distinct from the queried ambient channel under every scope.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.ActiveObservation

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open ActiveMarkedNames ScopedActiveFrontier

universe u v

theorem hasHeader_subject_compare {Key : Type u} {Other : Type v}
    (kind : ActiveHeaderInvariant.Header) (subject fresh : Key)
    (otherSubject otherFresh : Other) : ∀ {Γ : Ctx sig}
      (environment : Environment Key Γ) (otherEnvironment : Environment Other Γ)
      (process : Proc Γ),
      (fresh = subject ↔ otherFresh = otherSubject) →
      (∀ name, environment name = subject ↔ otherEnvironment name = otherSubject) →
      (HasHeader kind subject fresh environment process ↔
        HasHeader kind otherSubject otherFresh otherEnvironment process)
  | _, _, _, .var _, _, _ => by
      simp [HasHeader, observations, ActiveSyntaxMarking.mark, ActiveMarkedNames.observe]
  | _, _, _, .op .nil .nil, _, _ => by
      simp [HasHeader, observations, ActiveSyntaxMarking.mark, ActiveMarkedNames.observe]
  | _, environment, otherEnvironment, .op .par (.cons first (.cons second .nil)), freshEq, names => by
      change HasHeader kind subject fresh environment (par first second) ↔
        HasHeader kind otherSubject otherFresh otherEnvironment (par first second)
      simp only [hasHeader_par]
      exact or_congr
        (hasHeader_subject_compare kind subject fresh otherSubject otherFresh environment otherEnvironment first freshEq names)
        (hasHeader_subject_compare kind subject fresh otherSubject otherFresh environment otherEnvironment second freshEq names)
  | _, environment, otherEnvironment, .op .inp1 (.cons channel (.cons body .nil)), freshEq, names => by
      cases channel with
      | var channel =>
          change HasHeader kind subject fresh environment (inp1 (.var channel) body) ↔
            HasHeader kind otherSubject otherFresh otherEnvironment (inp1 (.var channel) body)
          simp only [hasHeader_inp1, nameKey]
          exact and_congr Iff.rfl (eq_comm.trans ((names channel).trans eq_comm))
      | op operator _ => cases operator
  | _, environment, otherEnvironment, .op .inp2 (.cons channel (.cons body .nil)), freshEq, names => by
      cases channel with
      | var channel =>
          change HasHeader kind subject fresh environment (inp2 (.var channel) body) ↔
            HasHeader kind otherSubject otherFresh otherEnvironment (inp2 (.var channel) body)
          simp only [hasHeader_inp2, nameKey]
          exact and_congr Iff.rfl (eq_comm.trans ((names channel).trans eq_comm))
      | op operator _ => cases operator
  | _, environment, otherEnvironment, .op .out1 (.cons channel (.cons datum .nil)), freshEq, names => by
      cases channel with
      | var channel =>
          change HasHeader kind subject fresh environment (out1 (.var channel) datum) ↔
            HasHeader kind otherSubject otherFresh otherEnvironment (out1 (.var channel) datum)
          simp only [hasHeader_out1, nameKey]
          exact and_congr Iff.rfl (eq_comm.trans ((names channel).trans eq_comm))
      | op operator _ => cases operator
  | _, environment, otherEnvironment, .op .out2 (.cons channel (.cons first (.cons second .nil))), freshEq, names => by
      cases channel with
      | var channel =>
          change HasHeader kind subject fresh environment (out2 (.var channel) first second) ↔
            HasHeader kind otherSubject otherFresh otherEnvironment (out2 (.var channel) first second)
          simp only [hasHeader_out2, nameKey]
          exact and_congr Iff.rfl (eq_comm.trans ((names channel).trans eq_comm))
      | op operator _ => cases operator
  | _, environment, otherEnvironment, .op .nu (.cons body .nil), freshEq, names => by
      change HasHeader kind subject fresh environment (nu body) ↔
        HasHeader kind otherSubject otherFresh otherEnvironment (nu body)
      simp only [hasHeader_nu]
      apply hasHeader_subject_compare kind subject fresh otherSubject otherFresh
        (ActiveMarkedNames.extend fresh environment) (ActiveMarkedNames.extend otherFresh otherEnvironment) body freshEq
      intro name
      cases name with
      | zero => exact freshEq
      | succ old => exact names old
  | _, environment, otherEnvironment, .op .rep (.cons body .nil), freshEq, names => by
      change HasHeader kind subject fresh environment (rep body) ↔
        HasHeader kind otherSubject otherFresh otherEnvironment (rep body)
      simp only [hasHeader_rep]
      exact hasHeader_subject_compare kind subject fresh otherSubject otherFresh
        environment otherEnvironment body freshEq names
termination_by _ _ _ process _ _ => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

/-- The private marker is false and precisely the queried public variable
is true. This interpretation forgets other distinctions only after the
chosen observation has been specified. -/
noncomputable def publicKey {Γ : Ctx sig} (channel : Var Γ .nm) : Var Γ .nm → Bool :=
  fun name => @decide (name = channel) (Classical.propDecidable _)

theorem publicHeader_colored {Γ : Ctx sig} (kind : ActiveHeaderInvariant.Header)
    (channel : Var Γ .nm) (process : Proc Γ) :
    PublicHeader kind channel process ↔
      HasHeader kind true false (publicKey channel) process := by
  classical
  apply hasHeader_subject_compare
  · simp
  · intro name
    simp only [publicKey, Var.succ.injEq, decide_eq_true_eq]

theorem publicHeader_nu {Γ : Ctx sig} (kind : ActiveHeaderInvariant.Header)
    (channel : Var Γ .nm) (body : Proc (.nm :: Γ)) :
    PublicHeader kind channel (nu body) ↔ PublicHeader kind (.succ channel) body := by
  rw [publicHeader_colored, publicHeader_colored, hasHeader_nu]
  have keys : ActiveMarkedNames.extend false (publicKey channel) = publicKey (Var.succ channel) := by
    classical
    funext name
    cases name <;> simp [ActiveMarkedNames.extend, publicKey]
  rw [keys]

theorem publicHeader_scope_iff : ∀ {Γ Δ : Ctx sig} (scope : Scope Γ Δ)
    (kind : ActiveHeaderInvariant.Header) (channel : Var Γ .nm) (body : Proc Δ),
    PublicHeader kind channel (scope.close body) ↔
      PublicHeader kind (scope.inclusion .nm channel) body
  | _, _, .nil, _, _, _ => Iff.rfl
  | _, _, .bind rest, kind, channel, body =>
      (publicHeader_nu kind channel _).trans (publicHeader_scope_iff rest kind (.succ channel) body)

theorem publicHeader_parallel_iff {Γ : Ctx sig} (kind : ActiveHeaderInvariant.Header)
    (channel : Var Γ .nm) (processes : List (Proc Γ)) :
    PublicHeader kind channel (parallel processes) ↔
      ∃ process ∈ processes, PublicHeader kind channel process := by
  induction processes with
  | nil => simp [parallel, nil, PublicHeader, HasHeader, observations, ActiveSyntaxMarking.mark, ActiveMarkedNames.observe]
  | cons first rest ih =>
      change HasHeader kind _ _ _ (par first (parallel rest)) ↔ _
      rw [hasHeader_par]
      change PublicHeader kind channel first ∨ PublicHeader kind channel (parallel rest) ↔ _
      rw [ih]
      simp

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.ActiveObservation
