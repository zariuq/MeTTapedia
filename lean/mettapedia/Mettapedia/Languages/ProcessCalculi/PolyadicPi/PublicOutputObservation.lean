import Mettapedia.Languages.ProcessCalculi.PolyadicPi.NativeTypes
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedActiveFrontier
import Mettapedia.GSLT.Core.GSLTConstructions
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveHeaderInvariant
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveMarkedNames

/-!
# Public output observations of scoped polyadic pi

An output is active through parallel composition, restrictions and
replication, but not through an input guard. Under a restriction the queried
ambient channel is lifted, so a newly private subject is not mistaken for
that public channel. The observation admits the stated structural equations;
it is independent of any compiler or implementation scheduler.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.PublicOutputObservation

open Mettapedia.OSLF.Binding
open Mettapedia.GSLT
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedActiveFrontier
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveHeaderInvariant

/-- Active public output occurrences, with input continuations opaque. -/
inductive ActiveOutput : {Γ : Ctx sig} → Var Γ .nm → Proc Γ → Prop
  | unary {Γ : Ctx sig} (channel datum : Var Γ .nm) :
      ActiveOutput channel (out1 (.var channel) (.var datum))
  | binary {Γ : Ctx sig} (channel first second : Var Γ .nm) :
      ActiveOutput channel (out2 (.var channel) (.var first) (.var second))
  | parLeft {Γ : Ctx sig} {channel : Var Γ .nm} {process : Proc Γ}
      (frame : Proc Γ) : ActiveOutput channel process → ActiveOutput channel (par process frame)
  | parRight {Γ : Ctx sig} {channel : Var Γ .nm} {process : Proc Γ}
      (frame : Proc Γ) : ActiveOutput channel process → ActiveOutput channel (par frame process)
  | restricted {Γ : Ctx sig} {channel : Var Γ .nm} {body : Proc (.nm :: Γ)} :
      ActiveOutput (.succ channel) body → ActiveOutput channel (nu body)
  | replicated {Γ : Ctx sig} {channel : Var Γ .nm} {body : Proc Γ} :
      ActiveOutput channel body → ActiveOutput channel (rep body)

/-- Interpret private names by one fresh marker while observing a supplied
public subject. Private names need not be distinguished from one another. -/
def availability {Ω : Ctx sig} (fresh subject : Var Ω .nm) :
    {Γ : Ctx sig} → Ren sig Γ Ω → Proc Γ → Prop
  | _, _, .var _ => False
  | _, _, .op .nil .nil => False
  | _, environment, .op .par (.cons first (.cons second .nil)) =>
      availability fresh subject environment first ∨ availability fresh subject environment second
  | _, _, .op .inp1 (.cons _ (.cons _ .nil)) => False
  | _, _, .op .inp2 (.cons _ (.cons _ .nil)) => False
  | _, environment, .op .out1 (.cons channel (.cons _ .nil)) =>
      Bridges.ActiveMarkedNames.nameKey (environment .nm) channel = subject
  | _, environment, .op .out2 (.cons channel (.cons _ (.cons _ .nil))) =>
      Bridges.ActiveMarkedNames.nameKey (environment .nm) channel = subject
  | _, environment, .op .nu (.cons body .nil) =>
      availability fresh subject (prependRen fresh environment) body
  | _, environment, .op .rep (.cons body .nil) => availability fresh subject environment body
termination_by _ _ process => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

private theorem nameKey_rename {Γ Δ Ω : Ctx sig} (reindex : Ren sig Γ Δ)
    (environment : Ren sig Δ Ω) (channel : Name Γ) :
    Bridges.ActiveMarkedNames.nameKey (environment .nm) (rename reindex channel) =
      Bridges.ActiveMarkedNames.nameKey (fun name => environment .nm (reindex .nm name)) channel := by
  cases channel with
  | var name => rfl
  | op operator _ => cases operator

private theorem extension_comp {Γ Δ Ω : Ctx sig} (reindex : Ren sig Γ Δ)
    (environment : Ren sig Δ Ω) (fresh : Var Ω .nm) :
    (fun sort name => prependRen fresh environment sort (liftRen reindex [.nm] sort name)) =
      prependRen fresh (fun sort name => environment sort (reindex sort name)) := by
  funext sort name
  cases name <;> rfl

theorem availability_rename {Ω : Ctx sig} (fresh subject : Var Ω .nm) :
    ∀ {Γ Δ : Ctx sig} (reindex : Ren sig Γ Δ) (environment : Ren sig Δ Ω) (process : Proc Γ),
      availability fresh subject environment (rename reindex process) ↔
        availability fresh subject (fun sort name => environment sort (reindex sort name)) process
  | _, _, _, _, .var _ => by simp only [rename, availability]
  | _, _, _, _, .op .nil .nil => by simp only [rename, renameArgs, availability]
  | _, _, reindex, environment, .op .par (.cons first (.cons second .nil)) => by
      simp only [rename, renameArgs, liftRen, availability]
      exact or_congr (availability_rename fresh subject reindex environment first)
        (availability_rename fresh subject reindex environment second)
  | _, _, _, _, .op .inp1 (.cons _ (.cons _ .nil)) => by simp only [rename, renameArgs, availability]
  | _, _, _, _, .op .inp2 (.cons _ (.cons _ .nil)) => by simp only [rename, renameArgs, availability]
  | _, _, reindex, environment, .op .out1 (.cons channel (.cons _ .nil)) => by
      simp only [rename, renameArgs, liftRen, availability]
      rw [nameKey_rename reindex environment channel]
  | _, _, reindex, environment, .op .out2 (.cons channel (.cons _ (.cons _ .nil))) => by
      simp only [rename, renameArgs, liftRen, availability]
      rw [nameKey_rename reindex environment channel]
  | _, _, reindex, environment, .op .nu (.cons body .nil) => by
      simp only [rename, renameArgs, availability]
      rw [availability_rename fresh subject (liftRen reindex [.nm]) _ body, extension_comp]
  | _, _, reindex, environment, .op .rep (.cons body .nil) => by
      simp only [rename, renameArgs, liftRen, availability]
      exact availability_rename fresh subject reindex environment body
termination_by _ _ _ _ process => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

private theorem swap_environment {Γ Ω : Ctx sig} (fresh : Var Ω .nm) (environment : Ren sig Γ Ω) :
    (fun sort name => prependRen fresh (prependRen fresh environment) sort (swapRen sort name)) =
      prependRen fresh (prependRen fresh environment) := by
  funext sort name
  cases name with
  | zero => rfl
  | succ name => cases name <;> rfl

/-- Public availability respects all existing scope and replication laws.
This preserves existence of an output, rather than its finite multiplicity. -/
theorem availability_structural {Ω Γ : Ctx sig} (fresh subject : Var Ω .nm)
    {first second : Proc Γ} (equal : StructuralEq first second) :
    ∀ environment : Ren sig Γ Ω,
      availability fresh subject environment first ↔ availability fresh subject environment second := by
  induction equal with
  | refl => intro environment; rfl
  | symm _ ih => intro environment; exact (ih environment).symm
  | trans _ _ firstIH secondIH => intro environment; exact (firstIH environment).trans (secondIH environment)
  | parComm => intro environment; simp only [par, availability, or_comm]
  | parAssoc => intro environment; simp only [par, availability, or_assoc]
  | parUnit => intro environment; simp only [par, nil, availability, or_false]
  | nuUnused => intro environment; simp only [nu, availability, weaken, availability_rename]; rfl
  | nuPar => intro environment; simp only [nu, par, availability, weaken, availability_rename]; rfl
  | nuSwap => intro environment; simp only [nu, availability, availability_rename, swap_environment]
  | repUnfold => intro environment; simp only [rep, par, availability, or_self]
  | par _ _ firstIH secondIH =>
      intro environment
      simp only [par, availability]
      exact or_congr (firstIH environment) (secondIH environment)
  | nu _ ih => intro environment; simpa only [nu, availability] using ih (prependRen fresh environment)
  | inp1 => intro environment; simp only [inp1, availability]
  | inp2 => intro environment; simp only [inp2, availability]
  | rep _ ih => intro environment; simpa only [rep, availability] using ih environment

private theorem extension_separates {Γ Ω : Ctx sig} (environment : Ren sig Γ Ω)
    (channel : Var Γ .nm) (fresh subject : Var Ω .nm) (disjoint : fresh ≠ subject)
    (separates : ∀ name, environment .nm name = subject ↔ name = channel) :
    ∀ name, prependRen fresh environment .nm name = subject ↔ name = Var.succ channel := by
  intro name
  cases name with
  | zero => simp [prependRen, disjoint]
  | succ name => simpa only [prependRen, Var.succ.injEq] using separates name

/-- A name interpretation only needs to separate the observed public name
from its private marker and every other source name. -/
theorem availability_iff_active {Ω : Ctx sig} (fresh subject : Var Ω .nm)
    (disjoint : fresh ≠ subject) : ∀ {Γ : Ctx sig} (environment : Ren sig Γ Ω)
      (channel : Var Γ .nm) (process : Proc Γ),
      (∀ name, environment .nm name = subject ↔ name = channel) →
      (availability fresh subject environment process ↔ ActiveOutput channel process)
  | _, _, _, .var _, _ => by simp only [availability]; constructor <;> intro active <;> cases active
  | _, _, _, .op .nil .nil, _ => by simp only [availability]; constructor <;> intro active <;> cases active
  | _, environment, channel, .op .par (.cons first (.cons second .nil)), separates => by
      simp only [availability]
      rw [availability_iff_active fresh subject disjoint environment channel first separates,
        availability_iff_active fresh subject disjoint environment channel second separates]
      constructor
      · rintro (active | active)
        · exact .parLeft second active
        · exact .parRight first active
      · intro active
        cases active with
        | parLeft _ observed => exact .inl observed
        | parRight _ observed => exact .inr observed
  | _, _, _, .op .inp1 (.cons _ (.cons _ .nil)), _ => by simp only [availability]; constructor <;> intro active <;> cases active
  | _, _, _, .op .inp2 (.cons _ (.cons _ .nil)), _ => by simp only [availability]; constructor <;> intro active <;> cases active
  | _, environment, channel, .op .out1 (.cons sent (.cons datum .nil)), separates => by
      cases sent with
      | op operator _ => cases operator
      | var sent =>
          cases datum with
          | op operator _ => cases operator
          | var datum =>
              simp only [availability, Bridges.ActiveMarkedNames.nameKey]
              change (environment .nm sent = subject) ↔ ActiveOutput channel (out1 (.var sent) (.var datum))
              rw [separates]
              constructor
              · intro same; subst sent; exact .unary channel datum
              · intro active; cases active; rfl
  | _, environment, channel, .op .out2 (.cons sent (.cons first (.cons second .nil))), separates => by
      cases sent with
      | op operator _ => cases operator
      | var sent =>
          cases first with
          | op operator _ => cases operator
          | var first =>
              cases second with
              | op operator _ => cases operator
              | var second =>
                  simp only [availability, Bridges.ActiveMarkedNames.nameKey]
                  change (environment .nm sent = subject) ↔ ActiveOutput channel (out2 (.var sent) (.var first) (.var second))
                  rw [separates]
                  constructor
                  · intro same; subst sent; exact .binary channel first second
                  · intro active; cases active; rfl
  | _, environment, channel, .op .nu (.cons body .nil), separates => by
      simp only [availability]
      rw [availability_iff_active fresh subject disjoint (prependRen fresh environment) (.succ channel) body
        (extension_separates environment channel fresh subject disjoint separates)]
      constructor
      · exact fun active => .restricted active
      · intro active; cases active with | restricted observed => exact observed
  | _, environment, channel, .op .rep (.cons body .nil), separates => by
      simp only [availability]
      rw [availability_iff_active fresh subject disjoint environment channel body separates]
      constructor
      · exact fun active => .replicated active
      · intro active; cases active with | replicated observed => exact observed
termination_by _ _ _ process _ => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

theorem active_structural_congr {Γ : Ctx sig} (channel : Var Γ .nm) {first second : Proc Γ}
    (equal : StructuralEq first second) : ActiveOutput channel first ↔ ActiveOutput channel second := by
  let environment : Ren sig Γ (.nm :: Γ) := fun _ name => Var.succ name
  have disjoint : (Var.zero : Var (.nm :: Γ) .nm) ≠ Var.succ channel := by intro same; cases same
  have separates : ∀ name, environment .nm name = Var.succ channel ↔ name = channel := by
    intro name
    simp only [environment, Var.succ.injEq]
  rw [← availability_iff_active .zero (.succ channel) disjoint environment channel first separates,
    ← availability_iff_active .zero (.succ channel) disjoint environment channel second separates]
  exact availability_structural .zero (.succ channel) equal environment

def HasOutput {Γ : Ctx sig} (channel : Var Γ .nm) (process : Proc Γ) : Prop :=
  ∃ representative, StructuralEq process representative ∧ ActiveOutput channel representative

/-- Equation saturation cannot manufacture a public output occurrence. -/
theorem hasOutput_iff_active {Γ : Ctx sig} (channel : Var Γ .nm) (process : Proc Γ) :
    HasOutput channel process ↔ ActiveOutput channel process := by
  constructor
  · rintro ⟨representative, equal, active⟩
    exact (active_structural_congr channel equal).mpr active
  · exact fun active => ⟨process, .refl _, active⟩

theorem ActiveOutput.header_available {Γ : Ctx sig} {channel : Var Γ .nm} {process : Proc Γ}
    (active : ActiveOutput channel process) :
    visible .output1 process = true ∨ visible .output2 process = true := by
  induction active with
  | unary => exact .inl (by simp [visible, out1])
  | binary => exact .inr (by simp [visible, out2])
  | parLeft frame _ ih =>
      rcases ih with unary | binary
      · exact .inl (by simp only [par, visible, unary, Bool.true_or])
      · exact .inr (by simp only [par, visible, binary, Bool.true_or])
  | parRight frame _ ih =>
      rcases ih with unary | binary
      · exact .inl (by simp only [par, visible, unary, Bool.or_true])
      · exact .inr (by simp only [par, visible, binary, Bool.or_true])
  | restricted _ ih => simpa only [nu, visible] using ih
  | replicated _ ih => simpa only [rep, visible] using ih

theorem no_output_of_invisible {Γ : Ctx sig} (channel : Var Γ .nm) (process : Proc Γ)
    (unary : visible .output1 process = false) (binary : visible .output2 process = false) :
    ¬ HasOutput channel process := by
  rintro ⟨representative, equation, active⟩
  rcases active.header_available with first | second
  · rw [← visible_structural .output1 equation, unary] at first
    cases first
  · rw [← visible_structural .output2 equation, binary] at second
    cases second

theorem output_observed {Γ : Ctx sig} (channel datum : Var Γ .nm) :
    HasOutput channel (out1 (.var channel) (.var datum)) :=
  ⟨_, .refl _, .unary channel datum⟩

theorem nil_has_no_output {Γ : Ctx sig} (channel : Var Γ .nm) :
    ¬ HasOutput channel nil := no_output_of_invisible channel nil
  (by simp [visible, nil]) (by simp [visible, nil])

/-- Static rearrangements do not activate an output suspended by an input. -/
theorem input_guard_has_no_output {Γ : Ctx sig} (channel : Var Γ .nm)
    (subject : Name Γ) (body : Proc (.nm :: Γ)) :
    ¬ HasOutput channel (inp1 subject body) :=
  no_output_of_invisible channel (inp1 subject body)
    (by simp [visible, inp1]) (by simp [visible, inp1])

theorem structural_congr {Γ : Ctx sig} (channel : Var Γ .nm) {first second : Proc Γ}
    (equal : StructuralEq first second) : HasOutput channel first ↔ HasOutput channel second := by
  constructor
  · rintro ⟨representative, equation, active⟩
    exact ⟨representative, .trans (.symm equal) equation, active⟩
  · rintro ⟨representative, equation, active⟩
    exact ⟨representative, .trans equal equation, active⟩

theorem active_parallel_member {Γ : Ctx sig} (channel : Var Γ .nm)
    (processes : List (Proc Γ)) {selected : Proc Γ} (member : selected ∈ processes)
    (active : ActiveOutput channel selected) : ActiveOutput channel (parallel processes) := by
  induction processes with
  | nil => simp at member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact .parLeft _ active
      · exact .parRight _ (ih member)

theorem active_scope : ∀ {Γ Δ : Ctx sig} (scope : Scope Γ Δ)
    (channel : Var Γ .nm) {body : Proc Δ},
    ActiveOutput (scope.inclusion .nm channel) body → ActiveOutput channel (scope.close body)
  | _, _, .nil, _, _, active => active
  | _, _, .bind rest, channel, _, active => .restricted (active_scope rest (.succ channel) active)

theorem active_scope_iff : ∀ {Γ Δ : Ctx sig} (scope : Scope Γ Δ)
    (channel : Var Γ .nm) (body : Proc Δ),
    ActiveOutput channel (scope.close body) ↔ ActiveOutput (scope.inclusion .nm channel) body
  | _, _, .nil, _, _ => Iff.rfl
  | _, _, .bind rest, channel, body => by
      constructor
      · intro observed
        cases observed with
        | restricted inside => exact (active_scope_iff rest (.succ channel) body).mp inside
      · exact fun observed => .restricted ((active_scope_iff rest (.succ channel) body).mpr observed)

theorem active_parallel_selected {Γ : Ctx sig} (channel : Var Γ .nm)
    (processes : List (Proc Γ)) (observed : ActiveOutput channel (parallel processes)) :
    ∃ selected ∈ processes, ActiveOutput channel selected := by
  induction processes with
  | nil => cases observed
  | cons first rest ih =>
      cases observed with
      | parLeft _ active => exact ⟨first, by simp, active⟩
      | parRight _ active =>
          obtain ⟨selected, member, active⟩ := ih active
          exact ⟨selected, List.mem_cons_of_mem _ member, active⟩

/-- This source observation supplies an equation-saturated native type
both for one-step semantics and for its existing execution closure. -/
def nativePredicate {Γ : Ctx sig} (channel : Var Γ .nm) :
    EquationPredicate (NativeTypes.operationalTheory Γ) :=
  ⟨HasOutput channel, fun _ _ equal => structural_congr channel equal⟩

def closurePredicate {Γ : Ctx sig} (channel : Var Γ .nm) :
    EquationPredicate (NativeTypes.operationalTheory Γ).closure :=
  ⟨HasOutput channel, fun _ _ equal => structural_congr channel equal⟩

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.PublicOutputObservation
