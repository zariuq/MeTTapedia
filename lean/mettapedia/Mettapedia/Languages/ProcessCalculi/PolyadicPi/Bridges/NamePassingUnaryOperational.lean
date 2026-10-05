import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingUnaryForward
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolRuntimeTransition

/-!
# Arbitrary unary execution of the name-passing lambda compiler

Every real unary communication is inverted against the retained tuple
registry. Private work leaves the source unchanged; a public communication
is independently read back through the original lambda compiler. Supplied
target endpoints are retained in both cases. Forward execution works from
every related phase, rather than only from freshly emitted programs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingUnaryOperational

open Mettapedia.OSLF.Binding
open Mettapedia.GSLT.IndexedOperational Mettapedia.GSLT.Ultrainfinite
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open NamePassingLambda NamePassingEnvironmentEquationsNative NamePassingUnaryForward
open MonadicProtocol.RuntimeWitness

def Related {Γ : Ctx sig} (source : Expr Γ) (current : Proc (.nm :: Γ)) : Prop :=
  Nonempty (Witness (polyadic source) current)

/-- The debt belongs to the supplied occurrence witness. No uniqueness of
all possible witness presentations is assumed to define an account. -/
theorem readStep {Γ : Ctx sig} {source : Expr Γ} {current after : Proc (.nm :: Γ)}
    (before : Witness (polyadic source) current) (actual : StepModulo current after) :
    (∃ witness : Witness (polyadic source) after, witness.debt + 1 = before.debt) ∨
      ∃ next : Expr Γ, (sourceTheory Γ).Step source next ∧
        ∃ witness : Witness (polyadic next) after, witness.debt + 1 ≤ before.debt + 4 := by
  rcases MonadicProtocol.RuntimeTransition.readStep before actual with unchanged | advanced
  · exact .inl unchanged
  · obtain ⟨physicalAfter, step, witness, counted⟩ := advanced
    obtain ⟨action, next, sourceStep, represented⟩ :=
      NamePassingCompilerReadback.modulo_step_readback source (references Γ)
        (references_faithful Γ) .zero step
    exact .inr ⟨next, ⟨action, sourceStep⟩, witness.changeSource represented.symm, counted⟩

def readback (Γ : Ctx sig) :
    OperationalReadback (sourceTheory Γ) (NativeTypes.operationalTheory (.nm :: Γ)) where
  related := Related
  readStep := by
    rintro source current after ⟨before⟩ actual
    rcases readStep before actual with unchanged | advanced
    · obtain ⟨witness, _⟩ := unchanged
      exact .inl ⟨witness⟩
    · obtain ⟨next, step, witness, _⟩ := advanced
      exact .inr ⟨next, step, ⟨witness⟩⟩

def correspondence (Γ : Ctx sig) :
    OperationalCorrespondence (sourceTheory Γ) (NativeTypes.operationalTheory (.nm :: Γ)) where
  toOperationalReadback := readback Γ
  forward := by
    rintro source next current ⟨before⟩ step
    obtain ⟨path, witness, _, _⟩ := NamePassingUnaryForward.forward before step
    exact ⟨unary next, ⟨path⟩, ⟨witness⟩⟩

theorem compiled_related {Γ : Ctx sig} (source : Expr Γ) : Related source (unary source) := by
  obtain ⟨witness, _⟩ := NamePassingUnaryForward.initial source
  exact ⟨witness⟩

theorem positive_forward {Γ : Ctx sig} {source next : Expr Γ} {current : Proc (.nm :: Γ)}
    (related : Related source current) (step : (sourceTheory Γ).Step source next) :
    ∃ final, ∃ path : ExecutionPath (NativeTypes.operationalTheory (.nm :: Γ)) current final,
      0 < path.length ∧ Related next final := by
  obtain ⟨before⟩ := related
  obtain ⟨path, positive, witness⟩ := NamePassingUnaryForward.forward_positive before step
  exact ⟨unary next, path, positive, witness⟩

structure PrefixResult {Γ : Ctx sig} {source : Expr Γ} {current final : Proc (.nm :: Γ)}
    (before : Witness (polyadic source) current)
    (actual : ExecutionPath (NativeTypes.operationalTheory (.nm :: Γ)) current final) where
  after : Expr Γ
  sourcePath : ExecutionPath (sourceTheory Γ) source after
  witness : Witness (polyadic after) final
  length : sourcePath.length ≤ actual.length
  balance : witness.debt + actual.length ≤ before.debt + 4 * sourcePath.length

/-- The independently supplied prefix keeps its endpoint, its actual source
path and its remaining occurrence debt. A partial tuple call may have committed
a source step before all four implementation communications have happened. -/
theorem retainPrefix {Γ : Ctx sig} {source : Expr Γ} {current final : Proc (.nm :: Γ)}
    (before : Witness (polyadic source) current)
    (actual : ExecutionPath (NativeTypes.operationalTheory (.nm :: Γ)) current final) :
    Nonempty (PrefixResult before actual) := by
  induction actual generalizing source with
  | refl current => exact ⟨⟨source, .refl source, before, le_rfl, by simp only [Route.length]; omega⟩⟩
  | cons first rest ih =>
      rcases readStep before first.down with unchanged | advanced
      · obtain ⟨witness, debt⟩ := unchanged
        obtain ⟨remaining⟩ := ih witness
        refine ⟨⟨remaining.after, remaining.sourcePath, remaining.witness, ?_, ?_⟩⟩
        · change remaining.sourcePath.length ≤ rest.length + 1
          have bound := remaining.length
          change remaining.sourcePath.length ≤ rest.length at bound
          omega
        · change remaining.witness.debt + (rest.length + 1) ≤
            before.debt + 4 * remaining.sourcePath.length
          have bound := remaining.balance
          change remaining.witness.debt + rest.length ≤ witness.debt + 4 * remaining.sourcePath.length at bound
          omega
      · obtain ⟨next, step, witness, debt⟩ := advanced
        obtain ⟨remaining⟩ := ih witness
        refine ⟨⟨remaining.after, .cons ⟨step⟩ remaining.sourcePath, remaining.witness, ?_, ?_⟩⟩
        · change remaining.sourcePath.length + 1 ≤ rest.length + 1
          exact Nat.add_le_add_right remaining.length 1
        · change remaining.witness.debt + (rest.length + 1) ≤
            before.debt + 4 * (remaining.sourcePath.length + 1)
          have bound := remaining.balance
          change remaining.witness.debt + rest.length ≤ witness.debt + 4 * remaining.sourcePath.length at bound
          omega

theorem compiled_prefix {Γ : Ctx sig} (source : Expr Γ) {final : Proc (.nm :: Γ)}
    (actual : ExecutionPath (NativeTypes.operationalTheory (.nm :: Γ)) (unary source) final) :
    ∃ after, ∃ path : ExecutionPath (sourceTheory Γ) source after,
      ∃ witness : Witness (polyadic after) final,
        path.length ≤ actual.length ∧ witness.debt + actual.length ≤ 4 * path.length := by
  obtain ⟨before, zero⟩ := NamePassingUnaryForward.initial source
  obtain ⟨receipt⟩ := retainPrefix before actual
  refine ⟨receipt.after, receipt.sourcePath, receipt.witness, receipt.length, ?_⟩
  have balance := receipt.balance
  rw [zero, Nat.zero_add] at balance
  exact balance

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingUnaryOperational
