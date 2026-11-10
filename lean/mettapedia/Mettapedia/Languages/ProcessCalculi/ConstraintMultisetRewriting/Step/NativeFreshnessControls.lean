import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeFreshness
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeResidualExample

/-!
# Control: fresh under absent-only freshness, not fresh from the born identities

Native admission asks that the identities a firing makes be **absent** from the present store; the
commit protocol asks that they were **never born** (`Step/NativeFreshness`). This control separates the
two on a concrete native run.

* **The native run** (`makerRun`): the maker of occurrence `0` at the state with no occurrences
  (`NativeResidualExample.initial`), one firing. It is admitted: `0` is absent.
* **A reachable protocol history that has born `0` and consumed it** (`history_run`): from the initial
  protocol state (`start`), transaction `0` makes the occurrence `0` and transaction `1` takes it. The
  store is then empty again, the store the native state holds, and `0` is born.
* **No protocol run realizes the native run after that history** (`maker_not_realized`): the run is
  not fresh from the born identities (`maker_not_fresh`), so `not_realized_of_reborn` applies.
* **Positive control** (`maker_realized_from_start`): from the initial protocol state, where `0` was
  never born, the protocol realizes the same native run.

Both protocol states hold the same store, the present occurrences of the native state; only their
born ledgers differ. Absent-only freshness cannot tell them apart; the runtime can.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open NativeResidualExample (tiny initial maker maker_realized)

namespace NativeFreshnessControls

/-- **The native run**: the maker of occurrence `0`, at the state with no occurrences. -/
noncomputable def makerRun :
    Interface.Step.Run (native (S := tiny) (O := ℕ) (Γ := ([] : Ctx tiny)) (sort := ())).toStep initial :=
  .cons (maker 0 none).toNative (maker_realized 0 none) (.nil _)

/-- **The native run is fresh under absent-only freshness**: the identity it makes is absent from the
present occurrences. -/
theorem maker_absent : Disjoint (maker 0 none).selection.made.toFinset initial.state.present := by
  show Disjoint [0].toFinset (∅ : Finset ℕ)
  simp

/-- Transaction `0` makes the occurrence `0`, transaction `1` takes it, and transaction `2` is the native
maker's commit. -/
def history : ℕ → Commit ℕ Unit
  | 0 => ⟨∅, ∅, {0}, []⟩
  | 1 => ⟨{0}, ∅, ∅, []⟩
  | _ => (maker 0 none).selection.commit (T := Unit)

/-- The initial protocol state: nothing stored, nothing born, nothing claimed, every transaction idle. -/
def start : ProtocolState ℕ Unit ℕ where
  store := ∅
  born := ∅
  claim _ := none
  epoch _ := 0
  phase _ := .idle

theorem start_initial : Initial start := ⟨subset_rfl, fun _ => rfl, fun _ => rfl⟩

/-- **A reachable history that has born `0` and consumed it**: the store is empty again, and `0` is
born; transaction `2` is still idle and nothing is claimed. -/
theorem history_run :
    ∃ σ, Run (fun _ : ℕ => ()) history start [(0, history 0), (1, history 1)] σ ∧ σ.store = ∅ ∧ 0 ∈ σ.born ∧
      σ.phase 2 = .idle ∧ ∀ o, σ.claim o = none := by
  obtain ⟨σ₁, run₁, store₁, born₁, claims₁, _, phases₁⟩ :=
    Run.single (label := fun _ : ℕ => ()) (txn := history) (σ := start) (t := 0) rfl
      ⟨by simp [history], by simp [history], by simp [history], by simp [history, start],
        fun _ member => by simp [history] at member⟩
      (fun _ taken => by simp [history] at taken) (by simp [history, start])
  have unclaimed₁ : ∀ o, σ₁.claim o = none := fun o => (claims₁ o (by simp [history])).trans rfl
  obtain ⟨σ₂, run₂, store₂, born₂, claims₂, released₂, phases₂⟩ :=
    Run.single (label := fun _ : ℕ => ()) (txn := history) (σ := σ₁) (t := 1)
      ((phases₁ 1 (by decide)).trans rfl)
      ⟨by rw [store₁]; simp [history, fire], by simp [history], by simp [history],
        by simp [history], fun _ member => by simp [history] at member⟩
      (fun o _ => unclaimed₁ o) (by simp [history])
  refine ⟨σ₂, Run.trans run₁ run₂, ?_, ?_, ?_, fun o => ?_⟩
  · rw [store₂, store₁]
    simp [history, fire, start]
  · rw [born₂, born₁]
    simp [history, start]
  · rw [phases₂ 2 (by decide), phases₁ 2 (by decide)]
    rfl
  · by_cases taken : o ∈ (history 1).taken
    · exact released₂ o taken
    · exact (claims₂ o taken).trans (unclaimed₁ o)

/-- The transactions from `2` on carry the native run's commit. -/
theorem carries : NativeRun.Carries history makerRun 2 := ⟨rfl, trivial⟩

/-- **The native run is not fresh from the born identities of the history.** -/
theorem maker_not_fresh {σ : ProtocolState ℕ Unit ℕ} (born : 0 ∈ σ.born) : ¬ NativeRun.FreshFrom makerRun σ.born := by
  rintro ⟨apart, _⟩
  exact Finset.disjoint_left.mp apart (show 0 ∈ [0].toFinset by simp) born

/-- **After the history, no protocol run realizes the native run**, although the protocol's store is
the native state's present occurrences and the run is admitted natively. -/
theorem maker_not_realized :
    ∃ σ, Run (fun _ : ℕ => ()) history start [(0, history 0), (1, history 1)] σ ∧
      σ.store = initial.state.present ∧
      ∀ σ', ¬ Run (fun _ : ℕ => ()) history σ (NativeRun.trace history makerRun 2) σ' := by
  obtain ⟨σ, run, store, born, _, _⟩ := history_run
  exact ⟨σ, run, store, not_realized_of_reborn history makerRun 2 carries (maker_not_fresh born)⟩

/-- **Positive control**: from the initial protocol state, where `0` was never born, the protocol
realizes the same native run. -/
theorem maker_realized_from_start :
    ∃ σ', Run (fun _ : ℕ => ()) history start (NativeRun.trace history makerRun 2) σ' ∧
      σ'.store = makerRun.last.state.present :=
  (native_run_protocol_iff history makerRun 2 start carries rfl (fun _ _ => rfl) (fun _ => rfl)).mpr
    ⟨by simp [start], trivial⟩

end NativeFreshnessControls

#print axioms NativeFreshnessControls.maker_absent
#print axioms NativeFreshnessControls.history_run
#print axioms NativeFreshnessControls.maker_not_fresh
#print axioms NativeFreshnessControls.maker_not_realized
#print axioms NativeFreshnessControls.maker_realized_from_start

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
