import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeCommit
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeClosing

/-!
# Freshness: absent from the store, or never born

Native admission asks that a firing's produced ports be absent from the present store
(`ContextualConditionalExecution.Admitted.fresh`). The commit protocol asks more: a transaction commits
only when the identities it makes were never born (`CommitProtocol.Step.commit`), and born identities
only accumulate. This module proves what each reading gives.

## The protocol realizes exactly the runs that make unborn identities

* **A protocol run splits at its first commit** (`Run.first_commit`), and a run never forgets a born
  identity (`Run.born_subset`).
* **Freshness is forced** (`freshFrom_of_protocol`): a protocol run whose trace carries the commits of a
  native run makes the native run allocate fresh identities (`NativeRun.FreshFrom`) from the born
  identities of its start.
* **The characterization** (`native_run_protocol_iff`): a native run carried by the transactions is
  realized by a protocol run from an idle, unclaimed protocol state holding the present occurrences
  **exactly when** it makes only identities never born before. Under absent-only freshness, a run that
  takes an identity and later makes it again is admitted natively and realized by no protocol run
  (`not_realized_of_reborn`).

## The unborn reading as a step

`nativeUnborn` is the native step over states that carry the identities born so far: a firing is
admitted when it is natively admitted and makes no born identity, and its result adds what it makes.

* **Its runs are the native runs that allocate fresh identities** (`UnbornRun.forget`,
  `UnbornRun.freshFrom_forget`, `UnbornRun.ofFresh`, `UnbornRun.forget_ofFresh`).
* **Every one of its runs is realized by the commit protocol** (`unborn_run_protocol`).
* **Its diamonds are the native diamonds** (`unborn_each_after`, `unborn_closing_born`): two live
  firings that leave each other clear are each admitted at the other's result under unborn freshness,
  and the two orders reach the same born identities.

## Which reading

Absent-only freshness keeps every native diamond and the closing leg, but admits runs the runtime
cannot commit. Unborn freshness keeps the same diamonds and the same closing leg, with the born
identities of both orders equal, and every run is realized by the commit protocol. **Unborn freshness
is the reading faithful to the runtime**: by `native_run_protocol_iff`, absent-only admission agrees
with the runtime exactly on the runs that never remake an identity.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe u v w

variable {O : Type u} [LinearOrder O] {R : Type v} {T : Type w} [DecidableEq T]
  {label : O → R} {txn : T → Commit O R}

/-- **A protocol run never forgets a born identity.** -/
theorem Run.born_subset {σ σ' : ProtocolState O R T} {trace : List (T × Commit O R)}
    (run : Run label txn σ trace σ') : σ.born ⊆ σ'.born := by
  induction run with
  | refl => exact subset_rfl
  | step first _ ih => exact (first.born_subset).trans ih

/-- **A protocol run splits at its first commit**: a run without commits, the commit of the first
transaction of the trace with its fresh identities unborn, and the rest of the run. -/
theorem Run.first_commit {σ σ' : ProtocolState O R T} {trace : List (T × Commit O R)}
    (run : Run label txn σ trace σ') :
    ∀ {t : T} {c : Commit O R} {rest : List (T × Commit O R)}, trace = (t, c) :: rest →
      ∃ σ₁ σ₂ : ProtocolState O R T, Run label txn σ [] σ₁ ∧ c = txn t ∧ Disjoint (txn t).made σ₁.born ∧
        σ₂.born = σ₁.born ∪ (txn t).made ∧ Run label txn σ₂ rest σ' := by
  induction run with
  | refl => intro t c rest same; cases same
  | @step σ σ₁ σ₂ out trace first rest ih =>
      intro t c restT same
      cases out with
      | none =>
          obtain ⟨τ₁, τ₂, run₁, sameCommit, unborn, born, run₂⟩ := ih same
          exact ⟨τ₁, τ₂, .step first run₁, sameCommit, unborn, born, run₂⟩
      | some entry =>
          cases first with
          | commit t' seen active claimed keptLive epochsFresh unborn =>
              simp only [Option.toList_some, List.singleton_append, List.cons.injEq, Prod.mk.injEq] at same
              obtain ⟨⟨rfl, rfl⟩, rfl⟩ := same
              exact ⟨σ, _, .refl σ, rfl, unborn, rfl, rest⟩

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

variable {S : Signature} {O : Type} [LinearOrder O] {Γ : Ctx S} {sort : S.Srt}
  [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

/-! ## The protocol realizes exactly the runs that make unborn identities -/

namespace NativeRun

/-- Freshness from fewer born identities is weaker. -/
theorem FreshFrom.mono :
    ∀ {s : NativeState S O Γ sort} (r : Interface.Step.Run (native (S := S) (O := O) (Γ := Γ) (sort := sort)).toStep s)
      {small big : Finset O}, small ⊆ big → FreshFrom r big → FreshFrom r small
  | _, .nil _, _, _, _, _ => trivial
  | _, .cons _ _ rest, _, _, inside, fresh =>
      And.intro (fresh.1.mono_right inside) (FreshFrom.mono rest (Finset.union_subset_union inside subset_rfl) fresh.2)

end NativeRun

/-- **Freshness is forced**: a protocol run whose trace carries the commits of a native run makes the
native run allocate fresh identities from the born identities of its start. -/
theorem freshFrom_of_protocol (txn : ℕ → Commit O Unit) :
    ∀ {s : NativeState S O Γ sort} (r : Interface.Step.Run (native (S := S) (O := O) (Γ := Γ) (sort := sort)).toStep s)
      (k : ℕ) {σ σ' : ProtocolState O Unit ℕ}, NativeRun.Carries txn r k →
      Run (fun _ : O => ()) txn σ (NativeRun.trace txn r k) σ' → NativeRun.FreshFrom r σ.born
  | _, .nil _, _, _, _, _, _ => trivial
  | _, .cons f _ rest, k, σ, _, carries, run => by
      obtain ⟨carried, carriesRest⟩ := carries
      obtain ⟨σ₁, σ₂, run₁, -, unborn, born, run₂⟩ := run.first_commit rfl
      have before : σ.born ⊆ σ₁.born := run₁.born_subset
      rw [carried] at unborn born
      refine And.intro (unborn.mono_right before) ?_
      refine NativeRun.FreshFrom.mono rest ?_ (freshFrom_of_protocol txn rest (k + 1) carriesRest run₂)
      rw [born]
      exact Finset.union_subset_union before subset_rfl

/-- **The protocol realizes a native run exactly when the run makes only unborn identities.** A native
run carried by transactions `k`, `k + 1`, … is realized by a protocol run from an idle, unclaimed
protocol state whose store holds the present occurrences exactly when no firing makes an identity born
before it. -/
theorem native_run_protocol_iff (txn : ℕ → Commit O Unit) {s : NativeState S O Γ sort}
    (r : Interface.Step.Run (native (S := S) (O := O) (Γ := Γ) (sort := sort)).toStep s) (k : ℕ)
    (σ : ProtocolState O Unit ℕ) (carries : NativeRun.Carries txn r k) (store : σ.store = s.state.present)
    (idle : ∀ i, k ≤ i → σ.phase i = .idle) (unclaimed : ∀ o, σ.claim o = none) :
    (∃ σ', Run (fun _ : O => ()) txn σ (NativeRun.trace txn r k) σ' ∧ σ'.store = r.last.state.present) ↔
      NativeRun.FreshFrom r σ.born :=
  ⟨fun ⟨_, run, _⟩ => freshFrom_of_protocol txn r k carries run,
    fun fresh => native_run_protocol txn r k σ carries fresh store idle unclaimed⟩

/-- **Absent-only freshness is not enough**: a native run that makes an identity born before is
realized by no protocol run. -/
theorem not_realized_of_reborn (txn : ℕ → Commit O Unit) {s : NativeState S O Γ sort}
    (r : Interface.Step.Run (native (S := S) (O := O) (Γ := Γ) (sort := sort)).toStep s) (k : ℕ)
    {σ : ProtocolState O Unit ℕ} (carries : NativeRun.Carries txn r k) (reborn : ¬ NativeRun.FreshFrom r σ.born) :
    ∀ σ', ¬ Run (fun _ : O => ()) txn σ (NativeRun.trace txn r k) σ' :=
  fun _ run => reborn (freshFrom_of_protocol txn r k carries run)

/-! ## The unborn reading as a step -/

/-- **The native step with unborn freshness**: a native state with the identities born so far; a
firing is admitted when it is natively admitted and makes no born identity, and its result adds what
it makes. -/
noncomputable def nativeUnborn :
    Interface.Step.Standard (Frames.contextual S) O (NativeState S O Γ sort × Finset O)
      (fun state => NativeFiring state.1) where
  frame state := (native (S := S) (O := O) (Γ := Γ) (sort := sort)).frame state.1
  knowledge state := native.knowledge state.1
  present state := native.present state.1
  selection f := f.selection
  target f := native.target f
  extension f := native.extension f
  information f := native.information f
  transported f := native.transported f
  Shapes {state} f := native.Shapes f ∧ Disjoint f.selection.made.toFinset state.2
  Holds f := native.Holds f
  Admits {state} f := f.Realized ∧ Disjoint f.selection.made.toFinset state.2
  admits_iff := by
    intro state f
    constructor
    · rintro ⟨realized, unborn⟩
      obtain ⟨shapes, enabled, solvable, asks⟩ := (native_admits_iff f).mp realized
      exact ⟨⟨shapes, unborn⟩, enabled, solvable, asks⟩
    · rintro ⟨⟨shapes, unborn⟩, enabled, solvable, asks⟩
      exact ⟨(native_admits_iff f).mpr ⟨shapes, enabled, solvable, asks⟩, unborn⟩
  preparedResult {state} f p :=
    (native.preparedResult f ⟨p.1.1, p.2.1, p.2.2⟩, state.2 ∪ f.selection.made.toFinset)
  present_preparedResult f p := native.present_preparedResult f ⟨p.1.1, p.2.1, p.2.2⟩
  preparedSettle f p := native.preparedSettle f ⟨p.1.1, p.2.1, p.2.2⟩
  knowledge_preparedResult f p := native.knowledge_preparedResult f ⟨p.1.1, p.2.1, p.2.2⟩

namespace UnbornRun

/-- An unborn run, with its born identities forgotten. -/
noncomputable def forget : {state : NativeState S O Γ sort × Finset O} →
    Interface.Step.Run (nativeUnborn (S := S) (O := O) (Γ := Γ) (sort := sort)).toStep state →
      Interface.Step.Run (native (S := S) (O := O) (Γ := Γ) (sort := sort)).toStep state.1
  | _, .nil state => .nil state.1
  | _, .cons f admitted rest => .cons f admitted.1 (forget rest)

/-- **An unborn run allocates fresh identities.** -/
theorem freshFrom_forget : ∀ {state : NativeState S O Γ sort × Finset O}
    (r : Interface.Step.Run (nativeUnborn (S := S) (O := O) (Γ := Γ) (sort := sort)).toStep state),
    NativeRun.FreshFrom (forget r) state.2
  | _, .nil _ => trivial
  | _, .cons _ admitted rest => And.intro admitted.2 (freshFrom_forget rest)

/-- A native run that allocates fresh identities is an unborn run. -/
noncomputable def ofFresh : {s : NativeState S O Γ sort} → (born : Finset O) →
    (r : Interface.Step.Run (native (S := S) (O := O) (Γ := Γ) (sort := sort)).toStep s) → NativeRun.FreshFrom r born →
      Interface.Step.Run (nativeUnborn (S := S) (O := O) (Γ := Γ) (sort := sort)).toStep (s, born)
  | _, _, .nil s, _ => .nil (s, _)
  | _, born, .cons f admitted rest, fresh =>
      .cons (s := (_, born)) f ⟨admitted, fresh.1⟩ (ofFresh (born ∪ f.selection.made.toFinset) rest fresh.2)

theorem forget_ofFresh : ∀ {s : NativeState S O Γ sort} (born : Finset O)
    (r : Interface.Step.Run (native (S := S) (O := O) (Γ := Γ) (sort := sort)).toStep s) (fresh : NativeRun.FreshFrom r born),
    forget (ofFresh born r fresh) = r
  | _, _, .nil _, _ => rfl
  | _, born, .cons f admitted rest, fresh =>
      congrArg (Interface.Step.Run.cons f admitted) (forget_ofFresh (born ∪ f.selection.made.toFinset) rest fresh.2)

end UnbornRun

/-- **Every run of the unborn reading is realized by the commit protocol**, from an idle, unclaimed
protocol state holding the present occurrences with the run's born identities. -/
theorem unborn_run_protocol (txn : ℕ → Commit O Unit) {state : NativeState S O Γ sort × Finset O}
    (r : Interface.Step.Run (nativeUnborn (S := S) (O := O) (Γ := Γ) (sort := sort)).toStep state) (k : ℕ)
    (σ : ProtocolState O Unit ℕ) (carries : NativeRun.Carries txn (UnbornRun.forget r) k)
    (born : σ.born = state.2) (store : σ.store = state.1.state.present)
    (idle : ∀ i, k ≤ i → σ.phase i = .idle) (unclaimed : ∀ o, σ.claim o = none) :
    ∃ σ', Run (fun _ : O => ()) txn σ (NativeRun.trace txn (UnbornRun.forget r) k) σ' ∧
      σ'.store = (UnbornRun.forget r).last.state.present :=
  native_run_protocol txn (UnbornRun.forget r) k σ carries (born ▸ UnbornRun.freshFrom_forget r) store idle unclaimed

/-! ## Diamonds under unborn freshness -/

/-- **Each stays admitted after the other under unborn freshness**: two live firings that leave each
other clear and make no born identity are each admitted, under unborn freshness, at the other's
result. -/
theorem unborn_each_after {s : NativeState S O Γ sort} {born : Finset O} {f g : LiveFiring s}
    (first : f.toNative.Realized) (second : g.toNative.Realized)
    (unbornF : Disjoint f.selection.made.toFinset born) (unbornG : Disjoint g.selection.made.toFinset born)
    (clearF : Clear f g.selection g.rule g.outputs) (clearG : Clear g f.selection f.rule f.outputs) :
    (nativeUnborn (S := S) (O := O) (Γ := Γ) (sort := sort)).Admits
        (s := (native.result g.toNative second, born ∪ g.selection.made.toFinset)) (LiveFiring.residual second f) ∧
      (nativeUnborn (S := S) (O := O) (Γ := Γ) (sort := sort)).Admits
        (s := (native.result f.toNative first, born ∪ f.selection.made.toFinset)) (LiveFiring.residual first g) :=
  ⟨⟨LiveFiring.after first second clearF, Finset.disjoint_union_right.mpr ⟨unbornF, clearF.ports⟩⟩,
    ⟨LiveFiring.after second first clearG, Finset.disjoint_union_right.mpr ⟨unbornG, clearG.ports⟩⟩⟩

/-- **The two orders reach the same born identities.** -/
theorem unborn_closing_born {s : NativeState S O Γ sort} (born : Finset O) {f g : LiveFiring s}
    (first : f.toNative.Realized) (second : g.toNative.Realized) :
    born ∪ g.selection.made.toFinset ∪ (LiveFiring.residual second f).selection.made.toFinset =
      born ∪ f.selection.made.toFinset ∪ (LiveFiring.residual first g).selection.made.toFinset := by
  show born ∪ g.selection.made.toFinset ∪ f.selection.made.toFinset =
    born ∪ f.selection.made.toFinset ∪ g.selection.made.toFinset
  rw [Finset.union_assoc, Finset.union_comm g.selection.made.toFinset, ← Finset.union_assoc]

#print axioms Run.born_subset
#print axioms Run.first_commit
#print axioms NativeRun.FreshFrom.mono
#print axioms freshFrom_of_protocol
#print axioms native_run_protocol_iff
#print axioms not_realized_of_reborn
#print axioms UnbornRun.freshFrom_forget
#print axioms UnbornRun.forget_ofFresh
#print axioms unborn_run_protocol
#print axioms unborn_each_after
#print axioms unborn_closing_born

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
