import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeDiamond
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.CommitProtocol

/-!
# Native firings realized by the commit protocol

The commit protocol (`OccurrenceCommits.CommitProtocol`) is the runtime's view of a commit: a
transaction begins at a store where its commit is enabled, claims what it takes in canonical order,
and commits when its takes are claimed, its keeps live and its fresh identities unborn.

* **Claims in canonical order** (`Run.claim_sorted`): an active transaction claims every
  occurrence it takes, smallest first, by a run of claim steps that leaves every other claim as it
  was.
* **One transaction begins, claims and commits** (`Run.single`), leaving the other transactions'
  phases and the claims outside its takes as they were.
* **Every native firing is realized by a protocol run** (`native_protocol_run`): a transaction whose
  commit is the native firing's commit begins at a store holding the state's present occurrences,
  claims, and commits, and the protocol's store is then the present occurrences of the native
  result. The fresh identities must be **unborn**, not only absent from the store.
* **That hypothesis is needed** (`Run.reborn_never_commits`, `Controls.remake_never_commits`): born
  identities only accumulate (`Step.born_subset`), so a transaction that makes an identity already
  born commits in no continuation, although its commit is enabled at the store, as the native step's
  admission asks (`Controls.remake_enabled`).
* **Apart native firings commit concurrently, in either order** (`native_protocol_concurrent`): for
  two apart admitted firings (`NativeFiring.Apart`, `Step/NativeDiamond`), two transactions begin,
  claim, and then commit in either order; both orders end at the composite physical result. This is
  the protocol side of the frame-free half of the native diamond.
* **Every native run that allocates fresh identities is realized by a protocol run**
  (`native_run_protocol`): transaction `k + i` carries the `i`-th firing's commit
  (`NativeRun.Carries`), no firing makes an identity already born or made earlier
  (`NativeRun.FreshFrom`), and the protocol's store ends at the present occurrences of the run's last
  state.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe u v w

variable {O : Type u} [LinearOrder O] {R : Type v} {T : Type w} [DecidableEq T]
  {label : O → R} {txn : T → Commit O R}

/-- Runs compose. -/
theorem Run.trans {σ σ' σ'' : ProtocolState O R T} {first second : List (T × Commit O R)}
    (one : Run label txn σ first σ') : Run label txn σ' second σ'' → Run label txn σ (first ++ second) σ'' := by
  induction one with
  | refl => exact id
  | step step _ ih =>
      intro two
      rw [List.append_assoc]
      exact Run.step step (ih two)

/-- **Claims in canonical order**: an active transaction claims the occurrences of a sorted list of
its takes, smallest first, when they are live and unclaimed and every other take is already its. -/
theorem Run.claim_sorted (t : T) (seen : (R → Bool) → ℕ) :
    ∀ (pending : List O) (σ : ProtocolState O R T), pending.Pairwise (· ≤ ·) → pending.Nodup →
      σ.phase t = .active seen →
      (∀ o ∈ pending, o ∈ (txn t).taken ∧ o ∈ σ.store ∧ σ.claim o = none) →
      (∀ o ∈ (txn t).taken, o ∉ pending → σ.claim o = some t) →
      ∃ claim : O → Option T, Run label txn σ [] { σ with claim := claim } ∧
        (∀ o ∈ (txn t).taken, claim o = some t) ∧ ∀ o, o ∉ pending → claim o = σ.claim o
  | [], σ, _, _, _, _, claimed =>
      ⟨σ.claim, .refl σ, fun o taken => claimed o taken List.not_mem_nil, fun _ _ => rfl⟩
  | o :: rest, σ, sorted, nodup, active, pending, claimed => by
      obtain ⟨taken, live, free⟩ := pending o List.mem_cons_self
      have fresh : o ∉ rest := (List.nodup_cons.mp nodup).1
      have canonical : ∀ o' ∈ (txn t).taken, o' < o → σ.claim o' = some t := by
        intro o' taken' smaller
        refine claimed o' taken' fun member => ?_
        rcases List.mem_cons.mp member with same | inRest
        · exact absurd same (ne_of_lt smaller)
        · exact absurd ((List.pairwise_cons.mp sorted).1 o' inRest) (not_le.mpr smaller)
      obtain ⟨claim, run, all, outside⟩ := Run.claim_sorted t seen rest
        { σ with claim := Function.update σ.claim o (some t) }
        (List.pairwise_cons.mp sorted).2 (List.nodup_cons.mp nodup).2 active
        (fun o' inRest => by
          obtain ⟨taken', live', free'⟩ := pending o' (List.mem_cons_of_mem _ inRest)
          have different : o' ≠ o := fun same => fresh (same ▸ inRest)
          exact ⟨taken', live', by simp [Function.update_of_ne different, free']⟩)
        (fun o' taken' notRest => by
          by_cases same : o' = o
          · subst same
            simp
          · have notPending : o' ∉ o :: rest := fun member =>
              (List.mem_cons.mp member).elim same notRest
            simp [Function.update_of_ne same, claimed o' taken' notPending])
      refine ⟨claim, .step (.claim σ t seen o active taken live free canonical) run, all, fun o' notPending => ?_⟩
      have different : o' ≠ o := fun same => notPending (same ▸ List.mem_cons_self)
      rw [outside o' fun inRest => notPending (List.mem_cons_of_mem _ inRest)]
      exact Function.update_of_ne different _ _


/-- **One transaction begins, claims and commits.** The run touches no other transaction's phase,
keeps every claim outside its takes, releases its takes, and records its fresh identities as born. -/
theorem Run.single {σ : ProtocolState O R T} {t : T} (idle : σ.phase t = .idle)
    (enabled : Enabled label σ.store (txn t)) (unclaimed : ∀ o ∈ (txn t).taken, σ.claim o = none)
    (unborn : Disjoint (txn t).made σ.born) :
    ∃ σ', Run label txn σ [(t, txn t)] σ' ∧ σ'.store = fire σ.store (txn t) ∧
      σ'.born = σ.born ∪ (txn t).made ∧ (∀ o, o ∉ (txn t).taken → σ'.claim o = σ.claim o) ∧
      (∀ o ∈ (txn t).taken, σ'.claim o = none) ∧ ∀ t', t' ≠ t → σ'.phase t' = σ.phase t' := by
  have active : (Function.update σ.phase t (.active σ.epoch)) t = .active σ.epoch := Function.update_self ..
  obtain ⟨claim, claims, all, outside⟩ := Run.claim_sorted (label := label) (txn := txn) t σ.epoch
    ((txn t).taken.sort) { σ with phase := Function.update σ.phase t (.active σ.epoch) }
    (Finset.pairwise_sort _ _) (Finset.sort_nodup _ _) active
    (fun o member => ⟨(Finset.mem_sort _).mp member, enabled.taken_subset ((Finset.mem_sort _).mp member),
      unclaimed o ((Finset.mem_sort _).mp member)⟩)
    (fun o taken notSorted => absurd ((Finset.mem_sort _).mpr taken) notSorted)
  refine ⟨_, Run.trans (.step (.begin σ t idle enabled) claims)
    (.step (.commit { ({ σ with phase := Function.update σ.phase t (.active σ.epoch) } : ProtocolState O R T) with
        claim := claim } t σ.epoch active all enabled.kept_subset (fun _ _ => rfl) unborn) (.refl _)),
    rfl, rfl, fun o notTaken => ?_, fun o taken => ?_, fun t' different => ?_⟩
  · show (if o ∈ (txn t).taken then none else claim o) = σ.claim o
    rw [if_neg notTaken]
    exact outside o fun inSorted => notTaken ((Finset.mem_sort _).mp inSorted)
  · show (if o ∈ (txn t).taken then none else claim o) = none
    rw [if_pos taken]
  · show Function.update (Function.update σ.phase t (.active σ.epoch)) t .done t' = σ.phase t'
    rw [Function.update_of_ne different, Function.update_of_ne different]

/-- A step never forgets a born identity. -/
theorem Step.born_subset {σ σ' : ProtocolState O R T} {out : Option (T × Commit O R)}
    (step : Step label txn σ out σ') : σ.born ⊆ σ'.born := by
  cases step with
  | begin => exact subset_rfl
  | claim => exact subset_rfl
  | commit => exact Finset.subset_union_left
  | abort => exact subset_rfl

/-- **A transaction that makes a born identity commits in no continuation.** -/
theorem Run.reborn_never_commits {σ σ' : ProtocolState O R T} {trace : List (T × Commit O R)}
    (run : Run label txn σ trace σ') {t : T} :
    ¬ Disjoint (txn t).made σ.born → ∀ entry ∈ trace, entry.1 ≠ t := by
  induction run with
  | refl => intro _ entry member; cases member
  | step first _ ih =>
      intro reborn entry member
      rcases List.mem_append.mp member with here | later
      · cases first with
        | begin => simp at here
        | claim => simp at here
        | abort => simp at here
        | commit t' seen active claimed keptLive epochsFresh unborn =>
            simp only [Option.toList_some, List.mem_singleton] at here
            subst here
            rintro rfl
            exact reborn unborn
      · exact ih (fun disjoint => reborn (disjoint.mono_right first.born_subset)) entry later

namespace Controls

/-- The identity `0` was born and removed; the store holds `1`. -/
def removed : ProtocolState ℕ Unit Unit where
  store := {1}
  born := {0, 1}
  claim := fun _ => none
  epoch := fun _ => 0
  phase := fun _ => .idle

/-- A commit that makes the removed identity `0` again. -/
def remake : Unit → Commit ℕ Unit := fun _ => ⟨∅, ∅, {0}, []⟩

/-- **Its commit is enabled at the store**: `0` is not present. -/
theorem remake_enabled : Enabled (fun _ : ℕ => ()) removed.store (remake ()) := by
  decide

/-- **It commits in no continuation**: `0` was born. -/
theorem remake_never_commits {σ : ProtocolState ℕ Unit Unit} {trace : List (Unit × Commit ℕ Unit)}
    (run : Run (fun _ : ℕ => ()) remake removed trace σ) : trace = [] :=
  List.eq_nil_iff_forall_not_mem.mpr fun entry member =>
    run.reborn_never_commits (t := ()) (by decide) entry member rfl

end Controls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

variable {S : Signature} {O : Type} [LinearOrder O] {Γ : Ctx S} {sort : S.Srt}
  [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] {T : Type*} [DecidableEq T]

/-- **Every native firing is realized by a protocol run.** A transaction whose commit is the
firing's commit, idle at a protocol state whose store holds the state's present occurrences, with
its takes unclaimed and its fresh identities unborn, begins, claims and commits; the protocol's
store is then the present occurrences of the native result. -/
theorem native_protocol_run {s : NativeState S O Γ sort} (f : NativeFiring s) (realized : f.Realized)
    (txn : T → Commit O Unit) (t : T) (transaction : txn t = f.selection.commit (T := Unit))
    (σ : ProtocolState O Unit T) (store : σ.store = s.state.present) (idle : σ.phase t = .idle)
    (unclaimed : ∀ o ∈ (txn t).taken, σ.claim o = none) (unborn : Disjoint (txn t).made σ.born) :
    ∃ σ', Run (fun _ : O => ()) txn σ [(t, txn t)] σ' ∧
      σ'.store = (native.result f realized).state.present := by
  have enabled : Enabled (fun _ : O => ()) σ.store (txn t) := by
    rw [store, transaction]
    exact ((native_admits_iff f).mp realized).2.1
  have active : (Function.update σ.phase t (.active σ.epoch)) t = .active σ.epoch :=
    Function.update_self ..
  obtain ⟨claim, claims, all, -⟩ := Run.claim_sorted (label := fun _ : O => ()) (txn := txn) t σ.epoch
    ((txn t).taken.sort) { σ with phase := Function.update σ.phase t (.active σ.epoch) }
    (Finset.pairwise_sort _ _) (Finset.sort_nodup _ _) active
    (fun o member => ⟨(Finset.mem_sort _).mp member, enabled.taken_subset ((Finset.mem_sort _).mp member),
      unclaimed o ((Finset.mem_sort _).mp member)⟩)
    (fun o taken notSorted => absurd ((Finset.mem_sort _).mpr taken) notSorted)
  have noQueries : ∀ read ∈ (txn t).queries,
      σ.epoch read.region = σ.epoch read.region := fun _ _ => rfl
  refine ⟨_, Run.trans (.step (.begin σ t idle enabled) claims)
    (.step (.commit { σ with phase := Function.update σ.phase t (.active σ.epoch), claim := claim } t σ.epoch
      active all enabled.kept_subset noQueries unborn) (.refl _)), ?_⟩
  show fire σ.store (txn t) = _
  rw [store, transaction]
  exact (native.present_result f realized).symm


/-- **Apart native firings commit concurrently, in either order.** Two distinct idle transactions
whose commits are the commits of two apart admitted native firings, at an initial protocol state whose
store holds the state's present occurrences and whose born identities miss their fresh ones, both
begin and claim, and then commit in either order; both orders end at the composite physical result. -/
theorem native_protocol_concurrent {s : NativeState S O Γ sort} {f g : NativeFiring s}
    (apart : f.Apart g) (first : f.Realized) (second : g.Realized) (txn : T → Commit O Unit) {t t' : T}
    (different : t ≠ t') (txnF : txn t = f.selection.commit (T := Unit))
    (txnG : txn t' = g.selection.commit (T := Unit)) (σ : ProtocolState O Unit T) (initial : Initial σ)
    (store : σ.store = s.state.present) (unbornF : Disjoint (txn t).made σ.born)
    (unbornG : Disjoint (txn t').made σ.born) :
    (∃ σ', Run (fun _ : O => ()) txn σ [(t, txn t), (t', txn t')] σ' ∧
      σ'.store = fire (fire s.state.present (f.selection.commit (T := Unit))) (g.selection.commit (T := Unit))) ∧
    ∃ σ', Run (fun _ : O => ()) txn σ [(t', txn t'), (t, txn t)] σ' ∧
      σ'.store = fire (fire s.state.present (f.selection.commit (T := Unit))) (g.selection.commit (T := Unit)) := by
  have enabledF : Enabled (fun _ : O => ()) σ.store (txn t) := by
    rw [store, txnF]
    exact ((native_admits_iff f).mp first).2.1
  have enabledG : Enabled (fun _ : O => ()) σ.store (txn t') := by
    rw [store, txnG]
    exact ((native_admits_iff g).mp second).2.1
  have independent : Independent (fun _ : O => ()) (txn t) (txn t') := by
    rw [txnF, txnG]
    exact apart.commits_independent
  have disjointTakes : Disjoint (txn t).taken (txn t').taken := by
    by_contra common
    exact independent.1 (Or.inl common)
  have wf : WellFormed (fun _ : O => ()) txn σ := wellFormed_of_initial initial
  obtain ⟨_, unclaimed, idle⟩ := initial
  have idleT' : (Function.update σ.phase t (.active σ.epoch)) t' = .idle := by
    rw [Function.update_of_ne (Ne.symm different), idle]
  have activeT : (Function.update (Function.update σ.phase t (.active σ.epoch)) t' (.active σ.epoch)) t =
      .active σ.epoch := by
    rw [Function.update_of_ne different, Function.update_self]
  have activeT' : (Function.update (Function.update σ.phase t (.active σ.epoch)) t' (.active σ.epoch)) t' =
      .active σ.epoch :=
    Function.update_self ..
  have begun : Run (fun _ : O => ()) txn σ []
      { σ with phase := Function.update (Function.update σ.phase t (.active σ.epoch)) t' (.active σ.epoch) } :=
    .step (.begin σ t (idle t) enabledF)
      (.step (.begin { σ with phase := Function.update σ.phase t (.active σ.epoch) } t' idleT' enabledG) (.refl _))
  obtain ⟨claimT, claimsT, allT, outsideT⟩ := Run.claim_sorted (label := fun _ : O => ()) (txn := txn) t σ.epoch
    ((txn t).taken.sort)
    { σ with phase := Function.update (Function.update σ.phase t (.active σ.epoch)) t' (.active σ.epoch) }
    (Finset.pairwise_sort _ _) (Finset.sort_nodup _ _) activeT
    (fun o member => ⟨(Finset.mem_sort _).mp member, enabledF.taken_subset ((Finset.mem_sort _).mp member),
      unclaimed o⟩)
    (fun o taken notSorted => absurd ((Finset.mem_sort _).mpr taken) notSorted)
  obtain ⟨claimBoth, claimsT', allT', outsideT'⟩ := Run.claim_sorted (label := fun _ : O => ()) (txn := txn) t'
    σ.epoch ((txn t').taken.sort)
    { ({ σ with phase := Function.update (Function.update σ.phase t (.active σ.epoch)) t' (.active σ.epoch) } : ProtocolState O Unit T) with
      claim := claimT }
    (Finset.pairwise_sort _ _) (Finset.sort_nodup _ _) activeT'
    (fun o member => by
      have taken' := (Finset.mem_sort _).mp member
      have notT : o ∉ (txn t).taken.sort := fun inT =>
        Finset.disjoint_left.mp disjointTakes ((Finset.mem_sort _).mp inT) taken'
      exact ⟨taken', enabledG.taken_subset taken', (outsideT o notT).trans (unclaimed o)⟩)
    (fun o taken notSorted => absurd ((Finset.mem_sort _).mpr taken) notSorted)
  have readyT : Ready (txn := txn)
      { ({ σ with phase := Function.update (Function.update σ.phase t (.active σ.epoch)) t' (.active σ.epoch) } : ProtocolState O Unit T) with
        claim := claimBoth } t :=
    ⟨σ.epoch, activeT, fun o taken => by
        have notT' : o ∉ (txn t').taken.sort := fun inT' =>
          Finset.disjoint_left.mp disjointTakes taken ((Finset.mem_sort _).mp inT')
        exact (outsideT' o notT').trans (allT o taken),
      enabledF.kept_subset, fun _ _ => rfl, unbornF⟩
  have readyT' : Ready (txn := txn)
      { ({ σ with phase := Function.update (Function.update σ.phase t (.active σ.epoch)) t' (.active σ.epoch) } : ProtocolState O Unit T) with
        claim := claimBoth } t' :=
    ⟨σ.epoch, activeT', allT', enabledG.kept_subset, fun _ _ => rfl, unbornG⟩
  have readyEither : ∀ x, x = t ∨ x = t' → Ready (txn := txn)
      { ({ σ with phase := Function.update (Function.update σ.phase t (.active σ.epoch)) t' (.active σ.epoch) } : ProtocolState O Unit T) with
        claim := claimBoth } x := by
    rintro x (rfl | rfl)
    · exact readyT
    · exact readyT'
  obtain ⟨final, commits⟩ := Run.commit_all (label := fun _ : O => ()) [t, t'] _ (by simp [different])
    (fun x member => readyEither x (by simpa using member))
    (List.pairwise_pair.mpr ⟨independent.1, independent.2.1⟩)
  obtain ⟨final', commits'⟩ := Run.commit_all (label := fun _ : O => ()) [t', t] _ (by simp [Ne.symm different])
    (fun x member => readyEither x (by simpa [or_comm] using member))
    (List.pairwise_pair.mpr ⟨fun clash => independent.1 clash.symm, independent.2.2⟩)
  have run : Run (fun _ : O => ()) txn σ [(t, txn t), (t', txn t')] final :=
    Run.trans begun (Run.trans claimsT (Run.trans claimsT' commits))
  have run' : Run (fun _ : O => ()) txn σ [(t', txn t'), (t, txn t)] final' :=
    Run.trans begun (Run.trans claimsT (Run.trans claimsT' commits'))
  have enabledF' := ((native_admits_iff f).mp first).2.1
  have enabledG' := ((native_admits_iff g).mp second).2.1
  refine ⟨⟨final, run, ?_⟩, final', run', ?_⟩
  · rw [(run.refines wf).2.1]
    show fire (fire σ.store (txn t)) (txn t') = _
    rw [store, txnF, txnG]
  · rw [(run'.refines wf).2.1]
    show fire (fire σ.store (txn t')) (txn t) = _
    rw [store, txnF, txnG]
    exact (fire_comm enabledF' enabledG').symm


namespace NativeRun

/-- The commits of a native run as a protocol trace, transaction `k` onward. -/
noncomputable def trace (txn : ℕ → Commit O Unit) :
    {s : NativeState S O Γ sort} → Interface.Step.Run (native (S := S) (O := O) (Γ := Γ) (sort := sort)).toStep s →
      ℕ → List (ℕ × Commit O Unit)
  | _, .nil _, _ => []
  | _, .cons _ _ rest, k => (k, txn k) :: trace txn rest (k + 1)

/-- Transactions from `k` on carry the commits of the run's firings, in order. -/
def Carries (txn : ℕ → Commit O Unit) :
    {s : NativeState S O Γ sort} → Interface.Step.Run (native (S := S) (O := O) (Γ := Γ) (sort := sort)).toStep s →
      ℕ → Prop
  | _, .nil _, _ => True
  | _, .cons f _ rest, k => txn k = f.selection.commit (T := Unit) ∧ Carries txn rest (k + 1)

/-- **The run allocates fresh identities**: no firing makes an identity already born, nor one an
earlier firing made. -/
def FreshFrom :
    {s : NativeState S O Γ sort} → Interface.Step.Run (native (S := S) (O := O) (Γ := Γ) (sort := sort)).toStep s →
      Finset O → Prop
  | _, .nil _, _ => True
  | _, .cons f _ rest, born =>
      Disjoint f.selection.made.toFinset born ∧ FreshFrom rest (born ∪ f.selection.made.toFinset)

end NativeRun

/-- **Every native run that allocates fresh identities is realized by a protocol run**: transaction
`k + i` carries the `i`-th firing's commit; each begins, claims and commits in turn, and the
protocol's store ends at the present occurrences of the run's last state. -/
theorem native_run_protocol (txn : ℕ → Commit O Unit) :
    ∀ {s : NativeState S O Γ sort} (r : Interface.Step.Run (native (S := S) (O := O) (Γ := Γ) (sort := sort)).toStep s)
      (k : ℕ) (σ : ProtocolState O Unit ℕ), NativeRun.Carries txn r k → NativeRun.FreshFrom r σ.born →
      σ.store = s.state.present → (∀ i, k ≤ i → σ.phase i = .idle) → (∀ o, σ.claim o = none) →
      ∃ σ', Run (fun _ : O => ()) txn σ (NativeRun.trace txn r k) σ' ∧ σ'.store = r.last.state.present
  | _, .nil _, _, σ, _, _, store, _, _ => ⟨σ, .refl σ, store⟩
  | _, .cons f admitted rest, k, σ, carries, freshness, store, idle, unclaimed => by
      obtain ⟨carried, carriesRest⟩ := carries
      obtain ⟨fresh, freshRest⟩ := freshness
      have enabled : Enabled (fun _ : O => ()) σ.store (txn k) := by
        rw [store, carried]
        exact ((native_admits_iff f).mp admitted).2.1
      obtain ⟨σ₁, run₁, store₁, born₁, outside₁, inside₁, phase₁⟩ := Run.single (label := fun _ : O => ())
        (idle k le_rfl) enabled (fun o _ => unclaimed o) (by rw [carried]; exact fresh)
      obtain ⟨σ₂, run₂, store₂⟩ := native_run_protocol txn rest (k + 1) σ₁ carriesRest
        (by rw [born₁, carried]; exact freshRest)
        (by rw [store₁, store, carried]; exact (native.present_result f admitted).symm)
        (fun i later => by rw [phase₁ i (by omega)]; exact idle i (by omega))
        (fun o => by
          by_cases taken : o ∈ (txn k).taken
          · exact inside₁ o taken
          · rw [outside₁ o taken]
            exact unclaimed o)
      exact ⟨σ₂, Run.trans run₁ run₂, store₂⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits in
#print axioms Run.trans
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits in
#print axioms Run.claim_sorted
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits in
#print axioms Run.single
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits in
#print axioms Run.reborn_never_commits
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits in
#print axioms Controls.remake_enabled
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits in
#print axioms Controls.remake_never_commits
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface in
#print axioms native_protocol_run
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface in
#print axioms native_protocol_concurrent
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface in
#print axioms native_run_protocol
