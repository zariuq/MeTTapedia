import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeFreshness

/-!
# The commit protocol and the native diamond

The commit protocol is the runtime's view of firing (`OccurrenceCommits.CommitProtocol`). For two live
firings that leave each other clear (`Clear`), this module relates the protocol's concurrent commit to
the native diamond.

* **Clear firings commit independently** (`Clear.commits_independent`): no clash, and neither takes
  what the other reads.
* **Independent enabled commits commit concurrently, in either order** (`protocol_concurrent`): two
  idle transactions begin and claim, then commit in either order, and both orders end at the composite
  physical result. This is R81's `native_protocol_concurrent` for any pair of independent commits, with
  no hypothesis on guards or queries.
* **The protocol realizes the native diamond** (`live_protocol_diamond`): for two live firings that
  leave each other clear and make unborn identities, both protocol orders end with the store the two
  native orders publish, and the two native composite states are the one joint state carried
  (`LiveFiring.closing`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

variable {S : Signature} {O : Type} [LinearOrder O] {Γ : Ctx S} {sort : S.Srt}
  [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] {T : Type*} [DecidableEq T]

/-- **Independent enabled commits commit concurrently, in either order.** Two distinct idle
transactions whose commits are enabled and independent at the store of an initial protocol state, with
fresh identities unborn, begin and claim, and then commit in either order; both orders end at the
composite physical result. -/
theorem protocol_concurrent (txn : T → Commit O Unit) {t t' : T} (different : t ≠ t')
    (σ : ProtocolState O Unit T) (initial : Initial σ)
    (enabledF : Enabled (fun _ : O => ()) σ.store (txn t)) (enabledG : Enabled (fun _ : O => ()) σ.store (txn t'))
    (independent : Independent (fun _ : O => ()) (txn t) (txn t'))
    (unbornF : Disjoint (txn t).made σ.born) (unbornG : Disjoint (txn t').made σ.born) :
    (∃ σ', Run (fun _ : O => ()) txn σ [(t, txn t), (t', txn t')] σ' ∧ σ'.store = fire (fire σ.store (txn t)) (txn t')) ∧
      ∃ σ', Run (fun _ : O => ()) txn σ [(t', txn t'), (t, txn t)] σ' ∧ σ'.store = fire (fire σ.store (txn t)) (txn t') := by
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
    { ({ σ with phase := Function.update (Function.update σ.phase t (.active σ.epoch)) t' (.active σ.epoch) } :
        ProtocolState O Unit T) with claim := claimT }
    (Finset.pairwise_sort _ _) (Finset.sort_nodup _ _) activeT'
    (fun o member => by
      have taken' := (Finset.mem_sort _).mp member
      have notT : o ∉ (txn t).taken.sort := fun inT =>
        Finset.disjoint_left.mp disjointTakes ((Finset.mem_sort _).mp inT) taken'
      exact ⟨taken', enabledG.taken_subset taken', (outsideT o notT).trans (unclaimed o)⟩)
    (fun o taken notSorted => absurd ((Finset.mem_sort _).mpr taken) notSorted)
  have readyT : Ready (txn := txn)
      { ({ σ with phase := Function.update (Function.update σ.phase t (.active σ.epoch)) t' (.active σ.epoch) } :
          ProtocolState O Unit T) with claim := claimBoth } t :=
    ⟨σ.epoch, activeT, fun o taken => by
        have notT' : o ∉ (txn t').taken.sort := fun inT' =>
          Finset.disjoint_left.mp disjointTakes taken ((Finset.mem_sort _).mp inT')
        exact (outsideT' o notT').trans (allT o taken),
      enabledF.kept_subset, fun _ _ => rfl, unbornF⟩
  have readyT' : Ready (txn := txn)
      { ({ σ with phase := Function.update (Function.update σ.phase t (.active σ.epoch)) t' (.active σ.epoch) } :
          ProtocolState O Unit T) with claim := claimBoth } t' :=
    ⟨σ.epoch, activeT', allT', enabledG.kept_subset, fun _ _ => rfl, unbornG⟩
  have readyEither : ∀ x, x = t ∨ x = t' → Ready (txn := txn)
      { ({ σ with phase := Function.update (Function.update σ.phase t (.active σ.epoch)) t' (.active σ.epoch) } :
          ProtocolState O Unit T) with claim := claimBoth } x := by
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
  refine ⟨⟨final, run, (run.refines wf).2.1⟩, final', run', ?_⟩
  rw [(run'.refines wf).2.1]
  exact (fire_comm enabledF enabledG).symm

namespace Clear

variable {s : NativeState S O Γ sort} {f g : LiveFiring s}

omit [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
/-- **Live firings that leave each other clear commit independently.** -/
theorem commits_independent (clearF : Clear f g.selection g.rule g.outputs)
    (clearG : Clear g f.selection f.rule f.outputs) :
    Independent (fun _ : O => ()) (f.selection.commit (T := Unit)) (g.selection.commit (T := Unit)) := by
  refine ⟨fun clash => clash.elim (fun common => common clearF.takes) (fun common => common clearF.ports), ?_, ?_⟩
  · rintro (common | ⟨read, member, _⟩)
    · exact common clearG.keeps
    · simp [Selection.commit] at member
  · rintro (common | ⟨read, member, _⟩)
    · exact common clearF.keeps
    · simp [Selection.commit] at member

end Clear

/-- **The protocol realizes the native diamond.** Two live firings that leave each other clear, carried
by two distinct idle transactions of an initial protocol state that holds the present occurrences and
has not born their fresh identities, commit in either order; both orders end with the store that both
native orders publish. -/
theorem live_protocol_diamond {s : NativeState S O Γ sort} {f g : LiveFiring s}
    (first : f.toNative.Realized) (second : g.toNative.Realized)
    (clearF : Clear f g.selection g.rule g.outputs) (clearG : Clear g f.selection f.rule f.outputs)
    (txn : T → Commit O Unit) {t t' : T} (different : t ≠ t') (txnF : txn t = f.selection.commit (T := Unit))
    (txnG : txn t' = g.selection.commit (T := Unit)) (σ : ProtocolState O Unit T) (initial : Initial σ)
    (store : σ.store = s.state.present) (unbornF : Disjoint (txn t).made σ.born)
    (unbornG : Disjoint (txn t').made σ.born) :
    (∃ σ', Run (fun _ : O => ()) txn σ [(t, txn t), (t', txn t')] σ' ∧
        σ'.store = (native.result (LiveFiring.residual second f) (LiveFiring.after first second clearF)).state.present) ∧
      ∃ σ', Run (fun _ : O => ()) txn σ [(t', txn t'), (t, txn t)] σ' ∧
        σ'.store = (native.result (LiveFiring.residual first g) (LiveFiring.after second first clearG)).state.present := by
  have enabledF : Enabled (fun _ : O => ()) σ.store (txn t) := by
    rw [store, txnF]
    exact ((native_admits_iff f.toNative).mp first).2.1
  have enabledG : Enabled (fun _ : O => ()) σ.store (txn t') := by
    rw [store, txnG]
    exact ((native_admits_iff g.toNative).mp second).2.1
  have independent : Independent (fun _ : O => ()) (txn t) (txn t') := by
    rw [txnF, txnG]
    exact Clear.commits_independent clearF clearG
  obtain ⟨⟨final, run, finalStore⟩, final', run', finalStore'⟩ :=
    protocol_concurrent txn different σ initial enabledF enabledG independent unbornF unbornG
  have present := (LiveFiring.closing first second clearF clearG).1
  have physical : (native.result (LiveFiring.residual second f) (LiveFiring.after first second clearF)).state.present =
      fire (fire s.state.present (f.selection.commit (T := Unit))) (g.selection.commit (T := Unit)) := by
    show (LiveFiring.residualExecution first second clearF).target.present = _
    rw [NativeClosing.present_second (LiveFiring.residualExecution_executes first second clearF),
      (LiveFiring.execution_data second).2.1]
    exact fire_comm ((native_admits_iff g.toNative).mp second).2.1 ((native_admits_iff f.toNative).mp first).2.1
  refine ⟨⟨final, run, ?_⟩, final', run', ?_⟩
  · rw [finalStore, store, txnF, txnG]
    exact physical.symm
  · rw [finalStore', store, txnF, txnG]
    exact physical.symm.trans present

#print axioms protocol_concurrent
#print axioms Clear.commits_independent
#print axioms live_protocol_diamond

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
