import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeConcurrent
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeProtocol

/-!
# The protocol wave realizes the native concurrent step

R83's `live_protocol_diamond` is the two-firing case: two clear live firings commit concurrently in
either order and end with the store both native orders publish. This module is the case of any
number of firings.

## The protocol side

* **Every idle transaction of a batch begins** (`Run.begin_all`), with no commit, each at the epochs
  of the start.
* **Every active transaction of a batch with disjoint takes claims its takes** (`Run.claim_all`),
  each in canonical order, with no commit.
* **A wave of pairwise independent enabled commits commits in every order** (`protocol_wave`): the
  batch begins, claims, and then commits in any order, and every order ends with one store, the wave
  formula. This is the protocol's wave commit (`Run.wave`) for a wave with no precedence at all,
  where every order is a ranking.

## The bridge

**The protocol wave realizes the native concurrent step** (`live_protocol_wave`): the transactions of
a clear family of live firings, carried by distinct idle transactions of an initial protocol state
that holds the state's present occurrences and has not born their fresh identities, commit in every
order, and every order ends with the store the native concurrent step publishes. Its present
occurrences are those of every sequentialization (`DeadEquiv.present_eq`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe u v w

variable {O : Type u} [LinearOrder O] {R : Type v} {T : Type w} [DecidableEq T]
  {label : O → R} {txn : T → Commit O R}

/-- **Every idle transaction of a batch begins**, each at the epochs of the start, with no commit. -/
theorem Run.begin_all : ∀ (W : List T) (σ : ProtocolState O R T), W.Nodup → (∀ t ∈ W, σ.phase t = .idle) →
    (∀ t ∈ W, Enabled label σ.store (txn t)) →
    ∃ phase : T → Phase R, Run label txn σ [] { σ with phase := phase } ∧
      (∀ t ∈ W, phase t = .active σ.epoch) ∧ ∀ t, t ∉ W → phase t = σ.phase t
  | [], σ, _, _, _ => ⟨σ.phase, .refl σ, fun _ member => absurd member List.not_mem_nil, fun _ _ => rfl⟩
  | t :: rest, σ, nodup, idle, enabled => by
      have fresh : t ∉ rest := (List.nodup_cons.mp nodup).1
      obtain ⟨phase, run, active, outside⟩ := Run.begin_all rest
        { σ with phase := Function.update σ.phase t (.active σ.epoch) } (List.nodup_cons.mp nodup).2
        (fun t' inRest => by
          have different : t' ≠ t := fun same => fresh (same ▸ inRest)
          show Function.update σ.phase t (.active σ.epoch) t' = .idle
          rw [Function.update_of_ne different]
          exact idle t' (List.mem_cons_of_mem _ inRest))
        (fun t' inRest => enabled t' (List.mem_cons_of_mem _ inRest))
      refine ⟨phase, .step (.begin σ t (idle t List.mem_cons_self) (enabled t List.mem_cons_self)) run, ?_, ?_⟩
      · intro t' member
        rcases List.mem_cons.mp member with same | inRest
        · rw [same, outside t fresh]
          exact Function.update_self ..
        · exact active t' inRest
      · intro t' notMember
        have different : t' ≠ t := fun same => notMember (same ▸ List.mem_cons_self)
        rw [outside t' fun inRest => notMember (List.mem_cons_of_mem _ inRest)]
        exact Function.update_of_ne different _ _

/-- **Every active transaction of a batch with disjoint takes claims its takes**, each in canonical
order, with no commit. -/
theorem Run.claim_all (seen : (R → Bool) → ℕ) : ∀ (W : List T) (σ : ProtocolState O R T), W.Nodup →
    (∀ t ∈ W, σ.phase t = .active seen) → W.Pairwise (fun a b => Disjoint (txn a).taken (txn b).taken) →
    (∀ t ∈ W, ∀ o ∈ (txn t).taken, o ∈ σ.store ∧ σ.claim o = none) →
    ∃ claim : O → Option T, Run label txn σ [] { σ with claim := claim } ∧
      (∀ t ∈ W, ∀ o ∈ (txn t).taken, claim o = some t) ∧
      ∀ o, (∀ t ∈ W, o ∉ (txn t).taken) → claim o = σ.claim o
  | [], σ, _, _, _, _ => ⟨σ.claim, .refl σ, fun _ member => absurd member List.not_mem_nil, fun _ _ => rfl⟩
  | t :: rest, σ, nodup, active, disjoint, free => by
      obtain ⟨claim₁, claims₁, all₁, outside₁⟩ := Run.claim_sorted (label := label) (txn := txn) t seen
        ((txn t).taken.sort) σ (Finset.pairwise_sort _ _) (Finset.sort_nodup _ _) (active t List.mem_cons_self)
        (fun o member => ⟨(Finset.mem_sort _).mp member,
          (free t List.mem_cons_self o ((Finset.mem_sort _).mp member)).1,
          (free t List.mem_cons_self o ((Finset.mem_sort _).mp member)).2⟩)
        (fun o taken notSorted => absurd ((Finset.mem_sort _).mpr taken) notSorted)
      have apart : ∀ t' ∈ rest, Disjoint (txn t).taken (txn t').taken := (List.pairwise_cons.mp disjoint).1
      obtain ⟨claim, claims, all, outside⟩ := Run.claim_all seen rest { σ with claim := claim₁ }
        (List.nodup_cons.mp nodup).2 (fun t' inRest => active t' (List.mem_cons_of_mem _ inRest))
        (List.pairwise_cons.mp disjoint).2
        (fun t' inRest o taken => by
          have notT : o ∉ (txn t).taken := fun takenT => Finset.disjoint_left.mp (apart t' inRest) takenT taken
          refine ⟨(free t' (List.mem_cons_of_mem _ inRest) o taken).1, ?_⟩
          show claim₁ o = none
          rw [outside₁ o fun inSorted => notT ((Finset.mem_sort _).mp inSorted)]
          exact (free t' (List.mem_cons_of_mem _ inRest) o taken).2)
      refine ⟨claim, Run.trans claims₁ claims, ?_, ?_⟩
      · intro t' member o taken
        rcases List.mem_cons.mp member with same | inRest
        · rw [same] at taken ⊢
          rw [outside o fun t'' inRest' taken'' => Finset.disjoint_left.mp (apart t'' inRest') taken taken'']
          exact all₁ o taken
        · exact all t' inRest o taken
      · intro o notTaken
        rw [outside o fun t' inRest => notTaken t' (List.mem_cons_of_mem _ inRest)]
        exact outside₁ o fun inSorted => notTaken t List.mem_cons_self ((Finset.mem_sort _).mp inSorted)

theorem Independent.symm' {c d : Commit O R} (independent : Independent label c d) : Independent label d c :=
  ⟨fun clash => independent.1 clash.symm, independent.2.2, independent.2.1⟩

/-- **A wave of pairwise independent enabled commits commits in every order.** The batch, idle at an
initial state with fresh identities unborn, begins, claims, and then commits in any order, and every
order ends with the wave formula's store. -/
theorem protocol_wave {W : List T} (nodup : W.Nodup) (σ : ProtocolState O R T) (initial : Initial σ)
    (enabled : ∀ t ∈ W, Enabled label σ.store (txn t))
    (independent : W.Pairwise fun a b => Independent label (txn a) (txn b))
    (unborn : ∀ t ∈ W, Disjoint (txn t).made σ.born) {order : List T} (perm : order.Perm W) :
    ∃ σ', Run label txn σ (order.map fun t => (t, txn t)) σ' ∧ σ'.store = fireList σ.store (W.map txn) := by
  have wf : WellFormed label txn σ := wellFormed_of_initial initial
  obtain ⟨_, unclaimed, idle⟩ := initial
  obtain ⟨phase, begun, active, _⟩ := Run.begin_all (label := label) (txn := txn) W σ nodup (fun t _ => idle t) enabled
  have disjointTakes : W.Pairwise fun a b => Disjoint (txn a).taken (txn b).taken :=
    independent.imp fun {a b} indep => by
      by_contra common
      exact indep.1 (Or.inl common)
  obtain ⟨claim, claims, all, _⟩ := Run.claim_all (label := label) (txn := txn) σ.epoch W { σ with phase := phase }
    nodup active disjointTakes (fun t inW o taken => ⟨(enabled t inW).taken_subset taken, unclaimed o⟩)
  have independentOrder : order.Pairwise fun a b => Independent label (txn a) (txn b) :=
    (perm.pairwise_iff fun {_ _} indep => Independent.symm' indep).mpr independent
  obtain ⟨σ', commits⟩ := Run.commit_all (label := label) (txn := txn) order
    { ({ σ with phase := phase } : ProtocolState O R T) with claim := claim } (perm.nodup_iff.mpr nodup)
    (fun t member => ⟨σ.epoch, active t (perm.subset member), all t (perm.subset member),
      (enabled t (perm.subset member)).kept_subset, fun _ _ => rfl, unborn t (perm.subset member)⟩)
    (independentOrder.imp fun {_ _} indep => ⟨indep.1, indep.2.1⟩)
  have run := Run.trans begun (Run.trans claims commits)
  rw [List.nil_append, List.nil_append] at run
  have matched : MatchedAt σ.store (order.map txn) := by
    intro c member
    obtain ⟨t, inOrder, rfl⟩ := List.mem_map.mp member
    exact ⟨(enabled t (perm.subset inOrder)).taken_subset, (enabled t (perm.subset inOrder)).fresh⟩
  refine ⟨σ', run, (run.refines wf).2.1.trans ?_⟩
  rw [List.map_map]
  exact fireList_perm matched (perm.map txn)

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open NativeIterated NativeDead NativeConcurrent

variable {S : Signature} {O : Type} [LinearOrder O] {Γ : Ctx S} {sort : S.Srt}
  [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] {T : Type*} [DecidableEq T]

omit [LinearOrder O] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
/-- States that agree up to dead names have the same present occurrences. -/
theorem NativeDead.DeadEquiv.present_eq {s t : NativeState S O Γ sort} (same : DeadEquiv s t) :
    s.state.present = t.state.present := by
  obtain ⟨u, ⟨first⟩, ⟨second⟩⟩ := same
  exact first.present.symm.trans second.present

/-- **The protocol wave realizes the native concurrent step.** The transactions of a clear family of
live firings, carried by distinct idle transactions of an initial protocol state that holds the
state's present occurrences and has not born their fresh identities, commit in every order, and every
order ends with the store the native concurrent step publishes. -/
theorem live_protocol_wave {s : NativeState S O Γ sort} {fs : List (LiveFiring s)} (clear : FamilyClear s fs)
    (txn : T → Commit O Unit) {W : List T} (nodup : W.Nodup)
    (carries : W.map txn = fs.map fun f => f.selection.commit (T := Unit))
    (σ : ProtocolState O Unit T) (initial : Initial σ) (store : σ.store = s.state.present)
    (unborn : ∀ t ∈ W, Disjoint (txn t).made σ.born) {t₀ : NativeState S O Γ sort}
    (step : Concurrent s (fs : Multiset (LiveFiring s)) t₀) {order : List T} (perm : order.Perm W) :
    ∃ σ', Run (fun _ : O => ()) txn σ (order.map fun t => (t, txn t)) σ' ∧ σ'.store = t₀.state.present := by
  have enabledOf : ∀ f ∈ fs, Enabled (fun _ : O => ()) s.state.present (f.selection.commit (T := Unit)) :=
    fun f member => ((native_admits_iff f.toNative).mp (clear.admitted f member)).2.1
  have enabled : ∀ t ∈ W, Enabled (fun _ : O => ()) σ.store (txn t) := by
    intro t member
    have inMap : txn t ∈ fs.map fun f => f.selection.commit (T := Unit) := carries ▸ List.mem_map_of_mem member
    obtain ⟨f, inFs, same⟩ := List.mem_map.mp inMap
    rw [store, ← same]
    exact enabledOf f inFs
  have independent : W.Pairwise fun a b => Independent (fun _ : O => ()) (txn a) (txn b) := by
    apply List.pairwise_map.mp
    rw [carries]
    exact List.pairwise_map.mpr (clear.pairwise.imp fun {_ _} clears => Clear.commits_independent clears.1 clears.2)
  obtain ⟨σ', run, final⟩ := protocol_wave nodup σ initial enabled independent unborn perm
  have matched : MatchedAt s.state.present (fs.map fun f => f.selection.commit (T := Unit)) := by
    intro c member
    obtain ⟨f, inFs, rfl⟩ := List.mem_map.mp member
    exact ⟨(enabledOf f inFs).taken_subset, (enabledOf f inFs).fresh⟩
  refine ⟨σ', run, final.trans ?_⟩
  rw [carries, store, step.present, fireList_eq_fire_effectOf matched]

/-- **Every order of the wave ends with the present occurrences of every native sequentialization.** -/
theorem live_protocol_wave_orders {s : NativeState S O Γ sort} {fs : List (LiveFiring s)} (clear : FamilyClear s fs)
    (txn : T → Commit O Unit) {W : List T} (nodup : W.Nodup)
    (carries : W.map txn = fs.map fun f => f.selection.commit (T := Unit))
    (σ : ProtocolState O Unit T) (initial : Initial σ) (store : σ.store = s.state.present)
    (unborn : ∀ t ∈ W, Disjoint (txn t).made σ.born) {order : List T} (perm : order.Perm W)
    {firings : List (LiveFiring s)} (firingsPerm : firings.Perm fs) :
    ∃ σ' t, Run (fun _ : O => ()) txn σ (order.map fun t => (t, txn t)) σ' ∧ Sequential s firings t ∧
      σ'.store = t.state.present := by
  obtain ⟨t₀, step⟩ := concurrent_of_clear clear
  obtain ⟨σ', run, final⟩ := live_protocol_wave clear txn nodup carries σ initial store unborn step perm
  obtain ⟨t, sequential, agree⟩ := step.agrees (Multiset.coe_eq_coe.mpr firingsPerm)
  exact ⟨σ', t, run, sequential, final.trans agree.present_eq⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

#print axioms Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Run.begin_all
#print axioms Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Run.claim_all
#print axioms Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.protocol_wave
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.NativeDead.DeadEquiv.present_eq
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.live_protocol_wave
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.live_protocol_wave_orders
