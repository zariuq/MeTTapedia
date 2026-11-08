import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Canonical
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CellsFirstOrder
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EscapeFirstOrder

/-!
# Canonical interleavings of the one-frame instance

* **Every key on firings obeys the key laws** (`firstOrderKeyLaws`): the one-frame transport moves and
  carries nothing. So canonical interleavings are complete for every key and every sound oracle
  (`firstOrder_exists_canonical`), in particular for the exact oracle, independence itself, which the
  static fibre decides (`decidableIndependent`).
* **A nonempty run is an executable word** (`executable_of_run`).

## Controls (`CanonicalControls`)

* **Joint consistency** (`hollow_cube_never_round`): the tells `X = Y`, `X = 1` and `Y = 2` are
  independent in pairs at the empty configuration, and no run fires all three, in any order. Canonical
  exploration reorders runs and never assembles a round from pairwise independence.
* **Three independent firings explored once instead of six times** (`clique_explored_once`): three
  producers of fresh occurrences run in each of the six orders, every adjacent pair independent, and a
  run of them is canonical exactly when its key word is the sorted one. Producers of distinct fresh
  occurrences run in every order (`producers_run`) with every adjacent pair independent
  (`producers_adjacent`), for any number of them.
* **A dependent pair is kept** (`dependent_pair_kept`): the watcher queries a region the writer writes
  into. The writer has the smaller key, so sorting would put it first; the pair is not independent, the
  order watcher then writer is canonical for every sound oracle, and the sorted order does not run.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

open Interface (Frames Transport)
open Interface.Transport (KeyLaws keyWord Canonical AdjacentIndependent)
open GuardFreeProcessOrders (SameUpTo)

universe uT uS uO uK

section Laws

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
  (A : SubstitutionAction T S) (label : O → T)

/-- **Every key on firings obeys the key laws of the one-frame transport.** -/
theorem firstOrderKeyLaws {κ : Type uK} (key : Firing T S O → κ) :
    KeyLaws (firstOrderTransport A label) fun _ f => key f :=
  ⟨fun _ _ => rfl, fun same => congrArg key same, fun _ _ _ => rfl⟩

/-- **Canonical interleavings of the one-frame instance are complete**, for every key and every sound
oracle. -/
theorem firstOrder_exists_canonical {κ : Type uK} [LinearOrder κ] (key : Firing T S O → κ)
    {indep : (C : Configuration T O) → Firing T S O → Firing T S O → Prop}
    (sound : ∀ C f g, indep C f g → (firstOrderTransport A label).Independent C f g)
    {C : Configuration T O} (r : (firstOrder A label).Run C) :
    ∃ r' : (firstOrder A label).Run C, (firstOrderTransport A label).TraceEquiv C r r' ∧
      Canonical (firstOrderTransport A label) (fun _ f => key f) indep r' ∧
      (keyWord (fun _ f => key f) r').Perm (keyWord (fun _ f => key f) r) ∧
      SameUpTo A r.last r'.last := by
  obtain ⟨r', equivalent, canonical, perm⟩ :=
    Transport.exists_canonical sound (firstOrderKeyLaws A label key) r
  exact ⟨r', equivalent, canonical, perm,
    Nonempty.elim (Transport.TraceEquiv.same_last equivalent) fun i => i.down⟩

/-- **A nonempty run is an executable word.** -/
theorem executable_of_run : ∀ {C : Configuration T O} (r : (firstOrder A label).Run C),
    r.word ≠ [] → Executable A label C (r.word.map Sigma.snd)
  | _, .nil _, nonempty => absurd rfl nonempty
  | _, .cons _ admitted rest, _ => by
      by_cases none : rest.word = []
      · cases rest with
        | nil => exact ⟨admitted, admitted.firing.consistent⟩
        | cons => simp [Interface.Step.Run.word] at none
      · exact ⟨admitted, executable_of_run rest none⟩

end Laws

/-! ## Controls -/

namespace CanonicalControls

open Mettapedia.Logic.LP
open ConstraintMultisetRewriting.Controls (signature A)

/-! ### Joint consistency: the hollow cube -/

section HollowCube

open AnnotatedRuns.Controls (label)
open RoundControls (tellSame tellOne tellTwo empty)

/-- **Joint consistency**: the three tells are independent in pairs, and no run fires all three. -/
theorem hollow_cube_never_round :
    ((firstOrderTransport A label).Independent empty tellSame tellOne ∧
        (firstOrderTransport A label).Independent empty tellSame tellTwo ∧
        (firstOrderTransport A label).Independent empty tellOne tellTwo) ∧
      ∀ r : (firstOrder A label).Run empty, ¬ (r.word.map Sigma.snd).Perm [tellSame, tellOne, tellTwo] := by
  refine ⟨⟨CellControls.same_one, CellControls.same_two, CellControls.one_two⟩, fun r perm => ?_⟩
  have nonempty : r.word ≠ [] := by
    intro nil
    have lengths := perm.length_eq
    rw [nil] at lengths
    simp at lengths
  exact RoundControls.pairwise_consistent_not_joint _ perm (executable_of_run A label r nonempty)

end HollowCube

/-! ### Independent producers: one order explored -/

section Producers

open EscapeControls (blank)

/-- Makes occurrence `o` and takes nothing. -/
def producer (o : ℕ) : Firing (Term signature) (Subst signature) ℕ :=
  ⟨⟨[], [], [], [], [.const 0]⟩, [], ⟨[], [], [o]⟩⟩

/-- The key of a producer is the occurrence it makes. -/
def producerKey (f : Firing (Term signature) (Subst signature) ℕ) : ℕ := f.selection.made.headD 0

theorem producer_equations (o : ℕ) (C : Configuration (Term signature) ℕ) :
    ((producer o).result blank C).equations = C.equations := by
  simp [Firing.result, Selection.result, Selection.problem, Selection.equations, producer]

theorem producer_present (o : ℕ) (C : Configuration (Term signature) ℕ) :
    ((producer o).result blank C).present = C.present ∪ {o} := by
  simp [Firing.result, Selection.result, MeTTaCalculus.OccurrenceCommits.fire, Selection.commit, producer]

/-- **A producer is admitted exactly where its occurrence is fresh**, without knowledge. -/
theorem producer_valid_iff {C : Configuration (Term signature) ℕ} (noKnowledge : C.equations = [])
    (o : ℕ) : (producer o).Valid A blank C ↔ o ∉ C.present := by
  constructor
  · intro valid
    have fresh := valid.firing.occurrences.fresh
    simpa [Selection.commit, producer] using fresh
  · intro fresh
    refine ⟨⟨by simp [producer], by simp [producer], rfl, rfl, rfl,
      ⟨by simp [Selection.commit, producer], by simp [Selection.commit, producer],
        by simp [Selection.commit, producer], by simpa [Selection.commit, producer] using fresh,
        by simp [Selection.commit]⟩,
      ⟨Subst.id signature, fun e member => by
        simp [Selection.problem, Selection.equations, producer, noKnowledge] at member⟩,
      by simp [producer]⟩, by simp [producer]⟩

/-- **Producers of distinct fresh occurrences run in every order.** -/
theorem producers_run : ∀ (os : List ℕ) {C : Configuration (Term signature) ℕ}, C.equations = [] →
    os.Nodup → (∀ o ∈ os, o ∉ C.present) →
      ∃ r : (firstOrder A blank).Run C, r.word.map Sigma.snd = os.map producer
  | [], C, _, _, _ => ⟨.nil C, rfl⟩
  | o :: os, C, noKnowledge, nodup, fresh => by
      have valid := (producer_valid_iff noKnowledge o).mpr (fresh o (List.mem_cons_self ..))
      obtain ⟨notIn, nodupRest⟩ := List.nodup_cons.mp nodup
      obtain ⟨r, word⟩ := producers_run os (C := (producer o).result blank C)
        (by rw [producer_equations, noKnowledge]) nodupRest (fun o' member => by
          rw [producer_present, Finset.mem_union, Finset.mem_singleton, not_or]
          exact ⟨fresh o' (List.mem_cons_of_mem _ member), fun same => notIn (same ▸ member)⟩)
      refine ⟨.cons (producer o) valid r, ?_⟩
      show producer o :: r.word.map Sigma.snd = producer o :: os.map producer
      rw [word]

/-- **Adjacent producers are independent**, without knowledge. -/
theorem producers_adjacent : ∀ {C : Configuration (Term signature) ℕ} (r : (firstOrder A blank).Run C),
    C.equations = [] → (∀ x ∈ r.word, ∃ o, x.2 = producer o) →
      AdjacentIndependent (firstOrderTransport A blank) (firstOrderTransport A blank).Independent r
  | _, .nil C, _, _ => .nil C
  | _, .cons f admitted (.nil _), _, _ =>
      AdjacentIndependent.single (T := firstOrderTransport A blank)
        (indep := (firstOrderTransport A blank).Independent) f admitted
  | C, .cons f admitted (.cons g later rest), noKnowledge, producers => by
      obtain ⟨o, hf⟩ := producers ⟨C, f⟩ (by simp [Interface.Step.Run.word])
      obtain ⟨o', hg⟩ := producers ⟨(firstOrder A blank).result f admitted, g⟩
        (by simp [Interface.Step.Run.word])
      change f = producer o at hf
      change g = producer o' at hg
      have afterKnowledge : ((firstOrder A blank).result f admitted).equations = [] := by
        show (f.result blank C).equations = []
        rw [hf, producer_equations, noKnowledge]
      have laterFresh : o' ∉ C.present ∪ {o} := by
        have fresh := (producer_valid_iff afterKnowledge o').mp (by rw [← hg]; exact later)
        rwa [show (firstOrder A blank).result f admitted = f.result blank C from rfl, hf,
          producer_present] at fresh
      rw [Finset.mem_union, Finset.mem_singleton, not_or] at laterFresh
      have firstFresh : o ∉ C.present := (producer_valid_iff noKnowledge o).mp (by rw [← hf]; exact admitted)
      have independent : (firstOrderTransport A blank).Independent C f g := by
        refine (firstOrder_independent_iff A blank).mpr ⟨admitted, ?_, later, ?_⟩
        · rw [hg]
          exact (producer_valid_iff noKnowledge o').mpr laterFresh.1
        · rw [hf, hg]
          refine (producer_valid_iff (by rw [producer_equations, noKnowledge]) o).mpr ?_
          rw [producer_present, Finset.mem_union, Finset.mem_singleton, not_or]
          exact ⟨firstFresh, fun same => laterFresh.2 same.symm⟩
      exact .cons admitted rfl later independent
        (producers_adjacent (.cons g later rest) afterKnowledge fun x member =>
          producers x (by simp only [Interface.Step.Run.word, List.mem_cons] at member ⊢; tauto))

/-- No knowledge and no occurrences. -/
def blankStart : Configuration (Term signature) ℕ := ⟨[], ∅⟩

/-- The key word of a run of producers is the word of their occurrences. -/
theorem keyWord_eq {C : Configuration (Term signature) ℕ} (r : (firstOrder A blank).Run C) :
    keyWord (fun _ f => producerKey f) r = (r.word.map Sigma.snd).map producerKey := by
  simp [keyWord, List.map_map, Function.comp_def]

/-- **Three independent firings are explored once instead of six times.** Each of the six orders of
the producers of `10`, `11` and `12` is a run with every adjacent pair independent, and such a run is
canonical exactly when its key word is `[10, 11, 12]`. -/
theorem clique_explored_once :
    (List.permutations [10, 11, 12]).length = 6 ∧
      (∀ os : List ℕ, os.Perm [10, 11, 12] → ∃ r : (firstOrder A blank).Run blankStart,
        r.word.map Sigma.snd = os.map producer ∧
          AdjacentIndependent (firstOrderTransport A blank) (firstOrderTransport A blank).Independent r) ∧
      ∀ r : (firstOrder A blank).Run blankStart,
        AdjacentIndependent (firstOrderTransport A blank) (firstOrderTransport A blank).Independent r →
          (keyWord (fun _ f => producerKey f) r).Perm [10, 11, 12] →
          (Canonical (firstOrderTransport A blank) (fun _ f => producerKey f)
              (firstOrderTransport A blank).Independent r ↔
            keyWord (fun _ f => producerKey f) r = [10, 11, 12]) := by
  refine ⟨by rw [List.length_permutations]; rfl, fun os perm => ?_, fun r adjacent perm => ⟨fun canonical => ?_, fun sorted => ?_⟩⟩
  · obtain ⟨r, word⟩ := producers_run os (C := blankStart) rfl (perm.nodup_iff.mpr (by decide))
      (fun _ _ => Finset.notMem_empty _)
    refine ⟨r, word, producers_adjacent r rfl fun x member => ?_⟩
    have inWord : x.2 ∈ r.word.map Sigma.snd := List.mem_map_of_mem member
    rw [word] at inWord
    obtain ⟨o, -, made⟩ := List.mem_map.mp inWord
    exact ⟨o, made.symm⟩
  · exact List.Perm.eq_of_pairwise (fun _ _ _ _ first second => le_antisymm first second)
      (Transport.pairwise_of_canonical (firstOrderKeyLaws A blank producerKey) adjacent canonical)
      (by decide) perm
  · exact Transport.canonical_of_pairwise (firstOrderKeyLaws A blank producerKey) (by rw [sorted]; decide)

end Producers

/-! ### A dependent pair is kept -/

section Dependent

open TransportControls (label watcher writer start watcher_valid watcher_refused_after_writer
  overlap_at_one_solution_only)

/-- The key counts the predicate queries: the writer's is smaller than the watcher's. -/
def queryKey (f : Firing (Term signature) (Subst signature) ℕ) : ℕ := f.queries.length

theorem writer_valid_after_watcher : writer.Valid A label (watcher.result label start) :=
  ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide,
    ⟨Subst.id signature, by
      simp [Firing.result, Selection.result, Selection.problem, Selection.equations, start, writer,
        watcher]⟩,
    by simp [writer]⟩, by simp [writer]⟩

/-- The watcher, then the writer. -/
abbrev watcherFirst : (firstOrder A label).Run start :=
  .cons watcher watcher_valid (.cons writer writer_valid_after_watcher (.nil _))

/-- **A dependent pair is kept.** The writer has the smaller key; the pair is not independent; the
order watcher then writer is canonical for every sound oracle; and the sorted order does not run. -/
theorem dependent_pair_kept :
    queryKey writer < queryKey watcher ∧
      ¬ (firstOrderTransport A label).Independent start watcher writer ∧
      (∀ indep : Configuration (Term signature) ℕ → Firing (Term signature) (Subst signature) ℕ →
          Firing (Term signature) (Subst signature) ℕ → Prop,
        (∀ C f g, indep C f g → (firstOrderTransport A label).Independent C f g) →
          Canonical (firstOrderTransport A label) (fun _ f => queryKey f) indep watcherFirst) ∧
      ¬ watcher.Valid A label (writer.result label start) := by
  have dependent : ¬ (firstOrderTransport A label).Independent start watcher writer :=
    fun independent => overlap_at_one_solution_only.2.2.2.2.1 independent.symm
  refine ⟨by decide, dependent, fun indep sound => ?_, watcher_refused_after_writer⟩
  refine (Transport.canonical_pair_iff watcher_valid writer_valid_after_watcher).mpr ?_
  rintro ⟨g, alike, -, independent⟩
  have same : g = writer := alike
  subst same
  exact dependent (sound _ _ _ independent)

end Dependent

end CanonicalControls

#print axioms firstOrderKeyLaws
#print axioms firstOrder_exists_canonical
#print axioms executable_of_run
#print axioms CanonicalControls.hollow_cube_never_round
#print axioms CanonicalControls.producer_valid_iff
#print axioms CanonicalControls.producers_run
#print axioms CanonicalControls.producers_adjacent
#print axioms CanonicalControls.clique_explored_once
#print axioms CanonicalControls.writer_valid_after_watcher
#print axioms CanonicalControls.dependent_pair_kept

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
