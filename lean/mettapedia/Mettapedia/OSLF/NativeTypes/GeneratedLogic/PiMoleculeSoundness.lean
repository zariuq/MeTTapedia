import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiLeastPartners

/-!
# π's molecules denote π processes, and their reactions are π reductions

A molecule denotes its restricted names, in any order, over the parallel composition of its guarded processes, in any
order (`Denotes`), and a bag of molecules the parallel composition of what they denote (`BagDenotes`). Then:

- **Any two denotations are structurally congruent** (`denotes_congruent`, `bagDenotes_congruent`).
- **A lifted process is congruent to its scope over its components** (`lifts_congruent`), and **renaming a restricted
  name is α-conversion** (`alpha_congruent`).
- **Every reaction of a bag is a reduction of π** between processes the bags denote (`reacts_reduces`): an internal
  communication reduces under the molecule's restrictions, and a communication between two molecules extrudes their
  scopes into one before it reduces, so a restricted payload stays restricted.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.Pi.LeastPartners

open Mettapedia.Languages.ProcessCalculi.PiCalculus
open Mettapedia.GSLT.BagRelativePushout (bag bag_injective)
open Mettapedia.GSLT.SemiSaturated (Reacts)

/-! ## Lifting is congruence -/

/-- **A lifted process is congruent to its scope over its components.** -/
theorem lifts_congruent {process : Process} {scope : Finset Name} {body : Multiset Prime}
    (lifts : Lifts process scope body) :
    ∃ (names : List Name) (primes : List Prime), names.Nodup ∧ names.toFinset = scope ∧ (primes : Multiset Prime) = body ∧
      Congruent process (nuList names (parList (primes.map Subtype.val))) := by
  induction lifts with
  | nil => exact ⟨[], [], List.nodup_nil, rfl, rfl, Congruent.refl _⟩
  | guarded guarded => exact ⟨[], [⟨_, guarded⟩], List.nodup_nil, rfl, rfl, (Congruent.nilRight _).symm⟩
  | @par left right leftScope rightScope leftBody rightBody _ _ apart leftFresh rightFresh leftHolds rightHolds =>
    obtain ⟨leftNames, leftPrimes, leftNodup, leftScopeEq, leftBodyEq, leftCongruent⟩ := leftHolds
    obtain ⟨rightNames, rightPrimes, rightNodup, rightScopeEq, rightBodyEq, rightCongruent⟩ := rightHolds
    subst leftScopeEq rightScopeEq leftBodyEq rightBodyEq
    refine ⟨leftNames ++ rightNames, leftPrimes ++ rightPrimes, ?_, by simp, by simp, ?_⟩
    · exact List.nodup_append.mpr ⟨leftNodup, rightNodup, fun name leftMem other rightMem same =>
        Finset.disjoint_left.mp apart (List.mem_toFinset.mpr leftMem) (List.mem_toFinset.mpr (same ▸ rightMem))⟩
    · refine (Congruent.par leftCongruent rightCongruent).trans ((nuList_merge ?_ ?_).trans (nuList_congruent _ ?_))
      · rw [← rightCongruent.freeNames_eq]
        exact leftFresh
      · refine Finset.disjoint_left.mpr fun name restricted inside => ?_
        by_cases bound : name ∈ leftNames.toFinset
        · exact Finset.disjoint_left.mp apart bound restricted
        · have free : name ∈ left.freeNames := by
            rw [leftCongruent.freeNames_eq, freeNames_nuList]
            exact Finset.mem_sdiff.mpr ⟨inside, bound⟩
          exact Finset.disjoint_left.mp rightFresh restricted free
      · rw [List.map_append]
        exact (parList_append _ _).symm
  | @nu name new process scope body _ newNotScope newFresh holds =>
    obtain ⟨names, primes, nodup, scopeEq, bodyEq, congruent⟩ := holds
    subst scopeEq bodyEq
    refine ⟨new :: names, primes, List.nodup_cons.mpr ⟨fun member => newNotScope (List.mem_toFinset.mpr member), nodup⟩,
      by simp, rfl, ?_⟩
    by_cases same : new = name
    · subst same
      rw [substitute_self] at congruent
      exact Congruent.nu _ congruent
    · have notFree : new ∉ process.freeNames := fun inside =>
        newFresh (by simp [Process.freeNames, inside, same])
      exact Congruent.trans ⟨.alpha_nu name new process notFree⟩ (Congruent.nu new congruent)

/-! ## Communication reduces -/

/-- **A communication reduces**, a replicated input through its unfolding, keeping the server. -/
theorem fires_reduces {receiver sender : Prime} {continuation : Process} {kept : Multiset Prime}
    (fires : Fires receiver sender continuation kept) :
    ∃ keptPrimes : List Prime, (keptPrimes : Multiset Prime) = kept ∧
      (∀ prime ∈ keptPrimes, prime.1.freeNames ⊆ receiver.1.freeNames) ∧
      Nonempty ((receiver.1 ||| sender.1) ⇝ (continuation ||| parList (keptPrimes.map Subtype.val))) := by
  cases fires with
  | input x y z body =>
    exact ⟨[], rfl, by simp, reduces_of_congruent (Congruent.refl _) ⟨.comm x y z body⟩ (Congruent.nilRight _).symm⟩
  | replicate x y z body =>
    refine ⟨[⟨.replicate x y body, .replicate x y body⟩], rfl, by simp, ?_⟩
    have unfold : Congruent (Process.replicate x y body ||| Process.output x z)
        ((Process.input x y body ||| Process.output x z) ||| Process.replicate x y body) :=
      (Congruent.par ⟨.replicate_unfold x y body⟩ (Congruent.refl _)).trans ((Congruent.assoc _ _ _).trans
        ((Congruent.par (Congruent.refl _) (Congruent.comm _ _)).trans (Congruent.assoc _ _ _).symm))
    exact reduces_of_congruent unfold (reduces_parLeft _ ⟨.comm x y z body⟩)
      (Congruent.par (Congruent.refl _) (Congruent.nilRight _).symm)

/-- **A communication under a scope**: a receiver and a sender among the parallel components react, and the
continuation's restrictions join the scope. -/
theorem comm_under_scope {names : List Name} {receiver sender : Prime} {rest : List Prime} {continuation : Process}
    {kept : Multiset Prime} {lifted : Finset Name} {components : Multiset Prime}
    (fires : Fires receiver sender continuation kept) (lifts : Lifts continuation lifted components)
    (fresh : ∀ name ∈ lifted,
      name ∉ names ∧ name ∉ (parList ((receiver :: sender :: rest).map Subtype.val)).freeNames) :
    ∃ (liftedNames : List Name) (liftedPrimes keptPrimes : List Prime), liftedNames.Nodup ∧ liftedNames.toFinset = lifted ∧
      (liftedPrimes : Multiset Prime) = components ∧ (keptPrimes : Multiset Prime) = kept ∧
      Nonempty (nuList names (parList ((receiver :: sender :: rest).map Subtype.val)) ⇝
        nuList (names ++ liftedNames) (parList ((rest ++ keptPrimes ++ liftedPrimes).map Subtype.val))) := by
  obtain ⟨keptPrimes, keptEq, keptNames, step⟩ := fires_reduces fires
  obtain ⟨liftedNames, liftedPrimes, nodup, scopeEq, bodyEq, congruent⟩ := lifts_congruent lifts
  refine ⟨liftedNames, liftedPrimes, keptPrimes, nodup, scopeEq, bodyEq, keptEq, ?_⟩
  rw [nuList_append]
  set restProcess := parList (rest.map Subtype.val)
  set keptProcess := parList (keptPrimes.map Subtype.val)
  set liftedProcess := parList (liftedPrimes.map Subtype.val)
  have outside : ∀ name ∈ liftedNames.toFinset, name ∉ receiver.1.freeNames ∧ name ∉ restProcess.freeNames := by
    intro name member
    have away := (fresh name (scopeEq ▸ member)).2
    simp only [List.map_cons, parList, Process.freeNames, Finset.mem_union, not_or] at away
    exact ⟨away.1, away.2.2⟩
  have keptFresh : Disjoint liftedNames.toFinset keptProcess.freeNames := by
    refine Finset.disjoint_left.mpr fun name member inside => ?_
    obtain ⟨process, processMem, present⟩ := mem_freeNames_parList.mp inside
    obtain ⟨prime, primeMem, rfl⟩ := List.mem_map.mp processMem
    exact (outside name member).1 (keptNames prime primeMem present)
  have restFresh : Disjoint liftedNames.toFinset (keptProcess ||| restProcess).freeNames := by
    refine Finset.disjoint_left.mpr fun name member inside => ?_
    simp only [Process.freeNames, Finset.mem_union] at inside
    rcases inside with kept | restInside
    · exact Finset.disjoint_left.mp keptFresh member kept
    · exact (outside name member).2 restInside
  have before : Congruent (parList ((receiver :: sender :: rest).map Subtype.val))
      ((receiver.1 ||| sender.1) ||| restProcess) := (Congruent.assoc _ _ _).symm
  have after : Congruent ((continuation ||| keptProcess) ||| restProcess)
      (nuList liftedNames (parList ((rest ++ keptPrimes ++ liftedPrimes).map Subtype.val))) := by
    refine (Congruent.assoc _ _ _).trans ((Congruent.par congruent (Congruent.refl _)).trans
      ((nuList_extrude restFresh).trans (nuList_congruent _ ?_)))
    rw [List.map_append, List.map_append]
    refine Congruent.trans ?_ ((parList_append _ _).trans (Congruent.par (parList_append _ _) (Congruent.refl _))).symm
    exact (Congruent.comm _ _).trans (Congruent.par (Congruent.comm _ _) (Congruent.refl _))
  exact reduces_of_congruent (nuList_congruent names before) (reduces_nuList names (reduces_parLeft _ step))
    (nuList_congruent names after)

/-! ## What molecules denote -/

/-- **What a molecule denotes**: its restricted names, in some order, over its guarded processes, in some order. -/
def Denotes (molecule : Molecule) (process : Process) : Prop :=
  ∃ (names : List Name) (primes : List Prime), names.Nodup ∧ names.toFinset = molecule.scope ∧
    (primes : Multiset Prime) = molecule.body ∧ process = nuList names (parList (primes.map Subtype.val))

theorem denotes_exists (molecule : Molecule) : ∃ process, Denotes molecule process :=
  ⟨_, molecule.scope.toList, molecule.body.toList, molecule.scope.nodup_toList, by simp, by simp, rfl⟩

/-- **Any two denotations of a molecule are structurally congruent.** -/
theorem denotes_congruent {molecule : Molecule} {first second : Process} (firstDenotes : Denotes molecule first)
    (secondDenotes : Denotes molecule second) : Congruent first second := by
  obtain ⟨names, primes, nodup, scopeEq, bodyEq, rfl⟩ := firstDenotes
  obtain ⟨names', primes', nodup', scopeEq', bodyEq', rfl⟩ := secondDenotes
  have namesPerm : names.Perm names' := (List.perm_ext_iff_of_nodup nodup nodup').mpr fun name => by
    rw [← List.mem_toFinset, ← List.mem_toFinset, scopeEq, scopeEq']
  have primesPerm : primes.Perm primes' := Multiset.coe_eq_coe.mp (bodyEq.trans bodyEq'.symm)
  exact (nuList_perm namesPerm _).trans (nuList_congruent _ (parList_perm (primesPerm.map _)))

theorem freeNames_parList_primes {molecule : Molecule} {primes : List Prime}
    (bodyEq : (primes : Multiset Prime) = molecule.body) :
    (parList (primes.map Subtype.val)).freeNames ⊆ molecule.bodyNames := by
  intro name inside
  obtain ⟨process, processMem, present⟩ := mem_freeNames_parList.mp inside
  obtain ⟨prime, primeMem, rfl⟩ := List.mem_map.mp processMem
  exact Molecule.mem_bodyNames.mpr ⟨prime, bodyEq ▸ Multiset.mem_coe.mpr primeMem, present⟩

/-- **Renaming a restricted name is α-conversion.** -/
theorem renameStep_congruent {molecule renamed : Molecule} (step : Molecule.RenameStep molecule renamed)
    {process : Process} (denotes : Denotes molecule process) :
    ∃ process', Denotes renamed process' ∧ Congruent process process' := by
  cases step with
  | @rename old new restricted unused fresh =>
    obtain ⟨names, primes, nodup, scopeEq, bodyEq, rfl⟩ := denotes
    have oldMem : old ∈ names := List.mem_toFinset.mp (scopeEq ▸ restricted)
    have perm : names.Perm (old :: names.erase old) := List.perm_cons_erase oldMem
    have oldNotRest : old ∉ names.erase old := nodup.not_mem_erase
    have newNotRest : new ∉ names.erase old := fun member =>
      unused (scopeEq ▸ List.mem_toFinset.mpr (List.mem_of_mem_erase member))
    have notFree : new ∉ (nuList (names.erase old) (parList (primes.map Subtype.val))).freeNames := by
      rw [freeNames_nuList]
      exact fun inside => fresh (freeNames_parList_primes bodyEq (Finset.mem_sdiff.mp inside).1)
    refine ⟨_, ⟨new :: names.erase old, primes.map (Molecule.renamePrime old new),
      List.nodup_cons.mpr ⟨newNotRest, nodup.erase old⟩, ?_, by simp [← bodyEq], rfl⟩, ?_⟩
    · ext name
      simp only [List.toFinset_cons, Finset.mem_insert, List.mem_toFinset, nodup.mem_erase_iff, Finset.mem_erase,
        ← scopeEq]
    · refine (nuList_perm perm _).trans (Congruent.trans ⟨.alpha_nu old new _ notFree⟩ ?_)
      rw [substitute_nuList oldNotRest newNotRest, substitute_parList, List.map_map, List.map_map]
      exact Congruent.refl _

/-- **α-variants denote congruent processes.** -/
theorem alpha_congruent {molecule renamed : Molecule} (variant : Molecule.Alpha molecule renamed) {process : Process}
    (denotes : Denotes molecule process) : ∃ process', Denotes renamed process' ∧ Congruent process process' := by
  induction variant with
  | refl => exact ⟨process, denotes, Congruent.refl _⟩
  | tail _ step holds =>
    obtain ⟨middle, middleDenotes, congruent⟩ := holds
    obtain ⟨last, lastDenotes, congruent'⟩ := renameStep_congruent step middleDenotes
    exact ⟨last, lastDenotes, congruent.trans congruent'⟩

/-! ## Communications are reductions -/

/-- **A communication inside a molecule is a reduction** of what it denotes. -/
theorem comm_reduces {molecule : Molecule} {receiver sender : Prime} {continuation : Process} {kept : Multiset Prime}
    {lifted : Finset Name} {components : Multiset Prime} (contained : {receiver, sender} ≤ molecule.body)
    (fires : Fires receiver sender continuation kept) (lifts : Lifts continuation lifted components)
    (fresh : Disjoint lifted (molecule.scope ∪ molecule.bodyNames)) {process : Process}
    (denotes : Denotes molecule process) :
    ∃ process', Denotes ⟨molecule.scope ∪ lifted, molecule.body - {receiver, sender} + kept + components⟩ process' ∧
      Nonempty (process ⇝ process') := by
  obtain ⟨names, primes, nodup, scopeEq, bodyEq, rfl⟩ := denotes
  obtain ⟨extra, sum⟩ := Multiset.le_iff_exists_add.mp contained
  have perm : primes.Perm (receiver :: sender :: extra.toList) := by
    apply Multiset.coe_eq_coe.mp
    rw [bodyEq, sum]
    simp only [Multiset.insert_eq_cons, Multiset.cons_add, Multiset.singleton_add]
    rw [← Multiset.cons_coe, ← Multiset.cons_coe, Multiset.coe_toList]
  have permEq : ((receiver :: sender :: extra.toList : List Prime) : Multiset Prime) = molecule.body := by
    rw [← bodyEq]
    exact Multiset.coe_eq_coe.mpr perm.symm
  obtain ⟨liftedNames, liftedPrimes, keptPrimes, liftedNodup, liftedScope, liftedBody, keptEq, step⟩ :=
    comm_under_scope (names := names) (rest := extra.toList) fires lifts fun name member =>
      ⟨fun inside => Finset.disjoint_left.mp fresh member (Finset.mem_union_left _ (scopeEq ▸ List.mem_toFinset.mpr inside)),
        fun inside => Finset.disjoint_left.mp fresh member (Finset.mem_union_right _ (freeNames_parList_primes permEq inside))⟩
  refine ⟨_, ⟨names ++ liftedNames, extra.toList ++ keptPrimes ++ liftedPrimes, ?_, ?_, ?_, rfl⟩,
    reduces_of_congruent (nuList_congruent _ (parList_perm (perm.map _))) step (Congruent.refl _)⟩
  · refine List.nodup_append.mpr ⟨nodup, liftedNodup, fun name inside other liftedInside same => ?_⟩
    subst same
    exact Finset.disjoint_left.mp fresh (liftedScope ▸ List.mem_toFinset.mpr liftedInside)
      (Finset.mem_union_left _ (scopeEq ▸ List.mem_toFinset.mpr inside))
  · rw [List.toFinset_append, scopeEq, liftedScope]
  · rw [← Multiset.coe_add, ← Multiset.coe_add, liftedBody, keptEq, sum, add_tsub_cancel_left, Multiset.coe_toList]

/-- **An internal communication is a reduction.** -/
theorem internal_reduces {molecule result : Molecule} (internal : Internal molecule result) {process : Process}
    (denotes : Denotes molecule process) : ∃ process', Denotes result process' ∧ Nonempty (process ⇝ process') := by
  cases internal with
  | comm contained fires lifts fresh => exact comm_reduces contained fires lifts fresh denotes

theorem bodyNames_add (first second : Molecule) (scope : Finset Name) :
    (Molecule.mk scope (first.body + second.body)).bodyNames = first.bodyNames ∪ second.bodyNames := by
  ext name
  simp only [Finset.mem_union, Molecule.mem_bodyNames, Multiset.mem_add]
  constructor
  · rintro ⟨prime, (inFirst | inSecond), present⟩
    · exact Or.inl ⟨prime, inFirst, present⟩
    · exact Or.inr ⟨prime, inSecond, present⟩
  · rintro (⟨prime, inFirst, present⟩ | ⟨prime, inSecond, present⟩)
    · exact ⟨prime, Or.inl inFirst, present⟩
    · exact ⟨prime, Or.inr inSecond, present⟩

/-- **Two molecules apart merge**: their parallel composition is congruent to their merged scope. -/
theorem merge_denotes {first second : Molecule} (apart : Apart first second) {firstProcess secondProcess : Process}
    (firstDenotes : Denotes first firstProcess) (secondDenotes : Denotes second secondProcess) :
    ∃ process, Denotes ⟨first.scope ∪ second.scope, first.body + second.body⟩ process ∧
      Congruent (firstProcess ||| secondProcess) process := by
  obtain ⟨firstNames, firstPrimes, firstNodup, firstScope, firstBody, rfl⟩ := firstDenotes
  obtain ⟨secondNames, secondPrimes, secondNodup, secondScope, secondBody, rfl⟩ := secondDenotes
  refine ⟨_, ⟨firstNames ++ secondNames, firstPrimes ++ secondPrimes, ?_, ?_, ?_, rfl⟩, ?_⟩
  · refine List.nodup_append.mpr ⟨firstNodup, secondNodup, fun name inside other secondInside same => ?_⟩
    subst same
    exact Finset.disjoint_left.mp apart.1 (firstScope ▸ List.mem_toFinset.mpr inside)
      (Finset.mem_union_left _ (secondScope ▸ List.mem_toFinset.mpr secondInside))
  · rw [List.toFinset_append, firstScope, secondScope]
  · rw [← Multiset.coe_add, firstBody, secondBody]
  · refine (nuList_merge ?_ ?_).trans (nuList_congruent _ ?_)
    · rw [firstScope, freeNames_nuList]
      exact apart.1.mono_right fun name inside =>
        Finset.mem_union_right _ (freeNames_parList_primes secondBody (Finset.mem_sdiff.mp inside).1)
    · rw [secondScope]
      exact apart.2.mono_right fun name inside => Finset.mem_union_right _ (freeNames_parList_primes firstBody inside)
    · rw [List.map_append]
      exact (parList_append _ _).symm

theorem pair_sub_add {first second : Multiset Prime} {mine theirs : Prime} (mineMem : mine ∈ first)
    (theirsMem : theirs ∈ second) : first + second - {mine, theirs} = (first - {mine}) + (second - {theirs}) := by
  obtain ⟨firstRest, rfl⟩ := Multiset.exists_cons_of_mem mineMem
  obtain ⟨secondRest, rfl⟩ := Multiset.exists_cons_of_mem theirsMem
  rw [Multiset.insert_eq_cons, Multiset.sub_cons, Multiset.sub_singleton, Multiset.sub_singleton,
    Multiset.sub_singleton, Multiset.erase_cons_head, Multiset.erase_cons_head, Multiset.cons_add,
    Multiset.erase_cons_head, Multiset.add_cons, Multiset.erase_cons_head]

/-- **A communication between two molecules is a reduction** of their parallel composition, after their scopes extrude
into one. -/
theorem cross_reduces {first second result : Molecule} (cross : Cross first second result)
    {firstProcess secondProcess : Process} (firstDenotes : Denotes first firstProcess)
    (secondDenotes : Denotes second secondProcess) :
    ∃ process', Denotes result process' ∧ Nonempty ((firstProcess ||| secondProcess) ⇝ process') := by
  cases cross with
  | @receive first' second' receiver sender continuation kept lifted components firstVariant secondVariant apart
      receiverMem senderMem fires lifts fresh =>
    obtain ⟨firstProcess', firstDenotes', firstCongruent⟩ := alpha_congruent firstVariant firstDenotes
    obtain ⟨secondProcess', secondDenotes', secondCongruent⟩ := alpha_congruent secondVariant secondDenotes
    obtain ⟨merged, mergedDenotes, mergedCongruent⟩ := merge_denotes apart firstDenotes' secondDenotes'
    have contained : ({receiver, sender} : Multiset Prime) ≤ first'.body + second'.body := by
      rw [Multiset.insert_eq_cons, ← Multiset.singleton_add]
      exact add_le_add (Multiset.singleton_le.mpr receiverMem) (Multiset.singleton_le.mpr senderMem)
    have fresh' : Disjoint lifted ((Molecule.mk (first'.scope ∪ second'.scope) (first'.body + second'.body)).scope ∪
        (Molecule.mk (first'.scope ∪ second'.scope) (first'.body + second'.body)).bodyNames) := by
      rw [bodyNames_add]
      exact fresh.mono_right fun name inside => by simp only [Finset.mem_union] at inside ⊢; tauto
    obtain ⟨process', denotes', step⟩ := comm_reduces contained fires lifts fresh' mergedDenotes
    refine ⟨process', ?_, reduces_of_congruent ((Congruent.par firstCongruent secondCongruent).trans mergedCongruent)
      step (Congruent.refl _)⟩
    simpa only [pair_sub_add receiverMem senderMem] using denotes'
  | @send first' second' receiver sender continuation kept lifted components firstVariant secondVariant apart
      senderMem receiverMem fires lifts fresh =>
    obtain ⟨firstProcess', firstDenotes', firstCongruent⟩ := alpha_congruent firstVariant firstDenotes
    obtain ⟨secondProcess', secondDenotes', secondCongruent⟩ := alpha_congruent secondVariant secondDenotes
    obtain ⟨merged, mergedDenotes, mergedCongruent⟩ := merge_denotes apart firstDenotes' secondDenotes'
    have contained : ({receiver, sender} : Multiset Prime) ≤ first'.body + second'.body := by
      rw [Multiset.insert_eq_cons, ← Multiset.singleton_add, add_comm]
      exact add_le_add (Multiset.singleton_le.mpr senderMem) (Multiset.singleton_le.mpr receiverMem)
    have fresh' : Disjoint lifted ((Molecule.mk (first'.scope ∪ second'.scope) (first'.body + second'.body)).scope ∪
        (Molecule.mk (first'.scope ∪ second'.scope) (first'.body + second'.body)).bodyNames) := by
      rw [bodyNames_add]
      exact fresh.mono_right fun name inside => by simp only [Finset.mem_union] at inside ⊢; tauto
    obtain ⟨process', denotes', step⟩ := comm_reduces contained fires lifts fresh' mergedDenotes
    refine ⟨process', ?_, reduces_of_congruent ((Congruent.par firstCongruent secondCongruent).trans mergedCongruent)
      step (Congruent.refl _)⟩
    have swap : ({receiver, sender} : Multiset Prime) = {sender, receiver} := by
      simp only [Multiset.insert_eq_cons]
      exact Multiset.cons_swap _ _ _
    simpa only [swap, pair_sub_add senderMem receiverMem] using denotes'

/-! ## Bags of molecules -/

/-- **What a bag of molecules denotes**: the parallel composition of what its molecules denote, in some order. -/
def BagDenotes (agent : Multiset Molecule) (process : Process) : Prop :=
  ∃ (molecules : List Molecule) (processes : List Process), (molecules : Multiset Molecule) = agent ∧
    List.Forall₂ Denotes molecules processes ∧ process = parList processes

theorem forall₂_denotes_exists : ∀ molecules : List Molecule, ∃ processes, List.Forall₂ Denotes molecules processes
  | [] => ⟨[], .nil⟩
  | molecule :: molecules =>
    let ⟨process, denotes⟩ := denotes_exists molecule
    let ⟨processes, rest⟩ := forall₂_denotes_exists molecules
    ⟨process :: processes, .cons denotes rest⟩

theorem bagDenotes_exists (agent : Multiset Molecule) : ∃ process, BagDenotes agent process :=
  let ⟨processes, denotes⟩ := forall₂_denotes_exists agent.toList
  ⟨_, agent.toList, processes, Multiset.coe_toList _, denotes, rfl⟩

theorem forall₂_congruent : ∀ {molecules : List Molecule} {first second : List Process},
    List.Forall₂ Denotes molecules first → List.Forall₂ Denotes molecules second → List.Forall₂ Congruent first second
  | [], _, _, .nil, .nil => .nil
  | _ :: _, _ :: _, _ :: _, .cons denotes rest, .cons denotes' rest' =>
    .cons (denotes_congruent denotes denotes') (forall₂_congruent rest rest')

/-- Denotations follow a permutation of the molecules. -/
theorem forall₂_perm {molecules molecules' : List Molecule} (perm : molecules.Perm molecules')
    {processes : List Process} (denotes : List.Forall₂ Denotes molecules processes) :
    ∃ processes', List.Forall₂ Denotes molecules' processes' ∧ processes.Perm processes' := by
  induction perm generalizing processes with
  | nil => cases denotes; exact ⟨[], .nil, .nil⟩
  | cons molecule _ holds =>
    cases denotes with
    | cons head rest =>
      obtain ⟨processes', rest', perm'⟩ := holds rest
      exact ⟨_, .cons head rest', perm'.cons _⟩
  | swap first second rest =>
    cases denotes with
    | cons secondDenotes others =>
      cases others with
      | cons firstDenotes rest' => exact ⟨_, .cons firstDenotes (.cons secondDenotes rest'), .swap _ _ _⟩
  | trans _ _ first second =>
    obtain ⟨middle, middleDenotes, firstPerm⟩ := first denotes
    obtain ⟨last, lastDenotes, secondPerm⟩ := second middleDenotes
    exact ⟨last, lastDenotes, firstPerm.trans secondPerm⟩

/-- **Any two denotations of a bag are structurally congruent.** -/
theorem bagDenotes_congruent {agent : Multiset Molecule} {first second : Process} (firstDenotes : BagDenotes agent first)
    (secondDenotes : BagDenotes agent second) : Congruent first second := by
  obtain ⟨molecules, processes, moleculesEq, denotes, rfl⟩ := firstDenotes
  obtain ⟨molecules', processes', moleculesEq', denotes', rfl⟩ := secondDenotes
  obtain ⟨permuted, permutedDenotes, perm⟩ :=
    forall₂_perm (Multiset.coe_eq_coe.mp (moleculesEq.trans moleculesEq'.symm)) denotes
  exact (parList_perm perm).trans (parList_forall₂ (forall₂_congruent permutedDenotes denotes'))

/-- **Every reaction of a bag of molecules is a reduction of π** between processes the bags denote. -/
theorem reacts_reduces {agent next : Multiset Molecule} (reacts : Reacts rules (bag agent) (bag next))
    {process : Process} (denotes : BagDenotes agent process) :
    ∃ process', BagDenotes next process' ∧ Nonempty (process ⇝ process') := by
  obtain ⟨rule, member, redex, reactum, redexEq, reactumEq, contained, rfl⟩ :=
    Mettapedia.GSLT.BagSaturated.reacts_iff.mp reacts
  obtain ⟨restProcesses, restDenotes⟩ := forall₂_denotes_exists (agent - redex).toList
  have agentEq : agent = redex + (agent - redex) := (add_tsub_cancel_of_le contained).symm
  rcases member with ⟨molecule, result, internal, rfl⟩ | ⟨first, second, result, cross, rfl⟩
  · obtain rfl := bag_injective redexEq
    obtain rfl := bag_injective reactumEq
    obtain ⟨moleculeProcess, moleculeDenotes⟩ := denotes_exists molecule
    obtain ⟨resultProcess, resultDenotes, step⟩ := internal_reduces internal moleculeDenotes
    have source : BagDenotes agent (parList (moleculeProcess :: restProcesses)) := by
      refine ⟨molecule :: (agent - {molecule}).toList, _, ?_, .cons moleculeDenotes restDenotes, rfl⟩
      rw [← Multiset.cons_coe, Multiset.coe_toList, ← Multiset.singleton_add, ← agentEq]
    refine ⟨parList (resultProcess :: restProcesses),
      ⟨result :: (agent - {molecule}).toList, _, ?_, .cons resultDenotes restDenotes, rfl⟩,
      reduces_of_congruent (bagDenotes_congruent denotes source) (reduces_parLeft _ step) (Congruent.refl _)⟩
    rw [← Multiset.cons_coe, Multiset.coe_toList, ← Multiset.singleton_add]
  · obtain rfl := bag_injective redexEq
    obtain rfl := bag_injective reactumEq
    obtain ⟨firstProcess, firstDenotes⟩ := denotes_exists first
    obtain ⟨secondProcess, secondDenotes⟩ := denotes_exists second
    obtain ⟨resultProcess, resultDenotes, step⟩ := cross_reduces cross firstDenotes secondDenotes
    have source : BagDenotes agent (parList (firstProcess :: secondProcess :: restProcesses)) := by
      refine ⟨first :: second :: (agent - {first, second}).toList, _, ?_,
        .cons firstDenotes (.cons secondDenotes restDenotes), rfl⟩
      rw [← Multiset.cons_coe, ← Multiset.cons_coe, Multiset.coe_toList]
      conv_rhs => rw [agentEq]
      rw [Multiset.insert_eq_cons, Multiset.cons_add, Multiset.singleton_add]
    refine ⟨parList (resultProcess :: restProcesses),
      ⟨result :: (agent - {first, second}).toList, _, ?_, .cons resultDenotes restDenotes, rfl⟩, ?_⟩
    · rw [← Multiset.cons_coe, Multiset.coe_toList, ← Multiset.singleton_add]
    · exact reduces_of_congruent ((bagDenotes_congruent denotes source).trans (Congruent.assoc _ _ _).symm)
        (reduces_parLeft _ step) (Congruent.refl _)

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.Pi.LeastPartners
