import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiMoleculeLiftings
import Mettapedia.Languages.ProcessCalculi.PiCalculus.SaturatedReduction

/-!
# Representation independence of π molecules

Bags of molecules denoting structurally congruent processes react alike, so the least labels describe processes, not
the ways of writing them.

- **Renaming a restricted name keeps communications** (`internal_renameStep`, `internalSim_of_alpha`): a communication
  of a renamed molecule is the renaming of one of the original, and their results denote congruent processes.
- **A lifting of a denotation whose restricted names are fresh is an α-variant of the molecule**
  (`alpha_of_lifts_denotation`); a molecule lifts what it denotes with its own names (`lifts_of_denotes`).
- **A bag merges into one molecule** (`Merged`, `merged_exists`, `merged_denotes`): α-variants of its molecules, each
  apart from the rest, side by side. A communication inside the merge is a reaction of the bag, inside one molecule or
  across two (`merged_internal_reacts`).
- **Completeness for every bag** (`bag_reacts_of_reduces`): every reduction of what a bag denotes is a reaction of that
  bag, up to structural congruence. Harmony gives a molecule realizing the reduction; its lifting into the bag's
  denotation is congruent to it (`liftsRel_of_congruent`), an α-variant of the merge, whose communication is the bag's.
- **Representation independence** (`saturatedBisimilar_of_congruent`): bags denoting structurally congruent processes
  are saturated bisimilar, in every context.
- **π's own equivalence** (`saturatedBisimilarIn_iff_reduction`): bags are saturated bisimilar exactly when the
  processes they denote are saturated reduction bisimilar, beside every π process.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.Pi.LeastPartners

open Mettapedia.Languages.ProcessCalculi.PiCalculus
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Molecule
open Mettapedia.GSLT.BagRelativePushout (bag bag_injective)
open Mettapedia.GSLT.SemiSaturated (Reacts)
open Mettapedia.GSLT.BagHennessyMilner (SaturatedBisimilarIn IsSaturatedIn)

/-! ## Communications of a renamed molecule -/

theorem pair_le_map {body : Multiset Prime} {f : Prime → Prime} {first second : Prime}
    (contained : {first, second} ≤ body.map f) :
    ∃ first₀ second₀, {first₀, second₀} ≤ body ∧ f first₀ = first ∧ f second₀ = second := by
  have firstMem : first ∈ body.map f := Multiset.subset_of_le contained (by simp)
  obtain ⟨first₀, firstMem₀, rfl⟩ := Multiset.mem_map.mp firstMem
  obtain ⟨rest, rfl⟩ := Multiset.exists_cons_of_mem firstMem₀
  rw [Multiset.map_cons, Multiset.insert_eq_cons, Multiset.cons_le_cons_iff, Multiset.singleton_le] at contained
  obtain ⟨second₀, secondMem₀, rfl⟩ := Multiset.mem_map.mp contained
  refine ⟨first₀, second₀, ?_, rfl, rfl⟩
  rw [Multiset.insert_eq_cons, Multiset.cons_le_cons_iff, Multiset.singleton_le]
  exact secondMem₀

theorem map_sub_pair {body : Multiset Prime} {f : Prime → Prime} {first second : Prime}
    (contained : {first, second} ≤ body) : body.map f - {f first, f second} = (body - {first, second}).map f := by
  obtain ⟨rest, rfl⟩ := Multiset.le_iff_exists_add.mp contained
  rw [Multiset.map_add, show ({first, second} : Multiset Prime).map f = {f first, f second} by simp,
    add_tsub_cancel_left, add_tsub_cancel_left]

/-- What a communication keeps: nothing after an input, the server after a replicated input. -/
theorem fires_kept {receiver sender : Prime} {continuation : Process} {kept : Multiset Prime}
    (fires : Fires receiver sender continuation kept) :
    ((∃ x binder body, receiver.1 = .input x binder body) ∧ kept = 0) ∨
      ((∃ x binder body, receiver.1 = .replicate x binder body) ∧ kept = {receiver}) := by
  cases fires with
  | input x binder payload body => exact Or.inl ⟨⟨x, binder, body, rfl⟩, rfl⟩
  | replicate x binder payload body => exact Or.inr ⟨⟨x, binder, body, rfl⟩, rfl⟩

theorem replaceName_injective {old new first second : Name} (firstNew : first ≠ new) (secondNew : second ≠ new)
    (same : (if first = old then new else first) = (if second = old then new else second)) : first = second := by
  split_ifs at same with firstOld secondOld <;> simp_all

/-- **A communication of renamed guarded processes is the renaming of one of the originals.** -/
theorem fires_renamed {old new : Name} {receiver sender : Prime} {continuation : Process} {kept : Multiset Prime}
    (fires : Fires (renamePrime old new receiver) (renamePrime old new sender) continuation kept)
    (receiverNew : new ∉ receiver.1.freeNames) (senderNew : new ∉ sender.1.freeNames) :
    ∃ continuation₀ kept₀, Fires receiver sender continuation₀ kept₀ ∧ kept = kept₀.map (renamePrime old new) := by
  obtain ⟨x', payload', keptPrimes, sends', receives', -, -, -⟩ := fires_receive fires
  obtain ⟨sender, senderGuarded⟩ := sender
  obtain ⟨receiver, receiverGuarded⟩ := receiver
  simp only [renamePrime] at sends' receives' fires receiverNew senderNew
  cases senderGuarded with
  | input => obtain ⟨_, _, shape⟩ := substitute_input_shape .. ; rw [shape] at sends'; cases sends'
  | replicate => obtain ⟨_, _, shape⟩ := substitute_replicate_shape .. ; rw [shape] at sends'; cases sends'
  | output x₁ payload =>
    simp only [Process.substitute, Process.output.injEq] at sends'
    obtain ⟨channelEq, -⟩ := sends'
    have senderChannel : x₁ ≠ new := fun same => senderNew (by simp [Process.freeNames, same])
    cases receiverGuarded with
    | output =>
      simp only [Process.substitute] at receives'
      rcases receives' with ⟨_, _, impossible⟩ | ⟨_, _, impossible⟩ <;> cases impossible
    | input x₀ binder body =>
      have receiverChannel : x₀ ≠ new := fun same => receiverNew (by simp [Process.freeNames, same])
      obtain ⟨binder', body', shape⟩ := substitute_input_shape x₀ binder body old new
      rw [shape] at receives'
      rcases receives' with ⟨_, _, same⟩ | ⟨_, _, impossible⟩
      · simp only [Process.input.injEq] at same
        obtain rfl := replaceName_injective receiverChannel senderChannel (same.1.trans channelEq.symm)
        refine ⟨_, 0, .input x₀ binder payload body, ?_⟩
        rcases fires_kept fires with ⟨-, kept₀⟩ | ⟨⟨_, _, _, impossible⟩, -⟩
        · rw [kept₀, Multiset.map_zero]
        · simp only [shape] at impossible; cases impossible
      · cases impossible
    | replicate x₀ binder body =>
      have receiverChannel : x₀ ≠ new := fun same => receiverNew (by simp [Process.freeNames, same])
      obtain ⟨binder', body', shape⟩ := substitute_replicate_shape x₀ binder body old new
      rw [shape] at receives'
      rcases receives' with ⟨_, _, impossible⟩ | ⟨_, _, same⟩
      · cases impossible
      · simp only [Process.replicate.injEq] at same
        obtain rfl := replaceName_injective receiverChannel senderChannel (same.1.trans channelEq.symm)
        refine ⟨_, _, .replicate x₀ binder payload body, ?_⟩
        rcases fires_kept fires with ⟨⟨_, _, _, impossible⟩, -⟩ | ⟨-, kept₀⟩
        · simp only [shape] at impossible; cases impossible
        · rw [kept₀, Multiset.map_singleton]
          rfl

/-- **A communication of a molecule with a restricted name renamed is the renaming of one of the molecule's**, and
their results denote congruent processes. -/
theorem internal_renameStep {molecule renamed : Molecule} (step : RenameStep molecule renamed) :
    InternalSim renamed molecule := by
  intro result internal
  cases step with
  | @rename old new restricted unused fresh =>
  cases internal with
  | @comm receiver' sender' continuation' kept' lifted' components' contained fires lifts freshLifted =>
  obtain ⟨receiver, sender, contained₀, rfl, rfl⟩ := pair_le_map contained
  have receiverMem : receiver ∈ molecule.body := Multiset.subset_of_le contained₀ (by simp)
  have senderMem : sender ∈ molecule.body := Multiset.subset_of_le contained₀ (by simp)
  have receiverNew : new ∉ receiver.1.freeNames := fun inside => fresh (mem_bodyNames.mpr ⟨_, receiverMem, inside⟩)
  have senderNew : new ∉ sender.1.freeNames := fun inside => fresh (mem_bodyNames.mpr ⟨_, senderMem, inside⟩)
  obtain ⟨continuation, kept, fires₀, -⟩ := fires_renamed fires receiverNew senderNew
  obtain ⟨lifted, components, lifts₀, avoids⟩ :=
    lifts_exists _ continuation le_rfl (molecule.scope ∪ molecule.bodyNames)
  refine ⟨_, .comm contained₀ fires₀ lifts₀ avoids, ?_⟩
  obtain ⟨x, payload, -, sends, receives, -, -, -⟩ := fires_receive fires₀
  obtain ⟨others, othersNodup, othersEq⟩ : ∃ others : List Name, others.Nodup ∧
      others.toFinset = molecule.scope.erase old := ⟨_, Finset.nodup_toList _, Finset.toList_toFinset _⟩
  have oldOthers : old ∉ others := fun inside =>
    Finset.notMem_erase old molecule.scope (othersEq ▸ List.mem_toFinset.mpr inside)
  have newOthers : new ∉ others := fun inside =>
    unused (Finset.mem_of_mem_erase (othersEq ▸ List.mem_toFinset.mpr inside))
  obtain ⟨rest, restEq⟩ : ∃ rest : List Prime, (rest : Multiset Prime) = molecule.body - {receiver, sender} :=
    ⟨_, Multiset.coe_toList _⟩
  obtain ⟨process, denotes⟩ := denotes_exists
    ⟨molecule.scope ∪ lifted, molecule.body - {receiver, sender} + kept + components⟩
  obtain ⟨process', denotes'⟩ := denotes_exists
    ⟨insert new (molecule.scope.erase old) ∪ lifted', molecule.body.map (renamePrime old new) -
      {renamePrime old new receiver, renamePrime old new sender} + kept' + components'⟩
  have original := result_congruent contained₀ fires₀ lifts₀ avoids (names := old :: others) (rest := rest)
    (List.nodup_cons.mpr ⟨oldOthers, othersNodup⟩)
    (by rw [List.toFinset_cons, othersEq, Finset.insert_erase restricted]) restEq sends denotes
  have renamedSends : (renamePrime old new sender).1 =
      .output (if x = old then new else x) (if payload = old then new else payload) := by
    simp only [renamePrime, sends, Process.substitute]
  have renamedResult := result_congruent contained fires lifts freshLifted (names := new :: others)
    (rest := rest.map (renamePrime old new)) (List.nodup_cons.mpr ⟨newOthers, othersNodup⟩)
    (by rw [List.toFinset_cons, othersEq])
    (by rw [map_sub_pair contained₀, ← restEq, Multiset.map_coe]) renamedSends denotes'
  have notFree : new ∉ (nuList others (.par (parList (rest.map Subtype.val)) (receive receiver.1 payload))).freeNames := by
    rw [freeNames_nuList]
    intro inside
    obtain ⟨present, -⟩ := Finset.mem_sdiff.mp inside
    simp only [Process.freeNames, Finset.mem_union] at present
    rcases present with inRest | inReceived
    · obtain ⟨process, processMem, there⟩ := mem_freeNames_parList.mp inRest
      obtain ⟨prime, primeMem, rfl⟩ := List.mem_map.mp processMem
      have member : prime ∈ molecule.body :=
        Multiset.mem_of_le (Multiset.sub_le_self _ _) (restEq ▸ Multiset.mem_coe.mpr primeMem)
      exact fresh (mem_bodyNames.mpr ⟨prime, member, there⟩)
    · rcases Finset.mem_insert.mp (freeNames_receive receives payload inReceived) with isPayload | fromReceiver
      · exact senderNew (by rw [sends, ← isPayload]; simp [Process.freeNames])
      · exact receiverNew fromReceiver
  refine ⟨process', process, denotes', denotes, renamedResult.trans (Congruent.trans ?_ original.symm)⟩
  refine Congruent.symm (Congruent.trans ⟨.alpha_nu old new _ notFree⟩ ?_)
  rw [substitute_nuList oldOthers newOthers, Process.substitute_par, substitute_parList, List.map_map, List.map_map]
  exact Congruent.nu new (nuList_congruent others
    (Congruent.par (Congruent.refl _) (receive_renamed receives old new payload).symm))

/-- **α-variants communicate alike**: a communication of a variant is matched by one of the original. -/
theorem internalSim_of_alpha {molecule renamed : Molecule} (variant : Alpha molecule renamed) :
    InternalSim renamed molecule := by
  induction variant with
  | refl => exact InternalSim.refl _
  | tail _ step holds => exact (internal_renameStep step).trans holds

/-! ## Liftings of a denotation -/

theorem lifts_parList : ∀ primes : List Prime, Lifts (parList (primes.map Subtype.val)) ∅ (primes : Multiset Prime)
  | [] => .nil
  | prime :: primes => by
    have both := Lifts.par (Lifts.guarded prime.2) (lifts_parList primes) (Finset.disjoint_empty_left _)
      (Finset.disjoint_empty_left _) (Finset.disjoint_empty_left _)
    rw [Finset.empty_union, Multiset.singleton_add, Multiset.cons_coe] at both
    exact both

theorem lifts_nuList_parList : ∀ (names : List Name) (primes : List Prime), names.Nodup →
    Lifts (nuList names (parList (primes.map Subtype.val))) names.toFinset (primes : Multiset Prime)
  | [], primes, _ => lifts_parList primes
  | name :: names, primes, nodup => by
    rw [List.nodup_cons] at nodup
    rw [List.toFinset_cons]
    refine .nu ?_ (fun inside => nodup.1 (List.mem_toFinset.mp inside)) (by simp [Process.freeNames])
    rw [substitute_self]
    exact lifts_nuList_parList names primes nodup.2

/-- **A molecule lifts what it denotes**, with its own restricted names. -/
theorem lifts_of_denotes {molecule : Molecule} {process : Process} (denotes : Denotes molecule process) :
    Lifts process molecule.scope molecule.body := by
  obtain ⟨names, primes, nodup, scopeEq, bodyEq, rfl⟩ := denotes
  rw [← scopeEq, ← bodyEq]
  exact lifts_nuList_parList names primes nodup

theorem lifts_parList_inv : ∀ (primes : List Prime) {scope : Finset Name} {body : Multiset Prime},
    Lifts (parList (primes.map Subtype.val)) scope body → scope = ∅ ∧ body = (primes : Multiset Prime)
  | [], _, _, lifts => lifts_nil_inv lifts
  | prime :: primes, _, _, lifts => by
    obtain ⟨headScope, restScope, headBody, restBody, headLifts, restLifts, -, -, -, rfl, rfl⟩ := lifts_par_inv lifts
    obtain ⟨rfl, rfl⟩ := lifts_guarded_inv prime.2 headLifts
    obtain ⟨rfl, rfl⟩ := lifts_parList_inv primes restLifts
    exact ⟨Finset.empty_union _, by rw [Multiset.singleton_add, Multiset.cons_coe]⟩

theorem substitute_parList_primes (primes : List Prime) (old new : Name) :
    (parList (primes.map Subtype.val)).substitute old new =
      parList ((primes.map (renamePrime old new)).map Subtype.val) := by
  rw [substitute_parList, List.map_map, List.map_map]
  rfl

/-- **A lifting of a denotation whose restricted names avoid the molecule's is an α-variant of the molecule**, beside
any other restricted names apart from both. -/
theorem alpha_of_lifts_denotation : ∀ (names : List Name) (primes : List Prime) (outer : Finset Name)
    {scope : Finset Name} {body : Multiset Prime}, names.Nodup → Disjoint outer names.toFinset →
    Disjoint outer scope → Disjoint scope names.toFinset →
    Lifts (nuList names (parList (primes.map Subtype.val))) scope body →
    Alpha ⟨outer ∪ names.toFinset, primes⟩ ⟨outer ∪ scope, body⟩
  | [], primes, outer, scope, body, _, _, _, _, lifts => by
    obtain ⟨rfl, rfl⟩ := lifts_parList_inv primes lifts
    exact .refl
  | name :: names, primes, outer, scope, body, nodup, outerNames, outerScope, scopeNames, lifts => by
    obtain ⟨new, rest, innerLifts, newOut, newFree, rfl⟩ := lifts_nu_inv lifts
    rw [List.nodup_cons] at nodup
    have newNotNames : new ∉ name :: names := fun inside =>
      Finset.disjoint_left.mp scopeNames (Finset.mem_insert_self _ _) (List.mem_toFinset.mpr inside)
    rw [List.mem_cons, not_or] at newNotNames
    rw [substitute_nuList nodup.1 newNotNames.2, substitute_parList_primes] at innerLifts
    have newOuter : new ∉ outer := fun inside => Finset.disjoint_left.mp outerScope inside (Finset.mem_insert_self _ _)
    have nameOuter : name ∉ outer := fun inside =>
      Finset.disjoint_left.mp outerNames inside (List.mem_toFinset.mpr List.mem_cons_self)
    have newBody : new ∉ (Molecule.mk (outer ∪ (name :: names).toFinset) (primes : Multiset Prime)).bodyNames := by
      intro inside
      obtain ⟨prime, primeMem, present⟩ := Molecule.mem_bodyNames.mp inside
      apply newFree
      simp only [Process.freeNames, freeNames_nuList, Finset.mem_sdiff, Finset.mem_singleton, List.mem_toFinset]
      exact ⟨⟨mem_freeNames_parList.mpr ⟨prime.1, List.mem_map_of_mem (Multiset.mem_coe.mp primeMem), present⟩,
        newNotNames.2⟩, newNotNames.1⟩
    have step : RenameStep ⟨outer ∪ (name :: names).toFinset, primes⟩
        ⟨insert new ((outer ∪ (name :: names).toFinset).erase name),
          (primes : Multiset Prime).map (renamePrime name new)⟩ := by
      refine .rename (by simp) ?_ newBody
      simp only [Finset.mem_union, List.mem_toFinset, List.mem_cons, not_or]
      exact ⟨newOuter, newNotNames.1, newNotNames.2⟩
    have holds := alpha_of_lifts_denotation names (primes.map (renamePrime name new)) (insert new outer)
      nodup.2 ?_ ?_ ?_ innerLifts
    · have middle : (Molecule.mk (insert new ((outer ∪ (name :: names).toFinset).erase name))
          ((primes : Multiset Prime).map (renamePrime name new))) =
          ⟨insert new outer ∪ names.toFinset, ((primes.map (renamePrime name new) : List Prime) : Multiset Prime)⟩ := by
        congr 1
        · ext other
          by_cases isName : other = name
          · subst isName
            simp [Ne.symm newNotNames.1, nameOuter, nodup.1]
          · simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_union, List.mem_toFinset, List.toFinset_cons,
              isName, ne_eq, not_false_eq_true, true_and, false_or]
            tauto
      have last : (Molecule.mk (outer ∪ insert new rest) body) = ⟨insert new outer ∪ rest, body⟩ := by
        rw [Finset.insert_union, Finset.union_insert]
      rw [last]
      refine .head step ?_
      rw [middle]
      exact holds
    · refine Finset.disjoint_insert_left.mpr ⟨fun inside => newNotNames.2 (List.mem_toFinset.mp inside), ?_⟩
      exact outerNames.mono_right fun other inside => by
        rw [List.toFinset_cons]; exact Finset.mem_insert_of_mem inside
    · exact Finset.disjoint_insert_left.mpr ⟨newOut, outerScope.mono_right (Finset.subset_insert _ _)⟩
    · exact (scopeNames.mono_left (Finset.subset_insert _ _)).mono_right fun other inside => by
        rw [List.toFinset_cons]; exact Finset.mem_insert_of_mem inside

/-! ## Merging a bag -/

/-- **A merge of a list of molecules**: α-variants of them, each apart from the merge of those after it, their scopes
and bodies joined. -/
inductive Merged : List Molecule → Molecule → Prop
  | nil : Merged [] ⟨∅, 0⟩
  | cons {molecule variant rest : Molecule} {molecules : List Molecule} :
      Alpha molecule variant → Merged molecules rest → Apart variant rest →
      Merged (molecule :: molecules) ⟨variant.scope ∪ rest.scope, variant.body + rest.body⟩

theorem Apart.symm {first second : Molecule} (apart : Apart first second) : Apart second first := ⟨apart.2, apart.1⟩

theorem apart_join_iff {molecule first second : Molecule} :
    Apart molecule ⟨first.scope ∪ second.scope, first.body + second.body⟩ ↔
      Apart molecule first ∧ Apart molecule second := by
  simp only [Apart, bodyNames_add, Finset.disjoint_union_left, Finset.disjoint_union_right]
  tauto

/-- **Every list of molecules has a merge**, with restricted names avoiding any finite set. -/
theorem merged_exists : ∀ (molecules : List Molecule) (avoid : Finset Name),
    ∃ merged, Merged molecules merged ∧ Disjoint merged.scope avoid
  | [], _ => ⟨_, .nil, Finset.disjoint_empty_left _⟩
  | molecule :: molecules, avoid => by
    obtain ⟨rest, restMerged, restAvoids⟩ := merged_exists molecules (avoid ∪ molecule.freeNames)
    obtain ⟨variant, variantAlpha, variantAvoids⟩ :=
      exists_alpha_avoiding _ molecule (avoid ∪ rest.scope ∪ rest.bodyNames) le_rfl
    refine ⟨_, .cons variantAlpha restMerged ⟨?_, ?_⟩, ?_⟩
    · exact variantAvoids.mono_right fun name inside => by
        simp only [Finset.mem_union] at inside ⊢; tauto
    · refine Finset.disjoint_left.mpr fun name restricted inside => ?_
      rcases Finset.mem_union.mp inside with bound | mentioned
      · exact Finset.disjoint_left.mp variantAvoids bound (by simp [restricted])
      · rcases Finset.mem_union.mp (alpha_freeNames variantAlpha mentioned) with free | bound
        · exact Finset.disjoint_left.mp restAvoids restricted (Finset.mem_union_right _ free)
        · exact Finset.disjoint_left.mp variantAvoids bound (by simp [restricted])
    · refine Finset.disjoint_union_left.mpr ⟨variantAvoids.mono_right fun name inside => ?_,
        restAvoids.mono_right Finset.subset_union_left⟩
      simp [inside]

/-- **A merge denotes the parallel composition of the molecules**, up to structural congruence. -/
theorem merged_denotes {molecules : List Molecule} {merged : Molecule} (merging : Merged molecules merged) :
    ∀ {processes : List Process}, List.Forall₂ Denotes molecules processes →
      ∃ process, Denotes merged process ∧ Congruent (parList processes) process := by
  induction merging with
  | nil =>
    intro processes denotes
    cases denotes
    exact ⟨.nil, ⟨[], [], List.nodup_nil, by simp, by simp, rfl⟩, Congruent.refl _⟩
  | cons variantAlpha _ apart holds =>
    intro processes denotes
    cases denotes with
    | cons headDenotes restDenotes =>
      obtain ⟨variantProcess, variantDenotes, variantCongruent⟩ := alpha_congruent variantAlpha headDenotes
      obtain ⟨restProcess, restProcessDenotes, restCongruent⟩ := holds restDenotes
      obtain ⟨process, denotes, congruent⟩ := merge_denotes apart variantDenotes restProcessDenotes
      exact ⟨process, denotes, (Congruent.par variantCongruent restCongruent).trans congruent⟩

/-- **A guarded process of a merge is in one molecule's variant**, the merge of the others beside it. -/
theorem merged_extract {molecules : List Molecule} {merged : Molecule} (merging : Merged molecules merged)
    {prime : Prime} (member : prime ∈ merged.body) :
    ∃ molecule variant rest others, molecules.Perm (molecule :: others) ∧ Alpha molecule variant ∧
      Merged others rest ∧ Apart variant rest ∧ prime ∈ variant.body ∧
      merged = ⟨variant.scope ∪ rest.scope, variant.body + rest.body⟩ := by
  induction merging with
  | nil => simp at member
  | @cons molecule variant rest molecules variantAlpha restMerged apart holds =>
    rcases Multiset.mem_add.mp member with inVariant | inRest
    · exact ⟨molecule, variant, rest, molecules, .refl _, variantAlpha, restMerged, apart, inVariant, rfl⟩
    · obtain ⟨found, foundVariant, rest', others, perm, foundAlpha, merged', apart', foundMem, rfl⟩ := holds inRest
      have parts := apart_join_iff.mp apart
      refine ⟨found, foundVariant, ⟨variant.scope ∪ rest'.scope, variant.body + rest'.body⟩, molecule :: others,
        (perm.cons molecule).trans (.swap _ _ _), foundAlpha, .cons variantAlpha merged' parts.2,
        apart_join_iff.mpr ⟨parts.1.symm, apart'⟩, foundMem, ?_⟩
      simp only [Molecule.mk.injEq]
      exact ⟨Finset.union_left_comm _ _ _, add_left_comm _ _ _⟩

theorem mem_right_of_pair_le {first second : Multiset Prime} {receiver sender : Prime}
    (contained : {receiver, sender} ≤ first + second) (receiverMem : receiver ∈ first)
    (notBoth : ¬ ({receiver, sender} : Multiset Prime) ≤ first) : sender ∈ second := by
  obtain ⟨rest, rfl⟩ := Multiset.exists_cons_of_mem receiverMem
  rw [Multiset.insert_eq_cons, Multiset.cons_add, Multiset.cons_le_cons_iff, Multiset.singleton_le] at contained
  rw [Multiset.insert_eq_cons, Multiset.cons_le_cons_iff, Multiset.singleton_le] at notBoth
  rcases Multiset.mem_add.mp contained with inRest | inSecond
  · exact absurd inRest notBoth
  · exact inSecond

theorem reacts_internal {molecules others : List Molecule} {molecule result : Molecule}
    (perm : molecules.Perm (molecule :: others)) (internal : Internal molecule result) :
    Reacts rules (bag (molecules : Multiset Molecule)) (bag (result ::ₘ (others : Multiset Molecule))) := by
  have bagEq : (molecules : Multiset Molecule) = molecule ::ₘ others := by
    rw [Multiset.coe_eq_coe.mpr perm, ← Multiset.cons_coe]
  refine Mettapedia.GSLT.BagSaturated.reacts_iff.mpr ⟨internalRule molecule result,
    Or.inl ⟨_, _, internal, rfl⟩, {molecule}, {result}, rfl, rfl, ?_, ?_⟩
  · rw [bagEq]; exact Multiset.singleton_le.mpr (Multiset.mem_cons_self _ _)
  · rw [bagEq, Multiset.sub_singleton, Multiset.erase_cons_head, Multiset.singleton_add]

theorem reacts_cross {molecules others : List Molecule} {first second result : Molecule}
    (perm : molecules.Perm (first :: second :: others)) (cross : Cross first second result) :
    Reacts rules (bag (molecules : Multiset Molecule)) (bag (result ::ₘ (others : Multiset Molecule))) := by
  have bagEq : (molecules : Multiset Molecule) = {first, second} + others := by
    rw [Multiset.coe_eq_coe.mpr perm, Multiset.insert_eq_cons, Multiset.cons_add, Multiset.singleton_add]
    rfl
  refine Mettapedia.GSLT.BagSaturated.reacts_iff.mpr ⟨crossRule first second result,
    Or.inr ⟨_, _, _, cross, rfl⟩, {first, second}, {result}, rfl, rfl, ?_, ?_⟩
  · rw [bagEq]; exact Multiset.le_add_right _ _
  · rw [bagEq, add_tsub_cancel_left, Multiset.singleton_add]

/-- What remains after a communication inside a molecule stays apart from a molecule apart from it. -/
theorem apart_after {molecule rest : Molecule} {receiver sender : Prime} {continuation : Process}
    {kept : Multiset Prime} {lifted : Finset Name} {components : Multiset Prime}
    (contained : {receiver, sender} ≤ molecule.body) (fires : Fires receiver sender continuation kept)
    (lifts : Lifts continuation lifted components) (apart : Apart molecule rest)
    (fresh : Disjoint lifted (rest.scope ∪ rest.bodyNames)) :
    Apart ⟨molecule.scope ∪ lifted, molecule.body - {receiver, sender} + kept + components⟩ rest := by
  have names := bodyNames_after contained fires lifts (molecule.scope ∪ lifted)
  refine ⟨Finset.disjoint_union_left.mpr ⟨apart.1, fresh⟩, ?_⟩
  refine Finset.disjoint_left.mpr fun name restricted inside => ?_
  rcases Finset.mem_union.mp inside with bound | mentioned
  · rcases Finset.mem_union.mp bound with inMolecule | inLifted
    · exact Finset.disjoint_left.mp apart.2 restricted (Finset.mem_union_left _ inMolecule)
    · exact Finset.disjoint_left.mp fresh inLifted (Finset.mem_union_left _ restricted)
  · rcases Finset.mem_union.mp (names mentioned) with inMolecule | inLifted
    · exact Finset.disjoint_left.mp apart.2 restricted (Finset.mem_union_right _ inMolecule)
    · exact Finset.disjoint_left.mp fresh inLifted (Finset.mem_union_left _ restricted)

/-- **A communication inside the merge of a bag is a reaction of the bag**: inside one molecule, or across two; what
the bag becomes denotes what the merge becomes. -/
theorem merged_internal_reacts {molecules : List Molecule} {merged result : Molecule}
    (merging : Merged molecules merged) (internal : Internal merged result) :
    ∃ next process process', Reacts rules (bag (molecules : Multiset Molecule)) (bag next) ∧
      BagDenotes next process ∧ Denotes result process' ∧ Congruent process' process := by
  cases internal with
  | @comm receiver sender continuation kept lifted components contained fires lifts fresh =>
  have receiverMem : receiver ∈ merged.body := Multiset.subset_of_le contained (by simp)
  obtain ⟨found, variant, rest, others, perm, variantAlpha, restMerged, apart, receiverIn, rfl⟩ :=
    merged_extract merging receiverMem
  have freshRest : Disjoint lifted (rest.scope ∪ rest.bodyNames) := by
    refine fresh.mono_right fun name inside => ?_
    rcases Finset.mem_union.mp inside with bound | mentioned
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ bound)
    · exact Finset.mem_union_right _ (mem_bodyNames_add.mpr (Or.inr mentioned))
  by_cases both : ({receiver, sender} : Multiset Prime) ≤ variant.body
  · have freshVariant : Disjoint lifted (variant.scope ∪ variant.bodyNames) := by
      refine fresh.mono_right fun name inside => ?_
      rcases Finset.mem_union.mp inside with bound | mentioned
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ bound)
      · exact Finset.mem_union_right _ (mem_bodyNames_add.mpr (Or.inl mentioned))
    have inner : Internal variant ⟨variant.scope ∪ lifted, variant.body - {receiver, sender} + kept + components⟩ :=
      .comm both fires lifts freshVariant
    obtain ⟨result', internal', innerProcess, process', innerDenotes, denotes', congruent⟩ :=
      internalSim_of_alpha variantAlpha _ inner
    obtain ⟨restProcesses, restDenotes⟩ := forall₂_denotes_exists others
    obtain ⟨restProcess, restProcessDenotes, restCongruent⟩ := merged_denotes restMerged restDenotes
    obtain ⟨joined, joinedDenotes, joinedCongruent⟩ :=
      merge_denotes (apart_after both fires lifts apart freshRest) innerDenotes restProcessDenotes
    refine ⟨result' ::ₘ others, parList (process' :: restProcesses), joined, reacts_internal perm internal',
      ⟨result' :: others, _, rfl, .cons denotes' restDenotes, rfl⟩, ?_,
      joinedCongruent.symm.trans (Congruent.par congruent restCongruent.symm)⟩
    convert joinedDenotes using 1
    simp only [Molecule.mk.injEq]
    constructor
    · exact Finset.union_right_comm _ _ _
    · rw [← tsub_add_eq_add_tsub both]
      ac_rfl
  · have senderIn := mem_right_of_pair_le contained receiverIn both
    obtain ⟨second, secondVariant, rest₂, others₂, perm₂, secondAlpha, merged₂, apart₂, senderIn', rfl⟩ :=
      merged_extract restMerged senderIn
    have parts := apart_join_iff.mp apart
    have freshCross : Disjoint lifted (variant.scope ∪ variant.bodyNames ∪ secondVariant.scope ∪
        secondVariant.bodyNames) := by
      refine fresh.mono_right fun name inside => ?_
      simp only [Finset.mem_union] at inside ⊢
      rcases inside with ((bound | mentioned) | bound') | mentioned'
      · exact Or.inl (Or.inl bound)
      · exact Or.inr (mem_bodyNames_add.mpr (Or.inl mentioned))
      · exact Or.inl (Or.inr (Or.inl bound'))
      · exact Or.inr (mem_bodyNames_add.mpr (Or.inr (mem_bodyNames_add.mpr (Or.inl mentioned'))))
    have cross := Cross.receive variantAlpha secondAlpha parts.1 receiverIn senderIn' fires lifts freshCross
    have joinedContained : ({receiver, sender} : Multiset Prime) ≤ variant.body + secondVariant.body := by
      rw [Multiset.insert_eq_cons, ← Multiset.singleton_add]
      exact add_le_add (Multiset.singleton_le.mpr receiverIn) (Multiset.singleton_le.mpr senderIn')
    have freshRest₂ : Disjoint lifted (rest₂.scope ∪ rest₂.bodyNames) := by
      refine freshRest.mono_right fun name inside => ?_
      rcases Finset.mem_union.mp inside with bound | mentioned
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ bound)
      · exact Finset.mem_union_right _ (mem_bodyNames_add.mpr (Or.inr mentioned))
    have pairApart : Apart ⟨variant.scope ∪ secondVariant.scope, variant.body + secondVariant.body⟩ rest₂ :=
      (apart_join_iff.mpr ⟨parts.2.symm, apart₂.symm⟩).symm
    have crossApart := apart_after (molecule := ⟨variant.scope ∪ secondVariant.scope,
      variant.body + secondVariant.body⟩) joinedContained fires lifts pairApart freshRest₂
    rw [pair_sub_add receiverIn senderIn'] at crossApart
    obtain ⟨crossProcess, crossDenotes⟩ := denotes_exists
      ⟨variant.scope ∪ secondVariant.scope ∪ lifted,
        (variant.body - {receiver}) + (secondVariant.body - {sender}) + kept + components⟩
    obtain ⟨restProcesses, restDenotes⟩ := forall₂_denotes_exists others₂
    obtain ⟨restProcess, restProcessDenotes, restCongruent⟩ := merged_denotes merged₂ restDenotes
    obtain ⟨joined, joinedDenotes, joinedCongruent⟩ := merge_denotes crossApart crossDenotes restProcessDenotes
    refine ⟨_ ::ₘ others₂, parList (crossProcess :: restProcesses), joined,
      reacts_cross (perm.trans (perm₂.cons found)) cross,
      ⟨_ :: others₂, _, rfl, .cons crossDenotes restDenotes, rfl⟩, ?_,
      joinedCongruent.symm.trans (Congruent.par (Congruent.refl _) restCongruent.symm)⟩
    convert joinedDenotes using 1
    simp only [Molecule.mk.injEq]
    constructor
    · ext name
      simp only [Finset.mem_union]
      tauto
    · rw [← add_assoc, ← tsub_add_eq_add_tsub joinedContained, pair_sub_add receiverIn senderIn']
      ac_rfl

/-! ## Completeness for every bag -/

/-- **Every reduction of what a bag denotes is a reaction of the bag**, up to structural congruence. -/
theorem bag_reacts_of_reduces {agent : Multiset Molecule} {source target : Process}
    (denotes : BagDenotes agent source) (step : source ⇝ target) :
    ∃ next process, Reacts rules (bag agent) (bag next) ∧ BagDenotes next process ∧ Congruent target process := by
  obtain ⟨molecules, processes, rfl, moleculesDenote, rfl⟩ := denotes
  obtain ⟨merged, merging, -⟩ := merged_exists molecules ∅
  obtain ⟨mergedProcess, mergedDenotes, mergedCongruent⟩ := merged_denotes merging moleculesDenote
  obtain ⟨molecule, receiver, sender, continuation, kept, lifted, components, contained, fires, lifts, fresh,
    scopeAvoids, -, ⟨process, denotes, congruent⟩, ⟨process', denotes', congruent'⟩⟩ :=
    reduces_realized step [] merged.scope
  obtain ⟨equivalence⟩ : Congruent process mergedProcess := congruent.symm.trans mergedCongruent
  obtain ⟨scope', body', lifts', trimmed, bodies, names⟩ :=
    (liftsRel_of_congruent equivalence []).1 merged.scope (lifts_of_denotes denotes)
  have equivalent : MolEquiv molecule ⟨scope', body'⟩ := by
    have toTrim := molEquiv_trim _ molecule le_rfl
    have fromTrim := molEquiv_trim _ (Molecule.mk scope' body') le_rfl
    have middle : MolEquiv molecule.trim ⟨(Molecule.mk scope' body').trim.scope, body'⟩ := by
      rw [← trimmed]
      exact bodies.molEquiv _
    exact .trans _ _ _ toTrim (.trans _ _ _ middle (.symm _ _ fromTrim))
  have scopeApart : Disjoint scope' merged.scope := Finset.disjoint_left.mpr fun name inside restricted =>
    (names name inside).elim (fun old => Finset.disjoint_left.mp scopeAvoids old restricted)
      (fun outside => outside restricted)
  obtain ⟨mergedNames, mergedPrimes, nodup, scopeEq, bodyEq, rfl⟩ := mergedDenotes
  have variant := alpha_of_lifts_denotation mergedNames mergedPrimes ∅ nodup (Finset.disjoint_empty_left _)
    (Finset.disjoint_empty_left _) (by rw [scopeEq]; exact scopeApart) lifts'
  rw [Finset.empty_union, Finset.empty_union, scopeEq, bodyEq] at variant
  obtain ⟨lifting, liftingInternal, process₁, liftingProcess, denotes₁, liftingDenotes, congruent₁⟩ :=
    (internalSim_of_equiv equivalent).1 _ (.comm contained fires lifts fresh)
  obtain ⟨result, resultInternal, liftingProcess', resultProcess, liftingDenotes', resultDenotes, congruent₂⟩ :=
    internalSim_of_alpha variant lifting liftingInternal
  obtain ⟨next, nextProcess, resultProcess', reacts, nextDenotes, resultDenotes', congruent₃⟩ :=
    merged_internal_reacts merging resultInternal
  exact ⟨next, nextProcess, reacts, nextDenotes, congruent'.trans ((denotes_congruent denotes' denotes₁).trans
    (congruent₁.trans ((denotes_congruent liftingDenotes liftingDenotes').trans (congruent₂.trans
      ((denotes_congruent resultDenotes resultDenotes').trans congruent₃)))))⟩

/-! ## Representation independence -/

/-- **Two bags representing congruent processes.** -/
def Represent (first second : Multiset Molecule) : Prop :=
  ∃ firstProcess secondProcess, BagDenotes first firstProcess ∧ BagDenotes second secondProcess ∧
    Congruent firstProcess secondProcess

theorem Represent.symm {first second : Multiset Molecule} (related : Represent first second) :
    Represent second first := by
  obtain ⟨firstProcess, secondProcess, firstDenotes, secondDenotes, congruent⟩ := related
  exact ⟨secondProcess, firstProcess, secondDenotes, firstDenotes, congruent.symm⟩

theorem bagDenotes_add {first second : Multiset Molecule} {firstProcess secondProcess : Process}
    (firstDenotes : BagDenotes first firstProcess) (secondDenotes : BagDenotes second secondProcess) :
    ∃ process, BagDenotes (first + second) process ∧ Congruent process (firstProcess ||| secondProcess) := by
  obtain ⟨firstMolecules, firstProcesses, rfl, firstForall, rfl⟩ := firstDenotes
  obtain ⟨secondMolecules, secondProcesses, rfl, secondForall, rfl⟩ := secondDenotes
  exact ⟨_, ⟨firstMolecules ++ secondMolecules, firstProcesses ++ secondProcesses, Multiset.coe_add _ _,
    List.rel_append firstForall secondForall, rfl⟩, parList_append _ _⟩

/-- **Contexts keep representations related.** -/
theorem Represent.add {first second : Multiset Molecule} (related : Represent first second)
    (context : Multiset Molecule) : Represent (first + context) (second + context) := by
  obtain ⟨firstProcess, secondProcess, firstDenotes, secondDenotes, congruent⟩ := related
  obtain ⟨contextProcess, contextDenotes⟩ := bagDenotes_exists context
  obtain ⟨firstJoined, firstJoinedDenotes, firstCongruent⟩ := bagDenotes_add firstDenotes contextDenotes
  obtain ⟨secondJoined, secondJoinedDenotes, secondCongruent⟩ := bagDenotes_add secondDenotes contextDenotes
  exact ⟨firstJoined, secondJoined, firstJoinedDenotes, secondJoinedDenotes,
    firstCongruent.trans ((Congruent.par congruent (Congruent.refl _)).trans secondCongruent.symm)⟩

/-- **A reaction of a bag is matched by a bag representing the same process**, to bags representing congruent
processes. -/
theorem Represent.forth {first second next : Multiset Molecule} (related : Represent first second)
    (reacts : Reacts rules (bag first) (bag next)) :
    ∃ matched, Reacts rules (bag second) (bag matched) ∧ Represent next matched := by
  obtain ⟨firstProcess, secondProcess, firstDenotes, secondDenotes, congruent⟩ := related
  obtain ⟨nextProcess, nextDenotes, step⟩ := reacts_reduces reacts firstDenotes
  obtain ⟨step'⟩ := reduces_of_congruent congruent.symm step (Congruent.refl _)
  obtain ⟨matched, matchedProcess, matchedReacts, matchedDenotes, matchedCongruent⟩ :=
    bag_reacts_of_reduces secondDenotes step'
  exact ⟨matched, matchedReacts, nextProcess, matchedProcess, nextDenotes, matchedDenotes, matchedCongruent⟩

/-- **Representing congruent processes is a saturated bisimulation.** -/
theorem isSaturatedIn_represent (admissible : Multiset Molecule → Prop) :
    IsSaturatedIn rules admissible Represent := by
  intro first second related context _
  rw [Mettapedia.GSLT.BagRelativePushout.bag_comp, Mettapedia.GSLT.BagRelativePushout.bag_comp]
  constructor
  · intro next reacts
    exact (related.add context).forth reacts
  · intro next reacts
    obtain ⟨matched, matchedReacts, matchedRelated⟩ := (related.add context).symm.forth reacts
    exact ⟨matched, matchedReacts, matchedRelated.symm⟩

/-- **Representation independence**: bags of molecules denoting structurally congruent processes are saturated
bisimilar. -/
theorem saturatedBisimilar_of_congruent {first second : Multiset Molecule} {firstProcess secondProcess : Process}
    (firstDenotes : BagDenotes first firstProcess) (secondDenotes : BagDenotes second secondProcess)
    (congruent : Congruent firstProcess secondProcess) :
    SaturatedBisimilarIn rules (fun _ => True) first second :=
  ⟨Represent, isSaturatedIn_represent _, firstProcess, secondProcess, firstDenotes, secondDenotes, congruent⟩

/-! ## π's own equivalence -/

/-- **Every process is denoted by a bag**, up to structural congruence: its lifting, as one molecule. -/
theorem bagDenotes_of_process (process : Process) :
    ∃ agent denoted, BagDenotes agent denoted ∧ Congruent denoted process := by
  obtain ⟨scope, body, lifts, -⟩ := lifts_exists _ process le_rfl ∅
  obtain ⟨names, primes, nodup, scopeEq, bodyEq, congruent⟩ := lifts_congruent lifts
  exact ⟨{⟨scope, body⟩}, parList [nuList names (parList (primes.map Subtype.val))],
    ⟨[⟨scope, body⟩], _, rfl, .cons ⟨names, primes, nodup, scopeEq, bodyEq, rfl⟩ .nil, rfl⟩,
    (Congruent.nilRight _).trans congruent.symm⟩

/-- **The molecules' saturated bisimilarity is π's saturated reduction bisimilarity**, read through what the bags
denote. -/
theorem saturatedBisimilarIn_iff_reduction {first second : Multiset Molecule} {firstProcess secondProcess : Process}
    (firstDenotes : BagDenotes first firstProcess) (secondDenotes : BagDenotes second secondProcess) :
    SaturatedBisimilarIn rules (fun _ => True) first second ↔ SaturatedReductionBisimilar firstProcess secondProcess := by
  constructor
  · rintro ⟨relation, saturated, related⟩
    refine ⟨fun left right => ∃ agent agent', (∃ denoted, BagDenotes agent denoted ∧ Congruent denoted left) ∧
      (∃ denoted, BagDenotes agent' denoted ∧ Congruent denoted right) ∧ relation agent agent', ?_,
      first, second, ⟨firstProcess, firstDenotes, Congruent.refl _⟩, ⟨secondProcess, secondDenotes, Congruent.refl _⟩,
      related⟩
    rintro left right ⟨agent, agent', ⟨leftProcess, leftDenotes, leftCongruent⟩,
      ⟨rightProcess, rightDenotes, rightCongruent⟩, agentsRelated⟩ context
    obtain ⟨contextAgent, contextProcess, contextDenotes, contextCongruent⟩ := bagDenotes_of_process context
    obtain ⟨leftJoined, leftJoinedDenotes, leftJoinedCongruent⟩ := bagDenotes_add leftDenotes contextDenotes
    obtain ⟨rightJoined, rightJoinedDenotes, rightJoinedCongruent⟩ := bagDenotes_add rightDenotes contextDenotes
    have leftSame : Congruent (left ||| context) leftJoined :=
      (leftJoinedCongruent.trans (Congruent.par leftCongruent contextCongruent)).symm
    have rightSame : Congruent (right ||| context) rightJoined :=
      (rightJoinedCongruent.trans (Congruent.par rightCongruent contextCongruent)).symm
    obtain ⟨forth, back⟩ := saturated agentsRelated contextAgent trivial
    simp only [Mettapedia.GSLT.BagRelativePushout.bag_comp] at forth back
    constructor
    · intro next step
      obtain ⟨step'⟩ := reduces_of_congruent leftSame.symm step (Congruent.refl _)
      obtain ⟨reached, reachedProcess, reacts, reachedDenotes, reachedCongruent⟩ :=
        bag_reacts_of_reduces leftJoinedDenotes step'
      obtain ⟨matched, matchedReacts, matchedRelated⟩ := forth reached reacts
      obtain ⟨matchedProcess, matchedDenotes, matchedStep⟩ := reacts_reduces matchedReacts rightJoinedDenotes
      exact ⟨matchedProcess, reduces_of_congruent rightSame matchedStep (Congruent.refl _), reached, matched,
        ⟨reachedProcess, reachedDenotes, reachedCongruent.symm⟩, ⟨matchedProcess, matchedDenotes, Congruent.refl _⟩,
        matchedRelated⟩
    · intro next step
      obtain ⟨step'⟩ := reduces_of_congruent rightSame.symm step (Congruent.refl _)
      obtain ⟨reached, reachedProcess, reacts, reachedDenotes, reachedCongruent⟩ :=
        bag_reacts_of_reduces rightJoinedDenotes step'
      obtain ⟨matched, matchedReacts, matchedRelated⟩ := back reached reacts
      obtain ⟨matchedProcess, matchedDenotes, matchedStep⟩ := reacts_reduces matchedReacts leftJoinedDenotes
      exact ⟨matchedProcess, reduces_of_congruent leftSame matchedStep (Congruent.refl _), matched, reached,
        ⟨matchedProcess, matchedDenotes, Congruent.refl _⟩, ⟨reachedProcess, reachedDenotes, reachedCongruent.symm⟩,
        matchedRelated⟩
  · rintro ⟨relation, saturated, related⟩
    refine ⟨fun agent agent' => ∃ process process', (∃ denoted, BagDenotes agent denoted ∧ Congruent denoted process) ∧
      (∃ denoted, BagDenotes agent' denoted ∧ Congruent denoted process') ∧ relation process process', ?_,
      firstProcess, secondProcess, ⟨firstProcess, firstDenotes, Congruent.refl _⟩,
      ⟨secondProcess, secondDenotes, Congruent.refl _⟩, related⟩
    rintro agent agent' ⟨process, process', ⟨denoted, denotes, congruent⟩, ⟨denoted', denotes', congruent'⟩,
      processesRelated⟩ context -
    obtain ⟨contextProcess, contextDenotes⟩ := bagDenotes_exists context
    obtain ⟨joined, joinedDenotes, joinedCongruent⟩ := bagDenotes_add denotes contextDenotes
    obtain ⟨joined', joinedDenotes', joinedCongruent'⟩ := bagDenotes_add denotes' contextDenotes
    have same : Congruent joined (process ||| contextProcess) :=
      joinedCongruent.trans (Congruent.par congruent (Congruent.refl _))
    have same' : Congruent joined' (process' ||| contextProcess) :=
      joinedCongruent'.trans (Congruent.par congruent' (Congruent.refl _))
    obtain ⟨forth, back⟩ := saturated processesRelated contextProcess
    simp only [Mettapedia.GSLT.BagRelativePushout.bag_comp]
    constructor
    · intro next reacts
      obtain ⟨nextProcess, nextDenotes, step⟩ := reacts_reduces reacts joinedDenotes
      obtain ⟨matchedProcess, matchedStep, matchedRelated⟩ :=
        forth nextProcess (reduces_of_congruent same.symm step (Congruent.refl _))
      obtain ⟨step'⟩ := reduces_of_congruent same' matchedStep (Congruent.refl _)
      obtain ⟨matched, matchedDenoted, matchedReacts, matchedDenotes, matchedCongruent⟩ :=
        bag_reacts_of_reduces joinedDenotes' step'
      exact ⟨matched, matchedReacts, nextProcess, matchedProcess, ⟨nextProcess, nextDenotes, Congruent.refl _⟩,
        ⟨matchedDenoted, matchedDenotes, matchedCongruent.symm⟩, matchedRelated⟩
    · intro next reacts
      obtain ⟨nextProcess, nextDenotes, step⟩ := reacts_reduces reacts joinedDenotes'
      obtain ⟨matchedProcess, matchedStep, matchedRelated⟩ :=
        back nextProcess (reduces_of_congruent same'.symm step (Congruent.refl _))
      obtain ⟨step'⟩ := reduces_of_congruent same matchedStep (Congruent.refl _)
      obtain ⟨matched, matchedDenoted, matchedReacts, matchedDenotes, matchedCongruent⟩ :=
        bag_reacts_of_reduces joinedDenotes step'
      exact ⟨matched, matchedReacts, matchedProcess, nextProcess, ⟨matchedDenoted, matchedDenotes, matchedCongruent.symm⟩,
        ⟨nextProcess, nextDenotes, Congruent.refl _⟩, matchedRelated⟩

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.Pi.LeastPartners
