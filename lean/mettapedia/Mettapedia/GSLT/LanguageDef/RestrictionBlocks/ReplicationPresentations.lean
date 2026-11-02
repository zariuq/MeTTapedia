import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationMolecular

/-!
# Presentations of a state of a calculus with replication

A step of a process is a reaction of an unfolding of its canonical form within the calculus's arity times the
ceiling read off the canonical form (`replication_reaction`). The presentations of a state list fewer unfoldings
when they can:

- **Copies of one-component replicated components** (`unfoldsWithin_copies`): when the replicated components of a
  block copy one component each, the block beside copies of their arguments, read again, is an unfolding within as
  many unfoldings as copies; conversely every unfolding is one (`unfolds_atomic`).
- **Compression** (`compress_flat`): for such a block, a reaction of any unfolding is a reaction of an unfolding
  within the arity: the reaction takes at most one copy per part, and the copies it does not take are absorbed, in
  what it leaves, by their replicated components, which are not parts.
- **A step of a process is matched by a step of a presentation of its canonical form** (`replication_presented`):
  within the arity when the canonical form's replicated components copy molecules (`compress_molecular`), within the
  arity times the ceiling otherwise.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationEquiv)
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (engineBasePremises)
open Mettapedia.GSLT.LanguageDef.WellSorted

variable {block : ReplicationBlock}

/-! ## Copies of one-component replicated components -/

section Copies

variable (fresh : block.replicate ∉ block.emptyUnits) (restrictFresh : block.replicate ≠ block.restrict)

include fresh restrictFresh in
/-- **Copies of one-component replicated components are an unfolding**: a block beside copies of arguments of its
replicated components, each argument one component read again, is an unfolding of the block within as many
unfoldings as copies. -/
theorem unfoldsWithin_copies : ∀ (pairs : List (Pattern × Pattern)) {form : Prenex},
    (∀ pair ∈ pairs, ∃ argument, pair.1 = .apply block.replicate [argument] ∧ pair.1 ∈ form.components ∧
      decompose block.toBlock argument = Prenex.atom argument ∧ pair.2 = recanon block argument) →
    UnfoldsWithin block pairs.length form ⟨form.count, form.components ++ pairs.map Prod.snd⟩
  | [], ⟨count, components⟩, _ => by simpa using UnfoldsWithin.refl (block := block) 0 ⟨count, components⟩
  | (server, copy) :: pairs, ⟨count, components⟩, facts => by
      obtain ⟨argument, serverIs, inForm, atomic, copyIs⟩ := facts (server, copy) List.mem_cons_self
      simp only at serverIs inForm copyIs
      subst serverIs copyIs
      have copied : (Prenex.mk count components).unfoldWith (normal block (decompose block.toBlock argument)) =
          ⟨count, components ++ [recanon block argument]⟩ := by
        rw [atomic, normal_atom fresh restrictFresh atomic, unfoldWith_atom]
      have rest := unfoldsWithin_copies pairs (form := ⟨count, components ++ [recanon block argument]⟩)
        fun pair member => by
          obtain ⟨argument', serverIs', inForm', atomic', copyIs'⟩ := facts pair (List.mem_cons_of_mem _ member)
          exact ⟨argument', serverIs', List.mem_append_left _ inForm', atomic', copyIs'⟩
      simp only [List.append_assoc, List.singleton_append] at rest
      simp only [List.length_cons, List.map_cons]
      exact .step inForm (by rw [copied]; exact rest)

end Copies

/-! ## Compression -/

section Compress

variable {language : LanguageDef} [laws : ReplicationLanguage language block]
variable {step : Pattern → Pattern → Prop}

include laws in
/-- **The parts of a reaction of an unfolding, between the block and the copies**: when the replicated components of a
block copy one component each, none replicated, the parts of a reaction of an unfolding of the block are some of the
block's components beside copies of arguments of its replicated components, and those replicated components stay
beside the rest of the block. What the reaction leaves beside the rest of the block reads, under the block's
restrictions, as what it leaves beside the rest of the unfolding: the copies it does not take are absorbed by their
replicated components. -/
theorem compress_parts (reactions : ReplicationReactions language block step) {free : FreeTypeContext}
    {bound : List TypeExpr} (context : BaseContext free bound) {depth : Nat} {form unfolded : Prenex}
    (flat : ∀ component ∈ form.components, ∀ argument, component = .apply block.replicate [argument] →
      decompose block.toBlock argument = Prenex.atom argument ∧ isReplicated block argument = false)
    (unfolds : UnfoldsWithin block depth form unfolded) {redex : reactions.Redex} {restU : List Pattern}
    (split : unfolded.components.Perm (reactions.parts redex ++ restU))
    (plain : ∀ part ∈ reactions.parts redex, isReplicated block part = false)
    (members : Members language block.toBlock free (List.replicate unfolded.count (TypeExpr.base block.name) ++ bound)
      unfolded.components) :
    unfolded.count = form.count ∧
      ∃ (taken rest : List Pattern) (chosen : List (Pattern × Pattern)),
        form.components.Perm (taken ++ rest) ∧
        (reactions.parts redex).Perm (taken ++ chosen.map Prod.snd) ∧
        (∀ pair ∈ chosen, ∃ argument, pair.1 = .apply block.replicate [argument] ∧ pair.1 ∈ rest ∧
          decompose block.toBlock argument = Prenex.atom argument ∧ pair.2 = recanon block argument) ∧
        (∀ component ∈ form.components ++ chosen.map Prod.snd, component ∈ unfolded.components) ∧
        EquationEquiv (engineBasePremises RelationEnv.empty) language
          (Prenex.restricts block.toBlock form.count (.collection .hashBag (reactions.result redex ++ rest) none))
          (Prenex.restricts block.toBlock unfolded.count
            (.collection .hashBag (reactions.result redex ++ restU) none)) := by
  have fresh := replicate_not_emptyUnit (block := block) (language := language)
  have restrictFresh := replicate_ne_restrict (block := block) (language := language)
  obtain ⟨pairs, unfoldedIs, pairsFacts⟩ := unfolds_atomic fresh restrictFresh unfolds flat
  subst unfoldedIs
  simp only at split members ⊢
  -- the parts taken from the block and from the copies
  obtain ⟨tags, takenFirst, takenSecond, restFirst, restSecond, takenIs, firstPerm, secondPerm, restPerm⟩ :=
    perm_append_split split
  obtain ⟨chosen, others, pairsPerm, chosenMap⟩ := exists_perm_map Prod.snd
    (((List.sublist_append_left takenSecond restSecond).subperm).trans secondPerm.symm.subperm)
  have othersMap : (others.map Prod.snd).Perm restSecond := by
    have whole : (pairs.map Prod.snd).Perm (takenSecond ++ others.map Prod.snd) := by
      rw [← chosenMap, ← List.map_append]
      exact pairsPerm.map _
    exact (List.perm_append_left_iff takenSecond).mp (whole.symm.trans secondPerm)
  have partsPerm : (reactions.parts redex).Perm (takenFirst ++ takenSecond) := by
    rw [takenIs]
    exact interleave_perm tags takenFirst takenSecond
  have pairFacts : ∀ pair ∈ pairs, ∃ argument, pair.1 = .apply block.replicate [argument] ∧
      pair.1 ∈ form.components ∧ decompose block.toBlock argument = Prenex.atom argument ∧
        pair.2 = recanon block argument := by
    intro pair member
    obtain ⟨argument, serverIs, inForm, copyIs⟩ := pairsFacts pair member
    exact ⟨argument, serverIs, inForm, (flat _ inForm argument serverIs).1, copyIs⟩
  -- a replicated component is not a part, so it stays beside what the reaction leaves
  have serverKept : ∀ pair ∈ pairs, pair.1 ∈ restFirst := by
    intro pair member
    obtain ⟨argument, serverIs, inForm, -⟩ := pairsFacts pair member
    rcases List.mem_append.mp (firstPerm.subset inForm) with taken | kept
    · have replicated : isReplicated block pair.1 = true := by
        rw [serverIs]
        simp [isReplicated]
      rw [plain _ (partsPerm.symm.subset (List.mem_append_left _ taken))] at replicated
      cases replicated
    · exact kept
  have partsMembers : Members language block.toBlock free (List.replicate form.count (TypeExpr.base block.name) ++ bound)
      (reactions.parts redex) := fun part member => members part (split.symm.subset (List.mem_append_left _ member))
  have restUMembers : Members language block.toBlock free (List.replicate form.count (TypeExpr.base block.name) ++ bound)
      restU := fun element member => members element (split.symm.subset (List.mem_append_right _ member))
  refine ⟨trivial, takenFirst, restFirst, chosen, firstPerm, by rw [chosenMap]; exact partsPerm, fun pair member => ?_,
    fun component member => ?_, ?_⟩
  -- the copies the reaction takes, and their replicated components
  · have inPairs := pairsPerm.symm.subset (List.mem_append_left _ member)
    obtain ⟨argument, serverIs, -, atomic, copyIs⟩ := pairFacts pair inPairs
    exact ⟨argument, serverIs, serverKept pair inPairs, atomic, copyIs⟩
  · rw [chosenMap] at member
    rcases List.mem_append.mp member with inForm | inTaken
    · exact List.mem_append_left _ inForm
    · exact List.mem_append_right _ (secondPerm.symm.subset (List.mem_append_left _ inTaken))
  -- the copies the reaction does not take are absorbed in what it leaves
  · have leftMembers : Members language block.toBlock free
        (List.replicate form.count (TypeExpr.base block.name) ++ bound) (reactions.result redex ++ restFirst) := by
      intro element member
      rcases List.mem_append.mp member with inResult | inRest
      · exact reactions.result_members redex partsMembers element inResult
      · exact restUMembers element (restPerm.symm.subset (List.mem_append_left _ inRest))
    have absorbing := unfoldsWithin_copies fresh restrictFresh others
      (form := ⟨form.count, reactions.result redex ++ restFirst⟩) fun pair member => by
        have inPairs := pairsPerm.symm.subset (List.mem_append_right _ member)
        obtain ⟨argument, serverIs, -, atomic, copyIs⟩ := pairFacts pair inPairs
        exact ⟨argument, serverIs, List.mem_append_right _ (serverKept pair inPairs), atomic, copyIs⟩
    have unfoldedMembers := absorbing.members context leftMembers
    have absorbed := absorbing.equivalent context leftMembers
    simp only [Prenex.toPattern] at absorbed unfoldedMembers
    have reordered : ((reactions.result redex ++ restFirst) ++ others.map Prod.snd).Perm
        (reactions.result redex ++ restU) := by
      rw [List.append_assoc]
      exact List.Perm.append_left _ ((othersMap.append_left restFirst).trans restPerm.symm)
    exact Relation.EqvGen.trans _ _ _
      (restricts_equation (block := block.toBlock) form.count (bag_body_equivalent leftMembers).toEquationEquiv)
      (Relation.EqvGen.trans _ _ _ absorbed
        (restricts_equation (block := block.toBlock) form.count (Relation.EqvGen.trans _ _ _
          (Relation.EqvGen.symm _ _ (bag_body_equivalent unfoldedMembers).toEquationEquiv)
          (bag_perm_equivalent (block := block) unfoldedMembers reordered).toEquationEquiv)))

include laws in
/-- **Compressing an unfolding to the copies a reaction takes**: when the replicated components of a block copy one
component each, none replicated, a reaction of an unfolding of the block is a reaction of an unfolding within the
arity, with the block's restrictions, leaving what reads as the first reaction leaves: the copies it does not take are
absorbed by their replicated components, which are not parts. -/
theorem compress_flat (reactions : ReplicationReactions language block step) {free : FreeTypeContext}
    {bound : List TypeExpr} (context : BaseContext free bound) {depth : Nat} {form unfolded : Prenex}
    (flat : ∀ component ∈ form.components, ∀ argument, component = .apply block.replicate [argument] →
      decompose block.toBlock argument = Prenex.atom argument ∧ isReplicated block argument = false)
    (unfolds : UnfoldsWithin block depth form unfolded) {redex : reactions.Redex} {restU : List Pattern}
    (split : unfolded.components.Perm (reactions.parts redex ++ restU))
    (plain : ∀ part ∈ reactions.parts redex, isReplicated block part = false)
    (members : Members language block.toBlock free (List.replicate unfolded.count (TypeExpr.base block.name) ++ bound)
      unfolded.components)
    (objects : ∀ component ∈ unfolded.components, isObjectPattern component = true) :
    ∃ compressed, UnfoldsWithin block reactions.arity form compressed ∧ compressed.count = unfolded.count ∧
      ∃ restC, compressed.components.Perm (reactions.parts redex ++ restC) ∧
        Members language block.toBlock free (List.replicate compressed.count (TypeExpr.base block.name) ++ bound)
          compressed.components ∧
        (∀ component ∈ compressed.components, isObjectPattern component = true) ∧
        EquationEquiv (engineBasePremises RelationEnv.empty) language
          (Prenex.restricts block.toBlock compressed.count
            (.collection .hashBag (reactions.result redex ++ restC) none))
          (Prenex.restricts block.toBlock unfolded.count
            (.collection .hashBag (reactions.result redex ++ restU) none)) := by
  have fresh := replicate_not_emptyUnit (block := block) (language := language)
  have restrictFresh := replicate_ne_restrict (block := block) (language := language)
  obtain ⟨sameCount, taken, rest, chosen, formPerm, partsPerm, chosenFacts, inUnfolded, absorbed⟩ :=
    compress_parts reactions context flat unfolds split plain members
  rw [sameCount] at members
  refine ⟨⟨form.count, form.components ++ chosen.map Prod.snd⟩, ?_, sameCount.symm, rest, ?_,
    fun component member => members component (inUnfolded component member),
    fun component member => objects component (inUnfolded component member), absorbed⟩
  -- within the arity
  · have within := unfoldsWithin_copies fresh restrictFresh chosen (form := form) fun pair member => by
      obtain ⟨argument, serverIs, kept, atomic, copyIs⟩ := chosenFacts pair member
      exact ⟨argument, serverIs, formPerm.symm.subset (List.mem_append_right _ kept), atomic, copyIs⟩
    refine within.mono ((?_ : chosen.length ≤ (reactions.parts redex).length).trans (reactions.arity_le redex))
    rw [partsPerm.length_eq, List.length_append, List.length_map]
    omega
  -- the parts beside the rest
  · have middle : ((taken ++ rest) ++ chosen.map Prod.snd).Perm ((taken ++ chosen.map Prod.snd) ++ rest) := by
      rw [List.append_assoc, List.append_assoc]
      exact List.perm_append_comm.append_left taken
    exact (formPerm.append_right _).trans (middle.trans (partsPerm.symm.append_right rest))

/-! ## Steps through presentations -/

include laws in
/-- **A step of a process is matched by a step of a presentation of its canonical form**, to a contractum equivalent
to the original contractum: within the arity when the canonical form's replicated components copy molecules, by
compression, and within the arity times the ceiling otherwise. -/
theorem replication_presented (reactions : ReplicationReactions language block step) {free : FreeTypeContext}
    {bound : List TypeExpr} (context : BaseContext free bound) {source target : Pattern} {count : Nat}
    {redex : reactions.Redex} {rest : List Pattern}
    (reached : ReplicationStepAt reactions free bound source target count redex rest)
    (sourceTyped : HasType language free bound source (.base block.proc))
    (sourceObject : isObjectPattern source = true) :
    ∃ shown ∈ replicationPresentations block reactions.arity (canonR block source), ∃ target',
      step shown target' ∧ EquationEquiv (engineBasePremises RelationEnv.empty) language target' target := by
  have fresh := replicate_not_emptyUnit (block := block) (language := language)
  have restrictFresh := replicate_ne_restrict (block := block) (language := language)
  obtain ⟨unfolded, unfolds, redex', restU, split, plain, members, objects, reaches⟩ :=
    replication_reaction reactions context reached sourceTyped sourceObject
  have facts := canonFacts fresh restrictFresh sourceObject (restrictionsBind_of_typed (block := block) source sourceTyped)
  have decomposed : decompose block.toBlock (canonR block source) = canonP block source := by
    unfold canonR
    exact decompose_toPattern facts.atomic facts.used
  -- an unfolding within the presentation depth holding a redex
  obtain ⟨shownForm, within, redexS, restS, splitS, membersS, objectsS, reachesS⟩ :
      ∃ shownForm, UnfoldsWithin block (presentationDepth block reactions.arity (canonP block source))
          (canonP block source) shownForm ∧
        ∃ (redexS : reactions.Redex) (restS : List Pattern),
          shownForm.components.Perm (reactions.parts redexS ++ restS) ∧
          Members language block.toBlock free (List.replicate shownForm.count (TypeExpr.base block.name) ++ bound)
            shownForm.components ∧
          (∀ component ∈ shownForm.components, isObjectPattern component = true) ∧
          EquationEquiv (engineBasePremises RelationEnv.empty) language
            (Prenex.restricts block.toBlock shownForm.count
              (.collection .hashBag (reactions.result redexS ++ restS) none)) target := by
    unfold presentationDepth
    split_ifs with molecular
    · obtain ⟨compressed, compressedWithin, redexC, restC, splitC, -, membersC, objectsC, compressedReads⟩ :=
        compress_molecular reactions context (moleculeServers_spec molecular)
          ((canonP_sound_all source).1.members context sourceTyped) unfolds split plain members objects
      exact ⟨compressed, compressedWithin, redexC, restC, splitC, membersC, objectsC,
        Relation.EqvGen.trans _ _ _ compressedReads reaches⟩
    · exact ⟨unfolded, unfolds, redex', restU, split, members, objects, reaches⟩
  obtain ⟨contracted, stepped, contractedIs⟩ := reactions.react redexS splitS membersS objectsS
  refine ⟨shownForm.toPattern block.toBlock, ?_, Prenex.restricts block.toBlock shownForm.count contracted,
    reactions.restricts_step shownForm.count stepped,
    Relation.EqvGen.trans _ _ _ (restricts_equation (block := block.toBlock) shownForm.count contractedIs) reachesS⟩
  unfold replicationPresentations
  rw [decomposed]
  exact List.mem_map_of_mem ((mem_unfoldings _ _ _).mpr within)

end Compress

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
