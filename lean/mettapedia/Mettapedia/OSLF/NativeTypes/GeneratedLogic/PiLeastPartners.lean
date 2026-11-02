import Mettapedia.Languages.ProcessCalculi.PiCalculus.CongruenceToolkit
import Mettapedia.GSLT.Logic.BagHennessyMilner

/-!
# π's least partners, aware of scope

π composes in parallel, but restriction hides names: a partner can never name what a process restricts. Here a process
is a bag of **molecules**: a molecule is a scope of restricted names over a bag of guarded processes (inputs, outputs,
replicated inputs), and partners are bags of molecules beside the hole. A partner's molecules keep their own scopes,
so it cannot name the agent's restricted names; scope extrusion is a reaction that merges two molecules into one scope.
The context category is the free commutative monoid of bags of molecules, so every span has relative pushouts and the
generic results for parallel calculi apply. There:

- **Reactions** (`Internal`, `Cross`, `rules`): a communication inside one molecule, on any channel; and a
  communication between two molecules, after renaming their restricted names apart (`Alpha`, `Apart`), which merges
  their scopes, so a restricted payload stays restricted in the receiver. The continuation's top-level restrictions
  join the scope and its parallel components the bag (`Lifts`).
- **Scope**: two molecules apart can communicate only on a channel neither restricts (`channel_public`), so a molecule
  that only uses restricted channels (`Private`) takes part in no communication with another (`not_private_of_cross`).
- **Least labels** (`actIPO_iff`): a least label is what the agent lacks of a redex: nothing, when the agent holds it;
  the molecule of an internal communication, when it lacks it; or what it lacks of the two molecules of a cross
  communication. A private molecule is observed only through the steps it takes alone (`private_steps_alone`).
- **Saturated bisimilarity** against every partner is semi-saturated: least-labelled steps characterize it
  (`semiSaturated_iff_saturated`). A private molecule with no internal step is saturated bisimilar to the inert process
  (`private_inert`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.Pi.LeastPartners

open _root_.CategoryTheory
open Mettapedia.Languages.ProcessCalculi.PiCalculus
open Mettapedia.GSLT.RedexRelativeCongruence (ReactionRule ActIPO)
open Mettapedia.GSLT.BagRelativePushout (Obj bag bag_injective)
open Mettapedia.GSLT.SemiSaturated (Reacts SemiSaturatedBisimilar SaturatedBisimilar)
open Mettapedia.GSLT.BagHennessyMilner (SaturatedBisimilarIn IsSaturatedIn)

/-! ## Guarded processes and molecules -/

/-- **A guarded process**: an input, an output, or a replicated input. -/
inductive Guarded : Process → Prop
  | input (x y : Name) (body : Process) : Guarded (.input x y body)
  | output (x z : Name) : Guarded (.output x z)
  | replicate (x y : Name) (body : Process) : Guarded (.replicate x y body)

instance : DecidablePred Guarded := fun process => by
  cases process
  case input x y body => exact isTrue (.input x y body)
  case output x z => exact isTrue (.output x z)
  case replicate x y body => exact isTrue (.replicate x y body)
  all_goals exact isFalse (by rintro ⟨⟩)

/-- The guarded processes. -/
abbrev Prime : Type := {process : Process // Guarded process}

/-- The channel a guarded process listens or sends on. -/
def subject : Process → Name
  | .input x _ _ => x
  | .output x _ => x
  | .replicate x _ _ => x
  | _ => ""

theorem guarded_substitute {process : Process} (guarded : Guarded process) (y z : Name) :
    Guarded (process.substitute y z) := by
  cases guarded with
  | input x w body => rw [Process.substitute]; split_ifs <;> exact .input _ _ _
  | output x w => rw [Process.substitute]; exact .output _ _
  | replicate x w body => rw [Process.substitute]; split_ifs <;> exact .replicate _ _ _

theorem subject_substitute {process : Process} (guarded : Guarded process) (y z : Name) :
    subject (process.substitute y z) = if subject process = y then z else subject process := by
  cases guarded with
  | input x w body => rw [Process.substitute]; split_ifs <;> simp_all [subject]
  | output x w => rw [Process.substitute]; simp only [subject]; split_ifs <;> simp_all
  | replicate x w body => rw [Process.substitute]; split_ifs <;> simp_all [subject]

/-- **A molecule**: a scope of restricted names over a bag of guarded processes, `ν scope. ∏ body`. -/
structure Molecule where
  scope : Finset Name
  body : Multiset Prime
  deriving DecidableEq

namespace Molecule

/-- The free names of a molecule's body, its restricted names among them. -/
def bodyNames (molecule : Molecule) : Finset Name := molecule.body.toFinset.biUnion fun prime => prime.1.freeNames

theorem mem_bodyNames {molecule : Molecule} {name : Name} :
    name ∈ molecule.bodyNames ↔ ∃ prime ∈ molecule.body, name ∈ prime.1.freeNames := by
  simp [bodyNames]

theorem freeNames_le_bodyNames {molecule : Molecule} {prime : Prime} (member : prime ∈ molecule.body) :
    prime.1.freeNames ⊆ molecule.bodyNames := fun _ inside => mem_bodyNames.mpr ⟨prime, member, inside⟩

theorem subject_mem_freeNames {process : Process} (guarded : Guarded process) : subject process ∈ process.freeNames := by
  cases guarded <;> simp [subject, Process.freeNames]

theorem subject_mem_bodyNames {molecule : Molecule} {prime : Prime} (member : prime ∈ molecule.body) :
    subject prime.1 ∈ molecule.bodyNames :=
  freeNames_le_bodyNames member (subject_mem_freeNames prime.2)

/-- **A private molecule**: every guarded process in it is on a restricted channel. -/
def Private (molecule : Molecule) : Prop := ∀ prime ∈ molecule.body, subject prime.1 ∈ molecule.scope

/-- Renaming a guarded process. -/
def renamePrime (old new : Name) (prime : Prime) : Prime := ⟨prime.1.substitute old new, guarded_substitute prime.2 old new⟩

/-- **One restricted name renamed** to a name the molecule does not use. -/
inductive RenameStep : Molecule → Molecule → Prop
  | rename {molecule : Molecule} {old new : Name} (restricted : old ∈ molecule.scope) (unused : new ∉ molecule.scope)
      (fresh : new ∉ molecule.bodyNames) :
      RenameStep molecule ⟨insert new (molecule.scope.erase old), molecule.body.map (renamePrime old new)⟩

/-- **α-variants**: restricted names renamed, one at a time. -/
abbrev Alpha : Molecule → Molecule → Prop := Relation.ReflTransGen RenameStep

theorem private_renameStep {molecule renamed : Molecule} (step : RenameStep molecule renamed) (hidden : Private molecule) :
    Private renamed := by
  cases step with
  | @rename old new restricted unused fresh =>
    intro prime member
    obtain ⟨original, originalMem, rfl⟩ := Multiset.mem_map.mp member
    simp only [renamePrime, subject_substitute original.2]
    split_ifs with same
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨same, hidden original originalMem⟩)

theorem private_alpha {molecule renamed : Molecule} (variant : Alpha molecule renamed) (hidden : Private molecule) :
    Private renamed := by
  induction variant with
  | refl => exact hidden
  | tail _ step holds => exact private_renameStep step holds

end Molecule

open Molecule

/-- **Two molecules apart**: neither's restricted names occur in the other. -/
def Apart (first second : Molecule) : Prop :=
  Disjoint first.scope (second.scope ∪ second.bodyNames) ∧ Disjoint second.scope (first.scope ∪ first.bodyNames)

/-! ## Communication -/

/-- **A communication between guarded processes**: a receiver and a sender on one channel, the continuation, and
what the receiver keeps (a replicated input keeps itself). -/
inductive Fires : Prime → Prime → Process → Multiset Prime → Prop
  | input (x y z : Name) (body : Process) :
      Fires ⟨.input x y body, .input x y body⟩ ⟨.output x z, .output x z⟩ (body.substitute y z) 0
  | replicate (x y z : Name) (body : Process) :
      Fires ⟨.replicate x y body, .replicate x y body⟩ ⟨.output x z, .output x z⟩ (body.substitute y z)
        {⟨.replicate x y body, .replicate x y body⟩}

theorem Fires.subject_eq {receiver sender : Prime} {continuation : Process} {kept : Multiset Prime}
    (fires : Fires receiver sender continuation kept) : subject receiver.1 = subject sender.1 := by
  cases fires <;> rfl

/-- **A process lifted into a scope**: its top-level restrictions, renamed apart, join the scope, and its parallel
components the bag. -/
inductive Lifts : Process → Finset Name → Multiset Prime → Prop
  | nil : Lifts .nil ∅ 0
  | guarded {process : Process} (guarded : Guarded process) : Lifts process ∅ {⟨process, guarded⟩}
  | par {left right : Process} {leftScope rightScope : Finset Name} {leftBody rightBody : Multiset Prime} :
      Lifts left leftScope leftBody → Lifts right rightScope rightBody → Disjoint leftScope rightScope →
      Disjoint leftScope right.freeNames → Disjoint rightScope left.freeNames →
      Lifts (left ||| right) (leftScope ∪ rightScope) (leftBody + rightBody)
  | nu {name new : Name} {process : Process} {scope : Finset Name} {body : Multiset Prime} :
      Lifts (process.substitute name new) scope body → new ∉ scope → new ∉ (Process.nu name process).freeNames →
      Lifts (.nu name process) (insert new scope) body

/-- **A communication inside a molecule**, on any channel. -/
inductive Internal : Molecule → Molecule → Prop
  | comm {molecule : Molecule} {receiver sender : Prime} {continuation : Process} {kept : Multiset Prime}
      {lifted : Finset Name} {components : Multiset Prime} :
      {receiver, sender} ≤ molecule.body → Fires receiver sender continuation kept →
      Lifts continuation lifted components → Disjoint lifted (molecule.scope ∪ molecule.bodyNames) →
      Internal molecule
        ⟨molecule.scope ∪ lifted, molecule.body - {receiver, sender} + kept + components⟩

/-- **A communication between two molecules**: both renamed apart, a receiver in one and a sender in the other; the
scopes merge, so a restricted payload stays restricted in the receiver. -/
inductive Cross : Molecule → Molecule → Molecule → Prop
  | receive {first second first' second' : Molecule} {receiver sender : Prime} {continuation : Process}
      {kept : Multiset Prime} {lifted : Finset Name} {components : Multiset Prime} :
      Alpha first first' → Alpha second second' → Apart first' second' → receiver ∈ first'.body →
      sender ∈ second'.body → Fires receiver sender continuation kept → Lifts continuation lifted components →
      Disjoint lifted (first'.scope ∪ first'.bodyNames ∪ second'.scope ∪ second'.bodyNames) →
      Cross first second
        ⟨first'.scope ∪ second'.scope ∪ lifted,
          (first'.body - {receiver}) + (second'.body - {sender}) + kept + components⟩
  | send {first second first' second' : Molecule} {receiver sender : Prime} {continuation : Process}
      {kept : Multiset Prime} {lifted : Finset Name} {components : Multiset Prime} :
      Alpha first first' → Alpha second second' → Apart first' second' → sender ∈ first'.body →
      receiver ∈ second'.body → Fires receiver sender continuation kept → Lifts continuation lifted components →
      Disjoint lifted (first'.scope ∪ first'.bodyNames ∪ second'.scope ∪ second'.bodyNames) →
      Cross first second
        ⟨first'.scope ∪ second'.scope ∪ lifted,
          (first'.body - {sender}) + (second'.body - {receiver}) + kept + components⟩

/-- **Molecules apart communicate only on a channel neither restricts.** -/
theorem channel_public {first second : Molecule} (apart : Apart first second) {mine theirs : Prime}
    (mineMem : mine ∈ first.body) (theirsMem : theirs ∈ second.body) (same : subject mine.1 = subject theirs.1) :
    subject mine.1 ∉ first.scope ∧ subject theirs.1 ∉ second.scope := by
  constructor
  · intro restricted
    have := subject_mem_bodyNames theirsMem
    rw [← same] at this
    exact Finset.disjoint_left.mp apart.1 restricted (Finset.mem_union_right _ this)
  · intro restricted
    have := subject_mem_bodyNames mineMem
    rw [same] at this
    exact Finset.disjoint_left.mp apart.2 restricted (Finset.mem_union_right _ this)

/-- **A private molecule communicates with no other.** -/
theorem not_private_of_cross {first second result : Molecule} (cross : Cross first second result) :
    ¬ Private first ∧ ¬ Private second := by
  cases cross with
  | receive firstVariant secondVariant apart receiverMem senderMem fires _ _ =>
    have outside := channel_public apart receiverMem senderMem fires.subject_eq
    exact ⟨fun hidden => outside.1 (private_alpha firstVariant hidden _ receiverMem),
      fun hidden => outside.2 (private_alpha secondVariant hidden _ senderMem)⟩
  | send firstVariant secondVariant apart senderMem receiverMem fires _ _ =>
    have outside := channel_public apart senderMem receiverMem fires.subject_eq.symm
    exact ⟨fun hidden => outside.1 (private_alpha firstVariant hidden _ senderMem),
      fun hidden => outside.2 (private_alpha secondVariant hidden _ receiverMem)⟩

/-! ## The reactive system -/

/-- An internal communication as a reaction rule. -/
def internalRule (molecule result : Molecule) : ReactionRule (Obj Molecule) where
  codomain := Obj Molecule
  redex := bag {molecule}
  reactum := bag {result}

/-- A communication between two molecules as a reaction rule. -/
def crossRule (first second result : Molecule) : ReactionRule (Obj Molecule) where
  codomain := Obj Molecule
  redex := bag {first, second}
  reactum := bag {result}

/-- **π's reaction rules on bags of molecules.** -/
def rules (rule : ReactionRule (Obj Molecule)) : Prop :=
  (∃ molecule result, Internal molecule result ∧ rule = internalRule molecule result) ∨
    ∃ first second result, Cross first second result ∧ rule = crossRule first second result

/-- **Least labels characterize saturated bisimilarity**: every span of bags has relative pushouts. -/
theorem semiSaturated_iff_saturated {first second : Multiset Molecule} :
    SemiSaturatedBisimilar rules (bag first) (bag second) ↔ SaturatedBisimilar rules (bag first) (bag second) :=
  Mettapedia.GSLT.BagSaturated.semiSaturated_iff_saturated

/-- **π's least-labelled steps**: the label is what the agent lacks of an internal communication's molecule, or of a
cross communication's two molecules; the result is the reactum with what the agent keeps. -/
theorem actIPO_iff {agent label target : Multiset Molecule} :
    ActIPO rules (bag label) (bag agent) (bag target) ↔
      (∃ molecule result, Internal molecule result ∧ label = {molecule} - agent ∧
          target = {result} + (agent - {molecule})) ∨
        ∃ first second result, Cross first second result ∧ label = {first, second} - agent ∧
          target = {result} + (agent - {first, second}) := by
  rw [Mettapedia.GSLT.BagSaturated.actIPO_iff]
  constructor
  · rintro ⟨_, (⟨molecule, result, internal, rfl⟩ | ⟨first, second, result, cross, rfl⟩), l, k, redexEq, reactumEq,
      rfl, rfl⟩
    · obtain rfl := bag_injective redexEq
      obtain rfl := bag_injective reactumEq
      exact Or.inl ⟨molecule, result, internal, rfl, rfl⟩
    · obtain rfl := bag_injective redexEq
      obtain rfl := bag_injective reactumEq
      exact Or.inr ⟨first, second, result, cross, rfl, rfl⟩
  · rintro (⟨molecule, result, internal, rfl, rfl⟩ | ⟨first, second, result, cross, rfl, rfl⟩)
    · exact ⟨internalRule molecule result, Or.inl ⟨molecule, result, internal, rfl⟩, _, _, rfl, rfl, rfl, rfl⟩
    · exact ⟨crossRule first second result, Or.inr ⟨first, second, result, cross, rfl⟩, _, _, rfl, rfl, rfl, rfl⟩

/-- **A private molecule is observed only through the steps it takes alone**: a least-labelled step of it either is
one of its internal communications, with the empty label, or does not involve it, the label being a whole redex. -/
theorem private_steps_alone {molecule : Molecule} (hidden : Private molecule) {label target : Multiset Molecule}
    (step : ActIPO rules (bag label) (bag {molecule}) (bag target)) :
    (∃ result, Internal molecule result ∧ label = 0 ∧ target = {result}) ∨
      ∃ rule : ReactionRule (Obj Molecule), rules rule ∧ ∃ redex reactum : Multiset Molecule,
        rule.redex = bag redex ∧ rule.reactum = bag reactum ∧ molecule ∉ redex ∧ label = redex ∧
          target = reactum + {molecule} := by
  rcases actIPO_iff.mp step with ⟨other, result, internal, rfl, rfl⟩ | ⟨first, second, result, cross, rfl, rfl⟩
  · by_cases same : other = molecule
    · subst same
      exact Or.inl ⟨result, internal, by simp, by simp⟩
    · refine Or.inr ⟨internalRule other result, Or.inl ⟨other, result, internal, rfl⟩, {other}, {result}, rfl, rfl,
        by simpa [eq_comm] using same, ?_, ?_⟩
      · rw [Multiset.sub_singleton, Multiset.erase_of_notMem (by simpa [eq_comm] using same)]
      · rw [Multiset.sub_singleton, Multiset.erase_of_notMem (by simpa using same), add_comm]
  · have notFirst : first ≠ molecule := fun same => (not_private_of_cross cross).1 (same ▸ hidden)
    have notSecond : second ≠ molecule := fun same => (not_private_of_cross cross).2 (same ▸ hidden)
    have absent : molecule ∉ ({first, second} : Multiset Molecule) := by
      simp [Multiset.insert_eq_cons, Ne.symm notFirst, Ne.symm notSecond]
    refine Or.inr ⟨crossRule first second result, Or.inr ⟨first, second, result, cross, rfl⟩, {first, second},
      {result}, rfl, rfl, absent, ?_, ?_⟩
    · rw [Multiset.sub_singleton, Multiset.erase_of_notMem absent]
    · rw [Multiset.insert_eq_cons, Multiset.sub_cons, Multiset.erase_of_notMem (by simpa using notFirst),
        Multiset.sub_singleton, Multiset.erase_of_notMem (by simpa using notSecond), add_comm]

/-! ## Private molecules are inert -/

/-- A private molecule with no internal step is in no redex. -/
theorem not_mem_redex {molecule : Molecule} (hidden : Private molecule) (still : ∀ result, ¬ Internal molecule result)
    {rule : ReactionRule (Obj Molecule)} (member : rules rule) {redex : Multiset Molecule}
    (redexEq : rule.redex = bag redex) : molecule ∉ redex := by
  rcases member with ⟨other, result, internal, rfl⟩ | ⟨first, second, result, cross, rfl⟩
  · obtain rfl := bag_injective redexEq
    intro inside
    obtain rfl := Multiset.mem_singleton.mp inside
    exact still result internal
  · obtain rfl := bag_injective redexEq
    intro inside
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at inside
    rcases inside with rfl | rfl
    · exact (not_private_of_cross cross).1 hidden
    · exact (not_private_of_cross cross).2 hidden

theorem le_of_le_add_singleton {redex rest : Multiset Molecule} {molecule : Molecule}
    (contained : redex ≤ rest + {molecule}) (absent : molecule ∉ redex) : redex ≤ rest := by
  refine Multiset.le_iff_count.mpr fun other => ?_
  have bound := Multiset.le_iff_count.mp contained other
  by_cases same : other = molecule
  · subst same
    simp [Multiset.count_eq_zero.mpr absent]
  · simpa [Multiset.count_singleton, same] using bound

/-- **A private molecule with no internal step is saturated bisimilar to the inert process**: no partner can name
what it restricts. -/
theorem private_inert {molecule : Molecule} (hidden : Private molecule) (still : ∀ result, ¬ Internal molecule result) :
    SaturatedBisimilarIn rules (fun _ => True) {molecule} 0 := by
  refine ⟨fun first second => first = second + {molecule}, ?_, by simp⟩
  rintro first second rfl context -
  simp only [Mettapedia.GSLT.BagRelativePushout.bag_comp]
  have arrange : second + {molecule} + context = (second + context) + {molecule} := add_right_comm _ _ _
  constructor
  · intro next reacts
    obtain ⟨rule, member, redex, reactum, redexEq, reactumEq, contained, rfl⟩ :=
      Mettapedia.GSLT.BagSaturated.reacts_iff.mp reacts
    rw [arrange] at contained ⊢
    have within := le_of_le_add_singleton contained (not_mem_redex hidden still member redexEq)
    refine ⟨reactum + (second + context - redex),
      Mettapedia.GSLT.BagSaturated.reacts_iff.mpr ⟨rule, member, redex, reactum, redexEq, reactumEq, within, rfl⟩, ?_⟩
    rw [← tsub_add_eq_add_tsub within, add_assoc]
  · intro next reacts
    obtain ⟨rule, member, redex, reactum, redexEq, reactumEq, contained, rfl⟩ :=
      Mettapedia.GSLT.BagSaturated.reacts_iff.mp reacts
    refine ⟨reactum + (second + {molecule} + context - redex),
      Mettapedia.GSLT.BagSaturated.reacts_iff.mpr ⟨rule, member, redex, reactum, redexEq, reactumEq,
        arrange ▸ contained.trans (Multiset.le_add_right _ _), rfl⟩, ?_⟩
    rw [arrange, ← tsub_add_eq_add_tsub contained, add_assoc]

/-! ## Every process lifts, and molecules rename apart -/

/-- **Every process lifts into a scope**, its restrictions renamed away from any finite set. -/
theorem lifts_exists : ∀ (size : ℕ) (process : Process), process.nodeCount ≤ size → ∀ avoid : Finset Name,
    ∃ scope body, Lifts process scope body ∧ Disjoint scope avoid
  | 0, process, small, _ => by cases process <;> simp [Process.nodeCount] at small
  | size + 1, process, small, avoid => by
    cases process with
    | nil => exact ⟨∅, 0, .nil, Finset.disjoint_empty_left _⟩
    | input x y body => exact ⟨∅, _, .guarded (.input x y body), Finset.disjoint_empty_left _⟩
    | output x z => exact ⟨∅, _, .guarded (.output x z), Finset.disjoint_empty_left _⟩
    | replicate x y body => exact ⟨∅, _, .guarded (.replicate x y body), Finset.disjoint_empty_left _⟩
    | par left right =>
      simp only [Process.nodeCount] at small
      obtain ⟨leftScope, leftBody, leftLifts, leftAvoids⟩ :=
        lifts_exists size left (by omega) (avoid ∪ right.freeNames)
      obtain ⟨rightScope, rightBody, rightLifts, rightAvoids⟩ :=
        lifts_exists size right (by omega) (avoid ∪ left.freeNames ∪ leftScope)
      refine ⟨leftScope ∪ rightScope, leftBody + rightBody, .par leftLifts rightLifts ?_ ?_ ?_, ?_⟩
      · exact (rightAvoids.mono_right Finset.subset_union_right).symm
      · exact leftAvoids.mono_right Finset.subset_union_right
      · exact rightAvoids.mono_right (Finset.subset_union_right.trans Finset.subset_union_left)
      · exact Finset.disjoint_union_left.mpr ⟨leftAvoids.mono_right Finset.subset_union_left,
          rightAvoids.mono_right (Finset.subset_union_left.trans Finset.subset_union_left)⟩
    | nu name body =>
      simp only [Process.nodeCount] at small
      obtain ⟨new, freshNew⟩ : ∃ new, new ∉ avoid ∪ body.names ∪ {name} :=
        ⟨_, Mettapedia.FreshString.fresh_not_mem _⟩
      simp only [Finset.mem_union, Finset.mem_singleton, not_or] at freshNew
      obtain ⟨⟨notAvoid, notNames⟩, notName⟩ := freshNew
      obtain ⟨scope, components, lifts, avoids⟩ :=
        lifts_exists size (body.substitute name new) (by rw [nodeCount_substitute]; omega) (avoid ∪ {new})
      refine ⟨insert new scope, components, .nu lifts ?_ ?_, ?_⟩
      · exact fun inside => Finset.disjoint_left.mp avoids inside (Finset.mem_union_right _ (Finset.mem_singleton_self _))
      · intro inside
        simp only [Process.freeNames, Finset.mem_sdiff] at inside
        exact notNames (Finset.mem_union_left _ inside.1)
      · rw [Finset.insert_eq]
        exact Finset.disjoint_union_left.mpr
          ⟨Finset.disjoint_singleton_left.mpr notAvoid, avoids.mono_right Finset.subset_union_left⟩

/-- The free names of a molecule: those of its body it does not restrict. -/
def Molecule.freeNames (molecule : Molecule) : Finset Name := molecule.bodyNames \ molecule.scope

theorem bodyNames_renamed {molecule : Molecule} {old new : Name} :
    (Molecule.mk (insert new (molecule.scope.erase old)) (molecule.body.map (renamePrime old new))).bodyNames ⊆
      insert new (molecule.bodyNames \ {old}) := by
  intro name member
  obtain ⟨renamed, renamedMem, inside⟩ := Molecule.mem_bodyNames.mp member
  obtain ⟨prime, primeMem, rfl⟩ := Multiset.mem_map.mp renamedMem
  have bound := Process.substitute_freeNames prime.1 old new inside
  simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton] at bound ⊢
  rcases bound with same | ⟨present, different⟩
  · exact Or.inl same
  · exact Or.inr ⟨Molecule.mem_bodyNames.mpr ⟨prime, primeMem, present⟩, different⟩


theorem renameStep_bodyNames {molecule renamed : Molecule} (step : RenameStep molecule renamed) :
    renamed.bodyNames ⊆ molecule.freeNames ∪ renamed.scope := by
  cases step with
  | @rename old new restricted unused fresh =>
    intro name member
    have bound := bodyNames_renamed member
    simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton] at bound
    simp only [Finset.mem_union, Molecule.freeNames, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
    rcases bound with same | ⟨present, different⟩
    · exact Or.inr (Or.inl same)
    · by_cases restrictedName : name ∈ molecule.scope
      · exact Or.inr (Or.inr ⟨different, restrictedName⟩)
      · exact Or.inl ⟨present, restrictedName⟩

theorem alpha_freeNames {molecule renamed : Molecule} (variant : Alpha molecule renamed) :
    renamed.bodyNames ⊆ molecule.freeNames ∪ renamed.scope := by
  induction variant with
  | refl =>
    intro name member
    by_cases restricted : name ∈ molecule.scope
    · exact Finset.mem_union_right _ restricted
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨member, restricted⟩)
  | @tail middle last _ step earlier =>
    intro name member
    rcases Finset.mem_union.mp (renameStep_bodyNames step member) with free | restricted
    · obtain ⟨present, notRestricted⟩ := Finset.mem_sdiff.mp free
      rcases Finset.mem_union.mp (earlier present) with original | middleRestricted
      · exact Finset.mem_union_left _ original
      · exact absurd middleRestricted notRestricted
    · exact Finset.mem_union_right _ restricted

/-- **Restricted names rename away from any finite set.** -/
theorem exists_alpha_avoiding : ∀ (count : ℕ) (molecule : Molecule) (avoid : Finset Name),
    (molecule.scope ∩ avoid).card ≤ count → ∃ renamed, Alpha molecule renamed ∧ Disjoint renamed.scope avoid
  | 0, molecule, avoid, small => ⟨molecule, .refl, Finset.disjoint_iff_inter_eq_empty.mpr
      (Finset.card_eq_zero.mp (Nat.le_zero.mp small))⟩
  | count + 1, molecule, avoid, small => by
    by_cases clear : molecule.scope ∩ avoid = ∅
    · exact ⟨molecule, .refl, Finset.disjoint_iff_inter_eq_empty.mpr clear⟩
    obtain ⟨old, oldMem⟩ := Finset.nonempty_iff_ne_empty.mpr clear
    obtain ⟨new, freshNew⟩ : ∃ new, new ∉ avoid ∪ molecule.scope ∪ molecule.bodyNames :=
      ⟨_, Mettapedia.FreshString.fresh_not_mem _⟩
    simp only [Finset.mem_union, not_or] at freshNew
    obtain ⟨⟨notAvoid, notScope⟩, notBody⟩ := freshNew
    have step : RenameStep molecule ⟨insert new (molecule.scope.erase old), molecule.body.map (renamePrime old new)⟩ :=
      .rename (Finset.mem_inter.mp oldMem).1 notScope notBody
    have smaller : ((insert new (molecule.scope.erase old)) ∩ avoid).card ≤ count := by
      have same : (insert new (molecule.scope.erase old)) ∩ avoid = (molecule.scope ∩ avoid).erase old := by
        ext name
        simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_erase]
        constructor
        · rintro ⟨rfl | ⟨different, restricted⟩, avoided⟩
          · exact absurd avoided notAvoid
          · exact ⟨different, restricted, avoided⟩
        · rintro ⟨different, restricted, avoided⟩
          exact ⟨Or.inr ⟨different, restricted⟩, avoided⟩
      rw [same, Finset.card_erase_of_mem oldMem]
      omega
    obtain ⟨renamed, variant, disjoint⟩ :=
      exists_alpha_avoiding count ⟨insert new (molecule.scope.erase old), molecule.body.map (renamePrime old new)⟩ avoid
        smaller
    exact ⟨renamed, Relation.ReflTransGen.head step variant, disjoint⟩

/-- **Any two molecules have α-variants apart.** -/
theorem exists_apart (first second : Molecule) :
    ∃ first' second', Alpha first first' ∧ Alpha second second' ∧ Apart first' second' := by
  obtain ⟨first', firstVariant, firstAvoids⟩ := exists_alpha_avoiding _ first second.freeNames le_rfl
  obtain ⟨second', secondVariant, secondAvoids⟩ :=
    exists_alpha_avoiding _ second (first'.scope ∪ first'.bodyNames) le_rfl
  refine ⟨first', second', firstVariant, secondVariant, ?_, secondAvoids⟩
  refine Finset.disjoint_left.mpr fun name restricted inside => ?_
  rcases Finset.mem_union.mp inside with theirs | body
  · exact Finset.disjoint_left.mp secondAvoids theirs (Finset.mem_union_left _ restricted)
  · rcases Finset.mem_union.mp (alpha_freeNames secondVariant body) with free | theirs
    · exact Finset.disjoint_left.mp firstAvoids restricted free
    · exact Finset.disjoint_left.mp secondAvoids theirs (Finset.mem_union_left _ restricted)

/-! ## Receivers and senders survive renaming -/

theorem subject_of_receivesOn {channel : Name} {process : Process} (receives : ReceivesOn channel process) :
    subject process = channel := by
  rcases receives with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> rfl

theorem subject_of_sendsOn {channel : Name} {process : Process} (sends : SendsOn channel process) :
    subject process = channel := by
  obtain ⟨_, rfl⟩ := sends
  rfl

/-- **A guarded process on an unrestricted channel survives renaming**, on the same channel and of the same kind. -/
theorem alpha_keeps {molecule renamed : Molecule} (variant : Alpha molecule renamed) {channel : Name}
    (kind : Process → Prop) (keeps : ∀ {process : Process} {old new : Name}, kind process → channel ≠ old →
      kind (process.substitute old new))
    (onChannel : ∀ {process : Process}, kind process → subject process = channel) {prime : Prime}
    (member : prime ∈ molecule.body) (holds : kind prime.1) (outside : channel ∉ molecule.scope) :
    ∃ prime' ∈ renamed.body, kind prime'.1 ∧ channel ∉ renamed.scope := by
  induction variant with
  | refl => exact ⟨prime, member, holds, outside⟩
  | @tail middle last _ step earlier =>
    obtain ⟨found, foundMem, foundHolds, foundOutside⟩ := earlier
    cases step with
    | @rename old new restricted unused fresh =>
      have notOld : channel ≠ old := fun same => foundOutside (same ▸ restricted)
      have notNew : channel ≠ new := fun same => fresh (same ▸ onChannel foundHolds ▸ subject_mem_bodyNames foundMem)
      refine ⟨renamePrime old new found, Multiset.mem_map_of_mem _ foundMem, keeps foundHolds notOld, ?_⟩
      simp only [Finset.mem_insert, Finset.mem_erase, not_or, not_and]
      exact ⟨notNew, fun _ inside => foundOutside inside⟩

theorem fires_of {channel : Name} {receiver sender : Prime} (receives : ReceivesOn channel receiver.1)
    (sends : SendsOn channel sender.1) : ∃ continuation kept, Fires receiver sender continuation kept := by
  obtain ⟨receiver, receiverGuarded⟩ := receiver
  obtain ⟨sender, senderGuarded⟩ := sender
  obtain ⟨payload, rfl⟩ := sends
  rcases receives with ⟨bound, body, rfl⟩ | ⟨bound, body, rfl⟩
  · exact ⟨_, _, .input channel bound payload body⟩
  · exact ⟨_, _, .replicate channel bound payload body⟩

/-- **A receiver and a sender on a channel neither molecule restricts communicate.** -/
theorem cross_exists {first second : Molecule} {receiver sender : Prime} {channel : Name}
    (receiverMem : receiver ∈ first.body) (senderMem : sender ∈ second.body) (receives : ReceivesOn channel receiver.1)
    (sends : SendsOn channel sender.1) (firstOutside : channel ∉ first.scope) (secondOutside : channel ∉ second.scope) :
    ∃ result, Cross first second result := by
  obtain ⟨first', second', firstVariant, secondVariant, apart⟩ := exists_apart first second
  obtain ⟨receiver', receiverMem', receives', -⟩ := alpha_keeps firstVariant (ReceivesOn channel)
    receivesOn_substitute subject_of_receivesOn receiverMem receives firstOutside
  obtain ⟨sender', senderMem', sends', -⟩ := alpha_keeps secondVariant (SendsOn channel)
    sendsOn_substitute subject_of_sendsOn senderMem sends secondOutside
  obtain ⟨continuation, kept, fires⟩ := fires_of receives' sends'
  obtain ⟨lifted, components, lifts, avoids⟩ := lifts_exists _ continuation le_rfl
    (first'.scope ∪ first'.bodyNames ∪ second'.scope ∪ second'.bodyNames)
  exact ⟨_, .receive firstVariant secondVariant apart receiverMem' senderMem' fires lifts avoids⟩

/-- **A sender and a receiver on a channel neither molecule restricts communicate.** -/
theorem cross_exists_send {first second : Molecule} {receiver sender : Prime} {channel : Name}
    (senderMem : sender ∈ first.body) (receiverMem : receiver ∈ second.body) (receives : ReceivesOn channel receiver.1)
    (sends : SendsOn channel sender.1) (firstOutside : channel ∉ first.scope) (secondOutside : channel ∉ second.scope) :
    ∃ result, Cross first second result := by
  obtain ⟨first', second', firstVariant, secondVariant, apart⟩ := exists_apart first second
  obtain ⟨sender', senderMem', sends', -⟩ := alpha_keeps firstVariant (SendsOn channel)
    sendsOn_substitute subject_of_sendsOn senderMem sends firstOutside
  obtain ⟨receiver', receiverMem', receives', -⟩ := alpha_keeps secondVariant (ReceivesOn channel)
    receivesOn_substitute subject_of_receivesOn receiverMem receives secondOutside
  obtain ⟨continuation, kept, fires⟩ := fires_of receives' sends'
  obtain ⟨lifted, components, lifts, avoids⟩ := lifts_exists _ continuation le_rfl
    (first'.scope ∪ first'.bodyNames ∪ second'.scope ∪ second'.bodyNames)
  exact ⟨_, .send firstVariant secondVariant apart senderMem' receiverMem' fires lifts avoids⟩

/-! ## The schemas of least partners -/

theorem pair_sub {agent : Multiset Molecule} {held partner : Molecule} (holds : held ∈ agent) (lacks : partner ∉ agent) :
    ({held, partner} : Multiset Molecule) - agent = {partner} := by
  have different : held ≠ partner := fun same => lacks (same ▸ holds)
  ext other
  rw [Multiset.count_sub, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton]
  by_cases isHeld : other = held
  · subst isHeld
    have := Multiset.one_le_count_iff_mem.mpr holds
    simp [different]
    omega
  · by_cases isPartner : other = partner
    · subst isPartner
      simp [Multiset.count_eq_zero.mpr lacks, isHeld]
    · simp [isHeld, isPartner]

/-- **The payload schema of a receiver**: an agent holding a molecule with an input (or replicated input) on a channel
it does not restrict has, for every molecule it lacks that sends on that channel without restricting it, that molecule
as a least label. The payload and the partner's other contents are the schema's metavariables; the partner's own
restricted names stay its own. -/
theorem payloadSchema {agent : Multiset Molecule} {held partner : Molecule} {receiver sender : Prime} {channel : Name}
    (holds : held ∈ agent) (lacks : partner ∉ agent) (receiverMem : receiver ∈ held.body)
    (senderMem : sender ∈ partner.body) (receives : ReceivesOn channel receiver.1) (sends : SendsOn channel sender.1)
    (heldOutside : channel ∉ held.scope) (partnerOutside : channel ∉ partner.scope) :
    ∃ result, Cross held partner result ∧
      ActIPO rules (bag {partner}) (bag agent) (bag ({result} + (agent - {held, partner}))) := by
  obtain ⟨result, cross⟩ := cross_exists receiverMem senderMem receives sends heldOutside partnerOutside
  exact ⟨result, cross, actIPO_iff.mpr (Or.inr ⟨held, partner, result, cross, (pair_sub holds lacks).symm, rfl⟩)⟩

/-- **The body schema of a sender**: an agent holding a molecule with an output on a channel it does not restrict has,
for every molecule it lacks that receives on that channel without restricting it, that molecule as a least label. A
restricted payload is extruded: it stays restricted in the merged scope. -/
theorem bodySchema {agent : Multiset Molecule} {held partner : Molecule} {receiver sender : Prime} {channel : Name}
    (holds : held ∈ agent) (lacks : partner ∉ agent) (senderMem : sender ∈ held.body)
    (receiverMem : receiver ∈ partner.body) (receives : ReceivesOn channel receiver.1) (sends : SendsOn channel sender.1)
    (heldOutside : channel ∉ held.scope) (partnerOutside : channel ∉ partner.scope) :
    ∃ result, Cross held partner result ∧
      ActIPO rules (bag {partner}) (bag agent) (bag ({result} + (agent - {held, partner}))) := by
  obtain ⟨result, cross⟩ := cross_exists_send senderMem receiverMem receives sends heldOutside partnerOutside
  exact ⟨result, cross, actIPO_iff.mpr (Or.inr ⟨held, partner, result, cross, (pair_sub holds lacks).symm, rfl⟩)⟩

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.Pi.LeastPartners
