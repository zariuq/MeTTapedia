import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricOperationalControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricPrincipalResults

/-!
# Open local variables, joint freshness and renamed-rule CMR controls

Profile: one first-order occurrence-bag store, ambient rules, guards after
tells. Independently admissible members may fail joint freshness. A genuine
renamed copy of an open rule preserves symmetric uniqueness; fresh result
variables need not have literally identical names.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricMatches.OpenControls

open Mettapedia.Logic.LP
open OneFrame (Terms frames ext)
open FirstOrderLicence.Controls (signature c x)
open MeTTaCalculus.OccurrenceCommits (Enabled)

abbrev X := frames (FirstOrder.action signature)
abbrev E := ext (FirstOrder.action signature)

def source : State (Terms (Term signature)) Nat := ⟨PUnit.unit, [], {0}, fun _ => c 1⟩

theorem source_term {term : Term signature} (mentioned : source.Mentions term) : term = c 1 := by
  rcases mentioned with impossible | impossible | ⟨_, _, row⟩
  · simp [source] at impossible
  · simp [source] at impossible
  · exact row.symm

def readRule : Rule (Terms (Term signature)) := ⟨PUnit.unit, ⟨[], [x], [], [], [x]⟩, []⟩
def readProgram : Program (Terms (Term signature)) := {readRule}
def readMember (out : Nat) : Member Nat E readProgram (a := source.frame) PUnit.unit :=
  ⟨readRule, rfl, Subst.id signature, ⟨[], [0], [out]⟩, []⟩

theorem read_fresh (out : Nat) : (readMember out).firing.Fresh X source := by
  intro b incoming locals
  cases b
  refine ⟨locals, ?_, ?_⟩
  · intro term mentioned
    rw [source_term mentioned]
    rfl
  · intro term _
    change locals.applyTerm ((Subst.id signature).applyTerm term) = locals.applyTerm term
    rw [Subst.applyTerm_id]

theorem read_admitted (out : Nat) (positive : 0 < out) : (readMember out).firing.Admits X source := by
  refine ⟨⟨read_fresh out, List.nodup_nil, List.nodup_singleton out, rfl, rfl, rfl, rfl⟩,
    ⟨(by change (∅ : Finset Nat) ⊆ _; exact Finset.empty_subset _),
      (by change ({0} : Finset Nat) ⊆ {0}; exact fun _ h => h),
      (by change Disjoint (∅ : Finset Nat) {0}; simp), ?_,
      fun q member => by simp [Selection.commit] at member⟩,
    ⟨PUnit.unit, (fun _ => c 1 : Subst signature), ?_⟩,
    fun b assignment _ => ⟨fun check member => absurd member List.not_mem_nil,
      fun q member => absurd member List.not_mem_nil⟩⟩
  · apply Finset.disjoint_left.mpr
    intro o made old
    have same : o = out := by simpa [readMember, Selection.commit] using made
    have zero : o = 0 := by simpa [source] using old
    omega
  · intro equation member
    change equation ∈ [(x, c 1)] at member
    rw [List.mem_singleton.mp member]
    rfl

def capturedBag : Bag Nat E readProgram source.frame := ⟨PUnit.unit, [readMember 10, readMember 11]⟩

theorem singleton_freshness_is_not_joint_freshness :
    (readMember 10).firing.Admits X source ∧ (readMember 11).firing.Admits X source ∧
      ¬ capturedBag.Fresh X source := by
  refine ⟨read_admitted 10 (by decide), read_admitted 11 (by decide), ?_⟩
  intro fresh
  have first := fresh PUnit.unit (Subst.id signature) (fun _ => c 0 : Subst signature)
  have second := first (fun _ => c 1 : Subst signature)
  obtain ⟨assignment, ⟨_, firstValues⟩, secondValues⟩ := second
  have firstZero := firstValues x (by simp [readMember, readRule, Rule.terms])
  have secondOne := secondValues x (by simp [readMember, readRule, Rule.terms])
  change assignment 0 = c 0 at firstZero
  change assignment 0 = c 1 at secondOne
  have contradiction : (c 0 : Term signature) = c 1 := firstZero.symm.trans secondOne
  cases contradiction

def privateRead (slot out : Nat) : Member Nat E readProgram (a := source.frame) PUnit.unit :=
  ⟨readRule, rfl, (fun _ => .var slot : Subst signature), ⟨[], [0], [out]⟩, []⟩
def independentBag : Bag Nat E readProgram source.frame :=
  ⟨PUnit.unit, [privateRead 5 10, privateRead 6 11]⟩

theorem separate_openings_are_jointly_fresh : independentBag.Fresh X source := by
  intro b incoming
  cases b
  intro firstLocals secondLocals
  let assignment : Subst signature := fun v => if v = 5 then firstLocals 0 else secondLocals 0
  refine ⟨assignment, ⟨?_, ?_⟩, ?_⟩
  · intro term mentioned
    rw [source_term mentioned]
    rfl
  · intro term member
    have only : term = x := by simpa [privateRead, readRule, Rule.terms] using member
    rw [only]
    change assignment 5 = firstLocals 0
    simp only [assignment, if_pos rfl]
  · intro term member
    have only : term = x := by simpa [privateRead, readRule, Rule.terms] using member
    rw [only]
    change assignment 6 = secondLocals 0
    simp only [assignment, if_neg (by decide : (6 : Nat) ≠ 5)]

theorem independent_bag_admitted : independentBag.AdmitsOwn X source := by
  refine ⟨⟨separate_openings_are_jointly_fresh, by decide, by decide, ?_⟩,
    ⟨by decide, by decide, by decide, by decide,
      fun q member => by simp [Selection.commit] at member⟩,
    ⟨PUnit.unit, (fun _ => c 1 : Subst signature), ?_⟩, ?_⟩
  · intro m member
    have cases : m = privateRead 5 10 ∨ m = privateRead 6 11 := by
      rcases List.mem_cons.mp member with same | later
      · exact Or.inl same
      · exact Or.inr (List.mem_singleton.mp later)
    rcases cases with rfl | rfl <;> exact ⟨rfl, rfl, rfl, rfl⟩
  · intro equation member
    change equation ∈ [(Term.var (σ := signature) 5, c 1), (Term.var (σ := signature) 6, c 1)] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl
  · intro m member
    have cases : m = privateRead 5 10 ∨ m = privateRead 6 11 := by
      rcases List.mem_cons.mp member with same | later
      · exact Or.inl same
      · exact Or.inr (List.mem_singleton.mp later)
    rcases cases with rfl | rfl <;>
      exact fun b assignment _ => ⟨fun check member => absurd member List.not_mem_nil,
        fun q member => absurd member List.not_mem_nil⟩

def spawnRule : Rule (Terms (Term signature)) := ⟨PUnit.unit, ⟨[], [], [], [], [x]⟩, []⟩
def spawnProgram : Program (Terms (Term signature)) := {spawnRule}
def spawn (slot out : Nat) : Firing Nat E spawnProgram source.frame :=
  ⟨spawnRule, rfl, PUnit.unit, (fun _ => .var slot : Subst signature), ⟨[], [], [out]⟩, []⟩

theorem spawn_fresh (slot out : Nat) : (spawn slot out).Fresh X source := by
  intro b incoming locals
  cases b
  refine ⟨(fun _ => locals 0 : Subst signature), ?_, ?_⟩
  · intro term mentioned
    rw [source_term mentioned]
    rfl
  · intro term member
    have only : term = x := by simpa [spawn, spawnRule, Rule.terms] using member
    rw [only]
    rfl

theorem spawn_admitted (slot out : Nat) (positive : 0 < out) : (spawn slot out).Admits X source := by
  refine ⟨⟨spawn_fresh slot out, List.nodup_nil, List.nodup_singleton out, rfl, rfl, rfl, rfl⟩,
    ⟨(by change (∅ : Finset Nat) ⊆ _; exact Finset.empty_subset _),
      (by change (∅ : Finset Nat) ⊆ _; exact Finset.empty_subset _),
      (by change Disjoint (∅ : Finset Nat) ∅; simp), ?_,
      fun q member => by simp [Selection.commit] at member⟩,
    ⟨PUnit.unit, Subst.id signature, fun _ member => absurd member List.not_mem_nil⟩,
    fun b assignment _ => ⟨fun check member => absurd member List.not_mem_nil,
      fun q member => absurd member List.not_mem_nil⟩⟩
  apply Finset.disjoint_left.mpr
  intro o made old
  have same : o = out := by simpa [spawn, Selection.commit] using made
  have zero : o = 0 := by simpa [source] using old
  omega

theorem spawn_key (f : Firing Nat E spawnProgram source.frame) :
    identity.key f = identity.key (spawn 5 10) := by
  obtain ⟨r, member, extension, opening, selection, seen⟩ := f
  have rule : r = spawnRule := member
  subst r
  change (Presentation.key (signature := signature) (O := Nat) ⟨spawnRule, 0, 0⟩) = _
  rfl

theorem spawn_unique : (Bag.single (spawn 5 10)).AdmitsUniqueBy X source identity Set.univ := by
  refine ⟨⟨(Bag.admitsOwn_single X source _).mpr (spawn_admitted 5 10 (by decide)),
    fun key _ => Set.mem_univ key, List.nodup_singleton _, ?_⟩, rfl⟩
  intro f _ _
  simpa only [Bag.keysBy, Bag.single, List.map_singleton, Member.firing_ofFiring,
    List.mem_singleton] using spawn_key f

theorem renamed_copy_preserves_actual_unique :
    (renameRule Controls.shift.forward spawnRule ≠ spawnRule) ∧
      ∃ bag : Bag Nat E (spawnProgram ∪ renamedProgram Controls.shift spawnProgram) source.frame,
        bag.AdmitsUniqueBy X source identity Set.univ := by
  constructor
  · intro same
    have outputs := congrArg (β := List (Term signature))
      (fun rule : Rule (Terms (Term signature)) => rule.body.produce) same
    change [Term.var (σ := signature) 7] = [Term.var (σ := signature) 0] at outputs
    have value : (Term.var (σ := signature) 7) = Term.var (σ := signature) 0 := List.cons.inj outputs |>.1
    cases value
  · exact (copies_exist_every_unique Controls.shift Set.univ).2.mp ⟨Bag.single (spawn 5 10), spawn_unique⟩

theorem private_output_names_are_variants :
    ∃ names inverse : Nat → Nat,
      (readout source (spawn 5 10) (Subst.id signature)).map (UnificationRenaming.rename names) =
        readout source (spawn 6 11) (Subst.id signature) ∧
      (readout source (spawn 6 11) (Subst.id signature)).map (UnificationRenaming.rename inverse) =
        readout source (spawn 5 10) (Subst.id signature) ∧
      (∀ term ∈ readout source (spawn 5 10) (Subst.id signature),
        ∀ name ∈ term.freeVars, inverse (names name) = name) ∧
      (∀ term ∈ readout source (spawn 6 11) (Subst.id signature),
        ∀ name ∈ term.freeVars, names (inverse name) = name) :=
  principal_readouts_are_variants source _ _ (spawn_admitted 5 10 (by decide))
    (spawn_admitted 6 11 (by decide)) rfl _ _ FirstOrderLicence.Controls.empty_accepted
    FirstOrderLicence.Controls.empty_accepted

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricMatches.OpenControls
