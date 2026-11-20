import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricValueStates
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Singletons
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Examples

/-!
# Actual CMR admission controls for the symmetric two-pattern repair

Profile: one first-order occurrence-bag store, ambient rules, one-match and
own-information complete/unique bags, guards after tells. Two equal payloads
at distinct identities are consumed once each. Swapping their assignment to
identical patterns is one symmetric match, not two matches.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricMatches.OperationalControls

open Mettapedia.Logic.LP
open OneFrame (Terms frames ext)
open FirstOrderLicence.Controls (signature c)

abbrev X := frames (FirstOrder.action signature)
abbrev E := ext (FirstOrder.action signature)

def pairRule : Rule (Terms (Term signature)) :=
  ⟨PUnit.unit, ⟨[c 1, c 1], [], [], [], [c 2]⟩, []⟩
def program : Program (Terms (Term signature)) := {pairRule}
def state : State (Terms (Term signature)) Nat := ⟨PUnit.unit, [], {0, 1}, fun _ => c 1⟩
def pairFiring (a b out : Nat) : Firing Nat E program state.frame :=
  ⟨pairRule, rfl, PUnit.unit, Subst.id signature, ⟨[a, b], [], [out]⟩, []⟩

theorem pair_information (a b out : Nat) :
    (pairFiring a b out).information X state = [(c 1, c 1), (c 1, c 1)] := rfl

theorem pair_ground : ∀ term ∈ pairRule.terms, ∀ assignment : Subst signature,
    (FirstOrder.action signature).apply assignment term = term := by
  intro term member assignment
  have listed : term ∈ [c 1, c 1, c 2] := member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl | rfl <;> rfl

theorem forward_admitted (out : Nat) (fresh : 2 ≤ out) : (pairFiring 0 1 out).Admits X state := by
  refine ⟨⟨Examples.fresh_of_ground (FirstOrder.action signature) state (pairFiring 0 1 out) pair_ground,
    (by change ([0, 1] : List Nat).Nodup; decide), List.nodup_singleton out, rfl, rfl, rfl, rfl⟩,
    ⟨(by change ({0, 1} : Finset Nat) ⊆ {0, 1}; exact fun _ h => h),
      (by change (∅ : Finset Nat) ⊆ _; exact Finset.empty_subset _),
      (by change Disjoint ({0, 1} : Finset Nat) ∅; simp),
      ?_, fun q member => by simp [Selection.commit] at member⟩,
    ⟨PUnit.unit, Subst.id signature, ?_⟩,
    fun b assignment _ => ⟨fun check member => absurd member List.not_mem_nil,
      fun q member => absurd member List.not_mem_nil⟩⟩
  · apply Finset.disjoint_left.mpr
    intro o made old
    have same : o = out := by simpa [pairFiring, Selection.commit] using made
    subst o
    have cases : out = 0 ∨ out = 1 := by simpa [state] using old
    omega
  · intro equation member
    rw [pair_information] at member
    have identical : equation = (c 1, c 1) := by simpa only [List.mem_cons,
      List.not_mem_nil, or_false, or_self] using member
    rw [identical]
    rfl

theorem backward_admitted : (pairFiring 1 0 10).Admits X state := by
  apply (reselect_admitted_iff state (pairFiring 0 1 10) [1, 0] []
    (List.Perm.swap _ _ []) (List.Perm.refl _) (List.Perm.swap _ _ []) (List.Perm.refl _)).mp
  exact forward_admitted 10 (by decide)

theorem two_ordered_keys_one_symmetric_class :
    MatchIdentity.ordered.key (pairFiring 0 1 10) ≠ MatchIdentity.ordered.key (pairFiring 1 0 10) ∧
      identity.key (pairFiring 0 1 10) = identity.key (pairFiring 1 0 10) := by
  constructor
  · intro same
    have taken := congrArg (fun key : Rule (Terms (Term signature)) × List Nat × List Nat => key.2.1) same
    exact (by decide : ([0, 1] : List Nat) ≠ [1, 0]) taken
  · exact key_eq_of_pair_perms _ _ rfl (List.Perm.swap _ _ []) (List.Perm.refl _)

theorem admitted_key (f : Firing Nat E program state.frame) (admitted : f.Admits X state) :
    identity.key f = identity.key (pairFiring 0 1 10) := by
  obtain ⟨r, member, extension, opening, selection, seen⟩ := f
  have rule : r = pairRule := member
  subst r
  let f : Firing Nat E program state.frame := ⟨pairRule, rfl, extension, opening, selection, seen⟩
  change f.Admits X state at admitted
  change identity.key f = identity.key (pairFiring 0 1 10)
  have length : f.selection.taken.length = 2 := admitted.1.2.2.2.1.symm
  have read : f.selection.read = [] := List.length_eq_zero_iff.mp admitted.1.2.2.2.2.1.symm
  obtain ⟨a, b, taken⟩ := List.length_eq_two.mp length
  have first : a = 0 ∨ a = 1 := by
    have inside := admitted.2.1.taken_subset (List.mem_toFinset.mpr (by simp [taken] : a ∈ f.selection.taken))
    simpa [state] using inside
  have second : b = 0 ∨ b = 1 := by
    have inside := admitted.2.1.taken_subset (List.mem_toFinset.mpr (by simp [taken] : b ∈ f.selection.taken))
    simpa [state] using inside
  have different : a ≠ b := by simpa [taken] using admitted.1.2.1
  rcases first with rfl | rfl <;> rcases second with rfl | rfl
  · exact False.elim (different rfl)
  · apply key_eq_of_pair_perms f (pairFiring 0 1 10) rfl
    · change ([c 1, c 1].zip f.selection.taken).Perm _
      rw [taken]
      exact List.Perm.refl _
    · change ([].zip f.selection.read : List (Term signature × Nat)).Perm _
      rw [read]
      exact List.Perm.refl _
  · apply key_eq_of_pair_perms f (pairFiring 0 1 10) rfl
    · change ([c 1, c 1].zip f.selection.taken).Perm _
      rw [taken]
      exact List.Perm.swap _ _ []
    · change ([].zip f.selection.read : List (Term signature × Nat)).Perm _
      rw [read]
      exact List.Perm.refl _
  · exact False.elim (different rfl)

theorem symmetric_every_unique :
    (Bag.single (pairFiring 0 1 10)).AdmitsUniqueBy X state identity Set.univ := by
  refine ⟨⟨(Bag.admitsOwn_single X state _).mpr (forward_admitted 10 (by decide)),
    fun key _ => Set.mem_univ key, ?_, ?_⟩, rfl⟩
  · exact List.nodup_singleton _
  · intro f _ admitted
    have same := admitted_key f admitted
    simpa only [Bag.keysBy, Bag.single, List.map_singleton, Member.firing_ofFiring,
      List.mem_singleton] using same

theorem fresh_results_are_not_literal_states :
    identity.key (pairFiring 0 1 10) = identity.key (pairFiring 0 1 11) ∧
      (pairFiring 0 1 10).result X state ≠ (pairFiring 0 1 11).result X state := by
  refine ⟨rfl, ?_⟩
  intro same
  have present := congrArg (fun s : State (Terms (Term signature)) Nat => s.present) same
  exact (by decide : ((pairFiring 0 1 10).result X state).present ≠
    ((pairFiring 0 1 11).result X state).present) present

theorem fresh_results_are_equivalent :
    ∃ rename : Equiv.Perm Nat, (∀ o ∈ state.present, rename o = o) ∧
      (pairFiring 0 1 10).selection.made.map rename = (pairFiring 0 1 11).selection.made ∧
      ((pairFiring 0 1 10).result X state).present.map rename.toEmbedding =
        ((pairFiring 0 1 11).result X state).present :=
  same_class_occurrence_renaming state _ _ (forward_admitted 10 (by decide))
    (forward_admitted 11 (by decide)) rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricMatches.OperationalControls
