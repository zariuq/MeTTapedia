import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreCompletion
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.OrderedFinite
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Maximal

/-! # Complete ordered bags and the existing maximal discipline -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreSyntax

open Mettapedia.Logic.LP
open OneFrame (Terms frames ext)
open JointFirings

variable {signature : LPSignature} [DecidableEq signature.vars]
  [DecidableEq signature.constants] [DecidableEq signature.functionSymbols]
  {P : Program (Terms (Term signature))}

omit [DecidableEq signature.vars] [DecidableEq signature.constants] [DecidableEq signature.functionSymbols] in
theorem reopenBag_ordered_keys (slots : signature.vars ≃ ℕ) (firings : List (F (P := P))) :
    (reopenBag slots firings).members.map Member.key = firings.map firingKey := by
  change (firings.zipIdx.map fun entry => reopenedMember slots entry.2 entry.1).map Member.key = _
  rw [List.map_map]
  calc
    _ = firings.zipIdx.map (fun entry => firingKey entry.1) := by
      apply List.map_congr_left
      intro entry _
      exact reopen_ordered_key slots entry.2 entry.1
    _ = (firings.zipIdx.map Prod.fst).map firingKey := by
      rw [List.map_map]
      apply List.map_congr_left
      intro entry _
      rfl
    _ = _ := by rw [List.zipIdx_map_fst]

omit [DecidableEq signature.vars] [DecidableEq signature.constants] [DecidableEq signature.functionSymbols] in
theorem symmetric_of_ordered (first second : F (P := P)) (same : firingKey first = firingKey second) :
    SymmetricMatches.identity.key first = SymmetricMatches.identity.key second := by
  have rule := congrArg Prod.fst same
  have takes := congrArg (fun key => key.2.1) same
  have reads := congrArg (fun key => key.2.2) same
  apply congrArg SymmetricMatches.Presentation.key
  simp only [SymmetricMatches.presentation]
  change first.rule = second.rule at rule
  change first.selection.taken = second.selection.taken at takes
  change first.selection.read = second.selection.read at reads
  rw [rule, takes, reads]

theorem exists_ordered_every_bag (slots : signature.vars ≃ ℕ) (rows : Finset (Term signature))
    (ground : GroundRows rows) (pure : ∀ rule ∈ P, Propagates rule)
    (rules : List (Rule (Terms (Term signature)))) (covers : ∀ rule ∈ P, rule ∈ rules) :
    ∃ bag : SetStore.Candidate P, bag.AdmitsEvery X (SetStore.represent rows) P := by
  obtain ⟨representatives, distinct, admitted, complete⟩ :=
    SymmetricMatches.finite_ordered_representatives (SetStore.represent rows) rules covers
  refine ⟨reopenBag slots representatives, reopenBag_own slots rows ground pure representatives admitted,
    (fun m _ => m.member), ?_, ?_⟩
  · change ((reopenBag slots representatives).members.map Member.key).Nodup
    rw [reopenBag_ordered_keys]
    exact distinct
  · intro f _ yes
    rw [reopenBag_ordered_keys]
    exact complete f yes

theorem ordered_complete_is_symmetric_complete (rows : Finset (Term signature)) (bag : SetStore.Candidate P)
    (complete : bag.Complete X (SetStore.represent rows) P) :
    bag.CompleteBy X (SetStore.represent rows) SymmetricMatches.identity Set.univ := by
  intro f _ yes
  obtain ⟨member, inside, same⟩ := List.mem_map.mp (complete f f.member yes)
  apply List.mem_map.mpr
  refine ⟨member, inside, ?_⟩
  exact symmetric_of_ordered member.firing f same

theorem ordered_every_is_maximal (rows : Finset (Term signature)) (ground : GroundRows rows)
    (pure : ∀ rule ∈ P, Propagates rule) (bag : SetStore.Candidate P)
    (every : bag.AdmitsEvery X (SetStore.represent rows) P) :
    bag.AdmitsMaximal X (SetStore.represent rows) := by
  refine ⟨every.admits, every.2.2.1, ?_⟩
  intro other admitted _ _ key member
  obtain ⟨m, inside, rfl⟩ := List.mem_map.mp member
  obtain ⟨⟨⟩, members⟩ := other
  have own := admitsOwn_of_fixed (FirstOrder.action signature)
    (fun term mentioned assignment => source_fixed rows ground term mentioned assignment)
    (fun m _ => (pure m.rule m.member).positive) admitted
  have yes := Bag.admits_member X (fun _ _ => ⟨Subst.id signature⟩) own inside
  exact every.2.2.2 m.firing m.member yes

theorem exists_maximal_complete_bag (slots : signature.vars ≃ ℕ) (rows : Finset (Term signature))
    (ground : GroundRows rows) (pure : ∀ rule ∈ P, Propagates rule)
    (rules : List (Rule (Terms (Term signature)))) (covers : ∀ rule ∈ P, rule ∈ rules) :
    ∃ bag : SetStore.Candidate P,
      bag.AdmitsOwn X (SetStore.represent rows) ∧ bag.AdmitsMaximal X (SetStore.represent rows) ∧
        bag.CompleteBy X (SetStore.represent rows) SymmetricMatches.identity Set.univ := by
  obtain ⟨bag, every⟩ := exists_ordered_every_bag slots rows ground pure rules covers
  exact ⟨bag, every.1, ordered_every_is_maximal rows ground pure bag every,
    ordered_complete_is_symmetric_complete rows bag every.2.2.2⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreSyntax
