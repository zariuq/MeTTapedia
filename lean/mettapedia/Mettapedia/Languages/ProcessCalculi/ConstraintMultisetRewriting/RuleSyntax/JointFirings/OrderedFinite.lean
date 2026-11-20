import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricFinite
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.FiniteMatchIdentity

/-!
# Ordered-key representatives from the shared finite CMR selection enumerator

Profile: finite ambient program, one finite occurrence-bag store, the existing
one-match judgment after tells. Ordered identity is deliberately not quotiented
by local renaming or identical-pattern permutations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricMatches

open Mettapedia.Logic.LP
open OneFrame (Terms frames ext)

variable {signature : LPSignature} {O : Type*} [DecidableEq O]
  {P : Program (Terms (Term signature))}

def orderedCandidates (rules : List (Rule (Terms (Term signature)))) (rows : List O) :
    List (Rule (Terms (Term signature)) × List O × List O) :=
  rules.flatMap fun rule =>
    (selections rows rule.body.take.length).flatMap fun taken =>
      (selections rows rule.body.read.length).map fun read => (rule, taken, read)

theorem admitted_ordered_key_is_candidate (s : State (Terms (Term signature)) O)
    (rules : List (Rule (Terms (Term signature)))) (covers : ∀ rule ∈ P, rule ∈ rules)
    (f : Firing O (ext (FirstOrder.action signature)) P s.frame)
    (admitted : f.Admits (frames (FirstOrder.action signature)) s) :
    firingKey f ∈ orderedCandidates rules s.present.toList := by
  apply List.mem_flatMap.mpr
  refine ⟨f.rule, covers f.rule f.member, List.mem_flatMap.mpr ?_⟩
  refine ⟨f.selection.taken, ?_, List.mem_map.mpr ⟨f.selection.read, ?_, rfl⟩⟩
  · apply (mem_selections _ _ _).mpr
    exact ⟨admitted.1.2.2.2.1.symm, fun o member =>
      Finset.mem_toList.mpr (admitted.2.1.taken_subset (List.mem_toFinset.mpr member))⟩
  · apply (mem_selections _ _ _).mpr
    exact ⟨admitted.1.2.2.2.2.1.symm, fun o member =>
      Finset.mem_toList.mpr (admitted.2.1.kept_subset (List.mem_toFinset.mpr member))⟩

theorem finite_ordered_representatives (s : State (Terms (Term signature)) O)
    (rules : List (Rule (Terms (Term signature)))) (covers : ∀ rule ∈ P, rule ∈ rules) :
    ∃ representatives : List (Firing O (ext (FirstOrder.action signature)) P s.frame),
      (representatives.map firingKey).Nodup ∧
      (∀ f ∈ representatives, f.Admits (frames (FirstOrder.action signature)) s) ∧
      ∀ f : Firing O (ext (FirstOrder.action signature)) P s.frame,
        f.Admits (frames (FirstOrder.action signature)) s →
          firingKey f ∈ representatives.map firingKey :=
  MatchIdentity.finite_representatives (frames (FirstOrder.action signature)) s MatchIdentity.ordered
    (orderedCandidates rules s.present.toList) (admitted_ordered_key_is_candidate s rules covers)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricMatches
