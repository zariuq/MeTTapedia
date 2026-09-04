import Mettapedia.Languages.ProcessCalculi.MORK.ComputablePatternMonotonicity

/-!
# Monotonicity interfaces for compatible computable inputs

These compact corollaries keep target-specific simulations from reopening the
recursive positive matcher merely to extend an execution space with passive
rows.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK

theorem cmatchInputSpec_compat_mono
    (initial : Subst) (small large : CSpace) (patterns : List Atom)
    (included : ∀ atom ∈ small, atom ∈ large)
    {substitution : Subst}
    (member : substitution ∈
      (cmatchInputSpec initial small
        (.compat (mkPattern patterns))).map Prod.fst) :
    substitution ∈
      (cmatchInputSpec initial large
        (.compat (mkPattern patterns))).map Prod.fst := by
  rw [List.mem_map] at member ⊢
  obtain ⟨⟨matchedSubstitution, consumed⟩, matched, rfl⟩ := member
  refine ⟨(matchedSubstitution, consumed), ?_, rfl⟩
  exact cmatchPattern_mono initial small large (mkPattern patterns) included
    matchedSubstitution consumed matched

/-- Appending a passive frame after a space containing the selected
executable preserves every compatible matcher row in the scheduler's
remove-before-read presentation. -/
theorem cmatchInputSpec_compat_append_after_erase
    (initial : Subst) (selected : Atom) (space extra : CSpace)
    (patterns : List Atom) (shell : selected ∈ space)
    {substitution : Subst}
    (member : substitution ∈
      (cmatchInputSpec initial (selected :: space.erase selected)
        (.compat (mkPattern patterns))).map Prod.fst) :
    substitution ∈
      (cmatchInputSpec initial
        (selected :: (space ++ extra).erase selected)
        (.compat (mkPattern patterns))).map Prod.fst := by
  have liveExact :
      (space ++ extra).erase selected = space.erase selected ++ extra :=
    List.erase_append_left extra shell
  rw [liveExact]
  exact cmatchInputSpec_compat_mono initial
    (selected :: space.erase selected)
    (selected :: (space.erase selected ++ extra)) patterns
    (fun atom atomMember => by
      simp only [List.mem_cons] at atomMember ⊢
      rcases atomMember with rfl | atomMember
      · exact Or.inl rfl
      · exact Or.inr (List.mem_append_left _ atomMember))
    member

#print axioms cmatchInputSpec_compat_mono
#print axioms cmatchInputSpec_compat_append_after_erase

end Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable
