import Mettapedia.Logic.TierZero.Kernel2.AdmissionOrigins

/-!
# Why the admission-origin theorem retains local hypotheses

A local declaration can supply a premise that no admitted rule concludes.
The existing kernel permits such a claim. Erasing the local declaration from
the mathematical reading would then assert a stronger closed theorem.

This control concerns the rule-only basis. A guest logic may separately
justify discharge, for example using an inhabitation theorem. Such evidence
must be included in that guest's adequacy argument.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Kernel2.AdmissionOrigins.LocalControl

def fromObject : Rule := ⟨1, [.judg (pjd "object" [pv 0])], pjd "witness" []⟩

def localClaim : Claim String :=
  ⟨"local-witness", [], [.name], [], [("object", 0)], [], pjd "witness" [], [],
    [⟨0, "from-object", [.loc 0]⟩], .node 0⟩

def program : List (ClientAct String) :=
  [ .sendAdmission (.judgment "object" 1),
    .sendAdmission (.sort "object"),
    .sendAdmission (.judgment "witness" 0),
    .sendAdmission (.rule "from-object" fromObject),
    .sendClaim localClaim ]

theorem local_claim_is_accepted :
    (observeProgram 8 program).2.T = ["local-witness"] := by decide +kernel

theorem local_claim_is_promoted :
    (observeProgram 8 program).2.L.rules.map Prod.fst = ["from-object", "local-witness"] := by
  decide +kernel

theorem actual_rule_basis :
    (observeProgram 8 program).1 = [("from-object", fromObject)] := rfl

theorem local_claim_is_outside_the_closed_interface : localClaim.locals ≠ [] := by decide

theorem fromObject_singleton (frame : Frame) (term : Tm) :
    fromObject.instance frame [term] = some ([jd "object" [term]], jd "witness" []) := rfl

theorem fromObject_instance {frame : Frame} {arguments premises : List Tm} {conclusion : Tm}
    (instanceOf : fromObject.instance frame arguments = some (premises, conclusion)) :
    ∃ term, arguments = [term] ∧ premises = [jd "object" [term]] ∧ conclusion = jd "witness" [] := by
  have length : arguments.length = 1 := by
    unfold Rule.instance at instanceOf
    split at instanceOf
    · assumption
    · cases instanceOf
  obtain ⟨term, rfl⟩ := List.length_eq_one_iff.mp length
  rw [fromObject_singleton] at instanceOf
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj instanceOf)
  exact ⟨term, rfl, rfl, rfl⟩

theorem object_not_given (term : Tm) : ¬IsGiven (jd "object" [term]) := by
  rintro ⟨other, same⟩
  simp [givenTm, jd, ex, sym, flds] at same

theorem witness_not_given : ¬IsGiven (jd "witness" []) := by
  rintro ⟨other, same⟩
  simp [givenTm, jd, ex, sym, flds] at same

/-- Even arbitrary cited data cannot replace the local logical assumption. -/
theorem local_assumption_cannot_be_erased (frame : Frame) (givens : List Tm)
    (given : ∀ term ∈ givens, IsGiven term) :
    ¬Derivable (basisPres [("from-object", fromObject)] frame) givens (jd "witness" []) := by
  intro derivation
  apply witness_not_given
  apply basis_sound IsGiven _ given derivation
  intro position arguments premises conclusion instanceOf children
  fin_cases position
  obtain ⟨term, _, rfl, rfl⟩ := fromObject_instance instanceOf
  exact False.elim (object_not_given term (children _ (by simp)))

def inhabitant : Rule := ⟨0, [], pjd "object" [psym "seed"]⟩

/-- A profile that actually supplies an inhabitant can prove the closed
conclusion. The missing premise is discharged by a concrete two-rule proof. -/
theorem an_inhabited_profile_proves_the_closed_conclusion (frame : Frame) :
    Derivable (basisPres [("from-object", fromObject), ("inhabitant", inhabitant)] frame)
      [] (jd "witness" []) := by
  refine Derivable.rule
    (P := basisPres [("from-object", fromObject), ("inhabitant", inhabitant)] frame)
    (r := ⟨0, by decide⟩) (a := [sym "seed"])
    (ps := [jd "object" [sym "seed"]]) rfl ?_
  intro premise member _
  obtain rfl := List.mem_singleton.mp member
  exact Derivable.rule
    (P := basisPres [("from-object", fromObject), ("inhabitant", inhabitant)] frame)
    (r := ⟨1, by decide⟩) (a := []) (ps := []) rfl (by simp)

end Mettapedia.Logic.TierZero.Kernel2.AdmissionOrigins.LocalControl
