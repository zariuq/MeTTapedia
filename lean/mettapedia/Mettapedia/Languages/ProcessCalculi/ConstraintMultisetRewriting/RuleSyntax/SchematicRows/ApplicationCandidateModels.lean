import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationCandidateFresh

/-!
# Compatible premise readings have an actual candidate model

The caller interpretation is retained on the entire source context. Private
models for the two datum readings and the application-rule assignment are
amalgamated in separate namespaces. Thus model existence is derived from the
actual premise readings, not postulated for the firing information.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationMachine

open Mettapedia.Logic.LP
open Presentation.Schematic (Tm rowSig)
open ApplicationSyntax

universe uOcc
variable {O : Type uOcc}

theorem candidate_model (judgmentTag arrowTag : Nat) (s : Store O) (caller : Subst rowSig)
    (known : X.Models (a := PUnit.unit) (b := PUnit.unit) caller s.knowledge)
    (major minor made : O) (majorPresent : major ∈ s.present) (minorPresent : minor ∈ s.present)
    (function argument domain codomain : Tm)
    (majorReading : (s.label major).ReadsAt X (b := PUnit.unit) caller
      (judgment judgmentTag function (arrow arrowTag domain codomain)))
    (minorReading : (s.label minor).ReadsAt X (b := PUnit.unit) caller
      (judgment judgmentTag argument domain)) :
    ∃ assignment : Subst rowSig,
      X.Models (a := PUnit.unit) (b := PUnit.unit) assignment
        ((candidate judgmentTag arrowTag (sourceBound s) s major minor made).information X) ∧
      (∀ term ∈ context s, assignment.applyTerm term = caller.applyTerm term) ∧
      assignment.applyTerm ((privateOpening (sourceBound s) 0).applyTerm
        (judgment judgmentTag (app (.var 0) (.var 3)) (.var 2))) =
          judgment judgmentTag (app function argument) codomain := by
  obtain ⟨firstLocals, firstRealizes⟩ := privateUse_realizes (sourceBound s) 1
    (s.label major) caller _ majorReading
  obtain ⟨secondLocals, secondRealizes⟩ := privateUse_realizes (sourceBound s) 2
    (s.label minor) caller _ minorReading
  let user := applicationAssignment function argument domain codomain
  let requested : Nat → Subst rowSig :=
    fun index => if index = 0 then user else if index = 1 then firstLocals else secondLocals
  let assignment := FreshNamespaces.combine (Equiv.refl Nat) (sourceBound s) caller requested
  have agrees : ∀ term ∈ context s, assignment.applyTerm term = caller.applyTerm term := by
    intro term inside
    exact FreshNamespaces.source_agrees (Equiv.refl Nat) (sourceBound s) caller requested term
      (context_below s term inside)
  have opened (index : Nat) (term : Tm) :
      assignment.applyTerm ((privateOpening (sourceBound s) index).applyTerm term) =
        (requested index).applyTerm term :=
    FreshNamespaces.combine_opening (Equiv.refl Nat) (sourceBound s) caller requested index term
  have userTerms (term : Tm) :
      assignment.applyTerm ((privateOpening (sourceBound s) 0).applyTerm term) = user.applyTerm term := by
    simpa only [requested, if_pos rfl] using opened 0 term
  have first := firstRealizes assignment
    (fun term inside => agrees term (ambient_in_context s major majorPresent term inside))
    (fun term => by simpa [requested] using opened 1 term)
  have second := secondRealizes assignment
    (fun term inside => agrees term (ambient_in_context s minor minorPresent term inside))
    (fun term => by simpa [requested] using opened 2 term)
  have old : X.Models (a := PUnit.unit) (b := PUnit.unit) assignment s.knowledge := by
    intro equation inside
    change assignment.applyTerm equation.1 = assignment.applyTerm equation.2
    have left := agrees equation.1 (mentioned_in_context s equation.1
      ((State.scope_mentions_iff s equation.1).mpr (Or.inl (List.mem_map_of_mem (f := Prod.fst) inside))))
    have right := agrees equation.2 (mentioned_in_context s equation.2
      ((State.scope_mentions_iff s equation.2).mpr
        (Or.inr (Or.inl (List.mem_map_of_mem (f := Prod.snd) inside)))))
    rw [left, right]
    exact known equation inside
  have matching : X.Models (a := PUnit.unit) (b := PUnit.unit) assignment
      [((privateOpening (sourceBound s) 0).applyTerm
          (judgment judgmentTag (.var 0) (arrow arrowTag (.var 1) (.var 2))),
          RowUse.value (Tm := RowTerms) X (Subst.id rowSig) (privateUse (sourceBound s) 1 (s.label major))),
        ((privateOpening (sourceBound s) 0).applyTerm (judgment judgmentTag (.var 3) (.var 1)),
          RowUse.value (Tm := RowTerms) X (Subst.id rowSig) (privateUse (sourceBound s) 2 (s.label minor)))] := by
    intro equation inside
    rcases List.mem_cons.mp inside with rfl | tail
    · change assignment.applyTerm ((privateOpening (sourceBound s) 0).applyTerm
          (judgment judgmentTag (.var 0) (arrow arrowTag (.var 1) (.var 2)))) =
        assignment.applyTerm (RowUse.value (Tm := RowTerms) X (Subst.id rowSig)
          (privateUse (sourceBound s) 1 (s.label major)))
      rw [userTerms, first.2]
      simp only [apply_judgment, apply_arrow]
      rfl
    · obtain rfl := List.mem_singleton.mp tail
      change assignment.applyTerm ((privateOpening (sourceBound s) 0).applyTerm
          (judgment judgmentTag (.var 3) (.var 1))) =
        assignment.applyTerm (RowUse.value (Tm := RowTerms) X (Subst.id rowSig)
          (privateUse (sourceBound s) 2 (s.label minor)))
      rw [userTerms, second.2]
      simp only [apply_judgment]
      rfl
  refine ⟨assignment, ?_, agrees, ?_⟩
  · rw [candidate_information]
    simp only [Interface.Frames.models_append]
    exact ⟨⟨old, first.1, second.1⟩, matching⟩
  · rw [userTerms]
    simp only [apply_judgment, apply_app]
    rfl

#print axioms candidate_model

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationMachine
