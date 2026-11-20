import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadDirectCandidate
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ReadModels
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.Substitution
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Atoms

/-!
# Direct-read models and actual admission

A datum reading supplies a model of the independently constructed direct
firing while retaining the whole caller interface. Conversely every such
result model reads the selected datum at that caller. Resource admission is
derived separately from presence and the fresh output identity. These laws
refer to the direct schematic-row step, not to a held-rule expansion.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadDirect

open Mettapedia.Logic.LP
open Presentation.Schematic (Tm rowSig)
open ApplicationMachine (RowTerms Store X E privateOpening privateUse sourceBound)

universe uOcc
variable {O : Type uOcc}

theorem candidate_model (s : Store O) (caller : Subst rowSig)
    (known : X.Models (a := s.frame) (b := PUnit.unit) caller s.knowledge)
    (selected made : O) (present : selected ∈ s.present) (value : Tm)
    (reading : (s.label selected).ReadsAt X (b := PUnit.unit) caller value) :
    ∃ point : Subst rowSig,
      X.Models (a := s.frame) (b := PUnit.unit) point
        ((candidate (sourceBound s) s selected made).information X) ∧
      (∀ term, s.scope.Mentions term → point.applyTerm term = caller.applyTerm term) ∧
      point.applyTerm ((privateOpening (sourceBound s) 0).applyTerm (.var 0)) = value := by
  obtain ⟨datumLocals, realizes⟩ := ApplicationMachine.privateUse_realizes
    (sourceBound s) 1 (s.label selected) caller value reading
  let user : Subst rowSig := fun _ => value
  let requested : Nat → Subst rowSig := fun index => if index = 0 then user else datumLocals
  let point := FreshNamespaces.combine (Equiv.refl Nat) (sourceBound s) caller requested
  have agrees : ∀ term ∈ ApplicationMachine.context s,
      point.applyTerm term = caller.applyTerm term := by
    intro term inside
    exact FreshNamespaces.source_agrees (Equiv.refl Nat) (sourceBound s) caller requested term
      (ApplicationMachine.context_below s term inside)
  have opened (index : Nat) (term : Tm) :
      point.applyTerm ((privateOpening (sourceBound s) index).applyTerm term) =
        (requested index).applyTerm term :=
    FreshNamespaces.combine_opening (Equiv.refl Nat) (sourceBound s) caller requested index term
  have userTerms (term : Tm) :
      point.applyTerm ((privateOpening (sourceBound s) 0).applyTerm term) = user.applyTerm term := by
    simpa only [requested, if_pos rfl] using opened 0 term
  have datum := realizes point
    (fun term inside => agrees term (ApplicationMachine.ambient_in_context s selected present term inside))
    (fun term => by simpa [requested] using opened 1 term)
  have old : X.Models (a := s.frame) (b := PUnit.unit) point s.knowledge := by
    intro equation member
    change point.applyTerm equation.1 = point.applyTerm equation.2
    rw [agrees equation.1 (ApplicationMachine.mentioned_in_context s equation.1
      ((State.scope_mentions_iff s equation.1).mpr (Or.inl (List.mem_map_of_mem (f := Prod.fst) member)))),
      agrees equation.2 (ApplicationMachine.mentioned_in_context s equation.2
        ((State.scope_mentions_iff s equation.2).mpr
          (Or.inr (Or.inl (List.mem_map_of_mem (f := Prod.snd) member)))))]
    exact known equation member
  have matching : X.Models (a := s.frame) (b := PUnit.unit) point
      [((privateOpening (sourceBound s) 0).applyTerm (.var 0),
        RowUse.value (Tm := RowTerms) X (Subst.id rowSig) (privateUse (sourceBound s) 1 (s.label selected)))] := by
    intro equation member
    obtain rfl := List.mem_singleton.mp member
    change point.applyTerm ((privateOpening (sourceBound s) 0).applyTerm (.var 0)) =
      point.applyTerm (RowUse.value (Tm := RowTerms) X (Subst.id rowSig)
        (privateUse (sourceBound s) 1 (s.label selected)))
    rw [userTerms, datum.2]
    rfl
  refine ⟨point, ?_, fun term mentioned =>
    agrees term (ApplicationMachine.mentioned_in_context s term mentioned), ?_⟩
  · rw [candidate_information]
    exact (Interface.Frames.models_append _ _ _).mpr
      ⟨(Interface.Frames.models_append _ _ _).mpr ⟨old, datum.1⟩, matching⟩
  · exact userTerms (.var 0)

theorem reading_of_model (bound : Nat) (s : Store O) (selected made : O)
    (present : selected ∈ s.present) (shapes : (candidate bound s selected made).Shapes X)
    (point : Subst rowSig)
    (solved : X.Models (a := s.frame) (b := PUnit.unit) point
      ((candidate bound s selected made).information X))
    (caller : Subst rowSig)
    (agrees : ∀ term, s.scope.Mentions term → point.applyTerm term = caller.applyTerm term) :
    (s.label selected).ReadsAt X (b := PUnit.unit) caller
      (point.applyTerm ((privateOpening bound 0).applyTerm (.var 0))) := by
  let selectedUse : PackedUse RowTerms (fun _ _ : PUnit => Subst rowSig) s.frame s.frame :=
    ⟨s.label selected, privateUse bound 1 (s.label selected)⟩
  have member : selectedUse ∈ (candidate bound s selected made).uses := by
    rw [candidate_uses]
    exact List.mem_singleton_self _
  have datum := (candidate bound s selected made).selected_reading (b := PUnit.unit)
    X point solved shapes selectedUse member
  change (s.label selected).ReadsAt X (b := PUnit.unit) (point.comp (Subst.id rowSig))
    (point.applyTerm (RowUse.value (Tm := RowTerms) X (Subst.id rowSig)
      (privateUse bound 1 (s.label selected)))) at datum
  rw [Subst.comp_id_right] at datum
  have inInformation : ((privateOpening bound 0).applyTerm (.var 0),
      RowUse.value (Tm := RowTerms) X (Subst.id rowSig) (privateUse bound 1 (s.label selected))) ∈
      (candidate bound s selected made).information X := by
    rw [candidate_information]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have same := solved _ inInformation
  change point.applyTerm ((privateOpening bound 0).applyTerm (.var 0)) =
    point.applyTerm (RowUse.value (Tm := RowTerms) X (Subst.id rowSig)
      (privateUse bound 1 (s.label selected))) at same
  rw [← same] at datum
  apply (Row.readsAt_source_congr (a := s.frame) (b := PUnit.unit) X (s.label selected)
    point caller (fun term inside => agrees term
      ((State.scope_mentions_iff s term).mpr (Or.inr (Or.inr ⟨selected, present, inside⟩)))) _).mp
  exact datum

theorem candidate_shapes (s : Store O) (selected made : O)
    (wellFormed : (s.label selected).WellFormed) :
    (candidate (sourceBound s) s selected made).Shapes X := by
  refine ⟨candidate_fresh s selected made, List.nodup_nil, List.nodup_singleton made,
    rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro selectedUse member
    rw [candidate_uses] at member
    obtain rfl := List.mem_singleton.mp member
    exact wellFormed
  · intro output member
    cases member

variable [DecidableEq O]

theorem candidate_admitted (s : Store O) (caller : Subst rowSig)
    (known : X.Models (a := s.frame) (b := PUnit.unit) caller s.knowledge)
    (selected made : O) (present : selected ∈ s.present) (fresh : made ∉ s.present) (value : Tm)
    (reading : (s.label selected).ReadsAt X (b := PUnit.unit) caller value) :
    (candidate (sourceBound s) s selected made).Admits X := by
  obtain ⟨point, solved, _, _⟩ := candidate_model s caller known selected made present value reading
  refine ⟨candidate_shapes s selected made
    (ApplicationMachine.reading_wellFormed _ caller value reading), ?_, ⟨PUnit.unit, point, solved⟩, ?_⟩
  · apply RuleOccurrences.enabled_of
    · intro o member
      cases member
    · intro o member
      obtain rfl := List.mem_singleton.mp member
      exact present
    · intro o member
      cases member
    · intro o member
      obtain rfl := List.mem_singleton.mp member
      exact fresh
  · intro target assignment _
    constructor
    · intro check member
      cases member
    · intro query member
      cases member

theorem reading_iff_result_models (s : Store O) (caller : Subst rowSig)
    (known : X.Models (a := s.frame) (b := PUnit.unit) caller s.knowledge)
    (selected made : O) (present : selected ∈ s.present) (fresh : made ∉ s.present) (value : Tm) :
    (s.label selected).ReadsAt X (b := PUnit.unit) caller value ↔
      ∃ _admitted : (candidate (sourceBound s) s selected made).Admits X,
        ∃ point : Subst rowSig,
          X.Models (a := s.frame) (b := PUnit.unit) point
            ((candidate (sourceBound s) s selected made).result X).knowledge ∧
          (∀ term, s.scope.Mentions term → point.applyTerm term = caller.applyTerm term) ∧
          point.applyTerm ((privateOpening (sourceBound s) 0).applyTerm (.var 0)) = value := by
  constructor
  · intro reading
    exact ⟨candidate_admitted s caller known selected made present fresh value reading,
      candidate_model s caller known selected made present value reading⟩
  · rintro ⟨admitted, point, solved, agrees, output⟩
    have reading := reading_of_model (sourceBound s) s selected made present admitted.1 point solved caller agrees
    rwa [output] at reading

theorem reading_iff_actual_result (s : Store O) (caller : Subst rowSig)
    (known : X.Models (a := s.frame) (b := PUnit.unit) caller s.knowledge)
    (selected made : O) (present : selected ∈ s.present) (fresh : made ∉ s.present) (value : Tm) :
    (s.label selected).ReadsAt X (b := PUnit.unit) caller value ↔
      ∃ _admitted : (candidate (sourceBound s) s selected made).Admits X,
        ∃ point : Subst rowSig,
          X.Models (a := s.frame) (b := PUnit.unit) point
            ((candidate (sourceBound s) s selected made).result X).knowledge ∧
          (∀ term, s.scope.Mentions term → point.applyTerm term = caller.applyTerm term) ∧
          (((candidate (sourceBound s) s selected made).result X).label made).ReadsAt X
            (b := PUnit.unit) point value := by
  constructor
  · intro reading
    obtain ⟨admitted, point, solved, agrees, output⟩ :=
      (reading_iff_result_models s caller known selected made present fresh value).mp reading
    refine ⟨admitted, point, solved, agrees, ?_⟩
    rw [result_label_made]
    exact output
  · rintro ⟨admitted, point, solved, agrees, output⟩
    apply (reading_iff_result_models s caller known selected made present fresh value).mpr
    refine ⟨admitted, point, solved, agrees, ?_⟩
    rw [result_label_made] at output
    exact output

abbrev machine := (singleFiring X O E program).toStep

noncomputable def execution (bound : Nat) (s : Store O) (selected made : O)
    (admitted : (candidate bound s selected made).Admits X) : (machine (O := O)).Run s :=
  .cons (candidate bound s selected made) admitted (.nil _)

theorem execution_last (bound : Nat) (s : Store O) (selected made : O)
    (admitted : (candidate bound s selected made).Admits X) :
    (execution bound s selected made admitted).last = (candidate bound s selected made).result X := rfl

theorem execution_length (bound : Nat) (s : Store O) (selected made : O)
    (admitted : (candidate bound s selected made).Admits X) :
    (execution bound s selected made admitted).word.length = 1 := rfl

#print axioms candidate_model
#print axioms reading_of_model
#print axioms candidate_shapes
#print axioms candidate_admitted
#print axioms reading_iff_result_models
#print axioms reading_iff_actual_result
#print axioms execution_length

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadDirect
