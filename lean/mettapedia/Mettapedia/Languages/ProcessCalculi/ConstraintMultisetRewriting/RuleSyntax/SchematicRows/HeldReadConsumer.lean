import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldCopyConsumer

/-!
# Models and admission of the private materialized-row consumer

The consumer is an actual held-rule firing. Its only new equation identifies
its fresh local value with the selected temporary row. Every model of the
source extends to a model of this equation, without changing any term the
source mentions. Conversely every result model restricts to a source model.
Physical availability and the fresh output occurrence remain separate from
these model laws.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadConsumer

open Mettapedia.Logic.LP
open OneFrame (Terms frames ext)
open Presentation.Schematic (Tm rowSig)
open RuleOccurrences HeldCopyConsumer

universe uOcc uR uC uZ
variable {O : Type uOcc} {R : Type uR} {C : Type uC} {Z : Type uZ}
  (codes : Codes RowTerms C Z) (s : RState RowTerms O R C Z)
  (code : C) (temporary output : O)

theorem information (declared : codes.unfold code = readerSpec) :
    (consumer codes s code temporary output).information X = s.knowledge ++
      [((consumer codes s code temporary output).opening.applyTerm (.var 0), s.label temporary)] := by
  have specification := consumer_spec codes s code temporary output declared
  have transport : ∀ first second : Spec RowTerms C Z, first = second →
      HEq (first.body, first.params) (second.body, second.params) := by
    intro first second same
    cases same
    rfl
  have fields : ((consumer codes s code temporary output).spec.body,
      (consumer codes s code temporary output).spec.params) =
      ((readerSpec (C := C) (Z := Z)).body, (readerSpec (C := C) (Z := Z)).params) :=
    eq_of_heq (transport _ _ specification)
  have takes : (consumer codes s code temporary output).spec.body.take = [(.var 0 : Tm)] :=
    congrArg (fun parts : RuleInstance Tm × List Tm => parts.1.take) fields
  have reads : (consumer codes s code temporary output).spec.body.read = [] :=
    congrArg (fun parts : RuleInstance Tm × List Tm => parts.1.read) fields
  have tells : (consumer codes s code temporary output).spec.body.tell = [] :=
    congrArg (fun parts : RuleInstance Tm × List Tm => parts.1.tell) fields
  have params : (consumer codes s code temporary output).spec.params = [] :=
    congrArg (fun parts : RuleInstance Tm × List Tm => parts.2) fields
  unfold RFiring.information RFiring.env RFiring.base
  unfold RuleSyntax.Firing.information RuleSyntax.Firing.matching
    RuleSyntax.Firing.opened RuleSyntax.Firing.row
  dsimp only [RuleInstance.map]
  rw [takes, reads, tells, params]
  change (X.applyStore (X.id s.frame) s.knowledge ++
    [((consumer codes s code temporary output).opening.applyTerm (.var 0),
      X.act (X.id s.frame) (s.label temporary))] ++ [] ++ []) ++ [] = _
  simp only [Interface.Frames.applyStore_id, X.act_id, List.append_nil]

theorem models_iff (declared : codes.unfold code = readerSpec) (point : Subst rowSig) :
    X.Models (a := s.frame) (b := PUnit.unit) point
        ((consumer codes s code temporary output).information X) ↔
      X.Models (a := s.frame) (b := PUnit.unit) point s.knowledge ∧
        point.applyTerm ((consumer codes s code temporary output).opening.applyTerm (.var 0)) =
          point.applyTerm (s.label temporary) := by
  rw [information codes s code temporary output declared,
    Interface.Frames.models_append]
  constructor
  · rintro ⟨known, matched⟩
    exact ⟨known, matched _ (List.mem_singleton_self _)⟩
  · rintro ⟨known, matched⟩
    refine ⟨known, ?_⟩
    intro equation member
    obtain rfl := List.mem_singleton.mp member
    exact matched

theorem extends_model (declared : codes.unfold code = readerSpec)
    (present : temporary ∈ s.present) (caller : Subst rowSig)
    (known : X.Models (a := s.frame) (b := PUnit.unit) caller s.knowledge) :
    ∃ point : Subst rowSig,
      X.Models (a := s.frame) (b := PUnit.unit) point
        ((consumer codes s code temporary output).information X) ∧
      (∀ term, s.Mentions term → point.applyTerm term = caller.applyTerm term) ∧
      point.applyTerm ((consumer codes s code temporary output).opening.applyTerm (.var 0)) =
        caller.applyTerm (s.label temporary) := by
  let locals : Subst rowSig := fun _ => caller.applyTerm (s.label temporary)
  obtain ⟨point, source, localTerms⟩ :=
    consumer_fresh codes s code temporary output PUnit.unit caller locals
  have kept : ∀ term, s.Mentions term → point.applyTerm term = caller.applyTerm term := by
    intro term mentioned
    have sourceTerm := source term mentioned
    change point.applyTerm ((Subst.id rowSig).applyTerm term) = caller.applyTerm term
      at sourceTerm
    simpa only [Subst.applyTerm_id] using sourceTerm
  have localMember : (.var 0 : Tm) ∈ (consumer codes s code temporary output).spec.terms := by
    rw [consumer_spec codes s code temporary output declared]
    simp [Spec.terms, readerSpec, readerRule, Rule.terms]
  have copied : point.applyTerm ((consumer codes s code temporary output).opening.applyTerm (.var 0)) =
      caller.applyTerm (s.label temporary) :=
    localTerms (.var 0) localMember
  refine ⟨point, (models_iff codes s code temporary output declared point).mpr ⟨?_, ?_⟩,
    kept, copied⟩
  · intro equation member
    change point.applyTerm equation.1 = point.applyTerm equation.2
    rw [kept equation.1 (Or.inl (Or.inl (List.mem_map_of_mem member))),
      kept equation.2 (Or.inl (Or.inr (Or.inl (List.mem_map_of_mem member))))]
    exact known equation member
  · exact copied.trans (kept (s.label temporary)
      (Or.inl (Or.inr (Or.inr ⟨temporary, present, rfl⟩)))).symm

theorem shapes (ambient : Set C) (declared : codes.unfold code = readerSpec)
    (available : code ∈ ambient) :
    (consumer codes s code temporary output).Shapes X ambient := by
  refine ⟨consumer_fresh codes s code temporary output, ?_, ?_⟩
  · unfold RFiring.RowShapes
    rw [consumer_spec codes s code temporary output declared]
    exact ⟨List.nodup_singleton temporary, List.nodup_singleton output, rfl, rfl, rfl, rfl⟩
  · refine {
      available := available
      arguments := ?_
      installed := ?_
      madeNodup := List.nodup_nil
      madeLength := ?_
      madeNew := ?_
      removed := ?_
      removedNodup := List.nodup_nil
      removedHeld := ?_
      published := ?_ }
    · rw [consumer_spec codes s code temporary output declared]
      rfl
    · rw [consumer_spec codes s code temporary output declared]
      rfl
    · rw [consumer_spec codes s code temporary output declared]
      rfl
    · intro occurrence member
      cases member
    · rw [consumer_spec codes s code temporary output declared]
      rfl
    · intro pair member
      rw [consumer_spec codes s code temporary output declared] at member
      cases member
    · rw [consumer_spec codes s code temporary output declared]
      rfl

variable [DecidableEq O]

theorem admitted (ambient : Set C) (declared : codes.unfold code = readerSpec)
    (available : code ∈ ambient) (present : temporary ∈ s.present) (fresh : output ∉ s.present)
    (caller : Subst rowSig)
    (known : X.Models (a := s.frame) (b := PUnit.unit) caller s.knowledge) :
    (consumer codes s code temporary output).Admits X ambient := by
  obtain ⟨point, solved, _, _⟩ :=
    extends_model codes s code temporary output declared present caller known
  refine ⟨shapes codes s code temporary output ambient declared available, ?_,
    ⟨PUnit.unit, point, solved⟩, ?_⟩
  · apply enabled_of
    · intro occurrence member
      obtain rfl := List.mem_singleton.mp member
      exact present
    · intro occurrence member
      cases member
    · intro occurrence _ member
      cases member
    · intro occurrence member
      obtain rfl := List.mem_singleton.mp member
      exact fresh
  · intro target assignment _
    apply holds_of_none X (consumer codes s code temporary output)
    all_goals
      rw [consumer_spec codes s code temporary output declared]
      rfl

variable [DecidableEq R]

theorem result_present :
    ((consumer codes s code temporary output).result X).present =
      (s.present \ {temporary}) ∪ {output} := by
  simp [RFiring.result, MeTTaCalculus.OccurrenceCommits.fire, consumer, Selection.commit]

theorem result_models_iff (declared : codes.unfold code = readerSpec) (point : Subst rowSig) :
    X.Models (a := s.frame) (b := PUnit.unit) point
        ((consumer codes s code temporary output).result X).knowledge ↔
      X.Models (a := s.frame) (b := PUnit.unit) point s.knowledge ∧
        point.applyTerm (((consumer codes s code temporary output).result X).label output) =
          point.applyTerm (s.label temporary) := by
  rw [consumer_result_label codes s code temporary output declared]
  exact models_iff codes s code temporary output declared point

#print axioms information
#print axioms models_iff
#print axioms extends_model
#print axioms shapes
#print axioms admitted
#print axioms result_present
#print axioms result_models_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadConsumer
