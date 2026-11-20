import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.Step
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationSyntax
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.PrincipalOutputs

/-!
# Principal-settled application as an actual effect and step

There is one application rule. Candidates retain the actual row-labelled firing
and the answer returned by the existing total first-order solver. The occurrence
commit and admission are unchanged. Settlement normalizes retained captures;
each made result is a scheme capturing the normalized source interface.

The returned knowledge is empty because the principal answer solves the whole
information. Semantic refinement and answer coverage are derived below. This
construction is not literal-information settlement, and selects no default.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationMachine

open Mettapedia.Logic.LP
open Interface (Frames)
open Presentation.Schematic (Tm rowSig)
open MeTTaCalculus.OccurrenceCommits (fire)

universe uOcc

abbrev RowTerms := OneFrame.Terms Tm
abbrev X := OneFrame.frames (FirstOrder.action rowSig)
abbrev E := OneFrame.ext (FirstOrder.action rowSig)
abbrev Store (O : Type uOcc) := State RowTerms O

def program (judgmentTag arrowTag : Nat) : Set (Rule RowTerms) :=
  {Rule.ofShared (ApplicationSyntax.interpreter judgmentTag arrowTag)}

structure Attempt (judgmentTag arrowTag : Nat) (O : Type uOcc) (s : Store O) where
  raw : Firing O E (program judgmentTag arrowTag) s
  answer : Subst rowSig
  accepted : unifyTotal (raw.information X) = some answer

variable {judgmentTag arrowTag : Nat} {O : Type uOcc} {s : Store O}

def solve (raw : Firing O E (program judgmentTag arrowTag) s) :
    Option (Attempt judgmentTag arrowTag O s) :=
  match found : unifyTotal (raw.information X) with
  | none => none
  | some answer => some ⟨raw, answer, found⟩

noncomputable def context (s : Store O) : List Tm :=
  s.knowledge.map Prod.fst ++ s.knowledge.map Prod.snd ++ s.ambientTerms

namespace Attempt

variable (f : Attempt judgmentTag arrowTag O s)

theorem principal : X.Principal (a := PUnit.unit) (m := PUnit.unit)
    (f.raw.information X) f.answer :=
  (Frames.ofSubstitution_principal_iff (FirstOrder.action rowSig) _ _).mpr
    (FirstOrder.accepted_principal _ _ f.accepted)

noncomputable def outputs : List (Row RowTerms PUnit.unit) :=
  f.raw.rule.basic.body.produce.map fun value =>
    .schematic (PrincipalOutputs.scheme X (a := PUnit.unit) (m := PUnit.unit)
      f.answer (context s) (f.raw.opening.applyTerm value))

def retained (o : O) : Row RowTerms PUnit.unit := (s.label o).act X (b := PUnit.unit) f.answer

variable [DecidableEq O]

noncomputable def result : Store O where
  frame := PUnit.unit
  knowledge := []
  present := fire s.present (f.raw.selection.commit (T := Unit))
  label := RuleSyntax.relabel (Tm := fun a => Row RowTerms a) (a := PUnit.unit)
    f.retained f.raw.selection.made f.outputs

end Attempt

variable (judgmentTag arrowTag : Nat) (O : Type uOcc) [DecidableEq O]

noncomputable def effect : Interface.EffectCore X O (Store O) (Attempt judgmentTag arrowTag O) where
  frame s := s.frame
  knowledge s := s.knowledge
  present s := s.present
  selection f := f.raw.selection
  target _ := PUnit.unit
  extension _ := Subst.id rowSig
  information f := f.raw.information X
  information_refines := by
    intro s f b assignment solved
    exact (singleFiring X O E (program judgmentTag arrowTag)).toStep.models_knowledge
      f.raw assignment solved
  Shapes f := f.raw.Shapes X
  preparedResult f _ := f.result
  present_preparedResult _ _ := rfl
  preparedSettle f _ := f.answer
  result_refines := by
    intro s f _ b assignment _
    exact Frames.models_comp f.principal.sound assignment

noncomputable def machine : Interface.Step X O (Store O) (Attempt judgmentTag arrowTag O) where
  toEffectCore := effect judgmentTag arrowTag O
  Admits f := f.raw.Admits X
  admitted_prepares _ admitted := ⟨admitted.1, admitted.2.1, admitted.2.2.1⟩

theorem exactKnowledge : (effect judgmentTag arrowTag O).ExactKnowledge := by
  intro s f _ b assignment _
  exact Frames.models_nil (X := X) (a := PUnit.unit) (b := b) assignment

theorem solves_every_admitted (s : Store O)
    (raw : Firing O E (program judgmentTag arrowTag) s) (admitted : raw.Admits X) :
    ∃ f : Attempt judgmentTag arrowTag O s,
      solve raw = some f ∧ f.raw = raw ∧ (machine judgmentTag arrowTag O).Admits f := by
  obtain ⟨b, witness, solved⟩ := admitted.2.2.1
  obtain ⟨answer, accepted⟩ := (FirstOrder.accepted_iff_consistent (raw.information X)).mpr
    ⟨witness, solved⟩
  refine ⟨⟨raw, answer, accepted⟩, ?_, rfl, admitted⟩
  unfold solve
  split
  · rename_i refused
    rw [accepted] at refused
    cases refused
  · rename_i returned found
    have same : returned = answer := Option.some.inj (found.symm.trans accepted)
    subst returned
    rfl

theorem covers_information (s : Store O) (f : Attempt judgmentTag arrowTag O s)
    {b : PUnit} (candidate : Subst rowSig)
    (solved : X.Models (a := PUnit.unit) (b := b) candidate (f.raw.information X)) :
    ∃ residual : Subst rowSig,
      X.Models (a := PUnit.unit) (b := b) residual f.result.knowledge ∧
        ∀ value : Tm, candidate.applyTerm value = residual.applyTerm (f.answer.applyTerm value) := by
  obtain ⟨residual, factors⟩ := f.principal.factors b candidate solved
  refine ⟨residual, Frames.models_nil _, ?_⟩
  intro value
  simpa only [X, OneFrame.frames, Frames.ofSubstitution, FirstOrder.action, Subst.applyTerm_comp] using factors value

#print axioms Attempt.principal
#print axioms effect
#print axioms machine
#print axioms exactKnowledge
#print axioms solves_every_admitted
#print axioms covers_information

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationMachine
