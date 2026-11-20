import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationPairRuns

/-!
# Full-context capture has exponential unfolded interface length

This counts entries in the actual prepared machine's context lists, not
physical memory or machine instructions. Every admitted application retains
the old captures and adds one scheme capturing the entire current context.
With empty source knowledge the list length doubles per actual firing.

The semantic saturation laws therefore do not license a claim of compact
native representation. Sharing or interface minimization needs its own
operational and observation-preservation refinement.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationMachine

open Mettapedia.Logic.LP
open Presentation.Schematic (Tm rowSig)
open ApplicationSyntax
open MeTTaCalculus.OccurrenceCommits (fire)

universe uOcc
variable {judgmentTag arrowTag : Nat} {O : Type uOcc} [DecidableEq O] {s : Store O}

namespace Attempt

variable (f : Attempt judgmentTag arrowTag O s)

theorem singleton_output_label (made : O) (madeWord : f.raw.selection.made = [made]) :
    f.result.label made = Row.schematic
      (PrincipalOutputs.scheme X (a := PUnit.unit) (m := PUnit.unit) f.answer (context s)
        (f.raw.opening.applyTerm (judgment judgmentTag (app (.var 0) (.var 3)) (.var 2)))) := by
  change RuleSyntax.relabel (Tm := fun a => Row RowTerms a) f.retained
    f.raw.selection.made f.outputs made = _
  rw [madeWord, f.outputs_singleton]
  simp [RuleSyntax.relabel]

theorem ambient_length (admitted : (machine judgmentTag arrowTag O).Admits f) :
    f.result.ambientTerms.length = (context s).length + s.ambientTerms.length := by
  obtain ⟨made, madeWord⟩ := List.length_eq_one_iff.mp (f.made_one admitted)
  have fresh : made ∉ s.present := by
    intro old
    exact f.old_not_made admitted made old (madeWord.symm ▸ List.mem_singleton_self made)
  have present : f.result.present = insert made s.present := by
    change fire s.present (f.raw.selection.commit (T := Unit)) = _
    simp [Selection.commit, f.no_takes admitted, madeWord, fire]
  have newLength : (f.result.label made).ambientTerms.length = (context s).length := by
    rw [f.singleton_output_label made madeWord]
    change ((context s).map f.answer.applyTerm).length = (context s).length
    exact List.length_map _
  have oldLengths :
      (s.present.toList.flatMap fun o => (f.result.label o).ambientTerms).length =
        s.ambientTerms.length := by
    rw [List.length_flatMap]
    change _ = (s.present.toList.flatMap fun o => (s.label o).ambientTerms).length
    rw [List.length_flatMap]
    apply congrArg List.sum
    apply List.map_congr_left
    intro o member
    rw [f.retained_label admitted o (Finset.mem_toList.mp member)]
    change ((s.label o).act X f.answer).ambientTerms.length = (s.label o).ambientTerms.length
    rw [Row.ambientTerms_act, List.length_map]
  have reorder := (Finset.toList_insert fresh).flatMap_right
    (fun o => (f.result.label o).ambientTerms)
  change (f.result.present.toList.flatMap fun o => (f.result.label o).ambientTerms).length = _
  rw [present, reorder.length_eq, List.flatMap_cons, List.length_append, newLength, oldLengths]

theorem context_length (admitted : (machine judgmentTag arrowTag O).Admits f) :
    (context f.result).length = (context s).length + s.ambientTerms.length := by
  have empty : f.result.knowledge = [] := rfl
  change (f.result.knowledge.map Prod.fst ++ f.result.knowledge.map Prod.snd ++
    f.result.ambientTerms).length = _
  rw [empty]
  simpa only [List.map_nil, List.nil_append] using f.ambient_length admitted

theorem context_doubles (admitted : (machine judgmentTag arrowTag O).Admits f)
    (empty : s.knowledge = []) :
    (context f.result).length = 2 * (context s).length := by
  have initial : (context s).length = s.ambientTerms.length := by
    simp only [context, empty, List.map_nil, List.nil_append]
  rw [f.context_length admitted, ← initial]
  omega

end Attempt

theorem run_context_length (run : (machine judgmentTag arrowTag O).Run s)
    (empty : s.knowledge = []) :
    (context run.last).length = 2 ^ run.word.length * (context s).length := by
  induction run with
  | nil initial => simp [Interface.Step.Run.last, Interface.Step.Run.word]
  | @cons initial f admitted rest ih =>
    change (context rest.last).length = 2 ^ (rest.word.length + 1) * (context initial).length
    rw [ih rfl]
    change 2 ^ rest.word.length * (context f.result).length =
      2 ^ (rest.word.length + 1) * (context initial).length
    rw [f.context_doubles admitted empty, Nat.pow_succ, Nat.mul_assoc]

#print axioms Attempt.ambient_length
#print axioms Attempt.context_doubles
#print axioms run_context_length

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationMachine
