import Mettapedia.Languages.MM0.Presentation.SupportProgram
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.ProgramExtension

/-!
# Authored occurrence-support computation

The actual lookup and append components retain their meanings when composed
with the support equations. Structural traversal then computes complete
occurrence lists; their finite-set interpretation is the independent MM0
support judgment. Refusal and evaluator exhaustion remain distinct.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Presentation.ComputationalSupport

open Kernel ComputationalContext
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => supportProgram
local notation "H" => computationalHost

private theorem typing_disjoint :
    ∀ equation ∈ listAppendProgram ++ supportEquations,
      equation.head ∉ ComputationalTyping.typingProgram.calledHeads := by decide

private theorem append_before_disjoint :
    ∀ equation ∈ ComputationalTyping.typingProgram,
      equation.head ∉ listAppendProgram.calledHeads := by decide

private theorem append_after_disjoint :
    ∀ equation ∈ supportEquations, equation.head ∉ listAppendProgram.calledHeads := by decide

theorem lookup_reused (context : Context) (index : Nat) :
    Applies P H "mm0:data-at" [encodeContext context, natural index]
      (ComputationalTyping.encodeBinderResult context[index]?) := by
  exact (Applies.append_iff ComputationalTyping.typingProgram (listAppendProgram ++ supportEquations)
    H typing_disjoint "mm0:data-at" (by decide) _ _).mpr
      (ComputationalTyping.context_lookup_computes context index)

theorem append_reused (left right : List Nat) :
    Applies P H "nik:list-append" [encodeNaturals left, encodeNaturals right]
      (encodeNaturals (left ++ right)) := by
  have computed := (Applies.frame_iff listAppendProgram ComputationalTyping.typingProgram supportEquations H
    append_before_disjoint append_after_disjoint "nik:list-append" (by decide) _ _).mpr
      (list_append_computes (left.map natural) (right.map natural))
  simpa only [supportProgram, List.append_assoc, encodeNaturals, List.map_append] using computed

private theorem binder_computes (binder : Option Kernel.Binder) (index : Nat) :
    Applies P H "mm0:support-binder" [ComputationalTyping.encodeBinderResult binder, natural index]
      (encodeResult (match binder with
        | none => none
        | some (.bound _) => some [index]
        | some (.regular _ dependencies) => some (dependencies.sort (· ≤ ·)))) := by
  cases binder with
  | none => exact ⟨1, rfl⟩
  | some binder => cases binder <;> exact ⟨3, rfl⟩

private theorem variable_computes (context : Context) (index : Nat) :
    Applies P H "mm0:support" [encodeContext context, encode (.var index)]
      (encodeResult (indices? context (.var index))) := by
  have result : indices? context (.var index) = (match context[index]? with
      | none => none
      | some (.bound _) => some [index]
      | some (.regular _ dependencies) => some (dependencies.sort (· ≤ ·))) := by
    cases found : context[index]? with
    | none => simp [indices?, found]
    | some binder => cases binder <;> simp [indices?, found]
  rw [result]
  refine Applies.equation (equation := P[40])
    (environment := [("context", encodeContext context), ("index", natural index)]) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) .nil))
    (binder_computes context[index]? index)
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (lookup_reused context index)

private theorem argument_some (left right : List Nat) :
    Applies P H "mm0:support-argument"
      [encodeNaturals left, .expr [.sym "Some", encodeNaturals right]]
      (encodeResult (some (left ++ right))) := by
  refine Applies.equation (equation := P[49])
    (environment := [("left", encodeNaturals left), ("right", encodeNaturals right)]) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons ?_ .nil)
    (.constructor (by rfl) (by rfl))
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (append_reused left right)

private theorem function_some (context : Context) (argument : Preterm) (left : List Nat)
    (middle result : Term)
    (child : Applies P H "mm0:support" [encodeContext context, encode argument] middle)
    (next : Applies P H "mm0:support-argument" [encodeNaturals left, middle] result) :
    Applies P H "mm0:support-function"
      [.expr [.sym "Some", encodeNaturals left], encodeContext context, encode argument] result := by
  refine Applies.equation (equation := P[47])
    (environment := [("left", encodeNaturals left), ("context", encodeContext context),
      ("argument", encode argument)]) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) (.cons ?_ .nil)) next
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) child

private theorem application_start (context : Context) (function argument : Preterm)
    (middle result : Term)
    (child : Applies P H "mm0:support" [encodeContext context, encode function] middle)
    (next : Applies P H "mm0:support-function" [middle, encodeContext context, encode argument] result) :
    Applies P H "mm0:support" [encodeContext context, encode (.app function argument)] result := by
  refine Applies.equation (equation := P[42])
    (environment := [("context", encodeContext context), ("function", encode function),
      ("argument", encode argument)]) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))) next
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) child

theorem support_computes (context : Context) (expression : Preterm) :
    Applies P H "mm0:support" [encodeContext context, encode expression]
      (encodeResult (indices? context expression)) := by
  induction expression with
  | var index => exact variable_computes context index
  | term index => exact ⟨3, rfl⟩
  | app function argument ihFunction ihArgument =>
    refine application_start context function argument _ _ ihFunction ?_
    cases left : indices? context function with
    | none => simp only [indices?, left]; exact ⟨1, rfl⟩
    | some leftIndices =>
      cases right : indices? context argument with
      | none =>
        have child : Applies P H "mm0:support" [encodeContext context, encode argument] (.sym "None") := by
          simpa only [right, encodeResult] using ihArgument
        simpa [indices?, left, right, encodeResult] using
          function_some context argument leftIndices _ _ child ⟨1, rfl⟩
      | some rightIndices =>
        have child : Applies P H "mm0:support" [encodeContext context, encode argument]
            (encodeResult (some rightIndices)) := by simpa only [right] using ihArgument
        simpa [indices?, left, right, encodeResult] using
          function_some context argument leftIndices _ _ child (argument_some leftIndices rightIndices)

theorem support_result_exact (context : Context) (expression : Preterm) (result : Term) :
    Applies P H "mm0:support" [encodeContext context, encode expression] result ↔
      result = encodeResult (indices? context expression) := by
  constructor
  · exact fun run => run.deterministic (support_computes context expression)
  · rintro rfl
    exact support_computes context expression

theorem support_accepts_iff (context : Context) (expression : Preterm) (support : Finset Nat) :
    (∃ indices, Applies P H "mm0:support" [encodeContext context, encode expression]
      (encodeResult (some indices)) ∧ indices.toFinset = support) ↔
      Preterm.Supports context expression support := by
  constructor
  · rintro ⟨indices, run, rfl⟩
    exact indices_sound (encodeResult_injective ((support_result_exact _ _ _).mp run)).symm
  · intro supported
    obtain ⟨indices, computed, same⟩ := indices_complete supported
    refine ⟨indices, ?_, same⟩
    simpa only [computed] using support_computes context expression

theorem support_refuses_iff (context : Context) (expression : Preterm) :
    Applies P H "mm0:support" [encodeContext context, encode expression] (.sym "None") ↔
      ¬ ∃ support, Preterm.Supports context expression support := by
  rw [support_result_exact]
  constructor
  · intro same
    change encodeResult none = _ at same
    exact (indices_refusal_iff _ _).mp (encodeResult_injective same).symm
  · intro refused
    rw [(indices_refusal_iff _ _).mpr refused]
    rfl

theorem support_completed_result (context : Context) (expression : Preterm) (fuel : Nat)
    (finished : apply P H fuel "mm0:support" [encodeContext context, encode expression] ≠ .exhausted) :
    apply P H fuel "mm0:support" [encodeContext context, encode expression] =
      .value (encodeResult (indices? context expression)) :=
  (support_computes context expression).completed fuel finished

end Mettapedia.Languages.MM0.Presentation.ComputationalSupport
