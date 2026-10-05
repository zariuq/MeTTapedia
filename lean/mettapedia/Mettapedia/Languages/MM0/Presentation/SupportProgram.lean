import Mettapedia.Languages.MM0.Presentation.SupportData
import Mettapedia.Languages.MM0.Presentation.TypingLookup
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.ListAppendProgram

/-!
# Authored MM0 occurrence-support equations

The input context supplies bound and regular binders. Bound occurrences
contribute their position; regular occurrences contribute their declared
dependencies. Applications concatenate both occurrence lists, refusing an
undefined child. This program reuses the authored context lookup and list
append programs; there is no guest-support primitive.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Presentation.ComputationalSupport

open Kernel ComputationalContext
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

private def call (head : String) (arguments : List Term) : Term := .expr (.sym head :: arguments)
private def slot (name : String) : Term := .var name
private def equation (name head : String) (arguments : List Term) (body : Term) : Equation :=
  ⟨name, head, arguments, body⟩

def supportEquations : Program := [
  equation "support-var" "mm0:support" [slot "context", call "MM0:Var" [slot "index"]]
    (call "mm0:support-binder" [call "mm0:data-at" [slot "context", slot "index"], slot "index"]),
  equation "support-term" "mm0:support" [slot "context", call "MM0:Term" [slot "index"]]
    (call "Some" [.list []]),
  equation "support-app" "mm0:support" [slot "context", call "MM0:App" [slot "function", slot "argument"]]
    (call "mm0:support-function" [call "mm0:support" [slot "context", slot "function"],
      slot "context", slot "argument"]),
  equation "support-binder-none" "mm0:support-binder" [.sym "None", slot "index"] (.sym "None"),
  equation "support-binder-bound" "mm0:support-binder"
    [call "Some" [.list [.sym "MM0:Bound", slot "sort"]], slot "index"]
    (call "Some" [.list [slot "index"]]),
  equation "support-binder-regular" "mm0:support-binder"
    [call "Some" [.list [.sym "MM0:Regular", slot "sort", slot "dependencies"]], slot "index"]
    (call "Some" [slot "dependencies"]),
  equation "support-function-none" "mm0:support-function"
    [.sym "None", slot "context", slot "argument"] (.sym "None"),
  equation "support-function-some" "mm0:support-function"
    [call "Some" [slot "left"], slot "context", slot "argument"]
    (call "mm0:support-argument" [slot "left", call "mm0:support" [slot "context", slot "argument"]]),
  equation "support-argument-none" "mm0:support-argument" [slot "left", .sym "None"] (.sym "None"),
  equation "support-argument-some" "mm0:support-argument"
    [slot "left", call "Some" [slot "right"]]
    (call "Some" [call "nik:list-append" [slot "left", slot "right"]])]

def supportProgram : Program := ComputationalTyping.typingProgram ++ (listAppendProgram ++ supportEquations)

theorem supportEquations_leftLinear : LeftLinear supportEquations := by
  simp [LeftLinear, supportEquations, equation, call, slot, patternVarsList, patternVars]

theorem supportProgram_leftLinear : LeftLinear supportProgram := by
  simp only [supportProgram, LeftLinear, List.mem_append, or_imp, forall_and]
  exact ⟨ComputationalTyping.typingProgram_leftLinear, listAppendProgram_leftLinear,
    supportEquations_leftLinear⟩

theorem supportProgram_dataSeparated : DataSeparated supportProgram computationalHost where
  undefined := by
    intro head member
    have prior := ComputationalTyping.typingProgram_dataSeparated.undefined head member
    simp only [supportProgram, Program.defines, List.any_append]
    change (ComputationalTyping.typingProgram.defines head ||
      (listAppendProgram.defines head || supportEquations.defines head)) = false
    rw [prior]
    simp only [constructorHeads, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> rfl
  unhandled := by
    intro head member arguments
    simp [constructorHeads] at member
    rcases member with rfl | rfl | rfl <;> rfl

end Mettapedia.Languages.MM0.Presentation.ComputationalSupport
