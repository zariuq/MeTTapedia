import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CettaWireAtom
import Mettapedia.GSLT.LanguageDef.InferenceCettaWireFormat

/-! Code-support checking through the shared wire carrier. Data payloads are
ignored by this support check; application heads retain the evaluator's
actual support and dynamic-evaluation restrictions. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.WireCodeSupport

open Mettapedia.GSLT.LanguageDef CettaWire

mutual
  def check (allowed : String → Bool) : Term → Bool
    | .application head arguments =>
        Eval.expressionHeadWithin allowed [.symbol head] && checkMany allowed arguments
    | _ => true

  def checkMany (allowed : String → Bool) : List Term → Bool
    | [] => true
    | first :: rest => check allowed first && checkMany allowed rest
end

mutual
  theorem codeWithin_encode (allowed : String → Bool) (value : Term) :
      Eval.codeWithin allowed (CettaWireAtom.encode value) = check allowed value := by
    cases value with
    | symbol name => rfl
    | string value => rfl
    | natural value => rfl
    | application head arguments =>
      simp only [CettaWireAtom.encode, Eval.codeWithin, Eval.expressionHeadWithin,
        Eval.atomsWithin, Bool.true_and, check, atomsWithin_encodeMany]

  theorem atomsWithin_encodeMany (allowed : String → Bool) (values : List Term) :
      Eval.atomsWithin allowed (CettaWireAtom.encodeMany values) = checkMany allowed values := by
    cases values with
    | nil => rfl
    | cons first rest =>
      simp only [CettaWireAtom.encodeMany, Eval.atomsWithin, codeWithin_encode,
        atomsWithin_encodeMany, checkMany]
end

@[simp] theorem check_symbol (allowed : String → Bool) (name : String) : check allowed (.symbol name) = true := rfl
@[simp] theorem check_string (allowed : String → Bool) (value : String) : check allowed (.string value) = true := rfl
@[simp] theorem check_natural (allowed : String → Bool) (value : Nat) : check allowed (.natural value) = true := rfl

theorem check_application (allowed : String → Bool) (head : String) (arguments : List Term)
    (supported : Eval.expressionHeadWithin allowed [.symbol head] = true)
    (children : checkMany allowed arguments = true) : check allowed (.application head arguments) = true := by
  simp only [check, supported, children, Bool.true_and]

theorem check_encodeList {α : Type} (allowed : String → Bool) (encode : α → Term)
    (cons : allowed "LCons" = true) (values : List α)
    (valid : ∀ value ∈ values, check allowed (encode value) = true) :
    check allowed (CettaWire.encodeList encode values) = true := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    simp only [CettaWire.encodeList, check, Eval.expressionHeadWithin, cons, checkMany,
      valid value List.mem_cons_self, Bool.true_and, Bool.and_true]
    exact ih (fun other member => valid other (List.mem_cons_of_mem _ member))

example : check (fun head => head == "unique") (.application "unique" [.symbol "data"]) = false := by
  decide +kernel

example : check (fun head => head == "PApp") (.application "PApp" [.string "unique"]) = true := by
  decide +kernel

#print axioms codeWithin_encode
#print axioms check_encodeList

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.WireCodeSupport
