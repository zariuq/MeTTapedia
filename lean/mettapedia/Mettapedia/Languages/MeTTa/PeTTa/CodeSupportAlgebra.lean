import Mettapedia.Languages.MeTTa.PeTTa.Eval

/-! Intersections of supported vocabularies preserve code support, including
the helper operations introduced by native control forms. These laws concern
the code representation; program agreement and execution transport are
separate consumers. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Eval

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

theorem expressionHeadWithin_and (first second : String → Bool) (items : List Atom) :
    expressionHeadWithin (fun head => first head && second head) items =
      (expressionHeadWithin first items && expressionHeadWithin second items) := by
  cases items with
  | nil => rfl
  | cons item items =>
    cases item with
    | symbol head =>
      simp only [expressionHeadWithin]
      cases first head <;> cases second head <;>
        cases (head != "eval") <;> cases (head != "unique") <;>
        cases first "unique-atom" <;> cases first "superpose" <;>
        cases second "unique-atom" <;> cases second "superpose" <;> rfl
    | _ => rfl

mutual
  theorem codeWithin_and (first second : String → Bool) (code : Atom) :
      codeWithin (fun head => first head && second head) code =
        (codeWithin first code && codeWithin second code) := by
    cases code with
    | expression items =>
        have children := atomsWithin_and first second items
        simp only [codeWithin, expressionHeadWithin_and, children]
        simp only [Bool.and_assoc, Bool.and_comm, Bool.and_left_comm]
    | _ => rfl
  termination_by sizeOf code

  theorem atomsWithin_and (first second : String → Bool) (items : List Atom) :
      atomsWithin (fun head => first head && second head) items =
        (atomsWithin first items && atomsWithin second items) := by
    cases items with
    | nil => rfl
    | cons code items =>
        have firstPart := codeWithin_and first second code
        have restPart := atomsWithin_and first second items
        simp only [atomsWithin, firstPart, restPart]
        simp only [Bool.and_assoc, Bool.and_comm, Bool.and_left_comm]
  termination_by sizeOf items
end

end Mettapedia.Languages.MeTTa.PeTTa.Eval
