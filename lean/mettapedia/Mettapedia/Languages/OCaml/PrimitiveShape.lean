import Mettapedia.Languages.OCaml.ValueShape
import Mettapedia.Languages.OCaml.Primitives

/-! Primitive observations preserve data shape and function presence. Internal
IR diagnostics retain their original payloads and are not equated here. -/

set_option autoImplicit false

namespace Mettapedia.Languages.OCaml

private def followedBy (first rest : Compared) : Compared :=
  match first with
  | .error error => .error error
  | .ok (.error fault) => .ok (.error fault)
  | .ok (.ok .eq) => rest
  | .ok (.ok order) => .ok (.ok order)

private theorem followedBy_shape {first second rest tail : Compared}
    (head : first.toOption = second.toOption) (back : rest.toOption = tail.toOption) :
    (followedBy first rest).toOption = (followedBy second tail).toOption := by
  cases first with
  | error error => cases second <;> first | rfl | contradiction
  | ok a =>
      cases second with
      | error error => contradiction
      | ok b =>
          have same : a = b := Option.some.inj head
          subst b
          cases a with
          | error fault => rfl
          | ok order => cases order <;> first | rfl | exact back

private theorem FieldsShape.isEmpty {left right : List Value} (same : FieldsShape left right) :
    left.isEmpty = right.isEmpty := by cases same <;> rfl

private theorem compareValue_cons_eq (head tail first rest : Value) :
    compareValue (.cons head tail) (.cons first rest) = followedBy (compareValue head first) (compareValue tail rest) := by
  cases answer : compareValue head first with
  | error error => simp only [compareValue, followedBy, answer]; rfl
  | ok value =>
      cases value with
      | error fault => simp only [compareValue, followedBy, answer]; rfl
      | ok order => cases order <;> simp only [compareValue, followedBy, answer] <;> rfl

private theorem compareFields_cons_eq (head first : Value) (tail rest : List Value) :
    compareFields (head :: tail) (first :: rest) = followedBy (compareValue head first) (compareFields tail rest) := by
  cases answer : compareValue head first with
  | error error => simp only [compareFields, followedBy, answer]; rfl
  | ok value =>
      cases value with
      | error fault => simp only [compareFields, followedBy, answer]; rfl
      | ok order => cases order <;> simp only [compareFields, followedBy, answer] <;> rfl

mutual
  theorem compareValue_shape {left first right second : Value}
      (front : ValueShape left first) (back : ValueShape right second) :
      (compareValue left right).toOption = (compareValue first second).toOption := by
    cases front with
    | literal a =>
        cases back <;> try rfl
        case literal b => cases a <;> cases b <;> rfl
    | tuple fields =>
        cases back <;> try rfl
        case tuple values =>
          simp only [compareValue, fields.length, values.length]
          split
          · exact compareFields_shape fields values
          · rfl
    | cons head tail =>
        cases back <;> try rfl
        case literal a => cases a <;> rfl
        case cons first rest =>
          simpa only [compareValue_cons_eq] using
            followedBy_shape (compareValue_shape head first) (compareValue_shape tail rest)
    | variant fields =>
        cases back <;> try rfl
        case variant values =>
          simp only [compareValue]
          split
          · rfl
          · simp only [fields.isEmpty, values.isEmpty]
            split
            · rfl
            · split
              · rfl
              · split
                · exact compareFields_shape fields values
                · rfl
    | closure _ _ _ _ => cases back <;> rfl
    termination_by sizeOf left

  theorem compareFields_shape {left first right second : List Value}
      (front : FieldsShape left first) (back : FieldsShape right second) :
      (compareFields left right).toOption = (compareFields first second).toOption := by
    cases front with
    | nil => cases back <;> rfl
    | cons head tail =>
        cases back with
        | nil => rfl
        | cons first rest =>
            simpa only [compareFields_cons_eq] using
              followedBy_shape (compareValue_shape head first) (compareFields_shape tail rest)
    termination_by sizeOf left
end

private def compareResult (operator : Primitive) (answer : Compared) : Except InternalError Result :=
  match answer with
  | .error error => .error error
  | .ok (.error fault) => .ok (.error fault)
  | .ok (.ok order) => .ok (.ok (.literal (.boolean (comparison operator order))))

private theorem compareResult_shape (operator : Primitive) {first second : Compared}
    (same : first.toOption = second.toOption) :
    (compareResult operator first).toOption = (compareResult operator second).toOption := by
  cases first with
  | error error => cases second <;> first | rfl | contradiction
  | ok a =>
      cases second with
      | error error => contradiction
      | ok b => have equality : a = b := Option.some.inj same; subst b; rfl

private theorem comparison_eval_eq (operator : Primitive) (left right : Value)
    (comparative : operator = .equal ∨ operator = .different ∨ operator = .less ∨ operator = .lessEqual ∨
      operator = .greater ∨ operator = .greaterEqual) :
    operator.eval [left, right] = compareResult operator (compareValue left right) := by
  rcases comparative with rfl | rfl | rfl | rfl | rfl | rfl <;>
    cases answer : compareValue left right <;>
    simp only [Primitive.eval, answer, compareResult] <;>
    first | rfl | (rename_i value; cases value <;> rfl)

theorem Primitive.eval_shape (operator : Primitive) {first second : List Value}
    (same : FieldsShape first second) : (operator.eval first).toOption = (operator.eval second).toOption := by
  cases same with
  | nil => cases operator <;> rfl
  | cons head tail =>
      cases tail with
      | nil =>
          cases head <;> try (cases operator <;> rfl)
      | cons back rest =>
          cases rest with
          | cons more remaining =>
              cases head <;> cases back <;> cases operator <;>
                simp only [Primitive.eval, Except.toOption]
          | nil =>
              by_cases comparative : operator = .equal ∨ operator = .different ∨ operator = .less ∨ operator = .lessEqual ∨
                  operator = .greater ∨ operator = .greaterEqual
              · simp only [comparison_eval_eq operator _ _ comparative]
                exact compareResult_shape operator (compareValue_shape head back)
              · cases operator <;> simp_all only [or_false, or_true, not_true_eq_false, reduceCtorEq]
                all_goals cases head <;> cases back <;> try rfl
                all_goals simp only [Primitive.eval, Except.toOption]

#print axioms compareValue_shape
#print axioms compareFields_shape
#print axioms Primitive.eval_shape

theorem Primitive.eval_scalar (operator : Primitive) (arguments : List Value) {result : Result}
    (calculated : operator.eval arguments = .ok result) :
    ∃ scalar : Except Fault Literal, result = scalar.map Value.literal := by
  unfold Primitive.eval at calculated
  split at calculated
  all_goals try split at calculated
  all_goals try simp only [bind, Except.bind, pure, Except.pure] at calculated
  all_goals try split at calculated
  all_goals try simp only [Except.map] at calculated
  all_goals try split at calculated
  all_goals simp only [Except.ok.injEq, reduceCtorEq] at calculated
  all_goals first
    | contradiction
    | (subst result; exact ⟨.ok _, rfl⟩)
    | (subst result; exact ⟨.error _, rfl⟩)

end Mettapedia.Languages.OCaml
