import Mettapedia.GSLT.LanguageDef.DeterministicEquations.NaturalArithmetic

/-!
# Typed list views and the shared computational host

List viewing returns the actual head and list tail; list construction requires
a list tail. The fallback host is the small unbounded natural catalogue.
Neither operation interprets guest terms, symbol signatures or proofs.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations

def listView : List Term → Term
  | [] => .sym "List:Nil"
  | first :: rest => .expr [.sym "List:Cons", first, .list rest]

def computationalHost : Host where
  primitive head arguments :=
    if head = "nik:list-view" then
      match arguments with
      | [.list values] => .value (listView values)
      | _ => .fault
    else if head = "nik:list-cons" then
      match arguments with
      | [first, .list rest] => .value (.list (first :: rest))
      | _ => .fault
    else naturalArithmeticHost.primitive head arguments

theorem computationalHost_list_view (values : List Term) :
    computationalHost.primitive "nik:list-view" [.list values] = .value (listView values) := rfl

theorem computationalHost_list_cons (first : Term) (rest : List Term) :
    computationalHost.primitive "nik:list-cons" [first, .list rest] =
      .value (.list (first :: rest)) := rfl

theorem computationalHost_arithmetic (head : String) (arguments : List Term)
    (notView : head ≠ "nik:list-view") (notCons : head ≠ "nik:list-cons") :
    computationalHost.primitive head arguments = naturalArithmeticHost.primitive head arguments := by
  simp [computationalHost, notView, notCons]

theorem computationalHost_binary {head : String} {operation : NaturalBinary}
    (selected : naturalBinary? head = some operation) (left right : Nat)
    (notView : head ≠ "nik:list-view") (notCons : head ≠ "nik:list-cons") :
    computationalHost.primitive head [natural left, natural right] =
      .value (operation.result left right) := by
  rw [computationalHost_arithmetic head _ notView notCons]
  exact naturalArithmeticHost_binary selected _ _

theorem computationalHost_zero (value : Nat) :
    computationalHost.primitive "nik:nat-zero" [natural value] =
      .value (.sym (if value = 0 then "True" else "False")) := naturalHost_zero value

theorem computationalHost_pred (value : Nat) :
    computationalHost.primitive "nik:nat-pred" [natural value] =
      .value (natural value.pred) := naturalHost_pred value

theorem computationalHost_unhandled (head : String) (arguments : List Term)
    (notView : head ≠ "nik:list-view") (notCons : head ≠ "nik:list-cons")
    (notBinary : naturalBinary? head = none)
    (notZero : head ≠ "nik:nat-zero") (notPred : head ≠ "nik:nat-pred") :
    computationalHost.primitive head arguments = .unhandled := by
  rw [computationalHost_arithmetic head arguments notView notCons]
  exact naturalArithmeticHost_unhandled _ _ notBinary notZero notPred

/-- All previous natural primitive calls, including their malformed-input refusals,
retain the same result under the larger shared host. -/
theorem computationalHost_natural_operation (head : String) (arguments : List Term)
    (prior : head = "nik:nat-zero" ∨ head = "nik:nat-pred") :
    computationalHost.primitive head arguments = naturalHost.primitive head arguments := by
  rcases prior with rfl | rfl <;> rfl

theorem list_view_exposes_exact_tail (first : Term) (rest : List Term) :
    computationalHost.primitive "nik:list-view" [.list (first :: rest)] =
      .value (.expr [.sym "List:Cons", first, .list rest]) := rfl

theorem list_cons_requires_list_tail (first name : String) :
    computationalHost.primitive "nik:list-cons" [.sym first, .sym name] = .fault := rfl

theorem list_view_rejects_non_list (name : String) :
    computationalHost.primitive "nik:list-view" [.sym name] = .fault := rfl

theorem host_does_not_interpret_guest_checks :
    computationalHost.primitive "vibe:shift" [] = .unhandled ∧
      computationalHost.primitive "mm0:proof" [] = .unhandled := by constructor <;> rfl

end Mettapedia.GSLT.LanguageDef.DeterministicEquations
