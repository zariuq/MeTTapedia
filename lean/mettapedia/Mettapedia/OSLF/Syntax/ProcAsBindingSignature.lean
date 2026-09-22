import Mettapedia.OSLF.Syntax.BindingSignature
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.SubstitutionCaptureCanary

/-!
# The executable reflective model, presented as a binding signature

The model carries names explicitly, and its substitution therefore captures.
This module presents the fragment it covers as a binding signature -- three
sorts, eight term formers, and binding declared in the receiver's continuation
rather than managed by hand -- and translates into it.

The translation is what makes the repair checkable rather than asserted.  Two
receivers differing only in the name they bind translate to the *same* term,
because a bound occurrence has become a position and there is no name left for
a binder to capture.  Their images under the model's substitution do not, and
the way they differ is exactly capture: the free variable the substitution
introduced is still used in one and has been caught by the receiver's binder in
the other.

So the model's substitution takes equal inputs to unequal outputs on the
translated calculus, which is what it means for it not to be a function there.

What this module is not: the migration.  The tree still runs on the named
model; moving it is what retires the defect rather than measuring it.
-/


namespace Mettapedia.OSLF.Binding
namespace ProcMigration

open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Basic

set_option autoImplicit false

/-! ## Presenting the executable model as a binding signature -/

/-- Its three sorts: names, data, processes. -/
inductive PSrt where
  | nm
  | dat
  | pr
  deriving DecidableEq, Repr

/-- Its term formers.  `recv1` is the only one that binds: a receiver opens its
continuation under the datum it receives, which is what the model's pattern
variable is. -/
inductive POp : PSrt → Type where
  | nil : POp .pr
  | par2 : POp .pr
  | send : POp .pr
  | recv1 : POp .pr
  | freeN (s : String) : POp .nm
  | nameOf : POp .nm
  | atomD (s : String) : POp .dat
  | nameD : POp .dat

/-- The signature.  Binding is declared here, in `recv1`'s continuation. -/
abbrev psig : Signature where
  Srt := PSrt
  Op := POp
  arity := fun {_} o => match o with
    | .nil => []
    | .par2 => [([], PSrt.pr), ([], PSrt.pr)]
    | .send => [([], PSrt.nm), ([], PSrt.dat)]
    | .recv1 => [([], PSrt.nm), ([PSrt.dat], PSrt.pr)]
    | .freeN _ => []
    | .nameOf => [([], PSrt.dat)]
    | .atomD _ => []
    | .nameD => [([], PSrt.nm)]

/-- A naming environment, innermost binder first. -/
abbrev ctxOf (env : List Nat) : Ctx psig := env.map (fun _ => PSrt.dat)

/-- Where a named variable sits in the environment. -/
def lookupEnv : (env : List Nat) → Nat → Option (Var (ctxOf env) PSrt.dat)
  | [], _ => none
  | e :: rest, x =>
      if e = x then some .zero else (lookupEnv rest x).map .succ

mutual
/-- Translate a name. -/
def toName (env : List Nat) : Name → Option (Term psig (ctxOf env) PSrt.nm)
  | .free s => some (Term.op (S := psig) (POp.freeN s) .nil)
  | .fresh _ => none
  | .var x => (toData env (.var x)).map (fun d =>
      Term.op (S := psig) POp.nameOf (.cons d .nil))

/-- Translate a datum. -/
def toData (env : List Nat) : Data → Option (Term psig (ctxOf env) PSrt.dat)
  | .atom a => some (Term.op (S := psig) (POp.atomD a) .nil)
  | .var x => (lookupEnv env x).map Term.var
  | .tuple _ => none
  | .name n => match n with
      | .free s => some (Term.op (S := psig) POp.nameD
          (.cons (Term.op (S := psig) (POp.freeN s) .nil) .nil))
      | _ => none
end

/-- Translate a process, on the fragment the signature covers. -/
def toProc : (env : List Nat) → Proc → Option (Term psig (ctxOf env) PSrt.pr)
  | _, .nil => some (Term.op (S := psig) POp.nil .nil)
  | env, .par [a, b] =>
      match toProc env a, toProc env b with
      | some ta, some tb => some (Term.op (S := psig) POp.par2 (.cons ta (.cons tb .nil)))
      | _, _ => none
  | env, .send ch d =>
      match toName env ch, toData env d with
      | some tc, some td => some (Term.op (S := psig) POp.send (.cons tc (.cons td .nil)))
      | _, _ => none
  | env, .recv ch (.bind x) body =>
      match toName env ch, toProc (x :: env) body with
      | some tc, some tb => some (Term.op (S := psig) POp.recv1 (.cons tc (.cons tb .nil)))
      | _, _ => none
  | _, _ => none

/-! ## What the translation shows

The model distinguishes two alpha-variants after one communication.  The
translation does not distinguish them at all -- there are no names left for a
binder to capture.  So the model's substitution is not a function on the
translated calculus: it takes equal inputs to unequal outputs. -/

/-- The two alpha-variants have the same translation. -/
theorem alpha_variants_translate_equal :
    toProc [0] receiverBindingOne = toProc [0] receiverBindingTwo := rfl

/-- **But their images under the model's substitution do not**, and the way
they differ is exactly capture: in the environment `[1, 0]` the variable at
index zero is the free `1` that the substitution introduced.  After the model
substitutes, one translation still uses it and the other does not, because in
the other it was caught by the receiver's binder. -/
theorem substProc_captures_the_free_variable :
    (toProc [1, 0] (substProc capturingSubst receiverBindingOne)).map
        (countVar (Var.zero : Var (ctxOf [1, 0]) PSrt.dat))
      ≠ (toProc [1, 0] (substProc capturingSubst receiverBindingTwo)).map
        (countVar (Var.zero : Var (ctxOf [1, 0]) PSrt.dat)) := by
  rw [substProc_captures, substProc_alpha_variant]
  simp [toProc, toName, toData, lookupEnv, countVar, countVarArgs, sameVar, weakenVar]
  decide

end ProcMigration
end Mettapedia.OSLF.Binding
