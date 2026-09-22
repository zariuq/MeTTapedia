import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Basic

/-!
# The executable model's substitution captures

`substProc` erases the binder's own pattern variables before descending, which
is correct for *shadowing*: a variable the receiver itself binds is not
substituted inside the body.  It never freshens, so it is not correct for
*capture*: a variable occurring free in the replacement is caught by a binder
of the same name on the way in.

This module exhibits that, on the smallest example, as kernel-checked
computation rather than as a claim.  Two receivers differing only in the name
they bind -- alpha-variants, which no calculus may distinguish -- are carried by
the same substitution to bodies which, after one communication delivers a
value, are different processes.

The defect is a property of the representation, not of this file: names are
carried explicitly and nothing renames them apart.  A representation in which
a bound occurrence is a position rather than a name has nothing for a binder
to capture, and the substitution that goes with it is forced to shift what it
carries under a binder because no other program is well typed.  That
representation is `Mettapedia/OSLF/Syntax/BindingSignature.lean`; migrating this
model onto it is what would retire the defect rather than document it.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Basic

/-- A body mentioning only the outer variable `0`. -/
abbrev capturedBody : Proc := Proc.send (Name.free "d") (Data.var 0)

/-- A receiver binding `1`. -/
abbrev receiverBindingOne : Proc :=
  Proc.recv (Name.free "c") (Pat.bind 1) capturedBody

/-- The same receiver, binding `2` instead: an alpha-variant, since the body
mentions neither. -/
abbrev receiverBindingTwo : Proc :=
  Proc.recv (Name.free "c") (Pat.bind 2) capturedBody

/-- Substitute the outer variable by the *free* variable `1`. -/
abbrev capturingSubst : Subst := [(0, Data.var 1)]

/-- In the first receiver the introduced `1` lands under a binder for `1`. -/
theorem substProc_captures :
    substProc capturingSubst receiverBindingOne
      = Proc.recv (Name.free "c") (Pat.bind 1)
          (Proc.send (Name.free "d") (Data.var 1)) := by
  simp [substProc, substData, substName, patVars, eraseVars, eraseVar, lookup]

/-- In the alpha-variant it stays free. -/
theorem substProc_alpha_variant :
    substProc capturingSubst receiverBindingTwo
      = Proc.recv (Name.free "c") (Pat.bind 2)
          (Proc.send (Name.free "d") (Data.var 1)) := by
  simp [substProc, substData, substName, patVars, eraseVars, eraseVar, lookup]

/-- Delivering a value to the first receiver consumes the introduced variable,
because the receiver now binds it. -/
theorem delivery_after_capture :
    substProc [(1, Data.atom "V")] (Proc.send (Name.free "d") (Data.var 1))
      = Proc.send (Name.free "d") (Data.atom "V") := by
  simp [substProc, substData, substName, lookup]

/-- Delivering to the alpha-variant leaves it alone. -/
theorem delivery_after_alpha_variant :
    substProc [(2, Data.atom "V")] (Proc.send (Name.free "d") (Data.var 1))
      = Proc.send (Name.free "d") (Data.var 1) := by
  simp [substProc, substData, substName, lookup]

/-- **So the two alpha-variants behave differently after one communication.**
A substitution that does this is not a function on the calculus. -/
theorem alpha_variants_diverge :
    Proc.send (Name.free "d") (Data.atom "V")
      ≠ Proc.send (Name.free "d") (Data.var 1) := by
  intro h
  injection h with _ hd
  exact Data.noConfusion hd

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Basic
