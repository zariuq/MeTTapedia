import Mettapedia.GSLT.LanguageDef.CostRestorationRelation

/-!
# Which partners a semantic leaf can have

A common semantic atom occurs in a restored frame as `.fvar name`, and its
restoration at ambient depth `d` is its assigned normal form lifted by
`d - (support name).length`.  The depth-uniform relation `RestoresTogether`
therefore constrains a partner far more tightly than equality at one depth:
the whole *family* of lifts must agree with the partner's own restorations.

This module extracts that constraint once, as a shift law, and reads off the
two consequences a total leaf dispatcher needs:

* a bound-variable partner is **impossible** — not merely hard to construct
  (`not_restoresTogether_fvar_bvar`);
* any other partner **determines** the atom's assigned normal form
  (`assignment_eq_of_restoresTogether_fvar_left`), so a structured rigid
  partner is admissible exactly when that value equation holds and the
  partner's restoration is lift-stable.

Both directions are stated generically over profile, support, and
assignment; no cospan, environment, or plan is involved.

LLM primer: everything follows by instantiating the depth quantifier twice,
at `(support name).length` (where the lift is trivial) and at
`(support name).length + shift`.  Truncated subtraction is what makes the
first instantiation land exactly on `liftBVars 0 0`.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution

namespace ReflectiveContextSupport

variable {profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile}
variable {support : ContextSupport.Support}
variable {assignment : ContextSupport.Assignment}

@[simp]
theorem substituteAt_bvar (depth index : Nat) :
    substituteAt profile support assignment depth (.bvar index) =
      .bvar index := by
  rw [substituteAt]

@[simp]
theorem substituteAt_fvar (name : String) (depth : Nat) :
    substituteAt profile support assignment depth (.fvar name) =
      liftBVars 0 (depth - (support name).length) (assignment name) := by
  rw [substituteAt]

/-! ## The shift law -/

/-- A semantic leaf determines its assigned normal form: the partner's
restoration at the leaf's own support depth **is** the assignment.

This is the depth at which the lift is trivial, so no information about the
partner's shape is needed. -/
theorem assignment_eq_of_restoresTogether_fvar_left
    {name : String} {right : Pattern}
    (restores : RestoresTogether profile support assignment (.fvar name)
      right) :
    assignment name =
      substituteAt profile support assignment (support name).length right := by
  have base := restores (support name).length
  rw [substituteAt_fvar, Nat.sub_self, liftBVars_zero] at base
  exact base

/-- **Shift law.** Along a semantic leaf, lifting the partner's restoration
at the leaf's support depth reproduces the partner's restoration deeper by
exactly that shift.

Every obstruction below is an instance of this one equation. -/
theorem liftBVars_substituteAt_eq_substituteAt_of_restoresTogether_fvar_left
    {name : String} {right : Pattern}
    (restores : RestoresTogether profile support assignment (.fvar name)
      right)
    (shift : Nat) :
    liftBVars 0 shift
        (substituteAt profile support assignment (support name).length
          right) =
      substituteAt profile support assignment
        ((support name).length + shift) right := by
  have base := assignment_eq_of_restoresTogether_fvar_left restores
  have deeper := restores ((support name).length + shift)
  rw [substituteAt_fvar, Nat.add_sub_cancel_left] at deeper
  rw [← base]
  exact deeper

/-- A partner whose restoration does not vary with ambient depth must be
invariant under every lift.  This is the exclusion test: any candidate
partner carrying a free bound variable fails it. -/
theorem liftBVars_eq_self_of_restoresTogether_fvar_left
    {name : String} {right : Pattern}
    (restores : RestoresTogether profile support assignment (.fvar name)
      right)
    (shift : Nat)
    (invariant : substituteAt profile support assignment
        ((support name).length + shift) right =
      substituteAt profile support assignment (support name).length right) :
    liftBVars 0 shift
        (substituteAt profile support assignment (support name).length
          right) =
      substituteAt profile support assignment (support name).length right :=
  (liftBVars_substituteAt_eq_substituteAt_of_restoresTogether_fvar_left
    restores shift).trans invariant

/-! ## Bound-variable totality -/

/-- **A semantic leaf can never meet a bound variable.**

The bound variable restores to itself at every depth, so the shift law would
force `liftBVars 0 1` to fix it; but lifting at cutoff zero increments every
index.  The leaf dispatcher may therefore discharge this pair by absurdity
rather than by construction. -/
theorem not_restoresTogether_fvar_bvar (name : String) (index : Nat) :
    ¬ RestoresTogether profile support assignment (.fvar name)
      (.bvar index) := by
  intro restores
  have shifted :=
    liftBVars_eq_self_of_restoresTogether_fvar_left restores 1
      (by simp)
  rw [substituteAt_bvar] at shifted
  simp [liftBVars] at shifted

/-- Mirrored statement, for the dispatcher's right-oriented arm. -/
theorem not_restoresTogether_bvar_fvar (index : Nat) (name : String) :
    ¬ RestoresTogether profile support assignment (.bvar index)
      (.fvar name) := fun restores =>
  not_restoresTogether_fvar_bvar name index restores.symm

/-! ## Structured rigid partners -/

/-- A structured rigid partner is admissible exactly when it pins the atom's
assigned normal form.

Read as a design rule: the honest ancestry arm for a rigid partner owes
precisely one value equation — the boundary's normal form equals the
partner's restoration — which is the shape a recursive child closure already
supplies.  It owes nothing about occurrence ancestry on the rigid side. -/
theorem restoresTogether_fvar_left_iff_of_depthInvariant
    {name : String} {right : Pattern}
    (invariant : ∀ depth,
      substituteAt profile support assignment depth right = right) :
    RestoresTogether profile support assignment (.fvar name) right ↔
      (assignment name = right ∧ ∀ shift, liftBVars 0 shift right = right) := by
  constructor
  · intro restores
    have base := assignment_eq_of_restoresTogether_fvar_left restores
    rw [invariant] at base
    refine ⟨base, fun shift => ?_⟩
    have shifted :=
      liftBVars_eq_self_of_restoresTogether_fvar_left restores shift
        (by rw [invariant, invariant])
    rw [invariant] at shifted
    exact shifted
  · rintro ⟨value, stable⟩ depth
    rw [substituteAt_fvar, invariant, value]
    exact stable _

/-! ## Positive and negative examples -/

private def exampleProfile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile :=
  .empty

private def exampleSupport : ContextSupport.Support := fun _ => []

/-- An atom whose normal form is a closed rigid term. -/
private def exampleClosedAssignment : ContextSupport.Assignment := fun _ =>
  .apply "PZero" []

/-- An atom whose normal form retains a bound variable. -/
private def exampleOpenAssignment : ContextSupport.Assignment := fun _ =>
  .bvar 0

-- Positive: a semantic leaf genuinely can meet a structured rigid partner,
-- so the dispatcher may not omit that arm.
example :
    RestoresTogether exampleProfile exampleSupport exampleClosedAssignment
      (.fvar "atom") (.apply "PZero" []) := by
  intro depth
  rw [substituteAt_fvar, substituteAt]
  simp [exampleClosedAssignment, liftBVars]

-- Negative: the same leaf cannot meet a bound variable, at any assignment.
example (index : Nat) :
    ¬ RestoresTogether exampleProfile exampleSupport exampleOpenAssignment
      (.fvar "atom") (.bvar index) :=
  not_restoresTogether_fvar_bvar _ _

-- Negative: an open normal form cannot meet even the rigid term it equals
-- at depth zero, because deeper ambient contexts shift it.
example :
    ¬ RestoresTogether exampleProfile exampleSupport exampleOpenAssignment
      (.fvar "atom") (.bvar 0) :=
  not_restoresTogether_fvar_bvar _ _

end ReflectiveContextSupport

end Mettapedia.GSLT.LanguageDef
