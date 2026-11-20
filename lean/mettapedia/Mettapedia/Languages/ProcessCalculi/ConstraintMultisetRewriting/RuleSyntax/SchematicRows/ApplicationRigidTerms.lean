import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic.Terms

/-!
# Rigid source values and instantiable locals in the existing row signature

Symbols keep their tags. Existing name constants use even name tags, while
fixed target variables use odd name tags. Schema-local variables remain
variables. Both application and code formers are transported structurally.
This is an internal, decoded representation, not a change to public names or
a new term syntax or unifier.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationRigidTerms

open Mettapedia.Logic.LP
open Presentation.Schematic (Tm rowSig RowConstant)

def liftConstant : RowConstant → RowConstant
  | .sym tag => .sym tag
  | .name tag => .name (2 * tag)

def localLift : Tm → Tm
  | .var name => .var name
  | .const value => .const (liftConstant value)
  | .app former children => .app former (fun i => localLift (children i))

def rigidLift : Tm → Tm
  | .var name => .const (.name (2 * name + 1))
  | .const value => .const (liftConstant value)
  | .app former children => .app former (fun i => rigidLift (children i))

def decode : Tm → Tm
  | .var name => .var name
  | .const (.sym tag) => .const (.sym tag)
  | .const (.name tag) =>
      if tag % 2 = 0 then .const (.name (tag / 2)) else .var (tag / 2)
  | .app former children => .app former (fun i => decode (children i))

theorem decode_lifted_constant (value : RowConstant) :
    decode (.const (liftConstant value)) = .const value := by
  cases value with
  | sym tag => rfl
  | name tag =>
    have even : (2 * tag) % 2 = 0 := by omega
    have half : (2 * tag) / 2 = tag := by omega
    change (if (2 * tag) % 2 = 0 then Term.const (σ := rowSig) (.name ((2 * tag) / 2))
      else Term.var (σ := rowSig) ((2 * tag) / 2)) = Term.const (σ := rowSig) (.name tag)
    rw [if_pos even, half]

theorem decode_local (term : Tm) : decode (localLift term) = term := by
  induction term with
  | var name => rfl
  | const value => exact decode_lifted_constant value
  | app former children ih =>
    change Term.app former (fun i => decode (localLift (children i))) = .app former children
    exact congrArg (Term.app (σ := rowSig) former) (funext ih)

theorem decode_rigid (term : Tm) : decode (rigidLift term) = term := by
  induction term with
  | var name =>
    have odd : (2 * name + 1 : Nat) % 2 ≠ 0 := by omega
    have half : (2 * name + 1 : Nat) / 2 = name := by omega
    change (if (2 * name + 1) % 2 = 0 then Term.const (σ := rowSig) (.name ((2 * name + 1) / 2))
      else Term.var (σ := rowSig) ((2 * name + 1) / 2)) = Term.var (σ := rowSig) name
    rw [if_neg odd, half]
  | const value => exact decode_lifted_constant value
  | app former children ih =>
    change Term.app former (fun i => decode (rigidLift (children i))) = .app former children
    exact congrArg (Term.app (σ := rowSig) former) (funext ih)

theorem rigid_injective : Function.Injective rigidLift := by
  intro first second same
  exact (decode_rigid first).symm.trans ((congrArg decode same).trans (decode_rigid second))

theorem local_injective : Function.Injective localLift := by
  intro first second same
  exact (decode_local first).symm.trans ((congrArg decode same).trans (decode_local second))

theorem rigid_ground (term : Tm) : (rigidLift term).isGround := by
  induction term with
  | var name => trivial
  | const value => trivial
  | app former children ih => exact ih

theorem rigid_fixed (assignment : Subst rowSig) (term : Tm) :
    assignment.applyTerm (rigidLift term) = rigidLift term :=
  FirstOrder.ground_fixed assignment (rigidLift term) (rigid_ground term)

def liftAssignment (assignment : Subst rowSig) : Subst rowSig := fun name => rigidLift (assignment name)
def decodeAssignment (assignment : Subst rowSig) : Subst rowSig := fun name => decode (assignment name)

theorem lifted_substitution (assignment : Subst rowSig) (term : Tm) :
    (liftAssignment assignment).applyTerm (localLift term) = rigidLift (assignment.applyTerm term) := by
  induction term with
  | var name => rfl
  | const value => rfl
  | app former children ih =>
    change Term.app former (fun i => (liftAssignment assignment).applyTerm (localLift (children i))) =
      .app former (fun i => rigidLift (assignment.applyTerm (children i)))
    exact congrArg (Term.app (σ := rowSig) former) (funext ih)

theorem decoded_substitution (assignment : Subst rowSig) (term : Tm) :
    decode (assignment.applyTerm (localLift term)) = (decodeAssignment assignment).applyTerm term := by
  induction term with
  | var name => rfl
  | const value => exact decode_lifted_constant value
  | app former children ih =>
    change Term.app former (fun i => decode (assignment.applyTerm (localLift (children i)))) =
      .app former (fun i => (decodeAssignment assignment).applyTerm (children i))
    exact congrArg (Term.app (σ := rowSig) former) (funext ih)

theorem original_name_distinct_from_rigid_variable (name slot : Nat) :
    localLift (.const (.name name)) ≠ rigidLift (.var slot) := by
  intro same
  have equality := RowConstant.name.inj (Term.const.inj same)
  omega

namespace Controls

def naive : Tm → Tm
  | .var name => .const (.name name)
  | .const value => .const value
  | .app former children => .app former (fun i => naive (children i))

theorem naive_collapses_name_and_variable (name : Nat) :
    (.var name : Tm) ≠ .const (.name name) ∧ naive (.var name) = naive (.const (.name name)) := by
  constructor
  · intro impossible
    cases impossible
  · rfl

theorem unresolved_value_roundtrip (name : Nat) : decode (rigidLift (.var name)) = .var name :=
  decode_rigid (.var name)

end Controls

#print axioms decode_rigid
#print axioms rigid_injective
#print axioms rigid_ground
#print axioms lifted_substitution
#print axioms decoded_substitution
#print axioms original_name_distinct_from_rigid_variable
#print axioms Controls.naive_collapses_name_and_variable

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationRigidTerms
