import Mettapedia.Languages.Agda.Structural.Syntax
import Mettapedia.OSLF.Syntax.BindingTelescopeSubstitution

/-!
# Raw context geometry of the structural Agda signature

Ordinary variables have sort `term`; telescope declarations contain annotated
codes of sort `type`. All operations specialize the generic binding telescope.
The controls establish scope, dependence, and capture behavior of raw syntax.
They do not provide formation, typing, or an admitted category with families.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.ContextGeometry

open Mettapedia.OSLF.Binding

abbrev RawTm (n : Nat) := Telescope.RawTm sig .term n
abbrev RawTy (n : Nat) := Telescope.RawTy sig .term .type n
abbrev RawSub (n m : Nat) := Telescope.RawSub sig .term n m
abbrev RawContext (n : Nat) := Telescope.RawContext sig .term .type n

/-- The telescope uses exactly the ordinary scope of the structural syntax. -/
theorem scope_eq (n : Nat) : Telescope.scope (S := sig) .term n = Structural.scope n := rfl

abbrev lookup {n : Nat} (context : RawContext n) (var : Var (Structural.scope n) .term) : RawTy n :=
  Telescope.lookup context var

abbrev pairingEquiv (n m : Nat) : RawSub (n + 1) m ≃ RawSub n m × RawTm m :=
  Telescope.pairingEquiv sig .term n m

theorem pairing_precompose {n m p : Nat} (first : RawSub (n + 1) m) (second : RawSub m p) :
    pairingEquiv n p (Telescope.comp first second) =
      (Telescope.comp (pairingEquiv n m first).1 second,
        bind second (pairingEquiv n m first).2) := Telescope.pairing_precompose first second

namespace Controls

/-- A raw universe term and its explicit next-level annotation. -/
def universeTerm {n : Nat} (level : Nat) : RawTm n := sortTerm (set (levelClosed level))
def universeType {n : Nat} (level : Nat) : RawTy n :=
  el (set (levelClosed (level + 1))) (universeTerm level)

@[simp] theorem bind_universeTerm {n m : Nat} (substitution : RawSub n m) (level : Nat) :
    bind substitution (universeTerm (n := n) level) = universeTerm (n := m) level := rfl

@[simp] theorem bind_universeType {n m : Nat} (substitution : RawSub n m) (level : Nat) :
    bind substitution (universeType (n := n) level) = universeType (n := m) level := rfl

/-- Its code depends on the actual ordinary variable while retaining the annotation. -/
def dependentType : RawTy 1 := el (set (levelClosed 1)) (.var .zero)

def replaceNewest : RawSub 1 1 :=
  Telescope.pair (Telescope.emptySub (S := sig) .term 1) (universeTerm 0)

/-- Reindexing changes an annotated type code, even at the same raw scope. -/
theorem dependent_type_reindexes :
    bind replaceNewest dependentType = universeType (n := 1) 0 := rfl

theorem dependent_type_reindexing_nontrivial :
    bind replaceNewest dependentType ≠ dependentType := by
  intro same
  cases same

/-- The second declaration depends on the first one. -/
def contextOne : RawContext 1 := .snoc .nil (universeType 1)
def contextTwo : RawContext 2 := .snoc contextOne dependentType

/-- Newest-variable lookup keeps the dependency on the older occurrence. -/
theorem newest_lookup :
    lookup contextTwo .zero = el (set (levelClosed 1)) (.var (.succ .zero)) := rfl

/-- Older-variable lookup retains its original explicit universe annotation. -/
theorem older_lookup :
    lookup contextTwo (.succ .zero) = universeType (n := 2) 1 := rfl

theorem newest_lookup_does_not_capture :
    lookup contextTwo .zero ≠ el (set (levelClosed 1)) (.var .zero) := by
  intro same
  cases same

/-- The two supplied components occupy different declaration addresses. -/
def paired : RawSub 2 1 := Telescope.pair replaceNewest (Telescope.newest (S := sig) .term 0)

theorem paired_newest :
    bind paired (Telescope.newest (S := sig) .term 1) = Telescope.newest (S := sig) .term 0 := rfl

theorem paired_older :
    paired .term (.succ .zero) = universeTerm (n := 1) 0 := rfl

theorem paired_components_distinct : paired .term .zero ≠ paired .term (.succ .zero) := by
  intro same
  cases same

/-- The newest declaration's type reads the older substitution component. -/
theorem paired_newest_type :
    bind paired (lookup contextTwo .zero) = universeType (n := 1) 0 := rfl

theorem paired_older_type :
    bind paired (lookup contextTwo (.succ .zero)) = universeType (n := 1) 1 := rfl

/-- Reassembling arbitrary raw components is an actual inverse, without admission. -/
theorem pairing_roundTrip (substitution : RawSub 2 1) :
    (pairingEquiv 1 1).symm (pairingEquiv 1 1 substitution) = substitution :=
  (pairingEquiv 1 1).left_inv substitution

/-- Map the ambient variable to the newest variable of a larger ambient scope. -/
def ambientToNewest : RawSub 1 2 :=
  Telescope.pair (Telescope.emptySub (S := sig) .term 2) (Telescope.newest (S := sig) .term 1)

def ambientLambda : RawTm 1 := lam (.var (.succ .zero))

theorem lambda_avoids_capture :
    bind ambientToNewest ambientLambda = (lam (.var (.succ .zero)) : RawTm 2) := rfl

theorem lambda_does_not_capture :
    bind ambientToNewest ambientLambda ≠ (lam (.var .zero) : RawTm 2) := by
  intro same
  cases same

theorem lambda_preserves_bound_variable :
    bind ambientToNewest (lam (.var .zero) : RawTm 1) = (lam (.var .zero) : RawTm 2) := rfl

/-- Both the domain and the codomain retain their ordinary-variable dependency. -/
def ambientPi : RawTm 1 :=
  pi dependentType (el (set (levelClosed 1)) (.var (.succ .zero)))

theorem pi_avoids_capture :
    bind ambientToNewest ambientPi =
      (pi (el (set (levelClosed 1)) (.var .zero))
        (el (set (levelClosed 1)) (.var (.succ .zero))) : RawTm 2) := rfl

theorem pi_does_not_capture :
    bind ambientToNewest ambientPi ≠
      (pi (el (set (levelClosed 1)) (.var .zero))
        (el (set (levelClosed 1)) (.var .zero)) : RawTm 2) := by
  intro same
  cases same

end Controls

#print axioms pairing_precompose
#print axioms Controls.dependent_type_reindexing_nontrivial
#print axioms Controls.newest_lookup_does_not_capture
#print axioms Controls.pairing_roundTrip
#print axioms Controls.lambda_does_not_capture
#print axioms Controls.pi_does_not_capture

end Mettapedia.Languages.Agda.Structural.ContextGeometry
