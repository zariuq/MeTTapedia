import Mettapedia.Languages.MeTTa.PureKernel.DeclarationSpec
import Mettapedia.Languages.MeTTa.PureKernel.UnitDecl
import Mettapedia.Languages.MeTTa.PureKernel.BoolDecl
import Mettapedia.Languages.MeTTa.PureKernel.NatDecl

/-! LLM primer:
- `DeclName := Lean.Name` has `DecidableEq` and `BEq`
- `PureTm n` has `DecidableEq`
- `checkIndDecl` is the Lean-style `addInductive` analogue for our kernel
- No telescopes yet — this handles non-parametric, non-indexed families (Unit, Bool, Nat)
- Recursors are a separate concern (see RecursorDecl.lean)
-/

namespace Mettapedia.Languages.MeTTa.PureKernel.IndDecl

set_option linter.dupNamespace false

open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.Languages.MeTTa.PureKernel.DeclarationEnv
open Mettapedia.Languages.MeTTa.PureKernel.DeclarationSpec

/-! ## Input types -/

/-- A single constructor specification for an inductive family. -/
structure CtorSpec where
  name : DeclName
  /-- Constructor type as a closed term. For a non-parametric type `T`,
      this has the form `Π (a₁ : A₁) ... (aₖ : Aₖ). T`. -/
  type : PureTm 0
deriving DecidableEq, Repr

/-- An inductive type declaration (non-parametric, non-indexed).

- positive example: `{ typeName := `Nat, ctors := [{name := `Nat.zero, type := const `Nat},
    {name := `Nat.succ, type := pi (const `Nat) (const `Nat)}] }`
- negative example: a declaration where a constructor argument type mentions the
  family name negatively, e.g., `{..., type := pi (pi (const `Bad) u0) (const `Bad)}` -/
structure IndDecl where
  /-- Name of the type former (e.g., `Nat). -/
  typeName : DeclName
  /-- Constructor specifications. -/
  ctors : List CtorSpec
deriving Repr

/-! ## Validation predicates -/

/-- Check that the declaration name `c` does not occur as a `const` in `t`. -/
def notOccursConst (c : DeclName) : PureTm n → Bool
  | .var _ => true
  | .const d => d != c
  | .u0 => true
  | .u1 => true
  | .pi A B => notOccursConst c A && notOccursConst c B
  | .sigma A B => notOccursConst c A && notOccursConst c B
  | .id A a b => notOccursConst c A && notOccursConst c a && notOccursConst c b
  | .lam body => notOccursConst c body
  | .app f a => notOccursConst c f && notOccursConst c a
  | .pair a b => notOccursConst c a && notOccursConst c b
  | .fst p => notOccursConst c p
  | .snd p => notOccursConst c p
  | .refl a => notOccursConst c a

/-- Check that the family name occurs only positively within a type.

In `Π (a : A). B`: the family name must NOT occur in `A` (contravariant
position), but may occur positively in `B`.

At a non-Pi position, any occurrence is positive — returns `true`.

- positive example: `occursOnlyPositively `Nat (.const `Nat) = true`
- negative example: `occursOnlyPositively `Nat (.pi (.const `Nat) .u0) = false` -/
def occursOnlyPositively (familyName : DeclName) : PureTm n → Bool
  | .pi A B => notOccursConst familyName A && occursOnlyPositively familyName B
  | _ => true

/-- Check strict positivity of the family name in a constructor type.

For `Π (a : A). B`: the family name may appear in `A` but only positively
(not on the left of any arrow within `A`), and must be strictly positive in `B`.

At the target position (non-Pi head), anything is allowed.

- positive example: `Π (n : Nat). Nat` — `Nat` appears directly in arg, ok
- negative example: `Π (f : Nat → U0). Nat` — `Nat` on left of arrow in arg -/
def strictlyPositive (familyName : DeclName) : PureTm n → Bool
  | .pi A B => occursOnlyPositively familyName A && strictlyPositive familyName B
  | _ => true

/-- Check that a constructor type targets the family: peel off all outermost
Π-binders and verify the resulting head is `const familyName`. -/
def targetsFamily (familyName : DeclName) : PureTm n → Bool
  | .pi _ B => targetsFamily familyName B
  | .const c => c == familyName
  | _ => false

/-- Check that all names in a list are distinct. -/
def namesDistinct : List DeclName → Bool
  | [] => true
  | a :: rest => !rest.contains a && namesDistinct rest

/-! ## The checker -/

/-- Check an inductive declaration and emit `DeclSpec`s if valid.

Validates:
1. All names (type + constructors) are distinct
2. Each constructor type targets the family
3. Strict positivity: family name does not appear in constructor argument types

Returns the type spec (with type `U0`) followed by one spec per constructor.
Does NOT generate recursors or aliases — those are separate concerns.

- positive example: `checkIndDecl unitDecl = some [unitTySpec, unitCtorSpec]`
- negative example: a declaration with duplicate names returns `none` -/
def checkIndDecl (decl : IndDecl) : Option (List DeclSpec) :=
  let allNames := decl.typeName :: decl.ctors.map CtorSpec.name
  if !namesDistinct allNames then none
  else
    let ctorsValid := decl.ctors.all fun ctor =>
      targetsFamily decl.typeName ctor.type &&
      strictlyPositive decl.typeName ctor.type
    if !ctorsValid then none
    else
      let tySpec : DeclSpec := { name := decl.typeName, type := .u0 }
      let ctorSpecs : List DeclSpec := decl.ctors.map fun ctor =>
        { name := ctor.name, type := ctor.type }
      some (tySpec :: ctorSpecs)

/-! ## Standard declarations as `IndDecl` -/

def unitDecl : IndDecl :=
  { typeName := `Unit
    ctors := [{ name := `Unit.unit, type := .const `Unit }] }

def boolDecl : IndDecl :=
  { typeName := `Bool
    ctors := [{ name := `Bool.true, type := .const `Bool },
              { name := `Bool.false, type := .const `Bool }] }

def natDecl : IndDecl :=
  { typeName := `Nat
    ctors := [{ name := `Nat.zero, type := .const `Nat },
              { name := `Nat.succ, type := .pi (.const `Nat) (.const `Nat) }] }

/-! ## Checker passes on standard declarations -/

theorem check_unitDecl :
    checkIndDecl unitDecl = some
      [{ name := `Unit, type := .u0 },
       { name := `Unit.unit, type := .const `Unit }] := by
  decide

theorem check_boolDecl :
    checkIndDecl boolDecl = some
      [{ name := `Bool, type := .u0 },
       { name := `Bool.true, type := .const `Bool },
       { name := `Bool.false, type := .const `Bool }] := by
  decide

theorem check_natDecl :
    checkIndDecl natDecl = some
      [{ name := `Nat, type := .u0 },
       { name := `Nat.zero, type := .const `Nat },
       { name := `Nat.succ, type := .pi (.const `Nat) (.const `Nat) }] := by
  decide

/-! ## Negative examples -/

/-- A declaration with duplicate names is rejected. -/
def badDupDecl : IndDecl :=
  { typeName := `Bad
    ctors := [{ name := `Bad, type := .const `Bad }] }

theorem check_badDupDecl : checkIndDecl badDupDecl = none := by decide

/-- A declaration with a negatively-occurring family name is rejected. -/
def badNegDecl : IndDecl :=
  { typeName := `Bad
    ctors := [{ name := `Bad.mk,
                type := .pi (.pi (.const `Bad) .u0) (.const `Bad) }] }

theorem check_badNegDecl : checkIndDecl badNegDecl = none := by decide

/-- A constructor that doesn't target the family is rejected. -/
def badTargetDecl : IndDecl :=
  { typeName := `Bad
    ctors := [{ name := `Bad.mk, type := .u0 }] }

theorem check_badTargetDecl : checkIndDecl badTargetDecl = none := by decide

/-! ## Agreement with existing hand-written specs -/

open Mettapedia.Languages.MeTTa.PureKernel.UnitDecl in
theorem unitDecl_specs_agree :
    checkIndDecl unitDecl = some [unitTySpec, unitCtorSpec] := by decide

open Mettapedia.Languages.MeTTa.PureKernel.BoolDecl in
theorem boolDecl_specs_agree :
    checkIndDecl boolDecl = some [boolTySpec, boolTrueSpec, boolFalseSpec] := by decide

open Mettapedia.Languages.MeTTa.PureKernel.NatDecl in
theorem natDecl_specs_agree :
    checkIndDecl natDecl = some [natTySpec, natZeroSpec, natSuccSpec] := by decide

end Mettapedia.Languages.MeTTa.PureKernel.IndDecl
