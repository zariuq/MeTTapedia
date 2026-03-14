import Mettapedia.Languages.MeTTa.PureKernel.InductiveDecl

/-! LLM primer:
- `Ctx n` (from Context.lean) IS the telescope: `nil : Ctx 0`, `snoc Γ A : Ctx (n+1)`
- `telescopePi` wraps a body in Π's from a context (innermost first)
- `piArity` counts leading Π's; `resultIsU0 k t` peels k Π's and checks body = U0
- De Bruijn for parametric families: after peeling `k` total Π's with `p` params,
  param `j` (0-indexed outermost) has de Bruijn index `k - 1 - j`.
  `isParamApp` strips apps right-to-left starting at index `k - p`.
- `ParamIndDecl` subsumes `IndDecl`: set `typeFormerType := .u0` for 0-parameter families
- `targetsFamilyP` uses `targetsFamilyPAux` (standalone, not `where`) for kernel reducibility
- Checker validates `strictlyPositive` first (fast early-exit), then `matchingParamDomains`,
  then `targetsFamilyP` — this order prevents reduction budget exhaustion on negative examples
-/

namespace Mettapedia.Languages.MeTTa.PureKernel.Telescope

set_option linter.dupNamespace false

open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.Languages.MeTTa.PureKernel.Context
open Mettapedia.Languages.MeTTa.PureKernel.DeclarationEnv
open Mettapedia.Languages.MeTTa.PureKernel.DeclarationSpec
open Mettapedia.Languages.MeTTa.PureKernel.IndDecl

/-! ## Telescope operations -/

/-- Wrap a body in Π-binders from a context (innermost binder first).

- positive example: `telescopePi (snoc nil .u0) (.var 0) = .pi .u0 (.var 0)`
  (i.e., `Π (A : U0). A`)
- negative example: `telescopePi nil .u0 = .u0` (no binders) -/
def telescopePi : Ctx n → PureTm n → PureTm 0
  | .nil, body => body
  | .snoc Γ A, body => telescopePi Γ (.pi A body)

/-- Wrap a body in λ-binders from a context (innermost binder first).

- positive example: `telescopeLam (snoc nil .u0) (.var 0) = .lam (.var 0)`
- negative example: `telescopeLam nil .u0 = .u0` (no binders) -/
def telescopeLam : Ctx n → PureTm n → PureTm 0
  | .nil, body => body
  | .snoc Γ _, body => telescopeLam Γ (.lam body)

/-! ## Checker predicates -/

/-- Count leading Π-binders.

- positive example: `piArity (.pi .u0 .u0) = 1`
- negative example: `piArity .u0 = 0` -/
def piArity : PureTm n → Nat
  | .pi _ B => piArity B + 1
  | _ => 0

/-- After peeling `k` Π-binders, is the body `U0`?

- positive example: `resultIsU0 1 (.pi .u0 .u0) = true`
- negative example: `resultIsU0 0 (.pi .u0 .u0) = false` -/
def resultIsU0 : Nat → PureTm n → Bool
  | 0, .u0 => true
  | k + 1, .pi _ B => resultIsU0 k B
  | _, _ => false

/-- Check that the first `k` Π-domains of two terms match (by `BEq`).

- positive example: `matchingParamDomains 1 (.pi .u0 .u0) (.pi .u0 X) = true`
- negative example: `matchingParamDomains 1 (.pi .u0 .u0) (.pi .u1 X) = false` -/
def matchingParamDomains : Nat → PureTm n → PureTm n → Bool
  | 0, _, _ => true
  | k + 1, .pi A₁ B₁, .pi A₂ B₂ => A₁ == A₂ && matchingParamDomains k B₁ B₂
  | _, _, _ => false

/-- Check that a term is `const c` applied to consecutive de Bruijn variables.

Strips applications right-to-left, checking each argument is `var nextVar`,
then `var (nextVar + 1)`, etc.

- positive example: for `List` with `totalBinders = 1, numParams = 1`,
  `isParamApp `List 1 0 (.app (.const `List) (.var 0)) = true`
- negative example: `isParamApp `List 1 0 (.const `List) = false` (expected 1 app) -/
def isParamApp (c : DeclName) : (remaining : Nat) → (nextVar : Nat) → PureTm n → Bool
  | 0, _, .const d => d == c
  | k + 1, v, .app f (.var i) => i.val == v && isParamApp c k (v + 1) f
  | _, _, _ => false

/-- Auxiliary for `targetsFamilyP`: peel Π-binders while counting depth. -/
private def targetsFamilyPAux (familyName : DeclName) (numParams : Nat) (bindersSoFar : Nat) :
    PureTm m → Bool
  | .pi _ B => targetsFamilyPAux familyName numParams (bindersSoFar + 1) B
  | other => isParamApp familyName numParams (bindersSoFar - numParams) other

/-- After peeling ALL Π-binders, check the target is `familyName` applied to
the parameter variables (the first `numParams` outermost-bound vars).

- positive example: `targetsFamilyP `List 1 (.pi .u0 (.app (.const `List) (.var 0))) = true`
  (i.e., `Π (A : U0). List A` targets `List` with 1 param)
- negative example: `targetsFamilyP `List 1 (.pi .u0 (.const `List)) = false`
  (missing the parameter application) -/
def targetsFamilyP (familyName : DeclName) (numParams : Nat) (t : PureTm n) : Bool :=
  targetsFamilyPAux familyName numParams 0 t

/-! ## Parametric inductive declaration -/

/-- An inductive type declaration with parameters.

`numParams` is derived from `typeFormerType` (= `piArity typeFormerType`).
For non-parametric families, use `typeFormerType := .u0`.

- positive example: `{ typeName := `List, typeFormerType := .pi .u0 .u0, ctors := [...] }`
- negative example: `{ typeName := `Nat, typeFormerType := .u0, ctors := [...] }` (0-param) -/
structure ParamIndDecl where
  /-- Name of the type former (e.g., `List). -/
  typeName : DeclName
  /-- Full type of the type former (e.g., `Π (A : U0). U0` for List). -/
  typeFormerType : PureTm 0
  /-- Constructor specifications (fully closed types). -/
  ctors : List CtorSpec
deriving Repr

/-! ## The parametric checker -/

/-- Check a parametric inductive declaration and emit `DeclSpec`s if valid.

Validates:
1. All names (type + constructors) are distinct
2. Type former result is U0 after peeling parameter Π's
3. Each constructor: strict positivity (checked first for fast early-exit),
   then matching param domains, then correct target
4. Constructors' first `numParams` Π-domains match the type former's

Returns the type spec followed by one spec per constructor.
Does NOT generate recursors.

- positive example: `checkParamIndDecl listDecl = some [listTySpec, nilSpec, consSpec]`
- negative example: a declaration with mismatched parameter types returns `none` -/
def checkParamIndDecl (decl : ParamIndDecl) : Option (List DeclSpec) :=
  let numParams := piArity decl.typeFormerType
  let allNames := decl.typeName :: decl.ctors.map CtorSpec.name
  if !namesDistinct allNames then none
  else if !resultIsU0 numParams decl.typeFormerType then none
  else
    let ctorsValid := decl.ctors.all fun ctor =>
      -- Check strictlyPositive first: fast early-exit prevents budget exhaustion
      strictlyPositive decl.typeName ctor.type &&
      matchingParamDomains numParams decl.typeFormerType ctor.type &&
      targetsFamilyP decl.typeName numParams ctor.type
    if !ctorsValid then none
    else
      let tySpec : DeclSpec := { name := decl.typeName, type := decl.typeFormerType }
      let ctorSpecs : List DeclSpec := decl.ctors.map fun ctor =>
        { name := ctor.name, type := ctor.type }
      some (tySpec :: ctorSpecs)

/-! ## Standard parametric declarations -/

def listDecl : ParamIndDecl :=
  { typeName := `List
    typeFormerType := .pi .u0 .u0
    ctors :=
      [{ name := `List.nil,
         type := .pi .u0 (.app (.const `List) (.var 0)) },
       { name := `List.cons,
         type := .pi .u0
           (.pi (.var 0)
             (.pi (.app (.const `List) (.var 1))
               (.app (.const `List) (.var 2)))) }] }

/-! ## Backward-compatible 0-parameter declarations -/

def unitDeclP : ParamIndDecl :=
  { typeName := `Unit
    typeFormerType := .u0
    ctors := [{ name := `Unit.unit, type := .const `Unit }] }

def boolDeclP : ParamIndDecl :=
  { typeName := `Bool
    typeFormerType := .u0
    ctors := [{ name := `Bool.true, type := .const `Bool },
              { name := `Bool.false, type := .const `Bool }] }

def natDeclP : ParamIndDecl :=
  { typeName := `Nat
    typeFormerType := .u0
    ctors := [{ name := `Nat.zero, type := .const `Nat },
              { name := `Nat.succ, type := .pi (.const `Nat) (.const `Nat) }] }

/-! ## Checker passes on standard declarations -/

theorem check_listDecl :
    checkParamIndDecl listDecl = some
      [{ name := `List, type := .pi .u0 .u0 },
       { name := `List.nil, type := .pi .u0 (.app (.const `List) (.var 0)) },
       { name := `List.cons,
         type := .pi .u0
           (.pi (.var 0)
             (.pi (.app (.const `List) (.var 1))
               (.app (.const `List) (.var 2)))) }] := by
  decide

theorem check_unitDeclP :
    checkParamIndDecl unitDeclP = some
      [{ name := `Unit, type := .u0 },
       { name := `Unit.unit, type := .const `Unit }] := by
  decide

theorem check_boolDeclP :
    checkParamIndDecl boolDeclP = some
      [{ name := `Bool, type := .u0 },
       { name := `Bool.true, type := .const `Bool },
       { name := `Bool.false, type := .const `Bool }] := by
  decide

theorem check_natDeclP :
    checkParamIndDecl natDeclP = some
      [{ name := `Nat, type := .u0 },
       { name := `Nat.zero, type := .const `Nat },
       { name := `Nat.succ, type := .pi (.const `Nat) (.const `Nat) }] := by
  decide

/-! ## Negative examples -/

/-- A declaration with mismatched parameter types is rejected. -/
def badParamMismatch : ParamIndDecl :=
  { typeName := `Bad
    typeFormerType := .pi .u0 .u0
    ctors := [{ name := `Bad.mk,
                type := .pi .u1 (.app (.const `Bad) (.var 0)) }] }

theorem check_badParamMismatch : checkParamIndDecl badParamMismatch = none := by decide

/-- A constructor that doesn't apply the family to parameter vars is rejected. -/
def badParamTarget : ParamIndDecl :=
  { typeName := `Bad
    typeFormerType := .pi .u0 .u0
    ctors := [{ name := `Bad.mk,
                type := .pi .u0 (.const `Bad) }] }

theorem check_badParamTarget : checkParamIndDecl badParamTarget = none := by decide

/-- A parametric declaration with a negatively-occurring family name is rejected. -/
def badParamNeg : ParamIndDecl :=
  { typeName := `Bad
    typeFormerType := .pi .u0 .u0
    ctors := [{ name := `Bad.mk,
                type := .pi .u0 (.pi (.pi (.const `Bad) .u0) (.app (.const `Bad) (.var 1))) }] }

theorem check_badParamNeg : checkParamIndDecl badParamNeg = none := by decide

/-! ## Lifting from `IndDecl` -/

/-- Lift a non-parametric `IndDecl` to a `ParamIndDecl` with 0 parameters. -/
def liftToParam (d : IndDecl) : ParamIndDecl :=
  { typeName := d.typeName, typeFormerType := .u0, ctors := d.ctors }

/-! Agreement: the parametric checker on a lifted declaration gives
the same result as the non-parametric checker. -/

theorem toParam_unitDecl_agree :
    checkParamIndDecl (liftToParam unitDecl) = checkIndDecl unitDecl := by decide

theorem toParam_boolDecl_agree :
    checkParamIndDecl (liftToParam boolDecl) = checkIndDecl boolDecl := by decide

theorem toParam_natDecl_agree :
    checkParamIndDecl (liftToParam natDecl) = checkIndDecl natDecl := by decide

/-! ## Agreement with existing hand-written specs -/

open Mettapedia.Languages.MeTTa.PureKernel.UnitDecl in
theorem unitDeclP_specs_agree :
    checkParamIndDecl unitDeclP = some [unitTySpec, unitCtorSpec] := by
  simp only [unitTySpec, unitCtorSpec, unitTyName, unitCtorName]
  exact check_unitDeclP

open Mettapedia.Languages.MeTTa.PureKernel.BoolDecl in
theorem boolDeclP_specs_agree :
    checkParamIndDecl boolDeclP = some [boolTySpec, boolTrueSpec, boolFalseSpec] := by
  simp only [boolTySpec, boolTrueSpec, boolFalseSpec, boolTyName, boolTrueName, boolFalseName]
  exact check_boolDeclP

open Mettapedia.Languages.MeTTa.PureKernel.NatDecl in
theorem natDeclP_specs_agree :
    checkParamIndDecl natDeclP = some [natTySpec, natZeroSpec, natSuccSpec] := by
  simp only [natTySpec, natZeroSpec, natSuccSpec, natTyName, natZeroName, natSuccName]
  exact check_natDeclP

end Mettapedia.Languages.MeTTa.PureKernel.Telescope
