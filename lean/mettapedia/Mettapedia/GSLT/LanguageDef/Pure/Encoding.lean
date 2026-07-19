/-
# Pure statement encoding

Frozen benchmark statements are first elaborated by Lean and then reified into
the deliberately small Pure syntax.  Reification rejects every elaborated node
except an unlevelled sort, de Bruijn variables, Pi, lambda, and application.
The resulting terms use an independently parsed prefix-code at the parity
boundary.
-/

import Mathlib.Tactic
import Mettapedia.GSLT.LanguageDef.Pure.Statics

namespace Mettapedia.GSLT.LanguageDef.Pure

namespace Expr

/-- Maximum constructor depth, used as parser fuel. -/
def depth : Expr → Nat
  | .sort => 1
  | .bvar _ => 1
  | .pi domain body => max domain.depth body.depth + 1
  | .lam domain body => max domain.depth body.depth + 1
  | .app fn argument => max fn.depth argument.depth + 1

/-- Prefix code used by the Lean/Python parity boundary. -/
def encode : Expr → List Nat
  | .sort => [0]
  | .bvar index => [1, index]
  | .pi domain body => 2 :: (domain.encode ++ body.encode)
  | .lam domain body => 3 :: (domain.encode ++ body.encode)
  | .app fn argument => 4 :: (fn.encode ++ argument.encode)

/-- Independent prefix-code parser.  The returned suffix permits recursion. -/
def decodeFuel : Nat → List Nat → Option (Expr × List Nat)
  | 0, _ => none
  | _fuel + 1, [] => none
  | _fuel + 1, 0 :: rest => some (.sort, rest)
  | _fuel + 1, 1 :: index :: rest => some (.bvar index, rest)
  | _fuel + 1, 1 :: [] => none
  | fuel + 1, 2 :: rest => do
      let (domain, rest) ← decodeFuel fuel rest
      let (body, rest) ← decodeFuel fuel rest
      pure (.pi domain body, rest)
  | fuel + 1, 3 :: rest => do
      let (domain, rest) ← decodeFuel fuel rest
      let (body, rest) ← decodeFuel fuel rest
      pure (.lam domain body, rest)
  | fuel + 1, 4 :: rest => do
      let (fn, rest) ← decodeFuel fuel rest
      let (argument, rest) ← decodeFuel fuel rest
      pure (.app fn argument, rest)
  | _fuel + 1, _ :: _ => none

/-- Parse exactly one expression and reject trailing tokens. -/
def decode (code : List Nat) : Option Expr := do
  let (expression, rest) ← decodeFuel (code.length + 1) code
  if rest.isEmpty then some expression else none

theorem depth_lt_encode_length_add_one (expression : Expr) :
    expression.depth < expression.encode.length + 1 := by
  induction expression with
  | sort => simp [depth, encode]
  | bvar index => simp [depth, encode]
  | pi domain body domainIH bodyIH =>
      simp only [depth, encode, List.length_cons, List.length_append]
      omega
  | lam domain body domainIH bodyIH =>
      simp only [depth, encode, List.length_cons, List.length_append]
      omega
  | app fn argument fnIH argumentIH =>
      simp only [depth, encode, List.length_cons, List.length_append]
      omega

/-- The independent parser consumes precisely an encoded expression. -/
theorem decodeFuel_encode_append (expression : Expr) (suffix : List Nat)
    (fuel : Nat) (hdepth : expression.depth < fuel) :
    decodeFuel fuel (expression.encode ++ suffix) = some (expression, suffix) := by
  induction expression generalizing fuel suffix with
  | sort =>
      cases fuel with
      | zero => simp [depth] at hdepth
      | succ fuel => simp [encode, decodeFuel]
  | bvar index =>
      cases fuel with
      | zero => simp [depth] at hdepth
      | succ fuel => simp [encode, decodeFuel]
  | pi domain body domainIH bodyIH =>
      cases fuel with
      | zero => simp [depth] at hdepth
      | succ fuel =>
          simp only [depth, Nat.max_lt, Nat.add_lt_add_iff_right] at hdepth
          simp only [encode, List.cons_append, List.append_assoc, decodeFuel]
          rw [domainIH (body.encode ++ suffix) fuel hdepth.1]
          simp [bodyIH suffix fuel hdepth.2]
  | lam domain body domainIH bodyIH =>
      cases fuel with
      | zero => simp [depth] at hdepth
      | succ fuel =>
          simp only [depth, Nat.max_lt, Nat.add_lt_add_iff_right] at hdepth
          simp only [encode, List.cons_append, List.append_assoc, decodeFuel]
          rw [domainIH (body.encode ++ suffix) fuel hdepth.1]
          simp [bodyIH suffix fuel hdepth.2]
  | app fn argument fnIH argumentIH =>
      cases fuel with
      | zero => simp [depth] at hdepth
      | succ fuel =>
          simp only [depth, Nat.max_lt, Nat.add_lt_add_iff_right] at hdepth
          simp only [encode, List.cons_append, List.append_assoc, decodeFuel]
          rw [fnIH (argument.encode ++ suffix) fuel hdepth.1]
          simp [argumentIH suffix fuel hdepth.2]

/-- Every admitted Pure statement survives the cross-lane prefix codec. -/
theorem decode_encode (expression : Expr) :
    decode expression.encode = some expression := by
  unfold decode
  have hparse :
      decodeFuel (expression.encode.length + 1) expression.encode =
        some (expression, []) := by
    simpa using
      decodeFuel_encode_append expression [] (expression.encode.length + 1)
        (depth_lt_encode_length_add_one expression)
  rw [hparse]
  rfl

end Expr

end Mettapedia.GSLT.LanguageDef.Pure

/-! ## Closed elaboration-to-Pure bridge -/

open Lean Elab Term Meta

namespace Mettapedia.GSLT.LanguageDef.PureReify

private partial def reify : Lean.Expr → TermElabM Lean.Expr
  | .sort (.succ .zero) =>
      pure <| mkConst ``Mettapedia.GSLT.LanguageDef.Pure.Expr.sort
  | .sort _ =>
      throwError "Pure reification accepts exactly Type 0"
  | .bvar index =>
      pure <| mkApp
        (mkConst ``Mettapedia.GSLT.LanguageDef.Pure.Expr.bvar)
        (mkNatLit index)
  | .forallE _ domain body _ => do
      pure <| mkApp2
        (mkConst ``Mettapedia.GSLT.LanguageDef.Pure.Expr.pi)
        (← reify domain) (← reify body)
  | .lam _ domain body _ => do
      pure <| mkApp2
        (mkConst ``Mettapedia.GSLT.LanguageDef.Pure.Expr.lam)
        (← reify domain) (← reify body)
  | .app fn argument => do
      pure <| mkApp2
        (mkConst ``Mettapedia.GSLT.LanguageDef.Pure.Expr.app)
        (← reify fn) (← reify argument)
  | .mdata _ expression => reify expression
  | .letE _ _ _ _ _ =>
      throwError "Pure reification rejected let expression"
  | .fvar identifier =>
      throwError "Pure reification rejected free variable {identifier.name}"
  | .mvar identifier =>
      throwError "Pure reification rejected unresolved metavariable {identifier.name}"
  | .const name _ =>
      throwError "Pure reification rejected constant {name}"
  | .lit _ =>
      throwError "Pure reification rejected literal"
  | .proj typeName index _ =>
      throwError "Pure reification rejected projection {typeName}.{index}"

/--
Elaborate a closed Lean type and reify only its Pure fragment.  Lean supplies
implicit lambda domains and de Bruijn indices; this elaborator then rejects any
node outside the fragment instead of approximating it.
-/
elab "pure_type% " typeSyntax:term : term => do
  let expression ← Term.elabType typeSyntax
  Term.synthesizeSyntheticMVarsNoPostponing
  reify (← instantiateMVars expression)

end Mettapedia.GSLT.LanguageDef.PureReify
