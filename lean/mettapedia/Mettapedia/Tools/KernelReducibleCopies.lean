import Lean

/-!
# Kernel evaluation through proven reducible replacements

The kernel cannot evaluate a definition by well-founded recursion: its body
applies `WellFounded.fix` to an opaque proof of well-foundedness. A closed
computation that reaches such a definition is therefore stuck in the kernel,
however small it is.

Given equations `@replacement = @original`, where `replacement` is a
kernel-reducible implementation of `original`, this module copies every
definition whose body reaches an `original`, with each `original` replaced by
its `replacement` and each reached definition by its copy, and proves each
copy equal to the definition it copies. A closed equation is then checked by
the kernel on the copies and transported back along these equalities. No
existing definition changes; the copies are new constants, each with a
kernel-checked equation to its source.

Proofs inside a copied body are kept: each is cast along the replacement
equalities from the type it has in the definition to the type the copy expects
of it.
-/

set_option autoImplicit false

namespace Mettapedia.Tools.KernelReducibleCopies

open Lean Meta Elab Tactic

/-- A definition to replace, with the equation `@replacement.{us} = @original.{vs}`. -/
structure Replacement where
  original : Name
  equation : Name

/-- Read `@replacement = @original` off an equation theorem. -/
def Replacement.ofEquation (equation : Name) : MetaM Replacement := do
  let info ← getConstInfo equation
  let some (_, _, .const original _) := info.type.eq?
    | throwError "{equation} must state `@replacement = @original` for a constant `original`"
  return { original, equation }

/-- Which constants reach a replaced definition, and the copies made so far. -/
structure CopyCache where
  reaches : Std.HashMap Name Bool := {}
  copies : Std.HashMap Name (Name × Name) := {}

/-- The replacements, and the prefix under which copies are declared. -/
structure CopyContext where
  replacements : Array Replacement
  copyPrefix : Name

abbrev CopyM := ReaderT CopyContext (StateRefT CopyCache MetaM)

private def replacementFor? (name : Name) : CopyM (Option Replacement) :=
  return (← read).replacements.find? (·.original == name)

/-- Whether the body of a definition reaches a replaced definition through
other definitions. A copy does not: its body mentions originals only inside
the casts of its proofs. -/
partial def reachesReplaced (name : Name) : CopyM Bool := do
  if (← replacementFor? name).isSome then return true
  if name.anyS (· == "_kernelCopy") then return false
  if let some known := (← get).reaches[name]? then return known
  modify fun cache => { cache with reaches := cache.reaches.insert name false }
  let some (.defnInfo definition) := (← getEnv).find? name | return false
  let mut result := false
  for used in definition.value.getUsedConstants do
    if ← reachesReplaced used then
      result := true
      break
  modify fun cache => { cache with reaches := cache.reaches.insert name result }
  return result

/-- Distinct constant occurrences, with their universe levels, in order of discovery.
Shared subterms are visited once. -/
def constantOccurrences (term : Expr) : Array (Name × List Level) := Id.run do
  let mut found : Array (Name × List Level) := #[]
  let mut seen : Std.HashSet (Name × List Level) := {}
  let mut visited : Std.HashSet Expr := {}
  let mut pending : Array Expr := #[term]
  while !pending.isEmpty do
    let current := pending.back!
    pending := pending.pop
    if visited.contains current then continue
    visited := visited.insert current
    match current with
    | .const name levels =>
        unless seen.contains (name, levels) do
          seen := seen.insert (name, levels)
          found := found.push (name, levels)
    | .app function argument => pending := pending.push function |>.push argument
    | .lam _ type body _ | .forallE _ type body _ => pending := pending.push type |>.push body
    | .letE _ type value body _ => pending := pending.push type |>.push value |>.push body
    | .mdata _ body | .proj _ _ body => pending := pending.push body
    | _ => pure ()
  return found

/-- Each replaced occurrence maps to its replacement and a proof `replacement = occurrence`. -/
abbrev Substitution := Std.HashMap (Name × List Level) (Expr × Expr)

private def mentions (substitution : Substitution) (term : Expr) : Bool :=
  (term.find? fun part => match part with
    | .const name levels => substitution.contains (name, levels)
    | _ => false).isSome

/-- Whether `part` is a proof (a quick syntactic test first). -/
private def isProofTerm (part : Expr) : MetaM Bool := do
  match ← isProofQuick part with
  | .true => return true
  | .false => return false
  | .undef => isProof part

/-- `expected = expected[originals]`, one `congrArg` per replacement that occurs in it. -/
private def towardOriginals (expected : Expr) (substitution : Substitution) : MetaM (Option Expr) := do
  let mut current := expected
  let mut proof? : Option Expr := none
  for ((name, levels), (replacement, equation)) in substitution.toList do
    unless (current.find? (· == replacement)).isSome do continue
    let motive ← withLocalDeclD `x (← inferType replacement) fun bound => do
      mkLambdaFVars #[bound] (current.replace fun part =>
        if part == replacement then some bound else none)
    let step ← mkCongrArg motive equation
    proof? := some <| ← match proof? with
      | none => pure step
      | some earlier => mkEqTrans earlier step
    current := (mkApp motive (.const name levels)).headBeta
  return proof?

/-- Replace each occurrence by its replacement. A proof is kept, and cast from its
expected type with the originals to its expected type in the replaced term: the
original term is well typed, so the proof has the former type. The expected
type is the one the application computes, so a proof whose statement holds only
by unfolding a replaced definition (for example a structure field proof about
another field) is cast correctly. A `let` whose value changes is unfolded, so
that the expected types that depend on it mention the replacement. -/
private partial def substitute (term : Expr) (substitution : Substitution) : MetaM Expr :=
  visit term
where
  castTo (expected proof : Expr) : MetaM Expr := do
    match ← towardOriginals expected substitution with
    | none => return proof
    | some equation => mkEqMPR equation proof
  visit (term : Expr) : MetaM Expr := do
    unless mentions substitution term do return term
    match term with
    | .const name levels =>
        return (substitution[(name, levels)]?.map (·.1)).getD term
    | .app .. =>
        let function ← visit term.getAppFn
        let mut type ← inferType function
        let mut arguments : Array Expr := #[]
        for argument in term.getAppArgs do
          type ← whnf type
          let .forallE _ domain body _ := type
            | throwError "Cannot copy {term}: its head is not a function"
          let argument ← if ← isProofTerm argument then castTo domain argument else visit argument
          arguments := arguments.push argument
          type := body.instantiate1 argument
        return mkAppN function arguments
    | .lam name domain body info =>
        withLocalDecl name info (← visit domain) fun bound => do
          mkLambdaFVars #[bound] (← visit (body.instantiate1 bound))
    | .forallE name domain body info =>
        withLocalDecl name info (← visit domain) fun bound => do
          mkForallFVars #[bound] (← visit (body.instantiate1 bound))
    | .letE name type value body _ =>
        if mentions substitution value then visit (body.instantiate1 value)
        else withLetDecl name (← visit type) value fun bound => do
          mkLetFVars #[bound] (← visit (body.instantiate1 bound))
    | .proj structureName index body => return .proj structureName index (← visit body)
    | .mdata data body => return .mdata data (← visit body)
    | _ => return term

/-- A proof of `substitute term substitution = term`. Each occurrence `o` is
abstracted with a hypothesis `x = o`; the copy and the term are the two ends
of a chain that moves one occurrence at a time by `Eq.rec`. Casts become casts
along `rfl` at the far end, which proof irrelevance identifies with the
original proofs. -/
private def substitutionEquation (term : Expr) (occurrences : Array (Name × List Level))
    (substitution : Substitution) : MetaM Expr := do
  let originals := occurrences.map fun (name, levels) => Expr.const name levels
  let types ← originals.mapM inferType
  let rec abstract (index : Nat) (bounds : Array Expr) : MetaM Expr := do
    if h : index < originals.size then
      withLocalDeclD `x types[index]! fun bound => do
        withLocalDeclD `h (← mkEq bound originals[index]) fun equation =>
          abstract (index + 1) (bounds.push bound |>.push equation)
    else
      let mut abstractSubstitution : Substitution := {}
      for position in [:occurrences.size] do
        abstractSubstitution := abstractSubstitution.insert occurrences[position]!
          (bounds[2 * position]!, bounds[2 * position + 1]!)
      mkLambdaFVars bounds (← substitute term abstractSubstitution)
  let family ← abstract 0 #[]
  let argumentsMovedBefore (moved : Nat) : MetaM (Array Expr) := do
    let mut arguments : Array Expr := #[]
    for position in [:occurrences.size] do
      if position < moved then
        arguments := arguments.push originals[position]! |>.push (← mkEqRefl originals[position]!)
      else
        let (replacement, equation) := substitution[occurrences[position]!]!
        arguments := arguments.push replacement |>.push equation
    return arguments
  let mut proof? : Option Expr := none
  for position in [:occurrences.size] do
    let original := originals[position]!
    let type := types[position]!
    let (replacement, equation) := substitution[occurrences[position]!]!
    let arguments ← argumentsMovedBefore position
    let member ← withLocalDeclD `y type fun bound => do
      withLocalDeclD `e (← mkEq bound original) fun hypothesis => do
        let chosen := (arguments.set! (2 * position) bound).set! (2 * position + 1) hypothesis
        mkLambdaFVars #[bound, hypothesis] (mkAppN family chosen).headBeta
    let target := (mkApp2 member original (← mkEqRefl original)).headBeta
    let motive ← withLocalDeclD `y type fun bound => do
      withLocalDeclD `e (← mkEq original bound) fun hypothesis => do
        mkLambdaFVars #[bound, hypothesis]
          (← mkEq (mkApp2 member bound (← mkEqSymm hypothesis)).headBeta target)
    let step ← mkEqRec motive (← mkEqRefl target) (← mkEqSymm equation)
    proof? := some <| ← match proof? with
      | none => pure step
      | some earlier => mkEqTrans earlier step
  match proof? with
  | none => mkEqRefl term
  | some proof => return proof

private def checkedOptions (options : Options) : Options :=
  debug.skipKernelTC.set (Elab.async.set options false) false

mutual

/-- The copy of a definition and its equation `@copy.{us} = @definition.{us}`. -/
partial def copyConstant (name : Name) : CopyM (Name × Name) := do
  if let some known := (← get).copies[name]? then return known
  let copyName := (← read).copyPrefix ++ name
  let equationName := copyName ++ `eq
  if (← getEnv).contains equationName then
    modify fun cache => { cache with copies := cache.copies.insert name (copyName, equationName) }
    return (copyName, equationName)
  let some (.defnInfo definition) := (← getEnv).find? name
    | throwError "Cannot copy {name}: it is not a definition"
  let (value, equation) ← copyTerm definition.value
  let levels := definition.levelParams.map Level.param
  withOptions checkedOptions do
    addDecl <| .defnDecl {
      name := copyName, levelParams := definition.levelParams, type := definition.type,
      value, hints := definition.hints, safety := .safe }
    addDecl <| .thmDecl {
      name := equationName, levelParams := definition.levelParams,
      type := ← mkEq (.const copyName levels) (.const name levels), value := equation }
  modify fun cache => { cache with copies := cache.copies.insert name (copyName, equationName) }
  return (copyName, equationName)

/-- `(copy, proof : copy = term)`, where `copy` reaches no replaced definition. -/
partial def copyTerm (term : Expr) : CopyM (Expr × Expr) := do
  let occurrences ← (constantOccurrences term).filterM fun (name, _) => reachesReplaced name
  if occurrences.isEmpty then return (term, ← mkEqRefl term)
  let mut substitution : Substitution := {}
  for (name, levels) in occurrences do
    if let some replacement ← replacementFor? name then
      let info ← getConstInfo replacement.equation
      let some (_, _, .const _ equationLevels) := info.type.eq?
        | throwError "Malformed replacement equation {replacement.equation}"
      let assignment := info.levelParams.map fun parameter =>
        match (equationLevels.zip levels).find? (·.1 == Level.param parameter) with
        | some (_, level) => level
        | none => Level.zero
      let some (_, copy, _) := (info.type.instantiateLevelParams info.levelParams assignment).eq?
        | throwError "Malformed replacement equation {replacement.equation}"
      substitution := substitution.insert (name, levels)
        (copy, .const replacement.equation assignment)
    else
      let (copyName, equationName) ← copyConstant name
      substitution := substitution.insert (name, levels)
        (.const copyName levels, .const equationName levels)
  let copy ← substitute term substitution
  return (copy, ← substitutionEquation term occurrences substitution)

end

/-- Run a copy computation with replacements read from equation theorems. Copies
are declared under `_kernelCopy`, below the declaration being elaborated if any,
otherwise below the main module. -/
def CopyM.run' {α : Type} (equations : Array Name) (action : CopyM α) (cache : CopyCache := {})
    (declaration? : Option Name := none) : MetaM (α × CopyCache) := do
  let replacements ← equations.mapM Replacement.ofEquation
  let mainModule ← getMainModule
  let copyPrefix := match declaration? with
    | some declaration => declaration ++ `_kernelCopy
    | none => `_kernelCopy ++ mainModule
  (action.run { replacements, copyPrefix }).run cache

/-- `kernel_reflexivity using [e₁, e₂, ...]` closes a closed equation by kernel
reduction, after replacing each `original` of the equations `@replacement = @original`
by its `replacement` in copies of the definitions that reach it. -/
elab "kernel_reflexivity " "using " "[" equations:ident,+ "]" : tactic => do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  if target.hasFVar || target.hasMVar || target.hasLevelParam || target.hasSorry ||
      (← getEnv).hasUnsafe target then
    throwError "Expected a closed safe equality"
  let names ← equations.getElems.mapM fun equation => realizeGlobalConstNoOverloadWithInfo equation
  let ((copied, transport), _) ← CopyM.run' names (copyTerm target) (declaration? := ← Term.getDeclName?)
  let some (_, _, right) := copied.eq? | throwError "Expected an equality"
  let checked ← withOptions checkedOptions <| mkAuxLemma [] copied (← mkEqRefl right) (cache := false)
  let proof ← mkEqMP transport (mkConst checked)
  goal.assign (mkConst (← withOptions checkedOptions <| mkAuxLemma [] target proof (cache := false)))
  replaceMainGoal []

/-! ## Example: a definition that reaches a well-founded function -/

/-- Ackermann's function, by well-founded recursion on the lexicographic order. -/
private def ackermann : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => ackermann m 1
  | m + 1, n + 1 => ackermann m (ackermann (m + 1) n)
termination_by m n => (m, n)

/-- The same function by structural recursion. -/
private def ackermannStructural : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, n => Nat.rec (ackermannStructural m 1) (fun _ previous => ackermannStructural m previous) n

private theorem ackermannStructural_eq : ackermannStructural = ackermann := by
  funext m n
  induction m generalizing n with
  | zero => simp [ackermannStructural, ackermann]
  | succ m ihm =>
      induction n with
      | zero =>
          rw [ackermann, ← ihm]
          rfl
      | succ n ihn =>
          rw [ackermann, ← ihn, ← ihm]
          rfl

/-- A definition that reaches `ackermann` through its body. -/
private def ackermannRow (count : Nat) : List Nat := (List.range count).map (ackermann 2)

example : ackermannRow 4 = [3, 5, 7, 9] := by
  kernel_reflexivity using [ackermannStructural_eq]

/-- Without the replacement the kernel is stuck at the well-founded recursion. -/
example : True := by
  fail_if_success have : ackermannRow 4 = [3, 5, 7, 9] := by decide +kernel
  trivial

/-- A false equation is still refused. -/
example : True := by
  fail_if_success
    have : ackermannRow 4 = [3, 5, 7, 10] := by
      kernel_reflexivity using [ackermannStructural_eq]
  trivial

end Mettapedia.Tools.KernelReducibleCopies
