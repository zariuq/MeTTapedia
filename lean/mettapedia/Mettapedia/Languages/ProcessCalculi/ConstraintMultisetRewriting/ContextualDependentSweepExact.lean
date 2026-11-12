import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSweepWithin

/-!
# Exact arguments: the pattern condition with the inclusion of universes written out

A local can be passed to an unknown whenever its declared type is **below** the type the unknown declares for that
argument: a universe below a universe, a Π type with a codomain below. Written with the inclusion of one type in
the next, such an argument is `↑x`, not a variable. A store has **exact arguments** when every local passed to an
unknown is declared at the very type the unknown declares for it; then the arguments are variables in that
reading too.

* `exactCode`, `exactSide`, `exactEquation`, `contextExact`, **`storeExact`**: the definition, as a test on codes.
  It walks a side under the telescope of its annotation, so that every bound variable has its declared type, and
  compares, at every application of an unknown to a bound variable, the declared type of the variable with the
  type the unknown's declaration gives to that argument after the earlier ones (`domainAfter`). The comparison is
  identity of codes: a declared type that is equal to the unknown's but written differently is counted as not
  exact. Bound variables of abstractions that are not under the annotation's telescope have no declared type in
  the code and are not compared.
* `Problem.exact`: the test on the store of a raw problem, for the sweep.
* `Problem.narrowsTo`, `sweepExact`: the sweep split by the test; a stuck exact problem is tagged when one of its
  unknowns' declarations, written one universe position lower, gives a problem that commits.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentExact

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedContextual

variable {Head : Type}

/-- The head of an application spine and its arguments, first argument first. -/
def spineOf {n : Nat} : Tm Head n → Tm Head n × List (Tm Head n)
  | .app function argument => ((spineOf function).1, (spineOf function).2 ++ [argument])
  | other => (other, [])

/-- **The type a function type gives to its next argument**, after the earlier arguments. -/
def domainAfter {n : Nat} : Tm Head n → List (Tm Head n) → Option (Tm Head n)
  | .pi domain _, [] => some domain
  | .pi _ codomain, argument :: rest => domainAfter (inst0 argument codomain) rest
  | _, _ => none

/-- The declared types of the variables in scope, one binder further in; `none` where the code does not give
one. -/
def extendTypes {n : Nat} (types : Fin n → Option (Tm Head n)) (newest : Option (Tm Head n)) :
    Fin (n + 1) → Option (Tm Head (n + 1)) :=
  Fin.cases (newest.map (Presentation.rename wk)) fun index => (types index).map (Presentation.rename wk)

variable [DecidableEq Head]

/-- **One argument is exact**: where the head of the function is an unknown (a variable beyond the `locals`
innermost) and the argument is a local with a declared type, that type is the type the unknown's declaration gives
to the argument. -/
def argumentExact {n : Nat} (types : Fin n → Option (Tm Head n)) (locals : Nat) (function argument : Tm Head n) :
    Bool :=
  match (spineOf function).1, argument with
  | .var head, .var index =>
      if locals ≤ head.val ∧ index.val < locals then
        match types head, types index with
        | some headType, some localType =>
            match domainAfter headType (spineOf function).2 with
            | some domain => decide (localType = domain)
            | none => true
        | _, _ => true
      else true
  | _, _ => true

/-- **Every argument of a code is exact.** -/
def exactCode : {n : Nat} → (Fin n → Option (Tm Head n)) → Nat → Tm Head n → Bool
  | _, _, _, .var _ => true
  | _, _, _, .const _ => true
  | _, _, _, .head _ => true
  | _, types, locals, .pi domain codomain =>
      exactCode types locals domain && exactCode (extendTypes types (some domain)) (locals + 1) codomain
  | _, types, locals, .sigma first second =>
      exactCode types locals first && exactCode (extendTypes types (some first)) (locals + 1) second
  | _, types, locals, .id type left right =>
      exactCode types locals type && exactCode types locals left && exactCode types locals right
  | _, types, locals, .lam inner => exactCode (extendTypes types none) (locals + 1) inner
  | _, types, locals, .app function argument =>
      argumentExact types locals function argument && exactCode types locals function &&
        exactCode types locals argument
  | _, types, locals, .pair first second => exactCode types locals first && exactCode types locals second
  | _, types, locals, .fst inner => exactCode types locals inner
  | _, types, locals, .snd inner => exactCode types locals inner
  | _, types, locals, .refl point => exactCode types locals point

/-- **Every argument of a side is exact**, the side read under the telescope of its type. -/
def exactSide : {n : Nat} → (Fin n → Option (Tm Head n)) → Nat → Tm Head n → Tm Head n → Bool
  | _, types, locals, .pi domain codomain, .lam inner =>
      exactSide (extendTypes types (some domain)) (locals + 1) codomain inner
  | _, types, locals, _, side => exactCode types locals side

/-- The declared types of a context. -/
def declaredTypes {n : Nat} (context : Ctx Head n) : Fin n → Option (Tm Head n) :=
  fun index => some (Ctx.lookup context index)

/-- **Every declaration of a context has exact arguments**: an unknown's declared type passes the locals of its
own telescope to older unknowns at their declared types. -/
def contextExact : {n : Nat} → Ctx Head n → Bool
  | _, .nil => true
  | _, .snoc context type => contextExact context && exactCode (declaredTypes context) 0 type

end ContextualDependentExact

namespace ContextualDependentSweep

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentPatternFiring.Controls ContextualDependentExact

/-- **An equation has exact arguments**: its annotation and both sides, the sides read under the annotation's
telescope. -/
def exactEquation {Γ : Context setting.R} (equation : Equation (TotalTerm Γ)) : Bool :=
  exactCode (declaredTypes Γ.raw) 0 equation.1.1.code &&
    exactSide (declaredTypes Γ.raw) 0 equation.1.1.code equation.1.2.code &&
    exactSide (declaredTypes Γ.raw) 0 equation.1.1.code equation.2.2.code

/-- **A store has exact arguments**: its context and every equation. -/
def storeExact {Γ : Context setting.R} (store : EquationStore (TotalTerm Γ)) : Bool :=
  contextExact Γ.raw && store.all exactEquation

/-- The test on the store of a raw problem; an ill-typed problem counts as exact. -/
def Problem.exact (problem : Problem) : Bool :=
  match problem.store? with
  | none => true
  | some ⟨_, store⟩ => storeExact store

/-- The universe at the end of a telescope of Π types, written as `U0`. -/
def Raw.endLowered : Raw → Option Raw
  | .u1 => some .u0
  | .u2 => some .u0
  | .pi domain codomain => (Raw.endLowered codomain).map fun lower => .pi domain lower
  | _ => none

/-- The problems with one unknown's declaration lowered at its end. -/
def Problem.narrowings (problem : Problem) : List Problem :=
  (List.range problem.unknowns.length).filterMap fun position =>
    match problem.unknowns[position]? with
    | none => none
    | some declared =>
        (Raw.endLowered declared).map fun lower =>
          { problem with unknowns := problem.unknowns.set position lower }

/-- **A problem narrows to a committed problem**: one of its unknowns, declared with `U0` at the end of its
telescope, gives a problem on which the family commits. -/
def Problem.narrowsTo (verdict : Problem → Verdict) (problem : Problem) : Bool :=
  problem.narrowings.any fun narrowed => verdict narrowed == .ended .committed

/-- **Tallies split by exact arguments.** The stuck exact problems are kept: those that narrow to a committed
problem are counted, the others are listed. -/
structure Exactness where
  exact : LevelTally := {}
  inexact : LevelTally := {}
  narrowing : Nat := 0
  others : List Problem := []
  deriving Inhabited

/-- Count one problem. -/
def Exactness.count (verdict : Problem → Verdict) (tally : Exactness) (problem : Problem) : Exactness :=
  let read := verdict problem
  if problem.exact then
    let counted := { tally with exact := tally.exact.count problem read }
    if read = .ended .stuck then
      if problem.narrowsTo verdict then { counted with narrowing := counted.narrowing + 1 }
      else { counted with others := problem :: counted.others }
    else counted
  else { tally with inexact := tally.inexact.count problem read }

/-- **Sweep annotations at full width, split by exact arguments**: pairs of thinned sides and, for the first
`patterns` pattern sides, the pattern against every typed side in both orders, counted together. -/
def sweepExact (verdict : Problem → Verdict) (unknowns : List Raw) (Γ : Context setting.R)
    (annotations : List Raw) (bodySize shortSize perForm cap patterns : Nat) (start : Exactness := {}) :
    Exactness :=
  annotations.foldl (init := start) fun tally annotation =>
    let all := allSidesOf Γ annotation bodySize shortSize
    let thinned := thin (fun side => s!"{side.lamCount}:{(side.lamBody).headForm side.lamCount}") perForm cap all
    let chosen := (all.filter Raw.isPattern).take patterns
    let pairs := thinned.foldl (init := tally) fun tally left =>
      thinned.foldl (init := tally) fun tally right =>
        tally.count verdict { unknowns := unknowns, equations := [(annotation, left, right)] }
    chosen.foldl (init := pairs) fun tally pattern =>
      all.foldl (init := tally) fun tally side =>
        (tally.count verdict { unknowns := unknowns, equations := [(annotation, pattern, side)] }).count verdict
          { unknowns := unknowns, equations := [(annotation, side, pattern)] }

/-- Sweep a list of problems, split by exact arguments. -/
def sweepExactList (verdict : Problem → Verdict) (problems : List Problem) (start : Exactness := {}) : Exactness :=
  problems.foldl (init := start) (Exactness.count verdict)

/-- One line of counts over all universes. -/
def LevelTally.line (tally : LevelTally) : String :=
  s!"{tally.total} problems (U0 {tally.at0.total}, U1 {tally.at1.total}, U2 {tally.at2.total}): ill-typed " ++
    s!"{tally.at0.illTyped + tally.at1.illTyped + tally.at2.illTyped}, outside " ++
    s!"{tally.at0.outside + tally.at1.outside + tally.at2.outside}, committed " ++
    s!"{tally.at0.committed + tally.at1.committed + tally.at2.committed}, refuted " ++
    s!"{tally.at0.refuted + tally.at1.refuted + tally.at2.refuted}, stuck {tally.stuck} " ++
    s!"(U0 {tally.at0.stuck}, U1 {tally.at1.stuck}, U2 {tally.at2.stuck})"

/-- A reading of split tallies: the counts, and every stuck exact problem that does not narrow. -/
def Exactness.toText (tally : Exactness) : String :=
  s!" EXACT {tally.exact.line}\n   stuck exact: {tally.narrowing} narrow to a committed problem, " ++
    s!"{tally.others.length} others\n" ++
    "\n".intercalate (tally.others.reverse.map fun problem => s!"   OTHER {problem.toText}") ++
    s!"\n NOT EXACT {tally.inexact.line}"

end ContextualDependentSweep
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
