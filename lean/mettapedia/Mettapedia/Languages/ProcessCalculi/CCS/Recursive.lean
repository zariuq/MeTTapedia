import Mettapedia.Languages.ProcessCalculi.CCS.Blocks
import Mettapedia.GSLT.LanguageDef.WellSortedChecker
import Mettapedia.GSLT.LanguageDef.TypedBoundSubstitution
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Substitution

/-!
# CCS with recursion

Milner's CCS with parametric constants, in its reaction presentation. A constant is defined by a guarded sum over its
parameters, `A(x₀, …, xₖ₋₁) ≝ α₀.P₀ + … + αₘ.Pₘ` (`Definition`), and the sum uses no other name. The definitions are
the environment the calculus runs in (`definitionsEnv`); the calculus is one language for all of them (`ccsRecCalc`).
A call `A(a₀, …, aₖ₋₁)` (`CCall`) names its constant by a numeral, the definition's position, and lists its
arguments.

**A call takes part as its body, when one of its body's summands is taken.** A component offers guards (`offers`): a
sum its summands, a call the summands of its constant's body with the arguments for the parameters (`body`). An
action and the co-action on the same name, offered by two components standing in a parallel composition, react, and
a silent summand of an offer is taken:

- `CallTau`: `A(ã) ~> p` when the body offers `τ.p`;
- `CallAct`: `A(ã) | [~a.q + n] | rest ~> p | q | rest` when the body offers `a.p`;
- `CallCoAct`: `[a.p + m] | A(ã) | rest ~> p | q | rest` when the body offers `~a.q`;
- `CallCall`: `A(ã) | B(b̃) | rest ~> p | q | rest` when the bodies offer `a.p` and `~a.q`.

The body is the relation `Body`, which the environment answers with the sum of the instantiated summands. Every
metavariable of these rules is bound and used outside any binder.

Unfolding is a step, not a law: a call and its body are different states with the same behaviour, as in Milner's
semantics of constants. The static theory stays CCS's, with calls as atoms (`ccsRecBlockLanguage`), so the
restriction-block canonical form decides it.

## References

- Milner (1989), "Communication and Concurrency", chapter 2
- Milner (1999), "Communicating and Mobile Systems: the π-Calculus", chapter 4
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.CCS.Recursive

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextSubstitution (Assignment substitute)
open Mettapedia.GSLT.LanguageDef.WellSorted (HasType FreeTypeContext checkHasType checkHasType_sound
  TypedBoundAssignment isObjectPattern parameterType?)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks
open Mettapedia.Languages.ProcessCalculi.CCS
open Mettapedia.Languages.ProcessCalculi.CCS.Blocks (ccsBlock)

/-! ## Calls -/

/-- The numeral naming the constant defined at a position. -/
def constant : Nat → Pattern
  | 0 => .apply "CZ" []
  | index + 1 => .apply "CS" [constant index]

/-- The arguments of a call, as a list. -/
def arguments : List Pattern → Pattern
  | [] => .apply "CArgNil" []
  | argument :: rest => .apply "CArgCons" [argument, arguments rest]

/-- **A call** of the constant defined at a position: `A(a₀, …, aₖ₋₁)`. -/
def call (index : Nat) (names : List Pattern) : Pattern := .apply "CCall" [constant index, arguments names]

/-- The arguments of a call to a constant of `arity` parameters, when it lists that many. -/
def argumentsOf : Nat → Pattern → Option (List Pattern)
  | 0, pattern => if pattern = .apply "CArgNil" [] then some [] else none
  | arity + 1, .apply label [argument, rest] =>
      if label = "CArgCons" then (argumentsOf arity rest).map (argument :: ·) else none
  | _ + 1, _ => none

theorem argumentsOf_arguments : ∀ names : List Pattern, argumentsOf names.length (arguments names) = some names
  | [] => rfl
  | name :: names => by simp [argumentsOf, arguments, argumentsOf_arguments names]

theorem arguments_of_argumentsOf {arity : Nat} {pattern : Pattern} {names : List Pattern}
    (found : argumentsOf arity pattern = some names) : pattern = arguments names ∧ names.length = arity := by
  induction arity generalizing pattern names with
  | zero =>
      simp only [argumentsOf] at found
      split_ifs at found with isNil
      simp only [Option.some.injEq] at found
      subst found isNil
      exact ⟨rfl, rfl⟩
  | succ arity inner =>
      cases pattern with
      | apply label args =>
          match args, found with
          | [argument, rest], found =>
              simp only [argumentsOf] at found
              split_ifs at found with isCons
              obtain ⟨tail, tailFound, rfl⟩ := Option.map_eq_some_iff.mp found
              obtain ⟨rfl, length⟩ := inner tailFound
              subst isCons
              exact ⟨rfl, by simp [length]⟩
          | [], found | [_], found | _ :: _ :: _ :: _, found => simp [argumentsOf] at found
      | _ => simp [argumentsOf] at found

/-! ## Definitions -/

/-- **A constant's definition**: `A(x₀, …, xₖ₋₁) ≝ α₀.P₀ + … + αₘ.Pₘ`, a guarded sum over its parameters, the
parameter `xᵢ` the bound variable `i` of the summands. -/
structure Definition where
  arity : Nat
  guards : List Pattern
  deriving Repr, DecidableEq

/-- The arguments for the parameters: `xᵢ ↦ aᵢ`. -/
def argumentAssignment (names : List Pattern) : Assignment :=
  fun index => names.getD index (.bvar (index - names.length))

/-- The summands of a definition with the arguments for its parameters. -/
def Definition.instantiate (definition : Definition) (names : List Pattern) : List Pattern :=
  definition.guards.map (substitute (argumentAssignment names))

/-- The definition a numeral names. -/
def lookup (definitions : List Definition) (name : Pattern) : Option Definition :=
  ((List.range definitions.length).find? fun index => constant index == name).bind (definitions[·]?)

/-- **The body of a call**: the summands of its constant's definition with the arguments for the parameters. -/
def body (definitions : List Definition) (name args : Pattern) : Option (List Pattern) :=
  (lookup definitions name).bind fun definition =>
    (argumentsOf definition.arity args).map definition.instantiate

/-- **What a component offers**: a sum its summands, a call the summands of its body. -/
def offers (definitions : List Definition) : Pattern → Option (List Pattern)
  | .apply "CSum" [.collection .hashBag guards _] => some guards
  | .apply "CCall" [name, args] => body definitions name args
  | _ => none

/-- **The definitions as an environment**: the relation `Body` holds of a constant, a list of arguments and the sum
of the summands of its body. -/
def definitionsEnv (definitions : List Definition) : RelationEnv where
  tuples relation request :=
    match relation, request with
    | "Body", [name, args, _] =>
        match body definitions name args with
        | some guards => [[name, args, .apply "CSum" [.collection .hashBag guards none]]]
        | none => []
    | _, _ => []

theorem definitionsEnv_body (definitions : List Definition) (name args offered : Pattern) :
    (definitionsEnv definitions).tuples "Body" [name, args, offered] =
      match body definitions name args with
      | some guards => [[name, args, .apply "CSum" [.collection .hashBag guards none]]]
      | none => [] := rfl

/-! ## The calculus -/

/-- A call of a constant: `A(ã)`. -/
def callRule : GrammarRule :=
  { label := "CCall", category := "Proc",
    params := [.simple "k" (TypeExpr.base "Const"), .simple "args" (TypeExpr.base "Args")],
    syntaxPattern := [.nonTerminal "k", .terminal "(", .nonTerminal "args", .terminal ")"] }

/-- The first constant. -/
def constZeroRule : GrammarRule :=
  { label := "CZ", category := "Const", params := [], syntaxPattern := [.terminal "κ"] }

/-- The next constant. -/
def constSuccRule : GrammarRule :=
  { label := "CS", category := "Const", params := [.simple "k" (TypeExpr.base "Const")],
    syntaxPattern := [.terminal "S", .nonTerminal "k"] }

/-- No arguments. -/
def argumentsNilRule : GrammarRule :=
  { label := "CArgNil", category := "Args", params := [], syntaxPattern := [.terminal "·"] }

/-- An argument before the others. -/
def argumentsConsRule : GrammarRule :=
  { label := "CArgCons", category := "Args",
    params := [.simple "a" (TypeExpr.base "Name"), .simple "rest" (TypeExpr.base "Args")],
    syntaxPattern := [.nonTerminal "a", .terminal ",", .nonTerminal "rest"] }

/-- The summand pattern `[guard(x, y) + others]`. -/
def offering (guard : String) (arguments : List String) (others : String) : Pattern :=
  .apply "CSum" [.collection .hashBag [.apply guard (arguments.map .fvar)] (some others)]

/-- A call pattern `K(A)`. -/
def callPattern (name args : String) : Pattern := .apply "CCall" [.fvar name, .fvar args]

/-- `A(ã) ~> p` if the body of `A(ã)` offers `τ.p` -/
def callTauRewrite : RewriteRule where
  name := "CallTau"
  typeContext := [("K", .base "Const"), ("A", .base "Args"), ("p", .base "Proc")]
  premises := [.relationQuery "Body" [.fvar "K", .fvar "A", offering "CTau" ["p"] "m"]]
  left := callPattern "K" "A"
  right := .fvar "p"

/-- `A(ã) | [~a.q + n] | rest ~> p | q | rest` if the body of `A(ã)` offers `a.p` -/
def callActRewrite : RewriteRule where
  name := "CallAct"
  typeContext := [("K", .base "Const"), ("A", .base "Args"), ("a", .base "Name"), ("p", .base "Proc"),
    ("q", .base "Proc")]
  premises := [.relationQuery "Body" [.fvar "K", .fvar "A", offering "CAct" ["a", "p"] "m"]]
  left := .collection .hashBag [callPattern "K" "A", offering "CCoAct" ["a", "q"] "n"] (some "rest")
  right := .collection .hashBag [.fvar "p", .fvar "q"] (some "rest")

/-- `[a.p + m] | A(ã) | rest ~> p | q | rest` if the body of `A(ã)` offers `~a.q` -/
def callCoActRewrite : RewriteRule where
  name := "CallCoAct"
  typeContext := [("K", .base "Const"), ("A", .base "Args"), ("a", .base "Name"), ("p", .base "Proc"),
    ("q", .base "Proc")]
  premises := [.relationQuery "Body" [.fvar "K", .fvar "A", offering "CCoAct" ["a", "q"] "n"]]
  left := .collection .hashBag [offering "CAct" ["a", "p"] "m", callPattern "K" "A"] (some "rest")
  right := .collection .hashBag [.fvar "p", .fvar "q"] (some "rest")

/-- `A(ã) | B(b̃) | rest ~> p | q | rest` if the body of `A(ã)` offers `a.p` and that of `B(b̃)` offers `~a.q` -/
def callCallRewrite : RewriteRule where
  name := "CallCall"
  typeContext := [("K", .base "Const"), ("A", .base "Args"), ("L", .base "Const"), ("B", .base "Args"),
    ("a", .base "Name"), ("p", .base "Proc"), ("q", .base "Proc")]
  premises := [.relationQuery "Body" [.fvar "K", .fvar "A", offering "CAct" ["a", "p"] "m"],
    .relationQuery "Body" [.fvar "L", .fvar "B", offering "CCoAct" ["a", "q"] "n"]]
  left := .collection .hashBag [callPattern "K" "A", callPattern "L" "B"] (some "rest")
  right := .collection .hashBag [.fvar "p", .fvar "q"] (some "rest")

/-- **CCS with recursion**: finite CCS with calls of constants.

- **Sorts**: `["Proc", "Name", "Guard", "Const", "Args"]` (names are variables of the name sort, constants
  numerals, arguments lists of names)
- **Equations**: those of finite CCS: restriction of inaction, exchange of restrictions, scope extrusion and the
  empty sum, besides the laws of the parallel bag and of the multiset of summands
- **Reductions**: React, Tau, ParCong and ResCong, and CallTau, CallAct, CallCoAct and CallCall through the
  definitions -/
def ccsRecCalc : LanguageDef :=
  { name := "CCSRec"
    types := ["Proc", "Name", "Guard", "Const", "Args"]
    terms := [ccsCalc.terms[0], ccsCalc.terms[1], ccsCalc.terms[2], ccsCalc.terms[3], ccsCalc.terms[4],
      ccsCalc.terms[5], ccsCalc.terms[6], callRule, constZeroRule, constSuccRule, argumentsNilRule,
      argumentsConsRule]
    equations := ccsCalc.equations
    rewrites := [ccsReactRewrite, ccsTauRewrite, ccsParCongRewrite, ccsResCongRewrite, callTauRewrite,
      callActRewrite, callCoActRewrite, callCallRewrite] }

theorem ccsRecCalc_rewrites :
    ccsRecCalc.rewrites = [ccsReactRewrite, ccsTauRewrite, ccsParCongRewrite, ccsResCongRewrite, callTauRewrite,
      callActRewrite, callCoActRewrite, callCallRewrite] := rfl

/-! ## Admitted definitions -/

/-- No free names: the parameters are a definition's only names. -/
def noFreeNames : FreeTypeContext := fun _ => none

/-- **Admitted definitions**: every summand is an object guard over its definition's parameters, with no free name. -/
def admits (definitions : List Definition) : Bool :=
  definitions.all fun definition => definition.guards.all fun guard =>
    checkHasType ccsRecCalc noFreeNames (List.replicate definition.arity (.base "Name")) guard (.base "Guard") &&
      isObjectPattern guard

theorem lookup_mem {definitions : List Definition} {name : Pattern} {definition : Definition}
    (found : lookup definitions name = some definition) : definition ∈ definitions := by
  unfold lookup at found
  obtain ⟨index, -, at'⟩ := Option.bind_eq_some_iff.mp found
  exact List.mem_of_getElem? at'

theorem guard_admitted {definitions : List Definition} (admitted : admits definitions = true)
    {definition : Definition} (member : definition ∈ definitions) {guard : Pattern} (guardMember : guard ∈ definition.guards) :
    HasType ccsRecCalc noFreeNames (List.replicate definition.arity (.base "Name")) guard (.base "Guard") ∧
      isObjectPattern guard = true := by
  have each := List.all_eq_true.mp (List.all_eq_true.mp admitted definition member) guard guardMember
  simp only [Bool.and_eq_true] at each
  exact ⟨checkHasType_sound each.1, each.2⟩

/-- **The summands of a call's body are guards**, wherever the call's arguments are names. -/
theorem instantiate_typed {definitions : List Definition} (admitted : admits definitions = true)
    {definition : Definition} (member : definition ∈ definitions) {free : FreeTypeContext} {bound : List TypeExpr}
    {names : List Pattern} (length : names.length = definition.arity)
    (named : ∀ name ∈ names, HasType ccsRecCalc free bound name (.base "Name")) :
    ∀ guard ∈ definition.instantiate names, HasType ccsRecCalc free bound guard (.base "Guard") := by
  intro guard member'
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member'
  obtain ⟨typed, -⟩ := guard_admitted admitted member originalMember
  have retyped := typed.recontextualizeFree (target := free) fun {name} {_} _ unbound => by
    simp [noFreeNames] at unbound
  let assignment : TypedBoundAssignment ccsRecCalc free (List.replicate definition.arity (.base "Name")) bound :=
    { assignment := argumentAssignment names
      typed := by
        intro index type lookup
        have inRange : index < definition.arity := by
          by_contra outside
          rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_gt outside)] at lookup
          cases lookup
        rw [List.getElem?_replicate_of_lt inRange] at lookup
        cases lookup
        have present : index < names.length := length ▸ inRange
        simpa [argumentAssignment, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem present] using
          named names[index] (List.getElem_mem present) }
  exact retyped.substituteBound assignment

/-- **The summands of a call's body are object terms**, when its arguments are. -/
theorem instantiate_objects {definitions : List Definition} (admitted : admits definitions = true)
    {definition : Definition} (member : definition ∈ definitions) {names : List Pattern}
    (objects : ∀ name ∈ names, isObjectPattern name = true) :
    ∀ guard ∈ definition.instantiate names, isObjectPattern guard = true := by
  intro guard member'
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member'
  refine isObject_substitute original ?_ (guard_admitted admitted member originalMember).2
  intro index
  simp only [argumentAssignment]
  by_cases present : index < names.length
  · simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem present] using
      objects names[index] (List.getElem_mem present)
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt present), isObjectPattern]

/-! ## A calculus with restriction -/

/-- The sum is a named multiset of guards. -/
theorem sum_namedMultiset : NamedMultiset ccsRecCalc.terms[2] "Proc" :=
  ⟨rfl, rfl, ⟨"gs", "Guard", rfl, by decide⟩⟩

/-- Parallel composition is a bare bag beside the sum. -/
theorem ccsRec_parallelBag : ParallelBag ccsRecCalc ccsRecCalc.terms[1] "CNil" ["CSum"] where
  bagAuthored := List.getElem_mem (by decide)
  bagShape := ⟨"ps", rfl⟩
  bagAlgebra := rfl
  representedBare := rfl
  unitAuthored := ⟨ccsRecCalc.terms[0], List.getElem_mem (by decide), rfl, rfl, rfl⟩
  otherParameters := by
    intro rule member notBag
    simp only [ccsRecCalc, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · left; simp [ccsCalc]
    · exact absurd rfl notBag
    · exact .inr ⟨by simp [ccsCalc], sum_namedMultiset⟩
    all_goals left; simp [ccsCalc, callRule, constZeroRule, constSuccRule, argumentsNilRule, argumentsConsRule,
      TermParam.typeExpr, Mettapedia.GSLT.LanguageDef.BagNormalForm.collectionFree]

/-- **CCS with recursion is a calculus with restriction**: calls are atoms of its blocks. -/
instance ccsRecBlockLanguage : BlockLanguage ccsRecCalc ccsBlock where
  bag := ⟨ccsRecCalc.terms[1], ccsRec_parallelBag, rfl⟩
  equations := rfl
  restrictAuthored := ⟨ccsRecCalc.terms[3], List.getElem_mem (by decide), rfl⟩
  restrictShape := by
    intro rule member labelIs
    simp only [ccsRecCalc, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all [ccsCalc, callRule, constZeroRule, constSuccRule, argumentsNilRule, argumentsConsRule]
  unitShape := by
    intro rule member labelIs
    simp only [ccsRecCalc, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all [ccsCalc, callRule, constZeroRule, constSuccRule, argumentsNilRule, argumentsConsRule]
  multisetShape := by
    intro rule member listed
    simp only [ccsRecCalc, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [ccsCalc, callRule, constZeroRule, constSuccRule, argumentsNilRule, argumentsConsRule] at listed
    exact sum_namedMultiset
  emptyUnitShape := by
    intro label listed
    simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
    subst listed
    refine ⟨by simp, fun rule member labelIs => ?_⟩
    simp only [ccsRecCalc, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all [ccsCalc, callRule, constZeroRule, constSuccRule, argumentsNilRule, argumentsConsRule]
  emptyUnitAuthored := by
    intro label listed
    simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
    subst listed
    exact ⟨ccsRecCalc.terms[2], List.getElem_mem (by decide), rfl⟩
  labelsUnique := by decide
  params := by
    intro rule member notBare notMultiset parameter present
    simp only [ccsRecCalc, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp [ccsCalc] at present
    · exact absurd ⟨"ps", .hashBag, .base "Proc", rfl⟩ notBare
    · simp [ccsCalc] at notMultiset
    all_goals
      simp only [ccsCalc, callRule, constZeroRule, constSuccRule, argumentsNilRule, argumentsConsRule,
        List.getElem_cons_succ, List.getElem_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at present
    all_goals rcases present with rfl | rfl <;> simp [parameterType?]
  arrowsAbstract := by
    intro rule member notBare notMultiset parameter present domain sort found
    simp only [ccsRecCalc, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp [ccsCalc] at present
    · exact absurd ⟨"ps", .hashBag, .base "Proc", rfl⟩ notBare
    · simp [ccsCalc] at notMultiset
    all_goals
      simp only [ccsCalc, callRule, constZeroRule, constSuccRule, argumentsNilRule, argumentsConsRule,
        List.getElem_cons_succ, List.getElem_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at present
    all_goals rcases present with rfl | rfl <;> simp_all [parameterType?]

end Mettapedia.Languages.ProcessCalculi.CCS.Recursive
