import MeTTailCore.MeTTaIL.Match
import MeTTailCore.EvalIR

namespace MeTTailCore.MeTTaIL.RecursiveConstructors

open MeTTailCore.MeTTaIL.Syntax
open MeTTailCore.MeTTaIL.Match
open MeTTailCore.EvalIR

/-- Ground constructor/query terms accepted by the staged recursive
constructor layer.

Positive example: `Cons 1 (Cons 2 Nil)` is ground.
Negative example: `Cons $x Nil` is not ground and will not be specialized. -/
partial def isGroundPattern : Pattern → Bool
  | .apply _ args => args.all isGroundPattern
  | .collection _ elems rest => rest.isNone && elems.all isGroundPattern
  | .fvar _ | .bvar _ | .lambda _ | .multiLambda _ _ | .subst _ _ => false

/-- Look up an already-specialized concrete call. -/
def lookupSpecializedHead (seen : List (Pattern × String)) (call : Pattern) : Option String :=
  (seen.find? (fun entry => entry.1 == call)).map Prod.snd

/-- Keep generated helper heads MM2-safe and readable. -/
def sanitizeHead (head : String) : String :=
  String.ofList <| head.toList.map fun c => if c.isAlphanum then c else '_'

/-- Generated helper head for one concrete constructor-specialized call. -/
def mkSpecializedHead (head : String) (n : Nat) : String :=
  s!"__ctor_{sanitizeHead head}_{n}"

/-- Current staged layer only specializes ordinary premise-free recursive
rules. More expressive premises stay in the existing guarded/premise layers. -/
def firstMatchingConcreteRule?
    (rules : List RewriteRule) (call : Pattern) : Option (RewriteRule × Bindings) :=
  rules.findSome? fun rule =>
    if !rule.premises.isEmpty then
      none
    else
      match matchPatternMeTTa rule.left call with
      | [] => none
      | bindings :: _ => some (rule, bindings)

/-- Heads that the staged constructor layer may recursively specialize. -/
def knownRuleHeads (rules : List RewriteRule) : List String :=
  rules.filterMap fun rule =>
    match rule.left with
    | .apply head _ => some head
    | _ => none

/-- Simple quoted-string atom decoding aligned with the current Rust recursive
lane tests.

Positive example: `"just"` becomes `just`.
Negative example: `just` stays a symbolic constructor atom, not a string. -/
def decodeQuotedStringAtom? (atom : String) : Option String :=
  if atom.length ≥ 2 && atom.toList.head? == some '"' && atom.back == '"' then
    some (((atom.drop 1).dropEnd 1).toString)
  else
    none

/-- String equality in the current stable core is explicit, not polymorphic. -/
def isStringLiteralPattern : Pattern → Bool
  | .apply ctor [] => (decodeQuotedStringAtom? ctor).isSome
  | _ => false

structure ConstructorSpecState where
  nextId : Nat := 0
  seen : List (Pattern × String) := []
  outRules : List EvalRule := []
deriving Repr

mutual

/-- Specialize a concrete call into a nullary/core-friendly recursive helper.

Positive example: `len(Cons 1 Nil)` becomes a generated nullary helper head.
Negative example: a call with no matching constructor clause fails closed. -/
def specializeConcreteCall?
    (fuel : Nat) (rules : List RewriteRule) (knownHeads : List String)
    (call : Pattern) (st : ConstructorSpecState) :
    Option (String × ConstructorSpecState) :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
      match lookupSpecializedHead st.seen call with
      | some head => some (head, st)
      | none =>
          match call, firstMatchingConcreteRule? rules call with
          | .apply head _, some (rule, bindings) =>
              let specHead := mkSpecializedHead head st.nextId
              let seeded :=
                { st with
                    nextId := st.nextId + 1
                    seen := (call, specHead) :: st.seen }
              let rhs := applyBindings bindings rule.right
              match specializeGroundBody? fuel' rules knownHeads rhs seeded with
              | some (body, st') =>
                  let outRule : EvalRule := { head := specHead, params := [], body := body }
                  some (specHead, { st' with outRules := st'.outRules ++ [outRule] })
              | none => none
          | _, _ => none

/-- Lower a fully-instantiated constructor-specialized body into the current
stable `EvalIR` core, recursively specializing any remaining concrete
user-defined calls on the way. -/
def specializeGroundBody?
    (fuel : Nat) (rules : List RewriteRule) (knownHeads : List String)
    (body : Pattern) (st : ConstructorSpecState) :
    Option (EvalNode × ConstructorSpecState) :=
  match body with
  | .apply ctor [] =>
      if let some n := ctor.toInt? then
        some (.intLit n, st)
      else if ctor == "True" then
        some (.boolLit true, st)
      else if ctor == "False" then
        some (.boolLit false, st)
      else if let some s := decodeQuotedStringAtom? ctor then
        some (.strLit s, st)
      else if knownHeads.contains ctor then
        match specializeConcreteCall? fuel rules knownHeads (.apply ctor []) st with
        | some (specHead, st') => some (.userCall specHead [], st')
        | none => none
      else
        none
  | .apply ctor args =>
      if knownHeads.contains ctor && args.all isGroundPattern then
        match specializeConcreteCall? fuel rules knownHeads (.apply ctor args) st with
        | some (specHead, st') => some (.userCall specHead [], st')
        | none => none
      else
        match ctor, args with
        | "if", [c, t, e] =>
            match specializeGroundBody? fuel rules knownHeads c st with
            | some (c', st1) =>
                match specializeGroundBody? fuel rules knownHeads t st1 with
                | some (t', st2) =>
                    match specializeGroundBody? fuel rules knownHeads e st2 with
                    | some (e', st3) =>
                        some (.ifCond c' t' e', st3)
                    | none => none
                | none => none
            | none => none
        | "==", [a, b] =>
            match specializeGroundBody? fuel rules knownHeads a st with
            | some (a', st1) =>
                match specializeGroundBody? fuel rules knownHeads b st1 with
                | some (b', st2) =>
                    if isStringLiteralPattern a || isStringLiteralPattern b then
                      some (.eqStr a' b', st2)
                    else
                      some (.eqInt a' b', st2)
                | none => none
            | none => none
        | "+", [a, b] =>
            match specializeGroundBody? fuel rules knownHeads a st with
            | some (a', st1) =>
                match specializeGroundBody? fuel rules knownHeads b st1 with
                | some (b', st2) => some (.addInt a' b', st2)
                | none => none
            | none => none
        | "-", [a, b] =>
            match specializeGroundBody? fuel rules knownHeads a st with
            | some (a', st1) =>
                match specializeGroundBody? fuel rules knownHeads b st1 with
                | some (b', st2) => some (.subInt a' b', st2)
                | none => none
            | none => none
        | "*", [a, b] =>
            match specializeGroundBody? fuel rules knownHeads a st with
            | some (a', st1) =>
                match specializeGroundBody? fuel rules knownHeads b st1 with
                | some (b', st2) => some (.mulInt a' b', st2)
                | none => none
            | none => none
        | _, _ => none
  | .collection _ _ _ | .fvar _ | .bvar _ | .lambda _ | .multiLambda _ _ | .subst _ _ =>
      none

end

/-- Decode a stable-core scalar pattern result. -/
def patternToEvalValue? : Pattern → Option EvalValue
  | .apply ctor [] =>
      if let some n := ctor.toInt? then
        some (.int n)
      else if ctor == "True" then
        some (.bool true)
      else if ctor == "False" then
        some (.bool false)
      else
        (decodeQuotedStringAtom? ctor).map .str
  | _ => none

/-- Evaluate a ground constructor query to a ground pattern above the stable
core.

Positive example: `idTree(Cons 1 Nil)` evaluates to `Cons 1 Nil`.
Negative example: a non-ground query like `idTree($x)` stays outside this
staged layer. -/
partial def evalGroundPattern? (fuel : Nat) (rules : List RewriteRule) (knownHeads : List String)
    (term : Pattern) : Option Pattern :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
      let rec evalList? (args : List Pattern) : Option (List Pattern) :=
        match args with
        | [] => some []
        | arg :: rest =>
            match evalGroundPattern? fuel' rules knownHeads arg, evalList? rest with
            | some arg', some rest' => some (arg' :: rest')
            | _, _ => none
      match term with
      | .apply ctor [] =>
          if knownHeads.contains ctor then
            match firstMatchingConcreteRule? rules (.apply ctor []) with
            | some (rule, bindings) =>
                evalGroundPattern? fuel' rules knownHeads (applyBindings bindings rule.right)
            | none => none
          else
            some (.apply ctor [])
      | .apply ctor args =>
          match ctor, args with
          | "if", [c, t, e] =>
              match evalGroundPattern? fuel' rules knownHeads c with
              | some (.apply "True" []) => evalGroundPattern? fuel' rules knownHeads t
              | some (.apply "False" []) => evalGroundPattern? fuel' rules knownHeads e
              | _ => none
          | "==", [a, b] =>
              match evalGroundPattern? fuel' rules knownHeads a,
                  evalGroundPattern? fuel' rules knownHeads b with
              | some a', some b' =>
                  match patternToEvalValue? a', patternToEvalValue? b' with
                  | some _, some _ =>
                      some (.apply (if a' == b' then "True" else "False") [])
                  | _, _ => none
              | _, _ => none
          | "+", [a, b] =>
              match evalGroundPattern? fuel' rules knownHeads a,
                  evalGroundPattern? fuel' rules knownHeads b with
              | some a', some b' =>
                  match patternToEvalValue? a', patternToEvalValue? b' with
                  | some (.int x), some (.int y) => some (.apply s!"{x + y}" [])
                  | _, _ => none
              | _, _ => none
          | "-", [a, b] =>
              match evalGroundPattern? fuel' rules knownHeads a,
                  evalGroundPattern? fuel' rules knownHeads b with
              | some a', some b' =>
                  match patternToEvalValue? a', patternToEvalValue? b' with
                  | some (.int x), some (.int y) => some (.apply s!"{x - y}" [])
                  | _, _ => none
              | _, _ => none
          | "*", [a, b] =>
              match evalGroundPattern? fuel' rules knownHeads a,
                  evalGroundPattern? fuel' rules knownHeads b with
              | some a', some b' =>
                  match patternToEvalValue? a', patternToEvalValue? b' with
                  | some (.int x), some (.int y) => some (.apply s!"{x * y}" [])
                  | _, _ => none
              | _, _ => none
          | _, _ =>
              match evalList? args with
              | some args' =>
                  let rebuilt := .apply ctor args'
                  if knownHeads.contains ctor then
                    match firstMatchingConcreteRule? rules rebuilt with
                    | some (rule, bindings) =>
                        evalGroundPattern? fuel' rules knownHeads (applyBindings bindings rule.right)
                    | none => none
                  else
                    some rebuilt
              | none => none
      | .collection _ _ _ | .fvar _ | .bvar _ | .lambda _ | .multiLambda _ _ | .subst _ _ =>
          none

/-- Compile one concrete constructor query into the current stable `EvalIR`
core by generating nullary helpers for each reachable concrete recursive call.

Positive example: `len(Cons 1 (Cons 2 Nil))` compiles to ordinary nullary
helpers over the existing numeric core.
Negative example: `idTree(Cons 1 Nil) = Cons 1 Nil` fails closed because the
stable core still cannot return symbolic constructor terms. -/
def lowerConstructorQueryToEvalIR?
    (fuel : Nat) (query : Pattern) (rules : List RewriteRule) :
    Option (EvalNode × List EvalRule) := do
  if !isGroundPattern query then
    none
  else
    let knownHeads := knownRuleHeads rules
    let (rootHead, st) ← specializeConcreteCall? fuel rules knownHeads query {}
    some (.userCall rootHead [], st.outRules)

/-- Execute the staged constructor layer directly to a ground pattern result.

Positive example: `mirror(Node Leaf (Node Leaf Leaf))` returns a ground
constructor pattern.
Negative example: non-ground queries and unsupported higher-order terms still
fail closed. -/
def runConstructorPatternQuery?
    (fuel : Nat) (query : Pattern) (rules : List RewriteRule) :
    Option Pattern := do
  if !isGroundPattern query then
    none
  else
    evalGroundPattern? fuel rules (knownRuleHeads rules) query

/-- Execute the staged constructor layer by compiling to the stable `EvalIR`
core and then running the existing reference evaluator. -/
def runConstructorQuery?
    (specializeFuel evalFuel : Nat) (query : Pattern) (rules : List RewriteRule) :
    Option EvalValue := do
  let (irQuery, irRules) ← lowerConstructorQueryToEvalIR? specializeFuel query rules
  eval irRules evalFuel irQuery

namespace Examples

def sym (s : String) : Pattern := .apply s []

def app (head : String) (args : List Pattern) : Pattern := .apply head args

def fvar (name : String) : Pattern := .fvar name

def rewriteRule (name : String) (left right : Pattern) : RewriteRule := {
  name := name
  typeContext := []
  premises := []
  left := left
  right := right
}

def qstr (s : String) : Pattern := sym s!"\"{s}\""

def lenRules : List RewriteRule := [
  rewriteRule "len-nil"
    (app "len" [sym "Nil"])
    (sym "0"),
  rewriteRule "len-cons"
    (app "len" [app "Cons" [fvar "h", fvar "t"]])
    (app "+" [sym "1", app "len" [fvar "t"]])
]

def lenQuery : Pattern :=
  app "len" [app "Cons" [sym "1", app "Cons" [sym "2", sym "Nil"]]]

def tagRules : List RewriteRule := [
  rewriteRule "tag-just"
    (app "tag" [app "Just" [fvar "x"]])
    (qstr "just"),
  rewriteRule "tag-nothing"
    (app "tag" [sym "Nothing"])
    (qstr "nothing")
]

def tagQuery : Pattern := app "tag" [app "Just" [sym "5"]]

def treeSizeRules : List RewriteRule := [
  rewriteRule "tree-leaf"
    (app "treeSize" [sym "Leaf"])
    (sym "1"),
  rewriteRule "tree-node"
    (app "treeSize" [app "Node" [fvar "l", fvar "r"]])
    (app "+" [sym "1", app "+" [app "treeSize" [fvar "l"], app "treeSize" [fvar "r"]]])
]

def treeSizeQuery : Pattern :=
  app "treeSize" [app "Node" [sym "Leaf", app "Node" [sym "Leaf", sym "Leaf"]]]

def sumListRules : List RewriteRule := [
  rewriteRule "sum-nil"
    (app "sumList" [sym "Nil"])
    (sym "0"),
  rewriteRule "sum-cons"
    (app "sumList" [app "Cons" [fvar "h", fvar "t"]])
    (app "+" [fvar "h", app "sumList" [fvar "t"]])
]

def sumListQuery : Pattern :=
  app "sumList" [app "Cons" [sym "1", app "Cons" [sym "2", app "Cons" [sym "3", sym "Nil"]]]]

def idTreeRules : List RewriteRule := [
  rewriteRule "id-tree"
    (app "idTree" [fvar "x"])
    (fvar "x")
]

def idTreeQuery : Pattern := app "idTree" [app "Cons" [sym "1", sym "Nil"]]

def mirrorRules : List RewriteRule := [
  rewriteRule "mirror-leaf"
    (app "mirror" [sym "Leaf"])
    (sym "Leaf"),
  rewriteRule "mirror-node"
    (app "mirror" [app "Node" [fvar "l", fvar "r"]])
    (app "Node" [app "mirror" [fvar "r"], app "mirror" [fvar "l"]])
]

def mirrorQuery : Pattern :=
  app "mirror" [app "Node" [sym "Leaf", app "Node" [sym "Leaf", sym "Leaf"]]]

theorem run_len_constructor_query :
    runConstructorQuery? 16 64 lenQuery lenRules = some (.int 2) := by
  native_decide

theorem run_tag_constructor_query :
    runConstructorQuery? 8 32 tagQuery tagRules = some (.str "just") := by
  native_decide

theorem run_tree_size_constructor_query :
    runConstructorQuery? 24 128 treeSizeQuery treeSizeRules = some (.int 5) := by
  native_decide

theorem run_sum_list_constructor_query :
    runConstructorQuery? 24 128 sumListQuery sumListRules = some (.int 6) := by
  native_decide

theorem constructor_result_outside_core_fails_closed :
    runConstructorQuery? 8 32 idTreeQuery idTreeRules = none := by
  native_decide

theorem run_id_tree_constructor_pattern_query :
    runConstructorPatternQuery? 8 idTreeQuery idTreeRules =
      some (app "Cons" [sym "1", sym "Nil"]) := by
  native_decide

theorem run_mirror_constructor_pattern_query :
    runConstructorPatternQuery? 16 mirrorQuery mirrorRules =
      some (app "Node" [app "Node" [sym "Leaf", sym "Leaf"], sym "Leaf"]) := by
  native_decide

#eval if runConstructorQuery? 16 64 lenQuery lenRules == some (.int 2) then
    "recursive constructors: len(Cons 1 (Cons 2 Nil)) = 2 ✓"
  else
    "recursive constructors: len specialization FAILED"

#eval if runConstructorQuery? 8 32 tagQuery tagRules == some (.str "just") then
    "recursive constructors: tag(Just 5) = \"just\" ✓"
  else
    "recursive constructors: tag specialization FAILED"

#eval if runConstructorQuery? 24 128 treeSizeQuery treeSizeRules == some (.int 5) then
    "recursive constructors: treeSize(Node Leaf (Node Leaf Leaf)) = 5 ✓"
  else
    "recursive constructors: treeSize specialization FAILED"

#eval if runConstructorQuery? 24 128 sumListQuery sumListRules == some (.int 6) then
    "recursive constructors: sumList(Cons 1 (Cons 2 (Cons 3 Nil))) = 6 ✓"
  else
    "recursive constructors: sumList specialization FAILED"

#eval if runConstructorQuery? 8 32 idTreeQuery idTreeRules == none then
    "recursive constructors: symbolic result outside core fails closed ✓"
  else
    "recursive constructors: symbolic fail-closed check FAILED"

#eval if runConstructorPatternQuery? 8 idTreeQuery idTreeRules ==
    some (app "Cons" [sym "1", sym "Nil"]) then
    "recursive constructors: idTree(Cons 1 Nil) = Cons 1 Nil ✓"
  else
    "recursive constructors: idTree staged pattern result FAILED"

#eval if runConstructorPatternQuery? 16 mirrorQuery mirrorRules ==
    some (app "Node" [app "Node" [sym "Leaf", sym "Leaf"], sym "Leaf"]) then
    "recursive constructors: mirror(Node Leaf (Node Leaf Leaf)) = Node (Node Leaf Leaf) Leaf ✓"
  else
    "recursive constructors: mirror staged pattern result FAILED"

end Examples

end MeTTailCore.MeTTaIL.RecursiveConstructors
