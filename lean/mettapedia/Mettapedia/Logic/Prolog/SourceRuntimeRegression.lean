import Mettapedia.Logic.Prolog.SourceRuntime
import Mettapedia.Logic.LP.RuntimeReadback

/-!
# Concrete meta-call regressions

These fixtures start from canonical source terms, materialize them into the
shared LP heap, and execute through `SourceRuntime`.  They discriminate
dynamic heap decoding, `call/N` argument extension, DFS order, and the local
cut boundary installed by the shared engine.
-/

namespace Mettapedia.Logic.Prolog.SourceRuntimeRegression

open Mettapedia.Logic
open SourceSignature SourceRuntime

def x : SourceSignature.Term := var "X" 0
def g : SourceSignature.Term := var "G" 0
def y : SourceSignature.Term := var "Y" 0
def z : SourceSignature.Term := var "Z" 0
def leftVar : SourceSignature.Term := var "Left" 0
def rightVar : SourceSignature.Term := var "Right" 0
def bagVar : SourceSignature.Term := var "Bag" 0
def innerVar : SourceSignature.Term := var "Inner" 0
def outerVar : SourceSignature.Term := var "Outer" 0
def referenceVar : SourceSignature.Term := var "Reference" 0
def otherReferenceVar : SourceSignature.Term := var "OtherReference" 0

def equality (left right : SourceSignature.Term) : SourceSignature.Term :=
  compound "=" [left, right]

def conjunction (left right : SourceSignature.Term) : SourceSignature.Term :=
  compound "," [left, right]

def disjunction (left right : SourceSignature.Term) : SourceSignature.Term :=
  compound ";" [left, right]

def pair (left right : SourceSignature.Term) : SourceSignature.Term :=
  compound "pair" [left, right]

def metaGoal (callable : SourceSignature.Term) : SourceSignature.Goal :=
  SourceSignature.call "call" [callable]

def fact (name : String) (arguments : List SourceSignature.Term) :
    SourceSignature.Clause := {
  head := predicate name arguments
  body := .succeed
}

/-! ## Explicit `format/2` observations -/

def format2AtomicOutput : SourceSignature.Goal :=
  SourceSignature.call "format" [
    SourceSignature.string "~w~n",
    SourceSignature.list [SourceSignature.atom "a"]
  ]

def format2StringOutput : SourceSignature.Goal :=
  SourceSignature.call "format" [
    SourceSignature.string "~w~n",
    SourceSignature.list [SourceSignature.string "rendered"]
  ]

def format2UnsupportedDirective : SourceSignature.Goal :=
  SourceSignature.call "format" [
    SourceSignature.string "~q",
    SourceSignature.list [SourceSignature.atom "a"]
  ]

/-- Advance the one shared session until its first exact output observation.
Answers, failure, and terminal results cannot be mistaken for text. -/
def firstOutput : Nat → Session → Option (String × Session)
  | 0, _ => none
  | fuel + 1, session =>
      match RuntimeControl.stepSession session with
      | .terminal _ _ => none
      | .next resumed none => firstOutput fuel resumed
      | .next resumed (some (.output text)) => some (text, resumed)
      | .next resumed (some (.answer _)) => firstOutput fuel resumed

/-- `format/2` emits before the ordinary answer and leaves no heap or trail
debris after the answer stream completes. -/
def format2OutputTrace : Option (String × Nat × Nat) :=
  match SourceRuntime.openEmpty [] format2AtomicOutput with
  | .error _ => none
  | .ok session =>
      match firstOutput 128 session with
      | some ("a\n", afterOutput) =>
          match SourceRuntime.pullSession 128 afterOutput with
          | .answer _ afterAnswer =>
              match SourceRuntime.pullSession 128 afterAnswer with
              | .terminal (.completed memory) _ =>
                  some ("a\n", memory.heap.size, memory.trail.size)
              | _ => none
          | _ => none
      | _ => none

def format2EmitsExactOutput : Bool :=
  format2OutputTrace == some ("a\n", 0, 0)

def format2StringOutputTrace : Option (String × Nat × Nat) :=
  match SourceRuntime.openEmpty [] format2StringOutput with
  | .error _ => none
  | .ok session =>
      match firstOutput 128 session with
      | some ("rendered\n", afterOutput) =>
          match SourceRuntime.pullSession 128 afterOutput with
          | .answer _ afterAnswer =>
              match SourceRuntime.pullSession 128 afterAnswer with
              | .terminal (.completed memory) _ =>
                  some ("rendered\n", memory.heap.size, memory.trail.size)
              | _ => none
          | _ => none
      | _ => none

def format2WritesStringPayload : Bool :=
  format2StringOutputTrace == some ("rendered\n", 0, 0)

/-- Unknown format directives are visible runtime errors, never omitted text
or ordinary Prolog failure. -/
def format2RejectsUnsupportedDirective : Bool :=
  match SourceRuntime.openEmpty [] format2UnsupportedDirective with
  | .error _ => false
  | .ok session =>
      match SourceRuntime.pullSession 128 session with
      | .terminal (.runtimeError .unsupportedFormatDirective _) _ => true
      | _ => false

private def answerAtom? (answer : LP.RuntimeQuery.Answer Sigma) :
    Option String :=
  match answer.queryVarMap with
  | [(_, address)] =>
      match LP.RuntimeReadback.Heap.readTerm answer.memory.heap address with
      | .ok (.const (.atom name)) => some name
      | _ => none
  | _ => none

def collectAtoms : Nat → Session → Option (List String × Nat × Nat)
  | 0, _ => none
  | budget + 1, session =>
      match SourceRuntime.pullSession 128 session with
      | .open _ => none
      | .terminal (.completed memory) _ =>
          some ([], memory.heap.size, memory.trail.size)
      | .terminal (.runtimeError _ _) _ => none
      | .terminal (.raised _ _) _ => none
      | .answer answer resumed =>
          match answerAtom? answer, collectAtoms budget resumed with
          | some value, some (rest, heapSize, trailSize) =>
              some (value :: rest, heapSize, trailSize)
          | _, _ => none

def collectCount : Nat → Nat → Session → Option (Nat × Nat × Nat)
  | 0, _, _ => none
  | answerBudget + 1, count, session =>
      match SourceRuntime.pullSession 128 session with
      | .open _ => none
      | .terminal (.completed memory) _ =>
          some (count, memory.heap.size, memory.trail.size)
      | .terminal (.runtimeError _ _) _ => none
      | .terminal (.raised _ _) _ => none
      | .answer _ resumed => collectCount answerBudget (count + 1) resumed

private def answerTermFor? (identity : SourceSignature.Variable)
    (answer : LP.RuntimeQuery.Answer Sigma) : Option (LP.Term Sigma.scoped) :=
  match answer.queryVarMap.find? fun entry =>
      decide (entry.1 = LP.ScopedVar.at 0 identity) with
  | none => none
  | some (_, address) =>
      match LP.RuntimeReadback.Heap.readTerm answer.memory.heap address with
      | .ok term => some term
      | .error _ => none

def collectTermsFor : Nat → SourceSignature.Variable → Session →
    Option (List (LP.Term Sigma.scoped) × Nat × Nat)
  | 0, _, _ => none
  | budget + 1, identity, session =>
      match SourceRuntime.pullSession 512 session with
      | .open _ => none
      | .terminal (.completed memory) _ =>
          some ([], memory.heap.size, memory.trail.size)
      | .terminal (.runtimeError _ _) _ => none
      | .terminal (.raised _ _) _ => none
      | .answer answer resumed =>
          match answerTermFor? identity answer,
              collectTermsFor budget identity resumed with
          | some value, some (rest, heapSize, trailSize) =>
              some (value :: rest, heapSize, trailSize)
          | _, _ => none

def runTermsFor (program : SourceSignature.Program)
    (goal : SourceSignature.Goal) (identity : SourceSignature.Variable) :
    Option (List (LP.Term Sigma.scoped) × Nat × Nat) :=
  match SourceRuntime.openEmpty program goal with
  | .error _ => none
  | .ok session => collectTermsFor 8 identity session

/-- Finite, executable observation of the dependent runtime term used only by
these source-runtime regressions. -/
inductive RuntimeTermShape where
  | variable (scope : Nat) (spelling : String) (occurrence : Nat)
  | nil
  | atom (name : String)
  | integer (value : Int)
  | floatBits (bits : UInt64)
  | string (value : String)
  | clauseReference (reference : Nat)
  | compound (name : String) (arguments : List RuntimeTermShape)
deriving BEq, Repr

def runtimeTermShape : LP.Term Sigma.scoped → RuntimeTermShape
  | .var identity =>
      .variable identity.scope identity.name.spelling identity.name.occurrence
  | .const .nil => .nil
  | .const (.atom name) => .atom name
  | .const (.integer value) => .integer value
  | .const (.floatBits bits) => .floatBits bits
  | .const (.string value) => .string value
  | .const (.clauseReference reference) => .clauseReference reference
  | .app indicator arguments =>
      .compound indicator.name
        (List.ofFn fun index => runtimeTermShape (arguments index))

def RuntimeTermShape.listElements? : RuntimeTermShape →
    Option (List RuntimeTermShape)
  | .nil => some []
  | .compound "[|]" [head, tail] => do
      let rest ← tail.listElements?
      pure (head :: rest)
  | _ => none

def RuntimeTermShape.atomList? (shape : RuntimeTermShape) :
    Option (List String) := do
  let elements ← shape.listElements?
  elements.mapM fun element =>
    match element with
    | .atom name => some name
    | _ => none

def runAtomBagsFor (program : SourceSignature.Program)
    (goal : SourceSignature.Goal) (identity : SourceSignature.Variable) :
    Option (List (List String) × Nat × Nat) := do
  let (terms, heapSize, trailSize) ← runTermsFor program goal identity
  let bags ← terms.mapM fun term => (runtimeTermShape term).atomList?
  pure (bags, heapSize, trailSize)

def runShapesFor (program : SourceSignature.Program)
    (goal : SourceSignature.Goal) (identity : SourceSignature.Variable) :
    Option (List RuntimeTermShape × Nat × Nat) := do
  let (terms, heapSize, trailSize) ← runTermsFor program goal identity
  pure (terms.map runtimeTermShape, heapSize, trailSize)

def runAtomsFor (program : SourceSignature.Program)
    (goal : SourceSignature.Goal) (identity : SourceSignature.Variable) :
    Option (List String × Nat × Nat) := do
  let (terms, heapSize, trailSize) ← runTermsFor program goal identity
  let atoms ← terms.mapM fun term =>
    match term with
    | .const (.atom name) => some name
    | _ => none
  pure (atoms, heapSize, trailSize)

def runIntegersFor (program : SourceSignature.Program)
    (goal : SourceSignature.Goal) (identity : SourceSignature.Variable) :
    Option (List Int × Nat × Nat) := do
  let (terms, heapSize, trailSize) ← runTermsFor program goal identity
  let integers ← terms.mapM fun term =>
    match term with
    | .const (.integer value) => some value
    | _ => none
  pure (integers, heapSize, trailSize)

def runStringsFor (program : SourceSignature.Program)
    (goal : SourceSignature.Goal) (identity : SourceSignature.Variable) :
    Option (List String × Nat × Nat) := do
  let (terms, heapSize, trailSize) ← runTermsFor program goal identity
  let strings ← terms.mapM fun term =>
    match term with
    | .const (.string value) => some value
    | _ => none
  pure (strings, heapSize, trailSize)

def runAtomsWithFuel (fuel : Nat) (program : SourceSignature.Program)
    (goal : SourceSignature.Goal) :
    Option (List String × Nat × Nat) :=
  match SourceRuntime.openEmpty program goal with
  | .error _ => none
  | .ok session => collectAtoms fuel session

def runAtoms (program : SourceSignature.Program) (goal : SourceSignature.Goal) :
    Option (List String × Nat × Nat) :=
  runAtomsWithFuel 8 program goal

def runCount (program : SourceSignature.Program) (goal : SourceSignature.Goal) :
    Option (Nat × Nat × Nat) :=
  match SourceRuntime.openEmpty program goal with
  | .error _ => none
  | .ok session => collectCount 8 0 session

/-- Run to an uncaught finite atomic exception.  The packet is detached from
the rolled-back heap, whose exact cleanup remains separately observable. -/
def runRaisedAtom (program : SourceSignature.Program)
    (goal : SourceSignature.Goal) : Option (String × Nat × Nat) :=
  match SourceRuntime.openEmpty program goal with
  | .error _ => none
  | .ok session =>
      match SourceRuntime.pullSession 256 session with
      | .terminal (.raised packet memory) _ =>
          match packet.term with
          | .const (.atom name) =>
              some (name, memory.heap.size, memory.trail.size)
          | _ => none
      | _ => none

/-- A disjunction that exists only as a heap term is decoded at call time and
retains SWI's left-to-right answer order. -/
def dynamicDisjunction : SourceSignature.Goal :=
  metaGoal (disjunction (equality x (atom "a")) (equality x (atom "b")))

/-- The inner branch exhausts two bound-and-failed candidates before the outer
right branch runs.  It is a concrete nested-backtrack discriminator: losing
the outer checkpoint, or restoring a child heap as though it were the parent,
would not reach the sole answer `c`. -/
def nestedFailedLeftRetainsOuter : SourceSignature.Goal :=
  .disj
    (.conj
      (.disj (.unify x (atom "a")) (.unify x (atom "b")))
      .fail)
    (.unify x (atom "c"))

/-- A hard conditional commits its else branch after a successful condition
but must leave the older caller alternative.  The two observable answers are
therefore `a` and then `c`, never the else answer `b`. -/
def hardConditionalCommitsElseRetainsCaller : SourceSignature.Goal :=
  .disj
    (.ifThenElse .succeed (.unify x (atom "a")) (.unify x (atom "b")))
    (.unify x (atom "c"))

/-- A soft conditional removes its else delimiter after its first success but
keeps condition alternatives; unlike hard `->/2`, both `a` and `b` remain
observable and the else answer `c` does not run. -/
def softConditionalKeepsConditionAnswers : SourceSignature.Goal :=
  .softIfThenElse
    (.disj (.unify x (atom "a")) (.unify x (atom "b")))
    .succeed
    (.unify x (atom "c"))

/-- `once/1` is a hard return-frame commit over the same inner branch stack:
only the first protected answer survives. -/
def onceCommitsInnerBranch : SourceSignature.Goal :=
  .once (.disj (.unify x (atom "a")) (.unify x (atom "b")))

/-- Cut inside meta-call prunes the meta-call's own right branch but not the
older alternative of its caller.  The only answer is therefore `c`. -/
def metaCutRetainsCaller : SourceSignature.Goal :=
  let guarded := disjunction
    (conjunction (equality x (atom "a"))
      (conjunction (atom "!") (atom "fail")))
    (equality x (atom "b"))
  .disj (metaGoal guarded) (.unify x (atom "c"))

/-- `call/3` appends two arguments to an atomic predicate name. -/
def callThree : SourceSignature.Goal :=
  SourceSignature.call "call" [atom "p", atom "a", atom "b"]

/-- The callable itself may be constructed by unification before `call/1`;
the decoder observes the current heap graph rather than source syntax. -/
def heapBuiltCallable : SourceSignature.Goal :=
  .conj (.unify g (compound "p" [atom "a", atom "b"])) (metaGoal g)

/-! ## Finite `maplist/2` through the ordinary dynamic-call path -/

/-- The source fragment used by `maplist/2` never gets a private evaluator:
each list element becomes an ordinary `call/2` instruction on the shared
engine. -/
def maplistProgram : SourceSignature.Program := [
  fact "mark" [atom "a"],
  fact "mark" [atom "b"],
  fact "user:mark" [atom "a"],
  fact "user:mark" [atom "b"]
]

def maplistSucceeds : SourceSignature.Goal :=
  SourceSignature.call "maplist" [
    atom "mark", SourceSignature.list [atom "a", atom "b"]
  ]

/-- Pinned PeTTa's load directive uses the qualified spelling supplied by
`library(apply)`.  It is deliberately an alias for the same native fragment,
not a reason to load that library as executable source. -/
def qualifiedMaplistSucceeds : SourceSignature.Goal :=
  SourceSignature.call "apply:maplist" [
    atom "user:mark", SourceSignature.list [atom "a", atom "b"]
  ]

/-- A later list element still runs through ordinary call failure, so a finite
`maplist/2` cannot report a prefix as success. -/
def maplistFailsAfterPrefix : SourceSignature.Goal :=
  SourceSignature.call "maplist" [
    atom "mark", SourceSignature.list [atom "a", atom "missing"]
  ]

/-- A cut belonging to a closure call remains below that call's own barrier:
it cannot prune the caller's predicate alternatives or its outer disjunction. -/
def maplistCutClosureProgram : SourceSignature.Program := [
  fact "pick" [atom "a"],
  fact "pick" [atom "b"],
  { head := predicate "cut_closure" [atom "a"], body := .cut }
]

def maplistClosureCutRetainsCaller : SourceSignature.Goal :=
  .disj
    (.conj (SourceSignature.call "pick" [x])
      (SourceSignature.call "maplist" [
        atom "cut_closure", SourceSignature.list [atom "a"]
      ]))
    (.unify x (atom "c"))

/-! ## Finite relational `maplist/3` with an engine-owned result spine -/

def maplist3Program : SourceSignature.Program := [
  fact "copy" [atom "a", atom "a"],
  fact "copy" [atom "b", atom "b"]
]

/-- The result list begins unbound.  The shared engine allocates its spine,
binds it through the canonical unifier, and only then schedules the two
ordinary closure calls. -/
def maplist3BuildsOutput : SourceSignature.Goal :=
  .conj
    (SourceSignature.call "maplist" [
      atom "copy", SourceSignature.list [atom "a", atom "b"], x
    ])
    (.unify x (SourceSignature.list [atom "a", atom "b"]))

/-- A supplied finite output list reuses its existing roots rather than
constructing replacement values. -/
def maplist3UsesKnownOutput : SourceSignature.Goal :=
  SourceSignature.call "maplist" [
    atom "copy", SourceSignature.list [atom "a", atom "b"],
    SourceSignature.list [atom "a", atom "b"]
  ]

/-- An output list of the wrong length fails visibly instead of truncating a
closure sequence. -/
def maplist3RejectsWrongLength : SourceSignature.Goal :=
  SourceSignature.call "maplist" [
    atom "copy", SourceSignature.list [atom "a", atom "b"],
    SourceSignature.list [atom "a"]
  ]

/-- Open output spines are intentionally not yet enumerated.  This must stay
a structured error, never a false success, until relational list generation
lands in the shared engine. -/
def maplist3PartialOutput : SourceSignature.Goal :=
  SourceSignature.call "maplist" [
    atom "copy", SourceSignature.list [atom "a", atom "b"],
    SourceSignature.list [atom "a"] y
  ]

/-- The allocating `/3` entry retains the same nested closure barrier as
`/2`: a closure cut cannot escape through the fresh-output unification frame
to prune caller alternatives. -/
def maplist3CutClosureProgram : SourceSignature.Program := [
  fact "pick" [atom "a"],
  fact "pick" [atom "b"],
  { head := predicate "cut_copy" [atom "a", atom "a"], body := .cut }
]

def maplist3ClosureCutRetainsCaller : SourceSignature.Goal :=
  .disj
    (.conj (SourceSignature.call "pick" [x])
      (.conj
        (SourceSignature.call "maplist" [
          atom "cut_copy", SourceSignature.list [atom "a"], y
        ])
        (.unify y (SourceSignature.list [atom "a"]))))
    (.unify x (atom "c"))

/-! ## Derived negation and non-unifiability on shared hard-if checkpoints -/

def negationRejectsSuccess : SourceSignature.Goal := .neg .succeed

def negationAcceptsFailure : SourceSignature.Goal := .neg .fail

/-- Bindings made by a failing negated goal are restored before its success
continuation runs. -/
def negationRestoresTrialBindings : SourceSignature.Goal :=
  .conj (.neg (.conj (.unify x (atom "a")) .fail))
    (.conj (.isVar x) (.unify x (atom "b")))

/-- A cut inside the protected negated goal cannot prune the caller's older
disjunction alternative. -/
def negationCutRetainsCaller : SourceSignature.Goal :=
  .disj (.neg (.conj .cut .succeed)) (.unify x (atom "c"))

def distinctAtomsAreNotUnifiable : SourceSignature.Goal :=
  .notUnify (atom "a") (atom "b")

def variableAndAtomAreUnifiable : SourceSignature.Goal :=
  .notUnify x (atom "a")

/-- A failed `\=/2` trial restores its temporary binding before the caller's
right alternative is entered. -/
def notUnifyRestoresTrialBindings : SourceSignature.Goal :=
  .disj (.notUnify x (atom "a"))
    (.conj (.isVar x) (.unify x (atom "b")))

/-- These use heap-built callables, pinning the same derived expansion in the
read-only dynamic meta-call decoder rather than only in source classification. -/
def metaNonvarBound : SourceSignature.Goal :=
  metaGoal (compound "nonvar" [atom "a"])

def metaNonvarVariable : SourceSignature.Goal :=
  metaGoal (compound "nonvar" [x])

def metaForallSucceeds : SourceSignature.Goal :=
  metaGoal (compound "forall" [
    disjunction (equality x (atom "a")) (equality x (atom "b")),
    compound "\\=" [x, atom "c"]
  ])

def metaForallFails : SourceSignature.Goal :=
  metaGoal (compound "forall" [
    disjunction (equality x (atom "a")) (equality x (atom "b")),
    equality x (atom "a")
  ])

def metaForallRestoresBindings : SourceSignature.Goal :=
  .conj
    (metaGoal (compound "forall" [equality x (atom "a"), atom "true"]))
    (.conj (.isVar x) (.unify x (atom "c")))

/-! ## Shallow source-term tests through engine-owned dereference -/

def atomAcceptsAtom : SourceSignature.Goal :=
  SourceSignature.call "atom" [atom "a"]

def atomRejectsInteger : SourceSignature.Goal :=
  SourceSignature.call "atom" [integer 1]

def atomRejectsListNil : SourceSignature.Goal :=
  SourceSignature.call "atom" [SourceSignature.nil]

def atomicAcceptsString : SourceSignature.Goal :=
  SourceSignature.call "atomic" [string "a"]

def atomicRejectsCompound : SourceSignature.Goal :=
  SourceSignature.call "atomic" [pair (atom "a") (atom "b")]

def compoundAcceptsPair : SourceSignature.Goal :=
  SourceSignature.call "compound" [pair (atom "a") (atom "b")]

def compoundRejectsAtom : SourceSignature.Goal :=
  SourceSignature.call "compound" [atom "a"]

def numberAcceptsInteger : SourceSignature.Goal :=
  SourceSignature.call "number" [integer 1]

def numberAcceptsFloat : SourceSignature.Goal :=
  SourceSignature.call "number" [floatBits 0]

def numberRejectsAtom : SourceSignature.Goal :=
  SourceSignature.call "number" [atom "a"]

def stringAcceptsString : SourceSignature.Goal :=
  SourceSignature.call "string" [string "a"]

def stringRejectsAtom : SourceSignature.Goal :=
  SourceSignature.call "string" [atom "a"]

/-! ## Cycle-safe graph groundness -/

def groundTest (term : SourceSignature.Term) : SourceSignature.Goal :=
  SourceSignature.call "ground" [term]

def groundAcceptsCompound : SourceSignature.Goal :=
  groundTest (pair (atom "a") (SourceSignature.list [integer 1, atom "b"]))

def groundRejectsVariable : SourceSignature.Goal := groundTest x

def groundRejectsNestedVariable : SourceSignature.Goal :=
  groundTest (pair (atom "a") x)

def groundAcceptsRationalCompound : SourceSignature.Goal :=
  .conj (.unify x (compound "f" [x])) (groundTest x)

def groundRejectsRationalCompoundWithFreeLeaf : SourceSignature.Goal :=
  .conj (.unify x (compound "f" [x, y])) (groundTest x)

/-! ## Cycle-safe proper-list recognition -/

def isListTest (term : SourceSignature.Term) : SourceSignature.Goal :=
  SourceSignature.call "is_list" [term]

def isListAcceptsFinite : SourceSignature.Goal :=
  isListTest (SourceSignature.list [atom "a", atom "b"])

def isListRejectsImproper : SourceSignature.Goal :=
  isListTest (compound "[|]" [atom "a", atom "tail"])

def isListRejectsVariable : SourceSignature.Goal := isListTest x

def isListRejectsRationalSpine : SourceSignature.Goal :=
  .conj (.unify x (compound "[|]" [atom "a", x])) (isListTest x)

def isListAcceptsCyclicHead : SourceSignature.Goal :=
  .conj (.unify y (compound "f" [y]))
    (isListTest (SourceSignature.list [y]))

/-! ## Pure codes-destination formatting -/

def formatAtomicCodes (tail : SourceSignature.Term := SourceSignature.nil) :
    SourceSignature.Goal :=
  SourceSignature.call "format" [
    compound "codes" [x, tail],
    atom "~w",
    SourceSignature.list [atom "a"]
  ]

/-! ## Bidirectional atom/string code conversion -/

def atomCodes (text codes : SourceSignature.Term) : SourceSignature.Goal :=
  SourceSignature.call "atom_codes" [text, codes]

def stringCodes (text codes : SourceSignature.Term) : SourceSignature.Goal :=
  SourceSignature.call "string_codes" [text, codes]

def atomChars (text characters : SourceSignature.Term) : SourceSignature.Goal :=
  SourceSignature.call "atom_chars" [text, characters]

def atomCodesForward : SourceSignature.Goal := atomCodes (atom "aλ") x

def atomCodesReverse : SourceSignature.Goal :=
  atomCodes x (SourceSignature.list [integer 97, integer 955])

def atomCodesBindsElement : SourceSignature.Goal :=
  atomCodes (atom "a") (SourceSignature.list [x])

def atomCodesMismatch : SourceSignature.Goal :=
  atomCodes (atom "a") (SourceSignature.list [integer 98])

def stringCodesForward : SourceSignature.Goal :=
  stringCodes (string "aλ") x

def stringCodesReverse : SourceSignature.Goal :=
  stringCodes x (SourceSignature.list [integer 97, integer 955])

def atomCharsForward : SourceSignature.Goal := atomChars (atom "aλ") x

def atomCharsReverse : SourceSignature.Goal :=
  atomChars x (SourceSignature.list [atom "a", atom "λ"])

def atomCharsReverseCodes : SourceSignature.Goal :=
  atomChars x (SourceSignature.list [integer 97, integer 955])

def atomCharsReverseString : SourceSignature.Goal := atomChars x (string "aλ")

def atomCharsBoundCodes : SourceSignature.Goal :=
  atomChars (atom "aλ") (SourceSignature.list [integer 97, integer 955])

def atomCharsBoundString : SourceSignature.Goal := atomChars (atom "aλ") (string "aλ")

def atomCharsBindsElement : SourceSignature.Goal :=
  atomChars (atom "a") (SourceSignature.list [x])

def atomCharsMismatch : SourceSignature.Goal :=
  atomChars (atom "a") (SourceSignature.list [atom "b"])

def atomCharsBothUnbound : SourceSignature.Goal := atomChars x y

def atomCharsImproper : SourceSignature.Goal :=
  atomChars (atom "a") (compound "[|]" [atom "a", atom "tail"])

def atomCharsInvalidElement : SourceSignature.Goal :=
  atomChars x (SourceSignature.list [atom "ab"])

def atomCharsRejectsStringElement : SourceSignature.Goal :=
  atomChars x (SourceSignature.list [string "x"])

def atomCharsCyclicList : SourceSignature.Goal :=
  .conj (.unify y (compound "[|]" [atom "a", y])) (atomChars x y)

def atomString (atomValue stringValue : SourceSignature.Term) :
    SourceSignature.Goal :=
  SourceSignature.call "atom_string" [atomValue, stringValue]

def atomStringForward : SourceSignature.Goal := atomString (atom "aλ") x

def atomStringReverseString : SourceSignature.Goal := atomString x (string "aλ")

def atomStringReverseAtom : SourceSignature.Goal := atomString x (atom "aλ")

def atomStringMismatch : SourceSignature.Goal := atomString (atom "a") (string "b")

def atomStringBothUnbound : SourceSignature.Goal := atomString x y

def atomStringInvalidValue : SourceSignature.Goal :=
  atomString x (compound "pair" [atom "a", atom "b"])

def metaAtomStringReverse : SourceSignature.Goal :=
  metaGoal (compound "atom_string" [x, string "a"])

def numberCodes (number codes : SourceSignature.Term) : SourceSignature.Goal :=
  SourceSignature.call "number_codes" [number, codes]

def numberCodesForwardInteger : SourceSignature.Goal :=
  numberCodes (integer (-42)) x

def numberCodesForwardIntegerExact : SourceSignature.Goal :=
  numberCodes (integer (-42))
    (SourceSignature.list [integer 45, integer 52, integer 50])

def numberCodesReverseInteger : SourceSignature.Goal :=
  numberCodes x (SourceSignature.list [integer 52, integer 50])

def numberCodesReverseNegative : SourceSignature.Goal :=
  numberCodes x (SourceSignature.list [integer 45, integer 49])

def numberCodesReverseFloat : SourceSignature.Goal :=
  numberCodes x
    (SourceSignature.list [integer 49, integer 46, integer 53])

def numberCodesReverseNegativeFloat : SourceSignature.Goal :=
  numberCodes x
    (SourceSignature.list [integer 45, integer 49, integer 46, integer 53])

def numberCodesReverseExponent : SourceSignature.Goal :=
  numberCodes x
    (SourceSignature.list [integer 49, integer 101, integer 50])

def numberCodesReverseFloatExact : SourceSignature.Goal :=
  .conj numberCodesReverseFloat
    (SourceSignature.call "=="
      [x, floatBits (Float.ofScientific 15 true 1).toBits])

def numberCodesReverseNegativeFloatExact : SourceSignature.Goal :=
  .conj numberCodesReverseNegativeFloat
    (SourceSignature.call "=="
      [x, floatBits ((Float.ofScientific 15 true 1).toBits ^^^
        0x8000000000000000)])

def numberCodesReverseExponentExact : SourceSignature.Goal :=
  .conj numberCodesReverseExponent
    (SourceSignature.call "=="
      [x, floatBits (Float.ofScientific 1 false 2).toBits])

def numberCodesMismatch : SourceSignature.Goal :=
  numberCodes (integer 12) (SourceSignature.list [integer 49, integer 51])

def metaNumberCodesReverse : SourceSignature.Goal :=
  metaGoal (compound "number_codes"
    [x, SourceSignature.list [integer 52, integer 50]])

def numberCodesBothUnbound : SourceSignature.Goal := numberCodes x y

def numberCodesInvalidSyntax : SourceSignature.Goal :=
  numberCodes x (SourceSignature.list [integer 97])

def numberCodesImproper : SourceSignature.Goal :=
  numberCodes (integer 1) (compound "[|]" [integer 49, atom "tail"])

def numberCodesInvalidValue : SourceSignature.Goal :=
  numberCodes (atom "one") x

def numberCodesFloatForwardUnsupported : SourceSignature.Goal :=
  numberCodes (floatBits (Float.ofScientific 15 true 1).toBits) x

def atomCodesBothUnbound : SourceSignature.Goal := atomCodes x y

def atomCodesImproper : SourceSignature.Goal :=
  atomCodes (atom "a") (compound "[|]" [integer 97, atom "tail"])

def atomCodesInvalidScalar : SourceSignature.Goal :=
  atomCodes x (SourceSignature.list [integer 1114112])

def atomCodesCyclicList : SourceSignature.Goal :=
  .conj (.unify y (compound "[|]" [integer 97, y])) (atomCodes x y)

/-- A heap-built meta-call returns to the same source service rather than
using a second dynamic classification path. -/
def metaAtomAcceptsAtom : SourceSignature.Goal :=
  metaGoal (compound "atom" [atom "a"])

/-- Stable clause references are atomic runtime values but not source atoms,
matching SWI's opaque reference classification without making them forgeable. -/
def referenceIsAtomicButNotAtom : SourceSignature.Goal :=
  .conj
    (SourceSignature.call "assertz"
      [compound "p" [atom "a"], referenceVar])
    (.conj
      (SourceSignature.call "atomic" [referenceVar])
      (.neg (SourceSignature.call "atom" [referenceVar])))

/-! ## Read-only strict graph identity -/

def strictIdentity (left right : SourceSignature.Term) :
    SourceSignature.Goal :=
  SourceSignature.call "==" [left, right]

def strictNonIdentity (left right : SourceSignature.Term) :
    SourceSignature.Goal :=
  SourceSignature.call "\\==" [left, right]

def identitySameVariable : SourceSignature.Goal := strictIdentity x x

def identityDistinctVariables : SourceSignature.Goal := strictIdentity x y

def nonIdentityDistinctVariables : SourceSignature.Goal :=
  strictNonIdentity x y

def identitySeparateCompounds : SourceSignature.Goal :=
  strictIdentity (pair (atom "a") (atom "b"))
    (pair (atom "a") (atom "b"))

def identityDifferentCompounds : SourceSignature.Goal :=
  strictIdentity (pair (atom "a") (atom "b"))
    (pair (atom "a") (atom "c"))

def identityDistinguishesVariableSharing : SourceSignature.Goal :=
  strictIdentity (pair x x) (pair y z)

def identityEqualRationalCycles : SourceSignature.Goal :=
  .conj (.unify x (compound "f" [x]))
    (.conj (.unify y (compound "f" [y])) (strictIdentity x y))

def identityDifferentRationalCycles : SourceSignature.Goal :=
  .conj (.unify x (compound "f" [x]))
    (.conj (.unify y (compound "g" [y])) (strictIdentity x y))

/-- A failed identity test performs no trial binding before the caller's right
alternative; the old variable remains visibly unbound. -/
def identityFailureDoesNotBind : SourceSignature.Goal :=
  .disj (strictIdentity x (atom "a"))
    (.conj (.isVar x) (.unify x (atom "b")))

def metaIdentitySameVariable : SourceSignature.Goal :=
  metaGoal (compound "==" [x, x])

def identityDistinguishesNumericTypes : SourceSignature.Goal :=
  strictIdentity (integer 1) (floatBits 0)

def identityEqualStrings : SourceSignature.Goal :=
  strictIdentity (string "a") (string "a")

def identityAtomNotZeroArityCompound : SourceSignature.Goal :=
  strictIdentity (atom "f") (compound "f" [])

/-! ## Read-only variance modulo a variable bijection -/

def variantEqual (left right : SourceSignature.Term) :
    SourceSignature.Goal :=
  SourceSignature.call "=@=" [left, right]

def notVariant (left right : SourceSignature.Term) :
    SourceSignature.Goal :=
  SourceSignature.call "\\=@=" [left, right]

def variantDistinctVariables : SourceSignature.Goal := variantEqual x y

def variantPreservesSharing : SourceSignature.Goal :=
  variantEqual (pair x x) (pair y y)

def variantRejectsSharingCollapse : SourceSignature.Goal :=
  variantEqual (pair x x) (pair y z)

/-- The inverse sharing mismatch is equally important: a variance check must
maintain a bijection, not merely a function from left variables to right. -/
def variantRejectsSharingExpansion : SourceSignature.Goal :=
  variantEqual (pair x y) (pair z z)

def notVariantAcceptsSharingMismatch : SourceSignature.Goal :=
  notVariant (pair x x) (pair y z)

def notVariantAcceptsSharingExpansion : SourceSignature.Goal :=
  notVariant (pair x y) (pair z z)

def variantPermutesVariableNames : SourceSignature.Goal :=
  variantEqual (pair x y) (pair y x)

def variantEqualRationalCycles : SourceSignature.Goal :=
  .conj (.unify x (compound "f" [x]))
    (.conj (.unify y (compound "f" [y])) (variantEqual x y))

/-- SWI regards one-node and two-node presentations of the same rational
unfolding as variants; compound allocation topology is not observable. -/
def variantEqualRationalUnfoldings : SourceSignature.Goal :=
  .conj (.unify x (compound "f" [x]))
    (.conj (.unify y (compound "f" [z]))
      (.conj (.unify z (compound "f" [y])) (variantEqual x y)))

def variantRejectsDifferentRationalFunctor : SourceSignature.Goal :=
  .conj (.unify x (compound "f" [x]))
    (.conj (.unify y (compound "g" [y])) (variantEqual x y))

/-- A failed variance test does not perform trial binding before DFS enters
the caller's right alternative. -/
def variantFailureDoesNotBind : SourceSignature.Goal :=
  .disj (variantEqual (pair x x) (pair y z))
    (.conj (.isVar x) (.unify x (atom "b")))

def metaVariantDistinctVariables : SourceSignature.Goal :=
  metaGoal (compound "=@=" [x, y])

def nonIdentityDifferentCompounds : SourceSignature.Goal :=
  strictNonIdentity (pair (atom "a") (atom "b"))
    (pair (atom "a") (atom "c"))

/-! ## `=../2` on the shared heap -/

def univ (term list : SourceSignature.Term) : SourceSignature.Goal :=
  SourceSignature.call "=.." [term, list]

def univDecomposesCompound : SourceSignature.Goal :=
  univ (pair (atom "a") (atom "b")) x

def univConstructsCompound : SourceSignature.Goal :=
  univ x (SourceSignature.list [atom "pair", atom "a", atom "b"])

def univDecomposesAtom : SourceSignature.Goal :=
  univ (atom "a") x

def univConstructsAtom : SourceSignature.Goal :=
  univ x (SourceSignature.list [atom "a"])

def univDecomposesInteger : SourceSignature.Goal :=
  univ (integer 1) x

/-- Construction reuses list-element roots: repeated variables remain the
same variable inside the newly allocated application. -/
def univConstructionPreservesSharing : SourceSignature.Goal :=
  .conj
    (univ x (SourceSignature.list [atom "pair", y, y]))
    (.conj (.unify x (pair leftVar rightVar))
      (strictIdentity leftVar rightVar))

/-- Decomposition reuses application-argument roots: one repeated argument
is not copied into two fresh variables in the result list. -/
def univDecompositionPreservesSharing : SourceSignature.Goal :=
  .conj
    (univ (pair y y)
      (SourceSignature.list [atom "pair", leftVar, rightVar]))
    (strictIdentity leftVar rightVar)

/-- A heap-built meta-call reaches the same source service and shared engine
operation as a statically present `=../2` call. -/
def metaUnivConstructsCompound : SourceSignature.Goal :=
  metaGoal (compound "=.."
    [x, SourceSignature.list [atom "pair", atom "a", atom "b"]])

def univUnboundList : SourceSignature.Goal := univ x y

def univEmptyList : SourceSignature.Goal :=
  univ x SourceSignature.nil

def univUnboundFunctor : SourceSignature.Goal :=
  univ x (SourceSignature.list [y, atom "a"])

def univNonAtomFunctor : SourceSignature.Goal :=
  univ x (SourceSignature.list [integer 1, atom "a"])

def univExplicitZeroArityCompound : SourceSignature.Goal :=
  univ (compound "f" []) x

/-! ## Finite `copy_term/2` through capture, freshening, and one unifier -/

def copyTerm (source target : SourceSignature.Term) : SourceSignature.Goal :=
  SourceSignature.call "copy_term" [source, target]

/-- Repeated occurrences of one source variable remain one variable in the
copy. -/
def copyTermPreservesSharing : SourceSignature.Goal :=
  .conj (copyTerm (pair x x) (pair y z)) (strictIdentity y z)

/-- A copied residual variable is fresh relative to its source variable. -/
def copyTermSeparatesSource : SourceSignature.Goal :=
  .conj (copyTerm x y) (strictNonIdentity x y)

/-- Two calls at the persistent scope high-water cannot reuse a copied
variable identity. -/
def successiveCopiesAreSeparate : SourceSignature.Goal :=
  .conj (copyTerm x y)
    (.conj (copyTerm x z) (strictNonIdentity y z))

/-- Copy observes the source's current instantiation, not its entry syntax. -/
def copyTermUsesCurrentInstantiation : SourceSignature.Goal :=
  .conj (.unify x (atom "a"))
    (copyTerm (pair x x) y)

/-- Heap-built `call(copy_term(...))` returns to the same service and shared
engine transition as a statically present call. -/
def metaCopyTerm : SourceSignature.Goal :=
  metaGoal (compound "copy_term" [pair x x, pair y z])

def copyTermRationalSource : SourceSignature.Goal :=
  .conj (.unify x (compound "f" [x])) (copyTerm x y)

/-! ## Ordered source-variable discovery -/

def termVariables (term output : SourceSignature.Term) : SourceSignature.Goal :=
  SourceSignature.call "term_variables" [term, output]

def termVariablesPreservesOrderAndIdentity : SourceSignature.Goal :=
  .conj (termVariables (pair y x) z)
    (.conj (.unify z (SourceSignature.list [leftVar, rightVar]))
      (.conj (strictIdentity leftVar y)
        (strictIdentity rightVar x)))

def termVariablesDeduplicatesSharing : SourceSignature.Goal :=
  .conj (termVariables (pair x x) z)
    (.conj (.unify z (SourceSignature.list [leftVar]))
      (strictIdentity leftVar x))

def termVariablesGroundIsEmpty : SourceSignature.Goal :=
  termVariables (pair (atom "a") (atom "b")) SourceSignature.nil

def termVariablesRationalFreeLeaf : SourceSignature.Goal :=
  .conj (.unify x (compound "f" [x, y]))
    (.conj (termVariables x z)
      (.conj (.unify z (SourceSignature.list [leftVar]))
        (strictIdentity leftVar y)))

def termVariablesOutputMismatch : SourceSignature.Goal :=
  termVariables (pair x y) (SourceSignature.list [x])

def metaTermVariables : SourceSignature.Goal :=
  .conj (metaGoal (compound "term_variables" [pair x y, z]))
    (.unify z (SourceSignature.list [leftVar, rightVar]))

/-! ## ISO `numbervars/3,4` on finite source-materialized heap graphs -/

def numberedVariable (index : Nat) : SourceSignature.Term :=
  compound "$VAR" [integer (Int.ofNat index)]

def singletonVariable : SourceSignature.Term :=
  compound "$VAR" [atom "_"]

def numberVariablesThree (term : SourceSignature.Term) (start : Int)
    (endIndex : SourceSignature.Term) : SourceSignature.Goal :=
  SourceSignature.call "numbervars" [term, integer start, endIndex]

def numberVariablesFour (term : SourceSignature.Term) (start : Int)
    (endIndex : SourceSignature.Term) (singletons : Bool) :
    SourceSignature.Goal :=
  SourceSignature.call "numbervars" [term, integer start, endIndex,
    SourceSignature.list [compound "singletons"
      [atom (if singletons then "true" else "false")]]]

/-- First occurrence assigns an index and repeated occurrences retain one
binding; the final index counts distinct numbered roots. -/
def numberVariablesPreservesSharingAndOrder : SourceSignature.Goal :=
  .conj (numberVariablesThree (pair x (pair x y)) 0 z)
    (.conj (.unify x (numberedVariable 0))
      (.conj (.unify y (numberedVariable 1)) (.unify z (integer 2))))

/-- PeTTa's singleton option labels a once-occurring variable with `_` and
does not consume an integer index for it. -/
def numberVariablesMarksSingletons : SourceSignature.Goal :=
  .conj (numberVariablesFour (pair x (pair x y)) 0 z true)
    (.conj (.unify x (numberedVariable 0))
      (.conj (.unify y singletonVariable) (.unify z (integer 1))))

def numberVariablesStartsAtFive : SourceSignature.Goal :=
  .conj (numberVariablesFour (pair x (pair x y)) 5 z true)
    (.conj (.unify x (numberedVariable 5))
      (.conj (.unify y singletonVariable) (.unify z (integer 6))))

def numberVariablesSingletonsFalse : SourceSignature.Goal :=
  .conj (numberVariablesFour (pair x y) 0 z false)
    (.conj (.unify x (numberedVariable 0))
      (.conj (.unify y (numberedVariable 1)) (.unify z (integer 2))))

/-- Sharing an acyclic application through a bound variable contributes its
free leaf once per logical occurrence, not once per physical heap root. -/
def numberVariablesCountsSharedApplications : SourceSignature.Goal :=
  .conj (.unify x (compound "box" [y]))
    (.conj (numberVariablesFour (pair x x) 0 z true)
      (.conj (.unify y (numberedVariable 0)) (.unify z (integer 1))))

/-- Pinned SWI disables singleton labeling for a rational term as a whole;
the finite free leaf is therefore numbered normally. -/
def numberVariablesCycleDisablesSingletons : SourceSignature.Goal :=
  .conj (.unify x (compound "f" [x, y]))
    (.conj (numberVariablesFour x 0 z true)
      (.conj (.unify y (numberedVariable 0)) (.unify z (integer 1))))

/-- All bindings introduced by numbering are ordinary trailed unifications;
backtracking over the left disjunct restores both source variables. -/
def numberVariablesBindingsBacktrack : SourceSignature.Goal :=
  .disj
    (.conj (numberVariablesThree (pair x y) 0 z) .fail)
    (.conj (.isVar x) (.isVar y))

/-- A prebound incompatible final index fails through the canonical unifier
and restores every allocation at query completion. -/
def numberVariablesEndMismatch : SourceSignature.Goal :=
  numberVariablesThree (pair x y) 0 (integer 3)

def metaNumberVariables : SourceSignature.Goal :=
  .conj (metaGoal (compound "numbervars" [pair x y, integer 0, z]))
    (.unify z (integer 2))

def numberVariablesStartUnbound : SourceSignature.Goal :=
  SourceSignature.call "numbervars" [pair x y, z, leftVar]

def numberVariablesNegativeStart : SourceSignature.Goal :=
  numberVariablesThree (pair x y) (-1) z

def numberVariablesUnsupportedOptions : SourceSignature.Goal :=
  SourceSignature.call "numbervars" [pair x y, integer 0, z,
    SourceSignature.list [atom "unsupported"]]

/-! ## Pinned SWI-compatible `term_hash/2` -/

def termHashGoal (term output : SourceSignature.Term) : SourceSignature.Goal :=
  SourceSignature.call "term_hash" [term, output]

def termHashAtom : SourceSignature.Goal := termHashGoal (atom "a") x

def termHashInteger : SourceSignature.Goal := termHashGoal (integer 1) x

def termHashNegativeInteger : SourceSignature.Goal :=
  termHashGoal (integer (-1)) x

def termHashString : SourceSignature.Goal := termHashGoal (string "x") x

def termHashCompound : SourceSignature.Goal :=
  termHashGoal (compound "f" [atom "a", integer 1]) x

def termHashList : SourceSignature.Goal :=
  termHashGoal (SourceSignature.list [atom "a", atom "b"]) x

def termHashFloat : SourceSignature.Goal :=
  termHashGoal (floatBits (1.0 : Float).toBits) x

def termHashNegativeZero : SourceSignature.Goal :=
  termHashGoal (floatBits (-0.0 : Float).toBits) x

def termHashUnicodeAtom : SourceSignature.Goal :=
  termHashGoal (atom "λ") x

def termHashLatinOneAtom : SourceSignature.Goal :=
  termHashGoal (atom "é") x

def termHashUnicodeString : SourceSignature.Goal :=
  termHashGoal (string "λ") x

def termHashLatinOneString : SourceSignature.Goal :=
  termHashGoal (string "é") x

def termHashMixedWideString : SourceSignature.Goal :=
  termHashGoal (string "éλ") x

/-- Permanent guards for SWI's exact Latin-1/wide storage cutoff. -/
def termHashLatinOneBoundaryAtom : SourceSignature.Goal :=
  termHashGoal (atom "ÿ") x

def termHashWideBoundaryAtom : SourceSignature.Goal :=
  termHashGoal (atom "Ā") x

def termHashLatinOneBoundaryString : SourceSignature.Goal :=
  termHashGoal (string "ÿ") x

def termHashWideBoundaryString : SourceSignature.Goal :=
  termHashGoal (string "Ā") x

def termHashMixedBoundaryAtom : SourceSignature.Goal :=
  termHashGoal (atom "ÿĀ") x

def termHashMixedBoundaryString : SourceSignature.Goal :=
  termHashGoal (string "ÿĀ") x

/-- Physical sharing and structural duplication have the same key. -/
def termHashShared : SourceSignature.Goal :=
  .conj (.unify x (compound "box" [atom "a"]))
    (termHashGoal (pair x x) y)

def termHashDuplicated : SourceSignature.Goal :=
  termHashGoal (pair (compound "box" [atom "a"])
    (compound "box" [atom "a"])) y

/-- The shared graph hash uses SWI's cycle marker rather than diverging. -/
def termHashCycle : SourceSignature.Goal :=
  .conj (.unify x (compound "f" [x])) (termHashGoal x y)

/-- A cyclic child contributes SWI's cycle marker to its outer parent. -/
def termHashOuterCycle : SourceSignature.Goal :=
  .conj (.unify x (compound "g" [x]))
    (termHashGoal (pair x (atom "a")) y)

/-- Reusing one completed cyclic subgraph contributes the same cycle marker
at each incoming edge. -/
def termHashSharedCycle : SourceSignature.Goal :=
  .conj (.unify x (compound "f" [x])) (termHashGoal (pair x x) y)

/-- A nonground term succeeds but leaves its hash output untouched. -/
def termHashNongroundLeavesOutput : SourceSignature.Goal :=
  .conj (termHashGoal (pair x (atom "a")) y) (.isVar y)

def termHashNongroundKeepsBoundOutput : SourceSignature.Goal :=
  termHashGoal (pair x (atom "a")) (integer 7)

def termHashMismatch : SourceSignature.Goal :=
  termHashGoal (atom "a") (integer 0)

def termHashBigIntegerUnsupported : SourceSignature.Goal :=
  termHashGoal (integer 72057594037927936) x

def metaTermHash : SourceSignature.Goal :=
  .conj (metaGoal (compound "term_hash" [atom "a", x]))
    (.unify x (integer 45085902))

/-- This is pinned PeTTa's real call shape: copy, variant-normalize, then hash
the resulting ground key. -/
def termHashNormalizedKey : SourceSignature.Goal :=
  .conj (SourceSignature.call "copy_term" [pair x (pair x y), z])
    (.conj (numberVariablesFour z 0 leftVar true)
      (termHashGoal z rightVar))

/-! ## ISO `functor/3` on the canonical graph -/

def functorGoal (term name arity : SourceSignature.Term) :
    SourceSignature.Goal :=
  SourceSignature.call "functor" [term, name, arity]

def functorDecomposesCompound : SourceSignature.Goal :=
  functorGoal (pair (atom "a") (atom "b")) x y

def functorDecomposesAtomic : SourceSignature.Goal :=
  functorGoal (integer 7) x y

def functorConstructsCompound : SourceSignature.Goal :=
  functorGoal x (atom "pair") (integer 2)

/-- Positive-arity construction creates two distinct unbound argument roots,
not one repeated placeholder. -/
def functorConstructsDistinctFreshArguments : SourceSignature.Goal :=
  .conj (functorGoal x (atom "pair") (integer 2))
    (.conj (.unify x (pair y z))
      (.conj (.isVar y) (.conj (.isVar z) (strictNonIdentity y z))))

def functorConstructsAtomicAtZero : SourceSignature.Goal :=
  functorGoal x (integer 7) (integer 0)

def functorDecomposesRationalRoot : SourceSignature.Goal :=
  .conj (.unify x (compound "f" [x]))
    (functorGoal x y z)

def functorOutputMismatch : SourceSignature.Goal :=
  functorGoal (pair (atom "a") (atom "b")) (atom "wrong") (integer 2)

def metaFunctorConstructsCompound : SourceSignature.Goal :=
  metaGoal (compound "functor" [x, atom "pair", integer 2])

def functorNameUnbound : SourceSignature.Goal :=
  functorGoal x y (integer 1)

def functorArityUnbound : SourceSignature.Goal :=
  functorGoal x (atom "pair") y

def functorNegativeArity : SourceSignature.Goal :=
  functorGoal x (atom "pair") (integer (-1))

def functorNonAtomPositiveName : SourceSignature.Goal :=
  functorGoal x (pair (atom "a") (atom "b")) (integer 1)

def functorExplicitZeroArityCompound : SourceSignature.Goal :=
  functorGoal (compound "f" []) x y

/-- Observe a typed runtime error without identifying ordinary Prolog
failure with an engine-side malformed-operation result. -/
def runQueryError? (program : SourceSignature.Program)
    (goal : SourceSignature.Goal) : Option LP.RuntimeQuery.QueryError :=
  match SourceRuntime.openEmpty program goal with
  | .error error => some error
  | .ok session =>
      match SourceRuntime.pullSession 512 session with
      | .terminal (.runtimeError error _) _ => some error
      | _ => none

/-! ## Ground ASCII character classification used by pinned `dcg/basics` -/

def codeType (code kind : SourceSignature.Term) : SourceSignature.Goal :=
  SourceSignature.call "code_type" [code, kind]

def codeTypeSpace : SourceSignature.Goal :=
  codeType (integer 32) (atom "space")

def codeTypeNewlineSpace : SourceSignature.Goal :=
  codeType (integer 10) (atom "space")

def codeTypeLetterNotSpace : SourceSignature.Goal :=
  codeType (integer 65) (atom "space")

def codeTypeDigit : SourceSignature.Goal :=
  codeType (integer 57) (atom "digit")

def codeTypeLetterNotDigit : SourceSignature.Goal :=
  codeType (integer 65) (atom "digit")

def metaCodeTypeSpace : SourceSignature.Goal :=
  metaGoal (compound "code_type" [integer 32, atom "space"])

def codeTypeUnbound : SourceSignature.Goal :=
  codeType x (atom "space")

def codeTypeUnicodeOutsideCurrentFragment : SourceSignature.Goal :=
  codeType (integer 955) (atom "space")

def codeTypeUnsupportedClass : SourceSignature.Goal :=
  codeType (integer 65) (atom "graph")

def codeTypeInvalidClass : SourceSignature.Goal :=
  codeType (integer 65) (integer 1)

def univRejectsUnboundList : Bool :=
  match runQueryError? [] univUnboundList with
  | some .univListUnbound => true
  | _ => false

def univRejectsEmptyList : Bool :=
  match runQueryError? [] univEmptyList with
  | some .invalidUnivList => true
  | _ => false

def univRejectsUnboundFunctor : Bool :=
  match runQueryError? [] univUnboundFunctor with
  | some .univFunctorUnbound => true
  | _ => false

def univRejectsNonAtomFunctor : Bool :=
  match runQueryError? [] univNonAtomFunctor with
  | some .invalidUnivFunctor => true
  | _ => false

def univRejectsExplicitZeroArityCompound : Bool :=
  match runQueryError? [] univExplicitZeroArityCompound with
  | some .invalidUnivFunctor => true
  | _ => false

/-! ## Unbounded integer arithmetic on the shared heap -/

def arithmetic (name : String) (arguments : List SourceSignature.Term) :
    SourceSignature.Term := compound name arguments

def integerIs (result expression : SourceSignature.Term) :
    SourceSignature.Goal := SourceSignature.call "is" [result, expression]

def integerComparison (name : String) (left right : SourceSignature.Term) :
    SourceSignature.Goal := SourceSignature.call name [left, right]

def integerAddition : SourceSignature.Goal :=
  integerIs x (arithmetic "+" [integer 2, integer 3])

def integerNestedArithmetic : SourceSignature.Goal :=
  integerIs x (arithmetic "*"
    [arithmetic "+" [integer 2, integer 3], integer 4])

def integerSubtraction : SourceSignature.Goal :=
  integerIs x (arithmetic "-" [integer 3, integer 5])

def integerModuloNegativeDividend : SourceSignature.Goal :=
  integerIs x (arithmetic "mod" [integer (-5), integer 3])

def integerModuloNegativeDivisor : SourceSignature.Goal :=
  integerIs x (arithmetic "mod" [integer 5, integer (-3)])

def integerIsMismatchFails : SourceSignature.Goal :=
  integerIs (integer 4) (arithmetic "+" [integer 2, integer 3])

def integerComparisonsSucceed : SourceSignature.Goal :=
  .conj (integerComparison "<" (integer 1) (integer 2))
    (.conj (integerComparison "=<" (integer 2) (integer 2))
      (.conj (integerComparison ">" (integer 3) (integer 2))
        (.conj (integerComparison ">=" (integer 3) (integer 3))
          (.conj (integerComparison "=:="
            (arithmetic "+" [integer 2, integer 3]) (integer 5))
            (integerComparison "=\\=" (integer 5) (integer 6))))))

def integerComparisonFailureRetainsCaller : SourceSignature.Goal :=
  .disj (integerComparison "<" (integer 2) (integer 1))
    (.unify x (atom "b"))

def metaIntegerAddition : SourceSignature.Goal :=
  metaGoal (compound "is"
    [x, arithmetic "+" [integer 2, integer 3]])

def integerArithmeticUnbound : SourceSignature.Goal := integerIs x y

def integerArithmeticFloatOperand : SourceSignature.Goal :=
  integerIs x (floatBits 0)

def integerArithmeticUnsupportedExpression : SourceSignature.Goal :=
  integerIs x (arithmetic "/" [integer 4, integer 2])

def integerArithmeticZeroDivisorExpression : SourceSignature.Goal :=
  integerIs x (arithmetic "mod" [integer 4, integer 0])

def integerArithmeticRejectsUnbound : Bool :=
  match runQueryError? [] integerArithmeticUnbound with
  | some .arithmeticOperandUnbound => true
  | _ => false

def integerArithmeticRejectsFloat : Bool :=
  match runQueryError? [] integerArithmeticFloatOperand with
  | some .invalidArithmeticOperand => true
  | _ => false

def integerArithmeticRejectsUnsupported : Bool :=
  match runQueryError? [] integerArithmeticUnsupportedExpression with
  | some .unsupportedArithmeticFunction => true
  | _ => false

def integerArithmeticRejectsZeroDivisor : Bool :=
  match runQueryError? [] integerArithmeticZeroDivisorExpression with
  | some .arithmeticZeroDivisor => true
  | _ => false

def binaryFactProgram : SourceSignature.Program :=
  [fact "p" [atom "a", atom "b"]]

/-! ## Private answer collection on the shared choice stack -/

def bagIdentity : SourceSignature.Variable := { spelling := "Bag", occurrence := 0 }
def outerIdentity : SourceSignature.Variable := { spelling := "Outer", occurrence := 0 }
def xIdentity : SourceSignature.Variable := { spelling := "X", occurrence := 0 }
def yIdentity : SourceSignature.Variable := { spelling := "Y", occurrence := 0 }
def zIdentity : SourceSignature.Variable := { spelling := "Z", occurrence := 0 }

def expectedScoped (term : SourceSignature.Term) : LP.Term Sigma.scoped :=
  LP.Term.atScope 0 term

/-- The collector reverses its private accumulator exactly once, preserving
DFS order and multiplicity. -/
def findallOrderMultiplicity : SourceSignature.Goal :=
  .findall x
    (.disj (.unify x (atom "a"))
      (.disj (.unify x (atom "b")) (.unify x (atom "a"))))
    bagVar

/-- Generator bindings are backtrack-local: only the copied bag crosses the
delimiter, while the original template variable remains unbound. -/
def findallIsolatesGeneratorBindings : SourceSignature.Goal :=
  .conj (.findall x (.unify x (atom "a")) bagVar) (.isVar x)

/-- Exhausting a failing generator succeeds once with the empty list. -/
def findallEmpty : SourceSignature.Goal :=
  .findall x .fail bagVar

/-- A generator cut prunes only generator-local alternatives.  It cannot
remove the caller's right disjunct. -/
def findallCutRetainsCaller : SourceSignature.Goal :=
  .disj
    (.findall x
      (.disj (.conj (.unify x (atom "a")) .cut)
        (.unify x (atom "b")))
      bagVar)
    (.unify bagVar (SourceSignature.list [atom "c"]))

/-- An exception escapes the collector and discards the partial bag; recovery
sees the caller's entry binding state. -/
def findallExceptionDiscardsPartialBag : SourceSignature.Goal :=
  .catch
    (.findall x
      (.disj (.unify x (atom "a")) (.throw (atom "ball")))
      bagVar)
    (atom "ball")
    (.unify bagVar (SourceSignature.list [atom "caught"]))

/-- Nested collectors use distinct sentinels and preserve the inner bag as one
ordinary outer solution. -/
def nestedFindall : SourceSignature.Goal :=
  .findall innerVar
    (.findall x
      (.disj (.unify x (atom "a")) (.unify x (atom "b")))
      innerVar)
    outerVar

private def repeatedPairVariables? (term : LP.Term Sigma.scoped) :
    Option (LP.ScopedVar SourceSignature.Variable ×
      LP.ScopedVar SourceSignature.Variable) :=
  match term with
  | .app symbol arguments =>
      match symbol.name, List.ofFn arguments with
      | "[|]", [first, tail] =>
          match first, tail with
          | .app firstSymbol firstArguments, .app consSymbol consArguments =>
              match firstSymbol.name, List.ofFn firstArguments,
                  consSymbol.name, List.ofFn consArguments with
              | "pair", [.var firstLeft, .var firstRight], "[|]", [second, nil] =>
                  match second, nil with
                  | .app secondSymbol secondArguments, .const .nil =>
                      match secondSymbol.name, List.ofFn secondArguments with
                      | "pair", [.var secondLeft, .var secondRight] =>
                          if firstLeft = firstRight && secondLeft = secondRight &&
                              firstLeft != secondLeft then
                            some (firstLeft, secondLeft)
                          else none
                      | _, _ => none
                  | _, _ => none
              | _, _, _, _ => none
          | _, _ => none
      | _, _ => none
  | _ => none

private def oneSeparatedPair? (term : LP.Term Sigma.scoped) : Bool :=
  match term with
  | .app consSymbol consArguments =>
      match consSymbol.name, List.ofFn consArguments with
      | "[|]", [pairTerm, .const .nil] =>
          match pairTerm with
          | .app pairSymbol pairArguments =>
              match pairSymbol.name, List.ofFn pairArguments with
              | "pair", [.var left, .var right] => left != right
              | _, _ => false
          | _ => false
      | _, _ => false
  | _ => false

/-- Every solution copies its template at the current persistent high-water:
sharing is preserved within a solution and separated between solutions. -/
def findallCopiesPerSolution : SourceSignature.Goal :=
  .findall (pair y y) (.disj .succeed .succeed) bagVar

def copiedSolutionsAreFreshAndShared : Bool :=
  match runTermsFor [] findallCopiesPerSolution bagIdentity with
  | some ([term], 0, 0) => (repeatedPairVariables? term).isSome
  | _ => false

/-- Distinct residual variables in one template remain distinct in its copy. -/
def findallCopyPreservesSeparation : SourceSignature.Goal :=
  .findall (pair y z) .succeed bagVar

def copiedSolutionPreservesSeparation : Bool :=
  match runTermsFor [] findallCopyPreservesSeparation bagIdentity with
  | some ([term], 0, 0) => oneSeparatedPair? term
  | _ => false

def answerThenLoopProgram : SourceSignature.Program := [
  fact "answer_then_loop" [atom "a"],
  {
    head := predicate "answer_then_loop" [x]
    body := SourceSignature.call "answer_then_loop" [x]
  }
]

def findallAnswerThenLoop : SourceSignature.Goal :=
  .findall x (SourceSignature.call "answer_then_loop" [x]) bagVar

private def collectionAnswerCount :
    List (LP.RuntimeQuery.ChoicePointCore Sigma
      (RuntimeControl.RuntimeGoal Sigma.scoped) SourceSignature.Clause) → Nat
  | [] => 0
  | .collection boundary :: _ => boundary.reversed.length
  | _ :: older => collectionAnswerCount older

/-- Suppressed generator answers remain real machine progress steps.  A
left-recursive generator therefore yields an open finite prefix with a growing
private bag, never a fabricated public answer or completion. -/
def findallAnswerThenLoopHasOpenPrivatePrefix : Bool :=
  match SourceRuntime.openEmpty answerThenLoopProgram findallAnswerThenLoop with
  | .error _ => false
  | .ok session =>
      match SourceRuntime.pullSession 512 session with
      | .open resumed => collectionAnswerCount resumed.state.choices > 0
      | _ => false

/-! ## Exception control through the shared frame stack -/

/-- A fresh catcher is selected at throw time and reconstructed after rollback
before recovery executes. -/
def caughtGround : SourceSignature.Goal :=
  .catch (.throw (atom "ball")) x (.unify x (atom "ball"))

/-- Catcher selection must observe bindings made by the protected goal.  The
entry-time `X` is free, but the throw-time `X = body` rejects `ball`. -/
def throwTimeBoundCatcherRejects : SourceSignature.Goal :=
  .catch
    (.conj (.unify x (atom "body")) (.throw (atom "ball")))
    x .succeed

/-- Recovery executes outside the consumed handler, so its exception cannot
be swallowed by the same `catch/3`. -/
def recoveryRethrowEscapes : SourceSignature.Goal :=
  .catch (.throw (atom "a")) x (.throw (atom "b"))

/-- The protected goal is cut-opaque: its cut cannot remove the caller's older
right disjunct. -/
def guardedCutRetainsCaller : SourceSignature.Goal :=
  .disj
    (.catch
      (.conj (.unify x (atom "a")) (.conj .cut .fail))
      (atom "never") .succeed)
    (.unify x (atom "c"))

/-- Recovery is also cut-opaque and returns to the caller's cut scope only
after its own frame completes. -/
def recoveryCutRetainsCaller : SourceSignature.Goal :=
  .disj
    (.catch (.throw (atom "a")) (atom "a") (.conj .cut .fail))
    (.unify x (atom "c"))

/-- Ordinary answers retain the catch frame on the saved right branch, so
backtracking re-enters the protected goal rather than skipping the delimiter. -/
def catchRetainsGuardedAnswers : SourceSignature.Goal :=
  .catch
    (.disj (.unify x (atom "a")) (.unify x (atom "b")))
    (atom "never") .fail

/-- An inner mismatch must not erase throw-time bindings before an outer
catcher is tested.  SWI tests every candidate against the original throw-time
state before performing the selected unwind. -/
def nestedMismatchRetainsThrowTimeBinding : SourceSignature.Goal :=
  .catch
    (.catch
      (.conj (.unify x (atom "body")) (.throw (atom "ball")))
      (atom "nope") .fail)
    x .succeed

/-- The copied packet variable is fresh relative to the caller's original
`Y`; binding the catcher in recovery cannot bind that original variable. -/
def packetCopySeparatesCaller : SourceSignature.Goal :=
  .catch (.throw (compound "box" [y])) (compound "box" [x])
    (.conj (.unify x (atom "a")) (.isVar y))

/-- A bare variable ball raises SWI's exact `throw/1` instantiation-error
shape.  Recovery also verifies that unwinding did not bind the caller's
original variable. -/
def throwVariableRaisesInstantiationError : SourceSignature.Goal :=
  let catcher := compound "error" [
    atom "instantiation_error",
    compound "context" [
      compound ":" [atom "system", compound "/" [atom "throw", integer 1]],
      z
    ]
  ]
  .catch (.throw y) catcher (.isVar y)

/-- One repeated packet variable remains shared after capture, freshening, and
reinstallation, so incompatible recovery bindings fail. -/
def packetCopyPreservesSharing : SourceSignature.Goal :=
  .catch (.throw (pair y y)) (pair leftVar rightVar)
    (.conj (.unify leftVar (atom "a"))
      (.unify rightVar (atom "b")))

/-- Distinct packet variables do not collapse during copying. -/
def packetCopyPreservesSeparation : SourceSignature.Goal :=
  .catch (.throw (pair y z)) (pair leftVar rightVar)
    (.conj (.unify leftVar (atom "a"))
      (.unify rightVar (atom "b")))

/-! ## Persistent dynamic database through the shared session handler -/

def assertedP (value : String) : SourceSignature.Term :=
  compound "p" [atom value]

def assertedRuleP (value : String) : SourceSignature.Term :=
  compound ":-" [assertedP value, compound "q" [atom value]]

def assertzGoal (clause : SourceSignature.Term) : SourceSignature.Goal :=
  SourceSignature.call "assertz" [clause]

def assertaGoal (clause : SourceSignature.Term) : SourceSignature.Goal :=
  SourceSignature.call "asserta" [clause]

def assertzWithReferenceGoal (clause reference : SourceSignature.Term) :
    SourceSignature.Goal :=
  SourceSignature.call "assertz" [clause, reference]

def assertaWithReferenceGoal (clause reference : SourceSignature.Term) :
    SourceSignature.Goal :=
  SourceSignature.call "asserta" [clause, reference]

def retractGoal (clause : SourceSignature.Term) : SourceSignature.Goal :=
  SourceSignature.call "retract" [clause]

def clauseGoal (head body reference : SourceSignature.Term) :
    SourceSignature.Goal :=
  SourceSignature.call "clause" [head, body, reference]

def assertzThenCall : SourceSignature.Goal :=
  .conj (assertzGoal (assertedP "a"))
    (SourceSignature.call "p" [x])

/-- The assertion occurs in a branch that fails and is backtracked over.  The
right branch and later call can observe it only if the database is persistent
rather than stored in a choice checkpoint. -/
def failedBranchAssertionPersists : SourceSignature.Goal :=
  .conj
    (.disj (.conj (assertzGoal (assertedP "a")) .fail) .succeed)
    (SourceSignature.call "p" [x])

/-! ## Database transactions on the same shared control stack -/

/-- Transaction success is once-like: only the first protected answer is
committed, while an older caller alternative remains available. -/
def transactionFirstSolutionRetainsCaller : SourceSignature.Goal :=
  .disj
    (.transaction (.disj (.unify x (atom "a")) (.unify x (atom "b"))))
    (.unify x (atom "c"))

/-- A transaction assembled on the heap and entered through `call/1` reaches
the same typed delimiter as source-written control. -/
def metaTransactionFirstSolution : SourceSignature.Goal :=
  metaGoal (compound "transaction" [
    disjunction (equality x (atom "a")) (equality x (atom "b"))
  ])

/-- Successful transaction updates persist into the caller continuation. -/
def successfulTransactionCommits : SourceSignature.Goal :=
  .conj (.transaction (assertzGoal (assertedP "a")))
    (SourceSignature.call "p" [x])

/-- Failure restores the transaction-entry database even though ordinary
assertions are persistent across ordinary Prolog backtracking. -/
def failedTransactionRollsBack : SourceSignature.Goal :=
  .conj
    (.disj
      (.transaction (.conj (assertzGoal (assertedP "a")) .fail))
      .succeed)
    (SourceSignature.call "p" [x])

/-- An exception that escapes the protected goal rolls the database back
before the outer catcher runs. -/
def raisedTransactionRollsBack : SourceSignature.Goal :=
  .conj
    (.catch
      (.transaction
        (.conj (assertzGoal (assertedP "a")) (.throw (atom "ball"))))
      (atom "ball") .succeed)
    (SourceSignature.call "p" [x])

/-- A packet handled inside the protected goal does not cross the transaction
delimiter; the recovered goal may therefore commit its database updates. -/
def caughtInsideTransactionCommits : SourceSignature.Goal :=
  .conj
    (.transaction
      (.conj (assertzGoal (assertedP "a"))
        (.catch (.throw (atom "ball")) (atom "ball") .succeed)))
    (SourceSignature.call "p" [x])

/-- Committing an inner transaction does not escape a later rollback of its
outer transaction. -/
def outerRollbackUndoesInnerCommit : SourceSignature.Goal :=
  .conj
    (.disj
      (.transaction
        (.conj (assertzGoal (assertedP "a"))
          (.conj (.transaction (assertzGoal (assertedP "b"))) .fail)))
      .succeed)
    (SourceSignature.call "p" [x])

/-- Rolling back an inner transaction restores the outer transaction's live
database, which can then commit normally. -/
def innerRollbackPreservesOuterUpdate : SourceSignature.Goal :=
  .conj
    (.transaction
      (.conj (assertzGoal (assertedP "a"))
        (.disj
          (.transaction
            (.conj (assertzGoal (assertedP "b")) .fail))
          .succeed)))
    (SourceSignature.call "p" [x])

def assertaAndAssertzOrder : SourceSignature.Goal :=
  .conj (assertzGoal (assertedP "b"))
    (.conj (assertaGoal (assertedP "a"))
      (SourceSignature.call "p" [x]))

/-- `assertz/2` binds its fresh output through the canonical graph unifier to
an opaque stable occurrence identity. -/
def assertzReferenceIsBound : SourceSignature.Goal :=
  .conj (assertzWithReferenceGoal (assertedP "a") referenceVar)
    (.ifThenElse (.isVar referenceVar) .fail .succeed)

/-- The front-insertion form exposes the same kind of opaque identity. -/
def assertaReferenceIsBound : SourceSignature.Goal :=
  .conj (assertaWithReferenceGoal (assertedP "a") referenceVar)
    (.ifThenElse (.isVar referenceVar) .fail .succeed)

/-- Stable occurrence identities are never reused for two insertions. -/
def assertedReferencesAreDistinct : SourceSignature.Goal :=
  .conj (assertzWithReferenceGoal (assertedP "a") referenceVar)
    (.conj
      (assertzWithReferenceGoal (assertedP "b") otherReferenceVar)
      (.ifThenElse (.unify referenceVar otherReferenceVar) .fail .succeed))

/-- The opaque identity remains ordinary Prolog data: a later asserted fact
can store it and canonical clause execution reads back the same value. -/
def assertedReferenceRoundTrip : SourceSignature.Goal :=
  .conj (assertzWithReferenceGoal (assertedP "a") referenceVar)
    (.conj (assertzGoal (compound "saved" [referenceVar]))
      (SourceSignature.call "saved" [otherReferenceVar]))

/-- The second argument is output-only.  A bound value is rejected by the
shared engine before the session can advance the persistent database. -/
def preboundAssertReferenceRejectedBeforeInsert : Bool :=
  match SourceRuntime.openEmpty []
      (assertzWithReferenceGoal (assertedP "a") (atom "forged")) with
  | .error _ => false
  | .ok session =>
      match SourceRuntime.pullSession 256 session with
      | .terminal
          (.runtimeError (.databaseReferenceOutputNotVariable) memory)
          world =>
          memory.heap.size == 0 && memory.trail.size == 0 &&
            world.database.generation == 0 &&
            world.database.visibleClauses.isEmpty
      | _ => false

/-- `retract/1` is nondeterministic over the call-time clause snapshot and
uses the shared leftmost choice stack, so matching occurrences are erased and
reported in source order. -/
def retractFactsInOrder : SourceSignature.Goal :=
  .conj (assertzGoal (assertedP "a"))
    (.conj (assertzGoal (assertedP "b"))
      (retractGoal (compound "p" [x])))

/-- The retained retract cursor is an ordinary shared-engine choice point.
A cut after the first match therefore prunes the second candidate. -/
def retractCutPrunesLater : SourceSignature.Goal :=
  .conj (assertzGoal (assertedP "a"))
    (.conj (assertzGoal (assertedP "b"))
      (.conj (retractGoal (compound "p" [x])) .cut))

/-- A head-only retract pattern denotes `Head :- true`: it skips a
same-headed non-fact rule and continues to the later matching fact. -/
def retractFactSkipsRule : SourceSignature.Goal :=
  .conj (assertzGoal (assertedRuleP "a"))
    (.conj (assertzGoal (assertedP "b"))
      (retractGoal (compound "p" [x])))

/-- Clause erasure is persistent session state rather than part of a
backtrackable checkpoint: failing after deletion cannot resurrect `p(a)`. -/
def failedBranchRetractionPersists : SourceSignature.Goal :=
  .conj (assertzGoal (assertedP "a"))
    (.conj
      (.disj
        (.conj (retractGoal (assertedP "a")) .fail)
        .succeed)
      (SourceSignature.call "p" [x]))

/-- The retract cursor is frozen before its first candidate is tried.  The
first candidate inserts `p(c)` and then fails; retry must advance to the
already-snapshotted `p(b)`, never drift onto the new occurrence. -/
def retractSnapshotGoal : SourceSignature.Goal :=
  .conj (assertzGoal (assertedP "a"))
    (.conj (assertzGoal (assertedP "b"))
      (.conj (retractGoal (compound "p" [x]))
        (.ifThenElse (.unify x (atom "a"))
          (.conj (assertzGoal (assertedP "c")) .fail)
          .succeed)))

/-- A later occurrence erased by a nested operation remains in the outer
call's frozen logical-update snapshot.  Its stable erase request becomes a
successful no-op, so the outer call still reports that one snapshotted match. -/
def retractSnapshotRetainsErasedCandidate : SourceSignature.Goal :=
  .conj (assertzGoal (assertedP "a"))
    (.conj (assertzGoal (assertedP "b"))
      (.conj (retractGoal (compound "p" [x]))
        (.ifThenElse (.unify x (atom "a"))
          (.conj (retractGoal (assertedP "b")) .fail)
          .succeed)))

/-- `clause/3` enumerates one immutable visible-clause snapshot in source
order. Facts expose `true` as their body and their opaque reference does not
alter the observed head binding. -/
def clauseFactsInOrder : SourceSignature.Goal :=
  .conj (assertzGoal (assertedP "a"))
    (.conj (assertzGoal (assertedP "b"))
      (clauseGoal (compound "p" [x]) (atom "true") referenceVar))

/-- A reference obtained from `assertz/2` can filter `clause/3`; source text
still has no constructor capable of forging that identity. -/
def clauseBoundReferenceSelectsOccurrence : SourceSignature.Goal :=
  .conj (assertzWithReferenceGoal (assertedP "a") referenceVar)
    (.conj (assertzWithReferenceGoal (assertedP "b") otherReferenceVar)
      (clauseGoal (compound "p" [x]) (atom "true") otherReferenceVar))

/-- Rule bodies are reflected separately from their heads, with the selected
clause standardized apart before the canonical graph unifier sees it. -/
def clauseRuleBody : SourceSignature.Goal :=
  .conj (assertzGoal (assertedRuleP "a"))
    (clauseGoal (assertedP "a") (compound "q" [y]) referenceVar)

/-- The retained read-only cursor is the same ordinary choice resource as a
retract cursor, so a following cut prunes later visible clauses. -/
def clauseCutPrunesLater : SourceSignature.Goal :=
  .conj (assertzGoal (assertedP "a"))
    (.conj (assertzGoal (assertedP "b"))
      (.conj
        (clauseGoal (compound "p" [x]) (atom "true") referenceVar)
        .cut))

/-- Clause inspection reports the exact stable identity allocated by
`assertz/2`, rather than an independently generated or position-derived one. -/
def clauseReferenceRoundTrip : SourceSignature.Goal :=
  .conj (assertzWithReferenceGoal (assertedP "a") referenceVar)
    (.conj
      (clauseGoal (assertedP "a") (atom "true") otherReferenceVar)
      (.unify referenceVar otherReferenceVar))

/-- A wholly variable head cannot be used as an unrestricted database
enumerator. It fails closed before a candidate cursor or binding is created. -/
def clauseVariableHeadRejected : Bool :=
  match SourceRuntime.openEmpty [] (clauseGoal x y referenceVar) with
  | .error _ => false
  | .ok session =>
      match SourceRuntime.pullSession 128 session with
      | .terminal (.runtimeError (.invalidDynamicClause) memory) world =>
          memory.heap.size == 0 && memory.trail.size == 0 &&
            world.database.generation == 0 &&
            world.database.visibleClauses.isEmpty
      | _ => false

/-- The visible-clause list is frozen when `clause/3` opens. A clause asserted
after its first solution persists in the database but is not appended to this
already-live cursor. -/
def clauseSnapshotDoesNotDrift : SourceSignature.Goal :=
  .conj (assertzGoal (assertedP "a"))
    (.conj (assertzGoal (assertedP "b"))
      (.conj
        (clauseGoal (compound "p" [x]) (atom "true") referenceVar)
        (.ifThenElse (.unify x (atom "a"))
          (.conj (assertzGoal (assertedP "c")) .fail)
          .succeed)))

/-- A snapshotted occurrence remains inspectable once even if a nested
operation erases it before the outer cursor reaches it. -/
def clauseSnapshotRetainsErasedCandidate : SourceSignature.Goal :=
  .conj (assertzGoal (assertedP "a"))
    (.conj (assertzGoal (assertedP "b"))
      (.conj
        (clauseGoal (compound "p" [x]) (atom "true") referenceVar)
        (.ifThenElse (.unify x (atom "a"))
          (.conj (retractGoal (assertedP "b")) .fail)
          .succeed)))

def snapshotProgram : SourceSignature.Program := [
  fact "p" [atom "old"],
  {
    head := predicate "driver" []
    body := .conj (SourceSignature.call "p" [x])
      (.conj (assertzGoal (assertedP "new")) .fail)
  }
]

def collectCountDatabase : Nat → Nat → Session →
    Option (Nat × LP.RuntimeDatabase.Database SourceSignature.Clause)
  | 0, _, _ => none
  | budget + 1, count, session =>
      match SourceRuntime.pullSession 256 session with
      | .open _ => none
      | .answer _ next => collectCountDatabase budget (count + 1) next
      | .terminal (.runtimeError _ _) _ => none
      | .terminal (.raised _ _) _ => none
      | .terminal (.completed _) world => some (count, world.database)

def collectAtomsDatabase : Nat → Session →
    Option (List String × Nat × Nat ×
      LP.RuntimeDatabase.Database SourceSignature.Clause)
  | 0, _ => none
  | budget + 1, session =>
      match SourceRuntime.pullSession 256 session with
      | .open _ => none
      | .terminal (.runtimeError _ _) _ => none
      | .terminal (.raised _ _) _ => none
      | .terminal (.completed memory) world =>
          some ([], memory.heap.size, memory.trail.size, world.database)
      | .answer answer resumed =>
          match answerAtom? answer, collectAtomsDatabase budget resumed with
          | some value, some (rest, heapSize, trailSize, database) =>
              some (value :: rest, heapSize, trailSize, database)
          | _, _ => none

def retractSnapshotRun :
    Option (List String × Nat × Nat ×
      LP.RuntimeDatabase.Database SourceSignature.Clause) :=
  match SourceRuntime.openEmpty [] retractSnapshotGoal with
  | .error _ => none
  | .ok session => collectAtomsDatabase 8 session

/-- Snapshot isolation is observed both in the answer stream (`c` was not a
candidate) and in the final persistent database (`a` and `b` were erased;
the later assertion remains visible). -/
def retractSnapshotDoesNotDrift : Bool :=
  match retractSnapshotRun with
  | some (["b"], 0, 0, database) =>
      database.generation == 5 &&
      database.visibleClauses.filterMap
        (fun entry => ClauseReflection.reflect? entry.2 |>.map
          ClauseReflection.termCode) ==
          [ClauseReflection.termCode
            (ReaderSource.normalizedClauseTerm (assertedP "c") (atom "true"))]
  | _ => false

/-- An open `p/1` cursor was frozen before `p(new)` was asserted.  It reaches
no new answer, but the completed session still carries the advanced database.
-/
def snapshotRun :
    Option (Nat × LP.RuntimeDatabase.Database SourceSignature.Clause) :=
  match SourceRuntime.openEmpty snapshotProgram
      (SourceSignature.call "driver" []) with
  | .error _ => none
  | .ok session => collectCountDatabase 8 0 session

def snapshotDoesNotDrift : Bool :=
  match snapshotRun with
  | some (0, database) =>
      database.generation == 1 &&
      database.visibleClauses.map (fun entry => entry.2.head.symbol.name) ==
        ["p", "driver", "p"]
  | _ => false

def laterCallSeesAssertion :
    Option (List String × Nat × Nat) := do
  let (_, database) ← snapshotRun
  let session ← (SourceRuntime.openDatabase database
    (SourceSignature.call "p" [x])).toOption
  collectAtoms 8 session

/-! ## Finite list length and call-time predicate reflection -/

def finiteListLength : SourceSignature.Goal :=
  SourceSignature.call "length"
    [SourceSignature.list [atom "a", atom "b", atom "c"], x]

def matchingListLength : SourceSignature.Goal :=
  SourceSignature.call "length"
    [SourceSignature.list [atom "a", atom "b"], integer 2]

def mismatchingListLength : SourceSignature.Goal :=
  SourceSignature.call "length"
    [SourceSignature.list [atom "a", atom "b"], integer 1]

def generativeListLength : SourceSignature.Goal :=
  SourceSignature.call "length" [x, integer 2]

def currentPredicate (name : String) (arity : Int) : SourceSignature.Goal :=
  SourceSignature.call "current_predicate"
    [compound "/" [atom name, integer arity]]

def currentPredicateUnbound : SourceSignature.Goal :=
  SourceSignature.call "current_predicate" [x]

def assertedPredicateBecomesCurrent : SourceSignature.Goal :=
  .conj (assertzGoal (assertedP "a")) (currentPredicate "p" 1)

/-! ## ISO `compare/3` through the canonical standard-term order -/

def termCompare (result left right : SourceSignature.Term) :
    SourceSignature.Goal :=
  SourceSignature.call "compare" [result, left, right]

def compareAtoms : SourceSignature.Goal :=
  termCompare x (atom "a") (atom "b")

def compareEqualCompounds : SourceSignature.Goal :=
  termCompare x (compound "f" [atom "a"]) (compound "f" [atom "a"])

def compareCompoundArity : SourceSignature.Goal :=
  termCompare x (compound "f" [atom "a"])
    (compound "f" [atom "a", atom "b"])

def comparePreboundMismatch : SourceSignature.Goal :=
  termCompare (atom ">") (atom "a") (atom "b")

def compareInvalidOrderAtom : SourceSignature.Goal :=
  termCompare (atom "foo") (atom "a") (atom "b")

def compareInvalidOrderInteger : SourceSignature.Goal :=
  termCompare (integer 1) (atom "a") (atom "b")

def compareInvalidOrderCompound : SourceSignature.Goal :=
  termCompare (compound "f" [atom "x"]) (atom "a") (atom "b")

/-! ## Explicit read-only host text capability -/

def textFileRead : SourceSignature.Goal :=
  .conj
    (SourceSignature.call "read_file_to_string"
      [SourceSignature.string "/fixture.metta", x, SourceSignature.list []])
    (.unify x (SourceSignature.string "!(file-id a)\n"))

def textFileReadWithOptions : SourceSignature.Goal :=
  SourceSignature.call "read_file_to_string" [
    SourceSignature.string "/fixture.metta", x,
    SourceSignature.list [SourceSignature.atom "encoding(utf8)"]]

def fixtureTextResources : TextFileResources := fun path =>
  if path == "/fixture.metta" then some "!(file-id a)\n" else none

def runCountWithServices (services : RuntimeControl.Services Sigma)
    (program : SourceSignature.Program) (goal : SourceSignature.Goal) :
    Option (Nat × Nat × Nat) :=
  match RuntimeControl.openSessionWith services
      (LP.RuntimeTerm.Memory.empty Sigma.scoped) 0 1 program goal with
  | .error _ => none
  | .ok session => collectCount 8 0 session

def runQueryErrorWithServices? (services : RuntimeControl.Services Sigma)
    (goal : SourceSignature.Goal) : Option LP.RuntimeQuery.QueryError :=
  match RuntimeControl.openSessionWith services
      (LP.RuntimeTerm.Memory.empty Sigma.scoped) 0 1 [] goal with
  | .error error => some error
  | .ok session =>
      match SourceRuntime.pullSession 512 session with
      | .terminal (.runtimeError error _) _ => some error
      | _ => none

#guard runAtoms [] dynamicDisjunction == some (["a", "b"], 0, 0)
#guard runAtoms [] nestedFailedLeftRetainsOuter == some (["c"], 0, 0)
#guard runAtoms [] hardConditionalCommitsElseRetainsCaller == some (["a", "c"], 0, 0)
#guard runAtoms [] softConditionalKeepsConditionAnswers == some (["a", "b"], 0, 0)
#guard runAtoms [] onceCommitsInnerBranch == some (["a"], 0, 0)
#guard runCount maplistProgram maplistSucceeds == some (1, 0, 0)
#guard runCount maplistProgram qualifiedMaplistSucceeds == some (1, 0, 0)
#guard runCount maplistProgram maplistFailsAfterPrefix == some (0, 0, 0)
#guard runAtoms maplistCutClosureProgram maplistClosureCutRetainsCaller ==
  some (["a", "b", "c"], 0, 0)
#guard runCount maplist3Program maplist3BuildsOutput == some (1, 0, 0)
#guard runCount maplist3Program maplist3UsesKnownOutput == some (1, 0, 0)
#guard runCount maplist3Program maplist3RejectsWrongLength == some (0, 0, 0)
#guard match runQueryError? maplist3Program maplist3PartialOutput with
  | some .univListUnbound => true
  | _ => false
#guard runAtomsFor maplist3CutClosureProgram maplist3ClosureCutRetainsCaller
  { spelling := "X", occurrence := 0 } == some (["a", "b", "c"], 0, 0)
#guard runCountWithServices (servicesWithTextFiles fixtureTextResources) []
  textFileRead == some (1, 0, 0)
#guard runCount [] textFileRead == some (0, 0, 0)
#guard match runQueryErrorWithServices?
    (servicesWithTextFiles fun _ => none) textFileRead with
  | some .textFileUnavailable => true
  | _ => false
#guard match runQueryErrorWithServices?
    (servicesWithTextFiles fixtureTextResources) textFileReadWithOptions with
  | some .invalidTextFileOptions => true
  | _ => false
#guard runAtomsFor [] compareAtoms xIdentity == some (["<"], 0, 0)
#guard runAtomsFor [] compareEqualCompounds xIdentity == some (["="], 0, 0)
#guard runAtomsFor [] compareCompoundArity xIdentity == some (["<"], 0, 0)
#guard runCount [] comparePreboundMismatch == some (0, 0, 0)
#guard match runQueryError? [] compareInvalidOrderAtom with
  | some .invalidTermCompareOrder => true
  | _ => false
#guard match runQueryError? [] compareInvalidOrderInteger with
  | some .invalidTermCompareOrderType => true
  | _ => false
#guard match runQueryError? [] compareInvalidOrderCompound with
  | some .invalidTermCompareOrderType => true
  | _ => false
#guard runAtoms [] metaCutRetainsCaller == some (["c"], 0, 0)
#guard runCount binaryFactProgram callThree == some (1, 0, 0)
#guard runCount binaryFactProgram heapBuiltCallable == some (1, 0, 0)
#guard runCount [] negationRejectsSuccess == some (0, 0, 0)
#guard runCount [] negationAcceptsFailure == some (1, 0, 0)
#guard runAtoms [] negationRestoresTrialBindings == some (["b"], 0, 0)
#guard runAtoms [] negationCutRetainsCaller == some (["c"], 0, 0)
#guard runCount [] distinctAtomsAreNotUnifiable == some (1, 0, 0)
#guard runCount [] variableAndAtomAreUnifiable == some (0, 0, 0)
#guard runAtoms [] notUnifyRestoresTrialBindings == some (["b"], 0, 0)
#guard runCount [] metaNonvarBound == some (1, 0, 0)
#guard runCount [] metaNonvarVariable == some (0, 0, 0)
#guard runCount [] metaForallSucceeds == some (1, 0, 0)
#guard runCount [] metaForallFails == some (0, 0, 0)
#guard runAtoms [] metaForallRestoresBindings == some (["c"], 0, 0)
#guard runCount [] atomAcceptsAtom == some (1, 0, 0)
#guard runCount [] (SourceSignature.call "atom" [atom "[]"]) == some (1, 0, 0)
#guard runCount [] (SourceSignature.call "is_list" [atom "[]"]) == some (0, 0, 0)
#guard runCount [] (.unify SourceSignature.nil (atom "[]")) == some (0, 0, 0)
#guard runCount [] (termCompare (atom "<") SourceSignature.nil (atom "[]")) == some (1, 0, 0)
#guard runCount [] (termCompare (atom ">") SourceSignature.nil (atom "[]")) == some (0, 0, 0)
#guard runCount [] (.conj
  (SourceSignature.call "term_hash" [SourceSignature.nil,SourceSignature.var "H" 0])
  (SourceSignature.call "term_hash" [atom "[]",SourceSignature.var "H" 0])) == some (1, 0, 0)
#guard runCount [] atomRejectsInteger == some (0, 0, 0)
#guard runCount [] atomRejectsListNil == some (0, 0, 0)
#guard runCount [] atomicAcceptsString == some (1, 0, 0)
#guard runCount [] atomicRejectsCompound == some (0, 0, 0)
#guard runCount [] compoundAcceptsPair == some (1, 0, 0)
#guard runCount [] compoundRejectsAtom == some (0, 0, 0)
#guard runCount [] numberAcceptsInteger == some (1, 0, 0)
#guard runCount [] numberAcceptsFloat == some (1, 0, 0)
#guard runCount [] numberRejectsAtom == some (0, 0, 0)
#guard runCount [] stringAcceptsString == some (1, 0, 0)
#guard runCount [] stringRejectsAtom == some (0, 0, 0)
#guard runCount [] groundAcceptsCompound == some (1, 0, 0)
#guard runCount [] groundRejectsVariable == some (0, 0, 0)
#guard runCount [] groundRejectsNestedVariable == some (0, 0, 0)
#guard runCount [] groundAcceptsRationalCompound == some (1, 0, 0)
#guard runCount [] groundRejectsRationalCompoundWithFreeLeaf == some (0, 0, 0)
#guard runCount [] isListAcceptsFinite == some (1, 0, 0)
#guard runCount [] isListRejectsImproper == some (0, 0, 0)
#guard runCount [] isListRejectsVariable == some (0, 0, 0)
#guard runCount [] isListRejectsRationalSpine == some (0, 0, 0)
#guard runCount [] isListAcceptsCyclicHead == some (1, 0, 0)
#guard runShapesFor [] formatAtomicCodes xIdentity ==
  some ([.compound "[|]" [.integer 97, .nil]], 0, 0)
#guard runShapesFor [] (formatAtomicCodes (SourceSignature.list [integer 33]))
    xIdentity ==
  some ([.compound "[|]" [.integer 97,
    .compound "[|]" [.integer 33, .nil]]], 0, 0)
#guard runShapesFor [] atomCodesForward xIdentity ==
  some ([runtimeTermShape (expectedScoped
    (SourceSignature.list [integer 97, integer 955]))], 0, 0)
#guard runAtomsFor [] atomCodesReverse xIdentity == some (["aλ"], 0, 0)
#guard runIntegersFor [] atomCodesBindsElement xIdentity == some ([97], 0, 0)
#guard runCount [] atomCodesMismatch == some (0, 0, 0)
#guard runShapesFor [] stringCodesForward xIdentity ==
  some ([runtimeTermShape (expectedScoped
    (SourceSignature.list [integer 97, integer 955]))], 0, 0)
#guard runStringsFor [] stringCodesReverse xIdentity == some (["aλ"], 0, 0)
#guard runShapesFor [] atomCharsForward xIdentity ==
  some ([runtimeTermShape (expectedScoped
    (SourceSignature.list [atom "a", atom "λ"]))], 0, 0)
#guard runAtomsFor [] atomCharsReverse xIdentity == some (["aλ"], 0, 0)
#guard runAtomsFor [] atomCharsReverseCodes xIdentity == some (["aλ"], 0, 0)
#guard runAtomsFor [] atomCharsReverseString xIdentity == some (["aλ"], 0, 0)
#guard runCount [] atomCharsBoundCodes == some (1, 0, 0)
#guard runCount [] atomCharsBoundString == some (1, 0, 0)
#guard runAtomsFor [] atomCharsBindsElement xIdentity == some (["a"], 0, 0)
#guard runCount [] atomCharsMismatch == some (0, 0, 0)
#guard runStringsFor [] atomStringForward xIdentity == some (["aλ"], 0, 0)
#guard runAtomsFor [] atomStringReverseString xIdentity == some (["aλ"], 0, 0)
#guard runAtomsFor [] atomStringReverseAtom xIdentity == some (["aλ"], 0, 0)
#guard runCount [] atomStringMismatch == some (0, 0, 0)
#guard runAtomsFor [] metaAtomStringReverse xIdentity == some (["a"], 0, 0)
#guard runShapesFor [] numberCodesForwardInteger xIdentity ==
  some ([runtimeTermShape (expectedScoped
    (SourceSignature.list [integer 45, integer 52, integer 50]))], 0, 0)
#guard runShapesFor [] numberCodesReverseInteger xIdentity ==
  some ([.integer 42], 0, 0)
#guard runShapesFor [] numberCodesReverseNegative xIdentity ==
  some ([.integer (-1)], 0, 0)
#guard runShapesFor [] numberCodesReverseFloat xIdentity ==
  some ([.floatBits (Float.ofScientific 15 true 1).toBits], 0, 0)
#guard runShapesFor [] numberCodesReverseNegativeFloat xIdentity ==
  some ([.floatBits ((Float.ofScientific 15 true 1).toBits ^^^
    0x8000000000000000)], 0, 0)
#guard runShapesFor [] numberCodesReverseExponent xIdentity ==
  some ([.floatBits (Float.ofScientific 1 false 2).toBits], 0, 0)
#guard runCount [] numberCodesMismatch == some (0, 0, 0)
#guard runShapesFor [] metaNumberCodesReverse xIdentity ==
  some ([.integer 42], 0, 0)
#guard match runQueryError? [] numberCodesBothUnbound with
  | some .numberConversionUnbound => true
  | _ => false
#guard match runQueryError? [] numberCodesInvalidSyntax with
  | some .invalidNumberCodes => true
  | _ => false
#guard match runQueryError? [] numberCodesImproper with
  | some .invalidNumberCodes => true
  | _ => false
#guard match runQueryError? [] numberCodesInvalidValue with
  | some .invalidNumberValue => true
  | _ => false
#guard match runQueryError? [] numberCodesFloatForwardUnsupported with
  | some .unsupportedInstruction => true
  | _ => false
#guard match runQueryError? [] atomCodesBothUnbound with
  | some .textConversionUnbound => true
  | _ => false
#guard match runQueryError? [] atomCodesImproper with
  | some .invalidTextCodes => true
  | _ => false
#guard match runQueryError? [] atomCodesInvalidScalar with
  | some .invalidCharacterCode => true
  | _ => false
#guard match runQueryError? [] atomCodesCyclicList with
  | some .invalidTextCodes => true
  | _ => false
#guard match runQueryError? [] atomCharsBothUnbound with
  | some .textConversionUnbound => true
  | _ => false
#guard match runQueryError? [] atomCharsImproper with
  | some .invalidTextCodes => true
  | _ => false
#guard match runQueryError? [] atomCharsInvalidElement with
  | some .invalidTextCodes => true
  | _ => false
#guard match runQueryError? [] atomCharsRejectsStringElement with
  | some .invalidTextCodes => true
  | _ => false
#guard match runQueryError? [] atomCharsCyclicList with
  | some .invalidTextCodes => true
  | _ => false
#guard match runQueryError? [] atomStringBothUnbound with
  | some .textConversionUnbound => true
  | _ => false
#guard match runQueryError? [] atomStringInvalidValue with
  | some .invalidTextValue => true
  | _ => false
#guard runCount [] codeTypeSpace == some (1, 0, 0)
#guard runCount [] codeTypeNewlineSpace == some (1, 0, 0)
#guard runCount [] codeTypeLetterNotSpace == some (0, 0, 0)
#guard runCount [] codeTypeDigit == some (1, 0, 0)
#guard runCount [] codeTypeLetterNotDigit == some (0, 0, 0)
#guard runCount [] metaCodeTypeSpace == some (1, 0, 0)
#guard match runQueryError? [] codeTypeUnbound with
  | some .characterTypeUnbound => true
  | _ => false
#guard match runQueryError? [] codeTypeUnicodeOutsideCurrentFragment with
  | some .unsupportedInstruction => true
  | _ => false
#guard match runQueryError? [] codeTypeUnsupportedClass with
  | some .unsupportedInstruction => true
  | _ => false
#guard match runQueryError? [] codeTypeInvalidClass with
  | some .invalidCharacterType => true
  | _ => false
#guard runCount [] metaAtomAcceptsAtom == some (1, 0, 0)
#guard runCount [] referenceIsAtomicButNotAtom == some (1, 0, 0)
#guard runCount [] identitySameVariable == some (1, 0, 0)
#guard runCount [] identityDistinctVariables == some (0, 0, 0)
#guard runCount [] nonIdentityDistinctVariables == some (1, 0, 0)
#guard runCount [] identitySeparateCompounds == some (1, 0, 0)
#guard runCount [] identityDifferentCompounds == some (0, 0, 0)
#guard runCount [] identityDistinguishesVariableSharing == some (0, 0, 0)
#guard runCount [] identityEqualRationalCycles == some (1, 0, 0)
#guard runCount [] identityDifferentRationalCycles == some (0, 0, 0)
#guard runAtoms [] identityFailureDoesNotBind == some (["b"], 0, 0)
#guard runCount [] metaIdentitySameVariable == some (1, 0, 0)
#guard runCount [] identityDistinguishesNumericTypes == some (0, 0, 0)
#guard runCount [] identityEqualStrings == some (1, 0, 0)
#guard runCount [] identityAtomNotZeroArityCompound == some (0, 0, 0)
#guard runCount [] nonIdentityDifferentCompounds == some (1, 0, 0)
#guard runCount [] variantDistinctVariables == some (1, 0, 0)
#guard runCount [] variantPreservesSharing == some (1, 0, 0)
#guard runCount [] variantRejectsSharingCollapse == some (0, 0, 0)
#guard runCount [] variantRejectsSharingExpansion == some (0, 0, 0)
#guard runCount [] notVariantAcceptsSharingMismatch == some (1, 0, 0)
#guard runCount [] notVariantAcceptsSharingExpansion == some (1, 0, 0)
#guard runCount [] variantPermutesVariableNames == some (1, 0, 0)
#guard runCount [] variantEqualRationalCycles == some (1, 0, 0)
#guard runCount [] variantEqualRationalUnfoldings == some (1, 0, 0)
#guard runCount [] variantRejectsDifferentRationalFunctor == some (0, 0, 0)
#guard runAtomsFor [] variantFailureDoesNotBind xIdentity ==
  some (["b"], 0, 0)
#guard runCount [] metaVariantDistinctVariables == some (1, 0, 0)
#guard runShapesFor [] univDecomposesCompound xIdentity ==
  some ([runtimeTermShape (expectedScoped
    (SourceSignature.list [atom "pair", atom "a", atom "b"]))], 0, 0)
#guard runShapesFor [] univConstructsCompound xIdentity ==
  some ([runtimeTermShape (expectedScoped
    (pair (atom "a") (atom "b")))], 0, 0)
#guard runShapesFor [] univDecomposesAtom xIdentity ==
  some ([runtimeTermShape (expectedScoped
    (SourceSignature.list [atom "a"]))], 0, 0)
#guard runShapesFor [] univConstructsAtom xIdentity ==
  some ([runtimeTermShape (expectedScoped (atom "a"))], 0, 0)
#guard runShapesFor [] univDecomposesInteger xIdentity ==
  some ([runtimeTermShape (expectedScoped
    (SourceSignature.list [integer 1]))], 0, 0)
#guard runCount [] univConstructionPreservesSharing == some (1, 0, 0)
#guard runCount [] univDecompositionPreservesSharing == some (1, 0, 0)
#guard runShapesFor [] metaUnivConstructsCompound xIdentity ==
  some ([runtimeTermShape (expectedScoped
    (pair (atom "a") (atom "b")))], 0, 0)
#guard univRejectsUnboundList
#guard univRejectsEmptyList
#guard univRejectsUnboundFunctor
#guard univRejectsNonAtomFunctor
#guard univRejectsExplicitZeroArityCompound
#guard runCount [] copyTermPreservesSharing == some (1, 0, 0)
#guard runCount [] copyTermSeparatesSource == some (1, 0, 0)
#guard runCount [] successiveCopiesAreSeparate == some (1, 0, 0)
#guard runShapesFor [] copyTermUsesCurrentInstantiation yIdentity ==
  some ([runtimeTermShape (expectedScoped (pair (atom "a") (atom "a")))],
    0, 0)
#guard runCount [] metaCopyTerm == some (1, 0, 0)
#guard match runQueryError? [] copyTermRationalSource with
  | some (.copyTermReadback _) => true
  | _ => false
#guard runCount [] termVariablesPreservesOrderAndIdentity == some (1, 0, 0)
#guard runCount [] termVariablesDeduplicatesSharing == some (1, 0, 0)
#guard runCount [] termVariablesGroundIsEmpty == some (1, 0, 0)
#guard runCount [] termVariablesRationalFreeLeaf == some (1, 0, 0)
#guard runCount [] termVariablesOutputMismatch == some (0, 0, 0)
#guard runCount [] metaTermVariables == some (1, 0, 0)
#guard runCount [] numberVariablesPreservesSharingAndOrder == some (1, 0, 0)
#guard runCount [] numberVariablesMarksSingletons == some (1, 0, 0)
#guard runCount [] numberVariablesStartsAtFive == some (1, 0, 0)
#guard runCount [] numberVariablesSingletonsFalse == some (1, 0, 0)
#guard runCount [] numberVariablesCountsSharedApplications == some (1, 0, 0)
#guard runCount [] numberVariablesCycleDisablesSingletons == some (1, 0, 0)
#guard runCount [] numberVariablesBindingsBacktrack == some (1, 0, 0)
#guard runCount [] numberVariablesEndMismatch == some (0, 0, 0)
#guard runCount [] metaNumberVariables == some (1, 0, 0)
#guard match runQueryError? [] numberVariablesStartUnbound with
  | some .numberVariablesStartUnbound => true
  | _ => false
#guard match runQueryError? [] numberVariablesNegativeStart with
  | some .invalidNumberVariablesStart => true
  | _ => false
#guard match runQueryError? [] numberVariablesUnsupportedOptions with
  | some .invalidNumberVariablesOptions => true
  | _ => false
#guard runIntegersFor [] termHashAtom xIdentity ==
  some ([45085902], 0, 0)
#guard runIntegersFor [] termHashInteger xIdentity ==
  some ([3261798158], 0, 0)
#guard runIntegersFor [] termHashNegativeInteger xIdentity ==
  some ([2513478484], 0, 0)
#guard runIntegersFor [] termHashString xIdentity ==
  some ([2879703217], 0, 0)
#guard runIntegersFor [] termHashCompound xIdentity ==
  some ([3911831286], 0, 0)
#guard runIntegersFor [] termHashList xIdentity ==
  some ([3640712072], 0, 0)
#guard runIntegersFor [] termHashFloat xIdentity ==
  some ([2548459879], 0, 0)
#guard runIntegersFor [] termHashNegativeZero xIdentity ==
  some ([3913372751], 0, 0)
#guard runIntegersFor [] termHashUnicodeAtom xIdentity ==
  some ([3442556481], 0, 0)
#guard runIntegersFor [] termHashLatinOneAtom xIdentity ==
  some ([1745793758], 0, 0)
#guard runIntegersFor [] termHashUnicodeString xIdentity ==
  some ([2700480543], 0, 0)
#guard runIntegersFor [] termHashLatinOneString xIdentity ==
  some ([1955271470], 0, 0)
#guard runIntegersFor [] termHashMixedWideString xIdentity ==
  some ([3039697503], 0, 0)
#guard runIntegersFor [] termHashLatinOneBoundaryAtom xIdentity ==
  some ([1600750448], 0, 0)
#guard runIntegersFor [] termHashWideBoundaryAtom xIdentity ==
  some ([76569204], 0, 0)
#guard runIntegersFor [] termHashLatinOneBoundaryString xIdentity ==
  some ([1106877724], 0, 0)
#guard runIntegersFor [] termHashWideBoundaryString xIdentity ==
  some ([1856102780], 0, 0)
#guard runIntegersFor [] termHashMixedBoundaryAtom xIdentity ==
  some ([3590090015], 0, 0)
#guard runIntegersFor [] termHashMixedBoundaryString xIdentity ==
  some ([4162070450], 0, 0)
#guard runIntegersFor [] termHashShared yIdentity ==
  some ([2364898277], 0, 0)
#guard runIntegersFor [] termHashDuplicated yIdentity ==
  some ([2364898277], 0, 0)
#guard runIntegersFor [] termHashCycle yIdentity ==
  some ([570532129], 0, 0)
#guard runIntegersFor [] termHashOuterCycle yIdentity ==
  some ([998265445], 0, 0)
#guard runIntegersFor [] termHashSharedCycle yIdentity ==
  some ([4110201651], 0, 0)
#guard runCount [] termHashNongroundLeavesOutput == some (1, 0, 0)
#guard runCount [] termHashNongroundKeepsBoundOutput == some (1, 0, 0)
#guard runCount [] termHashMismatch == some (0, 0, 0)
#guard match runQueryError? [] termHashBigIntegerUnsupported with
  | some .unsupportedTermHashConstant => true
  | _ => false
#guard runCount [] metaTermHash == some (1, 0, 0)
#guard runIntegersFor [] termHashNormalizedKey
  { spelling := "Right", occurrence := 0 } ==
    some ([4245664480], 0, 0)
#guard runAtomsFor [] functorDecomposesCompound xIdentity ==
  some (["pair"], 0, 0)
#guard runIntegersFor [] functorDecomposesCompound yIdentity ==
  some ([2], 0, 0)
#guard runShapesFor [] functorDecomposesAtomic xIdentity ==
  some ([.integer 7], 0, 0)
#guard runIntegersFor [] functorDecomposesAtomic yIdentity ==
  some ([0], 0, 0)
#guard runCount [] functorConstructsCompound == some (1, 0, 0)
#guard runCount [] functorConstructsDistinctFreshArguments == some (1, 0, 0)
#guard runShapesFor [] functorConstructsAtomicAtZero xIdentity ==
  some ([.integer 7], 0, 0)
#guard runAtomsFor [] functorDecomposesRationalRoot yIdentity ==
  some (["f"], 0, 0)
#guard runIntegersFor [] functorDecomposesRationalRoot zIdentity ==
  some ([1], 0, 0)
#guard runCount [] functorOutputMismatch == some (0, 0, 0)
#guard runCount [] metaFunctorConstructsCompound == some (1, 0, 0)
#guard match runQueryError? [] functorNameUnbound with
  | some .functorNameUnbound => true
  | _ => false
#guard match runQueryError? [] functorArityUnbound with
  | some .functorArityUnbound => true
  | _ => false
#guard match runQueryError? [] functorNegativeArity with
  | some .invalidFunctorArity => true
  | _ => false
#guard match runQueryError? [] functorNonAtomPositiveName with
  | some .invalidFunctorName => true
  | _ => false
#guard match runQueryError? [] functorExplicitZeroArityCompound with
  | some .zeroArityCompoundFunctor => true
  | _ => false
#guard runShapesFor [] integerAddition xIdentity ==
  some ([.integer 5], 0, 0)
#guard runShapesFor [] integerNestedArithmetic xIdentity ==
  some ([.integer 20], 0, 0)
#guard runShapesFor [] integerSubtraction xIdentity ==
  some ([.integer (-2)], 0, 0)
#guard runShapesFor [] integerModuloNegativeDividend xIdentity ==
  some ([.integer 1], 0, 0)
#guard runShapesFor [] integerModuloNegativeDivisor xIdentity ==
  some ([.integer (-1)], 0, 0)
#guard runCount [] integerIsMismatchFails == some (0, 0, 0)
#guard runCount [] integerComparisonsSucceed == some (1, 0, 0)
#guard runAtoms [] integerComparisonFailureRetainsCaller ==
  some (["b"], 0, 0)
#guard runShapesFor [] metaIntegerAddition xIdentity ==
  some ([.integer 5], 0, 0)
#guard integerArithmeticRejectsUnbound
#guard integerArithmeticRejectsFloat
#guard integerArithmeticRejectsUnsupported
#guard integerArithmeticRejectsZeroDivisor
#guard runAtoms [] caughtGround == some (["ball"], 0, 0)
#guard runRaisedAtom [] throwTimeBoundCatcherRejects == some ("ball", 0, 0)
#guard runRaisedAtom [] recoveryRethrowEscapes == some ("b", 0, 0)
#guard runAtoms [] guardedCutRetainsCaller == some (["c"], 0, 0)
#guard runAtoms [] recoveryCutRetainsCaller == some (["c"], 0, 0)
#guard runAtoms [] catchRetainsGuardedAnswers == some (["a", "b"], 0, 0)
#guard runRaisedAtom [] nestedMismatchRetainsThrowTimeBinding ==
  some ("ball", 0, 0)
#guard runCount [] packetCopySeparatesCaller == some (1, 0, 0)
#guard runCount [] packetCopyPreservesSharing == some (0, 0, 0)
#guard runCount [] packetCopyPreservesSeparation == some (1, 0, 0)
#guard runCount [] throwVariableRaisesInstantiationError == some (1, 0, 0)
#guard runShapesFor [] findallOrderMultiplicity bagIdentity ==
  some ([runtimeTermShape
    (expectedScoped (SourceSignature.list [atom "a", atom "b", atom "a"]))],
    0, 0)
#guard runShapesFor [] findallIsolatesGeneratorBindings bagIdentity ==
  some ([runtimeTermShape
    (expectedScoped (SourceSignature.list [atom "a"]))], 0, 0)
#guard runShapesFor [] findallEmpty bagIdentity ==
  some ([runtimeTermShape (expectedScoped SourceSignature.nil)], 0, 0)
#guard runShapesFor [] findallCutRetainsCaller bagIdentity ==
  some ([runtimeTermShape (expectedScoped (SourceSignature.list [atom "a"])),
    runtimeTermShape (expectedScoped (SourceSignature.list [atom "c"]))], 0, 0)
#guard runShapesFor [] findallExceptionDiscardsPartialBag bagIdentity ==
  some ([runtimeTermShape
    (expectedScoped (SourceSignature.list [atom "caught"]))], 0, 0)
#guard runShapesFor [] nestedFindall outerIdentity ==
  some ([runtimeTermShape (expectedScoped
    (SourceSignature.list [SourceSignature.list [atom "a", atom "b"]]))], 0, 0)
#guard copiedSolutionsAreFreshAndShared
#guard copiedSolutionPreservesSeparation
#guard findallAnswerThenLoopHasOpenPrivatePrefix
#guard runAtoms [] assertzThenCall == some (["a"], 0, 0)
#guard runAtoms [] failedBranchAssertionPersists == some (["a"], 0, 0)
#guard runAtoms [] transactionFirstSolutionRetainsCaller ==
  some (["a", "c"], 0, 0)
#guard runAtoms [] metaTransactionFirstSolution == some (["a"], 0, 0)
#guard runAtoms [] successfulTransactionCommits == some (["a"], 0, 0)
#guard runAtoms [] failedTransactionRollsBack == some ([], 0, 0)
#guard runAtoms [] raisedTransactionRollsBack == some ([], 0, 0)
#guard runAtoms [] caughtInsideTransactionCommits == some (["a"], 0, 0)
#guard runAtoms [] outerRollbackUndoesInnerCommit == some ([], 0, 0)
#guard runAtoms [] innerRollbackPreservesOuterUpdate == some (["a"], 0, 0)
#guard runAtoms [] assertaAndAssertzOrder == some (["a", "b"], 0, 0)
#guard runCount [] assertzReferenceIsBound == some (1, 0, 0)
#guard runCount [] assertaReferenceIsBound == some (1, 0, 0)
#guard runCount [] assertedReferencesAreDistinct == some (1, 0, 0)
#guard runCount [] assertedReferenceRoundTrip == some (1, 0, 0)
#guard preboundAssertReferenceRejectedBeforeInsert
#guard runAtoms [] retractFactsInOrder == some (["a", "b"], 0, 0)
#guard runAtoms [] retractCutPrunesLater == some (["a"], 0, 0)
#guard runAtoms [] retractFactSkipsRule == some (["b"], 0, 0)
#guard runAtoms [] failedBranchRetractionPersists == some ([], 0, 0)
#guard runAtoms [] retractSnapshotRetainsErasedCandidate ==
  some (["b"], 0, 0)
#guard retractSnapshotDoesNotDrift
#guard runAtomsFor [] clauseFactsInOrder xIdentity ==
  some (["a", "b"], 0, 0)
#guard runAtomsFor [] clauseBoundReferenceSelectsOccurrence xIdentity ==
  some (["b"], 0, 0)
#guard runAtomsFor [] clauseRuleBody yIdentity == some (["a"], 0, 0)
#guard runAtomsFor [] clauseCutPrunesLater xIdentity == some (["a"], 0, 0)
#guard runCount [] clauseReferenceRoundTrip == some (1, 0, 0)
#guard clauseVariableHeadRejected
#guard runAtomsFor [] clauseSnapshotDoesNotDrift xIdentity ==
  some (["b"], 0, 0)
#guard runAtomsFor [] clauseSnapshotRetainsErasedCandidate xIdentity ==
  some (["b"], 0, 0)
#guard snapshotDoesNotDrift
#guard laterCallSeesAssertion == some (["old", "new"], 0, 0)
#guard runIntegersFor [] finiteListLength xIdentity == some ([3], 0, 0)
#guard runCount [] matchingListLength == some (1, 0, 0)
#guard runCount [] mismatchingListLength == some (0, 0, 0)
#guard match runQueryError? [] generativeListLength with
  | some .listLengthNeedsEnumeration => true
  | _ => false
#guard runCount binaryFactProgram (currentPredicate "p" 2) == some (1, 0, 0)
#guard runCount binaryFactProgram (currentPredicate "q" 2) == some (0, 0, 0)
#guard runCount [] (currentPredicate "copy_term" 2) == some (1, 0, 0)
#guard runCount [] (currentPredicate "term_variables" 2) == some (1, 0, 0)
#guard runCount [] (currentPredicate "numbervars" 3) == some (1, 0, 0)
#guard runCount [] (currentPredicate "numbervars" 4) == some (1, 0, 0)
#guard runCount [] (currentPredicate "term_hash" 2) == some (1, 0, 0)
#guard runCount [] (currentPredicate "functor" 3) == some (1, 0, 0)
#guard runCount [] (currentPredicate "nb_setval" 2) == some (1, 0, 0)
#guard runCount [] (currentPredicate "nb_getval" 2) == some (1, 0, 0)
#guard runCount [] (currentPredicate "nb_delete" 1) == some (1, 0, 0)
#guard match runQueryError? binaryFactProgram currentPredicateUnbound with
  | some .predicateIndicatorUnbound => true
  | _ => false
#guard runCount [] assertedPredicateBecomesCurrent == some (1, 0, 0)
#guard format2EmitsExactOutput
#guard format2WritesStringPayload
#guard format2RejectsUnsupportedDirective

end Mettapedia.Logic.Prolog.SourceRuntimeRegression
