import Mettapedia.GSLT.Parsing.PlainBnfStructuredDenotation

/-!
# Grammar-derived head election

This module derives a compact-expression plan from a structured grammar
alternative.  The generic policy names only lexical trivia, punctuation, and
categories whose values are operators.  It never identifies a production by
its category/body pair and never supplies a catch-all executable action.

The result is an intermediate *plan*, not another formula representation.  A
later typed compiler must admit the plan against the source constructor's
exact child and result sorts before it can emit an action.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.GrammarHeadElection

open PlainBnfStructuredDenotation

/-- Language-level notation facts used by the generic election rule.  These
are category/token dictionaries, not production occurrences. -/
structure Policy where
  triviaReferences : List String
  openingDelimiters : List String
  closingDelimiters : List String
  separators : List String
  terminators : List String
  /-- Categories whose complete value is source token text.  This set is
  normally derived as a fixed point from lexical/token leaves. -/
  tokenCategories : List String
  operatorCategories : List String
  deriving DecidableEq, Repr

structure Reference where
  name : String
  elementIndex : Nat
  childIndex : Nat
  deriving DecidableEq, Repr

structure Literal where
  text : String
  elementIndex : Nat
  deriving DecidableEq, Repr

inductive Item where
  | reference (value : Reference)
  | literal (value : Literal)
  deriving DecidableEq, Repr

/-- Preserve both source-element position and the physical nonterminal-child
position.  Trivia references advance `childIndex` even when later hidden. -/
def enumerateFrom : List Element → Nat → Nat → List Item
  | [], _, _ => []
  | .reference name _ :: rest, elementIndex, childIndex =>
      .reference ⟨name, elementIndex, childIndex⟩ ::
        enumerateFrom rest (elementIndex + 1) (childIndex + 1)
  | .literal text _ :: rest, elementIndex, childIndex =>
      .literal ⟨text, elementIndex⟩ ::
        enumerateFrom rest (elementIndex + 1) childIndex

def enumerate (alternative : Alternative) : List Item :=
  enumerateFrom alternative.elements 0 0

def Item.isTrivia (policy : Policy) : Item → Bool
  | .reference value => policy.triviaReferences.contains value.name
  | .literal _ => false

def visibleItems (policy : Policy) (alternative : Alternative) : List Item :=
  (enumerate alternative).filter (fun item => !(item.isTrivia policy))

def Item.reference? : Item → Option Reference
  | .reference value => some value
  | .literal _ => none

def Item.literal? : Item → Option Literal
  | .reference _ => none
  | .literal value => some value

def references (items : List Item) : List Reference :=
  items.filterMap Item.reference?

def literals (items : List Item) : List Literal :=
  items.filterMap Item.literal?

def Policy.isOpening (policy : Policy) (text : String) : Bool :=
  policy.openingDelimiters.contains text

def Policy.isPunctuation (policy : Policy) (text : String) : Bool :=
  policy.openingDelimiters.contains text ||
    policy.closingDelimiters.contains text ||
    policy.separators.contains text

def Item.isTerminator (policy : Policy) : Item → Bool
  | .literal value => policy.terminators.contains value.text
  | .reference _ => false

/-- A terminator is concrete punctuation only at the end of an alternative.
The same spelling can remain meaningful inside balanced delimiters. -/
def semanticItems (policy : Policy) (alternative : Alternative) : List Item :=
  ((visibleItems policy alternative).reverse.dropWhile
    (Item.isTerminator policy)).reverse

def meaningfulLiterals (policy : Policy) (items : List Item) : List Literal :=
  (literals items).filter (fun literal => !(policy.isPunctuation literal.text))

def expressionsFor (document : Document) (category : String) : List Expression :=
  document.entries.filterMap fun entry => match entry with
    | .rule name expression _ => if name == category then some expression else none
    | .comment _ _ | .blank _ => none

def addFresh (current additions : List String) : List String :=
  current ++ additions.filter (fun name => !(current.contains name))

/-- An alternative constructs one source token when every visible component
is either literal text or a reference to an already-known token category.
Unlike expression classification, delimiters are retained: `[.]`, `{.}` and
`(.)` are distinct tokens. -/
def surfaceTokenAlternative (policy : Policy) (known : List String)
    (alternative : Alternative) : Bool :=
  let items := visibleItems policy alternative
  !items.isEmpty && items.all fun item => match item with
    | .literal _ => true
    | .reference reference => known.contains reference.name

def surfaceTokenCategory (policy : Policy) (document : Document)
    (known : List String) (category : String) : Bool :=
  let expressions := expressionsFor document category
  !expressions.isEmpty && expressions.all fun expression =>
    !expression.alternatives.isEmpty &&
      expression.alternatives.all (surfaceTokenAlternative policy known)

/-- Least fixed point of grammar categories that construct token text.  The
seed consists of lexical/token leaves supplied by the grammar pipeline; no
production occurrence is named. -/
def deriveSurfaceTokenCategoriesAux (policy : Policy) (document : Document)
    (eligible : List String) : Nat → List String → List String
  | 0, known => known
  | fuel + 1, known =>
      let discovered := eligible.filter
        (surfaceTokenCategory policy document known)
      let next := addFresh known discovered
      if next.length == known.length then known
      else deriveSurfaceTokenCategoriesAux policy document eligible fuel next

def deriveSurfaceTokenCategories (policy : Policy) (document : Document)
    (eligible seeds : List String) : List String :=
  deriveSurfaceTokenCategoriesAux policy document eligible
    (eligible.length + 1) seeds

/-- One alternative denotes an operator token when, after trivia and
punctuation removal, it is either one literal or a transparent reference to
an operator category already known. -/
def operatorLikeAlternative (policy : Policy) (known : List String)
    (alternative : Alternative) : Bool :=
  let items := semanticItems policy alternative
  match meaningfulLiterals policy items, references items with
  | [_], [] => true
  | [], [reference] => known.contains reference.name
  | _, _ => false

def operatorLikeCategory (policy : Policy) (document : Document)
    (known : List String) (category : String) : Bool :=
  let expressions := expressionsFor document category
  !expressions.isEmpty && expressions.all fun expression =>
    !expression.alternatives.isEmpty &&
      expression.alternatives.all (operatorLikeAlternative policy known)

/-- Least fixed-point discovery, bounded by the number of eligible category
names.  Eligibility comes from the grammar's row-kind layer, so lexical word
and number categories cannot accidentally become expression operators. -/
def deriveOperatorCategoriesAux (policy : Policy) (document : Document)
    (eligible : List String) : Nat → List String → List String
  | 0, known => known
  | fuel + 1, known =>
      let discovered := eligible.filter
        (operatorLikeCategory policy document known)
      let next := addFresh known discovered
      if next.length == known.length then known
      else deriveOperatorCategoriesAux policy document eligible fuel next

def deriveOperatorCategories (policy : Policy) (document : Document)
    (eligible : List String) : List String :=
  deriveOperatorCategoriesAux policy document eligible (eligible.length + 1) []

/-- Operator discovery with an admitted lexical/base seed.  The seed's
construction is checked separately; this closure adds only categories whose
alternatives transparently preserve one known operator or introduce one
literal operator. -/
def deriveOperatorCategoriesFrom (policy : Policy) (document : Document)
    (eligible seeds : List String) : List String :=
  deriveOperatorCategoriesAux policy document eligible (eligible.length + 1)
    seeds

inductive Head where
  | fixed (text : String) (elementIndex : Nat)
  | child (reference : Reference)
  deriving DecidableEq, Repr

inductive Failure where
  | competingHeads (heads : List Head)
  | punctuationOnly
  deriving DecidableEq, Repr

inductive TokenPiece where
  | fixed (text : String) (elementIndex : Nat)
  | child (reference : Reference)
  deriving DecidableEq, Repr

def tokenPieces (policy : Policy) (alternative : Alternative) : List TokenPiece :=
  (visibleItems policy alternative).map fun item => match item with
    | .literal literal => .fixed literal.text literal.elementIndex
    | .reference reference => .child reference

/-- A structural plan over exact reference occurrences.  `sequence` and
`chain` are distinct because a typed compiler treats list accumulation and
same-head logical flattening differently. -/
inductive Plan where
  | empty
  | passthrough (child : Reference)
  | grouped (opening closing : String) (child : Reference)
  | literal (text : String)
  | token (pieces : List TokenPiece)
  | singleton (child : Reference)
  | sequence (children : List Reference)
  | tuple (children : List Reference)
  | apply (head : Head) (arguments : List Reference)
  | chain (head : Head) (arguments : List Reference)
  | unresolved (reason : Failure)
  deriving DecidableEq, Repr

/-- Recognize a single child enclosed by concrete grammar delimiters.  The
delimiters remain in the plan because grouping an atom and packaging an
ordered sequence are different typed actions, even though both erase the
surface punctuation. -/
def groupedChild? (policy : Policy) (items : List Item) :
    Option (String × String × Reference) :=
  match items with
  | .literal opening :: middle =>
      match middle.reverse with
      | .literal closing :: reversedBody =>
          let body := reversedBody.reverse
          match references body with
          | [child] =>
              if policy.openingDelimiters.contains opening.text &&
                  policy.closingDelimiters.contains closing.text &&
                  (literals body).all (fun literal =>
                    policy.isPunctuation literal.text) then
                some (opening.text, closing.text, child)
              else none
          | _ => none
      | _ => none
  | _ => none

def fixedCallHead? (policy : Policy) : List Item → Option Head
  | .literal keyword :: .literal delimiter :: _ =>
      if policy.isOpening delimiter.text &&
          !(policy.isPunctuation keyword.text) then
        some (.fixed keyword.text keyword.elementIndex)
      else none
  | _ => none

def dynamicCallHead? (policy : Policy) : List Item → Option Head
  | .reference function :: .literal delimiter :: _ =>
      if policy.isOpening delimiter.text then some (.child function) else none
  | _ => none

def operatorHeads (policy : Policy) (items : List Item) : List Head :=
  items.filterMap fun item => match item with
    | .reference reference =>
        if policy.operatorCategories.contains reference.name then
          some (.child reference)
        else none
    | .literal literal =>
        if policy.isPunctuation literal.text then none
        else some (.fixed literal.text literal.elementIndex)

def Head.isFixed : Head → Bool
  | .fixed _ _ => true
  | .child _ => false

def argumentsWithoutHead (head : Head) (children : List Reference) : List Reference :=
  match head with
  | .fixed _ _ => children
  | .child operator => children.filter (fun child => child.childIndex != operator.childIndex)

def recursiveChild? (category : String) (children : List Reference) : Option Reference :=
  children.find? (fun child => child.name == category)

def applyHead (category : String) (head : Head)
    (children : List Reference) : Plan :=
  let arguments := argumentsWithoutHead head children
  if arguments.isEmpty then
    match head with
    | .fixed text _ => .literal text
    | .child child => .passthrough child
  else if (recursiveChild? category arguments).isSome then
    .chain head arguments
  else .apply head arguments

/-- Generic head election.  Ordering is significant: explicit call syntax is
recognized before operator syntax; recursive same-category applications are
marked as chains; only then do pass-through and sequence defaults apply. -/
def classify (policy : Policy) (category : String)
    (alternative : Alternative) : Plan :=
  if policy.tokenCategories.contains category then
    .token (tokenPieces policy alternative)
  else
    let items := semanticItems policy alternative
    let children := references items
    match groupedChild? policy items with
    | some (opening, closing, child) => .grouped opening closing child
    | none => match fixedCallHead? policy items with
      | some head => .apply head children
      | none => match dynamicCallHead? policy items with
        | some head => .apply head (argumentsWithoutHead head children)
        | none =>
          let heads := operatorHeads policy items
          let fixedHeads := heads.filter Head.isFixed
          match fixedHeads with
          | [head] => applyHead category head children
          | _ :: _ :: _ => .unresolved (.competingHeads fixedHeads)
          | [] =>
            match heads with
            | [head] => applyHead category head children
            | [] =>
                match children with
                | [] => .empty
                | [child] => .passthrough child
                | children => .tuple children
            | heads => .unresolved (.competingHeads heads)

structure ClassifiedAlternative where
  category : String
  alternativeIndex : Nat
  alternative : Alternative
  plan : Plan
  deriving DecidableEq, Repr

def hasSeparator (policy : Policy) (alternative : Alternative) : Bool :=
  (visibleItems policy alternative).any fun item => match item with
    | .literal literal => policy.separators.contains literal.text
    | .reference _ => false

/-- A separated recursive category is a grammar-declared ordered list.  The
orientation is retained by the source order of its reference occurrences. -/
def separatedRecursiveList (policy : Policy) (category : String)
    (expression : Expression) : Bool :=
  expression.alternatives.any fun alternative =>
    hasSeparator policy alternative &&
      (references (semanticItems policy alternative)).any
        (fun child => child.name == category)

def classifyListAlternative (policy : Policy) (category : String)
    (alternative : Alternative) : Plan :=
  let children := references (semanticItems policy alternative)
  if (recursiveChild? category children).isSome then .sequence children
  else match children with
    | [] => .empty
    | [child] => .singleton child
    | children => .sequence children

def classifyExpression (policy : Policy) (category : String)
    (expression : Expression) : List ClassifiedAlternative :=
  let isList := separatedRecursiveList policy category expression
  expression.alternatives.zipIdx.map fun (alternative, index) =>
    let plan := if isList then classifyListAlternative policy category alternative
      else classify policy category alternative
    ⟨category, index, alternative, plan⟩

def classifyEntry (policy : Policy) : Entry → List ClassifiedAlternative
  | .rule category expression _ => classifyExpression policy category expression
  | .comment _ _ | .blank _ => []

def classifyDocument (policy : Policy) (document : Document) :
    List ClassifiedAlternative :=
  document.entries.flatMap (classifyEntry policy)

def Plan.resolved : Plan → Bool
  | .unresolved _ => false
  | _ => true

/-- A category is a transparent alias of a known semantic sort only when all
of its alternatives are bare pass-throughs to already-known categories.
Delimited grouping is intentionally excluded: it can package a sequence as
one host expression. -/
def transparentCategory (policy : Policy) (document : Document)
    (known : List String) (category : String) : Bool :=
  let expressions := expressionsFor document category
  !expressions.isEmpty && expressions.all fun expression =>
    !expression.alternatives.isEmpty && expression.alternatives.all fun alternative =>
      match classify policy category alternative with
      | .passthrough child => known.contains child.name
      | _ => false

def deriveTransparentCategoriesAux (policy : Policy) (document : Document)
    (eligible : List String) : Nat → List String → List String
  | 0, known => known
  | fuel + 1, known =>
      let discovered := eligible.filter
        (transparentCategory policy document known)
      let next := addFresh known discovered
      if next.length == known.length then known
      else deriveTransparentCategoriesAux policy document eligible fuel next

/-- Least fixed point of semantic-sort aliases rooted at a declared set of
categories.  This is reusable sort inference, not a TPTP production list. -/
def deriveTransparentCategories (policy : Policy) (document : Document)
    (eligible seeds : List String) : List String :=
  deriveTransparentCategoriesAux policy document eligible
    (eligible.length + 1) seeds

inductive HeadKey where
  | fixed (text : String)
  | childCategory (name : String)
  deriving DecidableEq, Repr

def Head.key : Head → HeadKey
  | .fixed text _ => .fixed text
  | .child reference => .childCategory reference.name

inductive TokenPieceKey where
  | fixed (text : String)
  | childCategory (name : String)
  deriving DecidableEq, Repr

def TokenPiece.key : TokenPiece → TokenPieceKey
  | .fixed text _ => .fixed text
  | .child reference => .childCategory reference.name

/-- Observable constructor shape after concrete punctuation is erased.
Pass-through keys deliberately omit the child category: if alternatives can
produce overlapping values, their quotient must be justified separately. -/
inductive PlanKey where
  | empty
  | passthrough
  | grouped (opening closing : String)
  | literal (text : String)
  | token (pieces : List TokenPieceKey)
  | singleton
  | sequence (arity : Nat)
  | tuple (arity : Nat)
  | apply (head : HeadKey) (arity : Nat)
  | chain (head : HeadKey) (arity : Nat)
  deriving DecidableEq, Repr

def Plan.key? : Plan → Option PlanKey
  | .empty => some .empty
  | .passthrough _ => some .passthrough
  | .grouped opening closing _ => some (.grouped opening closing)
  | .literal text => some (.literal text)
  | .token pieces => some (.token (pieces.map TokenPiece.key))
  | .singleton _ => some .singleton
  | .sequence children => some (.sequence children.length)
  | .tuple children => some (.tuple children.length)
  | .apply head arguments => some (.apply head.key arguments.length)
  | .chain head arguments => some (.chain head.key arguments.length)
  | .unresolved _ => none

structure Collision where
  category : String
  key : PlanKey
  alternativeIndices : List Nat
  deriving DecidableEq, Repr

def categoryNames (classified : List ClassifiedAlternative) : List String :=
  (classified.map (·.category)).eraseDups

def keysInCategory (classified : List ClassifiedAlternative)
    (category : String) : List PlanKey :=
  (classified.filter (fun row => row.category == category)).filterMap
    (fun row => row.plan.key?) |>.eraseDups

def collisionFor? (classified : List ClassifiedAlternative)
    (category : String) (key : PlanKey) : Option Collision :=
  let indices := (classified.filter fun row =>
    row.category == category && row.plan.key? == some key).map
      (·.alternativeIndex)
  if indices.length > 1 then some ⟨category, key, indices⟩ else none

/-- Every reported collision is computed from the elected plans themselves;
the language-specific layer may justify a quotient or override one semantic
choice, but cannot make an unreported collision disappear. -/
def collisions (classified : List ClassifiedAlternative) : List Collision :=
  (categoryNames classified).flatMap fun category =>
    (keysInCategory classified category).filterMap
      (collisionFor? classified category)

/-! ## Small controls -/

private def span : SourceSpan := ⟨0, 0⟩
private def ref (name : String) : Element := .reference name span
private def lit (text : String) : Element := .literal text span
private def alt (elements : List Element) : Alternative := ⟨elements, span⟩

private def testPolicy : Policy where
  triviaReferences := ["layout"]
  openingDelimiters := ["(", "["]
  closingDelimiters := [")", "]"]
  separators := [","]
  terminators := ["."]
  tokenCategories := ["compound"]
  operatorCategories := ["connective", "quantifier"]

example : classify testPolicy "formula" (alt [ref "atom"]) =
    .passthrough ⟨"atom", 0, 0⟩ := rfl

example : classify testPolicy "annotated"
    (alt [lit "fof", ref "layout", lit "(", ref "name", lit ",",
      ref "formula", lit ")", lit "."]) =
    .apply (.fixed "fof" 0) [⟨"name", 3, 1⟩, ⟨"formula", 5, 2⟩] := rfl

example : classify testPolicy "binary"
    (alt [ref "left", ref "connective", ref "right"]) =
    .apply (.child ⟨"connective", 1, 1⟩)
      [⟨"left", 0, 0⟩, ⟨"right", 2, 2⟩] := rfl

example : classify testPolicy "formula"
    (alt [lit "(", ref "layout", ref "formula", lit ")"]) =
    .grouped "(" ")" ⟨"formula", 2, 1⟩ := rfl

example : classify testPolicy "tuple"
    (alt [lit "[", ref "layout", ref "items", lit "]"]) =
    .grouped "[" "]" ⟨"items", 2, 1⟩ := rfl

example : classify testPolicy "compound"
    (alt [lit "~", ref "vline"]) =
    .token [.fixed "~" 0, .child ⟨"vline", 1, 0⟩] := rfl

/-- A fixed structural operator dominates token-valued operands after the
pure-token case has been ruled out. -/
example : classify { testPolicy with operatorCategories := ["word"] } "role"
    (alt [ref "word", lit "-", ref "payload"]) =
    .apply (.fixed "-" 1) [⟨"word", 0, 0⟩, ⟨"payload", 2, 1⟩] := rfl

/-- Two simultaneous meaningful literals are refused instead of choosing one
by position. -/
example : (classify testPolicy "bad"
    (alt [ref "left", lit ":", ref "middle", lit "=", ref "right"])).resolved =
    false := rfl

end Mettapedia.GSLT.Parsing.GrammarHeadElection
