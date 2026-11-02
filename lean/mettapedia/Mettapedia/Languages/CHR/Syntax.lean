import Mathlib.Data.List.Basic

/-! Source-independent data for ground CHR. Rule variables are local indices;
runtime values contain no logical variables. A body remains an ordered list
of goals, so evaluating a later arithmetic goal cannot move ahead of an
earlier constraint call. -/

set_option autoImplicit false

namespace Mettapedia.Languages.CHR

inductive Value where
  | integer (value : Int)
  | atom (name : String)
  | tuple (fields : List Value)
  deriving Repr

mutual
  private def Value.decEq : (first second : Value) → Decidable (first = second)
    | .integer first, .integer second => if same : first = second then isTrue (by cases same; rfl)
      else isFalse (by intro equal; exact same (Value.integer.inj equal))
    | .integer first, .atom second => isFalse (by intro same; cases same)
    | .integer first, .tuple second => isFalse (by intro same; cases same)
    | .atom first, .integer second => isFalse (by intro same; cases same)
    | .atom first, .atom second => if same : first = second then isTrue (by cases same; rfl)
      else isFalse (by intro equal; exact same (Value.atom.inj equal))
    | .atom first, .tuple second => isFalse (by intro same; cases same)
    | .tuple first, .integer second => isFalse (by intro same; cases same)
    | .tuple first, .atom second => isFalse (by intro same; cases same)
    | .tuple first, .tuple second => match Value.listDecEq first second with
      | isTrue same => isTrue (by cases same; rfl)
      | isFalse different => isFalse (by intro same; exact different (Value.tuple.inj same))

  private def Value.listDecEq : (first second : List Value) → Decidable (first = second)
    | [], [] => isTrue rfl
    | [], _ :: _ => isFalse (by intro same; cases same)
    | _ :: _, [] => isFalse (by intro same; cases same)
    | first :: rest, second :: tail =>
      match Value.decEq first second, Value.listDecEq rest tail with
      | isTrue same, isTrue tails => isTrue (by cases same; cases tails; rfl)
      | isFalse different, _ => isFalse (by intro same; exact different (List.cons.inj same).1)
      | _, isFalse different => isFalse (by intro same; exact different (List.cons.inj same).2)
end

instance : DecidableEq Value := Value.decEq
instance : BEq Value := ⟨fun first second => decide (first = second)⟩
instance : LawfulBEq Value where
  rfl := by intro first; simp
  eq_of_beq := by intro first second same; exact of_decide_eq_true same

abbrev Environment := List (Nat × Value)

def lookup (environment : Environment) (index : Nat) : Option Value :=
  (environment.find? (fun binding => binding.1 == index)).map Prod.snd

inductive Term where
  | value (value : Value)
  | var (index : Nat)
  | tuple (fields : List Term)
  deriving Repr

mutual
  private def Term.decEq : (first second : Term) → Decidable (first = second)
    | .value first, .value second => if same : first = second then isTrue (by cases same; rfl)
      else isFalse (by intro equal; exact same (Term.value.inj equal))
    | .value first, .var second => isFalse (by intro same; cases same)
    | .value first, .tuple second => isFalse (by intro same; cases same)
    | .var first, .value second => isFalse (by intro same; cases same)
    | .var first, .var second => if same : first = second then isTrue (by cases same; rfl)
      else isFalse (by intro equal; exact same (Term.var.inj equal))
    | .var first, .tuple second => isFalse (by intro same; cases same)
    | .tuple first, .value second => isFalse (by intro same; cases same)
    | .tuple first, .var second => isFalse (by intro same; cases same)
    | .tuple first, .tuple second => match Term.listDecEq first second with
      | isTrue same => isTrue (by cases same; rfl)
      | isFalse different => isFalse (by intro same; exact different (Term.tuple.inj same))

  private def Term.listDecEq : (first second : List Term) → Decidable (first = second)
    | [], [] => isTrue rfl
    | [], _ :: _ => isFalse (by intro same; cases same)
    | _ :: _, [] => isFalse (by intro same; cases same)
    | first :: rest, second :: tail =>
      match Term.decEq first second, Term.listDecEq rest tail with
      | isTrue same, isTrue tails => isTrue (by cases same; cases tails; rfl)
      | isFalse different, _ => isFalse (by intro same; exact different (List.cons.inj same).1)
      | _, isFalse different => isFalse (by intro same; exact different (List.cons.inj same).2)
end

instance : DecidableEq Term := Term.decEq
instance : BEq Term := ⟨fun first second => decide (first = second)⟩
instance : LawfulBEq Term where
  rfl := by intro first; simp
  eq_of_beq := by intro first second same; exact of_decide_eq_true same

def Term.instantiate (environment : Environment) : Term → Option Value
  | .value datum => some datum
  | .var index => lookup environment index
  | .tuple fields => Value.tuple <$> fields.mapM (Term.instantiate environment)

def Term.variables : Term → List Nat
  | .value _ => []
  | .var index => [index]
  | .tuple fields => fields.flatMap Term.variables

structure Constraint where
  name : String
  arguments : List Value
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

structure Head where
  name : String
  arguments : List Term
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

def Head.instantiate (environment : Environment) (head : Head) : Option Constraint := do
  pure ⟨head.name, ← head.arguments.mapM (Term.instantiate environment)⟩

def Head.variables (head : Head) : List Nat := head.arguments.flatMap Term.variables

inductive ArithmeticFault where
  | unbound (index : Nat)
  | nonInteger (value : Value)
  | uninstantiated (term : Term)
  | divisionByZero
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

inductive IntOperator where
  | add | subtract | multiply | quotient | remainder | modulo
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

/-- `quotient` and `remainder` truncate toward zero; `modulo` has the
divisor's sign, as in the Prolog integer operations `//`, `rem` and `mod`. -/
def IntOperator.eval : IntOperator → Int → Int → Except ArithmeticFault Int
  | .add, left, right => .ok (left + right)
  | .subtract, left, right => .ok (left - right)
  | .multiply, left, right => .ok (left * right)
  | .quotient, left, right =>
      if right = 0 then .error .divisionByZero else .ok (left.tdiv right)
  | .remainder, left, right =>
      if right = 0 then .error .divisionByZero else .ok (left.tmod right)
  | .modulo, left, right =>
      if right = 0 then .error .divisionByZero
      else let remainder := left % right
        .ok (if right < 0 ∧ remainder ≠ 0 then remainder + right else remainder)

inductive IntExpr where
  | literal (value : Int)
  | index (index : Nat)
  | operation (operator : IntOperator) (left right : IntExpr)
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

def IntExpr.eval (environment : Environment) : IntExpr → Except ArithmeticFault Int
  | .literal value => .ok value
  | .index idx => match lookup environment idx with
      | none => .error (.unbound idx)
      | some (.integer value) => .ok value
      | some value => .error (.nonInteger value)
  | .operation operator left right => do
      operator.eval (← left.eval environment) (← right.eval environment)

inductive Comparison where
  | equal | different | less | lessEqual | greater | greaterEqual
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

def Comparison.holds : Comparison → Int → Int → Bool
  | .equal, left, right => left == right
  | .different, left, right => left != right
  | .less, left, right => decide (left < right)
  | .lessEqual, left, right => decide (left ≤ right)
  | .greater, left, right => decide (left > right)
  | .greaterEqual, left, right => decide (left ≥ right)

inductive Guard where
  | identical (left right : Term)
  | distinct (left right : Term)
  | compare (operator : Comparison) (left right : IntExpr)
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

def Guard.eval (environment : Environment) : Guard → Except ArithmeticFault Bool
  | .identical left right => do
      let some leftValue := left.instantiate environment | .error (.uninstantiated left)
      let some rightValue := right.instantiate environment | .error (.uninstantiated right)
      pure (leftValue == rightValue)
  | .distinct left right => do
      let some leftValue := left.instantiate environment | .error (.uninstantiated left)
      let some rightValue := right.instantiate environment | .error (.uninstantiated right)
      pure (leftValue != rightValue)
  | .compare operator left right => do
      pure (operator.holds (← left.eval environment) (← right.eval environment))

inductive Goal where
  | tell (constraint : Head)
  | assign (index : Nat) (expression : IntExpr)
  | fail
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

structure Rule where
  name : String
  kept : List Head
  removed : List Head
  guards : List Guard
  body : List Goal
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

def Rule.heads (rule : Rule) : List Head := rule.kept ++ rule.removed
def Rule.variables (rule : Rule) : List Nat := rule.heads.flatMap Head.variables
def Rule.propagation (rule : Rule) : Bool := rule.removed.isEmpty

/-- SWI's refined profile registers removed head occurrences before kept
head occurrences within each rule. Head identities still use `Rule.heads`.
This makes duplicate cleanup retain the already suspended occurrence. -/
def Rule.visitOrder (rule : Rule) : List Nat :=
  ((List.range rule.removed.length).map (· + rule.kept.length)) ++ List.range rule.kept.length

structure Declaration where
  name : String
  arity : Nat
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

structure Program where
  declarations : List Declaration
  rules : List Rule
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

/-- A rule occurrence, distinct from a runtime constraint occurrence. -/
structure RuleOccurrence where
  rule : Nat
  head : Nat
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

def occurrences (program : Program) : List RuleOccurrence :=
  program.rules.zipIdx.flatMap fun (rule, index) =>
    rule.visitOrder.map fun head => ⟨index, head⟩

end Mettapedia.Languages.CHR
