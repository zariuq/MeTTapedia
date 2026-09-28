import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.CaseTreeCompile
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.CaseTreeConfluence
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.CumulativeConversion

/-!
# Definitions by several equations over the numbers, as case trees

The tower with the numbers and the booleans, and four definitions compiled by
the covering algorithm:

* `eqn : num → num → bool` inspects both arguments;
* `max : num → num → num` is Norell's example:
  `max zero y = y; max x zero = x; max (succ x) (succ y) = succ (max x y)`;
* `half : num → num` recurses on a sub-pattern two levels down:
  `half (succ (succ n)) = succ (half n)`;
* `pick : num → num → num` is `pick zero y = 1; pick x zero = 2; pick x y = 3`.

Each compiles to the expected tree. The trees compute by first-match
selection: `max (succ x) zero` steps to `succ x`, while `max x zero` is stuck
for a neutral `x`, so the second equation of `max` does not hold
definitionally. Likewise `pick x zero` is stuck for a neutral `x` although its
second equation matches. Without its last equation `pick` does not cover the
case `pick (succ x) (succ y)` and is not compiled. `eqn` is stuck on a neutral
second argument once its first is canonical: it inspects both arguments.

The rule package computing by the four trees is Church–Rosser.

Each defined constant's role carries the inspection skeleton of its tree, so
weak-head reduction inspects the arguments in the tree's order, nested
positions included (`half` inspects the predecessor of its argument), and the
package meets the root-shape obligations of weak-head reduction with these
roles.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open ConversionCoherence (ChurchRosser)

namespace TowerCaseTreesModel

/-! ## Names, roles and families -/

/-- The type of natural numbers. -/
def num : DeclName := .mkSimple "num"
/-- The constructor for zero. -/
def zero : DeclName := .mkSimple "zero"
/-- The successor constructor. -/
def succ : DeclName := .mkSimple "succ"
/-- The type of booleans. -/
def bool : DeclName := .mkSimple "bool"
/-- True. -/
def tt : DeclName := .mkSimple "true"
/-- False. -/
def ff : DeclName := .mkSimple "false"
/-- Equality test of numbers. -/
def eqn : DeclName := .mkSimple "eqn"
/-- The maximum of two numbers. -/
def max : DeclName := .mkSimple "max"
/-- Half of a number, rounded down. -/
def half : DeclName := .mkSimple "half"
/-- The first-match control. -/
def pick : DeclName := .mkSimple "pick"

/-- The constructors of the numbers. -/
def numCtors : List (DeclName × List (Field Tower.Head)) := [(zero, []), (succ, [.recursive])]

/-- The constructors of the booleans. -/
def boolCtors : List (DeclName × List (Field Tower.Head)) := [(tt, []), (ff, [])]

/-- The number `k`. -/
def numeral {n : Nat} : Nat → Tm Tower.Head n
  | 0 => .const zero
  | k + 1 => .app (.const succ) (numeral k)

/-! ## The trees -/

/-- The tree of `eqn`: split the first argument, then the second. -/
def eqnTree : CaseTree Tower.Head :=
  .split 0 num
    (.cons zero 0
      (.split 0 num
        (.cons zero 0 (.leaf 0 (.const tt))
          (.cons succ 1 (.leaf 1 (.const ff)) .nil)))
      (.cons succ 1
        (.split 1 num
          (.cons zero 0 (.leaf 1 (.const ff))
            (.cons succ 1 (.leaf 2 (appSpine (.const eqn) [.var 1, .var 0])) .nil)))
        .nil))

/-- The tree of `max`: the first argument first; the second only after a
successor. -/
def maxTree : CaseTree Tower.Head :=
  .split 0 num
    (.cons zero 0 (.leaf 1 (.var 0))
      (.cons succ 1
        (.split 1 num
          (.cons zero 0 (.leaf 1 (.app (.const succ) (.var 0)))
            (.cons succ 1 (.leaf 2 (.app (.const succ) (appSpine (.const max) [.var 1, .var 0])))
              .nil)))
        .nil))

/-- The tree of `half`: split the argument, then the predecessor. -/
def halfTree : CaseTree Tower.Head :=
  .split 0 num
    (.cons zero 0 (.leaf 0 (.const zero))
      (.cons succ 1
        (.split 0 num
          (.cons zero 0 (.leaf 0 (.const zero))
            (.cons succ 1 (.leaf 1 (.app (.const succ) (appSpine (.const half) [.var 0]))) .nil)))
        .nil))

/-- The tree of `pick`. -/
def pickTree : CaseTree Tower.Head :=
  .split 0 num
    (.cons zero 0 (.leaf 1 (numeral 1))
      (.cons succ 1
        (.split 1 num
          (.cons zero 0 (.leaf 1 (numeral 2))
            (.cons succ 1 (.leaf 2 (numeral 3)) .nil)))
        .nil))

/-- The roles: the families, their constructors, and the defined constants
with the inspection skeletons of their trees. -/
def roles : Roles Tower.Head := fun name =>
  if name = num then .inductive numCtors
  else if name = zero then .constructor 0
  else if name = succ then .constructor 1
  else if name = bool then .inductive boolCtors
  else if name = tt then .constructor 0
  else if name = ff then .constructor 0
  else if name = half then .computes 1 halfTree.inspect
  else if name = eqn ∨ name = max ∨ name = pick then
    .computes 2 (if name = eqn then eqnTree.inspect else if name = max then maxTree.inspect
      else pickTree.inspect)
  else .rigid

/-- The family of each constructor. -/
def familyOf : DeclName → DeclName := fun c =>
  if c = zero ∨ c = succ then num else if c = tt ∨ c = ff then bool else .anonymous

theorem roles_num : roles num = .inductive numCtors := rfl
theorem roles_bool : roles bool = .inductive boolCtors := rfl

/-- Only `num` and `bool` are inductive types. -/
theorem roles_inductive {T : DeclName} {cs : List (DeclName × List (Field Tower.Head))}
    (role : roles T = .inductive cs) :
    (T = num ∧ cs = numCtors) ∨ (T = bool ∧ cs = boolCtors) := by
  unfold roles at role
  split at role
  · exact .inl ⟨by assumption, (Role.inductive.inj role).symm⟩
  split at role
  · cases role
  split at role
  · cases role
  split at role
  · exact .inr ⟨by assumption, (Role.inductive.inj role).symm⟩
  split at role
  · cases role
  split at role
  · cases role
  split at role
  · cases role
  split at role
  · cases role
  cases role

theorem constructorsDeclared : ConstructorsDeclared roles where
  arity := by
    intro T cs k fields role mem
    rcases roles_inductive role with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp only [numCtors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
      rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
    · simp only [boolCtors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
      rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  distinct := by
    intro T cs role
    rcases roles_inductive role with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

/-! ## `eqn`: both arguments inspected -/

/-- `eqn zero zero = true`, `eqn zero (succ m) = false`, `eqn (succ n) zero = false`,
`eqn (succ n) (succ m) = eqn n m`. -/
def eqnEquations : List (Equation Tower.Head) :=
  [⟨[.con zero [], .con zero []], (.const tt : Tm Tower.Head 0)⟩,
   ⟨[.con zero [], .con succ [.var]], (.const ff : Tm Tower.Head 1)⟩,
   ⟨[.con succ [.var], .con zero []], (.const ff : Tm Tower.Head 1)⟩,
   ⟨[.con succ [.var], .con succ [.var]],
     (appSpine (.const eqn) [.var 1, .var 0] : Tm Tower.Head 2)⟩]

theorem eqn_compile : compile roles familyOf 2 eqnEquations = some eqnTree := by
  rfl

/-! ## `max`: Norell's example -/

/-- `max zero y = y`, `max x zero = x`, `max (succ x) (succ y) = succ (max x y)`. -/
def maxEquations : List (Equation Tower.Head) :=
  [⟨[.con zero [], .var], (.var 0 : Tm Tower.Head 1)⟩,
   ⟨[.var, .con zero []], (.var 0 : Tm Tower.Head 1)⟩,
   ⟨[.con succ [.var], .con succ [.var]],
     (.app (.const succ) (appSpine (.const max) [.var 1, .var 0]) : Tm Tower.Head 2)⟩]

theorem max_compile : compile roles familyOf 2 maxEquations = some maxTree := by
  rfl

/-! ## `half`: a recursive call two constructors down -/

/-- `half zero = zero`, `half (succ zero) = zero`, `half (succ (succ n)) = succ (half n)`. -/
def halfEquations : List (Equation Tower.Head) :=
  [⟨[.con zero []], (.const zero : Tm Tower.Head 0)⟩,
   ⟨[.con succ [.con zero []]], (.const zero : Tm Tower.Head 0)⟩,
   ⟨[.con succ [.con succ [.var]]],
     (.app (.const succ) (appSpine (.const half) [.var 0]) : Tm Tower.Head 1)⟩]

theorem half_compile : compile roles familyOf 1 halfEquations = some halfTree := by
  rfl

/-! ## `pick`: an earlier blocked equation blocks a later match -/

/-- `pick zero y = 1`, `pick x zero = 2`. -/
def pickEquations₂ : List (Equation Tower.Head) :=
  [⟨[.con zero [], .var], (numeral 1 : Tm Tower.Head 1)⟩,
   ⟨[.var, .con zero []], (numeral 2 : Tm Tower.Head 1)⟩]

/-- `pick zero y = 1`, `pick x zero = 2`, `pick x y = 3`. -/
def pickEquations : List (Equation Tower.Head) :=
  pickEquations₂ ++ [⟨[.var, .var], (numeral 3 : Tm Tower.Head 2)⟩]

theorem pick_compile : compile roles familyOf 2 pickEquations = some pickTree := by
  rfl

/-- Without its last equation `pick` misses `pick (succ x) (succ y)`: no tree. -/
theorem pick_missing_case : compile roles familyOf 2 pickEquations₂ = none := by
  rfl

/-! ## Steps and stuck spines -/

section Controls

variable {n : Nat}

/-- A constructor pattern of the numbers is blocked on a neutral value. -/
theorem blocked_num {c : DeclName} (hc : familyOf c = num) (ps : List Pat)
    {x : Tm Tower.Head n} (neutral : Neutral roles x) :
    Pat.matchValue roles familyOf (.con c ps) x = .blocked num x := by
  rw [Pat.matchValue_neutral constructorsDeclared ps (cs := numCtors) (by rw [hc]; rfl) neutral,
    hc]

/-- `eqn zero zero` steps to `true`. -/
theorem eqn_zero_zero :
    eqnTree.Step eqn 2 (appSpine (.const eqn) [.const zero, .const zero] : Tm Tower.Head n)
      (.const tt) := by
  have step := compile_firstMatch eqn_compile eqn (n := n) (args := [.const zero, .const zero])
      (i := 0) (by decide)
      (values := []) rfl
      (fun j hj => absurd hj (Nat.not_lt_zero j))
  exact step

/-- `eqn (succ a) (succ b)` steps to `eqn a b`. -/
theorem eqn_succ_succ (a b : Tm Tower.Head n) :
    eqnTree.Step eqn 2 (appSpine (.const eqn) [.app (.const succ) a, .app (.const succ) b])
      (appSpine (.const eqn) [a, b]) := by
  have step := compile_firstMatch eqn_compile eqn
      (args := [.app (.const succ) a, .app (.const succ) b])
      (i := 3) (by decide) (values := [a, b]) rfl
      (fun j hj => by
        rcases j with _ | _ | _ | j
        · rfl
        · rfl
        · rfl
        · exact absurd hj (by omega))
  exact step

/-- `eqn x zero` is stuck for a neutral `x`. -/
theorem eqn_stuck_first {x : Tm Tower.Head n} (neutral : Neutral roles x) (u : Tm Tower.Head n) :
    ¬ eqnTree.Step eqn 2 (appSpine (.const eqn) [x, .const zero]) u := by
  refine compile_blocked eqn_compile eqn (j := 0) (by decide) ⟨num, x, ?_⟩
    (fun i hi => absurd hi (Nat.not_lt_zero i)) u
  show (Pat.matchValue roles familyOf (.con zero []) x).seq
    (Pat.matchValues roles familyOf [.con zero []] [.const zero]) = _
  rw [blocked_num rfl [] neutral]
  rfl

/-- `eqn` inspects its second argument too: `eqn zero y` is stuck for a
neutral `y`. -/
theorem eqn_stuck_second {y : Tm Tower.Head n} (neutral : Neutral roles y) (u : Tm Tower.Head n) :
    ¬ eqnTree.Step eqn 2 (appSpine (.const eqn) [.const zero, y]) u := by
  refine compile_blocked eqn_compile eqn (j := 0) (by decide) ⟨num, y, ?_⟩
    (fun i hi => absurd hi (Nat.not_lt_zero i)) u
  show (Pat.matchValue roles familyOf (.con zero []) (.const zero)).seq
    ((Pat.matchValue roles familyOf (.con zero []) y).seq
      (Pat.matchValues roles familyOf [] [])) = _
  rw [blocked_num rfl [] neutral]
  rfl

/-- `max zero y` steps to `y` for every `y`. -/
theorem max_zero_left (y : Tm Tower.Head n) :
    maxTree.Step max 2 (appSpine (.const max) [.const zero, y]) y := by
  have step := compile_firstMatch max_compile max (args := [.const zero, y]) (i := 0) (by decide)
      (values := [y]) rfl
      (fun j hj => absurd hj (Nat.not_lt_zero j))
  exact step

/-- `max (succ x) zero` steps to `succ x`. -/
theorem max_succ_zero (x : Tm Tower.Head n) :
    maxTree.Step max 2 (appSpine (.const max) [.app (.const succ) x, .const zero])
      (.app (.const succ) x) := by
  have step := compile_firstMatch max_compile max
      (args := [.app (.const succ) x, .const zero]) (i := 1)
      (by decide) (values := [.app (.const succ) x]) rfl
      (fun j hj => by
        rcases j with _ | j
        · rfl
        · exact absurd hj (by omega))
  exact step

/-- `max (succ x) (succ y)` steps to `succ (max x y)`. -/
theorem max_succ_succ (x y : Tm Tower.Head n) :
    maxTree.Step max 2 (appSpine (.const max) [.app (.const succ) x, .app (.const succ) y])
      (.app (.const succ) (appSpine (.const max) [x, y])) := by
  have step := compile_firstMatch max_compile max
      (args := [.app (.const succ) x, .app (.const succ) y])
      (i := 2) (by decide) (values := [x, y]) rfl
      (fun j hj => by
        rcases j with _ | _ | j
        · rfl
        · rfl
        · exact absurd hj (by omega))
  exact step

/-- `max x zero` is stuck for a neutral `x`: the second equation of `max`
does not hold definitionally. -/
theorem max_stuck {x : Tm Tower.Head n} (neutral : Neutral roles x) (u : Tm Tower.Head n) :
    ¬ maxTree.Step max 2 (appSpine (.const max) [x, .const zero]) u := by
  refine compile_blocked max_compile max (j := 0) (by decide) ⟨num, x, ?_⟩
    (fun i hi => absurd hi (Nat.not_lt_zero i)) u
  show (Pat.matchValue roles familyOf (.con zero []) x).seq
    (Pat.matchValues roles familyOf [.var] [.const zero]) = _
  rw [blocked_num rfl [] neutral]
  rfl

/-- The second equation of `max` matches `max x zero` all the same. -/
theorem max_second_matches (x : Tm Tower.Head n) :
    maxEquations[1].Matches roles familyOf [x, .const zero] [x] :=
  rfl

/-- `half zero` steps to `zero`. -/
theorem half_zero :
    halfTree.Step half 1 (appSpine (.const half) [.const zero] : Tm Tower.Head n)
      (.const zero) := by
  have step := compile_firstMatch half_compile half (n := n) (args := [.const zero]) (i := 0)
      (by decide)
      (values := []) rfl
      (fun j hj => absurd hj (Nat.not_lt_zero j))
  exact step

/-- `half (succ zero)` steps to `zero`. -/
theorem half_one :
    halfTree.Step half 1 (appSpine (.const half) [numeral 1] : Tm Tower.Head n) (.const zero) := by
  have step := compile_firstMatch half_compile half (n := n) (args := [numeral 1]) (i := 1)
      (by decide)
      (values := []) rfl
      (fun j hj => by
        rcases j with _ | j
        · rfl
        · exact absurd hj (by omega))
  exact step

/-- `half (succ (succ x))` steps to `succ (half x)`: the recursive call is on a
variable two constructors down. -/
theorem half_succ_succ (x : Tm Tower.Head n) :
    halfTree.Step half 1 (appSpine (.const half) [.app (.const succ) (.app (.const succ) x)])
      (.app (.const succ) (appSpine (.const half) [x])) := by
  have step := compile_firstMatch half_compile half
      (args := [.app (.const succ) (.app (.const succ) x)])
      (i := 2) (by decide) (values := [x]) rfl
      (fun j hj => by
        rcases j with _ | _ | j
        · rfl
        · rfl
        · exact absurd hj (by omega))
  exact step

/-- `half (succ x)` is stuck for a neutral `x`: the tree inspects the
predecessor. -/
theorem half_stuck {x : Tm Tower.Head n} (neutral : Neutral roles x) (u : Tm Tower.Head n) :
    ¬ halfTree.Step half 1 (appSpine (.const half) [.app (.const succ) x]) u := by
  refine compile_blocked half_compile half (j := 1) (by decide) ⟨num, x, ?_⟩
    (fun i hi => by
      rcases i with _ | i
      · rfl
      · exact absurd hi (by omega)) u
  show ((Pat.matchValue roles familyOf (.con zero []) x).seq
    (Pat.matchValues roles familyOf [] [])).seq (Pat.matchValues roles familyOf [] []) = _
  rw [blocked_num rfl [] neutral]
  rfl

/-- `pick zero y` steps to `1`. -/
theorem pick_zero (y : Tm Tower.Head n) :
    pickTree.Step pick 2 (appSpine (.const pick) [.const zero, y]) (numeral 1) := by
  have step := compile_firstMatch pick_compile pick (args := [.const zero, y]) (i := 0) (by decide)
      (values := [y]) rfl
      (fun j hj => absurd hj (Nat.not_lt_zero j))
  exact step

/-- `pick (succ x) zero` steps to `2`. -/
theorem pick_succ_zero (x : Tm Tower.Head n) :
    pickTree.Step pick 2 (appSpine (.const pick) [.app (.const succ) x, .const zero])
      (numeral 2) := by
  have step := compile_firstMatch pick_compile pick
      (args := [.app (.const succ) x, .const zero]) (i := 1)
      (by decide) (values := [.app (.const succ) x]) rfl
      (fun j hj => by
        rcases j with _ | j
        · rfl
        · exact absurd hj (by omega))
  exact step

/-- The second equation of `pick` matches `pick x zero`. -/
theorem pick_second_matches (x : Tm Tower.Head n) :
    pickEquations[1].Matches roles familyOf [x, .const zero] [x] :=
  rfl

/-- Yet for a neutral `x`, `pick x zero` is stuck: the first equation is
blocked on `x`, so the second does not fire. -/
theorem pick_stuck {x : Tm Tower.Head n} (neutral : Neutral roles x) (u : Tm Tower.Head n) :
    ¬ pickTree.Step pick 2 (appSpine (.const pick) [x, .const zero]) u := by
  refine compile_blocked pick_compile pick (j := 0) (by decide) ⟨num, x, ?_⟩
    (fun i hi => absurd hi (Nat.not_lt_zero i)) u
  show (Pat.matchValue roles familyOf (.con zero []) x).seq
    (Pat.matchValues roles familyOf [.var] [.const zero]) = _
  rw [blocked_num rfl [] neutral]
  rfl

end Controls

/-! ## The package -/

/-- The universe of the numbers and the booleans. -/
def u : Tower.Head := .sort (.const 0)

/-- The declared types. -/
def constantType : DeclName → Option (Tm Tower.Head 0) := fun name =>
  if name = num ∨ name = bool then some (.head u)
  else if name = zero then some (.const num)
  else if name = succ then some (.pi (.const num) (.const num))
  else if name = tt ∨ name = ff then some (.const bool)
  else if name = eqn then some (.pi (.const num) (.pi (.const num) (.const bool)))
  else if name = max ∨ name = pick then some (.pi (.const num) (.pi (.const num) (.const num)))
  else if name = half then some (.pi (.const num) (.const num))
  else none

/-- The four definitions with their compiled trees. -/
def definitions : List (CaseTreeDefinition Tower.Head) :=
  [⟨eqn, 2, eqnTree⟩, ⟨max, 2, maxTree⟩, ⟨half, 1, halfTree⟩, ⟨pick, 2, pickTree⟩]

/-- The tower with the numbers, the booleans and the four definitions,
computing by their trees. -/
def rules : Rules Tower.Head :=
  { Tower.rules with
    constantType := constantType
    computation := caseTreeComputation definitions }

theorem compiled {d : CaseTreeDefinition Tower.Head} (mem : d ∈ definitions) :
    ∃ eqs, compile roles familyOf d.arity eqs = some d.tree := by
  simp only [definitions, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl
  · exact ⟨_, eqn_compile⟩
  · exact ⟨_, max_compile⟩
  · exact ⟨_, half_compile⟩
  · exact ⟨_, pick_compile⟩

theorem leafConditions : LeafConditions definitions where
  names := by decide
  arity_pos := by decide
  inScope := fun _ mem => by
    obtain ⟨_, h⟩ := compiled mem
    exact compile_scoped h
  constructors := by decide

/-- The package computing by the four trees is Church–Rosser. -/
theorem churchRosser : ChurchRosser rules :=
  caseTree_churchRosser leafConditions Iff.rfl Tower.headEq_symmetric

/-- Every root step happens at a defined constant applied to its arity whose
tree's skeleton accepts the arguments. -/
theorem shape : RootShape rules roles where
  spine := by
    intro n t u ⟨d, mem, step⟩
    obtain ⟨_, h⟩ := compiled mem
    have role : roles d.name = .computes d.arity d.tree.inspect := by
      simp only [definitions, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl | rfl <;> rfl
    obtain ⟨args, rfl, length, settled⟩ :=
      CaseTree.step_settled constructorsDeclared (compile_covers h) step
    exact ⟨d.name, d.arity, _, args, role, rfl, length, settled.accepts⟩
  deterministic := fun first second =>
    caseTreeComputation_deterministic (by decide) second first

/-! ## Weak-head reduction by the trees -/

/-- `half` reduces the predecessor of its argument before stepping: its tree's
skeleton inspects a position nested inside the successor it has accepted. -/
theorem half_reduces_nested {n : Nat} (a : Tm Tower.Head n) :
    WhStep rules roles (appSpine (.const half) [.app (.const succ) (.app (.lam (.var 0)) a)])
      (appSpine (.const half) [.app (.const succ) a]) := by
  have focus : halfTree.inspect.Focus roles [.app (.const succ) (.app (.lam (.var 0)) a)]
      [.app (.const succ) a] .constructor (.app (.lam (.var 0)) a) a :=
    .constructor (before := []) (after := []) (before' := []) (after' := []) (key := .const succ)
      (fields := [.app (.lam (.var 0)) a]) (fields' := [a]) rfl rfl rfl
      (.spine [.app (.lam (.var 0)) a] rfl) (.spine [a] rfl) (.here (before := []) (after := []) rfl)
  exact .scrutinee rfl rfl focus (.beta (.var 0) a)

/-- `half (succ x)` is neutral for a variable `x`: the nested inspection
reaches the variable. -/
theorem half_succ_var_neutral {n : Nat} (i : Fin n) :
    Neutral roles (appSpine (.const half) [.app (.const succ) (.var i)] : Tm Tower.Head n) :=
  .stuck (inspect := halfTree.inspect) rfl rfl
    (.constructor (before := []) (after := []) (before' := []) (after' := []) (key := .const succ)
      rfl rfl rfl (.spine [.var i] rfl) (.spine [.var i] rfl) (.here (before := []) (after := []) rfl))
    (.var i) nofun

/-- `half (succ x)` is a weak-head normal form for a variable `x`. -/
theorem half_succ_var_whnf {n : Nat} (i : Fin n) :
    Whnf rules roles (appSpine (.const half) [.app (.const succ) (.var i)] : Tm Tower.Head n) :=
  (half_succ_var_neutral i).whnf shape

/-! ## Axiom audit -/

#print axioms roles_inductive
#print axioms constructorsDeclared
#print axioms eqn_compile
#print axioms max_compile
#print axioms half_compile
#print axioms pick_compile
#print axioms pick_missing_case
#print axioms blocked_num
#print axioms eqn_zero_zero
#print axioms eqn_succ_succ
#print axioms eqn_stuck_first
#print axioms eqn_stuck_second
#print axioms max_zero_left
#print axioms max_succ_zero
#print axioms max_succ_succ
#print axioms max_stuck
#print axioms max_second_matches
#print axioms half_zero
#print axioms half_one
#print axioms half_succ_succ
#print axioms half_stuck
#print axioms pick_zero
#print axioms pick_succ_zero
#print axioms pick_second_matches
#print axioms pick_stuck
#print axioms compiled
#print axioms leafConditions
#print axioms churchRosser
#print axioms shape
#print axioms half_reduces_nested
#print axioms half_succ_var_neutral
#print axioms half_succ_var_whnf
#print axioms roles_num
#print axioms roles_bool

end TowerCaseTreesModel

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
