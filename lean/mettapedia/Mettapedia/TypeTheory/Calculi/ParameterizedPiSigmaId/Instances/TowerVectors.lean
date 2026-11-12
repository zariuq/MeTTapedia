import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerNumbers
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerEliminator
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.DeclaredComputations
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.WeakHeadNormalization

/-!
# Vectors with their dependent eliminator in the cumulative tower

The tower extended by

* the natural numbers `num`, `zero`, `succ` with their recursor `num-rec`;
* the unit type `unit`, its constructor `tt` and its recursor `unit-rec`;
* the family of vectors, declared by its two equations,

  `vec : Π (A : U0) (n : num). U0`,
  `vec A zero ⟶ unit`,
  `vec A (succ n) ⟶ Σ A (vec A n)`;

* the dependent eliminator of vectors, whose motive is indexed by the length and the vector,

  `vec-elim : Π (A : U0) (P : Π (n : num). vec A n → U0) (pn : P zero tt)
     (pc : Π (n : num) (a : A) (v : vec A n). P n v → P (succ n) (pair a v))
     (n : num) (v : vec A n). P n v`,

  declared by structural recursion on the length,

  `vec-elim A P pn pc zero v ⟶ unit-rec (λ w. P zero w) pn v`,
  `vec-elim A P pn pc (succ n) v ⟶ pc n (fst v) (snd v) (vec-elim A P pn pc n (snd v))`;

* addition by recursion on its first argument, `add zero m ⟶ m`,
  `add (succ n) m ⟶ succ (add n m)`;
* the empty type `void`, with no constructor, and its recursor `void-rec`, which has no case and
  no equation;
* the order on the numbers, declared by two structural recursions,

  `below zero i ⟶ void`, `below (succ n) i ⟶ below-step (below n) i`,
  `below-step h zero ⟶ unit`, `below-step h (succ i) ⟶ h i`,

  so that `below (succ n) zero ≡ unit` and `below (succ n) (succ i) ≡ below n i`, and the finite
  type is `fin n = Σ (i : num). below n i`;
* the based eliminator of identity types `id-elim`, for identity types of the lowest universe,
  with its equation at reflexivity.

The constructors of vectors are `tt : vec A zero` and `pair a v : vec A (succ n)`. The family is
indexed by computation on its index (a recursive family): the normalization model interprets
`vec A n` by the cases it already has, the unit type at `zero` and a dependent pair type at a
successor. The successor equation of the eliminator is typed by eta for pairs, which the typed
equality has; the zero equation needs the unit type's recursor, since the unit type has no eta.

Two properties separate this family from an inductive family with constructors of its own, and
both are proved as controls: the type former is not injective at length zero
(`vec A zero ≡ vec B zero` for all `A` and `B`), and at a successor length the eliminator unfolds on
every vector, a variable included.

Every hypothesis of the normalization model holds: the declared constants are semantic, the
root computations have the required shape, and every equation preserves typing. So injectivity,
discrimination, preservation and soundness of the conversion algorithm hold for this
presentation without hypotheses. The declarations are stated at every generic equality with the
laws of the model (`constantsAt`), so they hold for the algorithmic equality as well; completeness
of the conversion algorithm and decided equality follow in `TowerVectorsConversion`.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open Mettapedia.TypeTheory.UniverseLevel
open TelescopeAbstraction (closeType applyClosed)
open TowerNumbersModel (num zero succ numRec ctors u mem_zero mem_succ)

namespace TowerVectorsModel

/-! ## Names -/

/-- The unit type. -/
def unit : DeclName := .mkSimple "unit"
/-- Its constructor. -/
def tt : DeclName := .mkSimple "tt"
/-- Its recursor. -/
def unitRec : DeclName := .mkSimple "unit-rec"
/-- The family of vectors. -/
def vec : DeclName := .mkSimple "vec"
/-- The dependent eliminator of vectors. -/
def vecElim : DeclName := .mkSimple "vec-elim"
/-- Addition, by recursion on its first argument. -/
def add : DeclName := .mkSimple "add"
/-- The empty type. -/
def void : DeclName := .mkSimple "void"
/-- Its recursor, with no case. -/
def voidRec : DeclName := .mkSimple "void-rec"
/-- The step of the order: `below-step h zero = unit`, `below-step h (succ i) = h i`. -/
def belowStep : DeclName := .mkSimple "below-step"
/-- The order on numbers: `below n i` is inhabited exactly when `i < n`. -/
def below : DeclName := .mkSimple "below"
/-- The based eliminator of identity types. -/
def idElim : DeclName := .mkSimple "id-elim"

/-- The constructors of the unit type. -/
def unitCtors : List (DeclName × List (Field Tower.Head)) := [(tt, [])]

theorem mem_tt : ((tt, []) : DeclName × List (Field Tower.Head)) ∈ unitCtors :=
  List.mem_cons_self ..

/-! ## Terms -/

/-- The small universe. -/
abbrev U0 {n : Nat} : Tm Tower.Head n := .head u
abbrev numC {n : Nat} : Tm Tower.Head n := .const num
abbrev zeroC {n : Nat} : Tm Tower.Head n := .const zero
abbrev succC {n : Nat} (t : Tm Tower.Head n) : Tm Tower.Head n := .app (.const succ) t
abbrev unitC {n : Nat} : Tm Tower.Head n := .const unit
abbrev ttC {n : Nat} : Tm Tower.Head n := .const tt
abbrev vecC {n : Nat} (A k : Tm Tower.Head n) : Tm Tower.Head n := .app (.app (.const vec) A) k
abbrev addC {n : Nat} (a b : Tm Tower.Head n) : Tm Tower.Head n := .app (.app (.const add) a) b
abbrev unitRecC {n : Nat} (P d t : Tm Tower.Head n) : Tm Tower.Head n :=
  .app (.app (.app (.const unitRec) P) d) t
abbrev vecElimC {n : Nat} (A P pn pc k v : Tm Tower.Head n) : Tm Tower.Head n :=
  .app (.app (.app (.app (.app (.app (.const vecElim) A) P) pn) pc) k) v
abbrev voidC {n : Nat} : Tm Tower.Head n := .const void
abbrev voidRecC {n : Nat} (P t : Tm Tower.Head n) : Tm Tower.Head n := .app (.app (.const voidRec) P) t
abbrev belowStepC {n : Nat} (h i : Tm Tower.Head n) : Tm Tower.Head n :=
  .app (.app (.const belowStep) h) i
abbrev belowC {n : Nat} (k i : Tm Tower.Head n) : Tm Tower.Head n := .app (.app (.const below) k) i
/-- The finite type `fin k = Σ (i : num). below k i`. -/
abbrev finC {n : Nat} (k : Tm Tower.Head n) : Tm Tower.Head n :=
  .sigma numC (belowC (Presentation.rename wk k) (.var 0))

/-! ## The declarations by recursion -/

/-- The telescope of `vec`: a small type, then a number. -/
def vecEntries : (i : Nat) → Tm Tower.Head i
  | 0 => U0
  | _ + 1 => numC

/-- `vec` is a small type. -/
def vecResult : Tm Tower.Head (1 + 1 + 0) := U0

/-- The right-hand sides of `vec`, the recursive call abstracted: `unit` at zero, and
`Σ A h` at a successor, where `h` stands for `vec A n`. -/
def vecBody : (k : DeclName) → (fields : List (Field Tower.Head)) →
    Tm Tower.Head (1 + fields.length + 0 + (recPositions fields).length)
  | _, [] => unitC
  | _, [.recursive] => (.sigma (.var 2) (.var 1) : Tm Tower.Head 3)
  | _, _ => unitC

/-- The telescope of the eliminator: `A`, `P`, `pn`, `pc`, the length `n`, the vector `v`. -/
def elimEntries : (i : Nat) → Tm Tower.Head i
  | 0 => U0
  | 1 => .pi numC (.pi (vecC (.var 1) (.var 0)) U0)
  | 2 => .app (.app (.var 0) zeroC) ttC
  | 3 => .pi numC (.pi (.var 3) (.pi (vecC (.var 4) (.var 1))
      (.pi (.app (.app (.var 4) (.var 2)) (.var 0))
        (.app (.app (.var 5) (succC (.var 3))) (.pair (.var 2) (.var 1))))))
  | 4 => numC
  | 5 => vecC (.var 4) (.var 0)
  | _ => numC

/-- The result type `P n v`. -/
def elimResult : Tm Tower.Head (4 + 1 + 1) := .app (.app (.var 4) (.var 1)) (.var 0)

/-- At `zero`: `unit-rec (λ w. P zero w) pn v`, over `A P pn pc v`. -/
def elimZero : Tm Tower.Head 5 :=
  unitRecC (.lam (.app (.app (.var 4) zeroC) (.var 0))) (.var 2) (.var 0)

/-- At `succ n`: `pc n (fst v) (snd v) (h (snd v))`, over `A P pn pc n v h`, where `h` stands
for the recursive call `vec-elim A P pn pc n`. -/
def elimSucc : Tm Tower.Head 7 :=
  .app (.app (.app (.app (.var 3) (.var 2)) (.fst (.var 1))) (.snd (.var 1)))
    (.app (.var 0) (.snd (.var 1)))

/-- The right-hand sides of the eliminator, the recursive call abstracted. -/
def elimBody : (k : DeclName) → (fields : List (Field Tower.Head)) →
    Tm Tower.Head (4 + fields.length + 1 + (recPositions fields).length)
  | _, [] => elimZero
  | _, [.recursive] => elimSucc
  | _, _ => unitC

/-- The telescope of addition: the scrutinee, then the other summand. -/
def addEntries : (i : Nat) → Tm Tower.Head i := fun _ => numC

/-- The right-hand sides of addition: `m` at zero, `succ (h m)` at a successor. -/
def addBody : (k : DeclName) → (fields : List (Field Tower.Head)) →
    Tm Tower.Head (0 + fields.length + 1 + (recPositions fields).length)
  | _, [] => (.var 0 : Tm Tower.Head 1)
  | _, [.recursive] => (succC (.app (.var 0) (.var 1)) : Tm Tower.Head 3)
  | _, _ => numC

/-- The telescope of `below-step`: a family of small types over the numbers, then the scrutinee. -/
def belowStepEntries : (i : Nat) → Tm Tower.Head i
  | 0 => .pi numC U0
  | _ + 1 => numC

/-- The right-hand sides of `below-step`: `unit` at zero, `h i` at `succ i`. -/
def belowStepBody : (k : DeclName) → (fields : List (Field Tower.Head)) →
    Tm Tower.Head (1 + fields.length + 0 + (recPositions fields).length)
  | _, [] => unitC
  | _, [.recursive] => (.app (.var 2) (.var 1) : Tm Tower.Head 3)
  | _, _ => unitC

/-- The telescope of `below`: the scrutinee, then the other number. -/
def belowEntries : (i : Nat) → Tm Tower.Head i := fun _ => numC

/-- The right-hand sides of `below`: `void` at zero, `below-step h i` at a successor, where `h`
stands for the recursive call `below n`. -/
def belowBody : (k : DeclName) → (fields : List (Field Tower.Head)) →
    Tm Tower.Head (0 + fields.length + 1 + (recPositions fields).length)
  | _, [] => voidC
  | _, [.recursive] => (belowStepC (.var 0) (.var 1) : Tm Tower.Head 3)
  | _, _ => voidC

/-- The declared type of `below-step`. -/
def belowStepType : Tm Tower.Head 0 := closeType (ofEntries belowStepEntries (1 + 1 + 0)) U0
/-- The declared type of `below`. -/
def belowType : Tm Tower.Head 0 := closeType (ofEntries belowEntries (0 + 1 + 1)) U0

theorem belowStepType_eq : belowStepType = .pi (.pi numC U0) (.pi numC U0) := rfl
theorem belowType_eq : belowType = .pi numC (.pi numC U0) := rfl

/-- The declared type of `vec`. -/
def vecType : Tm Tower.Head 0 := closeType (ofEntries vecEntries (1 + 1 + 0)) vecResult
/-- The declared type of the eliminator. -/
def elimType : Tm Tower.Head 0 := closeType (ofEntries elimEntries (4 + 1 + 1)) elimResult
/-- The declared type of addition. -/
def addType : Tm Tower.Head 0 := closeType (ofEntries addEntries (0 + 1 + 1)) numC

theorem vecType_eq : vecType = .pi U0 (.pi numC U0) := rfl
theorem addType_eq : addType = .pi numC (.pi numC numC) := rfl

/-- The motives over `A`: `Π (n : num). vec A n → U0`. -/
def vecMotive {n : Nat} (A : Tm Tower.Head n) : Tm Tower.Head n :=
  .pi numC (.pi (vecC (Presentation.rename wk A) (.var 0)) U0)

/-- The type of the method for `pair`, over `A` and the motive `P`. -/
def vecMethod {n : Nat} (A P : Tm Tower.Head n) : Tm Tower.Head n :=
  .pi numC (.pi (Presentation.rename wk A)
    (.pi (vecC (Presentation.rename wk (Presentation.rename wk A)) (.var 1))
      (.pi (.app (.app (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk P)))
          (.var 2)) (.var 0))
        (.app (.app (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk
          (Presentation.rename wk P)))) (succC (.var 3))) (.pair (.var 2) (.var 1))))))

/-- The type of `unit-rec`. -/
theorem unitRecType_eq (lv : LevelExpr Nat) : recType unit (.sort lv) unitCtors =
    .pi (.pi unitC (.head (.sort lv))) (.pi (.app (.var 0) ttC) (.pi unitC (.app (.var 2) (.var 0)))) :=
  rfl

/-! ## Stages -/

/-- The unit type alone. -/
def unitStage₁ : Rules Tower.Head :=
  { Tower.rules with constantType := fun name => if name = unit then some (.head u) else none }

/-- The unit type and its constructor. -/
def unitStage₂ : Rules Tower.Head :=
  { Tower.rules with
    constantType := fun name =>
      if name = unit then some (.head u) else if name = tt then some (ctorType unit []) else none }

/-- The empty type alone. -/
def voidStage : Rules Tower.Head :=
  { Tower.rules with constantType := fun name => if name = void then some (.head u) else none }

/-- The numbers, the unit type with their constructors, and the empty type: the stage of `vec`. -/
def baseStage : Rules Tower.Head :=
  { Tower.rules with
    constantType := fun name =>
      if name = unit then some (.head u) else if name = tt then some (ctorType unit [])
      else if name = void then some (.head u)
      else TowerNumbersModel.rules₂.constantType name }

/-- With `below-step`: the stage of `below`. -/
def belowStage : Rules Tower.Head :=
  { Tower.rules with
    constantType := fun name =>
      if name = belowStep then some belowStepType else baseStage.constantType name }

/-- The equations of `vec`. -/
def vecComputation : RootComputation Tower.Head := recursionComputation vec ctors vecEntries 1 0 vecBody

variable (lv : LevelExpr Nat)

/-- With `vec`, its equations, and `unit-rec`: the stage of the eliminator. -/
def elimStage : Rules Tower.Head :=
  { Tower.rules with
    constantType := fun name =>
      if name = vec then some vecType
      else if name = unitRec then some (recType unit (.sort lv) unitCtors)
      else baseStage.constantType name
    computation := vecComputation }

/-- The declared types of the package. -/
def constantType : DeclName → Option (Tm Tower.Head 0) := fun name =>
  if name = add then some addType
  else if name = vecElim then some elimType
  else if name = numRec then some (recType num (.sort lv) ctors)
  else if name = voidRec then some (recType void (.sort lv) [])
  else if name = below then some belowType
  else if name = belowStep then some belowStepType
  else if name = idElim then some (Normalization.elimType u (.sort lv))
  else (elimStage lv).constantType name

/-- The computations: the recursors with constructors, the equations of the five definitions, and
the identity eliminator at reflexivity. The empty type's recursor has no equation. -/
def computations : List (DeclName × RootComputation Tower.Head) :=
  [(numRec, iotaComputation numRec ctors),
   (unitRec, iotaComputation unitRec unitCtors),
   (vec, vecComputation),
   (vecElim, recursionComputation vecElim ctors elimEntries 4 1 elimBody),
   (add, recursionComputation add ctors addEntries 0 1 addBody),
   (belowStep, recursionComputation belowStep ctors belowStepEntries 1 0 belowStepBody),
   (below, recursionComputation below ctors belowEntries 0 1 belowBody),
   (idElim, TowerEliminatorModel.computation idElim)]

/-- **The package**: the tower with numbers, the unit type and the empty type, vectors with their
eliminator, addition, the order on the numbers, and the identity eliminator; the recursors and
the identity eliminator's motives land in level `lv`. -/
def rules : Rules Tower.Head :=
  { Tower.rules with
    constantType := constantType lv
    computation := RootComputation.unionAll computations }

/-! ## Roles -/

/-- The roles of the declared constants. -/
def roles : Roles Tower.Head := fun name =>
  if name = unit then .inductive unitCtors
  else if name = tt then .constructor 0
  else if name = unitRec then .computes 3 (.split 2 .constructor fun _ => .leaf)
  else if name = vec then .computes 2 (.split 1 .constructor fun _ => .leaf)
  else if name = vecElim then .computes 6 (.split 4 .constructor fun _ => .leaf)
  else if name = add then .computes 2 (.split 0 .constructor fun _ => .leaf)
  else if name = void then .inductive []
  else if name = voidRec then .computes 2 (.split 1 .constructor fun _ => .leaf)
  else if name = belowStep then .computes 2 (.split 1 .constructor fun _ => .leaf)
  else if name = below then .computes 2 (.split 0 .constructor fun _ => .leaf)
  else if name = idElim then .computes 6 (.split 5 .constructor fun _ => .leaf)
  else TowerNumbersModel.roles name

theorem roles_num : roles num = .inductive ctors := rfl
theorem roles_zero : roles zero = .constructor 0 := rfl
theorem roles_succ : roles succ = .constructor 1 := rfl
theorem roles_numRec : roles numRec = .computes 4 (.split 3 .constructor fun _ => .leaf) := rfl
theorem roles_unit : roles unit = .inductive unitCtors := rfl
theorem roles_tt : roles tt = .constructor 0 := rfl
theorem roles_unitRec : roles unitRec =
    .computes (unitCtors.length + 2) (.split (unitCtors.length + 1) .constructor fun _ => .leaf) := rfl
theorem roles_vec : roles vec = .computes (1 + 1 + 0) (.split 1 .constructor fun _ => .leaf) := rfl
theorem roles_vecElim : roles vecElim = .computes (4 + 1 + 1) (.split 4 .constructor fun _ => .leaf) :=
  rfl
theorem roles_add : roles add = .computes (0 + 1 + 1) (.split 0 .constructor fun _ => .leaf) := rfl
theorem roles_void : roles void = .inductive [] := rfl
theorem roles_voidRec : roles voidRec =
    .computes (([] : List (DeclName × List (Field Tower.Head))).length + 2)
      (.split (([] : List (DeclName × List (Field Tower.Head))).length + 1) .constructor
        fun _ => .leaf) := rfl
theorem roles_belowStep : roles belowStep =
    .computes (1 + 1 + 0) (.split 1 .constructor fun _ => .leaf) := rfl
theorem roles_below : roles below = .computes (0 + 1 + 1) (.split 0 .constructor fun _ => .leaf) := rfl
theorem roles_idElim : roles idElim = .computes 6 (.split 5 .constructor fun _ => .leaf) := rfl

/-- The inductive types are `num`, `unit` and `void`. -/
theorem roles_inductive {T : DeclName} {cs : List (DeclName × List (Field Tower.Head))}
    (role : roles T = .inductive cs) :
    (T = num ∧ cs = ctors) ∨ (T = unit ∧ cs = unitCtors) ∨ (T = void ∧ cs = []) := by
  unfold roles at role
  split at role
  · rename_i h
    exact .inr (.inl ⟨h, (Role.inductive.inj role).symm⟩)
  split at role
  · cases role
  split at role
  · cases role
  split at role
  · cases role
  split at role
  · cases role
  split at role
  · cases role
  split at role
  · rename_i h
    exact .inr (.inr ⟨h, (Role.inductive.inj role).symm⟩)
  split at role
  · cases role
  split at role
  · cases role
  split at role
  · cases role
  split at role
  · cases role
  exact .inl (TowerNumbersModel.roles_inductive role)

theorem constructorsDeclared : ConstructorsDeclared roles where
  arity := by
    intro T cs k fields role mem
    rcases roles_inductive role with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
      rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact roles_zero
      · exact roles_succ
    · simp only [unitCtors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
      obtain ⟨rfl, rfl⟩ := mem
      exact roles_tt
    · exact absurd mem List.not_mem_nil
  distinct := by
    intro T cs role
    rcases roles_inductive role with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · decide
    · decide
    · decide

/-! ## The shape of the computation -/

theorem mem_numRec : (numRec, iotaComputation numRec ctors) ∈ computations :=
  List.mem_cons_self ..
theorem mem_unitRec : (unitRec, iotaComputation unitRec unitCtors) ∈ computations :=
  List.mem_cons_of_mem _ (List.mem_cons_self ..)
theorem mem_vec : (vec, vecComputation) ∈ computations :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
theorem mem_vecElim :
    (vecElim, recursionComputation vecElim ctors elimEntries 4 1 elimBody) ∈ computations :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
theorem mem_add : (add, recursionComputation add ctors addEntries 0 1 addBody) ∈ computations :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
theorem mem_belowStep :
    (belowStep, recursionComputation belowStep ctors belowStepEntries 1 0 belowStepBody) ∈ computations :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))
theorem mem_below :
    (below, recursionComputation below ctors belowEntries 0 1 belowBody) ∈ computations :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))
theorem mem_idElim : (idElim, TowerEliminatorModel.computation idElim) ∈ computations :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))

theorem computations_spine : ∀ entry ∈ computations, SpineShaped roles entry.2 := by
  intro entry mem
  simp only [computations, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun _ _ _ step => IotaStep.spine (T := num) roles_num roles_numRec constructorsDeclared step
  · exact fun _ _ _ step => IotaStep.spine (T := unit) roles_unit roles_unitRec constructorsDeclared
      step
  · exact fun _ _ _ step => RecursionStep.spine roles_num constructorsDeclared roles_vec step
  · exact fun _ _ _ step => RecursionStep.spine roles_num constructorsDeclared roles_vecElim step
  · exact fun _ _ _ step => RecursionStep.spine roles_num constructorsDeclared roles_add step
  · exact fun _ _ _ step => RecursionStep.spine roles_num constructorsDeclared roles_belowStep step
  · exact fun _ _ _ step => RecursionStep.spine roles_num constructorsDeclared roles_below step
  · intro n t r step
    obtain ⟨a₀, a₁, a₂, a₃, a₄, a₅, e₁, _⟩ := step
    subst e₁
    exact ⟨idElim, 6, .split 5 .constructor fun _ => .leaf, [a₀, a₁, a₂, a₃, a₄, .refl a₅],
      roles_idElim, rfl, rfl, InspectTree.accepts_single.mpr ⟨_, rfl, .inl ⟨a₅, rfl⟩⟩⟩

theorem computations_headed : ∀ entry ∈ computations, HeadedBy entry.1 entry.2 := by
  intro entry mem
  simp only [computations, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact iotaComputation_headed
  · exact iotaComputation_headed
  · exact recursionComputation_headed
  · exact recursionComputation_headed
  · exact recursionComputation_headed
  · exact recursionComputation_headed
  · exact recursionComputation_headed
  · intro n t r step
    obtain ⟨a₀, a₁, a₂, a₃, a₄, a₅, e₁, _⟩ := step
    exact ⟨_, e₁⟩

theorem computations_deterministic : ∀ entry ∈ computations, Deterministic entry.2 := by
  intro entry mem
  simp only [computations, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun _ _ _ _ step step' =>
      IotaStep.deterministic (T := num) roles_num constructorsDeclared step step'
  · exact fun _ _ _ _ step step' =>
      IotaStep.deterministic (T := unit) roles_unit constructorsDeclared step step'
  · exact fun _ _ _ _ step step' => RecursionStep.deterministic roles_num constructorsDeclared step step'
  · exact fun _ _ _ _ step step' => RecursionStep.deterministic roles_num constructorsDeclared step step'
  · exact fun _ _ _ _ step step' => RecursionStep.deterministic roles_num constructorsDeclared step step'
  · exact fun _ _ _ _ step step' => RecursionStep.deterministic roles_num constructorsDeclared step step'
  · exact fun _ _ _ _ step step' => RecursionStep.deterministic roles_num constructorsDeclared step step'
  · intro n t r r' first second
    obtain ⟨a₀, a₁, a₂, a₃, a₄, a₅, e₁, e₂⟩ := first
    obtain ⟨b₀, b₁, b₂, b₃, b₄, b₅, e₃, e₄⟩ := second
    subst e₂ e₄
    rw [e₁] at e₃
    obtain ⟨_, args⟩ := appSpine_const_injective e₃
    simp only [List.cons.injEq] at args
    exact args.2.2.2.1.symm

theorem computations_distinct : (computations.map Prod.fst).Nodup := by
  decide

theorem shape : RootShape (rules lv) roles where
  spine := fun step => RootComputation.unionAll_spine computations_spine step
  deterministic := fun step step' =>
    (RootComputation.unionAll_deterministic computations_distinct computations_headed
      computations_deterministic step step').symm

/-- The tower's level model, for this rule package. -/
def levels (valuation : Nat → Nat) : LevelModel (rules lv) ℕ where
  level := (TowerModel.levels valuation).level
  successor := (TowerModel.levels valuation).successor
  universe_typing := (TowerModel.levels valuation).universe_typing
  ground_typing := (TowerModel.levels valuation).ground_typing
  cumulative_universe := (TowerModel.levels valuation).cumulative_universe
  headEq_level := (TowerModel.levels valuation).headEq_level
  join_level := (TowerModel.levels valuation).join_level
  join_exists := (TowerModel.levels valuation).join_exists
  join_upper := (TowerModel.levels valuation).join_upper
  cumulative_refl := (TowerModel.levels valuation).cumulative_refl
  headEq_symm := (TowerModel.levels valuation).headEq_symm
  headEq_trans := (TowerModel.levels valuation).headEq_trans
  universe_decided := (TowerModel.levels valuation).universe_decided

/-- The normalization setting, at a generic equality. -/
def settingAt (valuation : Nat → Nat) (E : GenericEquality Tower.Head) : Setting Tower.Head ℕ where
  R := rules lv
  roles := roles
  E := E
  levels := levels lv valuation
  shape := shape lv
  constructors := constructorsDeclared

/-- The normalization setting, at the typed equality. -/
def setting (valuation : Nat → Nat) : Setting Tower.Head ℕ :=
  settingAt lv valuation (declarative (rules lv))

theorem laws (valuation : Nat → Nat) :
    (setting lv valuation).E.Laws (setting lv valuation).R (setting lv valuation).roles :=
  declarative_laws roles (levels lv valuation)

/-! ## Stage inclusions -/

theorem numbers₁_to_numbers₂ {name : DeclName} {type : Tm Tower.Head 0}
    (declared : TowerNumbersModel.rules₁.constantType name = some type) :
    TowerNumbersModel.rules₂.constantType name = some type := by
  change (if name = num then some (.head u) else none) = some type at declared
  split at declared
  · rename_i h
    subst h
    exact declared
  · cases declared

theorem numbers_to_base {name : DeclName} {type : Tm Tower.Head 0}
    (declared : TowerNumbersModel.rules₂.constantType name = some type) :
    baseStage.constantType name = some type := by
  show (if name = unit then some (.head u) else if name = tt then some (ctorType unit [])
    else if name = void then some (.head u)
    else TowerNumbersModel.rules₂.constantType name) = _
  by_cases h₁ : name = unit
  · subst h₁
    have none : TowerNumbersModel.rules₂.constantType unit = none := rfl
    rw [none] at declared
    cases declared
  · by_cases h₂ : name = tt
    · subst h₂
      have none : TowerNumbersModel.rules₂.constantType tt = none := rfl
      rw [none] at declared
      cases declared
    · by_cases h₃ : name = void
      · subst h₃
        have none : TowerNumbersModel.rules₂.constantType void = none := rfl
        rw [none] at declared
        cases declared
      · rw [if_neg h₁, if_neg h₂, if_neg h₃]
        exact declared

theorem unit₁_to_unit₂ {name : DeclName} {type : Tm Tower.Head 0}
    (declared : unitStage₁.constantType name = some type) :
    unitStage₂.constantType name = some type := by
  change (if name = unit then some (.head u) else none) = some type at declared
  split at declared
  · rename_i h
    subst h
    exact declared
  · cases declared

theorem unit₂_to_base {name : DeclName} {type : Tm Tower.Head 0}
    (declared : unitStage₂.constantType name = some type) :
    baseStage.constantType name = some type := by
  change (if name = unit then some (.head u) else if name = tt then some (ctorType unit [])
    else none) = some type at declared
  show (if name = unit then some (.head u) else if name = tt then some (ctorType unit [])
    else if name = void then some (.head u)
    else TowerNumbersModel.rules₂.constantType name) = _
  split at declared
  · rename_i h
    rw [if_pos h]
    exact declared
  · rename_i h₁
    split at declared
    · rename_i h₂
      rw [if_neg h₁, if_pos h₂]
      exact declared
    · cases declared

theorem void_to_base {name : DeclName} {type : Tm Tower.Head 0}
    (declared : voidStage.constantType name = some type) :
    baseStage.constantType name = some type := by
  change (if name = void then some (.head u) else none) = some type at declared
  split at declared
  · rename_i h
    subst h
    exact declared
  · cases declared

theorem base_to_below {name : DeclName} {type : Tm Tower.Head 0}
    (declared : baseStage.constantType name = some type) :
    belowStage.constantType name = some type := by
  show (if name = belowStep then some belowStepType else baseStage.constantType name) = _
  by_cases h : name = belowStep
  · subst h
    have none : baseStage.constantType belowStep = none := rfl
    rw [none] at declared
    cases declared
  · rw [if_neg h]
    exact declared

theorem base_to_elim {name : DeclName} {type : Tm Tower.Head 0}
    (declared : baseStage.constantType name = some type) :
    (elimStage lv).constantType name = some type := by
  show (if name = vec then some vecType
    else if name = unitRec then some (recType unit (.sort lv) unitCtors)
    else baseStage.constantType name) = _
  by_cases h₁ : name = vec
  · subst h₁
    have none : baseStage.constantType vec = none := rfl
    rw [none] at declared
    cases declared
  · by_cases h₂ : name = unitRec
    · subst h₂
      have none : baseStage.constantType unitRec = none := rfl
      rw [none] at declared
      cases declared
    · rw [if_neg h₁, if_neg h₂]
      exact declared

theorem elim_to_rules {name : DeclName} {type : Tm Tower.Head 0}
    (declared : (elimStage lv).constantType name = some type) :
    (rules lv).constantType name = some type := by
  show (if name = add then some addType
    else if name = vecElim then some elimType
    else if name = numRec then some (recType num (.sort lv) ctors)
    else if name = voidRec then some (recType void (.sort lv) [])
    else if name = below then some belowType
    else if name = belowStep then some belowStepType
    else if name = idElim then some (Normalization.elimType u (.sort lv))
    else (elimStage lv).constantType name) = _
  by_cases h₁ : name = add
  · subst h₁
    have none : (elimStage lv).constantType add = none := rfl
    rw [none] at declared
    cases declared
  by_cases h₂ : name = vecElim
  · subst h₂
    have none : (elimStage lv).constantType vecElim = none := rfl
    rw [none] at declared
    cases declared
  by_cases h₃ : name = numRec
  · subst h₃
    have none : (elimStage lv).constantType numRec = none := rfl
    rw [none] at declared
    cases declared
  by_cases h₄ : name = voidRec
  · subst h₄
    have none : (elimStage lv).constantType voidRec = none := rfl
    rw [none] at declared
    cases declared
  by_cases h₅ : name = below
  · subst h₅
    have none : (elimStage lv).constantType below = none := rfl
    rw [none] at declared
    cases declared
  by_cases h₆ : name = belowStep
  · subst h₆
    have none : (elimStage lv).constantType belowStep = none := rfl
    rw [none] at declared
    cases declared
  by_cases h₇ : name = idElim
  · subst h₇
    have none : (elimStage lv).constantType idElim = none := rfl
    rw [none] at declared
    cases declared
  rw [if_neg h₁, if_neg h₂, if_neg h₃, if_neg h₄, if_neg h₅, if_neg h₆, if_neg h₇]
  exact declared

theorem below_to_rules {name : DeclName} {type : Tm Tower.Head 0}
    (declared : belowStage.constantType name = some type) :
    (rules lv).constantType name = some type := by
  change (if name = belowStep then some belowStepType else baseStage.constantType name) = some type
    at declared
  split at declared
  · rename_i h
    subst h
    exact declared
  · exact elim_to_rules lv (base_to_elim lv declared)

theorem sub_elim : RulesSub (elimStage lv) (rules lv) :=
  ⟨id, id, id, id, id, fun declared => elim_to_rules lv declared,
    fun step => RootComputation.step_unionAll mem_vec step⟩
theorem sub_base : RulesSub baseStage (rules lv) :=
  ⟨id, id, id, id, id, fun declared => elim_to_rules lv (base_to_elim lv declared),
    fun step => nomatch step⟩
theorem sub_numbers₂ : RulesSub TowerNumbersModel.rules₂ (rules lv) :=
  ⟨id, id, id, id, id, fun declared =>
    elim_to_rules lv (base_to_elim lv (numbers_to_base declared)), fun step => nomatch step⟩
theorem sub_numbers₁ : RulesSub TowerNumbersModel.rules₁ (rules lv) :=
  ⟨id, id, id, id, id, fun declared => elim_to_rules lv (base_to_elim lv (numbers_to_base
    (numbers₁_to_numbers₂ declared))), fun step => nomatch step⟩
theorem sub_unit₂ : RulesSub unitStage₂ (rules lv) :=
  ⟨id, id, id, id, id, fun declared => elim_to_rules lv (base_to_elim lv (unit₂_to_base declared)),
    fun step => nomatch step⟩
theorem sub_unit₁ : RulesSub unitStage₁ (rules lv) :=
  ⟨id, id, id, id, id, fun declared =>
    elim_to_rules lv (base_to_elim lv (unit₂_to_base (unit₁_to_unit₂ declared))),
    fun step => nomatch step⟩
theorem sub_void : RulesSub voidStage (rules lv) :=
  ⟨id, id, id, id, id, fun declared => elim_to_rules lv (base_to_elim lv (void_to_base declared)),
    fun step => nomatch step⟩
theorem sub_below : RulesSub belowStage (rules lv) :=
  ⟨id, id, id, id, id, fun declared => below_to_rules lv declared, fun step => nomatch step⟩

/-! ## Typings in packages with the tower's universes -/

/-- A rule package with the tower's universes, joins and cumulativity. -/
structure TowerLike (R : Rules Tower.Head) : Prop where
  headTyping : ∀ l, R.headTyping (.sort l) (.sort (.succ l))
  isUniverse : ∀ l, R.isUniverse (.sort l)
  join : ∀ l r, R.join (.sort l) (.sort r) (.sort (.max l r))
  cumulative : ∀ l r, (∀ ν, LevelExpr.eval ν l ≤ LevelExpr.eval ν r) →
    R.cumulative (.sort l) (.sort r)

theorem towerLike_base : TowerLike baseStage :=
  ⟨LevelTower.HeadTyping.sort, LevelTower.IsUniverse.sort, LevelTower.Join.sorts, fun _ _ h => h⟩
theorem towerLike_unit₁ : TowerLike unitStage₁ :=
  ⟨LevelTower.HeadTyping.sort, LevelTower.IsUniverse.sort, LevelTower.Join.sorts, fun _ _ h => h⟩
theorem towerLike_unit₂ : TowerLike unitStage₂ :=
  ⟨LevelTower.HeadTyping.sort, LevelTower.IsUniverse.sort, LevelTower.Join.sorts, fun _ _ h => h⟩
theorem towerLike_numbers₂ : TowerLike TowerNumbersModel.rules₂ :=
  ⟨LevelTower.HeadTyping.sort, LevelTower.IsUniverse.sort, LevelTower.Join.sorts, fun _ _ h => h⟩
theorem towerLike_elim : TowerLike (elimStage lv) :=
  ⟨LevelTower.HeadTyping.sort, LevelTower.IsUniverse.sort, LevelTower.Join.sorts, fun _ _ h => h⟩
theorem towerLike_rules : TowerLike (rules lv) :=
  ⟨LevelTower.HeadTyping.sort, LevelTower.IsUniverse.sort, LevelTower.Join.sorts, fun _ _ h => h⟩
theorem towerLike_void : TowerLike voidStage :=
  ⟨LevelTower.HeadTyping.sort, LevelTower.IsUniverse.sort, LevelTower.Join.sorts, fun _ _ h => h⟩
theorem towerLike_below : TowerLike belowStage :=
  ⟨LevelTower.HeadTyping.sort, LevelTower.IsUniverse.sort, LevelTower.Join.sorts, fun _ _ h => h⟩

section TowerTyping

variable {R : Rules Tower.Head} (tw : TowerLike R) {n : Nat} {Γ : Ctx Tower.Head n}
include tw

theorem TowerLike.u0_typed : Typed R Γ U0 (.head (.sort (.succ (.const 0)))) :=
  .headType (tw.headTyping _)

/-- A constant declared as a small type is a small type. -/
theorem TowerLike.small {c : DeclName} (declared : R.constantType c = some (.head u)) :
    Typed R Γ (.const c) U0 :=
  .const declared (.headType (tw.headTyping _)) (tw.isUniverse _)

theorem TowerLike.collapse : R.cumulative (.sort (.max (.const 0) (.const 0))) (.sort (.const 0)) :=
  tw.cumulative _ _ fun ν => by simp [LevelExpr.eval]

/-- A dependent function type between small types is small. -/
theorem TowerLike.pi_small {A : Tm Tower.Head n} {B : Tm Tower.Head (n + 1)}
    (tA : Typed R Γ A U0) (tB : Typed R (.snoc Γ A) B U0) : Typed R Γ (.pi A B) U0 :=
  Derivable.cumul (.piForm tA (tw.isUniverse _) tB (tw.isUniverse _) (tw.join _ _)) tw.collapse

/-- A dependent pair type of small types is small. -/
theorem TowerLike.sigma_small {A : Tm Tower.Head n} {B : Tm Tower.Head (n + 1)}
    (tA : Typed R Γ A U0) (tB : Typed R (.snoc Γ A) B U0) : Typed R Γ (.sigma A B) U0 :=
  Derivable.cumul (.sigmaForm tA (tw.isUniverse _) tB (tw.isUniverse _) (tw.join _ _)) tw.collapse

/-- A small type is a type of every universe. -/
theorem TowerLike.lift {A : Tm Tower.Head n} (tA : Typed R Γ A U0) (l : LevelExpr Nat) :
    Typed R Γ A (.head (.sort l)) :=
  Derivable.cumul tA (tw.cumulative _ _ fun ν => by simp [LevelExpr.eval])

/-- The type of `unit-rec` is typed where the unit type and its constructor are declared. -/
theorem TowerLike.unitRecType_typed (dUnit : R.constantType unit = some (.head u))
    (dTt : R.constantType tt = some unitC) (lv : LevelExpr Nat) :
    ∃ w, R.isUniverse w ∧ Typed R .nil (recType unit (.sort lv) unitCtors) (.head w) := by
  have tUnit : ∀ {m : Nat} {Δ : Ctx Tower.Head m}, Typed R Δ unitC U0 := fun {_ _} => tw.small dUnit
  have tTt : ∀ {m : Nat} {Δ : Ctx Tower.Head m}, Typed R Δ ttC unitC :=
    fun {_ _} => .const dTt tUnit (tw.isUniverse _)
  have tM : Typed R .nil (.pi unitC (.head (.sort lv))) (.head (.sort (.max (.const 0) (.succ lv)))) :=
    .piForm tUnit (tw.isUniverse _) (.headType (tw.headTyping _)) (tw.isUniverse _) (tw.join _ _)
  have tP₁ : Typed R (.snoc .nil (.pi unitC (.head (.sort lv)))) (.var 0)
      (.pi unitC (.head (.sort lv))) := .var 0
  have tD : Typed R (.snoc .nil (.pi unitC (.head (.sort lv)))) (.app (.var 0) ttC)
      (.head (.sort lv)) := .appElim tP₁ tTt
  have tP₃ : Typed R (.snoc (.snoc (.snoc .nil (.pi unitC (.head (.sort lv))))
      (.app (.var 0) ttC)) unitC) (.var 2) (.pi unitC (.head (.sort lv))) := .var 2
  have tt₃ : Typed R (.snoc (.snoc (.snoc .nil (.pi unitC (.head (.sort lv))))
      (.app (.var 0) ttC)) unitC) (.var 0) unitC := .var 0
  have tBody : Typed R (.snoc (.snoc (.snoc .nil (.pi unitC (.head (.sort lv))))
      (.app (.var 0) ttC)) unitC) (.app (.var 2) (.var 0)) (.head (.sort lv)) :=
    .appElim tP₃ tt₃
  have t3 := Derivable.piForm tUnit (tw.isUniverse _) tBody (tw.isUniverse _) (tw.join _ _)
  have t2 := Derivable.piForm tD (tw.isUniverse _) t3 (tw.isUniverse _) (tw.join _ _)
  have t1 := Derivable.piForm tM (tw.isUniverse _) t2 (tw.isUniverse _) (tw.join _ _)
  exact ⟨_, tw.isUniverse _, t1⟩

end TowerTyping

/-! ## Packages declaring vectors -/

/-- A package with the tower's universes declaring the numbers, the unit type and `vec` with
its two equations. -/
structure VecDeclared (R : Rules Tower.Head) : Prop where
  tower : TowerLike R
  dNum : R.constantType num = some (.head u)
  dZero : R.constantType zero = some numC
  dSucc : R.constantType succ = some (.pi numC numC)
  dUnit : R.constantType unit = some (.head u)
  dTt : R.constantType tt = some unitC
  dVec : R.constantType vec = some (.pi U0 (.pi numC U0))
  vecZero : ∀ {n : Nat} (A : Tm Tower.Head n), R.computation.step (vecC A zeroC) unitC
  vecSucc : ∀ {n : Nat} (A k : Tm Tower.Head n),
    R.computation.step (vecC A (succC k)) (.sigma A (Presentation.rename wk (vecC A k)))

/-- The equation `vec A zero ⟶ unit`, as a step of the equations of `vec`. -/
theorem vecComputation_zero {n : Nat} (A : Tm Tower.Head n) :
    vecComputation.step (vecC A zeroC) unitC :=
  ⟨zero, [], consSub zeroC (consSub A fun i => Fin.elim0 i), [], mem_zero, rfl, rfl, rfl⟩

/-- The equation `vec A (succ k) ⟶ Σ A (vec A k)`. -/
theorem vecComputation_succ {n : Nat} (A k : Tm Tower.Head n) :
    vecComputation.step (vecC A (succC k)) (.sigma A (Presentation.rename wk (vecC A k))) :=
  ⟨succ, [.recursive], consSub (succC k) (consSub A fun i => Fin.elim0 i), [k], mem_succ, rfl, rfl,
    rfl⟩

theorem vecDeclared_elim : VecDeclared (elimStage lv) where
  tower := towerLike_elim lv
  dNum := rfl
  dZero := rfl
  dSucc := rfl
  dUnit := rfl
  dTt := rfl
  dVec := rfl
  vecZero := vecComputation_zero
  vecSucc := vecComputation_succ

theorem vecDeclared_rules : VecDeclared (rules lv) where
  tower := towerLike_rules lv
  dNum := rfl
  dZero := rfl
  dSucc := rfl
  dUnit := rfl
  dTt := rfl
  dVec := rfl
  vecZero := fun A => RootComputation.step_unionAll mem_vec (vecComputation_zero A)
  vecSucc := fun A k => RootComputation.step_unionAll mem_vec (vecComputation_succ A k)

namespace VecDeclared

variable {R : Rules Tower.Head} (D : VecDeclared R) {n : Nat} {Γ : Ctx Tower.Head n}
include D

theorem num_typed : Typed R Γ numC U0 := D.tower.small D.dNum
theorem unit_typed : Typed R Γ unitC U0 := D.tower.small D.dUnit
theorem zero_typed : Typed R Γ zeroC numC := .const D.dZero D.num_typed (D.tower.isUniverse _)
theorem tt_typed : Typed R Γ ttC unitC := .const D.dTt D.unit_typed (D.tower.isUniverse _)

theorem succ_typed {t : Tm Tower.Head n} (typed : Typed R Γ t numC) : Typed R Γ (succC t) numC :=
  .appElim (.const D.dSucc (D.tower.pi_small D.num_typed D.num_typed) (D.tower.isUniverse _)) typed

theorem vec_const_typed : Typed R Γ (.const vec) (.pi U0 (.pi numC U0)) :=
  .const D.dVec (.piForm D.tower.u0_typed (D.tower.isUniverse _)
    (.piForm D.num_typed (D.tower.isUniverse _) D.tower.u0_typed (D.tower.isUniverse _)
      (D.tower.join _ _)) (D.tower.isUniverse _) (D.tower.join _ _)) (D.tower.isUniverse _)

theorem vec_typed {A k : Tm Tower.Head n} (tA : Typed R Γ A U0) (tk : Typed R Γ k numC) :
    Typed R Γ (vecC A k) U0 :=
  .appElim (.appElim D.vec_const_typed tA) tk

/-- `vec A zero ≡ unit`. -/
theorem vec_zero {A : Tm Tower.Head n} (tA : Typed R Γ A U0) :
    Equal R Γ (vecC A zeroC) unitC U0 :=
  .root (D.vecZero A) (D.vec_typed tA D.zero_typed) D.unit_typed

/-- `vec A (succ k) ≡ Σ A (vec A k)`. -/
theorem vec_succ {A k : Tm Tower.Head n} (tA : Typed R Γ A U0) (tk : Typed R Γ k numC) :
    Equal R Γ (vecC A (succC k)) (.sigma A (Presentation.rename wk (vecC A k))) U0 :=
  .root (D.vecSucc A k) (D.vec_typed tA (D.succ_typed tk))
    (D.tower.sigma_small tA (D.vec_typed tA.weaken tk.weaken))

theorem vec_zero_eq {A : Tm Tower.Head n} (tA : Typed R Γ A U0) :
    TypeEq R Γ (vecC A zeroC) unitC :=
  ⟨u, D.tower.isUniverse _, D.vec_zero tA⟩

theorem vec_succ_eq {A k : Tm Tower.Head n} (tA : Typed R Γ A U0) (tk : Typed R Γ k numC) :
    TypeEq R Γ (vecC A (succC k)) (.sigma A (Presentation.rename wk (vecC A k))) :=
  ⟨u, D.tower.isUniverse _, D.vec_succ tA tk⟩

/-- **The empty vector**: `tt : vec A zero`. -/
theorem nil_typed {A : Tm Tower.Head n} (tA : Typed R Γ A U0) : Typed R Γ ttC (vecC A zeroC) :=
  Typed.convType D.tt_typed (D.vec_zero_eq tA).symm

/-- **The extended vector**: `pair a v : vec A (succ k)` for `a : A` and `v : vec A k`. -/
theorem cons_typed {A k a v : Tm Tower.Head n} (tA : Typed R Γ A U0) (tk : Typed R Γ k numC)
    (ta : Typed R Γ a A) (tv : Typed R Γ v (vecC A k)) :
    Typed R Γ (.pair a v) (vecC A (succC k)) := by
  have tSigma : Typed R Γ (.sigma A (Presentation.rename wk (vecC A k))) U0 :=
    D.tower.sigma_small tA (D.vec_typed tA.weaken tk.weaken)
  have tb : Typed R Γ v (inst0 a (Presentation.rename wk (vecC A k))) := by
    rw [inst0_rename_wk]
    exact tv
  exact Typed.convType (.pairIntro tSigma (D.tower.isUniverse _) ta tb) (D.vec_succ_eq tA tk).symm

/-- A vector of a successor length is a pair. -/
theorem vec_sigma {A k v : Tm Tower.Head n} (tA : Typed R Γ A U0) (tk : Typed R Γ k numC)
    (tv : Typed R Γ v (vecC A (succC k))) :
    Typed R Γ v (.sigma A (Presentation.rename wk (vecC A k))) :=
  Typed.convType tv (D.vec_succ_eq tA tk)

/-- The head of a vector of a successor length. -/
theorem fst_typed {A k v : Tm Tower.Head n} (tA : Typed R Γ A U0) (tk : Typed R Γ k numC)
    (tv : Typed R Γ v (vecC A (succC k))) : Typed R Γ (.fst v) A :=
  .fstElim (D.vec_sigma tA tk tv)

/-- The tail of a vector of a successor length. -/
theorem snd_typed {A k v : Tm Tower.Head n} (tA : Typed R Γ A U0) (tk : Typed R Γ k numC)
    (tv : Typed R Γ v (vecC A (succC k))) : Typed R Γ (.snd v) (vecC A k) := by
  have h := Derivable.sndElim (D.vec_sigma tA tk tv)
  rwa [inst0_rename_wk] at h

/-- **Eta at a successor length**: a vector is the pair of its head and tail. -/
theorem vec_eta {A k v : Tm Tower.Head n} (tA : Typed R Γ A U0) (tk : Typed R Γ k numC)
    (tv : Typed R Γ v (vecC A (succC k))) :
    Equal R Γ v (.pair (.fst v) (.snd v)) (vecC A (succC k)) := by
  have tS : Typed R Γ (.sigma A (Presentation.rename wk (vecC A k))) U0 :=
    D.tower.sigma_small tA (D.vec_typed tA.weaken tk.weaken)
  have tFst := D.fst_typed tA tk tv
  have tSnd : Typed R Γ (.snd v) (inst0 (.fst v) (Presentation.rename wk (vecC A k))) := by
    rw [inst0_rename_wk]
    exact D.snd_typed tA tk tv
  have tPair : Typed R Γ (.pair (.fst v) (.snd v)) (.sigma A (Presentation.rename wk (vecC A k))) :=
    .pairIntro tS (D.tower.isUniverse _) tFst tSnd
  have eFst : Equal R Γ (.fst v) (.fst (.pair (.fst v) (.snd v))) A :=
    .symm (.betaFst tS (D.tower.isUniverse _) tFst tSnd)
  have eSnd : Equal R Γ (.snd v) (.snd (.pair (.fst v) (.snd v)))
      (inst0 (.fst v) (Presentation.rename wk (vecC A k))) :=
    .symm (.betaSnd tS (D.tower.isUniverse _) tFst tSnd)
  exact Equal.convType (.etaSigma (D.vec_sigma tA tk tv) tPair eFst eSnd) (D.vec_succ_eq tA tk).symm

/-- `unit-rec Q d t : Q t`, where `unit-rec` is declared. -/
theorem unitRec_typed {lv : LevelExpr Nat}
    (dRec : R.constantType unitRec = some (recType unit (.sort lv) unitCtors))
    {Q d t : Tm Tower.Head n} (tQ : Typed R Γ Q (.pi unitC (.head (.sort lv))))
    (td : Typed R Γ d (.app Q ttC)) (tt' : Typed R Γ t unitC) :
    Typed R Γ (unitRecC Q d t) (.app Q t) := by
  obtain ⟨w, hw, typed⟩ := D.tower.unitRecType_typed D.dUnit D.dTt lv
  have tc : Typed R Γ (.const unitRec) (liftClosed (recType unit (.sort lv) unitCtors)) :=
    .const dRec typed hw
  have m₀ : SubstMor R .nil Γ fun i => Fin.elim0 i := fun i => Fin.elim0 i
  have mor : SubstMor R (recTele unit (.sort lv) unitCtors) Γ
      (consSub t (consSub d (consSub Q fun i => Fin.elim0 i))) :=
    SubstMor.cons (SubstMor.cons (SubstMor.cons m₀ tQ) td) tt'
  exact Typed.telescope_apply mor tc

/-! ### The declared type of the eliminator -/

/-- The telescope of the eliminator up to the method for `pair`. -/
abbrev ctxPc : Ctx Tower.Head 4 := ofEntries elimEntries 4

theorem entry1_typed : Typed R (.snoc .nil U0) (elimEntries 1)
    (.head (.sort (.max (.const 0) (.max (.const 0) (.succ (.const 0)))))) := by
  have tA : Typed R (.snoc (.snoc .nil U0) numC) (.var 1) U0 := .var 1
  have tk : Typed R (.snoc (.snoc .nil U0) numC) (.var 0) numC := .var 0
  have tInner := Derivable.piForm (D.vec_typed tA tk) (D.tower.isUniverse _) D.tower.u0_typed
    (D.tower.isUniverse _) (D.tower.join _ _)
  exact .piForm D.num_typed (D.tower.isUniverse _) tInner (D.tower.isUniverse _) (D.tower.join _ _)

theorem entry2_typed : Typed R (ofEntries elimEntries 2) (elimEntries 2) U0 := by
  have tP : Typed R (ofEntries elimEntries 2) (.var 0) (.pi numC (.pi (vecC (.var 2) (.var 0)) U0)) :=
    .var 0
  have tA : Typed R (ofEntries elimEntries 2) (.var 1) U0 := .var 1
  have tPz : Typed R (ofEntries elimEntries 2) (.app (.var 0) zeroC) (.pi (vecC (.var 1) zeroC) U0) :=
    .appElim tP D.zero_typed
  exact .appElim tPz (D.nil_typed tA)

theorem entry3_typed : Typed R (ofEntries elimEntries 3) (elimEntries 3) U0 := by
  -- the context `A P pn k a v ih`
  let Γk : Ctx Tower.Head 4 := .snoc (ofEntries elimEntries 3) numC
  let Γa : Ctx Tower.Head 5 := .snoc Γk (.var 3)
  let Γv : Ctx Tower.Head 6 := .snoc Γa (vecC (.var 4) (.var 1))
  let Γi : Ctx Tower.Head 7 := .snoc Γv (.app (.app (.var 4) (.var 2)) (.var 0))
  have tPi : Typed R Γi (.var 5) (.pi numC (.pi (vecC (.var 7) (.var 0)) U0)) := .var 5
  have tki : Typed R Γi (.var 3) numC := .var 3
  have tAi : Typed R Γi (.var 6) U0 := .var 6
  have tai : Typed R Γi (.var 2) (.var 6) := .var 2
  have tvi : Typed R Γi (.var 1) (vecC (.var 6) (.var 3)) := .var 1
  have tPs : Typed R Γi (.app (.var 5) (succC (.var 3))) (.pi (vecC (.var 6) (succC (.var 3))) U0) :=
    .appElim tPi (D.succ_typed tki)
  have tcod : Typed R Γi (.app (.app (.var 5) (succC (.var 3))) (.pair (.var 2) (.var 1))) U0 :=
    .appElim tPs (D.cons_typed tAi tki tai tvi)
  have tPv : Typed R Γv (.var 4) (.pi numC (.pi (vecC (.var 6) (.var 0)) U0)) := .var 4
  have tkv : Typed R Γv (.var 2) numC := .var 2
  have tvv : Typed R Γv (.var 0) (vecC (.var 5) (.var 2)) := .var 0
  have tih : Typed R Γv (.app (.app (.var 4) (.var 2)) (.var 0)) U0 := .appElim (.appElim tPv tkv) tvv
  have tva : Typed R Γa (vecC (.var 4) (.var 1)) U0 := D.vec_typed (.var 4) (.var 1)
  have tak : Typed R Γk (.var 3) U0 := .var 3
  exact D.tower.pi_small D.num_typed (D.tower.pi_small tak (D.tower.pi_small tva
    (D.tower.pi_small tih tcod)))

theorem entry5_typed : Typed R (ofEntries elimEntries 5) (elimEntries 5) U0 :=
  D.vec_typed (.var 4) (.var 0)

omit D in
theorem result_typed : Typed R (ofEntries elimEntries 6) elimResult U0 := by
  have tP : Typed R (ofEntries elimEntries 6) (.var 4) (.pi numC (.pi (vecC (.var 6) (.var 0)) U0)) :=
    .var 4
  have tv : Typed R (ofEntries elimEntries 6) (.var 0) (vecC (.var 5) (.var 1)) := .var 0
  exact .appElim (.appElim tP (.var 1)) tv

/-- **The eliminator's declared type is typed**, in every package declaring vectors. -/
theorem elimType_typed : ∃ w, R.isUniverse w ∧ Typed R .nil elimType (.head w) := by
  have t5 := D.tower.pi_small D.entry5_typed (result_typed (R := R))
  have t4 := D.tower.pi_small D.num_typed t5
  have t3 := D.tower.pi_small D.entry3_typed t4
  have t2 := D.tower.pi_small D.entry2_typed t3
  have t1 := Derivable.piForm D.entry1_typed (D.tower.isUniverse _) t2 (D.tower.isUniverse _)
    (D.tower.join _ _)
  have t0 := Derivable.piForm D.tower.u0_typed (D.tower.isUniverse _) t1 (D.tower.isUniverse _)
    (D.tower.join _ _)
  exact ⟨_, D.tower.isUniverse _, t0⟩

theorem ctxPc_formed : CtxFormed R ctxPc :=
  .snoc (.snoc (.snoc (.snoc .nil ⟨_, D.tower.isUniverse _, D.tower.u0_typed⟩)
    ⟨_, D.tower.isUniverse _, D.entry1_typed⟩) ⟨_, D.tower.isUniverse _, D.entry2_typed⟩)
    ⟨_, D.tower.isUniverse _, D.entry3_typed⟩

/-- **The eliminator at its declared type**: `vec-elim A P pn pc k v : P k v`, in every
package declaring vectors and the eliminator. -/
theorem vecElim_typed (dElim : R.constantType vecElim = some elimType)
    {A P pn pc k v : Tm Tower.Head n} (tA : Typed R Γ A U0) (tP : Typed R Γ P (vecMotive A))
    (tpn : Typed R Γ pn (.app (.app P zeroC) ttC)) (tpc : Typed R Γ pc (vecMethod A P))
    (tk : Typed R Γ k numC) (tv : Typed R Γ v (vecC A k)) :
    Typed R Γ (vecElimC A P pn pc k v) (.app (.app P k) v) := by
  obtain ⟨w, hw, typed⟩ := D.elimType_typed
  have tc : Typed R Γ (.const vecElim) (liftClosed elimType) := .const dElim typed hw
  have m₀ : SubstMor R .nil Γ fun i => Fin.elim0 i := fun i => Fin.elim0 i
  have mor : SubstMor R (ofEntries elimEntries 6) Γ
      (consSub v (consSub k (consSub pc (consSub pn (consSub P (consSub A fun i => Fin.elim0 i)))))) :=
    SubstMor.cons (SubstMor.cons (SubstMor.cons (SubstMor.cons (SubstMor.cons (SubstMor.cons m₀ tA)
      tP) tpn) tpc) tk) tv
  exact Typed.telescope_apply mor tc

end VecDeclared

/-! ## The equations of the eliminator are typed -/

/-- The context of the equation at `zero`: `A P pn pc (v : vec A zero)`. -/
theorem elimZero_formed :
    CtxFormed (elimStage lv) (.snoc (ofEntries elimEntries 4) (vecC (.var 3) zeroC)) :=
  .snoc (vecDeclared_elim lv).ctxPc_formed
    ⟨_, (vecDeclared_elim lv).tower.isUniverse _,
      (vecDeclared_elim lv).vec_typed (.var 3) (vecDeclared_elim lv).zero_typed⟩

/-- **The right-hand side at `zero` has the result type**: `unit-rec (λ w. P zero w) pn v : P zero v`. -/
theorem elimZero_typed :
    Typed (elimStage lv) (.snoc (ofEntries elimEntries 4) (vecC (.var 3) zeroC)) elimZero
      (.app (.app (.var 3) zeroC) (.var 0)) := by
  have D := vecDeclared_elim lv
  have tPw : Typed (elimStage lv) (.snoc (.snoc (ofEntries elimEntries 4) (vecC (.var 3) zeroC)) unitC)
      (.var 4) (.pi numC (.pi (vecC (.var 6) (.var 0)) U0)) := .var 4
  have tAw : Typed (elimStage lv) (.snoc (.snoc (ofEntries elimEntries 4) (vecC (.var 3) zeroC)) unitC)
      (.var 5) U0 := .var 5
  have tw₀ : Typed (elimStage lv) (.snoc (.snoc (ofEntries elimEntries 4) (vecC (.var 3) zeroC)) unitC)
      (.var 0) unitC := .var 0
  have tw : Typed (elimStage lv) (.snoc (.snoc (ofEntries elimEntries 4) (vecC (.var 3) zeroC)) unitC)
      (.var 0) (vecC (.var 5) zeroC) := Typed.convType tw₀ (D.vec_zero_eq tAw).symm
  have tPz : Typed (elimStage lv) (.snoc (.snoc (ofEntries elimEntries 4) (vecC (.var 3) zeroC)) unitC)
      (.app (.var 4) zeroC) (.pi (vecC (.var 5) zeroC) U0) := .appElim tPw D.zero_typed
  have tQbody : Typed (elimStage lv)
      (.snoc (.snoc (ofEntries elimEntries 4) (vecC (.var 3) zeroC)) unitC)
      (.app (.app (.var 4) zeroC) (.var 0)) (.head (.sort lv)) :=
    D.tower.lift (.appElim tPz tw) lv
  have tQty : Typed (elimStage lv) (.snoc (ofEntries elimEntries 4) (vecC (.var 3) zeroC))
      (.pi unitC (.head (.sort lv))) (.head (.sort (.max (.const 0) (.succ lv)))) :=
    .piForm D.unit_typed (D.tower.isUniverse _) (.headType (D.tower.headTyping _))
      (D.tower.isUniverse _) (D.tower.join _ _)
  have tQ : Typed (elimStage lv) (.snoc (ofEntries elimEntries 4) (vecC (.var 3) zeroC))
      (.lam (.app (.app (.var 4) zeroC) (.var 0))) (.pi unitC (.head (.sort lv))) :=
    .lamIntro tQty (D.tower.isUniverse _) tQbody
  have beta : Equal (elimStage lv) (.snoc (ofEntries elimEntries 4) (vecC (.var 3) zeroC))
      (.app (.lam (.app (.app (.var 4) zeroC) (.var 0))) ttC) (.app (.app (.var 3) zeroC) ttC)
      (.head (.sort lv)) :=
    .betaPi tQty (D.tower.isUniverse _) tQbody D.tt_typed
  have tpn : Typed (elimStage lv) (.snoc (ofEntries elimEntries 4) (vecC (.var 3) zeroC)) (.var 2)
      (.app (.app (.var 3) zeroC) ttC) := .var 2
  have tpn' : Typed (elimStage lv) (.snoc (ofEntries elimEntries 4) (vecC (.var 3) zeroC)) (.var 2)
      (.app (.lam (.app (.app (.var 4) zeroC) (.var 0))) ttC) :=
    Typed.convType tpn ⟨_, D.tower.isUniverse _, beta.symm⟩
  have tA : Typed (elimStage lv) (.snoc (ofEntries elimEntries 4) (vecC (.var 3) zeroC)) (.var 4) U0 :=
    .var 4
  have tv₀ : Typed (elimStage lv) (.snoc (ofEntries elimEntries 4) (vecC (.var 3) zeroC)) (.var 0)
      (vecC (.var 4) zeroC) := .var 0
  have tv : Typed (elimStage lv) (.snoc (ofEntries elimEntries 4) (vecC (.var 3) zeroC)) (.var 0)
      unitC := Typed.convType tv₀ (D.vec_zero_eq tA)
  have tRec := D.unitRec_typed (lv := lv) rfl tQ tpn' tv
  have beta' : Equal (elimStage lv) (.snoc (ofEntries elimEntries 4) (vecC (.var 3) zeroC))
      (.app (.lam (.app (.app (.var 4) zeroC) (.var 0))) (.var 0)) (.app (.app (.var 3) zeroC) (.var 0))
      (.head (.sort lv)) :=
    .betaPi tQty (D.tower.isUniverse _) tQbody tv
  exact Typed.convType tRec ⟨_, D.tower.isUniverse _, beta'⟩

/-- The context of the equation at `succ`: `A P pn pc n (v : vec A (succ n))
(h : Π (w : vec A n). P n w)`. -/
abbrev succCtx : Ctx Tower.Head 7 :=
  .snoc (.snoc (.snoc (ofEntries elimEntries 4) numC) (vecC (.var 4) (succC (.var 0))))
    (.pi (vecC (.var 5) (.var 1)) (.app (.app (.var 5) (.var 2)) (.var 0)))

theorem elimSucc_formed : CtxFormed (elimStage lv) succCtx := by
  have D := vecDeclared_elim lv
  have tA₅ : Typed (elimStage lv) (.snoc (ofEntries elimEntries 4) numC) (.var 4) U0 := .var 4
  have tn₅ : Typed (elimStage lv) (.snoc (ofEntries elimEntries 4) numC) (.var 0) numC := .var 0
  have tA₆ : Typed (elimStage lv) (.snoc (.snoc (ofEntries elimEntries 4) numC)
      (vecC (.var 4) (succC (.var 0)))) (.var 5) U0 := .var 5
  have tn₆ : Typed (elimStage lv) (.snoc (.snoc (ofEntries elimEntries 4) numC)
      (vecC (.var 4) (succC (.var 0)))) (.var 1) numC := .var 1
  have tP₇ : Typed (elimStage lv) (.snoc (.snoc (.snoc (ofEntries elimEntries 4) numC)
      (vecC (.var 4) (succC (.var 0)))) (vecC (.var 5) (.var 1))) (.var 5)
      (.pi numC (.pi (vecC (.var 7) (.var 0)) U0)) := .var 5
  have tn₇ : Typed (elimStage lv) (.snoc (.snoc (.snoc (ofEntries elimEntries 4) numC)
      (vecC (.var 4) (succC (.var 0)))) (vecC (.var 5) (.var 1))) (.var 2) numC := .var 2
  have tw₇ : Typed (elimStage lv) (.snoc (.snoc (.snoc (ofEntries elimEntries 4) numC)
      (vecC (.var 4) (succC (.var 0)))) (vecC (.var 5) (.var 1))) (.var 0) (vecC (.var 6) (.var 2)) :=
    .var 0
  have tCod : Typed (elimStage lv) (.snoc (.snoc (.snoc (ofEntries elimEntries 4) numC)
      (vecC (.var 4) (succC (.var 0)))) (vecC (.var 5) (.var 1)))
      (.app (.app (.var 5) (.var 2)) (.var 0)) U0 := .appElim (.appElim tP₇ tn₇) tw₇
  exact .snoc (.snoc (.snoc D.ctxPc_formed ⟨_, D.tower.isUniverse _, D.num_typed⟩)
    ⟨_, D.tower.isUniverse _, D.vec_typed tA₅ (D.succ_typed tn₅)⟩)
    ⟨_, D.tower.isUniverse _, D.tower.pi_small (D.vec_typed tA₆ tn₆) tCod⟩

/-- **The right-hand side at `succ` has the result type**, by eta for pairs:
`pc n (fst v) (snd v) (h (snd v)) : P (succ n) v`. -/
theorem elimSucc_typed :
    Typed (elimStage lv) succCtx elimSucc (.app (.app (.var 5) (succC (.var 2))) (.var 1)) := by
  have D := vecDeclared_elim lv
  have tA : Typed (elimStage lv) succCtx (.var 6) U0 := .var 6
  have tn : Typed (elimStage lv) succCtx (.var 2) numC := .var 2
  have tv : Typed (elimStage lv) succCtx (.var 1) (vecC (.var 6) (succC (.var 2))) := .var 1
  have th : Typed (elimStage lv) succCtx (.var 0)
      (.pi (vecC (.var 6) (.var 2)) (.app (.app (.var 6) (.var 3)) (.var 0))) := .var 0
  have tpc : Typed (elimStage lv) succCtx (.var 3) (vecMethod (.var 6) (.var 5)) := .var 3
  have tP : Typed (elimStage lv) succCtx (.var 5) (.pi numC (.pi (vecC (.var 7) (.var 0)) U0)) := .var 5
  have tFst := D.fst_typed tA tn tv
  have tSnd := D.snd_typed tA tn tv
  have t₁ := Derivable.appElim tpc tn
  have t₂ := Derivable.appElim t₁ tFst
  have t₃ := Derivable.appElim t₂ tSnd
  have tIh := Derivable.appElim th tSnd
  have t₄ := Derivable.appElim t₃ tIh
  have tPs : Typed (elimStage lv) succCtx (.app (.var 5) (succC (.var 2)))
      (.pi (vecC (.var 6) (succC (.var 2))) U0) := .appElim tP (D.succ_typed tn)
  have cong : Equal (elimStage lv) succCtx
      (.app (.app (.var 5) (succC (.var 2))) (.pair (.fst (.var 1)) (.snd (.var 1))))
      (.app (.app (.var 5) (succC (.var 2))) (.var 1)) U0 :=
    .appCong (.refl tPs) (D.vec_eta tA tn tv).symm
  exact Typed.convType t₄ ⟨_, D.tower.isUniverse _, cong⟩

/-! ## The declarations -/

/-! The declarations are stated at any generic equality with the laws of the model, so that
they hold for the typed equality and for the algorithmic equality alike. -/

section Declarations

variable (valuation : Nat → Nat) {E : GenericEquality Tower.Head} (lawsE : E.Laws (rules lv) roles)

/-- The package declares the natural numbers. -/
theorem declaresNum :
    DeclaresInductive (settingAt lv valuation E) (constantFreeRules (rules lv)) TowerNumbersModel.rules₁
      TowerNumbersModel.rules₂ num u ctors numRec (.sort lv) where
  role := roles_num
  recRole := roles_numRec
  hu := LevelTower.IsUniverse.sort _
  hv := LevelTower.IsUniverse.sort _
  sub₀ := RulesSub.constantFree _
  sub₁ := sub_numbers₁ lv
  sub₂ := sub_numbers₂ lv
  semantic₀ := fun declared => nomatch declared
  stage₁ := (TowerNumbersModel.declares lv valuation).stage₁
  stage₂ := (TowerNumbersModel.declares lv valuation).stage₂
  declared := rfl
  ctorDeclared := by
    intro k fields mem
    simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · rfl
  recDeclared := rfl
  fieldTyped := (TowerNumbersModel.declares lv valuation).fieldTyped
  ctorTyped := (TowerNumbersModel.declares lv valuation).ctorTyped
  recTyped := (TowerNumbersModel.declares lv valuation).recTyped
  iota := fun hms hi has hm =>
    RootComputation.step_unionAll mem_numRec ⟨_, _, _, _, _, _, _, hms, hi, has, hm, rfl, rfl⟩

/-- The package declares the unit type. -/
theorem declaresUnit :
    DeclaresInductive (settingAt lv valuation E) (constantFreeRules (rules lv)) unitStage₁ unitStage₂ unit
      u unitCtors unitRec (.sort lv) where
  role := roles_unit
  recRole := roles_unitRec
  hu := LevelTower.IsUniverse.sort _
  hv := LevelTower.IsUniverse.sort _
  sub₀ := RulesSub.constantFree _
  sub₁ := sub_unit₁ lv
  sub₂ := sub_unit₂ lv
  semantic₀ := fun declared => nomatch declared
  stage₁ := by
    intro name type declared
    change (if name = unit then some (.head u) else none) = some type at declared
    split at declared
    · rename_i h
      cases declared
      exact .inr ⟨h, rfl⟩
    · cases declared
  stage₂ := by
    intro name type declared
    change (if name = unit then some (.head u) else if name = tt then some (ctorType unit [])
      else none) = some type at declared
    split at declared
    · rename_i h
      cases declared
      subst h
      exact .inl rfl
    · split at declared
      · rename_i _ h
        cases declared
        exact .inr ⟨[], by subst h; exact mem_tt, rfl⟩
      · cases declared
  declared := rfl
  ctorDeclared := by
    intro k fields mem
    simp only [unitCtors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    obtain ⟨rfl, rfl⟩ := mem
    rfl
  recDeclared := rfl
  fieldTyped := by
    intro k fields F mem closed
    simp only [unitCtors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    obtain ⟨rfl, rfl⟩ := mem
    simp at closed
  ctorTyped := by
    intro k fields mem
    simp only [unitCtors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    obtain ⟨rfl, rfl⟩ := mem
    exact ⟨_, LevelTower.IsUniverse.sort _, towerLike_unit₁.small rfl⟩
  recTyped := towerLike_unit₂.unitRecType_typed rfl rfl lv
  iota := fun hms hi has hm =>
    RootComputation.step_unionAll mem_unitRec ⟨_, _, _, _, _, _, _, hms, hi, has, hm, rfl, rfl⟩

/-- The type of `void-rec`: `Π (P : void → V) (t : void). P t`, with no case. -/
theorem voidRecType_eq : recType void (.sort lv) [] =
    .pi (.pi voidC (.head (.sort lv))) (.pi voidC (.app (.var 1) (.var 0))) := rfl

theorem voidRecType_typed :
    ∃ w, voidStage.isUniverse w ∧ Typed voidStage .nil (recType void (.sort lv) []) (.head w) := by
  have tw := towerLike_void
  have tVoid : ∀ {m : Nat} {Δ : Ctx Tower.Head m}, Typed voidStage Δ voidC U0 :=
    fun {_ _} => tw.small rfl
  have tM : Typed voidStage .nil (.pi voidC (.head (.sort lv)))
      (.head (.sort (.max (.const 0) (.succ lv)))) :=
    .piForm tVoid (tw.isUniverse _) (.headType (tw.headTyping _)) (tw.isUniverse _) (tw.join _ _)
  have tP : Typed voidStage (.snoc (.snoc .nil (.pi voidC (.head (.sort lv)))) voidC) (.var 1)
      (.pi voidC (.head (.sort lv))) := .var 1
  have t₀ : Typed voidStage (.snoc (.snoc .nil (.pi voidC (.head (.sort lv)))) voidC) (.var 0) voidC :=
    .var 0
  have tBody : Typed voidStage (.snoc (.snoc .nil (.pi voidC (.head (.sort lv)))) voidC)
      (.app (.var 1) (.var 0)) (.head (.sort lv)) := .appElim tP t₀
  have t₂ := Derivable.piForm tVoid (tw.isUniverse _) tBody (tw.isUniverse _) (tw.join _ _)
  have t₁ := Derivable.piForm tM (tw.isUniverse _) t₂ (tw.isUniverse _) (tw.join _ _)
  exact ⟨_, tw.isUniverse _, t₁⟩

/-- **The package declares the empty type**, with no constructor; its recursor has no case. -/
theorem declaresVoid :
    DeclaresInductive (settingAt lv valuation E) (constantFreeRules (rules lv)) voidStage voidStage void
      u [] voidRec (.sort lv) where
  role := roles_void
  recRole := roles_voidRec
  hu := LevelTower.IsUniverse.sort _
  hv := LevelTower.IsUniverse.sort _
  sub₀ := RulesSub.constantFree _
  sub₁ := sub_void lv
  sub₂ := sub_void lv
  semantic₀ := fun declared => nomatch declared
  stage₁ := by
    intro name type declared
    change (if name = void then some (.head u) else none) = some type at declared
    split at declared
    · rename_i h
      cases declared
      exact .inr ⟨h, rfl⟩
    · cases declared
  stage₂ := fun declared => .inl declared
  declared := rfl
  ctorDeclared := fun mem => absurd mem List.not_mem_nil
  recDeclared := rfl
  fieldTyped := fun mem _ => absurd mem List.not_mem_nil
  ctorTyped := fun mem => absurd mem List.not_mem_nil
  recTyped := voidRecType_typed lv
  iota := fun _ found _ _ => by simp at found

include lawsE in
/-- The constants of the stage of `vec` are semantic. -/
theorem semantic_base : AllSemantic (settingAt lv valuation E) baseStage := by
  intro name type declared
  change (if name = unit then some (.head u) else if name = tt then some (ctorType unit [])
    else if name = void then some (.head u)
    else TowerNumbersModel.rules₂.constantType name) = some type at declared
  split at declared
  · rename_i h
    subst h
    cases declared
    exact (declaresUnit lv valuation).type_semantic lawsE
  · split at declared
    · rename_i _ h
      subst h
      cases declared
      exact (declaresUnit lv valuation).ctor_semantic lawsE mem_tt
    · split at declared
      · rename_i _ _ h
        subst h
        cases declared
        exact (declaresVoid lv valuation).type_semantic lawsE
      · exact (declaresNum lv valuation).semantic₂ lawsE declared

/-- `num → U0`, a type of the level above. -/
theorem family_typed {R : Rules Tower.Head} (tw : TowerLike R)
    (dNum : R.constantType num = some (.head u)) {m : Nat} {Δ : Ctx Tower.Head m} :
    Typed R Δ (.pi numC U0) (.head (.sort (.max (.const 0) (.succ (.const 0))))) :=
  .piForm (tw.small dNum) (tw.isUniverse _) tw.u0_typed (tw.isUniverse _) (tw.join _ _)

include lawsE in
/-- **The package declares `below-step`**: `below-step h zero ⟶ unit`,
`below-step h (succ i) ⟶ h i`. -/
theorem declaresBelowStep :
    DeclaresRecursion (settingAt lv valuation E) baseStage belowStep num ctors belowStepEntries 1 0 U0
      belowStepBody where
  role := roles_belowStep
  scrutinee := rfl
  declared := rfl
  sub₀ := sub_base lv
  semantic₀ := semantic_base lv valuation lawsE
  typed := ⟨_, LevelTower.IsUniverse.sort _, .piForm (family_typed towerLike_base rfl)
    (towerLike_base.isUniverse _) (family_typed towerLike_base rfl) (towerLike_base.isUniverse _)
    (towerLike_base.join _ _)⟩
  formed := by
    intro k fields mem
    simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · show CtxFormed baseStage (.snoc .nil (.pi numC U0))
      exact .snoc .nil ⟨_, towerLike_base.isUniverse _, family_typed towerLike_base rfl⟩
    · show CtxFormed baseStage (.snoc (.snoc (.snoc .nil (.pi numC U0)) numC) U0)
      exact .snoc (.snoc (.snoc .nil ⟨_, towerLike_base.isUniverse _, family_typed towerLike_base rfl⟩)
        ⟨_, towerLike_base.isUniverse _, towerLike_base.small rfl⟩)
        ⟨_, towerLike_base.isUniverse _, towerLike_base.u0_typed⟩
  bodyTyped := by
    intro k fields mem
    simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · show Typed baseStage (.snoc .nil (.pi numC U0)) unitC U0
      exact towerLike_base.small rfl
    · show Typed baseStage (.snoc (.snoc (.snoc .nil (.pi numC U0)) numC) U0) (.app (.var 2) (.var 1)) U0
      have th : Typed baseStage (.snoc (.snoc (.snoc .nil (.pi numC U0)) numC) U0) (.var 2)
          (.pi numC U0) := .var 2
      have ti : Typed baseStage (.snoc (.snoc (.snoc .nil (.pi numC U0)) numC) U0) (.var 1) numC :=
        .var 1
      exact .appElim th ti
  rule := by
    intro k fields mem m σ as has
    exact RootComputation.step_unionAll mem_belowStep ⟨_, _, σ, as, mem, has, rfl, rfl⟩

include lawsE in
/-- The constants of the stage of `below` are semantic. -/
theorem semantic_below : AllSemantic (settingAt lv valuation E) belowStage := by
  intro name type declared
  change (if name = belowStep then some belowStepType else baseStage.constantType name) = some type
    at declared
  split at declared
  · rename_i h
    subst h
    cases declared
    exact (declaresBelowStep lv valuation lawsE).semantic lawsE (declaresNum lv valuation)
  · exact semantic_base lv valuation lawsE declared

include lawsE in
/-- **The package declares `below`**: `below zero i ⟶ void`,
`below (succ n) i ⟶ below-step (below n) i`. -/
theorem declaresBelow :
    DeclaresRecursion (settingAt lv valuation E) belowStage below num ctors belowEntries 0 1 U0
      belowBody where
  role := roles_below
  scrutinee := rfl
  declared := rfl
  sub₀ := sub_below lv
  semantic₀ := semantic_below lv valuation lawsE
  typed := ⟨_, LevelTower.IsUniverse.sort _, .piForm (towerLike_below.small rfl)
    (towerLike_below.isUniverse _) (family_typed towerLike_below rfl) (towerLike_below.isUniverse _)
    (towerLike_below.join _ _)⟩
  formed := by
    intro k fields mem
    simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · show CtxFormed belowStage (.snoc .nil numC)
      exact .snoc .nil ⟨_, towerLike_below.isUniverse _, towerLike_below.small rfl⟩
    · show CtxFormed belowStage (.snoc (.snoc (.snoc .nil numC) numC) (.pi numC U0))
      exact .snoc (.snoc (.snoc .nil ⟨_, towerLike_below.isUniverse _, towerLike_below.small rfl⟩)
        ⟨_, towerLike_below.isUniverse _, towerLike_below.small rfl⟩)
        ⟨_, towerLike_below.isUniverse _, family_typed towerLike_below rfl⟩
  bodyTyped := by
    intro k fields mem
    simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · show Typed belowStage (.snoc .nil numC) voidC U0
      exact towerLike_below.small rfl
    · show Typed belowStage (.snoc (.snoc (.snoc .nil numC) numC) (.pi numC U0))
        (belowStepC (.var 0) (.var 1)) U0
      have tStep : Typed belowStage (.snoc (.snoc (.snoc .nil numC) numC) (.pi numC U0))
          (.const belowStep) (.pi (.pi numC U0) (.pi numC U0)) :=
        .const (type := .pi (.pi numC U0) (.pi numC U0)) rfl
          (.piForm (family_typed towerLike_below rfl) (towerLike_below.isUniverse _)
            (family_typed towerLike_below rfl) (towerLike_below.isUniverse _) (towerLike_below.join _ _))
          (towerLike_below.isUniverse _)
      have th : Typed belowStage (.snoc (.snoc (.snoc .nil numC) numC) (.pi numC U0)) (.var 0)
          (.pi numC U0) := .var 0
      have ti : Typed belowStage (.snoc (.snoc (.snoc .nil numC) numC) (.pi numC U0)) (.var 1) numC :=
        .var 1
      exact .appElim (.appElim tStep th) ti
  rule := by
    intro k fields mem m σ as has
    exact RootComputation.step_unionAll mem_below ⟨_, _, σ, as, mem, has, rfl, rfl⟩

include lawsE in
/-- **The package declares `vec` by its two equations.** -/
theorem declaresVec :
    DeclaresRecursion (settingAt lv valuation E) baseStage vec num ctors vecEntries 1 0 vecResult
      vecBody where
  role := roles_vec
  scrutinee := rfl
  declared := rfl
  sub₀ := sub_base lv
  semantic₀ := semantic_base lv valuation lawsE
  typed := ⟨_, LevelTower.IsUniverse.sort _, .piForm towerLike_base.u0_typed (towerLike_base.isUniverse _)
    (.piForm (towerLike_base.small rfl) (towerLike_base.isUniverse _) towerLike_base.u0_typed
      (towerLike_base.isUniverse _) (towerLike_base.join _ _)) (towerLike_base.isUniverse _)
    (towerLike_base.join _ _)⟩
  formed := by
    intro k fields mem
    simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · show CtxFormed baseStage (.snoc .nil U0)
      exact .snoc .nil ⟨_, towerLike_base.isUniverse _, towerLike_base.u0_typed⟩
    · show CtxFormed baseStage (.snoc (.snoc (.snoc .nil U0) numC) U0)
      exact .snoc (.snoc (.snoc .nil ⟨_, towerLike_base.isUniverse _, towerLike_base.u0_typed⟩)
        ⟨_, towerLike_base.isUniverse _, towerLike_base.small rfl⟩)
        ⟨_, towerLike_base.isUniverse _, towerLike_base.u0_typed⟩
  bodyTyped := by
    intro k fields mem
    simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · show Typed baseStage (.snoc .nil U0) unitC U0
      exact towerLike_base.small rfl
    · show Typed baseStage (.snoc (.snoc (.snoc .nil U0) numC) U0) (.sigma (.var 2) (.var 1)) U0
      have tA : Typed baseStage (.snoc (.snoc (.snoc .nil U0) numC) U0) (.var 2) U0 := .var 2
      have th : Typed baseStage (.snoc (.snoc (.snoc (.snoc .nil U0) numC) U0) (.var 2)) (.var 1) U0 :=
        .var 1
      exact towerLike_base.sigma_small tA th
  rule := by
    intro k fields mem m σ as has
    exact RootComputation.step_unionAll mem_vec ⟨_, _, σ, as, mem, has, rfl, rfl⟩

include lawsE in
/-- The constants of the stage of the eliminator are semantic. -/
theorem semantic_elim : AllSemantic (settingAt lv valuation E) (elimStage lv) := by
  intro name type declared
  change (if name = vec then some vecType
    else if name = unitRec then some (recType unit (.sort lv) unitCtors)
    else baseStage.constantType name) = some type at declared
  split at declared
  · rename_i h
    subst h
    cases declared
    exact (declaresVec lv valuation lawsE).semantic lawsE (declaresNum lv valuation)
  · split at declared
    · rename_i _ h
      subst h
      cases declared
      exact (declaresUnit lv valuation).rec_semantic lawsE
    · exact semantic_base lv valuation lawsE declared

include lawsE in
/-- **The package declares the dependent eliminator of vectors**, by structural recursion on the
length. -/
theorem declaresElim :
    DeclaresRecursion (settingAt lv valuation E) (elimStage lv) vecElim num ctors elimEntries 4 1
      elimResult elimBody where
  role := roles_vecElim
  scrutinee := rfl
  declared := rfl
  sub₀ := sub_elim lv
  semantic₀ := semantic_elim lv valuation lawsE
  typed := (vecDeclared_elim lv).elimType_typed
  formed := by
    intro k fields mem
    simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact elimZero_formed lv
    · exact elimSucc_formed lv
  bodyTyped := by
    intro k fields mem
    simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact elimZero_typed lv
    · exact elimSucc_typed lv
  rule := by
    intro k fields mem m σ as has
    exact RootComputation.step_unionAll mem_vecElim ⟨_, _, σ, as, mem, has, rfl, rfl⟩

include lawsE in
/-- **The package declares addition**, by recursion on its first argument. -/
theorem declaresAdd :
    DeclaresRecursion (settingAt lv valuation E) TowerNumbersModel.rules₂ add num ctors addEntries 0 1
      numC addBody where
  role := roles_add
  scrutinee := rfl
  declared := rfl
  sub₀ := sub_numbers₂ lv
  semantic₀ := (declaresNum lv valuation).semantic₂ lawsE
  typed := ⟨_, LevelTower.IsUniverse.sort _, towerLike_numbers₂.pi_small (towerLike_numbers₂.small rfl)
    (towerLike_numbers₂.pi_small (towerLike_numbers₂.small rfl) (towerLike_numbers₂.small rfl))⟩
  formed := by
    intro k fields mem
    simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · show CtxFormed TowerNumbersModel.rules₂ (.snoc .nil numC)
      exact .snoc .nil ⟨_, towerLike_numbers₂.isUniverse _, towerLike_numbers₂.small rfl⟩
    · show CtxFormed TowerNumbersModel.rules₂ (.snoc (.snoc (.snoc .nil numC) numC) (.pi numC numC))
      exact .snoc (.snoc (.snoc .nil ⟨_, towerLike_numbers₂.isUniverse _, towerLike_numbers₂.small rfl⟩)
        ⟨_, towerLike_numbers₂.isUniverse _, towerLike_numbers₂.small rfl⟩)
        ⟨_, towerLike_numbers₂.isUniverse _,
          towerLike_numbers₂.pi_small (towerLike_numbers₂.small rfl) (towerLike_numbers₂.small rfl)⟩
  bodyTyped := by
    intro k fields mem
    simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · show Typed TowerNumbersModel.rules₂ (.snoc .nil numC) (.var 0) numC
      exact .var 0
    · show Typed TowerNumbersModel.rules₂ (.snoc (.snoc (.snoc .nil numC) numC) (.pi numC numC))
        (succC (.app (.var 0) (.var 1))) numC
      have th : Typed TowerNumbersModel.rules₂ (.snoc (.snoc (.snoc .nil numC) numC) (.pi numC numC))
          (.var 0) (.pi numC numC) := .var 0
      have tm : Typed TowerNumbersModel.rules₂ (.snoc (.snoc (.snoc .nil numC) numC) (.pi numC numC))
          (.var 1) numC := .var 1
      have tNum : ∀ {m : Nat} {Δ : Ctx Tower.Head m}, Typed TowerNumbersModel.rules₂ Δ numC U0 :=
        fun {_ _} => towerLike_numbers₂.small rfl
      have tSucc : Typed TowerNumbersModel.rules₂ (.snoc (.snoc (.snoc .nil numC) numC) (.pi numC numC))
          (.const succ) (.pi numC numC) :=
        .const (type := .pi numC numC) rfl (towerLike_numbers₂.pi_small tNum tNum)
          (towerLike_numbers₂.isUniverse _)
      exact .appElim tSucc (.appElim th tm)
  rule := by
    intro k fields mem m σ as has
    exact RootComputation.step_unionAll mem_add ⟨_, _, σ, as, mem, has, rfl, rfl⟩

/-- **The package declares the identity eliminator**, for identity types of the lowest universe,
with motives in the universe of level `lv`. -/
theorem declaresIdElim :
    DeclaresEliminator (settingAt lv valuation E) idElim u (.sort lv) where
  role := roles_idElim
  declared := rfl
  rule := fun {_ a₀ a₁ a₂ a₃ a₄ a₅} =>
    RootComputation.step_unionAll mem_idElim ⟨a₀, a₁, a₂, a₃, a₄, a₅, rfl, rfl⟩
  hu := LevelTower.IsUniverse.sort _
  hv := LevelTower.IsUniverse.sort _
  typed := by
    obtain ⟨w, hw, typed⟩ := TowerEliminatorModel.elimType_typed (.const 0) lv
    exact ⟨w, hw, Derivable.mono ⟨id, id, id, id, id, id, id⟩ typed⟩

include lawsE in
/-- **Every declared constant is semantic**, for any generic equality with the laws. -/
theorem constantsAt : SemanticConstants (settingAt lv valuation E) := by
  intro name type w declared _ _
  change constantType lv name = some type at declared
  unfold constantType at declared
  split at declared
  · rename_i h
    subst h
    cases declared
    intro m Δ formed P r
    exact (declaresAdd lv valuation lawsE).semantic lawsE (declaresNum lv valuation) formed r
  · split at declared
    · rename_i _ h
      subst h
      cases declared
      intro m Δ formed P r
      exact (declaresElim lv valuation lawsE).semantic lawsE (declaresNum lv valuation) formed r
    · split at declared
      · rename_i _ _ h
        subst h
        cases declared
        intro m Δ formed P r
        exact (declaresNum lv valuation).rec_semantic lawsE formed r
      · split at declared
        · rename_i _ _ _ h
          subst h
          cases declared
          intro m Δ formed P r
          exact (declaresVoid lv valuation).rec_semantic lawsE formed r
        · split at declared
          · rename_i _ _ _ _ h
            subst h
            cases declared
            intro m Δ formed P r
            exact (declaresBelow lv valuation lawsE).semantic lawsE (declaresNum lv valuation)
              formed r
          · split at declared
            · rename_i _ _ _ _ _ h
              subst h
              cases declared
              intro m Δ formed P r
              exact (declaresBelowStep lv valuation lawsE).semantic lawsE
                (declaresNum lv valuation) formed r
            · split at declared
              · rename_i _ _ _ _ _ _ h
                subst h
                cases declared
                exact (declaresIdElim lv valuation).semantic lawsE
              · exact semantic_elim lv valuation lawsE declared

end Declarations

/-- **Every declared constant is semantic.** -/
theorem constants (valuation : Nat → Nat) : SemanticConstants (setting lv valuation) :=
  constantsAt lv valuation (laws lv valuation)

/-! ## The hypotheses of the model -/

/-- **The facts about the weak-head forms of the package's types**, from the normalization
model, in which its declared constants are semantic. -/
theorem facts : FormFacts (rules lv) roles :=
  .ofSemantic (S := setting lv fun _ => 0) (laws lv _) (constants lv _)

/-- **Every equation preserves typing**: both recursors, `vec`, the eliminator and addition. -/
theorem roots : RootPreserving (rules lv) := by
  intro n Γ l r A formed step typing
  obtain ⟨entry, mem, h⟩ := RootComputation.unionAll_step step
  simp only [computations, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (declaresNum lv (fun _ => 0) (E := declarative (rules lv))).toRecursor.step_preserves
      (facts lv) (RulesSub.refl _) formed h typing
  · exact (declaresUnit lv (fun _ => 0) (E := declarative (rules lv))).toRecursor.step_preserves
      (facts lv) (RulesSub.refl _) formed h typing
  · obtain ⟨k, fields, σ, as, mem, has, rfl, rfl⟩ := h
    exact (declaresVec lv (fun _ => 0) (laws lv fun _ => 0)).rule_preserves (facts lv)
      (declaresNum lv fun _ => 0) (RulesSub.refl _) formed mem σ as has typing
  · obtain ⟨k, fields, σ, as, mem, has, rfl, rfl⟩ := h
    exact (declaresElim lv (fun _ => 0) (laws lv fun _ => 0)).rule_preserves (facts lv)
      (declaresNum lv fun _ => 0) (RulesSub.refl _) formed mem σ as has typing
  · obtain ⟨k, fields, σ, as, mem, has, rfl, rfl⟩ := h
    exact (declaresAdd lv (fun _ => 0) (laws lv fun _ => 0)).rule_preserves (facts lv)
      (declaresNum lv fun _ => 0) (RulesSub.refl _) formed mem σ as has typing
  · obtain ⟨k, fields, σ, as, mem, has, rfl, rfl⟩ := h
    exact (declaresBelowStep lv (fun _ => 0) (laws lv fun _ => 0)).rule_preserves (facts lv)
      (declaresNum lv fun _ => 0) (RulesSub.refl _) formed mem σ as has typing
  · obtain ⟨k, fields, σ, as, mem, has, rfl, rfl⟩ := h
    exact (declaresBelow lv (fun _ => 0) (laws lv fun _ => 0)).rule_preserves (facts lv)
      (declaresNum lv fun _ => 0) (RulesSub.refl _) formed mem σ as has typing
  · obtain ⟨a₀, a₁, a₂, a₃, a₄, a₅, e₁, e₂⟩ := h
    subst e₁ e₂
    exact (declaresIdElim lv (fun _ => 0) (E := declarative (rules lv))).rule_preserves (facts lv)
      (RulesSub.refl _) formed typing

/-- Head equality steps preserve typing. -/
theorem heads : HeadPreserving (rules lv) := by
  intro n Γ h h' A same typing
  obtain ⟨w, headTyping, le⟩ := Typed.generation typing
  cases headTyping with
  | legacyGround =>
      cases h' with
      | legacyGround => exact Typed.subsume (.headType .legacyGround) le
      | sort _ => exact same.elim
  | sort l =>
      cases h' with
      | legacyGround => exact same.elim
      | sort r =>
          have raise : (rules lv).cumulative (.sort (.succ r)) (.sort (.succ l)) := by
            intro ν
            show LevelExpr.eval ν r + 1 ≤ LevelExpr.eval ν l + 1
            have := same ν
            omega
          exact Typed.subsume (.cumul (.headType (.sort r)) raise) le

theorem algebra : CumulativeAlgebra (rules lv) where
  trans := TowerModel.algebra.trans
  same_left := TowerModel.algebra.same_left
  same_right := TowerModel.algebra.same_right
  join_least := TowerModel.algebra.join_least

/-! ## The equations as steps -/

/-- The eliminator's equation at `zero`. -/
theorem elim_zero_step {n : Nat} (A P pn pc v : Tm Tower.Head n) :
    (rules lv).computation.step (vecElimC A P pn pc zeroC v)
      (unitRecC (.lam (.app (.app (Presentation.rename wk P) zeroC) (.var 0))) pn v) :=
  RootComputation.step_unionAll mem_vecElim
    ⟨zero, [], consSub v (consSub zeroC (consSub pc (consSub pn (consSub P
      (consSub A fun i => Fin.elim0 i))))), [], mem_zero, rfl, rfl, rfl⟩

/-- The eliminator's equation at `succ k`. -/
theorem elim_succ_step {n : Nat} (A P pn pc k v : Tm Tower.Head n) :
    (rules lv).computation.step (vecElimC A P pn pc (succC k) v)
      (.app (.app (.app (.app pc k) (.fst v)) (.snd v)) (vecElimC A P pn pc k (.snd v))) :=
  RootComputation.step_unionAll mem_vecElim
    ⟨succ, [.recursive], consSub v (consSub (succC k) (consSub pc (consSub pn (consSub P
      (consSub A fun i => Fin.elim0 i))))), [k], mem_succ, rfl, rfl, rfl⟩

/-- The unit recursor at `tt`. -/
theorem unit_iota_step {n : Nat} (Q d : Tm Tower.Head n) :
    (rules lv).computation.step (unitRecC Q d ttC) d :=
  RootComputation.step_unionAll mem_unitRec ⟨Q, [d], 0, tt, [], [], d, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `add zero m ⟶ m`. -/
theorem add_zero_step {n : Nat} (m : Tm Tower.Head n) :
    (rules lv).computation.step (addC zeroC m) m :=
  RootComputation.step_unionAll mem_add
    ⟨zero, [], consSub m (consSub zeroC fun i => Fin.elim0 i), [], mem_zero, rfl, rfl, rfl⟩

/-- `add (succ k) m ⟶ succ (add k m)`. -/
theorem add_succ_step {n : Nat} (k m : Tm Tower.Head n) :
    (rules lv).computation.step (addC (succC k) m) (succC (addC k m)) :=
  RootComputation.step_unionAll mem_add
    ⟨succ, [.recursive], consSub m (consSub (succC k) fun i => Fin.elim0 i), [k], mem_succ, rfl, rfl,
      rfl⟩

end TowerVectorsModel

/-! ## Consequences for the tower with vectors -/

section Consequences

open TowerVectorsModel

variable {lv : LevelExpr Nat} {n : Nat} {Γ : Ctx Tower.Head n}

/-- **Reduction preserves typing**, including the equations of `vec`, of the eliminator and of
addition. -/
theorem TowerVectors.reduces_preserve {t t' T : Tm Tower.Head n} (formed : CtxFormed (rules lv) Γ)
    (red : Reduces (rules lv) t t') (typing : Typed (rules lv) Γ t T) :
    Typed (rules lv) Γ t' T ∧ Equal (rules lv) Γ t t' T :=
  Reduces.preserve (S := setting lv fun _ => 0) (facts lv) (roots lv) (heads lv) formed red typing

/-- **Soundness of the conversion algorithm.** -/
theorem TowerVectors.algorithm_sound {st : AlgorithmStatement Tower.Head}
    (derivation : Algorithm (rules lv) st) : AlgorithmSound (setting lv fun _ => 0) st :=
  Algorithm.sound (S := setting lv fun _ => 0) (facts lv) (roots lv) (heads lv) (algebra lv)
    derivation

/-- Every typed term of a formed context has a weak-head normal form. -/
theorem TowerVectors.whnf_exists {t T : Tm Tower.Head n} (typing : Typed (rules lv) Γ t T)
    (formed : CtxFormed (rules lv) Γ) :
    ∃ nf, WhRed (rules lv) roles t nf ∧ Whnf (rules lv) roles nf :=
  Typed.whnf_exists (S := setting lv fun _ => 0) (laws lv _) (constants lv _) typing formed

/-- **Injectivity of dependent function types.** -/
theorem TowerVectors.pi_injective {A A' : Tm Tower.Head n} {B B' : Tm Tower.Head (n + 1)}
    (equal : TypeEq (rules lv) Γ (.pi A B) (.pi A' B')) (formed : CtxFormed (rules lv) Γ) :
    TypeEq (rules lv) Γ A A' ∧ TypeEq (rules lv) (.snoc Γ A) B B' :=
  TypeEq.pi_injective (facts lv) equal formed

/-- **Injectivity of dependent pair types**, hence of `vec` at successor lengths. -/
theorem TowerVectors.sigma_injective {A A' : Tm Tower.Head n} {B B' : Tm Tower.Head (n + 1)}
    (equal : TypeEq (rules lv) Γ (.sigma A B) (.sigma A' B')) (formed : CtxFormed (rules lv) Γ) :
    TypeEq (rules lv) Γ A A' ∧ TypeEq (rules lv) (.snoc Γ A) B B' :=
  TypeEq.sigma_injective (facts lv) equal formed

/-- **Discrimination**: the unit type is not a dependent pair type. -/
theorem TowerVectors.unit_ne_sigma {A : Tm Tower.Head n} {B : Tm Tower.Head (n + 1)}
    (formed : CtxFormed (rules lv) Γ) : ¬ TypeEq (rules lv) Γ unitC (.sigma A B) :=
  TypeEq.inductive_ne_sigma (facts lv) roles_unit formed

/-- Zero is not a successor. -/
theorem TowerVectors.zero_ne_succ (formed : CtxFormed (rules lv) Γ) {a : Tm Tower.Head n} :
    ¬ Equal (rules lv) Γ zeroC (succC a) numC :=
  Equal.ctor_discrimination (S := setting lv fun _ => 0) (laws lv _) (constants lv _) formed
    (T := num) (ctors := ctors) roles_num mem_zero mem_succ (by decide) (as := []) (bs := [a])

/-! ### Addition computes in conversion -/

/-- `add zero m ≡ m`. -/
theorem TowerVectors.add_zero {m : Tm Tower.Head n} (tm : Typed (rules lv) Γ m numC) :
    Equal (rules lv) Γ (addC zeroC m) m numC := by
  have D := vecDeclared_rules lv
  have tAdd : Typed (rules lv) Γ (.const add) (.pi numC (.pi numC numC)) :=
    .const (type := .pi numC (.pi numC numC)) rfl (D.tower.pi_small D.num_typed
      (D.tower.pi_small D.num_typed D.num_typed)) (D.tower.isUniverse _)
  exact .root (add_zero_step lv m) (.appElim (.appElim tAdd D.zero_typed) tm) tm

/-- `add (succ k) m ≡ succ (add k m)`. -/
theorem TowerVectors.add_succ {k m : Tm Tower.Head n} (tk : Typed (rules lv) Γ k numC)
    (tm : Typed (rules lv) Γ m numC) :
    Equal (rules lv) Γ (addC (succC k) m) (succC (addC k m)) numC := by
  have D := vecDeclared_rules lv
  have tAdd : Typed (rules lv) Γ (.const add) (.pi numC (.pi numC numC)) :=
    .const (type := .pi numC (.pi numC numC)) rfl (D.tower.pi_small D.num_typed
      (D.tower.pi_small D.num_typed D.num_typed)) (D.tower.isUniverse _)
  exact .root (add_succ_step lv k m) (.appElim (.appElim tAdd (D.succ_typed tk)) tm)
    (D.succ_typed (.appElim (.appElim tAdd tk) tm))

/-! ### The computation rules of the eliminator, on constructors -/

/-- **The computation rule at the empty vector**:
`vec-elim A P pn pc zero tt ≡ pn : P zero tt`. -/
theorem TowerVectors.vecElim_nil (formed : CtxFormed (rules lv) Γ) {A P pn pc : Tm Tower.Head n}
    (tA : Typed (rules lv) Γ A U0) (tP : Typed (rules lv) Γ P (vecMotive A))
    (tpn : Typed (rules lv) Γ pn (.app (.app P zeroC) ttC))
    (tpc : Typed (rules lv) Γ pc (vecMethod A P)) :
    Equal (rules lv) Γ (vecElimC A P pn pc zeroC ttC) pn (.app (.app P zeroC) ttC) := by
  have D := vecDeclared_rules lv
  have typing := D.vecElim_typed rfl tA tP tpn tpc D.zero_typed (D.nil_typed tA)
  have red : Reduces (rules lv) (vecElimC A P pn pc zeroC ttC) pn :=
    .tail (.single (.root (elim_zero_step lv A P pn pc ttC))) (.root (unit_iota_step lv _ pn))
  exact (TowerVectors.reduces_preserve formed red typing).2

/-- **The computation rule at an extended vector**:
`vec-elim A P pn pc (succ k) (pair a v) ≡ pc k a v (vec-elim A P pn pc k v) : P (succ k) (pair a v)`,
on open `k`, `a` and `v`. -/
theorem TowerVectors.vecElim_cons (formed : CtxFormed (rules lv) Γ)
    {A P pn pc k a v : Tm Tower.Head n}
    (tA : Typed (rules lv) Γ A U0) (tP : Typed (rules lv) Γ P (vecMotive A))
    (tpn : Typed (rules lv) Γ pn (.app (.app P zeroC) ttC))
    (tpc : Typed (rules lv) Γ pc (vecMethod A P)) (tk : Typed (rules lv) Γ k numC)
    (ta : Typed (rules lv) Γ a A) (tv : Typed (rules lv) Γ v (vecC A k)) :
    Equal (rules lv) Γ (vecElimC A P pn pc (succC k) (.pair a v))
      (.app (.app (.app (.app pc k) a) v) (vecElimC A P pn pc k v))
      (.app (.app P (succC k)) (.pair a v)) := by
  have D := vecDeclared_rules lv
  have typing := D.vecElim_typed rfl tA tP tpn tpc (D.succ_typed tk) (D.cons_typed tA tk ta tv)
  have red : Reduces (rules lv) (vecElimC A P pn pc (succC k) (.pair a v))
      (.app (.app (.app (.app pc k) a) v) (vecElimC A P pn pc k v)) :=
    .tail (.tail (.tail (.single (.root (elim_succ_step lv A P pn pc k (.pair a v))))
      (.congAppFun (.congAppFun (.congAppArg (.betaSigmaFst a v)))))
      (.congAppFun (.congAppArg (.betaSigmaSnd a v))))
      (.congAppArg (.congAppArg (.betaSigmaSnd a v)))
  exact (TowerVectors.reduces_preserve formed red typing).2

/-! ### Controls -/

/-- **Positive control: the rule fires on the empty vector**, as one weak-head step. -/
theorem TowerVectors.vecElim_nil_fires {A P pn pc : Tm Tower.Head n} :
    WhStep (rules lv) roles (vecElimC A P pn pc zeroC ttC)
      (unitRecC (.lam (.app (.app (Presentation.rename wk P) zeroC) (.var 0))) pn ttC) :=
  .root (elim_zero_step lv A P pn pc ttC)

/-- **Negative control: stuck on a variable length.** `vec-elim A P pn pc x v` is neutral when
`x` is a variable, so no weak-head step applies to it. -/
theorem TowerVectors.vecElim_stuck_length {A P pn pc v : Tm Tower.Head n} (x : Fin n) :
    Neutral roles (vecElimC A P pn pc (.var x) v) ∧
      Whnf (rules lv) roles (vecElimC A P pn pc (.var x) v) := by
  have neutral : Neutral roles (vecElimC A P pn pc (.var x) v) :=
    Neutral.stuck_single (before := [A, P, pn, pc]) (after := [v]) roles_vecElim rfl (.var x)
  exact ⟨neutral, neutral.whnf (shape lv)⟩

/-- **Negative control: stuck on a variable vector of length zero.** The eliminator unfolds to the
unit recursor, which is neutral at the variable: the unit type has no eta. -/
theorem TowerVectors.vecElim_stuck_zero_vector {A P pn pc : Tm Tower.Head n} (x : Fin n) :
    WhRed (rules lv) roles (vecElimC A P pn pc zeroC (.var x))
        (unitRecC (.lam (.app (.app (Presentation.rename wk P) zeroC) (.var 0))) pn (.var x)) ∧
      Neutral roles
        (unitRecC (.lam (.app (.app (Presentation.rename wk P) zeroC) (.var 0))) pn (.var x)) ∧
      Whnf (rules lv) roles
        (unitRecC (.lam (.app (.app (Presentation.rename wk P) zeroC) (.var 0))) pn (.var x)) := by
  have neutral : Neutral roles
      (unitRecC (.lam (.app (.app (Presentation.rename wk P) zeroC) (.var 0))) pn (.var x)) :=
    Neutral.stuck_single (before := [.lam (.app (.app (Presentation.rename wk P) zeroC) (.var 0)), pn])
      (after := []) roles_unitRec rfl (.var x)
  exact ⟨.single (.root (elim_zero_step lv A P pn pc (.var x))), neutral, neutral.whnf (shape lv)⟩

/-- **Control: at a successor length the eliminator unfolds on every vector**, a variable
included: the recursive family's vectors of a known successor length are pairs, by eta. This is
where it differs from an inductive family, whose eliminator is stuck on a variable vector. -/
theorem TowerVectors.vecElim_succ_unfolds {A P pn pc k : Tm Tower.Head n} (x : Fin n) :
    WhStep (rules lv) roles (vecElimC A P pn pc (succC k) (.var x))
      (.app (.app (.app (.app pc k) (.fst (.var x))) (.snd (.var x)))
        (vecElimC A P pn pc k (.snd (.var x)))) :=
  .root (elim_succ_step lv A P pn pc k (.var x))

/-- **Negative control: an ill-indexed empty vector is rejected.** `tt` is not a vector of a
successor length: its type would be the unit type, which is not a dependent pair type. -/
theorem TowerVectors.tt_not_succ (formed : CtxFormed (rules lv) Γ) {A k : Tm Tower.Head n}
    (tA : Typed (rules lv) Γ A U0) (tk : Typed (rules lv) Γ k numC) :
    ¬ Typed (rules lv) Γ ttC (vecC A (succC k)) := by
  intro typing
  have D := vecDeclared_rules lv
  obtain ⟨type, w, declared, _, _, le⟩ := Typed.generation typing
  have known : (rules lv).constantType tt = some unitC := rfl
  rw [known] at declared
  obtain rfl := Option.some.inj declared
  have equal : TypeEq (rules lv) Γ unitC (vecC A (succC k)) :=
    TypeLe.rigid (S := setting lv fun _ => 0) le
      ⟨_, D.tower.isUniverse _, D.vec_typed tA (D.succ_typed tk)⟩ formed
      (fun _ _ e => TypeEq.inductive_ne_head (facts lv) roles_unit formed e)
      (fun _ _ e => TypeEq.inductive_ne_pi (facts lv) roles_unit formed e)
      (fun _ _ e => TypeEq.inductive_ne_sigma (facts lv) roles_unit formed e)
  exact TowerVectors.unit_ne_sigma formed (TypeEq.trans (levels lv fun _ => 0) equal
    (D.vec_succ_eq tA tk))

/-- **Negative control: an ill-indexed extended vector is rejected.** A pair is not a vector of
length zero. -/
theorem TowerVectors.pair_not_zero (formed : CtxFormed (rules lv) Γ) {A a v : Tm Tower.Head n}
    (tA : Typed (rules lv) Γ A U0) : ¬ Typed (rules lv) Γ (.pair a v) (vecC A zeroC) := by
  intro typing
  have D := vecDeclared_rules lv
  obtain ⟨A', B', w, tS, hw, _, _, le⟩ := Typed.generation typing
  have below := TypeLe.toBelow le ⟨_, D.tower.isUniverse _, D.vec_typed tA D.zero_typed⟩
  obtain ⟨A'', B'', eT, _, _⟩ :=
    Below.sigma_source (S := setting lv fun _ => 0) (facts lv) below formed (IsType.refl ⟨w, hw, tS⟩)
  exact TowerVectors.unit_ne_sigma formed (TypeEq.trans (levels lv fun _ => 0) (D.vec_zero_eq tA).symm eT)

/-- **Not an inductive family: the type former is not injective at length zero.**
`vec num zero ≡ vec unit zero`, though `num` and `unit` are different types. -/
theorem TowerVectors.vec_zero_not_injective (formed : CtxFormed (rules lv) Γ) :
    TypeEq (rules lv) Γ (vecC numC zeroC) (vecC unitC zeroC) ∧ ¬ TypeEq (rules lv) Γ numC unitC := by
  have D := vecDeclared_rules lv
  refine ⟨TypeEq.trans (levels lv fun _ => 0) (D.vec_zero_eq D.num_typed) (D.vec_zero_eq D.unit_typed).symm,
    fun e => ?_⟩
  exact absurd (TypeEq.inductive_injective (facts lv) roles_num roles_unit e formed) (by decide)

end Consequences

#print axioms TowerVectorsModel.declaresVec
#print axioms TowerVectorsModel.declaresElim
#print axioms TowerVectorsModel.declaresAdd
#print axioms TowerVectorsModel.declaresVoid
#print axioms TowerVectorsModel.declaresBelowStep
#print axioms TowerVectorsModel.declaresBelow
#print axioms TowerVectorsModel.declaresIdElim
#print axioms TowerVectorsModel.constantsAt
#print axioms TowerVectorsModel.constants
#print axioms TowerVectorsModel.facts
#print axioms TowerVectorsModel.roots
#print axioms TowerVectors.reduces_preserve
#print axioms TowerVectors.algorithm_sound
#print axioms TowerVectors.pi_injective
#print axioms TowerVectors.sigma_injective
#print axioms TowerVectors.add_succ
#print axioms TowerVectors.vecElim_nil
#print axioms TowerVectors.vecElim_cons
#print axioms TowerVectors.vecElim_stuck_length
#print axioms TowerVectors.vecElim_stuck_zero_vector
#print axioms TowerVectors.vecElim_succ_unfolds
#print axioms TowerVectors.tt_not_succ
#print axioms TowerVectors.pair_not_zero
#print axioms TowerVectors.vec_zero_not_injective

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
