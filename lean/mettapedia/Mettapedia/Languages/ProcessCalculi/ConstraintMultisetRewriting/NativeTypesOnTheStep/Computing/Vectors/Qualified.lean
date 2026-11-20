import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.DeclarationCheck
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.TwoReadings
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerVectorsConversion

/-!
# The package with vectors and their eliminator is qualified

The package `TowerVectorsModel.rules lv` (numbers with their recursor, the unit and empty types, the
recursive family `vec` with its dependent eliminator, addition, the order `below` on the numbers and
the identity eliminator) is **qualified** for the definitional reading, at every level `lv` its
recursors eliminate into and at every valuation of its level variables (`vectors_qualified`).

The one field the package did not have yet is its constructor presentation:

* its computation is exactly the instances of fourteen rows (`vectorEquations`, `vector_sound`,
  `vector_cover`): two rows of the recursor of the numbers, one of the recursor of the unit type, two
  of `vec`, two of the eliminator, two of addition, two of `below-step`, two of `below`, and the
  identity eliminator at reflexivity;
* the rows pass the syntactic declaration-time check (`vector_check`): every left side is a defined
  constant at its arity applied to linear constructor patterns (`zero`, `succ`, `tt`, `refl`), every
  right-side variable occurs on the left, and no two left sides unify.

Every other field is a proved fact of the package: the laws and the semantic constants of the typed
equality, root and head preservation and the level algebra (`TowerVectors`), and the semantic
constants of the algorithmic equality, read off the same declarations at every generic equality
(`algorithmicConstantsAt`).

**Consequences for this package, by instantiation**: Church–Rosser with β and the projections
(`vectors_churchRosser`), unique normal forms (`vectors_eq_of_normal`), subject reduction of every
reduction, under binders included (`vectors_subjectReduction`), conservativity (`vectors_conv_toEqual`),
weak-head normal forms (`vectors_whnf`), and the typed equality with η decided by the type-directed
algorithm (`vectors_algorithm_iff`, `vectors_decide`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing.Vectors

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open AlgebraicSchema AlgebraicParallel ConversionCoherence
open ConstructorSystem (ConstructorPresentation)
open TowerNumbersModel (num zero succ numRec ctors u)
open TowerVectorsModel (unit tt unitRec vec vecElim add void voidRec belowStep below idElim unitCtors
  U0 numC zeroC succC unitC ttC vecC addC unitRecC vecElimC voidC belowStepC belowC)

variable (lv : LevelExpr Nat)

/-! ## The rows -/

/-- The recursor of the numbers at an argument spine. -/
abbrev numRecAt {n : Nat} (p z s t : Tower.Tm n) : Tower.Tm n :=
  .app (.app (.app (.app (.const numRec) p) z) s) t

/-- The identity eliminator at an argument spine. -/
abbrev idElimAt {n : Nat} (a₀ a₁ a₂ a₃ a₄ a₅ : Tower.Tm n) : Tower.Tm n :=
  .app (.app (.app (.app (.app (.app (.const idElim) a₀) a₁) a₂) a₃) a₄) a₅

/-- **The fourteen rows of the package.** -/
def vectorEquations : SchemaTable Tower.Head :=
  [⟨3, (numRecAt (.var 2) (.var 1) (.var 0) zeroC, .var 1)⟩,
   ⟨4, (numRecAt (.var 3) (.var 2) (.var 1) (succC (.var 0)),
      .app (.app (.var 1) (.var 0)) (numRecAt (.var 3) (.var 2) (.var 1) (.var 0)))⟩,
   ⟨2, (unitRecC (.var 1) (.var 0) ttC, .var 0)⟩,
   ⟨1, (vecC (.var 0) zeroC, unitC)⟩,
   ⟨2, (vecC (.var 1) (succC (.var 0)), .sigma (.var 1) (vecC (.var 2) (.var 1)))⟩,
   ⟨5, (vecElimC (.var 4) (.var 3) (.var 2) (.var 1) zeroC (.var 0),
      unitRecC (.lam (.app (.app (.var 4) zeroC) (.var 0))) (.var 2) (.var 0))⟩,
   ⟨6, (vecElimC (.var 5) (.var 4) (.var 3) (.var 2) (succC (.var 1)) (.var 0),
      .app (.app (.app (.app (.var 2) (.var 1)) (.fst (.var 0))) (.snd (.var 0)))
        (vecElimC (.var 5) (.var 4) (.var 3) (.var 2) (.var 1) (.snd (.var 0))))⟩,
   ⟨1, (addC zeroC (.var 0), .var 0)⟩,
   ⟨2, (addC (succC (.var 1)) (.var 0), succC (addC (.var 1) (.var 0)))⟩,
   ⟨1, (belowStepC (.var 0) zeroC, unitC)⟩,
   ⟨2, (belowStepC (.var 1) (succC (.var 0)), .app (.var 1) (.var 0))⟩,
   ⟨1, (belowC zeroC (.var 0), voidC)⟩,
   ⟨2, (belowC (succC (.var 1)) (.var 0), belowStepC (.app (.const below) (.var 1)) (.var 0))⟩,
   ⟨6, (idElimAt (.var 5) (.var 4) (.var 3) (.var 2) (.var 1) (.refl (.var 0)), .var 2)⟩]

theorem listed (i : Nat) (h : i < vectorEquations.length) {arity : Nat} {left right : Tower.Tm arity}
    (same : vectorEquations[i] = ⟨arity, (left, right)⟩) : vectorEquations.family left right := by
  change (⟨arity, (left, right)⟩ : Σ arity : Nat, Tower.Tm arity × Tower.Tm arity) ∈ vectorEquations
  rw [← same]
  exact List.getElem_mem h

/-- **Every instance of a row is a step of the package.** -/
theorem vector_sound {arity n : Nat} {left right : Tower.Tm arity}
    (rule : vectorEquations.family left right) (σ : Sub Tower.Head arity n) :
    (TowerVectorsModel.rules lv).computation.step (subst σ left) (subst σ right) := by
  change (⟨arity, (left, right)⟩ : Σ arity : Nat, Tower.Tm arity × Tower.Tm arity) ∈ vectorEquations
    at rule
  simp only [vectorEquations, List.mem_cons, List.not_mem_nil, or_false] at rule
  rcases rule with same | same | same | same | same | same | same | same | same | same | same | same |
    same | same <;> cases same
  · exact RootComputation.step_unionAll TowerVectorsModel.mem_numRec
      ⟨σ 2, [σ 1, σ 0], 0, zero, [], [], σ 1, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact RootComputation.step_unionAll TowerVectorsModel.mem_numRec
      ⟨σ 3, [σ 2, σ 1], 1, succ, [.recursive], [σ 0], σ 1, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact TowerVectorsModel.unit_iota_step lv (σ 1) (σ 0)
  · exact (TowerVectorsModel.vecDeclared_rules lv).vecZero (σ 0)
  · exact (TowerVectorsModel.vecDeclared_rules lv).vecSucc (σ 1) (σ 0)
  · exact TowerVectorsModel.elim_zero_step lv (σ 4) (σ 3) (σ 2) (σ 1) (σ 0)
  · exact TowerVectorsModel.elim_succ_step lv (σ 5) (σ 4) (σ 3) (σ 2) (σ 1) (σ 0)
  · exact TowerVectorsModel.add_zero_step lv (σ 0)
  · exact TowerVectorsModel.add_succ_step lv (σ 1) (σ 0)
  · exact RootComputation.step_unionAll TowerVectorsModel.mem_belowStep
      ⟨zero, [], consSub zeroC (consSub (σ 0) fun i => Fin.elim0 i), [], TowerNumbersModel.mem_zero,
        rfl, rfl, rfl⟩
  · exact RootComputation.step_unionAll TowerVectorsModel.mem_belowStep
      ⟨succ, [.recursive], consSub (succC (σ 0)) (consSub (σ 1) fun i => Fin.elim0 i), [σ 0],
        TowerNumbersModel.mem_succ, rfl, rfl, rfl⟩
  · exact RootComputation.step_unionAll TowerVectorsModel.mem_below
      ⟨zero, [], consSub (σ 0) (consSub zeroC fun i => Fin.elim0 i), [], TowerNumbersModel.mem_zero,
        rfl, rfl, rfl⟩
  · exact RootComputation.step_unionAll TowerVectorsModel.mem_below
      ⟨succ, [.recursive], consSub (σ 0) (consSub (succC (σ 1)) fun i => Fin.elim0 i), [σ 1],
        TowerNumbersModel.mem_succ, rfl, rfl, rfl⟩
  · exact RootComputation.step_unionAll TowerVectorsModel.mem_idElim
      ⟨σ 5, σ 4, σ 3, σ 2, σ 1, σ 0, rfl, rfl⟩

/-- **Every step of the package is an instance of a row.** -/
theorem vector_cover {n : Nat} {l r : Tower.Tm n}
    (step : (TowerVectorsModel.rules lv).computation.step l r) :
    ∃ (arity : Nat) (left right : Tower.Tm arity) (σ : Sub Tower.Head arity n),
      vectorEquations.family left right ∧ subst σ left = l ∧ subst σ right = r := by
  obtain ⟨entry, mem, h⟩ := RootComputation.unionAll_step step
  simp only [TowerVectorsModel.computations, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- the recursor of the numbers
    obtain ⟨p, ms, i, k, fields, args, m, hms, hi, has, hm, rfl, rfl⟩ := h
    rcases ms with _ | ⟨z, _ | ⟨s, _ | ⟨_, _⟩⟩⟩
    · cases hms
    · cases hms
    · rcases i with _ | _ | i
      · simp only [ctors, List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hi
        obtain ⟨rfl, rfl⟩ := hi
        rcases args with _ | ⟨_, _⟩
        · simp only [List.getElem?_cons_zero, Option.some.injEq] at hm
          subst hm
          exact ⟨3, _, _, consSub s (consSub z (consSub p Fin.elim0)), listed 0 (by decide) rfl, rfl,
            rfl⟩
        · cases has
      · simp only [ctors, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
          Prod.mk.injEq] at hi
        obtain ⟨rfl, rfl⟩ := hi
        rcases args with _ | ⟨a, _ | ⟨_, _⟩⟩
        · cases has
        · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hm
          subst hm
          exact ⟨4, _, _, consSub a (consSub s (consSub z (consSub p Fin.elim0))),
            listed 1 (by decide) rfl, rfl, rfl⟩
        · cases has
      · cases hi
    · cases hms
  · -- the recursor of the unit type
    obtain ⟨p, ms, i, k, fields, args, m, hms, hi, has, hm, rfl, rfl⟩ := h
    rcases ms with _ | ⟨d, _ | ⟨_, _⟩⟩
    · cases hms
    · rcases i with _ | i
      · simp only [unitCtors, List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hi
        obtain ⟨rfl, rfl⟩ := hi
        rcases args with _ | ⟨_, _⟩
        · simp only [List.getElem?_cons_zero, Option.some.injEq] at hm
          subst hm
          exact ⟨2, _, _, consSub d (consSub p Fin.elim0), listed 2 (by decide) rfl, rfl, rfl⟩
        · cases has
      · cases hi
    · cases hms
  · -- `vec`
    obtain ⟨k, fields, σ, as, memk, has, rfl, rfl⟩ := h
    simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at memk
    rcases memk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases as with _ | ⟨_, _⟩
      · exact ⟨1, _, _, matchSub 1 0 [] 0 σ, listed 3 (by decide) rfl, rfl, rfl⟩
      · cases has
    · rcases as with _ | ⟨x, _ | ⟨_, _⟩⟩
      · cases has
      · exact ⟨2, _, _, matchSub 1 1 [x] 0 σ, listed 4 (by decide) rfl, rfl, rfl⟩
      · cases has
  · -- the eliminator of vectors
    obtain ⟨k, fields, σ, as, memk, has, rfl, rfl⟩ := h
    simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at memk
    rcases memk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases as with _ | ⟨_, _⟩
      · exact ⟨5, _, _, matchSub 4 0 [] 1 σ, listed 5 (by decide) rfl, rfl, rfl⟩
      · cases has
    · rcases as with _ | ⟨x, _ | ⟨_, _⟩⟩
      · cases has
      · exact ⟨6, _, _, matchSub 4 1 [x] 1 σ, listed 6 (by decide) rfl, rfl, rfl⟩
      · cases has
  · -- addition
    obtain ⟨k, fields, σ, as, memk, has, rfl, rfl⟩ := h
    simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at memk
    rcases memk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases as with _ | ⟨_, _⟩
      · exact ⟨1, _, _, matchSub 0 0 [] 1 σ, listed 7 (by decide) rfl, rfl, rfl⟩
      · cases has
    · rcases as with _ | ⟨x, _ | ⟨_, _⟩⟩
      · cases has
      · exact ⟨2, _, _, matchSub 0 1 [x] 1 σ, listed 8 (by decide) rfl, rfl, rfl⟩
      · cases has
  · -- `below-step`
    obtain ⟨k, fields, σ, as, memk, has, rfl, rfl⟩ := h
    simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at memk
    rcases memk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases as with _ | ⟨_, _⟩
      · exact ⟨1, _, _, matchSub 1 0 [] 0 σ, listed 9 (by decide) rfl, rfl, rfl⟩
      · cases has
    · rcases as with _ | ⟨x, _ | ⟨_, _⟩⟩
      · cases has
      · exact ⟨2, _, _, matchSub 1 1 [x] 0 σ, listed 10 (by decide) rfl, rfl, rfl⟩
      · cases has
  · -- `below`
    obtain ⟨k, fields, σ, as, memk, has, rfl, rfl⟩ := h
    simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at memk
    rcases memk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases as with _ | ⟨_, _⟩
      · exact ⟨1, _, _, matchSub 0 0 [] 1 σ, listed 11 (by decide) rfl, rfl, rfl⟩
      · cases has
    · rcases as with _ | ⟨x, _ | ⟨_, _⟩⟩
      · cases has
      · exact ⟨2, _, _, matchSub 0 1 [x] 1 σ, listed 12 (by decide) rfl, rfl, rfl⟩
      · cases has
  · -- the identity eliminator at reflexivity
    obtain ⟨a₀, a₁, a₂, method, a₄, a₅, rfl, rfl⟩ := h
    exact ⟨6, _, _, consSub a₅ (consSub a₄ (consSub r (consSub a₂ (consSub a₁ (consSub a₀ Fin.elim0))))),
      listed 13 (by decide) rfl, rfl, rfl⟩

/-- **The package's computation, presented by its rows.** -/
def vectorPresentation : SchemaPresentation (TowerVectorsModel.rules lv) where
  schema := vectorEquations.family
  sound := vector_sound lv
  cover := vector_cover lv

/-! ## The rows pass the syntactic check -/

/-- The defined constants: the eight computing constants of the package. -/
def vectorDefined (name : DeclName) : Bool :=
  name == numRec || name == unitRec || name == vec || name == vecElim || name == add ||
    name == belowStep || name == below || name == idElim

/-- Their arities. -/
def vectorArity (name : DeclName) : Nat :=
  if name == numRec then 4
  else if name == unitRec then 3
  else if name == vecElim || name == idElim then 6
  else 2

/-- **The fourteen rows pass the declaration-time check.** -/
theorem vector_check : DeclarationCheck.checkTable vectorDefined vectorArity vectorEquations = true := by
  decide

/-- **The package as a definition by constructor patterns.** -/
def vectorConstructors : ConstructorPresentation (TowerVectorsModel.rules lv) where
  presentation := vectorPresentation lv
  system := DeclarationCheck.checkedSystem vector_check
  same _ _ := Iff.rfl
  symmetric := LevelTower.headEq_symmetric

/-! ## The package is qualified -/

/-- **The declared constants are semantic for the algorithmic equality, at every valuation**: the
declarations of the package hold at every generic equality with the laws. -/
theorem algorithmicConstantsAt (valuation : Nat → Nat) :
    SemanticConstants (algorithmicSetting (TowerVectorsModel.setting lv valuation)) :=
  TowerVectorsModel.constantsAt lv valuation
    (algorithmicSetting_laws (S := TowerVectorsModel.setting lv valuation)
      (TowerVectorsModel.laws lv valuation) (TowerVectorsModel.constants lv valuation)
      (TowerVectorsModel.roots lv) (TowerVectorsModel.heads lv) (TowerVectorsModel.algebra lv))

/-- **The package with vectors and their eliminator is qualified, at every level and every
valuation**: every field is a proved fact of the package. -/
theorem vectors_qualified (valuation : Nat → Nat) : Qualified (TowerVectorsModel.setting lv valuation) where
  laws := TowerVectorsModel.laws lv valuation
  constructors := ⟨vectorConstructors lv⟩
  constants := TowerVectorsModel.constants lv valuation
  roots := TowerVectorsModel.roots lv
  heads := TowerVectorsModel.heads lv
  algebra := TowerVectorsModel.algebra lv
  algorithmicConstants := algorithmicConstantsAt lv valuation
  decideHeads := TowerVectorsConversion.decideHeads lv

/-! ## Its consequences, by instantiation -/

/-- The qualified setting at the zero valuation. -/
theorem vq : Qualified (TowerVectorsModel.setting lv fun _ => 0) := vectors_qualified lv fun _ => 0

/-- **Church–Rosser** with β, the projections and the fourteen rows. -/
theorem vectors_churchRosser : ChurchRosser (TowerVectorsModel.rules lv) :=
  (vq lv).churchRosser

/-- **Unique normal forms**: convertible terms without computation steps are equal. -/
theorem vectors_eq_of_normal {n : Nat} {a b : Tower.Tm n}
    (normalA : ConstructorSystem.Normal (TowerVectorsModel.rules lv) a)
    (normalB : ConstructorSystem.Normal (TowerVectorsModel.rules lv) b)
    (conversion : Conv (TowerVectorsModel.rules lv).headEq a b (TowerVectorsModel.rules lv).computation) :
    a = b :=
  (vq lv).eq_of_normal normalA normalB conversion

/-- **Subject reduction of every reduction**, under binders included: reducts keep the type and are
typed-equal to the term. -/
theorem vectors_subjectReduction {n : Nat} {Γ : Ctx Tower.Head n}
    (formed : CtxFormed (TowerVectorsModel.rules lv) Γ) {t t' T : Tower.Tm n}
    (red : Reduces (TowerVectorsModel.rules lv) t t') (typing : Typed (TowerVectorsModel.rules lv) Γ t T) :
    Typed (TowerVectorsModel.rules lv) Γ t' T ∧ Equal (TowerVectorsModel.rules lv) Γ t t' T :=
  (vq lv).subjectReduction formed red typing

/-- **Conservativity**: convertible typed terms of one type are typed-equal. -/
theorem vectors_conv_toEqual {n : Nat} {Γ : Ctx Tower.Head n}
    (formed : CtxFormed (TowerVectorsModel.rules lv) Γ) {a b T : Tower.Tm n}
    (conversion : Conv (TowerVectorsModel.rules lv).headEq a b (TowerVectorsModel.rules lv).computation)
    (typedA : Typed (TowerVectorsModel.rules lv) Γ a T) (typedB : Typed (TowerVectorsModel.rules lv) Γ b T) :
    Equal (TowerVectorsModel.rules lv) Γ a b T :=
  (vq lv).conv_toEqual formed conversion typedA typedB

/-- **Weak-head normal forms** of typed terms. -/
theorem vectors_whnf {n : Nat} {Γ : Ctx Tower.Head n} {t A : Tower.Tm n}
    (typing : Typed (TowerVectorsModel.rules lv) Γ t A) (formed : CtxFormed (TowerVectorsModel.rules lv) Γ) :
    ∃ nf, WhRed (TowerVectorsModel.rules lv) TowerVectorsModel.roles t nf ∧
      Whnf (TowerVectorsModel.rules lv) TowerVectorsModel.roles nf :=
  (vq lv).whnf typing formed

/-- **The typed equality with η is what the type-directed algorithm derives**, on typed terms. -/
theorem vectors_algorithm_iff {n : Nat} {Γ : Ctx Tower.Head n}
    (formed : CtxFormed (TowerVectorsModel.rules lv) Γ) {t u A : Tower.Tm n}
    (typedT : Typed (TowerVectorsModel.rules lv) Γ t A) (typedU : Typed (TowerVectorsModel.rules lv) Γ u A) :
    Algorithm (TowerVectorsModel.rules lv) (.compare Γ t u A) ↔ Equal (TowerVectorsModel.rules lv) Γ t u A :=
  (vq lv).algorithm_iff formed typedT typedU

/-- **Typed conversion is decided**, without the choice axiom. -/
theorem vectors_decide {n : Nat} {Γ : Ctx Tower.Head n}
    (formed : CtxFormed (TowerVectorsModel.rules lv) Γ) {t u A : Tower.Tm n}
    (typedT : Typed (TowerVectorsModel.rules lv) Γ t A) (typedU : Typed (TowerVectorsModel.rules lv) Γ u A) :
    Equal (TowerVectorsModel.rules lv) Γ t u A ∨ ¬ Equal (TowerVectorsModel.rules lv) Γ t u A :=
  (vq lv).decide formed typedT typedU

/-- **A firing's answer has the call's type**: the answer reached by the package's computation from a
typed call is typed at the call's type and typed-equal to it. -/
theorem vectors_answer_typed {n : Nat} {Γ : Ctx Tower.Head n}
    (formed : CtxFormed (TowerVectorsModel.rules lv) Γ) {t v A : Tower.Tm n}
    (typing : Typed (TowerVectorsModel.rules lv) Γ t A) (answer : Answer (TowerVectorsModel.rules lv) t v) :
    Typed (TowerVectorsModel.rules lv) Γ v A ∧ Equal (TowerVectorsModel.rules lv) Γ t v A :=
  (vq lv).answer_typed formed typing answer

end NativeTypesOnTheStep.Computing.Vectors

#print axioms NativeTypesOnTheStep.Computing.Vectors.vector_sound
#print axioms NativeTypesOnTheStep.Computing.Vectors.vector_cover
#print axioms NativeTypesOnTheStep.Computing.Vectors.vectorPresentation
#print axioms NativeTypesOnTheStep.Computing.Vectors.vector_check
#print axioms NativeTypesOnTheStep.Computing.Vectors.vectorConstructors
#print axioms NativeTypesOnTheStep.Computing.Vectors.algorithmicConstantsAt
#print axioms NativeTypesOnTheStep.Computing.Vectors.vectors_qualified
#print axioms NativeTypesOnTheStep.Computing.Vectors.vectors_churchRosser
#print axioms NativeTypesOnTheStep.Computing.Vectors.vectors_eq_of_normal
#print axioms NativeTypesOnTheStep.Computing.Vectors.vectors_subjectReduction
#print axioms NativeTypesOnTheStep.Computing.Vectors.vectors_conv_toEqual
#print axioms NativeTypesOnTheStep.Computing.Vectors.vectors_whnf
#print axioms NativeTypesOnTheStep.Computing.Vectors.vectors_algorithm_iff
#print axioms NativeTypesOnTheStep.Computing.Vectors.vectors_decide
#print axioms NativeTypesOnTheStep.Computing.Vectors.vectors_answer_typed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
