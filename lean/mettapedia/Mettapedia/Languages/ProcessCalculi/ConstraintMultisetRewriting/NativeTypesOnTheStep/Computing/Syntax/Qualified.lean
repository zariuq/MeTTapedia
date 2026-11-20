import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.DeclarationCheck
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.TwoReadings
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerSyntaxEval

/-!
# The package of typed syntax is qualified

The package `TowerSyntaxModel.rules lv` (numbers, unit, empty, Booleans, object types, untyped
expressions with their recursors; addition, the zero test, the computed equations of the index, the
value type, the typing relation, the transports and the recursion principle of typed expressions) is
**qualified** for the definitional reading at every level and valuation (`syntax_qualified`).

* Its computation is exactly the instances of thirty-six rows (`syntaxEquations`, `syntax_sound`,
  `syntax_cover`): two of the numbers' recursor, one of the unit type's, two each of the Booleans' and
  the object types' recursors, five of the expressions' recursor, two each of addition, the zero test,
  `is-num`, `is-bool`, `val`, `at-num`, `at-bool`, five of the typing relation and five of the recursion
  principle. The empty type's recursor has no row.
* The rows pass the declaration-time check (`syntax_check`): defined heads at their arities over linear
  constructor patterns, covered right sides, no two left sides unifying.
* Every other field is a proved fact of the package (`TowerSyntaxModel`).

Consequences by instantiation: Church–Rosser (`syntax_churchRosser`), unique normal forms, subject
reduction of every reduction, weak-head normal forms, and the typed equality with η decided by the
type-directed algorithm (`syntax_algorithm_iff`, `syntax_decide`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing.Syntax

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open AlgebraicSchema AlgebraicParallel ConversionCoherence
open ConstructorSystem (ConstructorPresentation)
open TowerNumbersModel (num zero succ numRec ctors u)
open TowerVectorsModel (unit tt unitRec void voidRec add unitCtors U0 numC zeroC succC unitC ttC addC
  unitRecC voidC voidRecC)
open TowerSyntaxModel

variable (lv : LevelExpr Nat)

/-! ## The rows -/

abbrev numRecAt {n : Nat} (p z s t : Tower.Tm n) : Tower.Tm n :=
  .app (.app (.app (.app (.const numRec) p) z) s) t
abbrev tyRecAt {n : Nat} (p x y t : Tower.Tm n) : Tower.Tm n :=
  .app (.app (.app (.app (.const tyRec) p) x) y) t
abbrev rawRecAt {n : Nat} (p m₁ m₂ m₃ m₄ m₅ t : Tower.Tm n) : Tower.Tm n :=
  .app (.app (.app (.app (.app (.app (.app (.const rawRec) p) m₁) m₂) m₃) m₄) m₅) t

/-- **The thirty-six rows of the package.** -/
def syntaxEquations : SchemaTable Tower.Head :=
  [⟨3, (numRecAt (.var 2) (.var 1) (.var 0) zeroC, .var 1)⟩,
   ⟨4, (numRecAt (.var 3) (.var 2) (.var 1) (succC (.var 0)),
      .app (.app (.var 1) (.var 0)) (numRecAt (.var 3) (.var 2) (.var 1) (.var 0)))⟩,
   ⟨2, (unitRecC (.var 1) (.var 0) ttC, .var 0)⟩,
   ⟨3, (boolRecC (.var 2) (.var 1) (.var 0) btrueC, .var 1)⟩,
   ⟨3, (boolRecC (.var 2) (.var 1) (.var 0) bfalseC, .var 0)⟩,
   ⟨3, (tyRecAt (.var 2) (.var 1) (.var 0) tnumC, .var 1)⟩,
   ⟨3, (tyRecAt (.var 2) (.var 1) (.var 0) tboolC, .var 0)⟩,
   ⟨7, (rawRecAt (.var 6) (.var 5) (.var 4) (.var 3) (.var 2) (.var 1) (rnumC (.var 0)), .app (.var 5) (.var 0))⟩,
   ⟨7, (rawRecAt (.var 6) (.var 5) (.var 4) (.var 3) (.var 2) (.var 1) (rboolC (.var 0)), .app (.var 4) (.var 0))⟩,
   ⟨8, (rawRecAt (.var 7) (.var 6) (.var 5) (.var 4) (.var 3) (.var 2) (raddC (.var 1) (.var 0)),
      .app (.app (.app (.app (.var 4) (.var 1)) (.var 0))
        (rawRecAt (.var 7) (.var 6) (.var 5) (.var 4) (.var 3) (.var 2) (.var 1)))
        (rawRecAt (.var 7) (.var 6) (.var 5) (.var 4) (.var 3) (.var 2) (.var 0)))⟩,
   ⟨9, (rawRecAt (.var 8) (.var 7) (.var 6) (.var 5) (.var 4) (.var 3) (rifC (.var 2) (.var 1) (.var 0)),
      .app (.app (.app (.app (.app (.app (.var 4) (.var 2)) (.var 1)) (.var 0))
        (rawRecAt (.var 8) (.var 7) (.var 6) (.var 5) (.var 4) (.var 3) (.var 2)))
        (rawRecAt (.var 8) (.var 7) (.var 6) (.var 5) (.var 4) (.var 3) (.var 1)))
        (rawRecAt (.var 8) (.var 7) (.var 6) (.var 5) (.var 4) (.var 3) (.var 0)))⟩,
   ⟨7, (rawRecAt (.var 6) (.var 5) (.var 4) (.var 3) (.var 2) (.var 1) (rzeroC (.var 0)),
      .app (.app (.var 1) (.var 0)) (rawRecAt (.var 6) (.var 5) (.var 4) (.var 3) (.var 2) (.var 1) (.var 0)))⟩,
   ⟨1, (addC zeroC (.var 0), .var 0)⟩,
   ⟨2, (addC (succC (.var 1)) (.var 0), succC (addC (.var 1) (.var 0)))⟩,
   ⟨0, (isZeroC zeroC, btrueC)⟩,
   ⟨1, (isZeroC (succC (.var 0)), bfalseC)⟩,
   ⟨0, (isNumC tnumC, unitC)⟩,
   ⟨0, (isNumC tboolC, voidC)⟩,
   ⟨0, (isBoolC tnumC, voidC)⟩,
   ⟨0, (isBoolC tboolC, unitC)⟩,
   ⟨0, (valC tnumC, numC)⟩,
   ⟨0, (valC tboolC, boolC)⟩,
   ⟨2, (typingC (rnumC (.var 1)) (.var 0), isNumC (.var 0))⟩,
   ⟨2, (typingC (rboolC (.var 1)) (.var 0), isBoolC (.var 0))⟩,
   ⟨3, (typingC (raddC (.var 2) (.var 1)) (.var 0),
      .sigma (isNumC (.var 0)) (.sigma (typingC (.var 3) tnumC) (typingC (.var 3) tnumC)))⟩,
   ⟨4, (typingC (rifC (.var 3) (.var 2) (.var 1)) (.var 0),
      .sigma (typingC (.var 3) tboolC) (.sigma (typingC (.var 3) (.var 1)) (typingC (.var 3) (.var 2))))⟩,
   ⟨2, (typingC (rzeroC (.var 1)) (.var 0), .sigma (isBoolC (.var 0)) (typingC (.var 2) tnumC))⟩,
   ⟨3, (atNumC (.var 2) (.var 1) tnumC (.var 0), .var 1)⟩,
   ⟨3, (atNumC (.var 2) (.var 1) tboolC (.var 0), voidRecC (.lam (.app (.var 3) tboolC)) (.var 0))⟩,
   ⟨3, (atBoolC (.var 2) (.var 1) tnumC (.var 0), voidRecC (.lam (.app (.var 3) tnumC)) (.var 0))⟩,
   ⟨3, (atBoolC (.var 2) (.var 1) tboolC (.var 0), .var 1)⟩,
   ⟨9, (synRecC (.var 8) (.var 7) (.var 6) (.var 5) (.var 4) (.var 3) (rnumC (.var 2)) (.var 1) (.var 0),
      atNumC (.var 8) (.app (.var 7) (.var 2)) (.var 1) (.var 0))⟩,
   ⟨9, (synRecC (.var 8) (.var 7) (.var 6) (.var 5) (.var 4) (.var 3) (rboolC (.var 2)) (.var 1) (.var 0),
      atBoolC (.var 8) (.app (.var 6) (.var 2)) (.var 1) (.var 0))⟩,
   ⟨10, (synRecC (.var 9) (.var 8) (.var 7) (.var 6) (.var 5) (.var 4) (raddC (.var 3) (.var 2)) (.var 1) (.var 0),
      atNumC (.var 9)
        (.app (.app (.var 6) (synRecC (.var 9) (.var 8) (.var 7) (.var 6) (.var 5) (.var 4) (.var 3) tnumC
          (.fst (.snd (.var 0)))))
          (synRecC (.var 9) (.var 8) (.var 7) (.var 6) (.var 5) (.var 4) (.var 2) tnumC (.snd (.snd (.var 0)))))
        (.var 1) (.fst (.var 0)))⟩,
   ⟨11, (synRecC (.var 10) (.var 9) (.var 8) (.var 7) (.var 6) (.var 5) (rifC (.var 4) (.var 3) (.var 2)) (.var 1)
        (.var 0),
      .app (.app (.app (.app (.var 6) (.var 1))
        (synRecC (.var 10) (.var 9) (.var 8) (.var 7) (.var 6) (.var 5) (.var 4) tboolC (.fst (.var 0))))
        (synRecC (.var 10) (.var 9) (.var 8) (.var 7) (.var 6) (.var 5) (.var 3) (.var 1) (.fst (.snd (.var 0)))))
        (synRecC (.var 10) (.var 9) (.var 8) (.var 7) (.var 6) (.var 5) (.var 2) (.var 1) (.snd (.snd (.var 0)))))⟩,
   ⟨9, (synRecC (.var 8) (.var 7) (.var 6) (.var 5) (.var 4) (.var 3) (rzeroC (.var 2)) (.var 1) (.var 0),
      atBoolC (.var 8) (.app (.var 3) (synRecC (.var 8) (.var 7) (.var 6) (.var 5) (.var 4) (.var 3) (.var 2) tnumC
        (.snd (.var 0)))) (.var 1) (.fst (.var 0)))⟩]

theorem syntaxEquations_length : syntaxEquations.length = 36 := rfl

theorem listed (i : Nat) (h : i < syntaxEquations.length) {arity : Nat} {left right : Tower.Tm arity}
    (same : syntaxEquations[i] = ⟨arity, (left, right)⟩) : syntaxEquations.family left right := by
  change (⟨arity, (left, right)⟩ : Σ arity : Nat, Tower.Tm arity × Tower.Tm arity) ∈ syntaxEquations
  rw [← same]
  exact List.getElem_mem h

/-! ## The rows are the computation -/

/-- **Every instance of a row is a step of the package.** -/
theorem syntax_sound {arity n : Nat} {left right : Tower.Tm arity}
    (rule : syntaxEquations.family left right) (σ : Sub Tower.Head arity n) :
    (rules lv).computation.step (subst σ left) (subst σ right) := by
  change (⟨arity, (left, right)⟩ : Σ arity : Nat, Tower.Tm arity × Tower.Tm arity) ∈ syntaxEquations at rule
  simp only [syntaxEquations, List.mem_cons, List.not_mem_nil, or_false] at rule
  rcases rule with same | same | same | same | same | same | same | same | same | same | same | same |
    same | same | same | same | same | same | same | same | same | same | same | same | same | same |
    same | same | same | same | same | same | same | same | same | same <;> cases same
  · exact RootComputation.step_unionAll mem_numRec
      ⟨σ 2, [σ 1, σ 0], 0, zero, [], [], σ 1, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact RootComputation.step_unionAll mem_numRec
      ⟨σ 3, [σ 2, σ 1], 1, succ, [.recursive], [σ 0], σ 1, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact RootComputation.step_unionAll mem_unitRec
      ⟨σ 1, [σ 0], 0, tt, [], [], σ 0, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact RootComputation.step_unionAll mem_boolRec
      ⟨σ 2, [σ 1, σ 0], 0, btrue, [], [], σ 1, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact RootComputation.step_unionAll mem_boolRec
      ⟨σ 2, [σ 1, σ 0], 1, bfalse, [], [], σ 0, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact RootComputation.step_unionAll mem_tyRec
      ⟨σ 2, [σ 1, σ 0], 0, tnum, [], [], σ 1, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact RootComputation.step_unionAll mem_tyRec
      ⟨σ 2, [σ 1, σ 0], 1, tbool, [], [], σ 0, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact RootComputation.step_unionAll mem_rawRec
      ⟨σ 6, [σ 5, σ 4, σ 3, σ 2, σ 1], 0, rnum, [.closed numT], [σ 0], σ 5, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact RootComputation.step_unionAll mem_rawRec
      ⟨σ 6, [σ 5, σ 4, σ 3, σ 2, σ 1], 1, rbool, [.closed boolT], [σ 0], σ 4, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact RootComputation.step_unionAll mem_rawRec
      ⟨σ 7, [σ 6, σ 5, σ 4, σ 3, σ 2], 2, radd, [.recursive, .recursive], [σ 1, σ 0], σ 4, rfl, rfl, rfl, rfl,
        rfl, rfl⟩
  · exact RootComputation.step_unionAll mem_rawRec
      ⟨σ 8, [σ 7, σ 6, σ 5, σ 4, σ 3], 3, rif, [.recursive, .recursive, .recursive], [σ 2, σ 1, σ 0], σ 4, rfl,
        rfl, rfl, rfl, rfl, rfl⟩
  · exact RootComputation.step_unionAll mem_rawRec
      ⟨σ 6, [σ 5, σ 4, σ 3, σ 2, σ 1], 4, rzero, [.recursive], [σ 0], σ 1, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact add_zero_step lv (σ 0)
  · exact add_succ_step lv (σ 1) (σ 0)
  · exact RootComputation.step_unionAll mem_isZero
      ⟨zero, [], consSub zeroC fun i => Fin.elim0 i, [], TowerNumbersModel.mem_zero, rfl, rfl, rfl⟩
  · exact RootComputation.step_unionAll mem_isZero
      ⟨succ, [.recursive], consSub (succC (σ 0)) fun i => Fin.elim0 i, [σ 0], TowerNumbersModel.mem_succ, rfl,
        rfl, rfl⟩
  · exact isNum_tnum_step lv
  · exact isNum_tbool_step lv
  · exact isBool_tnum_step lv
  · exact isBool_tbool_step lv
  · exact val_tnum_step lv
  · exact val_tbool_step lv
  · exact typing_rnum_step lv (σ 1) (σ 0)
  · exact typing_rbool_step lv (σ 1) (σ 0)
  · exact typing_radd_step lv (σ 2) (σ 1) (σ 0)
  · exact typing_rif_step lv (σ 3) (σ 2) (σ 1) (σ 0)
  · exact typing_rzero_step lv (σ 1) (σ 0)
  · exact atNum_tnum_step lv (σ 2) (σ 1) (σ 0)
  · exact RootComputation.step_unionAll mem_atNum
      ⟨tbool, [], consSub (σ 0) (consSub tboolC (consSub (σ 1) (consSub (σ 2) fun i => Fin.elim0 i))), [],
        mem_tbool, rfl, rfl, rfl⟩
  · exact RootComputation.step_unionAll mem_atBool
      ⟨tnum, [], consSub (σ 0) (consSub tnumC (consSub (σ 1) (consSub (σ 2) fun i => Fin.elim0 i))), [],
        mem_tnum, rfl, rfl, rfl⟩
  · exact atBool_tbool_step lv (σ 2) (σ 1) (σ 0)
  · exact synRec_rnum_step lv (σ 8) (σ 7) (σ 6) (σ 5) (σ 4) (σ 3) (σ 2) (σ 1) (σ 0)
  · exact synRec_rbool_step lv (σ 8) (σ 7) (σ 6) (σ 5) (σ 4) (σ 3) (σ 2) (σ 1) (σ 0)
  · exact synRec_radd_step lv (σ 9) (σ 8) (σ 7) (σ 6) (σ 5) (σ 4) (σ 3) (σ 2) (σ 1) (σ 0)
  · exact synRec_rif_step lv (σ 10) (σ 9) (σ 8) (σ 7) (σ 6) (σ 5) (σ 4) (σ 3) (σ 2) (σ 1) (σ 0)
  · exact synRec_rzero_step lv (σ 8) (σ 7) (σ 6) (σ 5) (σ 4) (σ 3) (σ 2) (σ 1) (σ 0)

/-- **Every step of the package is an instance of a row.** -/
theorem syntax_cover {n : Nat} {l r : Tower.Tm n} (step : (rules lv).computation.step l r) :
    ∃ (arity : Nat) (left right : Tower.Tm arity) (σ : Sub Tower.Head arity n),
      syntaxEquations.family left right ∧ subst σ left = l ∧ subst σ right = r := by
  obtain ⟨entry, mem, h⟩ := RootComputation.unionAll_step step
  simp only [computations, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- the numbers' recursor
    obtain ⟨p, ms, i, k, fields, args, m, hms, hi, has, hm, rfl, rfl⟩ := h
    rcases ms with _ | ⟨z, _ | ⟨s, _ | ⟨_, _⟩⟩⟩ <;> try cases hms
    rcases i with _ | _ | i
    · simp only [ctors, List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hi
      obtain ⟨rfl, rfl⟩ := hi
      rcases args with _ | ⟨_, _⟩ <;> try cases has
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hm
      subst hm
      exact ⟨3, _, _, consSub s (consSub z (consSub p Fin.elim0)), listed 0 (by decide) rfl, rfl, rfl⟩
    · simp only [ctors, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
        Prod.mk.injEq] at hi
      obtain ⟨rfl, rfl⟩ := hi
      rcases args with _ | ⟨a, _ | ⟨_, _⟩⟩ <;> try cases has
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hm
      subst hm
      exact ⟨4, _, _, consSub a (consSub s (consSub z (consSub p Fin.elim0))), listed 1 (by decide) rfl, rfl, rfl⟩
    · simp [ctors] at hi
  · -- the unit type's recursor
    obtain ⟨p, ms, i, k, fields, args, m, hms, hi, has, hm, rfl, rfl⟩ := h
    rcases ms with _ | ⟨d, _ | ⟨_, _⟩⟩ <;> try cases hms
    rcases i with _ | i
    · simp only [unitCtors, List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hi
      obtain ⟨rfl, rfl⟩ := hi
      rcases args with _ | ⟨_, _⟩ <;> try cases has
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hm
      subst hm
      exact ⟨2, _, _, consSub d (consSub p Fin.elim0), listed 2 (by decide) rfl, rfl, rfl⟩
    · simp [unitCtors] at hi
  · -- the empty type's recursor has no case
    obtain ⟨p, ms, i, k, fields, args, m, hms, hi, has, hm, rfl, rfl⟩ := h
    simp at hi
  · -- the Booleans' recursor
    obtain ⟨p, ms, i, k, fields, args, m, hms, hi, has, hm, rfl, rfl⟩ := h
    rcases ms with _ | ⟨x, _ | ⟨y, _ | ⟨_, _⟩⟩⟩ <;> try cases hms
    rcases i with _ | _ | i
    · simp only [boolCtors, List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hi
      obtain ⟨rfl, rfl⟩ := hi
      rcases args with _ | ⟨_, _⟩ <;> try cases has
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hm
      subst hm
      exact ⟨3, _, _, consSub y (consSub x (consSub p Fin.elim0)), listed 3 (by decide) rfl, rfl, rfl⟩
    · simp only [boolCtors, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
        Prod.mk.injEq] at hi
      obtain ⟨rfl, rfl⟩ := hi
      rcases args with _ | ⟨_, _⟩ <;> try cases has
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hm
      subst hm
      exact ⟨3, _, _, consSub y (consSub x (consSub p Fin.elim0)), listed 4 (by decide) rfl, rfl, rfl⟩
    · simp [boolCtors] at hi
  · -- the object types' recursor
    obtain ⟨p, ms, i, k, fields, args, m, hms, hi, has, hm, rfl, rfl⟩ := h
    rcases ms with _ | ⟨x, _ | ⟨y, _ | ⟨_, _⟩⟩⟩ <;> try cases hms
    rcases i with _ | _ | i
    · simp only [tyCtors, List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hi
      obtain ⟨rfl, rfl⟩ := hi
      rcases args with _ | ⟨_, _⟩ <;> try cases has
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hm
      subst hm
      exact ⟨3, _, _, consSub y (consSub x (consSub p Fin.elim0)), listed 5 (by decide) rfl, rfl, rfl⟩
    · simp only [tyCtors, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
        Prod.mk.injEq] at hi
      obtain ⟨rfl, rfl⟩ := hi
      rcases args with _ | ⟨_, _⟩ <;> try cases has
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hm
      subst hm
      exact ⟨3, _, _, consSub y (consSub x (consSub p Fin.elim0)), listed 6 (by decide) rfl, rfl, rfl⟩
    · simp [tyCtors] at hi
  · -- the untyped expressions' recursor
    obtain ⟨p, ms, i, k, fields, args, m, hms, hi, has, hm, rfl, rfl⟩ := h
    rcases ms with _ | ⟨m₁, _ | ⟨m₂, _ | ⟨m₃, _ | ⟨m₄, _ | ⟨m₅, _ | ⟨_, _⟩⟩⟩⟩⟩⟩ <;> try cases hms
    rcases i with _ | _ | _ | _ | _ | i
    · simp only [rawCtors, List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hi
      obtain ⟨rfl, rfl⟩ := hi
      rcases args with _ | ⟨x, _ | ⟨_, _⟩⟩ <;> try cases has
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hm
      subst hm
      exact ⟨7, _, _, consSub x (consSub m₅ (consSub m₄ (consSub m₃ (consSub m₂ (consSub m₁ (consSub p Fin.elim0)))))),
        listed 7 (by decide) rfl, rfl, rfl⟩
    · simp only [rawCtors, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
        Prod.mk.injEq] at hi
      obtain ⟨rfl, rfl⟩ := hi
      rcases args with _ | ⟨x, _ | ⟨_, _⟩⟩ <;> try cases has
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hm
      subst hm
      exact ⟨7, _, _, consSub x (consSub m₅ (consSub m₄ (consSub m₃ (consSub m₂ (consSub m₁ (consSub p Fin.elim0)))))),
        listed 8 (by decide) rfl, rfl, rfl⟩
    · simp only [rawCtors, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
        Prod.mk.injEq] at hi
      obtain ⟨rfl, rfl⟩ := hi
      rcases args with _ | ⟨x, _ | ⟨y, _ | ⟨_, _⟩⟩⟩ <;> try cases has
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hm
      subst hm
      exact ⟨8, _, _, consSub y (consSub x (consSub m₅ (consSub m₄ (consSub m₃ (consSub m₂ (consSub m₁
        (consSub p Fin.elim0))))))), listed 9 (by decide) rfl, rfl, rfl⟩
    · simp only [rawCtors, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
        Prod.mk.injEq] at hi
      obtain ⟨rfl, rfl⟩ := hi
      rcases args with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨_, _⟩⟩⟩⟩ <;> try cases has
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hm
      subst hm
      exact ⟨9, _, _, consSub z (consSub y (consSub x (consSub m₅ (consSub m₄ (consSub m₃ (consSub m₂ (consSub m₁
        (consSub p Fin.elim0)))))))), listed 10 (by decide) rfl, rfl, rfl⟩
    · simp only [rawCtors, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
        Prod.mk.injEq] at hi
      obtain ⟨rfl, rfl⟩ := hi
      rcases args with _ | ⟨x, _ | ⟨_, _⟩⟩ <;> try cases has
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hm
      subst hm
      exact ⟨7, _, _, consSub x (consSub m₅ (consSub m₄ (consSub m₃ (consSub m₂ (consSub m₁ (consSub p Fin.elim0)))))),
        listed 11 (by decide) rfl, rfl, rfl⟩
    · simp [rawCtors] at hi
  · -- addition
    obtain ⟨k, fields, σ, as, memk, has, rfl, rfl⟩ := h
    simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at memk
    rcases memk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases as with _ | ⟨_, _⟩ <;> try cases has
      exact ⟨1, _, _, matchSub 0 0 [] 1 σ, listed 12 (by decide) rfl, rfl, rfl⟩
    · rcases as with _ | ⟨x, _ | ⟨_, _⟩⟩ <;> try cases has
      exact ⟨2, _, _, matchSub 0 1 [x] 1 σ, listed 13 (by decide) rfl, rfl, rfl⟩
  · -- the zero test
    obtain ⟨k, fields, σ, as, memk, has, rfl, rfl⟩ := h
    simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at memk
    rcases memk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases as with _ | ⟨_, _⟩ <;> try cases has
      exact ⟨0, _, _, matchSub 0 0 [] 0 σ, listed 14 (by decide) rfl, rfl, rfl⟩
    · rcases as with _ | ⟨x, _ | ⟨_, _⟩⟩ <;> try cases has
      exact ⟨1, _, _, matchSub 0 1 [x] 0 σ, listed 15 (by decide) rfl, rfl, rfl⟩
  · -- `is-num`
    obtain ⟨k, fields, σ, as, memk, has, rfl, rfl⟩ := h
    simp only [tyCtors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at memk
    rcases memk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases as with _ | ⟨_, _⟩ <;> try cases has
    · exact ⟨0, _, _, matchSub 0 0 [] 0 σ, listed 16 (by decide) rfl, rfl, rfl⟩
    · exact ⟨0, _, _, matchSub 0 0 [] 0 σ, listed 17 (by decide) rfl, rfl, rfl⟩
  · -- `is-bool`
    obtain ⟨k, fields, σ, as, memk, has, rfl, rfl⟩ := h
    simp only [tyCtors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at memk
    rcases memk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases as with _ | ⟨_, _⟩ <;> try cases has
    · exact ⟨0, _, _, matchSub 0 0 [] 0 σ, listed 18 (by decide) rfl, rfl, rfl⟩
    · exact ⟨0, _, _, matchSub 0 0 [] 0 σ, listed 19 (by decide) rfl, rfl, rfl⟩
  · -- the value type
    obtain ⟨k, fields, σ, as, memk, has, rfl, rfl⟩ := h
    simp only [tyCtors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at memk
    rcases memk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases as with _ | ⟨_, _⟩ <;> try cases has
    · exact ⟨0, _, _, matchSub 0 0 [] 0 σ, listed 20 (by decide) rfl, rfl, rfl⟩
    · exact ⟨0, _, _, matchSub 0 0 [] 0 σ, listed 21 (by decide) rfl, rfl, rfl⟩
  · -- the typing relation
    obtain ⟨k, fields, σ, as, memk, has, rfl, rfl⟩ := h
    simp only [rawCtors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at memk
    rcases memk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases as with _ | ⟨x, _ | ⟨_, _⟩⟩ <;> try cases has
      exact ⟨2, _, _, matchSub 0 1 [x] 1 σ, listed 22 (by decide) rfl, rfl, rfl⟩
    · rcases as with _ | ⟨x, _ | ⟨_, _⟩⟩ <;> try cases has
      exact ⟨2, _, _, matchSub 0 1 [x] 1 σ, listed 23 (by decide) rfl, rfl, rfl⟩
    · rcases as with _ | ⟨x, _ | ⟨y, _ | ⟨_, _⟩⟩⟩ <;> try cases has
      exact ⟨3, _, _, matchSub 0 2 [x, y] 1 σ, listed 24 (by decide) rfl, rfl, rfl⟩
    · rcases as with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨_, _⟩⟩⟩⟩ <;> try cases has
      exact ⟨4, _, _, matchSub 0 3 [x, y, z] 1 σ, listed 25 (by decide) rfl, rfl, rfl⟩
    · rcases as with _ | ⟨x, _ | ⟨_, _⟩⟩ <;> try cases has
      exact ⟨2, _, _, matchSub 0 1 [x] 1 σ, listed 26 (by decide) rfl, rfl, rfl⟩
  · -- `at-num`
    obtain ⟨k, fields, σ, as, memk, has, rfl, rfl⟩ := h
    simp only [tyCtors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at memk
    rcases memk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases as with _ | ⟨_, _⟩ <;> try cases has
    · exact ⟨3, _, _, matchSub 2 0 [] 1 σ, listed 27 (by decide) rfl, rfl, rfl⟩
    · exact ⟨3, _, _, matchSub 2 0 [] 1 σ, listed 28 (by decide) rfl, rfl, rfl⟩
  · -- `at-bool`
    obtain ⟨k, fields, σ, as, memk, has, rfl, rfl⟩ := h
    simp only [tyCtors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at memk
    rcases memk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases as with _ | ⟨_, _⟩ <;> try cases has
    · exact ⟨3, _, _, matchSub 2 0 [] 1 σ, listed 29 (by decide) rfl, rfl, rfl⟩
    · exact ⟨3, _, _, matchSub 2 0 [] 1 σ, listed 30 (by decide) rfl, rfl, rfl⟩
  · -- the recursion principle
    obtain ⟨k, fields, σ, as, memk, has, rfl, rfl⟩ := h
    simp only [rawCtors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at memk
    rcases memk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases as with _ | ⟨x, _ | ⟨_, _⟩⟩ <;> try cases has
      exact ⟨9, _, _, matchSub 6 1 [x] 2 σ, listed 31 (by decide) rfl, rfl, rfl⟩
    · rcases as with _ | ⟨x, _ | ⟨_, _⟩⟩ <;> try cases has
      exact ⟨9, _, _, matchSub 6 1 [x] 2 σ, listed 32 (by decide) rfl, rfl, rfl⟩
    · rcases as with _ | ⟨x, _ | ⟨y, _ | ⟨_, _⟩⟩⟩ <;> try cases has
      exact ⟨10, _, _, matchSub 6 2 [x, y] 2 σ, listed 33 (by decide) rfl, rfl, rfl⟩
    · rcases as with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨_, _⟩⟩⟩⟩ <;> try cases has
      exact ⟨11, _, _, matchSub 6 3 [x, y, z] 2 σ, listed 34 (by decide) rfl, rfl, rfl⟩
    · rcases as with _ | ⟨x, _ | ⟨_, _⟩⟩ <;> try cases has
      exact ⟨9, _, _, matchSub 6 1 [x] 2 σ, listed 35 (by decide) rfl, rfl, rfl⟩

/-- **The package's computation, presented by its rows.** -/
def syntaxPresentation : SchemaPresentation (rules lv) where
  schema := syntaxEquations.family
  sound := syntax_sound lv
  cover := syntax_cover lv

/-! ## The rows pass the declaration-time check -/

/-- The defined constants: the fourteen computing constants with rows. -/
def syntaxDefined (name : DeclName) : Bool :=
  name == numRec || name == unitRec || name == boolRec || name == tyRec || name == rawRec || name == add ||
    name == isZero || name == isNum || name == isBool || name == val || name == TowerSyntaxModel.typing ||
    name == atNum || name == atBool || name == synRec

/-- Their arities. -/
def syntaxArity (name : DeclName) : Nat :=
  if name == numRec || name == boolRec || name == tyRec || name == atNum || name == atBool then 4
  else if name == unitRec then 3
  else if name == rawRec then 7
  else if name == synRec then 9
  else if name == add || name == TowerSyntaxModel.typing then 2
  else 1

/-- **The thirty-six rows pass the declaration-time check**, by kernel evaluation. -/
theorem syntax_check : DeclarationCheck.checkTable syntaxDefined syntaxArity syntaxEquations = true := by
  decide +kernel

/-- **The package as a definition by constructor patterns.** -/
def syntaxConstructors : ConstructorPresentation (rules lv) where
  presentation := syntaxPresentation lv
  system := DeclarationCheck.checkedSystem syntax_check
  same _ _ := Iff.rfl
  symmetric := LevelTower.headEq_symmetric

/-! ## The package is qualified -/

/-- Head equality of the package is decided. -/
theorem decideHeads (h h' : Tower.Head) : HeadSame (rules lv) h h' ∨ ¬ HeadSame (rules lv) h h' := by
  rcases Decidable.em (Tower.HeadEq h h') with same | different
  · exact .inl (.inr same)
  · rcases Decidable.em (h = h') with equal | unequal
    · exact .inl (.inl equal)
    · exact .inr fun same => same.elim unequal different

/-- **The declared constants are semantic for the algorithmic equality.** -/
theorem algorithmicConstantsAt (valuation : Nat → Nat) :
    SemanticConstants (algorithmicSetting (TowerSyntaxModel.setting lv valuation)) :=
  TowerSyntaxModel.constantsAt lv valuation
    (algorithmicSetting_laws (S := TowerSyntaxModel.setting lv valuation)
      (TowerSyntaxModel.laws lv valuation) (TowerSyntaxModel.constants lv valuation)
      (TowerSyntaxModel.roots lv) (TowerSyntaxModel.heads lv) (TowerSyntaxModel.algebra lv))

/-- **The package of typed syntax is qualified, at every level and every valuation.** -/
theorem syntax_qualified (valuation : Nat → Nat) : Qualified (TowerSyntaxModel.setting lv valuation) where
  laws := TowerSyntaxModel.laws lv valuation
  constructors := ⟨syntaxConstructors lv⟩
  constants := TowerSyntaxModel.constants lv valuation
  roots := TowerSyntaxModel.roots lv
  heads := TowerSyntaxModel.heads lv
  algebra := TowerSyntaxModel.algebra lv
  algorithmicConstants := algorithmicConstantsAt lv valuation
  decideHeads := decideHeads lv

/-! ## Its consequences, by instantiation -/

theorem sq : Qualified (TowerSyntaxModel.setting lv fun _ => 0) := syntax_qualified lv fun _ => 0

/-- **Church–Rosser** with β, the projections and the thirty-six rows. -/
theorem syntax_churchRosser : ChurchRosser (rules lv) := (sq lv).churchRosser

/-- **Unique normal forms.** -/
theorem syntax_eq_of_normal {n : Nat} {a b : Tower.Tm n} (normalA : ConstructorSystem.Normal (rules lv) a)
    (normalB : ConstructorSystem.Normal (rules lv) b)
    (conversion : Conv (rules lv).headEq a b (rules lv).computation) : a = b :=
  (sq lv).eq_of_normal normalA normalB conversion

/-- **Subject reduction of every reduction.** -/
theorem syntax_subjectReduction {n : Nat} {Γ : Ctx Tower.Head n} (formed : CtxFormed (rules lv) Γ)
    {t t' T : Tower.Tm n} (red : Reduces (rules lv) t t') (typing : Typed (rules lv) Γ t T) :
    Typed (rules lv) Γ t' T ∧ Equal (rules lv) Γ t t' T :=
  (sq lv).subjectReduction formed red typing

/-- **Weak-head normal forms** of typed terms. -/
theorem syntax_whnf {n : Nat} {Γ : Ctx Tower.Head n} {t A : Tower.Tm n} (typing : Typed (rules lv) Γ t A)
    (formed : CtxFormed (rules lv) Γ) : ∃ nf, WhRed (rules lv) roles t nf ∧ Whnf (rules lv) roles nf :=
  (sq lv).whnf typing formed

/-- **The typed equality with η is what the type-directed algorithm derives.** -/
theorem syntax_algorithm_iff {n : Nat} {Γ : Ctx Tower.Head n} (formed : CtxFormed (rules lv) Γ)
    {t u A : Tower.Tm n} (typedT : Typed (rules lv) Γ t A) (typedU : Typed (rules lv) Γ u A) :
    Algorithm (rules lv) (.compare Γ t u A) ↔ Equal (rules lv) Γ t u A :=
  (sq lv).algorithm_iff formed typedT typedU

/-- **Typed conversion is decided**: a proved disjunction (its proof uses the choice axiom through the
cover proof of the rows). -/
theorem syntax_decide {n : Nat} {Γ : Ctx Tower.Head n} (formed : CtxFormed (rules lv) Γ) {t u A : Tower.Tm n}
    (typedT : Typed (rules lv) Γ t A) (typedU : Typed (rules lv) Γ u A) :
    Equal (rules lv) Γ t u A ∨ ¬ Equal (rules lv) Γ t u A :=
  (sq lv).decide formed typedT typedU

end NativeTypesOnTheStep.Computing.Syntax

#print axioms NativeTypesOnTheStep.Computing.Syntax.syntax_sound
#print axioms NativeTypesOnTheStep.Computing.Syntax.syntax_cover
#print axioms NativeTypesOnTheStep.Computing.Syntax.syntax_check
#print axioms NativeTypesOnTheStep.Computing.Syntax.syntaxConstructors
#print axioms NativeTypesOnTheStep.Computing.Syntax.algorithmicConstantsAt
#print axioms NativeTypesOnTheStep.Computing.Syntax.syntax_qualified
#print axioms NativeTypesOnTheStep.Computing.Syntax.syntax_churchRosser
#print axioms NativeTypesOnTheStep.Computing.Syntax.syntax_subjectReduction
#print axioms NativeTypesOnTheStep.Computing.Syntax.syntax_algorithm_iff
#print axioms NativeTypesOnTheStep.Computing.Syntax.syntax_decide

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
