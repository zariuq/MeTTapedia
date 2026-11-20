import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Vectors.Checker.AppendGround
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Vectors.NotUnitary

/-!
# Coverage, stated and not solved

The checker decides each row; it does not ask whether the rows **cover** the declared domain. In this
package the vector family is recursive: its length decides its constructor (`vec A zero ≡ unit`, whose
only value is `nil`; `vec A (succ k) ≡ Σ A (vec A k)`, whose values are `cons a v`). So coverage is read
**by the index**:

* **syntactically** (`CoversAt d j`): at the vector parameter `j`, every length `n` is accepted by the
  pattern of some row (`nil` accepts zero, `cons` the successors, a variable every length);
* **on the step** (`append_fires`): every written-out ground call fires some row: there is a closed
  instance of that row's frame, solving what its patterns teach, whose arguments are the call's.

**append covers** (`append_covers`, `append_fires`). With the guarantee of the checker and the
termination of obligation 6 (`append_ground`), every ground call of append fires a row and answers.

**A partial function** (`headDef`, one row at `cons`): admitted row by row (`head_admitted`), and not
covering (`head_not_covers`): at length zero no row fires (`head_zero_no_firing`), so a ground call
there has no answer by the rows (`head_zero_unanswered`). **What the guarantee says about it**: every
answer by the rows has the declared type, and at length zero there is none; the guarantee is vacuous
there. It promises types, not answers: progress needs coverage, and termination.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing.Vectors.Checker

open _root_.CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open TowerVectorsModel (U0 numC zeroC succC ttC vecC addC)
open ProgrammingOnTheStep.IndexedFamilies.Eliminator (level1 pkg D numType)

/-! ## Coverage by the index -/

/-- The lengths a pattern at a vector parameter accepts. -/
def Pattern.acceptsLength : Pattern → Nat → Bool
  | .var, _ => true
  | .nil, n => n == 0
  | .cons _ _, n => n != 0
  | _, _ => false

/-- **Coverage by the index** at the vector parameter `j`: every length is accepted by some row. -/
def CoversAt (d : Definition) (j : Nat) : Prop :=
  ∀ n : Nat, ∃ r ∈ d.rows, ∃ p, r.patterns[j]? = some p ∧ p.acceptsLength n = true

/-- **append covers its vector argument.** -/
theorem append_covers : CoversAt appendDef 3 := by
  intro n
  cases n with
  | zero => exact ⟨nilRow, List.mem_cons_self .., .nil, rfl, rfl⟩
  | succ k => exact ⟨consRow, List.mem_cons_of_mem _ (List.mem_singleton_self _), .cons .var .var, rfl, rfl⟩

/-- **head does not**: no row accepts length zero. -/
theorem head_not_covers : ¬ CoversAt headDef 2 := by
  intro covers
  obtain ⟨r, member, p, at', accepts⟩ := covers 0
  obtain rfl := List.mem_singleton.mp member
  obtain rfl := Option.some.inj at'
  cases accepts

/-! ## append fires a row on every written-out ground call -/

/-- The arguments of the ground call `append A |xs| |ys| xs ys`. -/
def appendArgs (A : Tower.Tm 0) (xs ys : List (Tower.Tm 0)) : Sub Tower.Head 5 0 :=
  consSub (written ys) (consSub (written xs) (consSub (numeral ys.length) (consSub (numeral xs.length)
    (consSub A fun i => Fin.elim0 i))))

/-- The raw pass of append's nil row: the function, `A`, `m`, `ys : vec A m`; the index `n` last, taught
`zero`. -/
abbrev nilAcc : Acc :=
  ⟨4, .snoc (.snoc (.snoc (.snoc .nil appendDef.type) U0) numC) (vecC (.var 1) (.var 0)),
    [some (.var 0), some ttC, some (.var 1), none, some (.var 2)], [some 0, some 1, none, some 2], some zeroC⟩

theorem nil_raw : rawPass appendDef nilRow = some nilAcc := by decide +kernel

/-- The closed values of the nil row's frame before the index. -/
def nilValues (A : Tower.Tm 0) (ys : List (Tower.Tm 0)) : Sub Tower.Head 4 0 :=
  consSub (written ys) (consSub (numeral ys.length) (consSub A
    (consSub TowerVectorsPrograms.appendProgram fun i => Fin.elim0 i)))

/-- The closed values of the cons row's frame before the index. -/
def consValuesOf (A a : Tower.Tm 0) (rest ys : List (Tower.Tm 0)) : Sub Tower.Head 7 0 :=
  consSub (written ys) (consSub (written rest) (consSub a (consSub (numeral rest.length)
    (consSub (numeral ys.length) (consSub A (consSub TowerVectorsPrograms.appendProgram fun i => Fin.elim0 i))))))

/-- **Every written-out ground call of append fires a row**: the nil row at length zero, the cons row
at the successors. -/
theorem append_fires {A : Tower.Tm 0} (tA : Typed pkg .nil A U0) {xs ys : List (Tower.Tm 0)}
    (typedXs : ∀ a ∈ xs, Typed pkg .nil a A) (typedYs : ∀ a ∈ ys, Typed pkg .nil a A) :
    ∃ r ∈ appendDef.rows, ∃ e, elaborate 16 appendDef r = some e ∧
      ∃ c : GroundCall e, c.args = appendArgs A xs ys := by
  have m₀ : SubstMor pkg (.nil : Ctx Tower.Head 0) .nil fun i => Fin.elim0 i := fun i => Fin.elim0 i
  cases xs with
  | nil =>
      obtain ⟨e, elaborated⟩ : ∃ e, elaborate 16 appendDef nilRow = some e :=
        Option.isSome_iff_exists.mp (by decide +kernel)
      have elaborated' := elaborated
      obtain ⟨formed, tv, l, rfl⟩ := elaborate_index elaborated nil_raw rfl
      have values : SubstMor pkg nilAcc.frame .nil (nilValues A ys) :=
        Normalization.SubstMor.cons (Normalization.SubstMor.cons (Normalization.SubstMor.cons
          (Normalization.SubstMor.cons m₀ (TowerVectorsPrograms.appendProgram_typed level1)) tA)
          (numeral_typed ys.length)) (written_typed tA typedYs)
      let inst : empty pkg ⟶ extend (prefixOf nilAcc formed) (numType _) :=
        pair (⟨nilValues A ys, values⟩ : empty pkg ⟶ prefixOf nilAcc formed) ⟨zeroC, D.zero_typed⟩
      have solves : (frames vecS.levels).Models inst
          [Elimination.definition (prefixOf nilAcc formed) ⟨zeroC, tv⟩] := by
        intro eq member
        obtain rfl := List.mem_singleton.mp member
        exact (equivalent_iff vecS.levels _ _).mpr
          ⟨⟨_, LevelTower.IsUniverse.sort _, .refl D.num_typed⟩, .refl D.zero_typed⟩
      refine ⟨nilRow, List.mem_cons_self .., _, elaborated', ⟨inst, solves⟩, ?_⟩
      funext x
      fin_cases x <;> rfl
  | cons a rest =>
      obtain ⟨e, elaborated⟩ : ∃ e, elaborate 16 appendDef consRow = some e :=
        Option.isSome_iff_exists.mp (by decide +kernel)
      have elaborated' := elaborated
      obtain ⟨formed, tv, l, rfl⟩ := elaborate_index elaborated cons_raw rfl
      have tRest := written_typed tA fun b member => typedXs b (List.mem_cons_of_mem _ member)
      have values : SubstMor pkg consAcc.frame .nil (consValuesOf A a rest ys) :=
        Normalization.SubstMor.cons (Normalization.SubstMor.cons (Normalization.SubstMor.cons
          (Normalization.SubstMor.cons (Normalization.SubstMor.cons (Normalization.SubstMor.cons
            (Normalization.SubstMor.cons m₀ (TowerVectorsPrograms.appendProgram_typed level1)) tA)
            (numeral_typed ys.length)) (numeral_typed rest.length)) (typedXs a (List.mem_cons_self ..)))
          tRest) (written_typed tA typedYs)
      let inst : empty pkg ⟶ extend (prefixOf consAcc formed) (numType _) :=
        pair (⟨consValuesOf A a rest ys, values⟩ : empty pkg ⟶ prefixOf consAcc formed)
          ⟨succC (numeral rest.length), D.succ_typed (numeral_typed rest.length)⟩
      have solves : (frames vecS.levels).Models inst
          [Elimination.definition (prefixOf consAcc formed) ⟨succC (.var 3), tv⟩] := by
        intro eq member
        obtain rfl := List.mem_singleton.mp member
        exact (equivalent_iff vecS.levels _ _).mpr
          ⟨⟨_, LevelTower.IsUniverse.sort _, .refl D.num_typed⟩, .refl (D.succ_typed (numeral_typed rest.length))⟩
      refine ⟨consRow, List.mem_cons_of_mem _ (List.mem_singleton_self _), _, elaborated', ⟨inst, solves⟩, ?_⟩
      funext x
      fin_cases x <;> rfl

/-- **Every written-out ground call of append fires a row and answers**, at its declared type. -/
theorem append_fires_and_answers {A : Tower.Tm 0} (tA : Typed pkg .nil A U0) {xs ys : List (Tower.Tm 0)}
    (typedXs : ∀ a ∈ xs, Typed pkg .nil a A) (typedYs : ∀ a ∈ ys, Typed pkg .nil a A)
    (normalXs : ∀ a ∈ xs, ConstructorSystem.Normal pkg a) (normalYs : ∀ a ∈ ys, ConstructorSystem.Normal pkg a) :
    (∃ r ∈ appendDef.rows, ∃ e, elaborate 16 appendDef r = some e ∧ ∃ c : GroundCall e, c.args = appendArgs A xs ys) ∧
      Answer pkg (appendCall A xs ys) (written (xs ++ ys)) ∧
      Typed pkg .nil (written (xs ++ ys)) (vecC A (addC (numeral xs.length) (numeral ys.length))) :=
  ⟨append_fires tA typedXs typedYs, (append_ground tA typedXs typedYs normalXs normalYs).1,
    (append_ground tA typedXs typedYs normalXs normalYs).2.2.1⟩

/-! ## head: admitted, and partial -/

/-- The raw pass of head's row: the function, `A`, `k`, `a : A`, `w : vec A k`; the index `n` last,
taught `succ k`. -/
abbrev headAcc : Acc :=
  ⟨5, .snoc (.snoc (.snoc (.snoc (.snoc .nil headDef.type) U0) numC) (.var 1)) (vecC (.var 2) (.var 1)),
    [some (.pair (.var 1) (.var 0)), none, some (.var 3)], [some 0, some 1, some 2, none, some 3],
    some (succC (.var 2))⟩

theorem head_raw : rawPass headDef headRow = some headAcc := by decide +kernel

/-- **At length zero head's row does not fire**: no closed instance of its frame solving `n ≐ succ k`
gives the call the length `zero`. -/
theorem head_zero_no_firing {fuel : Nat} {e : Elaborated headDef.arity} (elaborated : elaborate fuel headDef headRow = some e)
    (c : GroundCall e) : c.args (1 : Fin 3) ≠ zeroC := by
  obtain ⟨formed, tv, l, rfl⟩ := elaborate_index elaborated head_raw rfl
  intro zero
  have solved := (equivalent_iff vecS.levels _ _).mp (c.solves _ (List.mem_singleton_self _))
  have atZero : c.inst.substitution 0 = zeroC := zero
  have equal : Equal pkg .nil (c.inst.substitution 0) (succC (c.inst.substitution 3)) numC := solved.2
  rw [atZero] at equal
  exact num_ctor_apart .nil TowerNumbersModel.mem_zero TowerNumbersModel.mem_succ TowerNumbersModel.zero_ne_succ
    (as := []) (bs := [c.inst.substitution 3]) equal

/-- **So a ground call of head at length zero has no answer by the rows**: the guarantee of the checker
holds there vacuously. -/
theorem head_zero_unanswered {args : Sub Tower.Head headDef.arity 0} (zero : args (1 : Fin 3) = zeroC) (v : Tower.Tm 0) :
    ¬ RowAnswer 16 headDef headDef.rows args v := by
  rintro ⟨r, member, e, elaborated, c, same, -⟩
  obtain rfl := List.mem_singleton.mp member
  exact head_zero_no_firing elaborated c (by rw [same]; exact zero)

/-- **The guarantee for head**: every answer of a ground call by its row has the declared type. With
`head_zero_unanswered`, this is all it says: types, not answers. -/
theorem head_guarantee {args : Sub Tower.Head headDef.arity 0} {v : Tower.Tm 0}
    (answer : RowAnswer 16 headDef headDef.rows args v) : Typed pkg .nil v (subst args headDef.result) :=
  (guarantee head_admitted (fun _ member => member) answer).1

end NativeTypesOnTheStep.Computing.Vectors.Checker

#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.append_covers
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.head_not_covers
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.nil_raw
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.append_fires
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.append_fires_and_answers
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.head_raw
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.head_zero_no_firing
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.head_zero_unanswered
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.head_guarantee

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
