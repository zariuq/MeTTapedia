import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Vectors.Checker.Acceptance

/-!
# What a checked definition guarantees

**A ground call answered by a row** (`GroundCall`): a closed instance of the row's frame (the function at
a closed term of its declared type, every pattern variable and the call's index at closed terms) that
solves what the row's patterns teach. Its arguments are the declared parameters' images at the instance
(`GroundCall.args`). **An answer of a ground call by the function's rows** (`RowAnswer`): one of the
function's declared rows fires on the call, and the package's firings take the made row to a normal form
(`Answer`): a firing of the step is a root step at a call row, and the rest is the package's reduction.

**The guarantee** (`guarantee`). With `vectors_qualified`: if the checker admits a definition, and the
function's declared rows are among the definition's rows (`only`, **an assumption about the declaration**:
the checker does not see rows declared elsewhere), then every answer by the rows of a ground call has the
call's declared type, is typed-equal to the made row there, and is the made row's conversion normal form,
the only one. The proof: the fired row is typed after its match (soundness of yes), so the made row is typed
at the declared type at the instance, which solves what the match teaches; reduction preserves typing,
and on the qualified package the answer by firings is the conversion normal form.

**Not vacuous** (`guarantee_witness`): the cons row of `append`, fired on `append num 1 1 [2] [3]` with
the recursive call answered by the tree's eliminator program, answers `[2, 3]`, at `vec num (add 1 1)`.

**The hypothesis is needed** (`second_row_breaks`): with the unchecked row `append xs ys = xs` declared
as a second row, the ground call `append num 0 1 [] [3]` has the answer `[]`, which is not of the call's
declared type `vec num (add 0 1)`.

**Read the guarantee with its hypotheses.** It is about one firing: the recursive calls inside a fired
row are calls of the function variable, here instantiated by a closed term of the declared type. That the
rows themselves define a function whose every ground call answers at its type needs the package extended
by the rows to be qualified (confluence by the declaration check, typed right sides by this checker,
termination); that extension is not built here.
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
open ConversionCoherence (StepStar)
open TowerVectorsModel (U0 numC zeroC succC ttC vecC addC)
open ProgrammingOnTheStep.IndexedFamilies.Eliminator (level1 pkg D numType)
open ProgrammingOnTheStep.IndexedFamilies.ClosedCalls (one two three single twoThree)

/-! ## Ground calls and their answers by rows -/

/-- **A ground call answered by a row**: a closed instance of its frame solving what its patterns teach. -/
structure GroundCall {n : Nat} (e : Elaborated n) where
  inst : empty pkg ⟶ e.frame
  solves : (frames vecS.levels).Models inst e.tells

/-- The call's arguments: the declared parameters' images at the instance. -/
def GroundCall.args {n : Nat} {e : Elaborated n} (c : GroundCall e) : Sub Tower.Head n 0 :=
  fun x => subst c.inst.substitution (e.args x)

/-- The made row at the instance: what the firing makes, before the package computes. -/
def GroundCall.made {n : Nat} {e : Elaborated n} (c : GroundCall e) : Tower.Tm 0 :=
  subst c.inst.substitution e.made.code

/-- **An answer of a ground call by the function's declared rows**: a declared row fires on the call,
and the package's firings take its made row to a normal form. -/
def RowAnswer (fuel : Nat) (d : Definition) (declared : List Row) (args : Sub Tower.Head d.arity 0)
    (v : Tower.Tm 0) : Prop :=
  ∃ r ∈ declared, ∃ e, elaborate fuel d r = some e ∧ ∃ c : GroundCall e, c.args = args ∧ Answer pkg c.made v

/-! ## The guarantee -/

/-- **What a checked definition guarantees**: if the definition is admitted and the function's declared
rows are among its rows, every answer of a ground call by the rows has the call's declared type, is
typed-equal to the made row, and is its conversion normal form. -/
theorem guarantee {fuel : Nat} {d : Definition} (admitted : checkDefinition fuel d = .admitted)
    {declared : List Row} (only : ∀ r ∈ declared, r ∈ d.rows) {args : Sub Tower.Head d.arity 0}
    {v : Tower.Tm 0} (answer : RowAnswer fuel d declared args v) :
    Typed pkg .nil v (subst args d.result) ∧
      ∃ made : Tower.Tm 0, Equal pkg .nil made v (subst args d.result) ∧
        Conv pkg.headEq made v pkg.computation ∧ ConstructorSystem.Normal pkg v ∧
          ∀ v', Answer pkg made v' → v' = v := by
  obtain ⟨r, member, e, elaborated, c, sameArgs, fired⟩ := answer
  obtain ⟨e', elaborated', -, typedAfter⟩ := checkDefinition_admitted admitted r (only r member)
  rw [elaborated] at elaborated'
  obtain rfl := Option.some.inj elaborated'
  have atInstance : Typed pkg (empty pkg).raw (subst c.inst.substitution e.made.code)
      (e.made.type.reindex c.inst).code :=
    (typedAfterMatch_iff vecS.levels e.tells e.made).mp typedAfter (empty pkg) c.inst c.solves
  have declaredType : (e.made.type.reindex c.inst).code = subst args d.result := by
    show subst c.inst.substitution e.made.type.code = subst args d.result
    rw [made_type_code elaborated, subst_subComp, ← sameArgs]
    rfl
  rw [declaredType] at atInstance
  obtain ⟨typed, equal⟩ := vectors_answer_typed level1 .nil atInstance fired
  exact ⟨typed, c.made, equal, ((vectors_answer_iff level1).mp fired).1, fired.2,
    fun v' other => vectors_answer_unique level1 other fired⟩

/-! ## Not vacuous: the cons row of `append` on `append num 1 1 [2] [3]` -/

/-- The raw pass of append's cons row: the function, `A`, `m`, `k`, `a : A`, `v : vec A k`,
`ys : vec A m`; the call's index `n` comes last, taught `succ k`. -/
abbrev consAcc : Acc :=
  ⟨7, .snoc (.snoc (.snoc (.snoc (.snoc (.snoc (.snoc .nil appendDef.type) U0) numC) numC) (.var 2))
      (vecC (.var 3) (.var 1))) (vecC (.var 4) (.var 3)),
    [some (.var 0), some (.pair (.var 2) (.var 1)), some (.var 4), none, some (.var 5)],
    [some 0, some 1, some 2, some 3, some 4, none, some 5], some (succC (.var 3))⟩

theorem cons_raw : rawPass appendDef consRow = some consAcc := by decide +kernel

/-- The closed values of the frame before the index: `appendProgram`, `num`, `1`, `0`, `2`, `[]`, `[3]`. -/
def consValues : Sub Tower.Head 7 0 :=
  consSub (single three) (consSub ttC (consSub two (consSub zeroC (consSub one (consSub numC
    (consSub TowerVectorsPrograms.appendProgram fun i => Fin.elim0 i))))))

theorem consValues_typed : SubstMor pkg consAcc.frame .nil consValues := by
  have m₀ : SubstMor pkg (.nil : Ctx Tower.Head 0) .nil fun i => Fin.elim0 i := fun i => Fin.elim0 i
  have tNum : Typed pkg .nil numC U0 := D.num_typed
  have tZero : Typed pkg .nil zeroC numC := D.zero_typed
  have tOne : Typed pkg .nil one numC := D.succ_typed D.zero_typed
  have tTwo : Typed pkg .nil two numC := D.succ_typed tOne
  have tThree : Typed pkg .nil three numC := D.succ_typed tTwo
  have tNil : Typed pkg .nil ttC (vecC numC zeroC) := D.nil_typed tNum
  have tSingle : Typed pkg .nil (single three) (vecC numC one) := D.cons_typed tNum tZero tThree tNil
  exact Normalization.SubstMor.cons (Normalization.SubstMor.cons (Normalization.SubstMor.cons
    (Normalization.SubstMor.cons (Normalization.SubstMor.cons (Normalization.SubstMor.cons
      (Normalization.SubstMor.cons m₀ (TowerVectorsPrograms.appendProgram_typed level1)) tNum) tOne) tZero) tTwo)
    tNil) tSingle

/-- **A ground call of append's cons row**: the closed values, and the index at `1`. -/
def consInstance (formed : CtxFormed pkg consAcc.frame) : empty pkg ⟶ extend (prefixOf consAcc formed) (numType _) :=
  pair (⟨consValues, consValues_typed⟩ : empty pkg ⟶ prefixOf consAcc formed) ⟨one, D.succ_typed D.zero_typed⟩

/-- **It solves what the match teaches**: `n ≐ succ k` at `n ↦ 1`, `k ↦ 0`. -/
theorem consInstance_solves (formed : CtxFormed pkg consAcc.frame) (tv : Typed pkg consAcc.frame (succC (.var 3)) numC) :
    (frames vecS.levels).Models (consInstance formed)
      [Elimination.definition (prefixOf consAcc formed) ⟨succC (.var 3), tv⟩] := by
  intro eq member
  obtain rfl := List.mem_singleton.mp member
  exact (equivalent_iff vecS.levels _ _).mpr
    ⟨⟨_, LevelTower.IsUniverse.sort _, .refl D.num_typed⟩, .refl (D.succ_typed D.zero_typed)⟩

/-- The call's arguments: `num`, `1`, `1`, `[2]`, `[3]`; its declared type `vec num (add 1 1)`. -/
theorem consArgs :
    subst (fun x => subst (consSub one consValues) (indexArgs appendDef consAcc x)) appendDef.result =
      vecC numC (addC one one) := by
  decide +kernel

/-- The made row at the instance, `pair 2 (appendProgram num 0 1 [] [3])`, runs to `[2, 3]`, by kernel
evaluation of the package's reduction. -/
theorem consMade_runs :
    vecNormalize level1 60 (subst (consSub one consValues) (rename (indexRen consRow consAcc) consRow.body)) =
      some twoThree := by
  decide +kernel

/-- **The guarantee is not vacuous**: the cons row of `append`, on `append num 1 1 [2] [3]`, answers
`[2, 3]`, typed at `vec num (add 1 1)`. -/
theorem guarantee_witness :
    ∃ args, RowAnswer 16 appendDef appendDef.rows args twoThree ∧
      subst args appendDef.result = vecC numC (addC one one) ∧
      Typed pkg .nil twoThree (vecC numC (addC one one)) := by
  obtain ⟨e, elaborated⟩ : ∃ e, elaborate 16 appendDef consRow = some e :=
    Option.isSome_iff_exists.mp (by decide +kernel)
  have elaborated' := elaborated
  obtain ⟨formed, tv, l, rfl⟩ := elaborate_index elaborated cons_raw rfl
  let call : GroundCall (Elaborated.mk (extend (prefixOf consAcc formed) (numType _))
      [Elimination.definition (prefixOf consAcc formed) ⟨succC (.var 3), tv⟩]
      (madeAt (Γ := extend (prefixOf consAcc formed) (numType _)) (indexArgs appendDef consAcc) appendDef.result
        (rename (indexRen consRow consAcc) consRow.body) l) (indexArgs appendDef consAcc)) :=
    ⟨consInstance formed, consInstance_solves formed tv⟩
  have answer : RowAnswer 16 appendDef appendDef.rows call.args twoThree :=
    ⟨consRow, List.mem_cons_of_mem _ (List.mem_singleton_self _), _, elaborated', call, rfl,
      vecNormalize_sound level1 consMade_runs, twoThree_normal⟩
  have hargs : subst call.args appendDef.result = vecC numC (addC one one) := consArgs
  refine ⟨call.args, answer, hargs, ?_⟩
  have typed := (guarantee append_admitted (fun _ member => member) answer).1
  rwa [hargs] at typed

/-! ## The hypothesis is needed: a second, unchecked row -/

/-- The raw pass of `append xs ys = xs`: the function and the five parameters, no call index. -/
abbrev keepAcc : Acc :=
  ⟨6, .snoc (.snoc (.snoc (.snoc (.snoc (.snoc .nil appendDef.type) U0) numC) numC) (vecC (.var 2) (.var 1)))
      (vecC (.var 3) (.var 1)),
    [some (.var 0), some (.var 1), some (.var 2), some (.var 3), some (.var 4)],
    [some 0, some 1, some 2, some 3, some 4], none⟩

theorem keep_raw : rawPass appendDef keepRow = some keepAcc := by decide +kernel

/-- The closed values: `appendProgram`, `num`, `0`, `1`, `[]`, `[3]`. -/
def keepValues : Sub Tower.Head 6 0 :=
  consSub (single three) (consSub ttC (consSub one (consSub zeroC (consSub numC
    (consSub TowerVectorsPrograms.appendProgram fun i => Fin.elim0 i)))))

theorem keepValues_typed : SubstMor pkg keepAcc.frame .nil keepValues := by
  have m₀ : SubstMor pkg (.nil : Ctx Tower.Head 0) .nil fun i => Fin.elim0 i := fun i => Fin.elim0 i
  have tNum : Typed pkg .nil numC U0 := D.num_typed
  have tZero : Typed pkg .nil zeroC numC := D.zero_typed
  have tOne : Typed pkg .nil one numC := D.succ_typed D.zero_typed
  have tThree : Typed pkg .nil three numC := D.succ_typed (D.succ_typed tOne)
  have tNil : Typed pkg .nil ttC (vecC numC zeroC) := D.nil_typed tNum
  have tSingle : Typed pkg .nil (single three) (vecC numC one) := D.cons_typed tNum tZero tThree tNil
  exact Normalization.SubstMor.cons (Normalization.SubstMor.cons (Normalization.SubstMor.cons
    (Normalization.SubstMor.cons (Normalization.SubstMor.cons
      (Normalization.SubstMor.cons m₀ (TowerVectorsPrograms.appendProgram_typed level1)) tNum) tZero) tOne)
    tNil) tSingle

/-- The call's arguments: `num`, `0`, `1`, `[]`, `[3]`; its declared type `vec num (add 0 1)`. -/
theorem keepArgs :
    subst (fun x => subst keepValues (plainArgs appendDef keepAcc x)) appendDef.result = vecC numC (addC zeroC one) := by
  decide +kernel

/-- The made row at the instance is the first argument, `[]`. -/
theorem keepMade (pos : 0 < keepAcc.arity) :
    subst keepValues (rename (plainRen keepRow keepAcc pos) keepRow.body) = ttC := rfl

/-- The empty vector is no vector of length `add 0 1`: refuted by the checker's own refutation. -/
theorem nil_not_length_one : ¬ Typed pkg .nil ttC (vecC numC (addC zeroC one)) := by
  have found : (refute? 16 (.nil : Ctx Tower.Head 0) ttC (vecC numC (addC zeroC one))).isSome = true := by
    decide +kernel
  obtain ⟨r, _⟩ := Option.isSome_iff_exists.mp found
  exact r.down .nil ⟨_, D.tower.isUniverse _, D.vec_typed D.num_typed
    (TowerVectorsPrograms.add_typed level1 D.zero_typed (D.succ_typed D.zero_typed))⟩

/-- The unchecked row is not a row of the checked definition. -/
theorem keepRow_not_checked : keepRow ∉ appendDef.rows := by
  intro member
  rcases List.mem_cons.mp member with same | later
  · exact absurd (congrArg Row.patterns same) (by decide)
  · exact absurd (congrArg Row.patterns (List.mem_singleton.mp later)) (by decide)

/-- **A second, unchecked row breaks the guarantee**: declared beside the checked rows, `append xs ys =
xs` answers the ground call `append num 0 1 [] [3]` with `[]`, which is not of the call's declared type
`vec num (add 0 1)`. -/
theorem second_row_breaks :
    ¬ (∀ r ∈ appendDef.rows ++ [keepRow], r ∈ appendDef.rows) ∧
      ∃ args v, RowAnswer 16 appendDef (appendDef.rows ++ [keepRow]) args v ∧
        ¬ Typed pkg .nil v (subst args appendDef.result) := by
  refine ⟨fun only => keepRow_not_checked (only keepRow (List.mem_append_right _ (List.mem_singleton_self _))), ?_⟩
  obtain ⟨e, elaborated⟩ : ∃ e, elaborate 16 appendDef keepRow = some e :=
    Option.isSome_iff_exists.mp (by decide +kernel)
  have elaborated' := elaborated
  obtain ⟨pos, formed, l, rfl⟩ := elaborate_plain elaborated keep_raw rfl
  let call : GroundCall (Elaborated.mk (prefixOf keepAcc formed) []
      (madeAt (Γ := prefixOf keepAcc formed) (plainArgs appendDef keepAcc) appendDef.result
        (rename (plainRen keepRow keepAcc pos) keepRow.body) l) (plainArgs appendDef keepAcc)) :=
    ⟨(⟨keepValues, keepValues_typed⟩ : empty pkg ⟶ prefixOf keepAcc formed), Frames.models_nil _⟩
  have args : subst call.args appendDef.result = vecC numC (addC zeroC one) := keepArgs
  have made : call.made = ttC := keepMade pos
  refine ⟨call.args, ttC, ⟨keepRow, List.mem_append_right _ (List.mem_singleton_self _), _, elaborated', call, rfl,
    ?_⟩, ?_⟩
  · rw [made]
    exact ⟨.refl, const_normal level1 (by decide)⟩
  · rw [args]
    exact nil_not_length_one

end NativeTypesOnTheStep.Computing.Vectors.Checker

#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.guarantee
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.cons_raw
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.consValues_typed
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.consInstance_solves
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.consArgs
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.consMade_runs
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.guarantee_witness
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.keep_raw
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.keepValues_typed
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.keepArgs
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.keepMade
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.nil_not_length_one
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.keepRow_not_checked
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.second_row_breaks

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
