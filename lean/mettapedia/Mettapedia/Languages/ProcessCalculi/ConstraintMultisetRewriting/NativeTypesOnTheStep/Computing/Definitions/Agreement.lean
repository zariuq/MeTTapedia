import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Definitions.ExtensionRuns
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.ConstantExpansion

/-!
# The declared constant and its compiled term: reading the rows, and where they agree

A definition by rows lives twice: as a constant of the extended package whose rows are rules
(`Extension`), and as a closed term of the package, its compiled term (`Compile`). This module relates
the two by **reading** the constants as closed terms: `ConstantExpansion.expand`, the replacement of
constants by closed bodies, with the bodies of a `reading`.

* **Reading is sound for conversion, for every term** (`conv_reading`). When every rule of a checked
  development, read at the bodies, joins by the package's executable reduction (`rulesRead`, a
  kernel-evaluated check), every conversion of the extended package reads as a conversion of the
  package. The package's own rows are read as themselves, because the development's names do not occur
  in them. Nothing is asked of the shape of the rows.
* **Agreement** (`Recursive.agrees`): in the extended package, a call of the declared constant is
  convertible with the same call of the compiled term, at every instance whose call index is a numeral.
  It is proved for a constant defined by recursion on its call index (`Recursive`): two rules, at
  `zero` and at `succ k`; both read at the bodies join; the row at `zero` does not mention the constant;
  and in the row at `succ k` every occurrence of the constant is a **saturated call on the predecessor**
  (`Saturated`): the constant applied to all its arguments, with `k` at the call index. The proof is an
  induction on the numeral. Every condition is decided by kernel evaluation (`saturated?` for the last).
  A definition by recursion on the length of a vector has rules of the same two shapes (`Extension.ruleOf`).
* **Why saturated.** Agreement at a partial application is false: `add-by-rows 1` is a normal form of
  the extended package and the compiled addition at `1` reduces to an abstraction, so the two are not
  convertible (`partial_not_convertible`). In general a normal form of the extension that mentions a new
  constant is convertible with no term of the package (`normal_not_conv_old`). A row that passes the
  recursive call on without its later arguments is in the class of checked functions and outside this
  proof: for such a definition agreement fails at a full call with a variable among its arguments, and
  the ground calls that were run agree (`DirectedAnswers.Unsaturated`). Whether every ground call of
  such a definition has an answer by its rows is not decided.
* **A definition without a call index** (`Plain`, `Plain.agrees`): one row, every pattern a variable,
  no recursion. Its calls agree at every instance, with no induction.
* **Instances**, each by kernel evaluation: addition by rows and append over it, in their development
  (`add_recursive`, `append_recursive`, `addAppend_read`); `map`, with its function argument, in its own
  (`map_recursive`); `dup`, whose result is a pair, without a call index (`dup_plain`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing.Definitions

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open AlgebraicSchema
open ConstantExpansion (expand Bodies constantNames)
open ConversionCoherence (StepStar)
open TowerVectorsModel (numC zeroC succC ttC)
open ProgrammingOnTheStep.IndexedFamilies.Eliminator (level1 pkg)
open ProgrammingOnTheStep.IndexedFamilies.ClosedCalls (one)

/-! ## The extension contains the package -/

/-- A step over a smaller root computation is a step over a larger one. -/
theorem stepCore_mono {root root' : RootComputation Tower.Head} {headEq : Tower.Head → Tower.Head → Prop}
    (included : ∀ {k : Nat} {l r : Tower.Tm k}, root.step l r → root'.step l r) {n : Nat}
    {t u : Tower.Tm n} (step : StepCore root headEq t u) : StepCore root' headEq t u := by
  induction step with
  | betaPi body a => exact .betaPi body a
  | betaSigmaFst a b => exact .betaSigmaFst a b
  | betaSigmaSnd a b => exact .betaSigmaSnd a b
  | head equality => exact .head equality
  | root h => exact .root (included h)
  | congPiDom _ ih => exact .congPiDom ih
  | congPiCod _ ih => exact .congPiCod ih
  | congSigmaDom _ ih => exact .congSigmaDom ih
  | congSigmaCod _ ih => exact .congSigmaCod ih
  | congIdTy _ ih => exact .congIdTy ih
  | congIdLeft _ ih => exact .congIdLeft ih
  | congIdRight _ ih => exact .congIdRight ih
  | congLam _ ih => exact .congLam ih
  | congAppFun _ ih => exact .congAppFun ih
  | congAppArg _ ih => exact .congAppArg ih
  | congPairFst _ ih => exact .congPairFst ih
  | congPairSnd _ ih => exact .congPairSnd ih
  | congFst _ ih => exact .congFst ih
  | congSnd _ ih => exact .congSnd ih
  | congRefl _ ih => exact .congRefl ih

/-- **A conversion of the package is a conversion of every extension of it by a development.** -/
theorem conv_dev (dev : Development) (rows : SchemaTable Tower.Head) {n : Nat} {t u : Tower.Tm n}
    (conversion : Conv pkg.headEq t u pkg.computation) :
    Conv (devPackage dev rows).headEq t u (devPackage dev rows).computation := by
  induction conversion with
  | rel _ _ step => exact .rel _ _ (stepCore_mono (fun s => pkg_step_dev dev rows s) step)
  | refl _ => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ihFirst ihSecond => exact .trans _ _ _ ihFirst ihSecond

/-- **A directed reduction of the package is one of every extension of it.** -/
theorem reducesStar_dev (dev : Development) (rows : SchemaTable Tower.Head) {n : Nat} {t u : Tower.Tm n}
    (steps : StrongNormalization.ReducesStar pkg t u) :
    StrongNormalization.ReducesStar (devPackage dev rows) t u := by
  induction steps with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (stepCore_mono (fun s => pkg_step_dev dev rows s) step)

/-- The table of a checked development passes the declaration-time check. -/
theorem devCheck_table {dev : Development} (ok : devCheck dev = true) {rows : SchemaTable Tower.Head}
    (found : devRules dev = some rows) :
    DeclarationCheck.checkTable (devDefined dev) (devArity dev) (Vectors.vectorEquations ++ rows) = true := by
  obtain ⟨rows', found', -, -, table⟩ := devCheck_parts ok
  rw [found] at found'
  obtain rfl := Option.some.inj found'
  exact table

/-- **The package extended by a checked development is a constructor presentation.** -/
def devConstructors {dev : Development} (ok : devCheck dev = true) {rows : SchemaTable Tower.Head}
    (found : devRules dev = some rows) : ConstructorSystem.ConstructorPresentation (devPackage dev rows) :=
  DeclarationCheck.checkedConstructors (devBase dev) (by intro n l r impossible; exact impossible)
    LevelTower.headEq_symmetric (devCheck_table ok found)

/-- **A root step of a checked extension starts at a defined constant applied to exactly its arity of
arguments**, and the arity is positive. -/
theorem dev_root_spine {dev : Development} (ok : devCheck dev = true) {rows : SchemaTable Tower.Head}
    (found : devRules dev = some rows) {n : Nat} {t u : Tower.Tm n}
    (step : (devPackage dev rows).computation.step t u) :
    ∃ name, ConstructorSystem.spineHead t = some (name, devArity dev name) ∧ 0 < devArity dev name ∧
      devDefined dev name = true := by
  obtain ⟨_, left, right, σ, rule, shape, _⟩ := (devConstructors ok found).presentation.cover step
  obtain ⟨name, defined, positive, side⟩ := (devConstructors ok found).system.left
    (((devConstructors ok found).same left right).mp rule)
  exact ⟨name, shape ▸ ConstructorSystem.spineHead_subst_leftSide side σ, positive, defined⟩

/-- **No name of a checked development occurs in a row of the package.** -/
theorem dev_name_not_in_rows {dev : Development} (ok : devCheck dev = true) {c : DeclName}
    (occurs : ∃ r ∈ Vectors.vectorEquations, (constFreeB c r.2.1 && constFreeB c r.2.2) = false) :
    ∀ e ∈ dev, e.1 ≠ c := by
  obtain ⟨_, -, fresh, -, -⟩ := devCheck_parts ok
  obtain ⟨r, member, occurs⟩ := occurs
  intro e em same
  have free := (fresh e em).2 r member
  rw [same] at free
  rw [free.1, free.2] at occurs
  cases occurs

/-- **The constructors of values are no names of a checked development**: `zero`, `succ` and `tt` each
occur in a row of the package. -/
theorem dev_names_ne_constructors {dev : Development} (ok : devCheck dev = true) :
    (∀ e ∈ dev, e.1 ≠ TowerNumbersModel.zero) ∧ (∀ e ∈ dev, e.1 ≠ TowerNumbersModel.succ) ∧
      (∀ e ∈ dev, e.1 ≠ TowerVectorsModel.tt) :=
  ⟨dev_name_not_in_rows ok (by decide +kernel), dev_name_not_in_rows ok (by decide +kernel),
    dev_name_not_in_rows ok (by decide +kernel)⟩

/-- **The successor is no defined constant of a checked extension**: it occurs in the package's rows,
and no name of a checked development does. -/
theorem succ_not_defined {dev : Development} (ok : devCheck dev = true) :
    devDefined dev TowerNumbersModel.succ = false := by
  unfold devDefined
  rw [Bool.or_eq_false_iff]
  refine ⟨by decide, ?_⟩
  rw [List.any_eq_false]
  intro e em
  simp only [beq_iff_eq]
  exact (dev_names_ne_constructors ok).2.1 e em

/-- **In a checked extension, a normal form that mentions a constant of the development is convertible
with no term of the package.** A term without the new constants reduces, in the extension, only to such
terms (`dev_stepStar_old`), and the extension is Church–Rosser. -/
theorem normal_not_conv_old {dev : Development} (ok : devCheck dev = true) {rows : SchemaTable Tower.Head}
    (found : devRules dev = some rows) {n : Nat} {t u : Tower.Tm n}
    (normal : ConstructorSystem.Normal (devPackage dev rows) t) (new : ¬ OldTerm dev t)
    (old : OldTerm dev u) :
    ¬ Conv (devPackage dev rows).headEq t u (devPackage dev rows).computation := by
  intro conversion
  obtain ⟨common, fromT, fromU⟩ := (devConstructors ok found).churchRosser conversion
  have same : common = t := ConstructorSystem.Normal.stepStar normal fromT
  subst same
  exact new (dev_stepStar_old ok found fromU old).2

/-! ## Reading constants as closed terms -/

/-- **A reading**: a closed term of the package for each listed constant; every other constant is read
as itself. -/
def reading (terms : List (DeclName × Tower.Tm 0)) : Bodies Tower.Head := fun name =>
  match terms.find? (·.1 == name) with
  | some entry => entry.2
  | none => .const name

/-- A constant that is not listed is read as itself. -/
theorem reading_other {terms : List (DeclName × Tower.Tm 0)} {name : DeclName}
    (absent : ∀ entry ∈ terms, entry.1 ≠ name) : reading terms name = .const name := by
  have none : terms.find? (·.1 == name) = none := by
    rw [List.find?_eq_none]
    intro entry member
    simpa using absent entry member
  unfold reading
  rw [none]

/-- The reading of one constant leaves every other constant. -/
theorem reading_single_other {name d : DeclName} (c : Tower.Tm 0) (ne : d ≠ name) :
    reading [(name, c)] d = .const d :=
  reading_other (by
    intro entry member
    rw [List.mem_singleton.mp member]
    exact fun same => ne same.symm)

/-- A term whose constants are read as themselves is read as itself. -/
theorem expand_fixed {bodies : Bodies Tower.Head} {n : Nat} (t : Tower.Tm n)
    (fixed : ∀ name ∈ constantNames t, bodies name = .const name) : expand bodies t = t := by
  rw [ConstantExpansion.expand_eq_of_agreement bodies (fun name => .const name) t fixed,
    ConstantExpansion.expand_identity]

/-- The constants of a term free of `f` are not `f`. -/
theorem ne_of_mem_constantNames {f : DeclName} : ∀ {n : Nat} {t : Tower.Tm n}, ConstFree f t →
    ∀ name ∈ constantNames t, name ≠ f
  | _, .var _, _, _, member => by simp [constantNames] at member
  | _, .const c, free, name, member => by
      simp only [constantNames, List.mem_singleton] at member
      subst member
      exact free
  | _, .head _, _, _, member => by simp [constantNames] at member
  | _, .pi A B, free, name, member => by
      simp only [constantNames, List.mem_append] at member
      rcases member with inA | inB
      · exact ne_of_mem_constantNames free.1 name inA
      · exact ne_of_mem_constantNames free.2 name inB
  | _, .sigma A B, free, name, member => by
      simp only [constantNames, List.mem_append] at member
      rcases member with inA | inB
      · exact ne_of_mem_constantNames free.1 name inA
      · exact ne_of_mem_constantNames free.2 name inB
  | _, .id A a b, free, name, member => by
      simp only [constantNames, List.mem_append] at member
      rcases member with (inA | ina) | inb
      · exact ne_of_mem_constantNames free.1 name inA
      · exact ne_of_mem_constantNames free.2.1 name ina
      · exact ne_of_mem_constantNames free.2.2 name inb
  | _, .lam body, free, name, member => ne_of_mem_constantNames (t := body) free name member
  | _, .app g a, free, name, member => by
      simp only [constantNames, List.mem_append] at member
      rcases member with ing | ina
      · exact ne_of_mem_constantNames free.1 name ing
      · exact ne_of_mem_constantNames free.2 name ina
  | _, .pair a b, free, name, member => by
      simp only [constantNames, List.mem_append] at member
      rcases member with ina | inb
      · exact ne_of_mem_constantNames free.1 name ina
      · exact ne_of_mem_constantNames free.2 name inb
  | _, .fst p, free, name, member => ne_of_mem_constantNames (t := p) free name member
  | _, .snd p, free, name, member => ne_of_mem_constantNames (t := p) free name member
  | _, .refl a, free, name, member => ne_of_mem_constantNames (t := a) free name member

theorem expand_spine (bodies : Bodies Tower.Head) {n : Nat} : ∀ (g : Tower.Tm n) (as : List (Tower.Tm n)),
    expand bodies (spine g as) = spine (expand bodies g) (as.map (expand bodies))
  | _, [] => rfl
  | g, a :: as => expand_spine bodies (.app g a) as

/-! ## The rules read at the bodies -/

/-- **Every rule of the table, read at the bodies, joins** by the package's executable reduction. -/
def rulesRead (fuel : Nat) (bodies : Bodies Tower.Head) (rows : SchemaTable Tower.Head) : Bool :=
  rows.all fun r => joins fuel (expand bodies r.2.1) (expand bodies r.2.2)

/-- **Reading is sound for conversion.** For a development that passes the declaration-time check and
whose rules, read at the bodies, join: every conversion of the extended package, read at the bodies, is
a conversion of the package. The bodies read every constant outside the development as itself. -/
theorem conv_reading {dev : Development} (ok : devCheck dev = true) {rows : SchemaTable Tower.Head}
    (found : devRules dev = some rows) {bodies : Bodies Tower.Head}
    (others : ∀ d, (∀ e ∈ dev, e.1 ≠ d) → bodies d = .const d) {fuel : Nat}
    (read : rulesRead fuel bodies rows = true) {n : Nat} {t u : Tower.Tm n}
    (conversion : Conv (devPackage dev rows).headEq t u (devPackage dev rows).computation) :
    Conv pkg.headEq (expand bodies t) (expand bodies u) pkg.computation := by
  obtain ⟨rows', found', fresh, -, -⟩ := devCheck_parts ok
  rw [found] at found'
  obtain rfl := Option.some.inj found'
  have fixed : ∀ {k : Nat} (s : Tower.Tm k), (∀ e ∈ dev, constFreeB e.1 s = true) → expand bodies s = s := by
    intro k s free
    refine expand_fixed s fun name member => others name fun e em => ?_
    exact (ne_of_mem_constantNames (constFreeB_sound (free e em)) name member).symm
  refine ConstantExpansion.conv_expand bodies (fun {k left right} step => ?_) conversion
  rcases step with impossible | step
  · exact impossible.elim
  · cases step with
    | instantiate rule σ =>
        rw [ConstantExpansion.expand_subst, ConstantExpansion.expand_subst]
        rcases List.mem_append.mp rule with base | new
        · rw [fixed _ fun e em => ((fresh e em).2 _ base).1, fixed _ fun e em => ((fresh e em).2 _ base).2]
          exact .rel _ _ (.root (Vectors.vector_sound level1 base _))
        · exact Conv.substitute _ (joins_conv (List.all_eq_true.mp read _ new))

/-! ## Calls, presented by substitutions -/

/-- **The generic call** of a constant with `j` parameters before its call index and `q` after:
`name x₀ … x_{j-1} n y₁ … y_q`, over its `q + 1 + j` variables. A call is an instance of it. -/
def genericCall (name : DeclName) (q j : Nat) : Tower.Tm (q + 1 + j) := spine (.const name) (allVars q j)

/-- The substitution whose values are the arguments of a call, in telescope order. -/
def argSub {m : Nat} (q j : Nat) (as : List (Tower.Tm m)) : Sub Tower.Head (q + 1 + j) m :=
  fun x => as.getD (q + j - x.val) zeroC

theorem allVars_argSub {m q j : Nat} {as : List (Tower.Tm m)} (len : as.length = q + 1 + j) :
    (allVars q j).map (subst (argSub q j as)) = as := by
  apply List.ext_getElem
  · simp [allVars, len]
  · intro i h₁ h₂
    have lt : i < q + 1 + j := by rw [← len]; exact h₂
    simp only [allVars, List.getElem_map, List.getElem_ofFn, subst, argSub, Fin.val_rev]
    have same : q + j - (q + 1 + j - (i + 1)) = i := by omega
    simp only [same, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂, Option.getD_some]

theorem argSub_idx {m q j : Nat} {as : List (Tower.Tm m)} {a : Tower.Tm m} (index : as[j]? = some a) :
    argSub q j as (idx q j) = a := by
  have same : q + j - q = j := by omega
  simp only [argSub, idx, same, List.getD_eq_getElem?_getD, index, Option.getD_some]

/-- A call is the generic call at the substitution of its arguments. -/
theorem genericCall_argSub (name : DeclName) {m q j : Nat} {as : List (Tower.Tm m)}
    (len : as.length = q + 1 + j) : subst (argSub q j as) (genericCall name q j) = spine (.const name) as := by
  rw [genericCall, subst_spine, allVars_argSub len]
  rfl

theorem expand_allVars (bodies : Bodies Tower.Head) (q j : Nat) :
    (allVars q j).map (expand bodies) = allVars q j := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp only [allVars, List.getElem_map, List.getElem_ofFn]
    rfl

/-- The generic call read at the bodies: the same call of the constant's body. -/
theorem expand_genericCall (bodies : Bodies Tower.Head) (name : DeclName) (q j : Nat) :
    expand bodies (genericCall name q j) = spine (liftClosed (bodies name)) (allVars q j) := by
  rw [genericCall, expand_spine, expand_allVars]
  rfl

theorem expand_genericCall_argSub (bodies : Bodies Tower.Head) (name : DeclName) {m q j : Nat}
    {as : List (Tower.Tm m)} (len : as.length = q + 1 + j) :
    subst (argSub q j as) (expand bodies (genericCall name q j)) = spine (liftClosed (bodies name)) as := by
  rw [expand_genericCall, subst_spine, allVars_argSub len, subst_liftClosed]

/-! ## The two rules of a recursion on the call index -/

/-- The variables other than the call index, among all. -/
def skipIndex (q j : Nat) : Fin (q + j) → Fin (q + 1 + j) := fun y =>
  if y.val < q then ⟨y.val, by omega⟩ else ⟨y.val + 1, by omega⟩

/-- **The call index set to `zero`**, over the other `q + j` variables. -/
def atZero (q j : Nat) : Sub Tower.Head (q + 1 + j) (q + j) := fun x =>
  if h : x.val < q then .var ⟨x.val, by omega⟩
  else if h' : x.val = q then zeroC
  else .var ⟨x.val - 1, by omega⟩

/-- **The call index set to the successor of itself.** -/
def atSucc (q j : Nat) : Sub Tower.Head (q + 1 + j) (q + 1 + j) := fun x =>
  if x = idx q j then succC (.var (idx q j)) else .var x

/-- An instance with `zero` at the call index is an instance of the zero form. -/
theorem atZero_subst {m q j : Nat} (σ : Sub Tower.Head (q + 1 + j) m) (index : σ (idx q j) = zeroC)
    (t : Tower.Tm (q + 1 + j)) :
    subst (fun y => σ (skipIndex q j y)) (subst (atZero q j) t) = subst σ t := by
  rw [subst_comp]
  refine subst_ext (fun x => ?_) t
  unfold atZero
  split
  · rename_i h
    show σ (skipIndex q j ⟨x.val, _⟩) = σ x
    congr 1
    apply Fin.ext
    simp [skipIndex, h]
  · split
    · rename_i h'
      have same : x = idx q j := Fin.ext h'
      rw [same, index]
      rfl
    · rename_i h h'
      show σ (skipIndex q j ⟨x.val - 1, _⟩) = σ x
      congr 1
      apply Fin.ext
      have notLess : ¬ x.val - 1 < q := by omega
      simp only [skipIndex, notLess, if_false]
      omega

/-- The instance with the predecessor `k` at the call index. -/
def withIndex {m q j : Nat} (σ : Sub Tower.Head (q + 1 + j) m) (k : Tower.Tm m) : Sub Tower.Head (q + 1 + j) m :=
  fun y => if y = idx q j then k else σ y

theorem withIndex_idx {m q j : Nat} (σ : Sub Tower.Head (q + 1 + j) m) (k : Tower.Tm m) :
    withIndex σ k (idx q j) = k := by
  simp [withIndex]

/-- An instance with `succ k` at the call index is an instance of the successor form, with `k` there. -/
theorem atSucc_subst {m q j : Nat} (σ : Sub Tower.Head (q + 1 + j) m) {k : Tower.Tm m}
    (index : σ (idx q j) = succC k) (t : Tower.Tm (q + 1 + j)) :
    subst (withIndex σ k) (subst (atSucc q j) t) = subst σ t := by
  rw [subst_comp]
  refine subst_ext (fun x => ?_) t
  unfold atSucc
  split
  · rename_i h
    subst h
    show succC (withIndex σ k (idx q j)) = σ (idx q j)
    rw [withIndex_idx, index]
  · rename_i h
    show withIndex σ k x = σ x
    simp [withIndex, h]

theorem expand_atZero {bodies : Bodies Tower.Head}
    (zeroOld : bodies TowerNumbersModel.zero = .const TowerNumbersModel.zero) (q j : Nat) :
    (fun x => expand bodies (atZero q j x)) = atZero q j := by
  funext x
  unfold atZero
  split
  · rfl
  · split
    · show liftClosed (bodies TowerNumbersModel.zero) = zeroC
      rw [zeroOld]
      rfl
    · rfl

theorem expand_atSucc {bodies : Bodies Tower.Head}
    (succOld : bodies TowerNumbersModel.succ = .const TowerNumbersModel.succ) (q j : Nat) :
    (fun x => expand bodies (atSucc q j x)) = atSucc q j := by
  funext x
  unfold atSucc
  split
  · show Tm.app (liftClosed (bodies TowerNumbersModel.succ)) (.var (idx q j)) = succC (.var (idx q j))
    rw [succOld]
    rfl
  · rfl

/-! ## Saturated calls on the predecessor -/

/-- **Every occurrence of the constant is a saturated call on the predecessor**: the constant applied to
`j` arguments, the variable `pred`, and `q` more arguments, each of them saturated in turn. Under a
binder the predecessor is the next variable. -/
inductive Saturated (name : DeclName) (q j : Nat) : {n : Nat} → Fin n → Tower.Tm n → Prop
  | var {n : Nat} {pred : Fin n} (i : Fin n) : Saturated name q j pred (.var i)
  | const {n : Nat} {pred : Fin n} {c : DeclName} : c ≠ name → Saturated name q j pred (.const c)
  | head {n : Nat} {pred : Fin n} (h : Tower.Head) : Saturated name q j pred (.head h)
  | pi {n : Nat} {pred : Fin n} {A : Tower.Tm n} {B : Tower.Tm (n + 1)} :
      Saturated name q j pred A → Saturated name q j pred.succ B → Saturated name q j pred (.pi A B)
  | sigma {n : Nat} {pred : Fin n} {A : Tower.Tm n} {B : Tower.Tm (n + 1)} :
      Saturated name q j pred A → Saturated name q j pred.succ B → Saturated name q j pred (.sigma A B)
  | id {n : Nat} {pred : Fin n} {A a b : Tower.Tm n} :
      Saturated name q j pred A → Saturated name q j pred a → Saturated name q j pred b →
        Saturated name q j pred (.id A a b)
  | lam {n : Nat} {pred : Fin n} {body : Tower.Tm (n + 1)} :
      Saturated name q j pred.succ body → Saturated name q j pred (.lam body)
  | app {n : Nat} {pred : Fin n} {g a : Tower.Tm n} :
      Saturated name q j pred g → Saturated name q j pred a → Saturated name q j pred (.app g a)
  | pair {n : Nat} {pred : Fin n} {a b : Tower.Tm n} :
      Saturated name q j pred a → Saturated name q j pred b → Saturated name q j pred (.pair a b)
  | fst {n : Nat} {pred : Fin n} {p : Tower.Tm n} : Saturated name q j pred p → Saturated name q j pred (.fst p)
  | snd {n : Nat} {pred : Fin n} {p : Tower.Tm n} : Saturated name q j pred p → Saturated name q j pred (.snd p)
  | refl {n : Nat} {pred : Fin n} {a : Tower.Tm n} : Saturated name q j pred a → Saturated name q j pred (.refl a)
  | call {n : Nat} {pred : Fin n} (args : List (Tower.Tm n)) : args.length = q + 1 + j →
      args[j]? = some (.var pred) → (∀ a ∈ args, Saturated name q j pred a) →
      Saturated name q j pred (spine (.const name) args)

/-- **The decision of saturation**, within a budget. -/
def saturated? (name : DeclName) (q j : Nat) : Nat → {n : Nat} → Fin n → Tower.Tm n → Bool
  | 0, _, _, _ => false
  | fuel + 1, _, pred, t =>
      (match unspine (q + 1 + j) t with
        | some (.const c, args) =>
            c == name && decide (args[j]? = some (.var pred)) &&
              args.all (fun a => saturated? name q j fuel pred a)
        | _ => false) ||
      (match t with
        | .var _ => true
        | .const c => c != name
        | .head _ => true
        | .pi A B => saturated? name q j fuel pred A && saturated? name q j fuel pred.succ B
        | .sigma A B => saturated? name q j fuel pred A && saturated? name q j fuel pred.succ B
        | .id A a b =>
            saturated? name q j fuel pred A && saturated? name q j fuel pred a && saturated? name q j fuel pred b
        | .lam body => saturated? name q j fuel pred.succ body
        | .app g a => saturated? name q j fuel pred g && saturated? name q j fuel pred a
        | .pair a b => saturated? name q j fuel pred a && saturated? name q j fuel pred b
        | .fst p => saturated? name q j fuel pred p
        | .snd p => saturated? name q j fuel pred p
        | .refl a => saturated? name q j fuel pred a)

theorem saturated?_sound {name : DeclName} {q j : Nat} :
    ∀ (fuel : Nat) {n : Nat} {pred : Fin n} {t : Tower.Tm n},
      saturated? name q j fuel pred t = true → Saturated name q j pred t
  | 0, _, _, _, found => by simp [saturated?] at found
  | fuel + 1, n, pred, t, found => by
      unfold saturated? at found
      rcases Bool.or_eq_true_iff.mp found with call | structural
      · split at call
        · rename_i c args hu
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at call
          obtain ⟨⟨rfl, index⟩, all⟩ := call
          obtain ⟨rfl, len⟩ := unspine_sound _ hu
          exact .call args len index fun a member => saturated?_sound fuel (all a member)
        · cases call
      · cases t with
        | var i => exact .var i
        | const c =>
            simp only [bne_iff_ne, ne_eq] at structural
            exact .const structural
        | head h => exact .head h
        | pi A B =>
            simp only [Bool.and_eq_true] at structural
            exact .pi (saturated?_sound fuel structural.1) (saturated?_sound fuel structural.2)
        | sigma A B =>
            simp only [Bool.and_eq_true] at structural
            exact .sigma (saturated?_sound fuel structural.1) (saturated?_sound fuel structural.2)
        | id A a b =>
            simp only [Bool.and_eq_true] at structural
            exact .id (saturated?_sound fuel structural.1.1) (saturated?_sound fuel structural.1.2)
              (saturated?_sound fuel structural.2)
        | lam body => exact .lam (saturated?_sound fuel structural)
        | app g a =>
            simp only [Bool.and_eq_true] at structural
            exact .app (saturated?_sound fuel structural.1) (saturated?_sound fuel structural.2)
        | pair a b =>
            simp only [Bool.and_eq_true] at structural
            exact .pair (saturated?_sound fuel structural.1) (saturated?_sound fuel structural.2)
        | fst p => exact .fst (saturated?_sound fuel structural)
        | snd p => exact .snd (saturated?_sound fuel structural)
        | refl a => exact .refl (saturated?_sound fuel structural)

/-! ## Agreement, by induction on the numeral at the call index -/

theorem rename_nat {n m : Nat} (ρ : Ren n m) : ∀ N : Nat, rename ρ (nat N : Tower.Tm n) = nat N
  | 0 => rfl
  | N + 1 => by
      show succC (rename ρ (nat N)) = succC (nat N)
      rw [rename_nat ρ N]

/-- Conversion of two spines whose heads convert and whose arguments convert one by one. -/
theorem conv_spine_map {R : Rules Tower.Head} {n m : Nat} (f g : Tower.Tm n → Tower.Tm m) :
    ∀ (as : List (Tower.Tm n)) {head head' : Tower.Tm m}, Conv R.headEq head head' R.computation →
      (∀ a ∈ as, Conv R.headEq (f a) (g a) R.computation) →
      Conv R.headEq (spine head (as.map f)) (spine head' (as.map g)) R.computation
  | [], _, _, heads, _ => heads
  | a :: as, _, _, heads, args =>
      conv_spine_map f g as (Conv.congApp heads (args a (List.mem_cons_self ..)))
        fun b member => args b (List.mem_cons_of_mem _ member)

section Agreement

variable {R : Rules Tower.Head} {bodies : Bodies Tower.Head} {name : DeclName} {q j N : Nat}

/-- **Where every call on the numeral `N` agrees, every term saturated on a predecessor that is `N`
agrees**: its instance and the instance of its reading are convertible. -/
theorem Saturated.conv (others : ∀ d, d ≠ name → bodies d = .const d)
    (claim : ∀ {m : Nat} (θ : Sub Tower.Head (q + 1 + j) m), θ (idx q j) = nat N →
      Conv R.headEq (subst θ (genericCall name q j)) (subst θ (expand bodies (genericCall name q j)))
        R.computation) :
    ∀ {n : Nat} {pred : Fin n} {t : Tower.Tm n}, Saturated name q j pred t →
      ∀ {m : Nat} (τ : Sub Tower.Head n m), τ pred = nat N →
        Conv R.headEq (subst τ t) (subst τ (expand bodies t)) R.computation := by
  intro n pred t saturated
  induction saturated with
  | var i => intro m τ _; exact .refl _
  | @const n pred c ne =>
      intro m τ _
      have same : expand bodies (.const c : Tower.Tm n) = .const c := by
        show liftClosed (bodies c) = _
        rw [others c ne]
        rfl
      rw [same]
      exact .refl _
  | head h => intro m τ _; exact .refl _
  | pi _ _ ihA ihB =>
      intro m τ at_
      exact Conv.congPi (ihA τ at_) (ihB (liftSub τ) (by rw [liftSub_succ, at_, rename_nat]))
  | sigma _ _ ihA ihB =>
      intro m τ at_
      exact Conv.congSigma (ihA τ at_) (ihB (liftSub τ) (by rw [liftSub_succ, at_, rename_nat]))
  | id _ _ _ ihA iha ihb =>
      intro m τ at_
      exact Conv.congId (ihA τ at_) (iha τ at_) (ihb τ at_)
  | lam _ ih =>
      intro m τ at_
      exact Conv.congLam (ih (liftSub τ) (by rw [liftSub_succ, at_, rename_nat]))
  | app _ _ ihg iha =>
      intro m τ at_
      exact Conv.congApp (ihg τ at_) (iha τ at_)
  | pair _ _ iha ihb =>
      intro m τ at_
      exact Conv.congPair (iha τ at_) (ihb τ at_)
  | fst _ ih =>
      intro m τ at_
      exact Conv.mapCompatible Tm.fst (fun h => .congFst h) (ih τ at_)
  | snd _ ih =>
      intro m τ at_
      exact Conv.mapCompatible Tm.snd (fun h => .congSnd h) (ih τ at_)
  | refl _ ih =>
      intro m τ at_
      exact Conv.mapCompatible Tm.refl (fun h => .congRefl h) (ih τ at_)
  | @call n pred args len index _ ih =>
      intro m τ at_
      have lenB : (args.map fun a => subst τ (expand bodies a)).length = q + 1 + j := by
        rw [List.length_map, len]
      have indexB : (args.map fun a => subst τ (expand bodies a))[j]? = some (nat N) := by
        rw [List.getElem?_map, index]
        show some (τ pred) = _
        rw [at_]
      -- the arguments, one by one
      have arguments : Conv R.headEq (spine (.const name) (args.map (subst τ)))
          (spine (.const name) (args.map fun a => subst τ (expand bodies a))) R.computation :=
        conv_spine_map (subst τ) (fun a => subst τ (expand bodies a)) args (.refl _)
          fun a member => ih a member τ at_
      -- the call at the read arguments
      have atCall := claim (argSub q j (args.map fun a => subst τ (expand bodies a))) (argSub_idx indexB)
      rw [genericCall_argSub name lenB, expand_genericCall_argSub bodies name lenB] at atCall
      have left : subst τ (spine (.const name) args) = spine (.const name) (args.map (subst τ)) :=
        subst_spine τ _ args
      have right : subst τ (expand bodies (spine (.const name) args)) =
          spine (liftClosed (bodies name)) (args.map fun a => subst τ (expand bodies a)) := by
        rw [expand_spine, subst_spine, List.map_map]
        show spine (subst τ (liftClosed (bodies name))) _ = _
        rw [subst_liftClosed]
        rfl
      rw [left, right]
      exact .trans _ _ _ arguments atCall

end Agreement

/-- **A constant defined by recursion on its call index, read as a closed term**: its two rules are in
the table; read at the bodies, both join; the row at `zero` does not mention the constant; in the row at
`succ k` every occurrence of the constant is a saturated call on `k`; the bodies read every other
constant as itself, and the constant is neither `zero` nor `succ`. -/
structure Recursive (rows : SchemaTable Tower.Head) (bodies : Bodies Tower.Head) (name : DeclName)
    (q j : Nat) (r0 : Tower.Tm (q + j)) (r1 : Tower.Tm (q + 1 + j)) : Prop where
  zeroRule : (⟨q + j, (subst (atZero q j) (genericCall name q j), r0)⟩ :
    Σ arity : Nat, Tower.Tm arity × Tower.Tm arity) ∈ rows
  succRule : (⟨q + 1 + j, (subst (atSucc q j) (genericCall name q j), r1)⟩ :
    Σ arity : Nat, Tower.Tm arity × Tower.Tm arity) ∈ rows
  others : ∀ d, d ≠ name → bodies d = .const d
  notZero : TowerNumbersModel.zero ≠ name
  notSucc : TowerNumbersModel.succ ≠ name
  zeroReads : ∃ fuel, joins fuel (expand bodies (subst (atZero q j) (genericCall name q j)))
    (expand bodies r0) = true
  succReads : ∃ fuel, joins fuel (expand bodies (subst (atSucc q j) (genericCall name q j)))
    (expand bodies r1) = true
  zeroFree : expand bodies r0 = r0
  saturated : ∃ fuel, saturated? name q j fuel (idx q j) r1 = true

/-- **Agreement.** In the package extended by a development whose table holds the two rules of a
recursive constant, every call of the constant whose call index is a numeral is convertible with the
same call of the constant's body. -/
theorem Recursive.agrees {dev : Development} {rows : SchemaTable Tower.Head} {bodies : Bodies Tower.Head}
    {name : DeclName} {q j : Nat} {r0 : Tower.Tm (q + j)} {r1 : Tower.Tm (q + 1 + j)}
    (recursive : Recursive rows bodies name q j r0 r1) :
    ∀ (N : Nat) {m : Nat} (σ : Sub Tower.Head (q + 1 + j) m), σ (idx q j) = nat N →
      Conv (devPackage dev rows).headEq (subst σ (genericCall name q j))
        (subst σ (expand bodies (genericCall name q j))) (devPackage dev rows).computation := by
  intro N
  induction N with
  | zero =>
      intro m σ index
      have fire : (devPackage dev rows).computation.step
          (subst (fun y => σ (skipIndex q j y)) (subst (atZero q j) (genericCall name q j)))
          (subst (fun y => σ (skipIndex q j y)) r0) :=
        Or.inr (SchemaStep.instantiate (List.mem_append_right _ recursive.zeroRule) _)
      rw [atZero_subst σ index] at fire
      obtain ⟨fuel, ok⟩ := recursive.zeroReads
      have read := Conv.substitute (fun y => σ (skipIndex q j y)) (joins_conv ok)
      rw [ConstantExpansion.expand_subst, expand_atZero (recursive.others _ recursive.notZero),
        atZero_subst σ index, recursive.zeroFree] at read
      exact .trans _ _ _ (.rel _ _ (.root fire)) (.symm _ _ (conv_dev dev rows read))
  | succ N ih =>
      intro m σ index
      have fire : (devPackage dev rows).computation.step
          (subst (withIndex σ (nat N)) (subst (atSucc q j) (genericCall name q j)))
          (subst (withIndex σ (nat N)) r1) :=
        Or.inr (SchemaStep.instantiate (List.mem_append_right _ recursive.succRule) _)
      rw [atSucc_subst σ index] at fire
      obtain ⟨fuel, ok⟩ := recursive.succReads
      have read := Conv.substitute (withIndex σ (nat N)) (joins_conv ok)
      rw [ConstantExpansion.expand_subst, expand_atSucc (recursive.others _ recursive.notSucc),
        atSucc_subst σ index] at read
      obtain ⟨fuel', saturated⟩ := recursive.saturated
      have body := (saturated?_sound fuel' saturated).conv (R := devPackage dev rows) recursive.others
        (fun θ at_ => ih θ at_) (withIndex σ (nat N)) (withIndex_idx σ (nat N))
      exact .trans _ _ _ (.rel _ _ (.root fire))
        (.trans _ _ _ body (.symm _ _ (conv_dev dev rows read)))

/-! ## Addition by rows and append over it -/

/-- The reading of the development of addition and append: their compiled terms. -/
abbrev addAppendReading : Bodies Tower.Head := reading [(addName, addTerm), (appendName, appendRTerm)]

/-- **Every rule of addition and of append, read at the compiled terms, joins.** -/
theorem addAppend_read : rulesRead 40 addAppendReading addAppendRows = true := by decide +kernel

/-- The reading reads every constant outside the development as itself. -/
theorem addAppend_others (d : DeclName) (absent : ∀ e ∈ addAppendDev, e.1 ≠ d) :
    addAppendReading d = .const d := by
  refine reading_other ?_
  intro entry member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact absent (addName, addDef) (List.mem_cons_self ..)
  · exact absent (appendName, appendOnAddDef) (List.mem_cons_of_mem _ (List.mem_cons_self ..))

/-- **Every conversion of the package extended by addition and append by rows, read at the compiled
terms, is a conversion of the package**, for all terms. -/
theorem addAppend_conv_reading {n : Nat} {t u : Tower.Tm n}
    (conversion : Conv (devPackage addAppendDev addAppendRows).headEq t u
      (devPackage addAppendDev addAppendRows).computation) :
    Conv pkg.headEq (expand addAppendReading t) (expand addAppendReading u) pkg.computation :=
  conv_reading addAppend_devCheck addAppend_rules addAppend_others addAppend_read conversion

/-- **Addition by rows is a recursive constant read as the compiled addition**: one later parameter, no
earlier one. -/
theorem add_recursive :
    Recursive addAppendRows (reading [(addName, addTerm)]) addName 1 0 (.var 0)
      (succC (spine (.const addName) [.var 1, .var 0])) where
  zeroRule := by decide +kernel
  succRule := by decide +kernel
  others := fun d ne => reading_single_other addTerm ne
  notZero := by decide
  notSucc := by decide
  zeroReads := ⟨30, by decide +kernel⟩
  succReads := ⟨30, by decide +kernel⟩
  zeroFree := rfl
  saturated := ⟨8, by decide +kernel⟩

/-- **Append by rows is a recursive constant read as the compiled append**: the element type before the
length; the other length and the two vectors after. -/
theorem append_recursive :
    Recursive addAppendRows (reading [(appendName, appendRTerm)]) appendName 3 1 (.var 0)
      (.pair (.fst (.var 1)) (spine (.const appendName) [.var 4, .var 3, .var 2, .snd (.var 1), .var 0])) where
  zeroRule := by decide +kernel
  succRule := by decide +kernel
  others := fun d ne => reading_single_other appendRTerm ne
  notZero := by decide
  notSucc := by decide
  zeroReads := ⟨40, by decide +kernel⟩
  succReads := ⟨40, by decide +kernel⟩
  zeroFree := rfl
  saturated := ⟨8, by decide +kernel⟩

/-! ## Map -/

/-- The constant of map. -/
def mapName : DeclName := .mkSimple "map-by-rows"

/-- The development of map alone. -/
abbrev mapDev : Development := [(mapName, mapDef)]

/-- Its rules: `map A B g zero xs ⟶ tt` and
`map A B g (succ k) xs ⟶ pair (g (fst xs)) (map A B g k (snd xs))`. -/
abbrev mapRows : SchemaTable Tower.Head :=
  [⟨4, (spine (.const mapName) [.var 3, .var 2, .var 1, zeroC, .var 0], ttC)⟩,
    ⟨5, (spine (.const mapName) [.var 4, .var 3, .var 2, succC (.var 1), .var 0],
      .pair (.app (.var 2) (.fst (.var 0)))
        (spine (.const mapName) [.var 4, .var 3, .var 2, .var 1, .snd (.var 0)]))⟩]

theorem map_devCheck : devCheck mapDev = true := others_devCheck.2.1

theorem map_fresh : devFresh mapDev = true := others_fresh.2.1

theorem map_rules : devRules mapDev = some mapRows := by decide +kernel

/-- **Map by rows is a recursive constant read as its compiled term**: the two types and the function
before the length, the vector after. The function argument is applied in the row; nothing is asked
of it. -/
theorem map_recursive : ∃ c : Tower.Tm 0, Checked mapDef 0 c ∧
    Recursive mapRows (reading [(mapName, c)]) mapName 1 3 ttC
      (.pair (.app (.var 2) (.fst (.var 0)))
        (spine (.const mapName) [.var 4, .var 3, .var 2, .var 1, .snd (.var 0)])) := by
  obtain ⟨c, checked⟩ := map_checked
  have zeroReads : ((compile 0 mapDef).map fun c => joins 40
      (expand (reading [(mapName, c)]) (subst (atZero 1 3) (genericCall mapName 1 3)))
      (expand (reading [(mapName, c)]) (ttC : Tower.Tm (1 + 3)))) = some true := by decide +kernel
  have succReads : ((compile 0 mapDef).map fun c => joins 40
      (expand (reading [(mapName, c)]) (subst (atSucc 1 3) (genericCall mapName 1 3)))
      (expand (reading [(mapName, c)]) (.pair (.app (.var 2) (.fst (.var 0)))
        (spine (.const mapName) [.var 4, .var 3, .var 2, .var 1, .snd (.var 0)]) : Tower.Tm (1 + 1 + 3)))) =
        some true := by decide +kernel
  rw [checked.compiled] at zeroReads succReads
  refine ⟨c, checked, ?_⟩
  exact
    { zeroRule := by decide +kernel
      succRule := by decide +kernel
      others := fun d ne => reading_single_other c ne
      notZero := by decide
      notSucc := by decide
      zeroReads := ⟨40, Option.some.inj zeroReads⟩
      succReads := ⟨40, Option.some.inj succReads⟩
      zeroFree := rfl
      saturated := ⟨8, by decide +kernel⟩ }

/-! ## A definition without a call index -/

/-- The call of a constant at all its `a` variables, in telescope order. -/
def plainCall (name : DeclName) (a : Nat) : Tower.Tm a := spine (.const name) (telescopeVars a)

/-- **A constant defined by one row without a call index, read as a closed term**: its rule is in the
table; read at the bodies, its two sides join; and the row does not mention the constant. -/
structure Plain (rows : SchemaTable Tower.Head) (bodies : Bodies Tower.Head) (name : DeclName) (a : Nat)
    (r : Tower.Tm a) : Prop where
  rule : (⟨a, (plainCall name a, r)⟩ : Σ arity : Nat, Tower.Tm arity × Tower.Tm arity) ∈ rows
  reads : ∃ fuel, joins fuel (expand bodies (plainCall name a)) (expand bodies r) = true
  free : expand bodies r = r

/-- **Agreement for a definition without a call index**: every call of the constant is convertible, in
the extended package, with the same call of its body. No induction is needed. -/
theorem Plain.agrees {dev : Development} {rows : SchemaTable Tower.Head} {bodies : Bodies Tower.Head}
    {name : DeclName} {a : Nat} {r : Tower.Tm a} (plain : Plain rows bodies name a r) {m : Nat}
    (σ : Sub Tower.Head a m) :
    Conv (devPackage dev rows).headEq (subst σ (plainCall name a))
      (subst σ (expand bodies (plainCall name a))) (devPackage dev rows).computation := by
  have fire : (devPackage dev rows).computation.step (subst σ (plainCall name a)) (subst σ r) :=
    Or.inr (SchemaStep.instantiate (List.mem_append_right _ plain.rule) σ)
  obtain ⟨fuel, ok⟩ := plain.reads
  have read := Conv.substitute σ (joins_conv ok)
  rw [plain.free] at read
  exact .trans _ _ _ (.rel _ _ (.root fire)) (.symm _ _ (conv_dev dev rows read))

/-- The constant of `dup`. -/
def dupName : DeclName := .mkSimple "dup-by-rows"

/-- The development of `dup` alone. -/
abbrev dupDev : Development := [(dupName, dupDef)]

/-- Its rule: `dup n ⟶ pair n n`. -/
abbrev dupRows : SchemaTable Tower.Head :=
  [⟨1, (spine (.const dupName) [.var 0], .pair (.var 0) (.var 0))⟩]

theorem dup_devCheck : devCheck dupDev = true := by decide +kernel

theorem dup_fresh : devFresh dupDev = true := by decide +kernel

theorem dup_rules : devRules dupDev = some dupRows := by decide +kernel

/-- **`dup` by rows is a constant without a call index read as its compiled term.** -/
theorem dup_plain : ∃ c : Tower.Tm 0, Checked dupDef 0 c ∧
    Plain dupRows (reading [(dupName, c)]) dupName 1 (.pair (.var 0) (.var 0)) := by
  obtain ⟨c, checked⟩ := qualify_closed dup_verdict
  have reads : ((compile 0 dupDef).map fun c => joins 30
      (expand (reading [(dupName, c)]) (plainCall dupName 1))
      (expand (reading [(dupName, c)]) (.pair (.var 0) (.var 0) : Tower.Tm 1))) = some true := by
    decide +kernel
  rw [checked.compiled] at reads
  exact ⟨c, checked, by decide +kernel, ⟨30, Option.some.inj reads⟩, rfl⟩

/-! ## Control: a partial application does not agree -/

theorem lamSucc_old : OldTerm addAppendDev (.lam (succC (.var 0)) : Tower.Tm 0) := by
  intro e member
  simp only [addAppendDev, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact constFreeB_sound (by decide +kernel)
  · exact constFreeB_sound (by decide +kernel)

theorem one_old : OldTerm addAppendDev (one : Tower.Tm 0) := by
  intro e member
  simp only [addAppendDev, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact constFreeB_sound (by decide +kernel)
  · exact constFreeB_sound (by decide +kernel)

/-- **Agreement fails at a partial application.** In the package extended by addition and append by
rows, the constant of addition applied to `1` alone and the compiled addition applied to `1` are not
convertible: the first is a normal form, since a rule of the constant needs its two arguments, and the
second reduces to `λ m. succ m`. The proof of agreement uses that the recursive calls of a row are
saturated; a row that passes on the partial application of a recursive call is outside it. -/
theorem partial_not_convertible :
    ¬ Conv (devPackage addAppendDev addAppendRows).headEq
      (.app (.const addName) one : Tower.Tm 0) (.app addTerm one)
      (devPackage addAppendDev addAppendRows).computation := by
  intro conversion
  have normalLeft : ConstructorSystem.Normal (devPackage addAppendDev addAppendRows)
      (.app (.const addName) one : Tower.Tm 0) := by
    refine ConstructorSystem.Normal.app (ConstructorSystem.Normal.const _ ?_) ?_
      (fun body h => by cases h) ?_
    · intro target step
      obtain ⟨name, head, positive, -⟩ := dev_root_spine addAppend_devCheck addAppend_rules step
      have computed : ConstructorSystem.spineHead (.const addName : Tower.Tm 0) = some (addName, 0) := rfl
      rw [computed] at head
      simp only [Option.some.injEq, Prod.mk.injEq] at head
      obtain ⟨rfl, arity⟩ := head
      omega
    · intro target step
      obtain ⟨baseStep, -⟩ := dev_step_old addAppend_devCheck addAppend_rules step one_old
      exact Vectors.succ_normal level1 (Vectors.const_normal level1 (by decide)) baseStep
    · intro target step
      obtain ⟨name, head, -, -⟩ := dev_root_spine addAppend_devCheck addAppend_rules step
      have computed : ConstructorSystem.spineHead (.app (.const addName) one : Tower.Tm 0) =
          some (addName, 1) := rfl
      rw [computed] at head
      simp only [Option.some.injEq, Prod.mk.injEq] at head
      obtain ⟨rfl, arity⟩ := head
      exact absurd arity (by decide)
  have ran : Vectors.vecNormalize level1 30 (.app addTerm one : Tower.Tm 0) =
      some (.lam (succC (.var 0))) := by decide +kernel
  have toLam : Conv (devPackage addAppendDev addAppendRows).headEq (.app addTerm one : Tower.Tm 0)
      (.lam (succC (.var 0))) (devPackage addAppendDev addAppendRows).computation :=
    conv_dev _ _ (conv_of_stepStar (Vectors.vecNormalize_sound level1 ran))
  exact normal_not_conv_old addAppend_devCheck addAppend_rules normalLeft
    (fun old => (old (addName, addDef) (List.mem_cons_self ..)).1 rfl) lamSucc_old
    (.trans _ _ _ conversion toLam)

end NativeTypesOnTheStep.Computing.Definitions

section Audit
open NativeTypesOnTheStep.Computing.Definitions
#print axioms conv_dev
#print axioms reducesStar_dev
#print axioms devConstructors
#print axioms dev_root_spine
#print axioms dev_names_ne_constructors
#print axioms succ_not_defined
#print axioms normal_not_conv_old
#print axioms conv_reading
#print axioms saturated?_sound
#print axioms Saturated.conv
#print axioms Recursive.agrees
#print axioms addAppend_read
#print axioms addAppend_conv_reading
#print axioms add_recursive
#print axioms append_recursive
#print axioms map_rules
#print axioms map_recursive
#print axioms Plain.agrees
#print axioms dup_devCheck
#print axioms dup_rules
#print axioms dup_plain
#print axioms partial_not_convertible
end Audit

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
