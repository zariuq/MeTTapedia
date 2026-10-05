import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.DeclarationRewriting
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.RecursionComputation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.EmptyRootConversion

/-!
# Directed rules beside defining equations

A package has two lists. The **equations** are defining equations: they generate
conversion, and for a definition they are the computation `definedRules` already
uses. The **directed rules** are closed rules used for running. Conversion does
not read them.

Adding directed rules does not add a conversion (`rules_conservative`). Running
does read them: the fork `c ⟶ 5`, `c ⟶ 6` steps under running and does not step
under conversion (`fork_runs`).

A family may be admitted as equations when it is deterministic: one right side
for each left side, and every right side is a value (`Deterministic`). Admitting
the family as equations instead of rules leaves running and the answer counts
unchanged (`admission_instead`, `admission_instead_keeps_copies`): an admitted
equation steps left to right, which is the step of the rule. `admission_same_running`
keeps the family as rules and as equations, so each step occurs twice in the
union; it follows from `admission_instead`, and `pair_promotes` still cites it.
`copies_of_equations` is the count. One call then has one value
(`promoted_answers_unique`).

Conversion is symmetric and running is not. The fork `c ⟶ 5`, `c ⟶ 6` admitted
as equations still answers both (`fork_admitted_oriented`) and converts `5` with
`6` (`fork_promoted_conv`), while the package that keeps the fork as rules does
not (`fork_not_conv`). Reading every family as equations would preserve that
separation (`SeparatesAnswers`); the fork refutes it (`fork_refutes_free_promotion`).

The pair `c ⟶ 5`, `d ⟶ 5` is deterministic, so it promotes, and its two calls
still answer `5` once each. The rule `loop ⟶ loop` never reaches a value, and
admitting it adds only `loop = loop`, which does not change conversion.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Annotated

open ConversionCoherence

variable {Head : Type}

/-! ## A directed rule -/

/-- A directed rule: a closed left side and a closed right side. Two copies in a
list are two occurrences, whether or not the sides are the same terms. -/
structure DirectedRule (Head : Type) where
  left : CTm Head 0
  right : CTm Head 0

/-- The rule read as a defining equation of no metavariables. -/
def DirectedRule.promote (r : DirectedRule Head) : DefiningEquation Head where
  arity := 0
  telescope := .nil
  left := r.left
  right := r.right

/-- A ground rule `c ⟶ body` is the equation of an explicit definition with no
argument. -/
theorem promote_explicit (c : DeclName) (body : CTm Head 0) :
    DirectedRule.promote (⟨.const c, body⟩ : DirectedRule Head) =
      explicitEquation c (.nil : CTele Head 0 0) body := by
  rw [explicitEquation_nil]
  rfl

/-- The computation of a definition package is the erasure of its equations. -/
theorem definedRules_computation (target : Rules Head) (f : DeclName) (A : CTm Head 0)
    (eqs : List (DefiningEquation Head)) :
    (definedRules target f A eqs).computation = erasedComputation eqs :=
  rfl

open DirectedRule

/-- The root steps of a list of directed rules: the instances of the rules read
as equations. Running uses this. Conversion does not. -/
def directedRoot (rules : List (DirectedRule Head)) : RootComputation Head :=
  erasedComputation (rules.map promote)

/-! ## The package -/

/-- Equations and directed rules, over a base package. Conversion is generated
by the base computation and the equations. Running uses those and the directed
rules. -/
structure TwoKind (Head : Type) where
  base : Rules Head
  equations : List (DefiningEquation Head)
  rules : List (DirectedRule Head)

namespace TwoKind

/-- Root steps of the equations, together with the base computation. -/
def equationRoot (P : TwoKind Head) : RootComputation Head :=
  Normalization.RootComputation.union P.base.computation (erasedComputation P.equations)

/-- Root steps of running: the equation root, and the directed rules. -/
def runningRoot (P : TwoKind Head) : RootComputation Head :=
  Normalization.RootComputation.union P.equationRoot (directedRoot P.rules)

/-- The package whose conversion is the equation root. -/
def equationRules (P : TwoKind Head) : Rules Head :=
  { P.base with computation := P.equationRoot }

/-- The package whose root steps are the running root. -/
def runningRules (P : TwoKind Head) : Rules Head :=
  { P.base with computation := P.runningRoot }

/-- The same equations and no directed rules. -/
def dropRules (P : TwoKind Head) : TwoKind Head :=
  { P with rules := [] }

end TwoKind

open TwoKind

theorem union_step {first second : RootComputation Head} {n : Nat} {t u : Tm Head n} :
    (Normalization.RootComputation.union first second).step t u ↔
      first.step t u ∨ second.step t u :=
  Iff.rfl

/-- A running step is a step of the base, a step of an equation, or a step of a
directed rule. -/
theorem running_step_iff (P : TwoKind Head) {n : Nat} {t u : Tm Head n} :
    P.runningRoot.step t u ↔
      P.base.computation.step t u ∨ (erasedComputation P.equations).step t u ∨
        (directedRoot P.rules).step t u := by
  rw [runningRoot, equationRoot, union_step, union_step]
  constructor
  · rintro ((hbase | heqs) | hrules)
    · exact Or.inl hbase
    · exact Or.inr (Or.inl heqs)
    · exact Or.inr (Or.inr hrules)
  · rintro (hbase | heqs | hrules)
    · exact Or.inl (Or.inl hbase)
    · exact Or.inl (Or.inr heqs)
    · exact Or.inr hrules

/-- **Adding directed rules does not change conversion.** The equational theory
is the theory of the equations alone. -/
theorem rules_conservative (P : TwoKind Head) {n : Nat} {t u : Tm Head n} :
    Conv P.equationRules.headEq t u P.equationRules.computation ↔
      Conv (P.dropRules).equationRules.headEq t u
        (P.dropRules).equationRules.computation :=
  Iff.rfl

/-! ## Admission -/

/-- The family as directed rules, and not as equations. -/
def asRules (base : Rules Head) (family : List (DirectedRule Head)) : TwoKind Head where
  base := base
  equations := []
  rules := family

/-- The same occurrences, also admitted as equations. The rules stay, so each
step of the family occurs twice in the running union. -/
def asEquations (base : Rules Head) (family : List (DirectedRule Head)) : TwoKind Head where
  base := base
  equations := family.map promote
  rules := family

/-- The family admitted as equations, and not kept as rules. -/
def admittedOnly (base : Rules Head) (family : List (DirectedRule Head)) : TwoKind Head where
  base := base
  equations := family.map promote
  rules := []

theorem erased_nil_step {n : Nat} {t u : Tm Head n} :
    ¬ (erasedComputation ([] : List (DefiningEquation Head))).step t u := by
  intro ⟨_, member, _⟩
  cases member

/-- **Admitting a family as equations instead of rules leaves running unchanged.**
An admitted equation steps from its left side to its right side, which is the
step of the rule it came from. `directedRoot` is that erasure. -/
theorem admission_instead (base : Rules Head) (family : List (DirectedRule Head))
    {n : Nat} {t u : Tm Head n} :
    (asRules base family).runningRoot.step t u ↔
      (admittedOnly base family).runningRoot.step t u := by
  rw [running_step_iff, running_step_iff]
  simp only [asRules, admittedOnly, directedRoot]
  constructor
  · rintro (hbase | heqs | hrules)
    · exact Or.inl hbase
    · exact absurd heqs erased_nil_step
    · exact Or.inr (Or.inl hrules)
  · rintro (hbase | heqs | hrules)
    · exact Or.inl hbase
    · exact Or.inr (Or.inr heqs)
    · exact absurd hrules erased_nil_step

/-- **Keeping the rules beside the admitted equations does not change running.**
Each step occurs twice in the union, and the union of a relation with itself is
the relation. This follows from `admission_instead`. -/
theorem admission_same_running (base : Rules Head) (family : List (DirectedRule Head))
    {n : Nat} {t u : Tm Head n} :
    (asRules base family).runningRoot.step t u ↔
      (asEquations base family).runningRoot.step t u := by
  rw [admission_instead]
  rw [running_step_iff, running_step_iff]
  simp only [admittedOnly, asEquations, directedRoot]
  constructor
  · rintro (hbase | heqs | hrules)
    · exact Or.inl hbase
    · exact Or.inr (Or.inl heqs)
    · exact absurd hrules erased_nil_step
  · rintro (hbase | heqs | hrules)
    · exact Or.inl hbase
    · exact Or.inr (Or.inl heqs)
    · exact Or.inr (Or.inl hrules)

/-! ## Answers, with multiplicity -/

/-- How many occurrences of `rules` answer `call` with `answer`. -/
def copies [DecidableEq Head] : List (DirectedRule Head) → Tm Head 0 → Tm Head 0 → Nat
  | [], _, _ => 0
  | r :: rs, call, answer =>
      copies rs call answer +
        if r.left.erase = call ∧ r.right.erase = answer then 1 else 0

/-- How many admitted equations answer `call` with `answer`. An equation of
positive arity does not answer a closed call. -/
def equationCopies [DecidableEq Head] :
    List (DefiningEquation Head) → Tm Head 0 → Tm Head 0 → Nat
  | [], _, _ => 0
  | e :: es, call, answer =>
      equationCopies es call answer +
        if h : e.arity = 0 then
          if h ▸ e.left.erase = call ∧ h ▸ e.right.erase = answer then 1 else 0
        else 0

/-- **The occurrence counts survive admission.** Each directed rule contributes
the same answer as the equation it becomes. -/
theorem copies_of_equations [DecidableEq Head] (family : List (DirectedRule Head))
    (call answer : Tm Head 0) :
    copies family call answer = equationCopies (family.map promote) call answer := by
  induction family with
  | nil => rfl
  | cons r rs ih =>
      rw [List.map_cons, copies, equationCopies, ih, promote, dif_pos rfl]

/-- **The answer counts survive admission instead of rules.** A duplicated
occurrence stays duplicated: the two packages count the same copies of each
answer. -/
theorem admission_instead_keeps_copies [DecidableEq Head] (base : Rules Head)
    (family : List (DirectedRule Head)) (call answer : Tm Head 0) :
    copies (asRules base family).rules call answer =
      equationCopies (admittedOnly base family).equations call answer := by
  simpa [asRules, admittedOnly] using copies_of_equations family call answer

theorem mem_of_copies_pos [DecidableEq Head] {family : List (DirectedRule Head)}
    {call answer : Tm Head 0} (positive : 0 < copies family call answer) :
    ∃ r, r ∈ family ∧ r.left.erase = call ∧ r.right.erase = answer := by
  induction family with
  | nil =>
      rw [copies] at positive
      exact absurd positive (Nat.not_lt_zero 0)
  | cons r rs ih =>
      by_cases hit : r.left.erase = call ∧ r.right.erase = answer
      · exact ⟨r, List.mem_cons_self, hit.1, hit.2⟩
      · rw [copies, if_neg hit, Nat.add_zero] at positive
        obtain ⟨s, member, left, right⟩ := ih positive
        exact ⟨s, List.mem_cons_of_mem _ member, left, right⟩

/-- One right side for each left side, on the erased terms running uses. -/
def OneValue (rules : List (DirectedRule Head)) : Prop :=
  ∀ r r', r ∈ rules → r' ∈ rules → r.left.erase = r'.left.erase →
    r.right.erase = r'.right.erase

/-- **Under the deterministic side condition, one call has one value.** -/
theorem promoted_answers_unique [DecidableEq Head] {family : List (DirectedRule Head)}
    (oneValue : OneValue family) {call a b : Tm Head 0}
    (ha : 0 < copies family call a) (hb : 0 < copies family call b) : a = b := by
  obtain ⟨r, hr, rLeft, rRight⟩ := mem_of_copies_pos ha
  obtain ⟨s, hs, sLeft, sRight⟩ := mem_of_copies_pos hb
  have same := oneValue r s hr hs (rLeft.trans sLeft.symm)
  rw [← rRight, ← sRight]
  exact same

/-- The right side of a rule is not the left side of a rule: a run stops. -/
def isValue (rules : List (DirectedRule Head)) (t : Tm Head 0) : Prop :=
  ∀ r, r ∈ rules → r.left.erase ≠ t

/-- Deterministic and terminating: one value for each left side, and every
right side is a value. -/
structure Deterministic (rules : List (DirectedRule Head)) : Prop where
  oneValue : OneValue rules
  values : ∀ r r', r ∈ rules → r' ∈ rules → r.right.erase ≠ r'.left.erase

/-- The two terms reach one common term by the directed rules. -/
def Joins (rules : List (DirectedRule Head)) (a b : Tm Head 0) : Prop :=
  ∃ u, Relation.ReflTransGen (directedRoot rules).step a u ∧
    Relation.ReflTransGen (directedRoot rules).step b u

/-- **A deterministic family is confluent on the terms it rewrites**: the two
right sides of one left side are the same term, so they have already joined. -/
theorem deterministic_confluent {family : List (DirectedRule Head)}
    (deterministic : Deterministic family) {r r' : DirectedRule Head}
    (hr : r ∈ family) (hr' : r' ∈ family) (same : r.left.erase = r'.left.erase) :
    Joins family r.right.erase r'.right.erase := by
  refine ⟨r.right.erase, Relation.ReflTransGen.refl, ?_⟩
  rw [deterministic.oneValue r r' hr hr' same]

theorem deterministic_right_is_value {family : List (DirectedRule Head)}
    (deterministic : Deterministic family) {r : DirectedRule Head} (hr : r ∈ family) :
    isValue family r.right.erase := by
  intro r' hr' same
  exact deterministic.values r r' hr hr' same.symm

/-! ## Steps that do not leave a term, and empty roots -/

theorem stepCore_base_or_same {base extra : RootComputation Head}
    {headEq : Head → Head → Prop}
    (self : ∀ {n : Nat} {t u : Tm Head n}, extra.step t u → t = u)
    {n : Nat} {t u : Tm Head n}
    (step : StepCore (Normalization.RootComputation.union base extra) headEq t u) :
    StepCore base headEq t u ∨ t = u := by
  induction step with
  | betaPi body a => exact Or.inl (.betaPi body a)
  | betaSigmaFst a b => exact Or.inl (.betaSigmaFst a b)
  | betaSigmaSnd a b => exact Or.inl (.betaSigmaSnd a b)
  | head same => exact Or.inl (.head same)
  | root rootStep =>
      rcases rootStep with rootStep | rootStep
      · exact Or.inl (.root rootStep)
      · exact Or.inr (self rootStep)
  | congPiDom _ ih =>
      rcases ih with ih | rfl
      · exact Or.inl (.congPiDom ih)
      · exact Or.inr rfl
  | congPiCod _ ih =>
      rcases ih with ih | rfl
      · exact Or.inl (.congPiCod ih)
      · exact Or.inr rfl
  | congSigmaDom _ ih =>
      rcases ih with ih | rfl
      · exact Or.inl (.congSigmaDom ih)
      · exact Or.inr rfl
  | congSigmaCod _ ih =>
      rcases ih with ih | rfl
      · exact Or.inl (.congSigmaCod ih)
      · exact Or.inr rfl
  | congIdTy _ ih =>
      rcases ih with ih | rfl
      · exact Or.inl (.congIdTy ih)
      · exact Or.inr rfl
  | congIdLeft _ ih =>
      rcases ih with ih | rfl
      · exact Or.inl (.congIdLeft ih)
      · exact Or.inr rfl
  | congIdRight _ ih =>
      rcases ih with ih | rfl
      · exact Or.inl (.congIdRight ih)
      · exact Or.inr rfl
  | congLam _ ih =>
      rcases ih with ih | rfl
      · exact Or.inl (.congLam ih)
      · exact Or.inr rfl
  | congAppFun _ ih =>
      rcases ih with ih | rfl
      · exact Or.inl (.congAppFun ih)
      · exact Or.inr rfl
  | congAppArg _ ih =>
      rcases ih with ih | rfl
      · exact Or.inl (.congAppArg ih)
      · exact Or.inr rfl
  | congPairFst _ ih =>
      rcases ih with ih | rfl
      · exact Or.inl (.congPairFst ih)
      · exact Or.inr rfl
  | congPairSnd _ ih =>
      rcases ih with ih | rfl
      · exact Or.inl (.congPairSnd ih)
      · exact Or.inr rfl
  | congFst _ ih =>
      rcases ih with ih | rfl
      · exact Or.inl (.congFst ih)
      · exact Or.inr rfl
  | congSnd _ ih =>
      rcases ih with ih | rfl
      · exact Or.inl (.congSnd ih)
      · exact Or.inr rfl
  | congRefl _ ih =>
      rcases ih with ih | rfl
      · exact Or.inl (.congRefl ih)
      · exact Or.inr rfl

/-- A root that only steps a term to itself adds no conversion. -/
theorem conv_add_self {base extra : RootComputation Head} {headEq : Head → Head → Prop}
    (self : ∀ {n : Nat} {t u : Tm Head n}, extra.step t u → t = u)
    {n : Nat} {t u : Tm Head n}
    (conv : Conv headEq t u (Normalization.RootComputation.union base extra)) :
    Conv headEq t u base := by
  induction conv with
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
  | rel _ _ step =>
      rcases stepCore_base_or_same self step with step | rfl
      · exact Relation.EqvGen.rel _ _ step
      · exact Relation.EqvGen.refl _

theorem conv_mono_union {base extra : RootComputation Head} {headEq : Head → Head → Prop}
    {n : Nat} {t u : Tm Head n} (conv : Conv headEq t u base) :
    Conv headEq t u (Normalization.RootComputation.union base extra) :=
  Relation.EqvGen.mono
    (fun (a b : Tm Head n) (step : StepCore base headEq a b) =>
      StepCore.root_mono (fun s => Or.inl s) step)
    t u conv

/-- The same head equality and the same root steps generate the same conversion. -/
theorem conv_iff_of_steps {root root' : RootComputation Head} {headEq : Head → Head → Prop}
    (steps : ∀ {n : Nat} {t u : Tm Head n}, root.step t u ↔ root'.step t u)
    {n : Nat} {t u : Tm Head n} :
    Conv headEq t u root ↔ Conv headEq t u root' := by
  constructor
  · intro conv
    exact Relation.EqvGen.mono
      (fun (a b : Tm Head n) (step : StepCore root headEq a b) =>
        StepCore.root_mono (fun s => steps.mp s) step)
      t u conv
  · intro conv
    exact Relation.EqvGen.mono
      (fun (a b : Tm Head n) (step : StepCore root' headEq a b) =>
        StepCore.root_mono (fun s => steps.mpr s) step)
      t u conv

/-- A package with no computation and no head equality. -/
def quiet (Head : Type) : Rules Head where
  headTyping := fun _ _ => False
  isUniverse := fun _ => False
  join := fun _ _ _ => False
  cumulative := fun _ _ => False
  headEq := fun _ _ => False
  constantType := fun _ => none
  computation := RootComputation.empty

theorem false_symm {Head : Type} : Std.Symm (fun (_ _ : Head) => False) := by
  constructor
  intro _ _ impossible
  exact impossible.elim

theorem const_no_step {rules : Rules Head}
    (noRoot : ∀ {n : Nat} {t u : Tm Head n}, ¬ rules.computation.step t u)
    {n : Nat} {c : DeclName} {u : Tm Head n} :
    ¬ StepCore rules.computation rules.headEq (.const c) u := by
  intro step
  cases step with
  | root rootStep => exact noRoot rootStep

theorem const_star {rules : Rules Head}
    (noRoot : ∀ {n : Nat} {t u : Tm Head n}, ¬ rules.computation.step t u)
    {n : Nat} {c : DeclName} {u : Tm Head n}
    (steps : StepStar rules (.const c) u) : u = .const c := by
  induction steps with
  | refl => rfl
  | tail _ step ih =>
      subst ih
      exact absurd step (const_no_step noRoot)

/-- **Distinct constants are not convertible** when the package computes nothing. -/
theorem const_not_conv {n : Nat} {c c' : DeclName} (ne : c ≠ c') :
    ¬ Conv (quiet Head).headEq (.const c : Tm Head n) (.const c')
        (quiet Head).computation := by
  intro conv
  obtain ⟨_, toC, toC'⟩ :=
    EmptyRootConversion.churchRosser (quiet Head) rfl false_symm conv
  have left := const_star (fun s => False.elim s) toC
  have right := const_star (fun s => False.elim s) toC'
  injection left.symm.trans right with _ eq
  exact ne eq

theorem const_name {n : Nat} {c c' : DeclName}
    (same : (.const c : Tm Head n) = .const c') : c = c' := by
  injection same

/-! ## The fork `c ⟶ 5`, `c ⟶ 6` -/

/-- `c ⟶ 5` and `c ⟶ 6`. -/
def forkRules : List (DirectedRule Head) :=
  [{left := .const `c, right := .const `five}, {left := .const `c, right := .const `six}]

/-- The fork kept as directed rules. -/
def forkPackage (Head : Type) : TwoKind Head where
  base := quiet Head
  equations := []
  rules := forkRules

/-- The fork admitted as equations, occurrences unchanged. -/
def forkPromoted (Head : Type) : TwoKind Head where
  base := quiet Head
  equations := forkRules.map promote
  rules := forkRules

theorem fork_to_five {n : Nat} :
    (erasedComputation ((forkRules (Head := Head)).map promote)).step
      (.const `c : Tm Head n) (.const `five) := by
  refine ⟨promote {left := .const `c, right := .const `five}, ?_, Fin.elim0, rfl, rfl⟩
  rw [forkRules, List.map_cons]
  exact List.mem_cons_self

theorem fork_to_six {n : Nat} :
    (erasedComputation ((forkRules (Head := Head)).map promote)).step
      (.const `c : Tm Head n) (.const `six) := by
  refine ⟨promote {left := .const `c, right := .const `six}, ?_, Fin.elim0, rfl, rfl⟩
  rw [forkRules, List.map_cons, List.map_cons, List.map_nil]
  exact List.mem_cons_of_mem
    (promote {left := .const `c, right := .const `five}) List.mem_cons_self

theorem fork_equation_to_five {n : Nat} :
    (forkPromoted Head).equationRoot.step (.const `c : Tm Head n) (.const `five) :=
  Or.inr fork_to_five

theorem fork_equation_to_six {n : Nat} :
    (forkPromoted Head).equationRoot.step (.const `c : Tm Head n) (.const `six) :=
  Or.inr fork_to_six

/-- **Running answers the fork; conversion does not.** `c` steps to `5` by the
directed rule, and the equation root has no step. -/
theorem fork_runs {n : Nat} :
    (forkPackage Head).runningRoot.step (.const `c : Tm Head n) (.const `five) ∧
      ¬ (forkPackage Head).equationRoot.step (.const `c : Tm Head n) (.const `five) := by
  constructor
  · exact Or.inr fork_to_five
  · intro step
    rcases step with step | step
    · exact step.elim
    · exact erased_nil_step step

/-- Dropping the rules drops the running step. -/
theorem fork_drop_does_not_run {n : Nat} :
    ¬ (forkPackage Head).dropRules.runningRoot.step
        (.const `c : Tm Head n) (.const `five) := by
  intro step
  rw [running_step_iff] at step
  rcases step with step | step | step
  · exact step.elim
  · exact erased_nil_step step
  · rw [dropRules, directedRoot, List.map_nil] at step
    exact erased_nil_step step

theorem fork_not_oneValue : ¬ OneValue (forkRules (Head := Head)) := by
  intro oneValue
  have fiveMem :
      ({left := .const `c, right := .const `five} : DirectedRule Head) ∈
        forkRules (Head := Head) := by
    rw [forkRules]
    exact List.mem_cons_self
  have sixMem :
      ({left := .const `c, right := .const `six} : DirectedRule Head) ∈
        forkRules (Head := Head) := by
    rw [forkRules]
    exact List.mem_cons_of_mem
      ({left := .const `c, right := .const `five} : DirectedRule Head) List.mem_cons_self
  have same := oneValue
    ({left := .const `c, right := .const `five} : DirectedRule Head)
    ({left := .const `c, right := .const `six} : DirectedRule Head)
    fiveMem sixMem rfl
  exact absurd (const_name same) (by decide : (`five : DeclName) ≠ `six)

theorem fork_two_answers [DecidableEq Head] :
    copies (forkRules (Head := Head)) (.const `c) (.const `five) = 1 ∧
      copies (forkRules (Head := Head)) (.const `c) (.const `six) = 1 := by
  constructor
  · rw [forkRules, copies, if_pos ⟨rfl, rfl⟩, copies,
      if_neg (by
        intro same
        exact absurd (const_name same.2) (by decide : (`six : DeclName) ≠ `five)),
      copies]
  · rw [forkRules, copies,
      if_neg (by
        intro same
        exact absurd (const_name same.2) (by decide : (`five : DeclName) ≠ `six)),
      copies, if_pos ⟨rfl, rfl⟩, copies]

/-- **The directed fork does not make `5` equal to `6`.** -/
theorem fork_not_conv {n : Nat} :
    ¬ Conv (forkPackage Head).equationRules.headEq (.const `five : Tm Head n) (.const `six)
        (forkPackage Head).equationRules.computation := by
  intro conv
  have iffConv : Conv (quiet Head).headEq (.const `five : Tm Head n) (.const `six)
      (quiet Head).computation := by
    have steps : ∀ {m : Nat} {a b : Tm Head m},
        (forkPackage Head).equationRoot.step a b ↔ (quiet Head).computation.step a b := by
      intro m a b
      constructor
      · intro step
        rcases step with step | step
        · exact step
        · exact absurd step erased_nil_step
      · exact Or.inl
    exact (conv_iff_of_steps steps).mp conv
  exact const_not_conv (by decide : (`five : DeclName) ≠ `six) iffConv

/-- **Admitting the fork makes `5` and `6` convertible**, through `c`. -/
theorem fork_promoted_conv {n : Nat} :
    Conv (quiet Head).headEq (.const `five : Tm Head n) (.const `six)
      (forkPromoted Head).equationRoot :=
  Relation.EqvGen.trans _ _ _
    (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (.root fork_equation_to_five)))
    (Relation.EqvGen.rel _ _ (.root fork_equation_to_six))

/-- A running step of the admitted fork is `c ⟶ 5` or `c ⟶ 6`. -/
theorem fork_admitted_step {n : Nat} {t u : Tm Head n}
    (step : (admittedOnly (quiet Head) (forkRules (Head := Head))).runningRoot.step t u) :
    (t = .const `c ∧ u = .const `five) ∨ (t = .const `c ∧ u = .const `six) := by
  rw [running_step_iff] at step
  simp only [admittedOnly, directedRoot, List.map_nil] at step
  rcases step with step | step | step
  · exact step.elim
  · obtain ⟨_, member, _, rfl, rfl⟩ := step
    rw [forkRules, List.map_cons, List.map_cons, List.map_nil] at member
    rcases List.mem_cons.mp member with rfl | member
    · exact Or.inl ⟨rfl, rfl⟩
    · obtain rfl := List.mem_singleton.mp member
      exact Or.inr ⟨rfl, rfl⟩
  · exact (erased_nil_step step).elim

/-- **Admission leaves the fork running and changes what is equal.** The
equations step left to right, so `c` still answers `5` and `6` once each, and
`5` does not step back to `c`. Conversion is symmetric, so those two steps
identify `5` with `6`. The package that keeps the fork as rules does not. -/
theorem fork_admitted_oriented [DecidableEq Head] {n : Nat} :
    (admittedOnly (quiet Head) forkRules).runningRoot.step
        (.const `c : Tm Head n) (.const `five) ∧
      (admittedOnly (quiet Head) forkRules).runningRoot.step
        (.const `c : Tm Head n) (.const `six) ∧
      ¬ (admittedOnly (quiet Head) forkRules).runningRoot.step
          (.const `five : Tm Head n) (.const `c) ∧
      equationCopies (admittedOnly (quiet Head) forkRules).equations
          (.const `c) (.const `five) = 1 ∧
      equationCopies (admittedOnly (quiet Head) forkRules).equations
          (.const `c) (.const `six) = 1 ∧
      Conv (quiet Head).headEq (.const `five : Tm Head n) (.const `six)
        (admittedOnly (quiet Head) forkRules).equationRoot ∧
      ¬ Conv (asRules (quiet Head) forkRules).equationRules.headEq
          (.const `five : Tm Head n) (.const `six)
          (asRules (quiet Head) forkRules).equationRules.computation := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (admission_instead (quiet Head) forkRules).mp (fork_runs (n := n)).1
  · exact (admission_instead (quiet Head) forkRules).mp
      (by
        rw [running_step_iff]
        exact Or.inr (Or.inr (fork_to_six (n := n))))
  · intro step
    rcases fork_admitted_step step with ⟨ht, _⟩ | ⟨ht, _⟩
    · exact absurd (const_name ht) (by decide : (`five : DeclName) ≠ `c)
    · exact absurd (const_name ht) (by decide : (`five : DeclName) ≠ `c)
  · have hcount := (fork_two_answers (Head := Head)).1
    have hkeep := admission_instead_keeps_copies (quiet Head) (forkRules (Head := Head))
      (.const `c) (.const `five)
    rw [← hkeep]
    simpa [asRules] using hcount
  · have hcount := (fork_two_answers (Head := Head)).2
    have hkeep := admission_instead_keeps_copies (quiet Head) (forkRules (Head := Head))
      (.const `c) (.const `six)
    rw [← hkeep]
    simpa [asRules] using hcount
  · simpa [admittedOnly, forkPromoted, equationRoot] using fork_promoted_conv (n := n)
  · simpa [asRules, forkPackage] using fork_not_conv (n := n)

/-- What promotion without the side condition would claim: terms the empty
package keeps apart stay apart after the family is admitted. -/
def SeparatesAnswers (family : List (DirectedRule Head)) : Prop :=
  ∀ {n : Nat} {a b : Tm Head n},
    ¬ Conv (quiet Head).headEq a b (quiet Head).computation →
      ¬ Conv (quiet Head).headEq a b
          (Normalization.RootComputation.union (quiet Head).computation
            (erasedComputation (family.map promote)))

/-- **Rejected:** admitting every family preserves separation. The fork converts
`5` with `6`. -/
theorem fork_refutes_free_promotion : ¬ SeparatesAnswers (forkRules (Head := Head)) := by
  intro separates
  exact separates (n := 0)
    (const_not_conv (n := 0) (by decide : (`five : DeclName) ≠ `six))
    (fork_promoted_conv (n := 0))

theorem fork_admission_keeps_counts [DecidableEq Head] :
    copies (forkRules (Head := Head)) (.const `c) (.const `five) =
      equationCopies ((forkRules (Head := Head)).map promote) (.const `c) (.const `five) ∧
    copies (forkRules (Head := Head)) (.const `c) (.const `six) =
      equationCopies ((forkRules (Head := Head)).map promote) (.const `c) (.const `six) :=
  ⟨copies_of_equations _ _ _, copies_of_equations _ _ _⟩

/-! ## A deterministic pair `c ⟶ 5`, `d ⟶ 5` -/

/-- `c ⟶ 5` and `d ⟶ 5`. -/
def pairRules : List (DirectedRule Head) :=
  [{left := .const `c, right := .const `five}, {left := .const `d, right := .const `five}]

theorem pair_deterministic : Deterministic (pairRules (Head := Head)) where
  oneValue := by
    intro r r' hr hr' same
    rcases List.mem_cons.mp hr with rfl | hr
    · rcases List.mem_cons.mp hr' with rfl | hr'
      · rfl
      · obtain rfl := List.mem_singleton.mp hr'
        exact absurd (const_name same) (by decide : (`c : DeclName) ≠ `d)
    · obtain rfl := List.mem_singleton.mp hr
      rcases List.mem_cons.mp hr' with rfl | hr'
      · exact absurd (const_name same) (by decide : (`d : DeclName) ≠ `c)
      · obtain rfl := List.mem_singleton.mp hr'
        rfl
  values := by
    intro r r' hr hr' same
    rcases List.mem_cons.mp hr with rfl | hr
    · rcases List.mem_cons.mp hr' with rfl | hr'
      · exact absurd (const_name same) (by decide : (`five : DeclName) ≠ `c)
      · obtain rfl := List.mem_singleton.mp hr'
        exact absurd (const_name same) (by decide : (`five : DeclName) ≠ `d)
    · obtain rfl := List.mem_singleton.mp hr
      rcases List.mem_cons.mp hr' with rfl | hr'
      · exact absurd (const_name same) (by decide : (`five : DeclName) ≠ `c)
      · obtain rfl := List.mem_singleton.mp hr'
        exact absurd (const_name same) (by decide : (`five : DeclName) ≠ `d)

/-- The root steps of the admitted pair are `c ⟶ 5` and `d ⟶ 5`. -/
theorem pair_equation_step {n : Nat} {t u : Tm Head n}
    (step : (Normalization.RootComputation.union (quiet Head).computation
        (erasedComputation (pairRules.map promote))).step t u) :
    (t = .const `c ∧ u = .const `five) ∨ (t = .const `d ∧ u = .const `five) := by
  rcases step with step | ⟨_, member, _, rfl, rfl⟩
  · exact step.elim
  · rw [pairRules, List.map_cons, List.map_cons, List.map_nil] at member
    rcases List.mem_cons.mp member with rfl | member
    · exact Or.inl ⟨rfl, rfl⟩
    · obtain rfl := List.mem_singleton.mp member
      exact Or.inr ⟨rfl, rfl⟩

theorem pair_right_is_value : isValue (pairRules (Head := Head)) (.const `five) :=
  deterministic_right_is_value pair_deterministic List.mem_cons_self

theorem pair_answers [DecidableEq Head] :
    copies (pairRules (Head := Head)) (.const `c) (.const `five) = 1 ∧
      copies (pairRules (Head := Head)) (.const `d) (.const `five) = 1 := by
  constructor
  · rw [pairRules, copies, if_pos ⟨rfl, rfl⟩, copies,
      if_neg (by
        intro same
        exact absurd (const_name same.1) (by decide : (`d : DeclName) ≠ `c)),
      copies]
  · rw [pairRules, copies,
      if_neg (by
        intro same
        exact absurd (const_name same.1) (by decide : (`c : DeclName) ≠ `d)),
      copies, if_pos ⟨rfl, rfl⟩, copies]

/-- **The pair promotes**: it is deterministic, and admitting it does not change
running. -/
theorem pair_promotes {n : Nat} {t u : Tm Head n} :
    Deterministic (pairRules (Head := Head)) ∧
      ((asRules (quiet Head) pairRules).runningRoot.step t u ↔
        (asEquations (quiet Head) pairRules).runningRoot.step t u) :=
  ⟨pair_deterministic, admission_same_running (quiet Head) pairRules⟩

/-! ## `loop ⟶ loop` -/

/-- The rule `loop ⟶ loop`. -/
def loopRule : DirectedRule Head :=
  {left := .const `loop, right := .const `loop}

theorem loop_step_same {n : Nat} {t u : Tm Head n}
    (step : (directedRoot [loopRule (Head := Head)]).step t u) : t = u := by
  rw [directedRoot, List.map_cons, List.map_nil] at step
  obtain ⟨_, member, _, rfl, rfl⟩ := step
  obtain rfl := List.mem_singleton.mp member
  rfl

theorem loop_stays {n : Nat} {u : Tm Head n}
    (steps : Relation.ReflTransGen (directedRoot [loopRule]).step (.const `loop) u) :
    u = .const `loop := by
  induction steps with
  | refl => rfl
  | tail _ step ih =>
      subst ih
      exact (loop_step_same step).symm

theorem loop_not_value : ¬ isValue [loopRule (Head := Head)] (.const `loop) := by
  intro value
  exact value loopRule (List.mem_singleton_self _) rfl

/-- **Running never answers.** Every term reached from `loop`, including
`loop` itself, is the left side of the rule. -/
theorem loop_never_value {u : Tm Head 0}
    (steps : Relation.ReflTransGen (directedRoot [loopRule]).step (.const `loop) u) :
    ¬ isValue [loopRule] u := by
  intro value
  exact loop_not_value (by rwa [← loop_stays steps])

theorem loop_one_step [DecidableEq Head] :
    copies [loopRule (Head := Head)] (.const `loop) (.const `loop) = 1 := by
  rw [copies, if_pos ⟨rfl, rfl⟩, copies]

/-- **Admitting `loop ⟶ loop` does not change conversion.** The new root step
takes `loop` to itself, which conversion already has. -/
theorem loop_promotion_same {n : Nat} {t u : Tm Head n} (base : Rules Head) :
    Conv base.headEq t u
        (Normalization.RootComputation.union base.computation
          (directedRoot [loopRule (Head := Head)])) ↔
      Conv base.headEq t u base.computation := by
  constructor
  · exact fun conv => conv_add_self (fun step => loop_step_same step) conv
  · exact fun conv => conv_mono_union conv

/-! ## Axioms -/

#print axioms rules_conservative
#print axioms admission_instead
#print axioms admission_same_running
#print axioms copies_of_equations
#print axioms admission_instead_keeps_copies
#print axioms fork_admitted_oriented
#print axioms promoted_answers_unique
#print axioms deterministic_confluent
#print axioms fork_runs
#print axioms fork_two_answers
#print axioms fork_not_conv
#print axioms fork_promoted_conv
#print axioms fork_refutes_free_promotion
#print axioms pair_deterministic
#print axioms pair_promotes
#print axioms loop_never_value
#print axioms loop_promotion_same
#print axioms promote_explicit

end Annotated
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
