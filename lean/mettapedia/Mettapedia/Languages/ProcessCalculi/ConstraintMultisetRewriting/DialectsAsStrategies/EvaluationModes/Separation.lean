import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.EvaluationModes.Laws

/-!
# The separating theorems

* **Weakening forces running** (`weakening_forces_running`), for any answer function at all: if a
  held argument returned under `Number` gives answers that no check refused, the same answers come
  back under `Proc`, `%Undefined%` and a type variable. Under `Number` a refusal-free answer is a
  number, so the held text was run; weakening carries the run up the line. The hypothesis is met
  (`byName_meets`), and every design that runs held parameters alike under all computation types
  is such an answer function at every fuel (`design_weakening_for`).
* **The three Prime test lines cannot all pass in a design that keeps weakening**
  (`primeTests_break_weakening`, every design of the family): the `%Undefined%` line needs the held
  argument run, the `Proc` lines need it held, and weakening `Proc` to `%Undefined%` on `(f a)` then
  changes `(f a)` into `5`. The hybrid meets the hypothesis (`Acceptance.hybrid_prime_tests`).
* **The first three laws** (weakening, `let`, values final) hold in a design exactly when values are
  final and held parameters do not split between `Proc` and the other computation types
  (`first_three_laws_iff`). This leaves three held rules: never (code value), at every computation
  position (by-name), and at the root only (the Prime draft's rule). **Identity insertion** removes
  the third: the four laws hold exactly for code value and by-name (`four_laws_iff`), whatever the
  three remaining choices (`atomBody`, `constructorsRun`, `reportsRefusal`).
* **`Atom` results** (`atomCode_iff`): an `Atom` result builds code exactly when its body is
  returned as written.
* **The fork is one bit** (`plain_fork`, `inert_fork`, `not_plain_and_inert`): no design keeps
  both the plain reading of a held parameter returned as the body and inert held text; under the
  four laws, the plain reading holds exactly for by-name and inertness exactly for code value.
  The `%Undefined%` test line of the Prime draft asks for the first, its two `Proc` lines for the
  second.

The family statements are over all 96 values of `Design`; the counterexample parts are decided by
the kernel design by design.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.EvaluationModes

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Core CoreLaws Acceptance Weakening Laws

namespace Separation

/-! ## Weakening forces running, for any answer function -/

/-- Core answers of queries in programs (a design's elaboration at some fuel, or anything else). -/
abbrev AnswerFn := SProg → Atom → Option (List Ans)

/-- The weakening law for an answer function. -/
def WeakeningFor (A : AnswerFn) : Prop :=
  ∀ (P : SProg) (g : String) (R R' : Ty) (q : Atom) (L : List Ans), LineWeaker R R' →
    A (setResult P g R) q = some L → allVal L = true → A (setResult P g R') q = some L

theorem tvar_line : LineWeaker .number .tvar := ⟨⟨0, 2, rfl, rfl, by omega⟩, .inl rfl⟩

/-- **Weakening forces running.** -/
theorem weakening_forces_running (A : AnswerFn) (hw : WeakeningFor A) (L : List Ans)
    (hL : allVal L = true) (hnum : A (setResult (rangeProg .number) "g" .number) qRange = some L) :
    A (setResult (rangeProg .number) "g" .proc) qRange = some L ∧
      A (setResult (rangeProg .number) "g" .undef) qRange = some L ∧
      A (setResult (rangeProg .number) "g" .tvar) qRange = some L :=
  ⟨hw _ _ _ _ _ _ number_proc hnum hL, hw _ _ _ _ _ _ number_undef hnum hL,
    hw _ _ _ _ _ _ tvar_line hnum hL⟩

/-- A design whose held parameters run alike under every computation type is, at every fuel, an
answer function that keeps weakening. -/
theorem design_weakening_for (D : Design) (h : D.holdsUnderProc = false ∨ D.held = .never)
    (n : Nat) : WeakeningFor fun P q => runQ D P n q :=
  fun P g R R' q L line strong noRefusal => keepsWeakening_of D h P g R R' q n L line strong noRefusal

/-- The hypothesis is met: by-name runs `(f a)` to `5` under `Number`, refusing nothing. -/
theorem byName_meets :
    runQ byName (setResult (rangeProg .number) "g" .number) F qRange =
      some [(.val (N 5), ["g", "f"])] ∧ allVal [(.val (N 5), ["g", "f"])] = true := by
  decide +kernel

/-- Under weakening, `Proc` and `%Undefined%` agree on the held identity whatever they answer. -/
theorem proc_undef_agree (A : AnswerFn) (hw : WeakeningFor A) (L : List Ans) (hL : allVal L = true)
    (hproc : A (setResult (rangeProg .proc) "g" .proc) qRange = some L) :
    A (setResult (rangeProg .proc) "g" .undef) qRange = some L :=
  hw _ _ _ _ _ _ proc_undef hproc hL

/-! ## The three Prime test lines -/

/-- The counterexample the three test lines leave: under `Proc` the held `(f a)` comes back as
written, under `%Undefined%` it does not. -/
def ProcUndefSplit (D : Design) : Prop :=
  runQ D (setResult (rangeProg .proc) "g" .proc) F qRange = some [(.val callFA, ["g"])] ∧
    runQ D (setResult (rangeProg .proc) "g" .undef) F qRange ≠ some [(.val callFA, ["g"])]

theorem not_keepsWeakening_of_split {D : Design} (h : ProcUndefSplit D) : ¬ KeepsWeakening D :=
  fun hw => h.2 (hw _ _ _ _ _ _ _ proc_undef h.1 rfl)

theorem split_of_primeTests : ∀ D : Design, PassesPrimeTests D → ProcUndefSplit D := by
  intro D
  rcases D with ⟨held, p, r, a, c, rep⟩
  unfold PassesPrimeTests ProcUndefSplit
  cases held <;> cases p <;> cases r <;> cases a <;> cases c <;> cases rep <;> decide +kernel

/-- **No design of the family passes the three Prime test lines and keeps the weakening law.** -/
theorem primeTests_break_weakening (D : Design) (h : PassesPrimeTests D) : ¬ KeepsWeakening D :=
  not_keepsWeakening_of_split (split_of_primeTests D h)

/-- The hypothesis is not empty: the hybrid passes the three lines (and so breaks weakening). -/
theorem primeTests_witness : PassesPrimeTests hybrid ∧ ¬ KeepsWeakening hybrid :=
  ⟨hybrid_prime_tests, primeTests_break_weakening hybrid hybrid_prime_tests⟩

/-! ## The first three laws -/

/-- The `let` counterexample: `(let $y (held-atom (f a)) $y)` prints `5`, its source `(f a)`. -/
def LetSplit (D : Design) : Prop :=
  answers D letProg F qLet = some [N 5] ∧
    answers D letProg F (E [S "held-atom", callFA]) = some [callFA]

theorem not_keepsLet_of_split {D : Design} (h : LetSplit D) : ¬ KeepsLet D := by
  intro hl
  exact not_iff_of_prints ⟨F, h.1⟩ ⟨F, h.2⟩ (by decide)
    (hl letProg "y" (E [S "held-atom", callFA]) [callFA])

theorem letSplit_of_rerun : ∀ D : Design, D.rerunValues = true → LetSplit D := by
  intro D
  rcases D with ⟨held, p, r, a, c, rep⟩
  unfold LetSplit
  cases held <;> cases p <;> cases r <;> cases a <;> cases c <;> cases rep <;> decide +kernel

/-- The `Number` to `Proc` counterexample: `5` under `Number`, refusing nothing, and something
else under `Proc`. -/
def NumberProcSplit (D : Design) : Prop :=
  runQ D (setResult (rangeProg .number) "g" .number) F qRange = some [(.val (N 5), ["g", "f"])] ∧
    runQ D (setResult (rangeProg .number) "g" .proc) F qRange ≠
      some [(.val (N 5), ["g", "f"])]

theorem not_keepsWeakening_of_numberProc {D : Design} (h : NumberProcSplit D) :
    ¬ KeepsWeakening D :=
  fun hw => h.2 (hw _ _ _ _ _ _ _ number_proc h.1 rfl)

theorem numberProcSplit_of : ∀ D : Design, D.holdsUnderProc = true → D.held ≠ .never →
    NumberProcSplit D := by
  intro D
  rcases D with ⟨held, p, r, a, c, rep⟩
  unfold NumberProcSplit
  cases held <;> cases p <;> cases r <;> cases a <;> cases c <;> cases rep <;> decide +kernel

/-- **The first three laws characterized**: values final, and held parameters not split between
`Proc` and the other computation types. -/
theorem first_three_laws_iff (D : Design) :
    (KeepsWeakening D ∧ KeepsLet D ∧ KeepsValuesFinal D) ↔
      (D.rerunValues = false ∧ (D.holdsUnderProc = false ∨ D.held = .never)) := by
  constructor
  · rintro ⟨hw, hl, _⟩
    refine ⟨?_, ?_⟩
    · cases hr : D.rerunValues
      · rfl
      · exact absurd hl (not_keepsLet_of_split (letSplit_of_rerun D hr))
    · cases hp : D.holdsUnderProc
      · exact .inl rfl
      · by_cases hn : D.held = .never
        · exact .inr hn
        · exact absurd hw (not_keepsWeakening_of_numberProc (numberProcSplit_of D hp hn))
  · rintro ⟨hr, h⟩
    exact ⟨keepsWeakening_of D h, keepsLet_of D hr, keepsValuesFinal_of D hr⟩

/-- The three held rules that keep the first three laws, each with its named design. -/
theorem three_rules_keep :
    (KeepsWeakening codeValue ∧ KeepsLet codeValue ∧ KeepsValuesFinal codeValue) ∧
      (KeepsWeakening byName ∧ KeepsLet byName ∧ KeepsValuesFinal byName) ∧
      (KeepsWeakening primeToday ∧ KeepsLet primeToday ∧ KeepsValuesFinal primeToday) :=
  ⟨(first_three_laws_iff _).mpr ⟨rfl, .inl rfl⟩, (first_three_laws_iff _).mpr ⟨rfl, .inl rfl⟩,
    (first_three_laws_iff _).mpr ⟨rfl, .inl rfl⟩⟩

/-! ## Identity insertion separates the root rule -/

/-- The identity counterexample: `(g (f a))` prints `5`, `(g' (f a))` prints `(f a)`. -/
def IdentitySplit (D : Design) : Prop :=
  answers D (identityProg .undef .undef [fA]) F (gQ callFA) = some [N 5] ∧
    answers D (identityProg .undef .undef [fA]) F (g'Q callFA) = some [callFA]

theorem not_keepsIdentity_of_split {D : Design} (h : IdentitySplit D) : ¬ KeepsIdentity D := by
  intro hi
  exact not_iff_of_prints ⟨F, h.1⟩ ⟨F, h.2⟩ (by decide)
    (hi [fA] .undef .undef callFA [callFA] (.inr (.inl rfl)) (.inr (.inl rfl)))

theorem identitySplit_of_root : ∀ D : Design, D.held = .root → D.rerunValues = false →
    IdentitySplit D := by
  intro D
  rcases D with ⟨held, p, r, a, c, rep⟩
  unfold IdentitySplit
  cases held <;> cases p <;> cases r <;> cases a <;> cases c <;> cases rep <;> decide +kernel

theorem heldRuns_uniform (D : Design) (h : D.held ≠ .root) :
    ∀ R, Unchecked R → heldRunsAt D (D.heldUnder R) true = heldRunsAt D (D.heldUnder R) false := by
  intro R _
  unfold heldRunsAt
  cases hh : D.held with
  | never => rfl
  | root => exact absurd hh h
  | everywhere => rfl

/-- **Weakening, `let`, values final and identity insertion hold exactly for the code-value and
by-name rules**, whatever the other three choices. -/
theorem four_laws_iff (D : Design) :
    (KeepsWeakening D ∧ KeepsLet D ∧ KeepsValuesFinal D ∧ KeepsIdentity D) ↔
      (D.rerunValues = false ∧ D.held ≠ .root ∧ (D.holdsUnderProc = false ∨ D.held = .never)) := by
  constructor
  · rintro ⟨hw, hl, hv, hi⟩
    obtain ⟨hr, hp⟩ := (first_three_laws_iff D).mp ⟨hw, hl, hv⟩
    refine ⟨hr, ?_, hp⟩
    intro hroot
    exact not_keepsIdentity_of_split (identitySplit_of_root D hroot hr) hi
  · rintro ⟨hr, hroot, hp⟩
    obtain ⟨hw, hl, hv⟩ := (first_three_laws_iff D).mpr ⟨hr, hp⟩
    exact ⟨hw, hl, hv, keepsIdentity_of D hr (heldRuns_uniform D hroot)⟩

/-- The held rules the four laws leave are exactly `never` and `everywhere`. -/
theorem four_laws_held_rule (D : Design)
    (h : KeepsWeakening D ∧ KeepsLet D ∧ KeepsValuesFinal D ∧ KeepsIdentity D) :
    D.held = .never ∨ (D.held = .everywhere ∧ D.holdsUnderProc = false) := by
  obtain ⟨_, hroot, hp⟩ := (four_laws_iff D).mp h
  cases hh : D.held with
  | never => exact .inl rfl
  | root => exact absurd hh hroot
  | everywhere =>
      rcases hp with hp | hp
      · exact .inr ⟨rfl, hp⟩
      · rw [hh] at hp; cases hp

/-- Both rules occur: code value and by-name keep the four laws, the Prime draft does not. -/
theorem four_laws_witnesses :
    (KeepsWeakening codeValue ∧ KeepsLet codeValue ∧ KeepsValuesFinal codeValue ∧
        KeepsIdentity codeValue) ∧
      (KeepsWeakening byName ∧ KeepsLet byName ∧ KeepsValuesFinal byName ∧
        KeepsIdentity byName) ∧
      ¬ (KeepsWeakening primeToday ∧ KeepsLet primeToday ∧ KeepsValuesFinal primeToday ∧
        KeepsIdentity primeToday) :=
  ⟨(four_laws_iff _).mpr ⟨rfl, by decide, .inl rfl⟩, (four_laws_iff _).mpr ⟨rfl, by decide, .inl rfl⟩,
    fun h => (four_laws_iff _).mp h |>.2.1 rfl⟩

/-! ## `Atom` results -/

/-- The `Atom`-result counterexample: `(= (g $x) (+ 1 2))` under `Atom` prints `3`. -/
def AtomSplit (D : Design) : Prop :=
  answers D [atomFn (E [S "+", N 1, N 2])] F (gQ (N 0)) = some [N 3]

theorem atomSplit_of : ∀ D : Design, D.atomBody = true → AtomSplit D := by
  intro D
  rcases D with ⟨held, p, r, a, c, rep⟩
  unfold AtomSplit
  cases held <;> cases p <;> cases r <;> cases a <;> cases c <;> cases rep <;> decide +kernel

/-- **An `Atom` result builds code exactly when its body is returned as written.** -/
theorem atomCode_iff (D : Design) : KeepsAtomCode D ↔ D.atomBody = false := by
  constructor
  · intro h
    cases ha : D.atomBody
    · rfl
    · have h1 := h [] (E [S "+", N 1, N 2]) (N 0)
      exact absurd (Prints.det h1 ⟨F, atomSplit_of D ha⟩) (by decide +kernel)
  · exact keepsAtomCode_of D

/-! ## The fork is one bit: the plain reading, or inert held text -/

/-- **Held text is inert**: `(= (g $x) $x)` with `$x` held returns the text as written, under every
computation type of the line. -/
def KeepsInertHeld (D : Design) : Prop :=
  ∀ (P0 : SProg) (R : Ty) (M : Atom), Unchecked R → Prints D (heldId "g" R :: P0) (gQ M) [M]

theorem keepsInertHeld_of (D : Design)
    (h : ∀ R, Unchecked R → heldRunsAt D (D.heldUnder R) true = false) : KeepsInertHeld D := by
  intro P0 R M hR
  refine ⟨0 + 4, ?_⟩
  rw [answers_eq, runQ_heldId D R hR P0 M 0, if_neg (by simp [h R hR])]
  rfl

/-- `(g (f a))` under `%Undefined%` runs to `5`, and `(f a)` prints `5`. -/
def RunSplit (D : Design) : Prop :=
  answers D (heldId "g" .undef :: [fA]) F (gQ callFA) = some [N 5] ∧
    answers D (heldId "g" .undef :: [fA]) F callFA = some [N 5]

/-- `(g (f a))` under `%Undefined%` returns `(f a)`, while `(f a)` prints `5`. -/
def HoldSplit (D : Design) : Prop :=
  answers D (heldId "g" .undef :: [fA]) F (gQ callFA) = some [callFA] ∧
    answers D (heldId "g" .undef :: [fA]) F callFA = some [N 5]

theorem runSplit_of : ∀ D : Design, D.held ≠ .never → RunSplit D := by
  intro D
  rcases D with ⟨held, p, r, a, c, rep⟩
  unfold RunSplit
  cases held <;> cases p <;> cases r <;> cases a <;> cases c <;> cases rep <;> decide +kernel

theorem holdSplit_of : ∀ D : Design, D.held = .never → HoldSplit D := by
  intro D
  rcases D with ⟨held, p, r, a, c, rep⟩
  unfold HoldSplit
  cases held <;> cases p <;> cases r <;> cases a <;> cases c <;> cases rep <;> decide +kernel

theorem not_inert_of_runSplit {D : Design} (h : RunSplit D) : ¬ KeepsInertHeld D := fun hk =>
  absurd (Prints.det (hk [fA] .undef callFA (.inr (.inl rfl))) ⟨F, h.1⟩) (by decide)

theorem not_plain_of_holdSplit {D : Design} (h : HoldSplit D) : ¬ KeepsPlainReading D :=
  fun hk => not_iff_of_prints ⟨F, h.1⟩ ⟨F, h.2⟩ (by decide)
    (hk [fA] .undef callFA [N 5] (.inr (.inl rfl)))

/-- **No design keeps both**: the plain reading says `(g (f a))` prints `5`, inertness says it
prints `(f a)`. -/
theorem not_plain_and_inert (D : Design) : ¬ (KeepsPlainReading D ∧ KeepsInertHeld D) := by
  rintro ⟨hp, hi⟩
  by_cases hn : D.held = .never
  · exact not_plain_of_holdSplit (holdSplit_of D hn) hp
  · exact not_inert_of_runSplit (runSplit_of D hn) hi

/-- **Under the four laws, the plain reading picks by-name.** -/
theorem plain_fork (D : Design) :
    (KeepsWeakening D ∧ KeepsLet D ∧ KeepsValuesFinal D ∧ KeepsIdentity D ∧
        KeepsPlainReading D) ↔
      (D.rerunValues = false ∧ D.held = .everywhere ∧ D.holdsUnderProc = false) := by
  constructor
  · rintro ⟨hw, hl, hv, hi, hp⟩
    obtain ⟨hr, _, _⟩ := (four_laws_iff D).mp ⟨hw, hl, hv, hi⟩
    rcases four_laws_held_rule D ⟨hw, hl, hv, hi⟩ with hn | ⟨he, hq⟩
    · exact absurd hp (not_plain_of_holdSplit (holdSplit_of D hn))
    · exact ⟨hr, he, hq⟩
  · rintro ⟨hr, he, hq⟩
    obtain ⟨hw, hl, hv, hi⟩ := (four_laws_iff D).mpr ⟨hr, by rw [he]; decide, .inl hq⟩
    refine ⟨hw, hl, hv, hi, keepsPlainReading_of D ?_⟩
    rintro R (rfl | rfl | rfl) <;> simp [heldRunsAt, he, Design.heldUnder, hq]

/-- **Under the four laws, inert held text picks code value.** -/
theorem inert_fork (D : Design) :
    (KeepsWeakening D ∧ KeepsLet D ∧ KeepsValuesFinal D ∧ KeepsIdentity D ∧
        KeepsInertHeld D) ↔
      (D.rerunValues = false ∧ D.held = .never) := by
  constructor
  · rintro ⟨hw, hl, hv, hi, hk⟩
    obtain ⟨hr, _, _⟩ := (four_laws_iff D).mp ⟨hw, hl, hv, hi⟩
    by_cases hn : D.held = .never
    · exact ⟨hr, hn⟩
    · exact absurd hk (not_inert_of_runSplit (runSplit_of D hn))
  · rintro ⟨hr, hn⟩
    obtain ⟨hw, hl, hv, hi⟩ := (four_laws_iff D).mpr ⟨hr, by rw [hn]; decide, .inr hn⟩
    refine ⟨hw, hl, hv, hi, keepsInertHeld_of D ?_⟩
    intro R _
    simp [heldRunsAt, hn]

/-- Both sides of the fork are inhabited. -/
theorem fork_witnesses :
    (KeepsWeakening byName ∧ KeepsLet byName ∧ KeepsValuesFinal byName ∧ KeepsIdentity byName ∧
        KeepsPlainReading byName) ∧
      (KeepsWeakening codeValue ∧ KeepsLet codeValue ∧ KeepsValuesFinal codeValue ∧
        KeepsIdentity codeValue ∧ KeepsInertHeld codeValue) :=
  ⟨(plain_fork _).mpr ⟨rfl, rfl, rfl⟩, (inert_fork _).mpr ⟨rfl, rfl⟩⟩

/-! ## The hybrid's column -/

/-- Under `Proc` the hybrid returns the held `(f a)` as written. -/
theorem hybrid_breaks_plainReading : ¬ KeepsPlainReading hybrid := by
  intro h
  have hg : Prints hybrid (heldId "g" .proc :: [fA]) (gQ callFA) [callFA] := ⟨F, by decide +kernel⟩
  have hM : Prints hybrid (heldId "g" .proc :: [fA]) callFA [N 5] := ⟨F, by decide +kernel⟩
  exact not_iff_of_prints hg hM (by decide) (h [fA] .proc callFA [N 5] (.inl rfl))

/-- HE's `if` written with a `Proc` result: the hybrid selects the branch and does not run it. -/
theorem hybrid_breaks_if : ¬ KeepsIf hybrid := by
  intro h
  have hif : Prints hybrid (myIf .proc :: [fA]) (ifQ callFA (E [S "boom"])) [callFA] :=
    ⟨F, by decide +kernel⟩
  have hM : Prints hybrid (myIf .proc :: [fA]) callFA [N 5] := ⟨F, by decide +kernel⟩
  exact not_iff_of_prints hif hM (by decide)
    (h [fA] .proc callFA (E [S "boom"]) [N 5] (.inl rfl) rfl rfl)

/-- The withdrawn hybrid against the laws. -/
theorem hybrid_laws :
    ¬ KeepsWeakening hybrid ∧ KeepsLet hybrid ∧ KeepsValuesFinal hybrid ∧
      ¬ KeepsPlainReading hybrid ∧ ¬ KeepsIf hybrid ∧ ¬ KeepsIdentity hybrid ∧
      ¬ KeepsAtomCode hybrid ∧ ¬ KeepsSubstitution hybrid :=
  ⟨hybrid_breaks_weakening, keepsLet_of _ rfl, keepsValuesFinal_of _ rfl,
    hybrid_breaks_plainReading, hybrid_breaks_if,
    not_keepsIdentity_of_split (identitySplit_of_root _ rfl rfl),
    fun h => absurd ((atomCode_iff hybrid).mp h) (by decide),
    valueFinal_designs_break_substitution.2.2.2⟩

/-! ## The Prime test lines, design by design -/

/-- `(roles:compute (roles:hold (+ 7 8)))` from the same test file, with `roles:compute` an
evaluated identity: a value passed on stays a value. -/
def rolesValueProg : SProg := [heldId "roles:hold" .atom, valueId "roles:compute" .proc]

/-- The answers each design gives on the three conflicting lines and on the values-final line. -/
theorem prime_test_lines :
    (answers he testUndefProg F testUndefQuery = some [N 5] ∧
      answers he testProcProg F testProcQuery = some [N 3] ∧
      answers he testRolesProg F testRolesQuery = some [N 9] ∧
      answers he rolesValueProg F
        (E [S "roles:compute", E [S "roles:hold", E [S "+", N 7, N 8]]]) = some [N 15]) ∧
    (answers byName testUndefProg F testUndefQuery = some [N 5] ∧
      answers byName testProcProg F testProcQuery = some [N 3] ∧
      answers byName testRolesProg F testRolesQuery = some [N 9] ∧
      answers byName rolesValueProg F
        (E [S "roles:compute", E [S "roles:hold", E [S "+", N 7, N 8]]]) =
          some [E [S "+", N 7, N 8]]) ∧
    (answers codeValue testUndefProg F testUndefQuery = some [callFA] ∧
      answers codeValue testProcProg F testProcQuery = some [E [S "+", N 1, N 2]] ∧
      answers codeValue testRolesProg F testRolesQuery = some [E [S "+", N 4, N 5]] ∧
      answers codeValue rolesValueProg F
        (E [S "roles:compute", E [S "roles:hold", E [S "+", N 7, N 8]]]) =
          some [E [S "+", N 7, N 8]]) ∧
    (answers primeToday testUndefProg F testUndefQuery = some [N 5] ∧
      answers primeToday testProcProg F testProcQuery = some [N 3] ∧
      answers primeToday testRolesProg F testRolesQuery = some [N 9] ∧
      answers primeToday rolesValueProg F
        (E [S "roles:compute", E [S "roles:hold", E [S "+", N 7, N 8]]]) =
          some [E [S "+", N 7, N 8]]) ∧
    (answers hybrid testUndefProg F testUndefQuery = some [N 5] ∧
      answers hybrid testProcProg F testProcQuery = some [E [S "+", N 1, N 2]] ∧
      answers hybrid testRolesProg F testRolesQuery = some [E [S "+", N 4, N 5]] ∧
      answers hybrid rolesValueProg F
        (E [S "roles:compute", E [S "roles:hold", E [S "+", N 7, N 8]]]) =
          some [E [S "+", N 7, N 8]]) := by
  decide +kernel

/-! ## The plain reading for evaluated parameters -/

/-- `(: vg (-> %Undefined% %Undefined%)) (= (vg $x) (held-atom $x))`: an evaluated parameter used
at a held position. -/
def valueAtHeld : SProg :=
  [fA, heldId "held-atom" .atom,
    ⟨"vg", some ([.undef], .undef), [([V "x"], E [S "held-atom", V "x"])]⟩]

/-- **The plain reading fails for an evaluated parameter used at a held position, in every named
design**: `(vg (f a))` passes the value `5` on, while the body with `(f a)` written in for `$x`
holds `(f a)`. The plain reading of an evaluated parameter holds only where its occurrences are at
computation positions (the bare body: `KeepsValuesFinal`). -/
theorem value_param_at_held_position :
    (answers he valueAtHeld F (E [S "vg", callFA]) = some [N 5] ∧
      answers he valueAtHeld F (E [S "held-atom", callFA]) = some [callFA]) ∧
    (answers byName valueAtHeld F (E [S "vg", callFA]) = some [N 5] ∧
      answers byName valueAtHeld F (E [S "held-atom", callFA]) = some [callFA]) ∧
    (answers codeValue valueAtHeld F (E [S "vg", callFA]) = some [N 5] ∧
      answers codeValue valueAtHeld F (E [S "held-atom", callFA]) = some [callFA]) ∧
    (answers primeToday valueAtHeld F (E [S "vg", callFA]) = some [N 5] ∧
      answers primeToday valueAtHeld F (E [S "held-atom", callFA]) = some [callFA]) ∧
    (answers hybrid valueAtHeld F (E [S "vg", callFA]) = some [N 5] ∧
      answers hybrid valueAtHeld F (E [S "held-atom", callFA]) = some [callFA]) := by
  decide +kernel

end Separation

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.EvaluationModes
