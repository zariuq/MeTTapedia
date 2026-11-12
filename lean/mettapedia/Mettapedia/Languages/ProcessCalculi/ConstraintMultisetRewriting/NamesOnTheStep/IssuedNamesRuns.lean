import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamesOnTheStep.IssuedNamesControls

/-!
# Issuing is necessary, and not stricter than necessary: the runs

Concrete runs and refusals on the first-order step over ground terms (`IssuedNamesControls`).

## The use check is necessary

* `freshOnly_derives_W`: in the theory with consumption, without the use check, a run makes `W`:
  `r1` writes `A 0` before `r2` issues `0`. With issuing no run does (`issuing_never_derives_W`).
* In the theory with an absence guard (`k04`: `p` makes `A x`; `nw` issues `n` and makes `B n`;
  `gd` keeps `B n`, asks that `A n` be absent and makes `V n`):
  - `issuing_refuses_an_unissued_name`, `issuing_admits_the_guard`: with issuing, `p` on the unissued
    `0` is refused, and after `nw` issues `0` the guard is admitted;
  - `freshOnly_issued_name_is_in_the_store`, `freshOnly_refuses_the_guard`: without the use check,
    `p` writes `A 0`, the name `nw` then issues is already in the store, and the guard is refused.

## Freshness is necessary

* `usesOnly_reissues_a_used_name`, `usesOnly_refuses_the_guard`: without freshness, `nw` issues `0`
  a second time after `A 0` was made, and the guard is refused; `issuing_refuses_reissue`: issuing
  refuses any second issue.

## Not stricter than necessary

* `issued_name_is_accepted` (k30): `p` on `0`, refused before `0` is issued, is admitted after.
* `codes_need_no_issuing`: the code of a closed term, and a constant, are written at the empty
  ledger.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamesOnTheStep.IssuingControls

/-! ## The theory with consumption, without the use check -/

def g1 : Fir := ⟨r1 (.name 0), [], ⟨[], [(factT, 0)], [(factA (.name 0), 0)]⟩⟩
def g2 : Fir := ⟨r0, [], ⟨[(factT, 0)], [], [(factU, 0)]⟩⟩
def g3 : Fir := ⟨r2 0, [], ⟨[], [(factU, 0)], [(factB (.name 0), 0)]⟩⟩
def g4 : Fir := ⟨r3 (.name 0), [], ⟨[], [(factA (.name 0), 0), (factB (.name 0), 0)], [(factW, 0)]⟩⟩

abbrev fo29 := withLedger base (freshOnly k29)

theorem fo29a1 : fo29.Admits (s := start) (g1, []) :=
  admits_of (by decide) (by decide) rfl rfl rfl (by decide) (by decide) rfl (no_checks rfl)
    ⟨⟨List.nodup_nil, fun _ member => absurd member List.not_mem_nil⟩, Or.inl ⟨_, rfl, rfl⟩⟩

theorem fo29a2 : fo29.Admits (s := fo29.result (s := start) _ fo29a1) (g2, []) :=
  admits_of (by decide) (by decide) rfl rfl rfl (by decide) (by decide) rfl (no_checks rfl)
    ⟨⟨List.nodup_nil, fun _ member => absurd member List.not_mem_nil⟩, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩

theorem fo29a3 :
    fo29.Admits (s := fo29.result (s := fo29.result (s := start) _ fo29a1) _ fo29a2) (g3, [0]) := by
  refine admits_of (by decide) (by decide) rfl rfl rfl (by decide) (by decide) rfl (no_checks rfl)
    ⟨⟨List.nodup_singleton 0, ?_⟩, Or.inr (Or.inr (Or.inl ⟨0, rfl, rfl⟩))⟩
  intro n member
  simp only [List.mem_singleton] at member
  subst member
  show (0 : ℕ) ∉ (start.2 ∪ {n | n ∈ ([] : List ℕ)}) ∪ {n | n ∈ ([] : List ℕ)}
  simp [start]

theorem fo29a4 :
    fo29.Admits (s := fo29.result (s := fo29.result (s := fo29.result (s := start) _ fo29a1) _ fo29a2)
      _ fo29a3) (g4, []) :=
  admits_of (by decide) (by decide) rfl rfl rfl (by decide) (by decide) rfl (no_checks rfl)
    ⟨⟨List.nodup_nil, fun _ member => absurd member List.not_mem_nil⟩,
      Or.inr (Or.inr (Or.inr ⟨_, rfl, rfl⟩))⟩

/-- The run of the four firings. -/
def fo29Run : fo29.Run start :=
  .cons _ fo29a1 (.cons _ fo29a2 (.cons _ fo29a3 (.cons _ fo29a4 (.nil _))))

/-- **Without the use check, a run makes `W`.** `r1` is given the name `0` before `r2` issues it. -/
theorem freshOnly_derives_W :
    ∃ r : (withLedger base (freshOnly k29)).Run start, ∃ o ∈ r.last.1.present, o.1 = factW :=
  ⟨fo29Run, (factW, 0), by decide, rfl⟩

/-! ## The theory with an absence guard -/

def p (x : Expr) : RuleInstance Expr := rule [] [] [factA x]
def nw (n : ℕ) : RuleInstance Expr := rule [] [] [factB (.name n)]
def gd (n : ℕ) : RuleInstance Expr :=
  rule [] [factB (.name n)] [factV (.name n)] [.absent (factA (.name n))]

/-- The theory: a pure maker, an issuer, and a guard that the issued name is unused. -/
abbrev k04 (f : Fir) (fresh : List ℕ) : Prop :=
  (∃ x, f.rule = p x ∧ fresh = []) ∨ (∃ n, f.rule = nw n ∧ fresh = [n]) ∨
    (∃ n, f.rule = gd n ∧ fresh = [])

/-- The empty store, with nothing issued. -/
def empty : Conf × Set ℕ := (⟨[], ∅⟩, ∅)

def makeA (x : Expr) (copy : ℕ) : Fir := ⟨p x, [], ⟨[], [], [(factA x, copy)]⟩⟩
def issue (n copy : ℕ) : Fir := ⟨nw n, [], ⟨[], [], [(factB (.name n), copy)]⟩⟩
def guard (n copy : ℕ) : Fir :=
  ⟨gd n, [], ⟨[], [(factB (.name n), copy)], [(factV (.name n), 0)]⟩⟩

/-- The names `issue n copy` writes. -/
theorem issue_writes {n copy m : ℕ} (written : m ∈ firingNames Expr.names (issue n copy)) : m = n := by
  rcases mem_firingNames.mp written with ⟨_, member, _⟩ | ⟨_, member, _⟩ | ⟨_, member, _⟩ |
      ⟨t, member, named⟩
  · simp [issue, nw, rule] at member
  · simp [issue, nw, rule] at member
  · simp [issue, nw, rule] at member
  · simp only [issue, nw, rule, List.mem_singleton] at member
    subst member
    simpa [factB] using named

/-- The names `makeA x copy` writes. -/
theorem makeA_writes {x : Expr} {copy m : ℕ} (written : m ∈ firingNames Expr.names (makeA x copy)) :
    m ∈ x.support := by
  rcases mem_firingNames.mp written with ⟨_, member, _⟩ | ⟨_, member, _⟩ | ⟨_, member, _⟩ |
      ⟨t, member, named⟩
  · simp [makeA, p, rule] at member
  · simp [makeA, p, rule] at member
  · simp [makeA, p, rule] at member
  · simp only [makeA, p, rule, List.mem_singleton] at member
    subst member
    simpa [factA] using named

/-- The names `guard n copy` writes. -/
theorem guard_writes {n copy m : ℕ} (written : m ∈ firingNames Expr.names (guard n copy)) : m = n := by
  rcases mem_firingNames.mp written with ⟨_, member, _⟩ | ⟨t, member, named⟩ | ⟨_, member, _⟩ |
      ⟨t, member, named⟩
  · simp [guard, gd, rule] at member
  · simp only [guard, gd, rule, List.mem_singleton] at member
    subst member
    simpa [factB] using named
  · simp [guard, gd, rule] at member
  · simp only [guard, gd, rule, List.mem_singleton] at member
    subst member
    simpa [factV] using named

/-! ### With issuing -/

abbrev is04 := withLedger base (issuing k04)

/-- **Issuing refuses the pure firing on an unissued name**, whatever its selection. -/
theorem issuing_refuses_an_unissued_name (f : Fir) (made : f.rule = p (.name 0)) :
    ¬ is04.Admits (s := empty) (f, []) := by
  intro admitted
  have written : 0 ∈ naming.firing (s := empty.1) f := by
    apply mem_firingNames.mpr
    refine Or.inr (Or.inr (Or.inr ⟨factA (.name 0), ?_, ?_⟩))
    · rw [made]
      simp [p, rule]
    · simp [factA]
  have issued := admitted.2.1.2.2 written
  simp [empty] at issued

theorem is04a1 : is04.Admits (s := empty) (issue 0 0, [0]) := by
  refine admits_of (by decide) (by decide) rfl rfl rfl (by decide) (by decide) rfl (no_checks rfl)
    ⟨⟨List.nodup_singleton 0, ?_, ?_⟩, Or.inr (Or.inl ⟨0, rfl, rfl⟩)⟩
  · intro n _
    simp [empty]
  · intro n written
    rw [issue_writes written]
    simp

theorem is04a2 : is04.Admits (s := is04.result (s := empty) _ is04a1) (guard 0 0, []) := by
  refine admits_of (by decide) (by decide) rfl rfl rfl (by decide) (by decide) rfl ?_
    ⟨⟨List.nodup_nil, fun _ member => absurd member List.not_mem_nil, ?_⟩,
      Or.inr (Or.inr ⟨0, rfl, rfl⟩)⟩
  · intro c member
    simp only [gd, rule, List.mem_singleton] at member
    subst member
    exact absent_holds (by decide)
  · intro n written
    rw [guard_writes written]
    show (0 : ℕ) ∈ (empty.2 ∪ {n | n ∈ [0]}) ∪ {n | n ∈ ([] : List ℕ)}
    simp

/-- **With issuing, the guard is admitted once `0` is issued.** -/
theorem issuing_admits_the_guard :
    ∃ r : is04.Run empty, r.word.length = 2 ∧ ∃ o ∈ r.last.1.present, o.1 = factV (.name 0) :=
  ⟨.cons _ is04a1 (.cons _ is04a2 (.nil _)), rfl, (factV (.name 0), 0), by decide, rfl⟩

/-! ### Without the use check -/

abbrev fo04 := withLedger base (freshOnly k04)

theorem fo04a1 : fo04.Admits (s := empty) (makeA (.name 0) 0, []) :=
  admits_of (by decide) (by decide) rfl rfl rfl (by decide) (by decide) rfl (no_checks rfl)
    ⟨⟨List.nodup_nil, fun _ member => absurd member List.not_mem_nil⟩, Or.inl ⟨_, rfl, rfl⟩⟩

/-- The state where `nw` issues `0`, under `freshOnly`. -/
noncomputable def freshOnlyBefore : Conf × Set ℕ := fo04.result (s := empty) _ fo04a1

theorem fo04a2 : fo04.Admits (s := freshOnlyBefore) (issue 0 0, [0]) := by
  refine admits_of (by decide) (by decide) rfl rfl rfl (by decide) (by decide) rfl (no_checks rfl)
    ⟨⟨List.nodup_singleton 0, ?_⟩, Or.inr (Or.inl ⟨0, rfl, rfl⟩)⟩
  intro n member
  simp only [List.mem_singleton] at member
  subst member
  show (0 : ℕ) ∉ empty.2 ∪ {n | n ∈ ([] : List ℕ)}
  simp [empty]

/-- The state after `nw` issued `0`, under `freshOnly`. -/
noncomputable def freshOnlyAfter : Conf × Set ℕ := fo04.result (s := freshOnlyBefore) _ fo04a2

/-- **Without the use check, the name `nw` issues is already in the store.** -/
theorem freshOnly_issued_name_is_in_the_store :
    0 ∉ freshOnlyBefore.2 ∧ 0 ∈ naming.state freshOnlyBefore.1 := by
  refine ⟨?_, mem_configurationNames.mpr (Or.inr ⟨(factA (.name 0), 0), by decide, ?_⟩)⟩
  · show (0 : ℕ) ∉ empty.2 ∪ {n | n ∈ ([] : List ℕ)}
    simp [empty]
  · simp [factA]

/-- **Without the use check, the guard is refused**, whatever its selection. -/
theorem freshOnly_refuses_the_guard (f : Fir) (asks : f.rule = gd 0) :
    ¬ fo04.Admits (s := freshOnlyAfter) (f, []) := by
  intro admitted
  have valid : f.selection.Valid ground Prod.fst f.rule freshOnlyAfter.1 := valid_of admitted
  exact absent_refuted valid (p := factA (.name 0)) (by rw [asks]; simp [gd, rule])
    (o := (factA (.name 0), 0)) (by decide) rfl

/-! ### Without freshness -/

abbrev uo04 := withLedger base (usesOnly k04)

theorem uo04a1 : uo04.Admits (s := empty) (issue 0 0, [0]) := by
  refine admits_of (by decide) (by decide) rfl rfl rfl (by decide) (by decide) rfl (no_checks rfl)
    ⟨?_, Or.inr (Or.inl ⟨0, rfl, rfl⟩)⟩
  intro n written
  rw [issue_writes written]
  simp

theorem uo04a2 : uo04.Admits (s := uo04.result (s := empty) _ uo04a1) (makeA (.name 0) 0, []) := by
  refine admits_of (by decide) (by decide) rfl rfl rfl (by decide) (by decide) rfl (no_checks rfl)
    ⟨?_, Or.inl ⟨_, rfl, rfl⟩⟩
  intro n written
  have zero : n = 0 := by simpa using makeA_writes written
  subst zero
  show (0 : ℕ) ∈ (empty.2 ∪ {n | n ∈ [0]}) ∪ {n | n ∈ ([] : List ℕ)}
  simp

/-- The state where `nw` issues `0` the second time, under `usesOnly`. -/
noncomputable def usesOnlyBefore : Conf × Set ℕ :=
  uo04.result (s := uo04.result (s := empty) _ uo04a1) _ uo04a2

theorem uo04a3 : uo04.Admits (s := usesOnlyBefore) (issue 0 1, [0]) := by
  refine admits_of (by decide) (by decide) rfl rfl rfl (by decide) (by decide) rfl (no_checks rfl)
    ⟨?_, Or.inr (Or.inl ⟨0, rfl, rfl⟩)⟩
  intro n written
  rw [issue_writes written]
  simp

/-- The state after the second issue of `0`, under `usesOnly`. -/
noncomputable def usesOnlyAfter : Conf × Set ℕ := uo04.result (s := usesOnlyBefore) _ uo04a3

/-- **Without freshness, a name is issued that was issued before and is already in the store.** -/
theorem usesOnly_reissues_a_used_name :
    0 ∈ usesOnlyBefore.2 ∧ 0 ∈ naming.state usesOnlyBefore.1 := by
  refine ⟨?_, mem_configurationNames.mpr (Or.inr ⟨(factA (.name 0), 0), by decide, ?_⟩)⟩
  · show (0 : ℕ) ∈ (empty.2 ∪ {n | n ∈ [0]}) ∪ {n | n ∈ ([] : List ℕ)}
    simp
  · simp [factA]

/-- **Without freshness, the guard is refused**, whatever its selection. -/
theorem usesOnly_refuses_the_guard (f : Fir) (asks : f.rule = gd 0) :
    ¬ uo04.Admits (s := usesOnlyAfter) (f, []) := by
  intro admitted
  have valid : f.selection.Valid ground Prod.fst f.rule usesOnlyAfter.1 := valid_of admitted
  exact absent_refuted valid (p := factA (.name 0)) (by rw [asks]; simp [gd, rule])
    (o := (factA (.name 0), 0)) (by decide) rfl

/-- **Issuing refuses any second issue of a name**, whatever the firing. -/
theorem issuing_refuses_reissue {σ : Conf × Set ℕ} (issued : 0 ∈ σ.2) (f : Fir) :
    ¬ is04.Admits (s := σ) (f, [0]) :=
  fun admitted => admitted.2.1.2.1 0 (List.mem_singleton_self 0) issued

/-! ## Not stricter than necessary -/

theorem is04p : is04.Admits (s := is04.result (s := empty) _ is04a1) (makeA (.name 0) 0, []) := by
  refine admits_of (by decide) (by decide) rfl rfl rfl (by decide) (by decide) rfl (no_checks rfl)
    ⟨⟨List.nodup_nil, fun _ member => absurd member List.not_mem_nil, ?_⟩, Or.inl ⟨_, rfl, rfl⟩⟩
  intro n written
  have zero : n = 0 := by simpa using makeA_writes written
  subst zero
  show (0 : ℕ) ∈ (empty.2 ∪ {n | n ∈ [0]}) ∪ {n | n ∈ ([] : List ℕ)}
  simp

/-- **k30: an issued name is accepted.** `p` on `0`, refused at the empty ledger, is admitted once
`nw` has issued `0`. -/
theorem issued_name_is_accepted :
    ¬ is04.Admits (s := empty) (makeA (.name 0) 0, []) ∧
      is04.Admits (s := is04.result (s := empty) _ is04a1) (makeA (.name 0) 0, []) :=
  ⟨issuing_refuses_an_unissued_name _ rfl, is04p⟩

/-- **Codes need no issuing**: the code of a closed term, and a constant, are written at the empty
ledger by the calculus's discipline. -/
theorem codes_need_no_issuing :
    is04.Admits (s := empty) (makeA (quote (.app (.sym 1) (.sym 2))) 0, []) ∧
      is04.Admits (s := empty) (makeA (.sym 5) 0, []) := by
  constructor
  · refine admits_of (by decide) (by decide) rfl rfl rfl (by decide) (by decide) rfl (no_checks rfl)
      ⟨⟨List.nodup_nil, fun _ member => absurd member List.not_mem_nil, ?_⟩, Or.inl ⟨_, rfl, rfl⟩⟩
    intro n written
    have closed := makeA_writes written
    simp [quote] at closed
  · refine admits_of (by decide) (by decide) rfl rfl rfl (by decide) (by decide) rfl (no_checks rfl)
      ⟨⟨List.nodup_nil, fun _ member => absurd member List.not_mem_nil, ?_⟩, Or.inl ⟨_, rfl, rfl⟩⟩
    intro n written
    have closed := makeA_writes written
    simp at closed

#print axioms freshOnly_derives_W
#print axioms issuing_refuses_an_unissued_name
#print axioms issuing_admits_the_guard
#print axioms freshOnly_issued_name_is_in_the_store
#print axioms freshOnly_refuses_the_guard
#print axioms usesOnly_reissues_a_used_name
#print axioms usesOnly_refuses_the_guard
#print axioms issuing_refuses_reissue
#print axioms issued_name_is_accepted
#print axioms codes_need_no_issuing

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamesOnTheStep.IssuingControls
