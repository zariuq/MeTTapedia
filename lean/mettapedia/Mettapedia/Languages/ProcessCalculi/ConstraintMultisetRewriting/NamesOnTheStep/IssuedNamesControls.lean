import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamesOnTheStep.FirstOrderNames
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamesOnTheStep.StructuralCodes

/-!
# Issuing on the first-order step: the theory with consumption

The controls of issuing run on the first-order instance of the step over ground terms with
generative names and codes (`base`), under its naming (`naming`), through the ledger step with three
disciplines:

* `issuing`: the calculus's discipline (`Issues`), restricted to a theory;
* `freshOnly`: issued names are new, but a written name need not have been issued;
* `usesOnly`: written names must have been issued, but an issued name need not be new.

This module reads admission of ground firings (`valid_of`, `present_after`, `reads_match`, ...),
builds admissions (`admits_of`), and proves the strong half of the first control.

**A theory with consumption** (`k29`): `r1` keeps `T` and makes `A x` for a caller-given `x`; `r0`
takes `T` and makes `U`; `r2` keeps `U`, issues `n` and makes `B n`; `r3` keeps `A x` and `B x` and
makes `W`. From the store holding one `T`, **no run of the theory with issuing ever makes `W`**
(`issuing_never_derives_W`): every reached state satisfies `K29`. While `T` is present nothing is
issued, so every `A x` has a closed argument, and every `B x` has a generative name as argument.
`IssuedNamesRuns.freshOnly_derives_W` is the run that makes `W` without the use check.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamesOnTheStep.IssuingControls

open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)

/-- Ground terms: the identity is the only solution, and equal means identical. -/
def ground : SubstitutionAction Expr Unit where
  E := Eq
  equivalence := ⟨fun _ => rfl, fun same => same.symm, fun first second => first.trans second⟩
  apply := fun _ e => e
  identity := ()
  compose := fun _ _ => ()
  apply_identity := fun _ => rfl
  apply_compose := fun _ _ _ => rfl
  preserves := fun _ _ _ same => same

/-- An occurrence: its label and a copy number. -/
abbrev Occ := Expr × ℕ
abbrev Conf := Configuration Expr Occ
abbrev Fir := AnnotatedRuns.Firing Expr Unit Occ

/-- The first-order step over ground terms. -/
abbrev base := (AnnotatedRuns.firstOrder ground (Prod.fst : Occ → Expr)).toStep

/-- Its naming: the support of terms. -/
abbrev naming : Mentions base ℕ := firstOrderMentions ground Prod.fst Expr.names

abbrev Disc := Discipline Conf (fun _ => Fir) ℕ

/-- The calculus's discipline, restricted to a theory. -/
abbrev issuing (theory : Fir → List ℕ → Prop) : Disc :=
  fun s issued f fresh => Issues naming s issued f fresh ∧ theory f fresh

/-- Fresh names are new, but a written name need not have been issued. -/
abbrev freshOnly (theory : Fir → List ℕ → Prop) : Disc :=
  fun _ issued f fresh => (fresh.Nodup ∧ ∀ n ∈ fresh, n ∉ issued) ∧ theory f fresh

/-- Written names must have been issued, but an issued name need not be new. -/
abbrev usesOnly (theory : Fir → List ℕ → Prop) : Disc :=
  fun s issued f fresh => naming.firing (s := s) f ⊆ issued ∪ {n | n ∈ fresh} ∧ theory f fresh

/-! ## Facts and rules -/

def factT : Expr := .sym 10
def factU : Expr := .sym 11
def factW : Expr := .sym 12
def factA (x : Expr) : Expr := .app (.sym 13) x
def factB (x : Expr) : Expr := .app (.sym 14) x
def factV (x : Expr) : Expr := .app (.sym 15) x

/-- A rule instance without tells. -/
def rule (take read produce : List Expr) (checks : List (Check Expr) := []) : RuleInstance Expr :=
  ⟨take, read, [], checks, produce⟩

/-! ## Reading admission over ground terms -/

section Reading

variable {D : Disc}

theorem valid_of {σ : Conf × Set ℕ} {f : Fir × List ℕ} (admitted : (withLedger base D).Admits (s := σ) f) :
    f.1.selection.Valid ground Prod.fst f.1.rule σ.1 :=
  (show f.1.Valid ground Prod.fst σ.1 from admitted.1).firing

theorem present_after {σ : Conf × Set ℕ} {f : Fir × List ℕ} (admitted : (withLedger base D).Admits (s := σ) f)
    {o : Occ} : o ∈ ((withLedger base D).result (s := σ) f admitted).1.present ↔
      (o ∈ σ.1.present ∧ o ∉ f.1.selection.taken) ∨ o ∈ f.1.selection.made := by
  change o ∈ fire σ.1.present (f.1.selection.commit (T := Expr)) ↔ _
  rw [mem_fire]
  simp [Selection.commit]

theorem ledger_after {σ : Conf × Set ℕ} {f : Fir × List ℕ} (admitted : (withLedger base D).Admits (s := σ) f) :
    ((withLedger base D).result (s := σ) f admitted).2 = σ.2 ∪ {n | n ∈ f.2} := rfl

theorem reads_match {C : Conf} {r : RuleInstance Expr} {sel : Selection Occ}
    (valid : sel.Valid ground Prod.fst r C) :
    List.Forall₂ (fun p (o : Occ) => p = o.1) r.read sel.read := by
  obtain ⟨u, solved⟩ := valid.consistent
  exact (Selection.models_problem ground valid solved).2.2.1

theorem takes_match {C : Conf} {r : RuleInstance Expr} {sel : Selection Occ}
    (valid : sel.Valid ground Prod.fst r C) :
    List.Forall₂ (fun p (o : Occ) => p = o.1) r.take sel.taken := by
  obtain ⟨u, solved⟩ := valid.consistent
  exact (Selection.models_problem ground valid solved).2.1

theorem read_present {C : Conf} {r : RuleInstance Expr} {sel : Selection Occ}
    (valid : sel.Valid ground Prod.fst r C) {o : Occ} (member : o ∈ sel.read) : o ∈ C.present :=
  valid.occurrences.kept_subset (show o ∈ sel.read.toFinset from List.mem_toFinset.mpr member)

theorem taken_present {C : Conf} {r : RuleInstance Expr} {sel : Selection Occ}
    (valid : sel.Valid ground Prod.fst r C) {o : Occ} (member : o ∈ sel.taken) : o ∈ C.present :=
  valid.occurrences.taken_subset (show o ∈ sel.taken.toFinset from List.mem_toFinset.mpr member)

theorem made_label {C : Conf} {r : RuleInstance Expr} {sel : Selection Occ}
    (valid : sel.Valid ground Prod.fst r C) {o : Occ} (member : o ∈ sel.made) : o.1 ∈ r.produce := by
  rw [← valid.outputs]
  exact List.mem_map_of_mem member

theorem match_one {p : Expr} {l : List Occ} (h : List.Forall₂ (fun p (o : Occ) => p = o.1) [p] l) :
    ∃ o, l = [o] ∧ p = o.1 := by
  cases h with
  | cons head tail =>
      cases tail
      exact ⟨_, rfl, head⟩

theorem match_two {p q : Expr} {l : List Occ}
    (h : List.Forall₂ (fun p (o : Occ) => p = o.1) [p, q] l) :
    ∃ o o', l = [o, o'] ∧ p = o.1 ∧ q = o'.1 := by
  cases h with
  | cons head tail =>
      cases tail with
      | cons head' tail' =>
          cases tail'
          exact ⟨_, _, rfl, head, head'⟩

/-- An absence check over ground terms is refuted by one present occurrence of its pattern. -/
theorem absent_refuted {C : Conf} {r : RuleInstance Expr} {sel : Selection Occ}
    (valid : sel.Valid ground Prod.fst r C) {p : Expr} (asked : Check.absent p ∈ r.checks)
    {o : Occ} (present : o ∈ C.present) (labelled : o.1 = p) : False := by
  obtain ⟨u, solved⟩ := valid.consistent
  exact valid.checks _ asked u solved o present labelled.symm

end Reading

/-! ## Building admissions over ground terms -/

theorem equations_self : ∀ {l : List Occ} {e : Equation Expr},
    e ∈ Selection.equations Prod.fst (l.map Prod.fst) l → e.1 = e.2
  | [], _, member => by simp [Selection.equations] at member
  | _ :: _, _, member => by
      simp only [List.map_cons, Selection.equations, List.zipWith_cons_cons, List.mem_cons] at member
      rcases member with here | later
      · subst here
        rfl
      · exact equations_self later

theorem admits_of {D : Disc} {σ : Conf × Set ℕ} {r : RuleInstance Expr} {sel : Selection Occ}
    {fresh : List ℕ} (takenDistinct : sel.taken.Nodup) (madeDistinct : sel.made.Nodup)
    (takes : r.take = sel.taken.map Prod.fst) (reads : r.read = sel.read.map Prod.fst)
    (outputs : sel.made.map Prod.fst = r.produce)
    (enabled : Enabled Prod.fst σ.1.present (sel.commit (T := Expr)))
    (knowledge : ∀ e ∈ σ.1.equations, e.1 = e.2) (noTells : r.tell = [])
    (checks : ∀ c ∈ r.checks, c.Holds ground () Prod.fst σ.1.present)
    (discipline : D σ.1 σ.2 ⟨r, [], sel⟩ fresh) :
    (withLedger base D).Admits (s := σ) (⟨r, [], sel⟩, fresh) := by
  refine ⟨(PredicateQueryAdmission.valid_empty_iff ground Prod.fst r σ.1 sel).mpr
    ⟨takenDistinct, madeDistinct, by rw [takes, List.length_map], by rw [reads, List.length_map],
      outputs, enabled, ⟨(), ?_⟩, ?_⟩, discipline⟩
  · intro e member
    simp only [Selection.problem, List.mem_append, noTells, List.not_mem_nil, or_false] at member
    rcases member with (old | taken) | read
    · exact knowledge e old
    · rw [takes] at taken
      exact equations_self taken
    · rw [reads] at read
      exact equations_self read
  · intro c member u _
    exact checks c member

theorem no_checks {r : RuleInstance Expr} (none : r.checks = []) {C : Conf} :
    ∀ c ∈ r.checks, c.Holds ground () Prod.fst C.present := by
  rw [none]
  intro c member
  exact absurd member List.not_mem_nil

theorem absent_holds {C : Conf} {p : Expr} (clear : ∀ o ∈ C.present, o.1 ≠ p) :
    (Check.absent p).Holds ground () Prod.fst C.present :=
  fun o present same => clear o present same.symm

/-! ## The use check is necessary: a theory with consumption -/

def r1 (x : Expr) : RuleInstance Expr := rule [] [factT] [factA x]
def r0 : RuleInstance Expr := rule [factT] [] [factU]
def r2 (n : ℕ) : RuleInstance Expr := rule [] [factU] [factB (.name n)]
def r3 (x : Expr) : RuleInstance Expr := rule [] [factA x, factB x] [factW]

/-- The theory: its four rules and the names each issues. -/
abbrev k29 (f : Fir) (fresh : List ℕ) : Prop :=
  (∃ x, f.rule = r1 x ∧ fresh = []) ∨ (f.rule = r0 ∧ fresh = []) ∨
    (∃ n, f.rule = r2 n ∧ fresh = [n]) ∨ (∃ x, f.rule = r3 x ∧ fresh = [])

/-- The store holding one `T`, with nothing issued. -/
def start : Conf × Set ℕ := (⟨[], {(factT, 0)}⟩, ∅)

/-- What every reached state of the theory with issuing satisfies. -/
structure K29 (σ : Conf × Set ℕ) : Prop where
  aClosed : ∀ o ∈ σ.1.present, ∀ x, o.1 = factA x → x.support = ∅
  bNamed : ∀ o ∈ σ.1.present, ∀ x, o.1 = factB x → ∃ n, x = .name n
  whileT : ∀ o ∈ σ.1.present, o.1 = factT → σ.2 = ∅
  afterU : ∀ o ∈ σ.1.present, o.1 = factU → ∀ o' ∈ σ.1.present, o'.1 ≠ factT
  oneT : ∀ o ∈ σ.1.present, ∀ o' ∈ σ.1.present, o.1 = factT → o'.1 = factT → o = o'
  noW : ∀ o ∈ σ.1.present, o.1 ≠ factW

theorem k29_start : K29 start := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [start, factT, factU, factW, factA, factB]

theorem k29_result {σ : Conf × Set ℕ} (f : Fir × List ℕ)
    (admitted : (withLedger base (issuing k29)).Admits (s := σ) f) (inv : K29 σ) :
    K29 ((withLedger base (issuing k29)).result (s := σ) f admitted) := by
  have valid := valid_of admitted
  have uses : naming.firing (s := σ.1) f.1 ⊆ σ.2 ∪ {n | n ∈ f.2} := admitted.2.1.2.2
  have after : ∀ o, o ∈ ((withLedger base (issuing k29)).result (s := σ) f admitted).1.present ↔
      (o ∈ σ.1.present ∧ o ∉ f.1.selection.taken) ∨ o ∈ f.1.selection.made :=
    fun o => present_after admitted
  rcases admitted.2.2 with ⟨x, hrule, hfresh⟩ | ⟨hrule, hfresh⟩ | ⟨n, hrule, hfresh⟩ | ⟨x, hrule, hfresh⟩
  · -- `r1 x`: keeps `T`, makes `A x`
    have reads := reads_match valid
    rw [hrule] at reads
    obtain ⟨oT, readT, isT⟩ := match_one reads
    have presentT : oT ∈ σ.1.present := read_present valid (by rw [readT]; simp)
    have noneIssued : σ.2 = ∅ := inv.whileT oT presentT isT.symm
    have closed : x.support = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro n member
      have written : n ∈ naming.firing (s := σ.1) f.1 := by
        apply mem_firingNames.mpr
        refine Or.inr (Or.inr (Or.inr ⟨factA x, ?_, ?_⟩))
        · rw [hrule]
          simp [r1, rule]
        · simp [factA, member]
      have issuedName := uses written
      rw [noneIssued, hfresh] at issuedName
      simp at issuedName
    have made : ∀ o ∈ f.1.selection.made, o.1 = factA x := by
      intro o member
      have produced := made_label valid member
      rw [hrule] at produced
      simpa [r1, rule] using produced
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro o present y labelled
      rcases (after o).mp present with ⟨old, _⟩ | new
      · exact inv.aClosed o old y labelled
      · rw [made o new] at labelled
        simp [factA] at labelled
        subst labelled
        exact closed
    · intro o present y labelled
      rcases (after o).mp present with ⟨old, _⟩ | new
      · exact inv.bNamed o old y labelled
      · rw [made o new] at labelled
        simp [factA, factB] at labelled
    · intro _ _ _
      change σ.2 ∪ {n | n ∈ f.2} = ∅
      rw [noneIssued, hfresh]
      simp
    · intro o present labelled
      rcases (after o).mp present with ⟨old, _⟩ | new
      · exact absurd isT.symm (inv.afterU o old labelled oT presentT)
      · rw [made o new] at labelled
        simp [factA, factU] at labelled
    · intro o present o' present' labelled labelled'
      rcases (after o).mp present with ⟨old, _⟩ | new
      · rcases (after o').mp present' with ⟨old', _⟩ | new'
        · exact inv.oneT o old o' old' labelled labelled'
        · rw [made o' new'] at labelled'
          simp [factA, factT] at labelled'
      · rw [made o new] at labelled
        simp [factA, factT] at labelled
    · intro o present labelled
      rcases (after o).mp present with ⟨old, _⟩ | new
      · exact inv.noW o old labelled
      · rw [made o new] at labelled
        simp [factA, factW] at labelled
  · -- `r0`: takes `T`, makes `U`
    have takes := takes_match valid
    rw [hrule] at takes
    obtain ⟨oT, takenT, isT⟩ := match_one takes
    have presentT : oT ∈ σ.1.present := taken_present valid (by rw [takenT]; simp)
    have made : ∀ o ∈ f.1.selection.made, o.1 = factU := by
      intro o member
      have produced := made_label valid member
      rw [hrule] at produced
      simpa [r0, rule] using produced
    have noT : ∀ o ∈ ((withLedger base (issuing k29)).result (s := σ) f admitted).1.present, o.1 ≠ factT := by
      intro o present labelled
      rcases (after o).mp present with ⟨old, notTaken⟩ | new
      · have same := inv.oneT o old oT presentT labelled isT.symm
        rw [takenT, same] at notTaken
        simp at notTaken
      · rw [made o new] at labelled
        simp [factU, factT] at labelled
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro o present y labelled
      rcases (after o).mp present with ⟨old, _⟩ | new
      · exact inv.aClosed o old y labelled
      · rw [made o new] at labelled
        simp [factU, factA] at labelled
    · intro o present y labelled
      rcases (after o).mp present with ⟨old, _⟩ | new
      · exact inv.bNamed o old y labelled
      · rw [made o new] at labelled
        simp [factU, factB] at labelled
    · intro o present labelled
      exact absurd labelled (noT o present)
    · intro _ _ _ o' present'
      exact noT o' present'
    · intro o present _ _ labelled _
      exact absurd labelled (noT o present)
    · intro o present labelled
      rcases (after o).mp present with ⟨old, _⟩ | new
      · exact inv.noW o old labelled
      · rw [made o new] at labelled
        simp [factU, factW] at labelled
  · -- `r2 n`: keeps `U`, issues `n`, makes `B n`
    have reads := reads_match valid
    rw [hrule] at reads
    obtain ⟨oU, readU, isU⟩ := match_one reads
    have presentU : oU ∈ σ.1.present := read_present valid (by rw [readU]; simp)
    have noTold : ∀ o' ∈ σ.1.present, o'.1 ≠ factT := inv.afterU oU presentU isU.symm
    have made : ∀ o ∈ f.1.selection.made, o.1 = factB (.name n) := by
      intro o member
      have produced := made_label valid member
      rw [hrule] at produced
      simpa [r2, rule] using produced
    have noT : ∀ o ∈ ((withLedger base (issuing k29)).result (s := σ) f admitted).1.present, o.1 ≠ factT := by
      intro o present labelled
      rcases (after o).mp present with ⟨old, _⟩ | new
      · exact noTold o old labelled
      · rw [made o new] at labelled
        simp [factB, factT] at labelled
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro o present y labelled
      rcases (after o).mp present with ⟨old, _⟩ | new
      · exact inv.aClosed o old y labelled
      · rw [made o new] at labelled
        simp [factB, factA] at labelled
    · intro o present y labelled
      rcases (after o).mp present with ⟨old, _⟩ | new
      · exact inv.bNamed o old y labelled
      · rw [made o new] at labelled
        simp [factB] at labelled
        exact ⟨n, labelled.symm⟩
    · intro o present labelled
      exact absurd labelled (noT o present)
    · intro _ _ _ o' present'
      exact noT o' present'
    · intro o present _ _ labelled _
      exact absurd labelled (noT o present)
    · intro o present labelled
      rcases (after o).mp present with ⟨old, _⟩ | new
      · exact inv.noW o old labelled
      · rw [made o new] at labelled
        simp [factB, factW] at labelled
  · -- `r3 x` is never admitted: `A x` has a closed argument and `B x` a named one
    exfalso
    have reads := reads_match valid
    rw [hrule] at reads
    obtain ⟨oA, oB, readAB, isA, isB⟩ := match_two reads
    have readA : oA ∈ f.1.selection.read := by rw [readAB]; simp
    have readB : oB ∈ f.1.selection.read := by rw [readAB]; simp
    have closed := inv.aClosed oA (read_present valid readA) x isA.symm
    obtain ⟨m, rfl⟩ := inv.bNamed oB (read_present valid readB) _ isB.symm
    simp at closed

/-- The invariant holds at every state a run of the theory with issuing reaches. -/
theorem k29_last : ∀ {σ : Conf × Set ℕ} (r : (withLedger base (issuing k29)).Run σ),
    K29 σ → K29 r.last
  | _, .nil _, inv => inv
  | _, .cons f admitted rest, inv => k29_last rest (k29_result f admitted inv)

/-- **With issuing, no run of the theory makes `W`.** -/
theorem issuing_never_derives_W (r : (withLedger base (issuing k29)).Run start) :
    ∀ o ∈ r.last.1.present, o.1 ≠ factW :=
  (k29_last r k29_start).noW

#print axioms k29_result
#print axioms issuing_never_derives_W

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamesOnTheStep.IssuingControls
