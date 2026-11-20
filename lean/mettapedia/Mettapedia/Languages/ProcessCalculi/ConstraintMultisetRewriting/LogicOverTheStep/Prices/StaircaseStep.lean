import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Prices.UnrestrictedStep

/-!
# Adequacy fails on the unrestricted step with four atoms

`UnrestrictedStep.unrestricted_adequacy_fails` uses infinitely many atoms. Here four suffice, so the
failure is not an artefact of an infinite observation set: it comes from the shape of the unrestricted
step itself. On knowledge, the unrestricted step is the reflexive and transitive prefix order of lists
of equations (`UnrestrictedStep.succ_extends`, `UnrestrictedStep.succ_tell`), and that order holds a
**staircase**.

* A **stair** (`stair r n i`) is a base (`[a = a]`, `[b = b]` or `[b = b, w = w]`), a height `n = n`, and
  `i ≤ n` steps `z = z`; it has `n - i` steps left (`OnStair`). Its extensions that stay drawn are
  further steps (`stair_extension`); every other extension is junk, and junk stays junk
  (`shaped_of_append'`).
* `stairView` observes four colours: `odd` and `even`, the parity of the steps left (and `odd` at the
  witness `[b = b, w = w]`), `root` at `[a = a]` and `[b = b]`, and `junk`.
* On a stair, truth depends only on the steps left (`stair_sat`). Every formula is eventually periodic
  in the steps left, with period two, and from some height on agrees at odd heights with the witness
  (`period`): the witness sees stairs of every height, and nothing a high stair cannot imitate within
  the formula's depth.
* So `[a = a]` and `[b = b]` satisfy the same formulas (`staircase_logicallyEquivalent`), while only
  `[b = b]` reaches the witness, which alternates colours without bound (`alt_wit`) where a stair is
  bounded by its height (`alt_upper`): they are not bisimilar (`staircase_not_bisimilar`,
  `staircase_adequacy_fails`).
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Prices.StaircaseStep

open Mettapedia.GSLT Mettapedia.GSLT.HennessyMilner
open StepSpan ProgramAdequacy
open NamesOnTheStep NamesOnTheStep.IssuingControls
open UnrestrictedStep (SelfEquated selfEquated_append succ_extends succ_tell succ_self
  sameKnowledge_isBisimulation selfEq rootA rootB wit witKnowledge)

/-! ## Stairs -/

/-- A step. -/
def zee : Expr := .sym 3
/-- A constant that no drawn knowledge ends with. -/
def jay : Expr := .sym 7

/-- The three bases of the stairs. -/
inductive Base
  | a
  | b
  | bw
  deriving DecidableEq

def Base.pre : Base → EquationStore Expr
  | .a => [selfEq rootA]
  | .b => [selfEq rootB]
  | .bw => witKnowledge

/-- **A stair**: a base, the height `n`, and `i` steps. -/
def stair (r : Base) (n i : ℕ) : EquationStore Expr :=
  r.pre ++ selfEq (.name n) :: List.replicate i (selfEq zee)

/-- On a stair with `m` steps left. -/
def OnStair (E : EquationStore Expr) (m : ℕ) : Prop :=
  ∃ (r : Base) (n i : ℕ), i ≤ n ∧ m = n - i ∧ E = stair r n i

/-- The drawn knowledge. -/
def Shaped (E : EquationStore Expr) : Prop :=
  E = [] ∨ E = [selfEq rootA] ∨ E = [selfEq rootB] ∨ E = witKnowledge ∨ ∃ m, OnStair E m

theorem selfEquated_one (x : Expr) : SelfEquated [selfEq x] := by
  intro e member
  rw [List.mem_singleton.mp member]
  rfl

theorem selfEquated_pre (r : Base) : SelfEquated r.pre := by
  cases r
  · exact UnrestrictedStep.selfEquated_single _
  · exact UnrestrictedStep.selfEquated_single _
  · exact UnrestrictedStep.selfEquated_pair _ _

theorem selfEquated_stair (r : Base) (n i : ℕ) : SelfEquated (stair r n i) := by
  refine selfEquated_append.mpr ⟨selfEquated_pre r, fun e member => ?_⟩
  rcases List.mem_cons.mp member with rfl | inside
  · rfl
  · rw [List.eq_of_mem_replicate inside]
    rfl

theorem stair_zero (r : Base) (n : ℕ) : stair r n 0 = r.pre ++ [selfEq (.name n)] := rfl

theorem stair_succ (r : Base) (n i : ℕ) : stair r n (i + 1) = stair r n i ++ [selfEq zee] := by
  simp [stair, List.replicate_succ']

theorem stair_zees (r : Base) (n i j : ℕ) :
    stair r n i ++ List.replicate j (selfEq zee) = stair r n (i + j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [List.replicate_succ', ← List.append_assoc, ih]
    show stair r n (i + j) ++ [selfEq zee] = stair r n ((i + j) + 1)
    rw [stair_succ]

theorem length_stair (r : Base) (n i : ℕ) : (stair r n i).length = r.pre.length + (i + 1) := by
  simp [stair]

theorem one_le_length_pre (r : Base) : 1 ≤ r.pre.length := by
  cases r <;> decide

/-- The base of a list of equations, read from its first two entries. -/
def baseOf : EquationStore Expr → Base
  | x :: y :: _ => if x = selfEq rootA then .a else if y = selfEq wit then .bw else .b
  | _ => .a

theorem baseOf_stair (r : Base) (n i : ℕ) : baseOf (stair r n i) = r := by
  cases r <;> rfl

/-- The index of a name, or zero. -/
def nameIndex : Option (Expr × Expr) → ℕ
  | some (.name k, _) => k
  | _ => 0

/-- The height of a stair on the base `r`. -/
def heightOf (r : Base) (E : EquationStore Expr) : ℕ := nameIndex E[r.pre.length]?

theorem heightOf_stair (r : Base) (n i : ℕ) : heightOf r (stair r n i) = n := by
  cases r <;> rfl

theorem stair_eq {r r' : Base} {n n' i i' : ℕ} (h : stair r n i = stair r' n' i') :
    r = r' ∧ n = n' ∧ i = i' := by
  have sameBase : r = r' := by
    have read := congrArg baseOf h
    rwa [baseOf_stair, baseOf_stair] at read
  subst sameBase
  have sameHeight : n = n' := by
    have read := congrArg (heightOf r) h
    rwa [heightOf_stair, heightOf_stair] at read
  have lengths := congrArg List.length h
  rw [length_stair, length_stair] at lengths
  exact ⟨rfl, sameHeight, by omega⟩

theorem stair_ne_single (r : Base) (n i : ℕ) (y : Expr × Expr) : stair r n i ≠ [y] := by
  intro h
  have lengths := congrArg List.length h
  rw [length_stair, List.length_singleton] at lengths
  have := one_le_length_pre r
  omega

theorem stair_ne_nil (r : Base) (n i : ℕ) : stair r n i ≠ [] := by
  intro h
  have lengths := congrArg List.length h
  rw [length_stair] at lengths
  simp at lengths

theorem stair_ne_wit (r : Base) (n i : ℕ) : stair r n i ≠ witKnowledge := by
  intro h
  cases r <;> simp [stair, Base.pre, witKnowledge, selfEq, rootA, rootB, wit] at h

theorem onStair_unique {E : EquationStore Expr} {m m' : ℕ} (h : OnStair E m) (h' : OnStair E m') :
    m = m' := by
  obtain ⟨r, n, i, _, rfl, rfl⟩ := h
  obtain ⟨r', n', i', _, rfl, same⟩ := h'
  obtain ⟨_, rfl, rfl⟩ := stair_eq same
  rfl

/-! ## Drawn knowledge is closed under prefixes -/

theorem witKnowledge_split : witKnowledge = [selfEq rootB] ++ [selfEq wit] := rfl

theorem shaped_of_append_single {E : EquationStore Expr} {x : Expr × Expr} (h : Shaped (E ++ [x])) :
    Shaped E := by
  rcases h with h | h | h | h | ⟨m, r, n, i, le, -, h⟩
  · simp at h
  · have empty : E = [] := by simpa using congrArg List.length h
    exact Or.inl empty
  · have empty : E = [] := by simpa using congrArg List.length h
    exact Or.inl empty
  · have split := List.append_inj' (h.trans witKnowledge_split) rfl
    exact Or.inr (Or.inr (Or.inl split.1))
  · cases i with
    | zero =>
      have split := List.append_inj' (h.trans (stair_zero r n)) rfl
      rw [split.1]
      cases r
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    | succ k =>
      have split := List.append_inj' (h.trans (stair_succ r n k)) rfl
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨n - k, r, n, k, by omega, rfl, split.1⟩)))

/-- **Drawn knowledge is closed under prefixes**, so junk is closed under extension. -/
theorem shaped_of_append' : ∀ (L : EquationStore Expr) {E : EquationStore Expr},
    Shaped (E ++ L) → Shaped E
  | [], _, h => by simpa using h
  | x :: L, E, h => shaped_of_append_single (shaped_of_append' L (by simpa using h))

/-- Knowledge ending with `jay` is junk. -/
theorem not_shaped_jay (E : EquationStore Expr) : ¬ Shaped (E ++ [selfEq jay]) := by
  rintro (h | h | h | h | ⟨m, r, n, i, -, -, h⟩)
  · simp at h
  · have split := (List.append_inj' (h.trans (List.nil_append [selfEq rootA]).symm) rfl).2
    simp [selfEq, jay, rootA] at split
  · have split := (List.append_inj' (h.trans (List.nil_append [selfEq rootB]).symm) rfl).2
    simp [selfEq, jay, rootB] at split
  · have split := (List.append_inj' (h.trans witKnowledge_split) rfl).2
    simp [selfEq, jay, wit] at split
  · cases i with
    | zero =>
      have split := (List.append_inj' (h.trans (stair_zero r n)) rfl).2
      simp [selfEq, jay] at split
    | succ k =>
      have split := (List.append_inj' (h.trans (stair_succ r n k)) rfl).2
      simp [selfEq, jay, zee] at split

/-! ## Which extensions stay drawn -/

theorem stair_extension_single {r : Base} {n i : ℕ} {x : Expr × Expr}
    (h : Shaped (stair r n i ++ [x])) : x = selfEq zee ∧ i + 1 ≤ n := by
  rcases h with h | h | h | h | ⟨m, r', n', i', le', -, h⟩
  · simp at h
  · have lengths := congrArg List.length h
    simp only [List.length_append, length_stair, List.length_singleton] at lengths
    omega
  · have lengths := congrArg List.length h
    simp only [List.length_append, length_stair, List.length_singleton] at lengths
    omega
  · have lengths := congrArg List.length h
    simp only [List.length_append, length_stair, List.length_singleton] at lengths
    have := one_le_length_pre r
    have witLength : witKnowledge.length = 2 := rfl
    omega
  · cases i' with
    | zero =>
      have split := List.append_inj' (h.trans (stair_zero r' n')) rfl
      cases r'
      · exact absurd split.1 (stair_ne_single r n i _)
      · exact absurd split.1 (stair_ne_single r n i _)
      · exact absurd split.1 (stair_ne_wit r n i)
    | succ k =>
      have split := List.append_inj' (h.trans (stair_succ r' n' k)) rfl
      obtain ⟨rfl, rfl, rfl⟩ := stair_eq split.1
      exact ⟨List.singleton_inj.mp split.2, le'⟩

/-- **A stair extends, staying drawn, only by further steps.** -/
theorem stair_extension : ∀ (L : EquationStore Expr) {r : Base} {n i : ℕ},
    Shaped (stair r n i ++ L) → ∃ j, L = List.replicate j (selfEq zee) ∧ i + j ≤ n
  | [], r, n, i, h => by
      rw [List.append_nil] at h
      rcases h with h | h | h | h | ⟨m, r', n', i', le', -, same⟩
      · exact absurd h (stair_ne_nil r n i)
      · exact absurd h (stair_ne_single r n i _)
      · exact absurd h (stair_ne_single r n i _)
      · exact absurd h (stair_ne_wit r n i)
      · obtain ⟨_, rfl, rfl⟩ := stair_eq same
        exact ⟨0, rfl, by omega⟩
  | x :: L, r, n, i, h => by
      have first : Shaped (stair r n i ++ [x]) := shaped_of_append' L (by simpa using h)
      obtain ⟨rfl, lt⟩ := stair_extension_single first
      have rest : Shaped (stair r n (i + 1) ++ L) := by
        rw [stair_succ]
        simpa using h
      obtain ⟨j, rfl, bound⟩ := stair_extension L rest
      exact ⟨j + 1, by simp [List.replicate_succ], by omega⟩

theorem base_extension_single (r : Base) {x : Expr × Expr} (h : Shaped (r.pre ++ [x])) :
    (∃ n, x = selfEq (.name n)) ∨ (r = .b ∧ x = selfEq wit) := by
  rcases h with h | h | h | h | ⟨m, r', n', i', -, -, h⟩
  · simp at h
  · have lengths := congrArg List.length h
    rw [List.length_append, List.length_singleton, List.length_singleton] at lengths
    have := one_le_length_pre r
    omega
  · have lengths := congrArg List.length h
    rw [List.length_append, List.length_singleton, List.length_singleton] at lengths
    have := one_le_length_pre r
    omega
  · cases r
    · simp [Base.pre, witKnowledge, selfEq, rootA, rootB] at h
    · right
      refine ⟨rfl, ?_⟩
      have split := (List.append_inj' (h.trans witKnowledge_split) rfl).2
      exact List.singleton_inj.mp split
    · have lengths := congrArg List.length h
      simp [Base.pre, witKnowledge] at lengths
  · cases i' with
    | zero =>
      have split := List.append_inj' (h.trans (stair_zero r' n')) rfl
      exact Or.inl ⟨n', List.singleton_inj.mp split.2⟩
    | succ k =>
      have split := List.append_inj' (h.trans (stair_succ r' n' k)) rfl
      cases r
      · exact absurd split.1.symm (stair_ne_single r' n' k _)
      · exact absurd split.1.symm (stair_ne_single r' n' k _)
      · exact absurd split.1.symm (stair_ne_wit r' n' k)

/-- **The extensions of a base**: itself, the witness (from `[b = b]` only), a stair on it, or junk. -/
theorem base_extension (r : Base) (L : EquationStore Expr) (h : Shaped (r.pre ++ L)) :
    L = [] ∨ (r = .b ∧ ∃ L', L = selfEq wit :: L' ∧ Shaped (witKnowledge ++ L')) ∨
      ∃ n i, i ≤ n ∧ r.pre ++ L = stair r n i := by
  cases L with
  | nil => exact Or.inl rfl
  | cons x L' =>
    have first : Shaped (r.pre ++ [x]) := shaped_of_append' L' (by simpa using h)
    rcases base_extension_single r first with ⟨n, rfl⟩ | ⟨rfl, rfl⟩
    · have onStair : Shaped (stair r n 0 ++ L') := by
        rw [stair_zero]
        simpa using h
      obtain ⟨j, rfl, bound⟩ := stair_extension L' onStair
      exact Or.inr (Or.inr ⟨n, j, by omega, rfl⟩)
    · refine Or.inr (Or.inl ⟨rfl, L', rfl, ?_⟩)
      simpa [Base.pre, witKnowledge] using h

theorem wit_extension (L : EquationStore Expr) (h : Shaped (witKnowledge ++ L)) :
    L = [] ∨ ∃ n i, i ≤ n ∧ witKnowledge ++ L = stair .bw n i := by
  rcases base_extension .bw L h with empty | ⟨impossible, _⟩ | found
  · exact Or.inl empty
  · exact Base.noConfusion impossible
  · exact Or.inr found

/-! ## The observation set -/

/-- The four colours. -/
inductive Color
  | odd
  | even
  | root
  | junk
  deriving DecidableEq

/-- **The staircase observation set**: four atoms, reading only the knowledge. -/
def stairView : Color → Conf → Prop
  | .root, C => C.equations = [selfEq rootA] ∨ C.equations = [selfEq rootB]
  | .odd, C => C.equations = witKnowledge ∨ ∃ m, OnStair C.equations m ∧ m % 2 = 1
  | .even, C => ∃ m, OnStair C.equations m ∧ m % 2 = 0
  | .junk, C => ¬ Shaped C.equations

theorem stairView_invariant (a : Color) (π : Equiv.Perm Occ) (C : Conf) (_ : Keeps Prod.fst π) :
    stairView a (renameConf π C) ↔ stairView a C := by
  cases a <;> exact Iff.rfl

/-- The colour of the stairs with `m` steps left. -/
def colorOf (m : ℕ) : Color → Prop
  | .odd => m % 2 = 1
  | .even => m % 2 = 0
  | .root => False
  | .junk => False

theorem stairView_onStair {C : Conf} {m : ℕ} (h : OnStair C.equations m) (a : Color) :
    stairView a C ↔ colorOf m a := by
  obtain ⟨r, n, i, le, hm, hE⟩ := h
  have here : OnStair C.equations m := ⟨r, n, i, le, hm, hE⟩
  cases a with
  | odd =>
    show (C.equations = witKnowledge ∨ ∃ m', OnStair C.equations m' ∧ m' % 2 = 1) ↔ m % 2 = 1
    constructor
    · rintro (isWit | ⟨m', on', odd⟩)
      · exact absurd (hE.symm.trans isWit) (stair_ne_wit r n i)
      · rw [onStair_unique here on']
        exact odd
    · intro odd
      exact Or.inr ⟨m, here, odd⟩
  | even =>
    show (∃ m', OnStair C.equations m' ∧ m' % 2 = 0) ↔ m % 2 = 0
    constructor
    · rintro ⟨m', on', even⟩
      rw [onStair_unique here on']
      exact even
    · intro even
      exact ⟨m, here, even⟩
  | root =>
    show (C.equations = [selfEq rootA] ∨ C.equations = [selfEq rootB]) ↔ False
    refine iff_false_intro ?_
    rintro (h | h) <;> exact stair_ne_single r n i _ (hE.symm.trans h)
  | junk =>
    show ¬ Shaped C.equations ↔ False
    exact iff_false_intro fun notShaped => notShaped (Or.inr (Or.inr (Or.inr (Or.inr ⟨m, here⟩))))

theorem stairView_junk {C : Conf} (junk : ¬ Shaped C.equations) (a : Color) :
    stairView a C ↔ a = .junk := by
  cases a with
  | odd =>
    refine iff_of_false ?_ (fun h => Color.noConfusion h)
    rintro (h | ⟨m, h, _⟩)
    · exact junk (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact junk (Or.inr (Or.inr (Or.inr (Or.inr ⟨m, h⟩))))
  | even =>
    refine iff_of_false ?_ (fun h => Color.noConfusion h)
    rintro ⟨m, h, _⟩
    exact junk (Or.inr (Or.inr (Or.inr (Or.inr ⟨m, h⟩))))
  | root =>
    refine iff_of_false ?_ (fun h => Color.noConfusion h)
    rintro (h | h)
    · exact junk (Or.inr (Or.inl h))
    · exact junk (Or.inr (Or.inr (Or.inl h)))
  | junk => exact iff_of_true junk rfl

/-! ## Truth depends only on the knowledge, and on a stair only on the steps left -/

/-- Satisfaction on the unrestricted step with the staircase observations. -/
abbrev Sat (φ : Formula Color Unit) (C : Conf) : Prop := (stepSystem base stairView).sat φ C

/-- The store with knowledge `E` and nothing present. -/
def knowConf (E : EquationStore Expr) : Conf := ⟨E, ∅⟩

theorem sat_knowledge {C D : Conf} (same : C.equations = D.equations) (φ : Formula Color Unit) :
    Sat φ C ↔ Sat φ D :=
  (stepSystem base stairView).sat_iff_of_isBisimulation
    (sameKnowledge_isBisimulation stairView fun a C D same => by
      cases a <;> simp only [stairView, same])
    φ same

/-- Pairs on stairs with the same steps left, or both junk. -/
def StairRel (C D : Conf) : Prop :=
  SelfEquated C.equations ∧ SelfEquated D.equations ∧
    ((∃ m, OnStair C.equations m ∧ OnStair D.equations m) ∨ (¬ Shaped C.equations ∧ ¬ Shaped D.equations))

theorem selfEquated_jay {E : EquationStore Expr} (selfE : SelfEquated E) :
    SelfEquated (E ++ [selfEq jay]) :=
  selfEquated_append.mpr ⟨selfE, selfEquated_one jay⟩

theorem stairRel_forth {C D C' : Conf} (related : StairRel C D) (step : Succ base C C') :
    ∃ D', Succ base D D' ∧ StairRel C' D' := by
  obtain ⟨selfC, selfD, (⟨m, onC, onD⟩ | ⟨junkC, junkD⟩)⟩ := related
  · obtain ⟨L, extended, selfC'⟩ := succ_extends step
    by_cases shaped : Shaped C'.equations
    · obtain ⟨r, n, i, le, hm, hC⟩ := onC
      obtain ⟨r', n', i', le', hm', hD⟩ := onD
      have drawn : Shaped (stair r n i ++ L) := by
        rw [← hC, ← extended]
        exact shaped
      obtain ⟨j, rfl, bound⟩ := stair_extension L drawn
      have bound' : i' + j ≤ n' := by omega
      have selfD' : SelfEquated (D.equations ++ List.replicate j (selfEq zee)) := by
        rw [hD, stair_zees]
        exact selfEquated_stair r' n' (i' + j)
      refine ⟨⟨D.equations ++ List.replicate j (selfEq zee), D.present⟩, succ_tell selfD', selfC', selfD',
        Or.inl ⟨m - j, ⟨r, n, i + j, bound, by omega, ?_⟩, ⟨r', n', i' + j, bound', by omega, ?_⟩⟩⟩
      · rw [extended, hC, stair_zees]
      · show D.equations ++ List.replicate j (selfEq zee) = _
        rw [hD, stair_zees]
    · exact ⟨⟨D.equations ++ [selfEq jay], D.present⟩, succ_tell (selfEquated_jay selfD), selfC',
        selfEquated_jay selfD, Or.inr ⟨shaped, not_shaped_jay D.equations⟩⟩
  · obtain ⟨L, extended, selfC'⟩ := succ_extends step
    refine ⟨D, succ_self selfD, selfC', selfD, Or.inr ⟨fun shaped => junkC ?_, junkD⟩⟩
    rw [extended] at shaped
    exact shaped_of_append' L shaped

theorem stairRel_symm {C D : Conf} (related : StairRel C D) : StairRel D C := by
  obtain ⟨selfC, selfD, (⟨m, onC, onD⟩ | ⟨junkC, junkD⟩)⟩ := related
  · exact ⟨selfD, selfC, Or.inl ⟨m, onD, onC⟩⟩
  · exact ⟨selfD, selfC, Or.inr ⟨junkD, junkC⟩⟩

theorem stairRel_isBisimulation : (stepSystem base stairView).IsBisimulation StairRel := by
  refine ⟨?_, ?_, ?_⟩
  · intro C D related _ C' step
    exact stairRel_forth related step
  · intro C D related _ D' step
    obtain ⟨C', back, related'⟩ := stairRel_forth (stairRel_symm related) step
    exact ⟨C', back, stairRel_symm related'⟩
  · intro C D related a
    obtain ⟨_, _, (⟨m, onC, onD⟩ | ⟨junkC, junkD⟩)⟩ := related
    · exact (stairView_onStair onC a).trans (stairView_onStair onD a).symm
    · exact (stairView_junk junkC a).trans (stairView_junk junkD a).symm

/-- Truth on the stairs, by the steps left. -/
def T (φ : Formula Color Unit) (m : ℕ) : Prop := Sat φ (knowConf (stair .a m 0))
/-- Truth on junk. -/
def J (φ : Formula Color Unit) : Prop := Sat φ (knowConf [selfEq jay])
/-- Truth at the witness. -/
def Y (φ : Formula Color Unit) : Prop := Sat φ (knowConf witKnowledge)

theorem onStair_canonical (m : ℕ) : OnStair (knowConf (stair .a m 0)).equations m :=
  ⟨.a, m, 0, Nat.zero_le m, by omega, rfl⟩

theorem jay_junk : ¬ Shaped (knowConf [selfEq jay]).equations := not_shaped_jay []

/-- **On a stair, truth depends only on the steps left.** -/
theorem stair_sat {C : Conf} {m : ℕ} (on : OnStair C.equations m) (selfC : SelfEquated C.equations)
    (φ : Formula Color Unit) : Sat φ C ↔ T φ m :=
  (stepSystem base stairView).sat_iff_of_isBisimulation stairRel_isBisimulation φ
    ⟨selfC, selfEquated_stair .a m 0, Or.inl ⟨m, on, onStair_canonical m⟩⟩

/-- **On junk, truth is constant.** -/
theorem junk_sat {C : Conf} (junk : ¬ Shaped C.equations) (selfC : SelfEquated C.equations)
    (φ : Formula Color Unit) : Sat φ C ↔ J φ :=
  (stepSystem base stairView).sat_iff_of_isBisimulation stairRel_isBisimulation φ
    ⟨selfC, selfEquated_one jay, Or.inr ⟨junk, jay_junk⟩⟩

/-! ## The modality at the drawn knowledge -/

theorem tell_step {E L : EquationStore Expr} (selfE : SelfEquated (E ++ L)) :
    Succ base (knowConf E) (knowConf (E ++ L)) :=
  succ_tell (C := knowConf E) selfE

theorem dia_stair (ψ : Formula Color Unit) (m : ℕ) :
    T (.dia () ψ) m ↔ (∃ m', m' ≤ m ∧ T ψ m') ∨ J ψ := by
  constructor
  · rintro ⟨C', step, holds⟩
    obtain ⟨L, extended, selfC'⟩ := succ_extends step
    have extended' : C'.equations = stair .a m 0 ++ L := extended
    by_cases shaped : Shaped C'.equations
    · have drawn : Shaped (stair .a m 0 ++ L) := by
        rw [← extended']
        exact shaped
      obtain ⟨j, rfl, bound⟩ := stair_extension L drawn
      refine Or.inl ⟨m - j, by omega, (stair_sat ⟨.a, m, j, by omega, rfl, ?_⟩ selfC' ψ).mp holds⟩
      rw [extended', stair_zees, Nat.zero_add]
    · exact Or.inr ((junk_sat shaped selfC' ψ).mp holds)
  · rintro (⟨m', le, holds⟩ | holds)
    · have selfNext : SelfEquated (stair .a m 0 ++ List.replicate (m - m') (selfEq zee)) := by
        rw [stair_zees]
        exact selfEquated_stair .a m _
      have onNext : OnStair (knowConf (stair .a m 0 ++ List.replicate (m - m') (selfEq zee))).equations m' :=
        ⟨.a, m, m - m', by omega, by omega, by
          show stair .a m 0 ++ List.replicate (m - m') (selfEq zee) = stair .a m (m - m')
          rw [stair_zees, Nat.zero_add]⟩
      exact ⟨_, tell_step selfNext, (stair_sat onNext selfNext ψ).mpr holds⟩
    · have selfNext := selfEquated_jay (selfEquated_stair .a m 0)
      exact ⟨_, tell_step selfNext, (junk_sat (not_shaped_jay _) selfNext ψ).mpr holds⟩

theorem dia_wit (ψ : Formula Color Unit) :
    Y (.dia () ψ) ↔ Y ψ ∨ (∃ m, T ψ m) ∨ J ψ := by
  have selfWit : SelfEquated witKnowledge := UnrestrictedStep.selfEquated_pair _ _
  constructor
  · rintro ⟨C', step, holds⟩
    obtain ⟨L, extended, selfC'⟩ := succ_extends step
    have extended' : C'.equations = witKnowledge ++ L := extended
    by_cases shaped : Shaped C'.equations
    · have drawn : Shaped (witKnowledge ++ L) := by
        rw [← extended']
        exact shaped
      rcases wit_extension L drawn with rfl | ⟨n, i, le, onStairBw⟩
      · exact Or.inl ((sat_knowledge (D := knowConf witKnowledge)
          (extended'.trans (List.append_nil _)) ψ).mp holds)
      · exact Or.inr (Or.inl ⟨n - i,
          (stair_sat ⟨.bw, n, i, le, rfl, extended'.trans onStairBw⟩ selfC' ψ).mp holds⟩)
    · exact Or.inr (Or.inr ((junk_sat shaped selfC' ψ).mp holds))
  · rintro (holds | ⟨m, holds⟩ | holds)
    · exact ⟨knowConf witKnowledge, succ_self (C := knowConf witKnowledge) selfWit, holds⟩
    · have selfNext : SelfEquated (witKnowledge ++ [selfEq (.name m)]) :=
        selfEquated_append.mpr ⟨selfWit, selfEquated_one _⟩
      exact ⟨_, tell_step selfNext,
        (stair_sat ⟨.bw, m, 0, Nat.zero_le m, by omega, rfl⟩ selfNext ψ).mpr holds⟩
    · have selfNext := selfEquated_jay selfWit
      exact ⟨_, tell_step selfNext, (junk_sat (not_shaped_jay _) selfNext ψ).mpr holds⟩

theorem dia_root (r : Base) (single : r ≠ .bw) (ψ : Formula Color Unit) :
    Sat (.dia () ψ) (knowConf r.pre) ↔
      Sat ψ (knowConf r.pre) ∨ (r = .b ∧ Y ψ) ∨ (∃ m, T ψ m) ∨ J ψ := by
  have selfPre := selfEquated_pre r
  constructor
  · rintro ⟨C', step, holds⟩
    obtain ⟨L, extended, selfC'⟩ := succ_extends step
    have extended' : C'.equations = r.pre ++ L := extended
    by_cases shaped : Shaped C'.equations
    · have drawn : Shaped (r.pre ++ L) := by
        rw [← extended']
        exact shaped
      rcases base_extension r L drawn with rfl | ⟨isB, L', rfl, drawnWit⟩ | ⟨n, i, le, onStairR⟩
      · exact Or.inl ((sat_knowledge (D := knowConf r.pre) (extended'.trans (List.append_nil _)) ψ).mp holds)
      · subst isB
        have extended'' : C'.equations = witKnowledge ++ L' := extended'
        rcases wit_extension L' drawnWit with rfl | ⟨n, i, le, onStairBw⟩
        · exact Or.inr (Or.inl ⟨rfl, (sat_knowledge (D := knowConf witKnowledge)
            (extended''.trans (List.append_nil _)) ψ).mp holds⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨n - i,
            (stair_sat ⟨.bw, n, i, le, rfl, extended''.trans onStairBw⟩ selfC' ψ).mp holds⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨n - i,
          (stair_sat ⟨r, n, i, le, rfl, extended'.trans onStairR⟩ selfC' ψ).mp holds⟩))
    · exact Or.inr (Or.inr (Or.inr ((junk_sat shaped selfC' ψ).mp holds)))
  · rintro (holds | ⟨rfl, holds⟩ | ⟨m, holds⟩ | holds)
    · exact ⟨knowConf r.pre, succ_self (C := knowConf r.pre) selfPre, holds⟩
    · have selfNext : SelfEquated (Base.pre .b ++ [selfEq wit]) := UnrestrictedStep.selfEquated_pair _ _
      exact ⟨_, tell_step selfNext, (sat_knowledge (D := knowConf witKnowledge) rfl ψ).mpr holds⟩
    · have selfNext : SelfEquated (r.pre ++ [selfEq (.name m)]) :=
        selfEquated_append.mpr ⟨selfPre, selfEquated_one _⟩
      exact ⟨_, tell_step selfNext, (stair_sat ⟨r, m, 0, Nat.zero_le m, by omega, rfl⟩ selfNext ψ).mpr holds⟩
    · have selfNext := selfEquated_jay selfPre
      exact ⟨_, tell_step selfNext, (junk_sat (not_shaped_jay _) selfNext ψ).mpr holds⟩

/-! ## Atoms at the drawn knowledge -/

theorem atom_stair (a : Color) (m : ℕ) : T (.atom a) m ↔ colorOf m a :=
  stairView_onStair (onStair_canonical m) a

theorem atom_junk (a : Color) : J (.atom a) ↔ a = .junk := stairView_junk jay_junk a

theorem atom_wit (a : Color) : Y (.atom a) ↔ a = .odd := by
  cases a with
  | odd => exact iff_of_true (Or.inl rfl) rfl
  | even =>
    refine iff_of_false ?_ (fun h => Color.noConfusion h)
    rintro ⟨m, ⟨r, n, i, _, _, h⟩, _⟩
    exact stair_ne_wit r n i h.symm
  | root =>
    refine iff_of_false ?_ (fun h => Color.noConfusion h)
    rintro (h | h) <;> simp [knowConf, witKnowledge] at h
  | junk =>
    refine iff_of_false ?_ (fun h => Color.noConfusion h)
    exact fun notShaped => notShaped (Or.inr (Or.inr (Or.inr (Or.inl rfl))))

theorem atom_root (r : Base) (single : r ≠ .bw) (a : Color) :
    Sat (.atom a) (knowConf r.pre) ↔ a = .root := by
  cases a with
  | root =>
    refine iff_of_true ?_ rfl
    cases r
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd rfl single
  | odd =>
    refine iff_of_false ?_ (fun h => Color.noConfusion h)
    rintro (h | ⟨m, ⟨r', n, i, _, _, h⟩, _⟩)
    · cases r
      · simp [knowConf, Base.pre, witKnowledge, selfEq, rootA, rootB] at h
      · simp [knowConf, Base.pre, witKnowledge] at h
      · exact single rfl
    · cases r
      · exact stair_ne_single r' n i _ h.symm
      · exact stair_ne_single r' n i _ h.symm
      · exact single rfl
  | even =>
    refine iff_of_false ?_ (fun h => Color.noConfusion h)
    rintro ⟨m, ⟨r', n, i, _, _, h⟩, _⟩
    cases r
    · exact stair_ne_single r' n i _ h.symm
    · exact stair_ne_single r' n i _ h.symm
    · exact single rfl
  | junk =>
    refine iff_of_false ?_ (fun h => Color.noConfusion h)
    intro notShaped
    cases r
    · exact notShaped (Or.inr (Or.inl rfl))
    · exact notShaped (Or.inr (Or.inr (Or.inl rfl)))
    · exact single rfl

/-! ## Every formula is eventually periodic on the stairs, and imitates the witness -/

theorem same_parity {φ : Formula Color Unit} {N : ℕ}
    (periodic : ∀ m, N ≤ m → (T φ m ↔ T φ (m + 2))) :
    ∀ a b, N ≤ a → N ≤ b → a % 2 = b % 2 → (T φ a ↔ T φ b) := by
  have up : ∀ a k, N ≤ a → (T φ a ↔ T φ (a + 2 * k)) := by
    intro a k low
    induction k with
    | zero => exact Iff.rfl
    | succ k ih =>
      refine ih.trans ?_
      rw [show a + 2 * (k + 1) = (a + 2 * k) + 2 by omega]
      exact periodic _ (by omega)
  intro a b ha hb parity
  rcases Nat.le_total a b with le | le
  · obtain ⟨k, rfl⟩ : ∃ k, b = a + 2 * k := ⟨(b - a) / 2, by omega⟩
    exact up a k ha
  · obtain ⟨k, rfl⟩ : ∃ k, a = b + 2 * k := ⟨(a - b) / 2, by omega⟩
    exact (up b k hb).symm

/-- **Eventual periodicity, and imitation of the witness at odd heights.** -/
theorem period (φ : Formula Color Unit) :
    ∃ N, ∀ m, N ≤ m → (T φ m ↔ T φ (m + 2)) ∧ (m % 2 = 1 → (Y φ ↔ T φ m)) := by
  induction φ with
  | top => exact ⟨0, fun _ _ => ⟨Iff.rfl, fun _ => Iff.rfl⟩⟩
  | atom a =>
    refine ⟨0, fun m _ => ⟨?_, fun odd => ?_⟩⟩
    · rw [atom_stair, atom_stair]
      cases a <;> simp only [colorOf] <;> omega
    · rw [atom_wit, atom_stair]
      cases a <;> simp [colorOf, odd]
  | conj φ ψ ihφ ihψ =>
    obtain ⟨N₁, h₁⟩ := ihφ
    obtain ⟨N₂, h₂⟩ := ihψ
    refine ⟨max N₁ N₂, fun m bound => ⟨?_, fun odd => ?_⟩⟩
    · exact and_congr (h₁ m (le_of_max_le_left bound)).1 (h₂ m (le_of_max_le_right bound)).1
    · exact and_congr ((h₁ m (le_of_max_le_left bound)).2 odd) ((h₂ m (le_of_max_le_right bound)).2 odd)
  | neg φ ih =>
    obtain ⟨N, h⟩ := ih
    exact ⟨N, fun m bound => ⟨not_congr (h m bound).1, fun odd => not_congr ((h m bound).2 odd)⟩⟩
  | dia l φ ih =>
    cases l
    obtain ⟨N, h⟩ := ih
    have parity := same_parity (fun m bound => (h m bound).1)
    refine ⟨N + 2, fun m bound => ⟨?_, fun odd => ?_⟩⟩
    · rw [dia_stair, dia_stair]
      constructor
      · rintro (⟨m', le, holds⟩ | holds)
        · exact Or.inl ⟨m', by omega, holds⟩
        · exact Or.inr holds
      · rintro (⟨m', le, holds⟩ | holds)
        · rcases Nat.lt_or_ge m m' with lt | ge
          · exact Or.inl ⟨m' - 2, by omega,
              (parity (m' - 2) m' (by omega) (by omega) (by omega)).mpr holds⟩
          · exact Or.inl ⟨m', ge, holds⟩
        · exact Or.inr holds
    · rw [dia_wit, dia_stair]
      constructor
      · rintro (holds | ⟨m', holds⟩ | holds)
        · exact Or.inl ⟨m, le_refl m, ((h m (by omega)).2 odd).mp holds⟩
        · rcases Nat.lt_or_ge m m' with lt | ge
          · have target : ∃ m'', m'' ≤ m ∧ N ≤ m'' ∧ m'' % 2 = m' % 2 := by
              rcases Nat.mod_two_eq_zero_or_one m' with even | odd'
              · exact ⟨m - 1, by omega, by omega, by omega⟩
              · exact ⟨m, le_refl m, by omega, by omega⟩
            obtain ⟨m'', le, low, sameParity⟩ := target
            exact Or.inl ⟨m'', le, (parity m'' m' low (by omega) sameParity).mpr holds⟩
          · exact Or.inl ⟨m', ge, holds⟩
        · exact Or.inr holds
      · rintro (⟨m', _, holds⟩ | holds)
        · exact Or.inr (Or.inl ⟨m', holds⟩)
        · exact Or.inr (Or.inr holds)

/-! ## The roots -/

theorem roots_agree (φ : Formula Color Unit) :
    Sat φ (knowConf (Base.pre .a)) ↔ Sat φ (knowConf (Base.pre .b)) := by
  induction φ with
  | top => exact Iff.rfl
  | atom a =>
    exact (atom_root .a (fun h => Base.noConfusion h) a).trans
      (atom_root .b (fun h => Base.noConfusion h) a).symm
  | conj φ ψ ihφ ihψ => exact and_congr ihφ ihψ
  | neg φ ih => exact not_congr ih
  | dia l φ ih =>
    cases l
    refine (dia_root .a (fun h => Base.noConfusion h) φ).trans
      (Iff.trans ?_ (dia_root .b (fun h => Base.noConfusion h) φ).symm)
    obtain ⟨N, h⟩ := period φ
    constructor
    · rintro (holds | ⟨impossible, _⟩ | holds | holds)
      · exact Or.inl (ih.mp holds)
      · exact Base.noConfusion impossible
      · exact Or.inr (Or.inr (Or.inl holds))
      · exact Or.inr (Or.inr (Or.inr holds))
    · rintro (holds | ⟨_, holdsY⟩ | holds | holds)
      · exact Or.inl (ih.mpr holds)
      · exact Or.inr (Or.inr (Or.inl ⟨2 * N + 1, ((h (2 * N + 1) (by omega)).2 (by omega)).mp holdsY⟩))
      · exact Or.inr (Or.inr (Or.inl holds))
      · exact Or.inr (Or.inr (Or.inr holds))

/-- **The two roots satisfy the same formulas**, with four atoms. -/
theorem staircase_logicallyEquivalent :
    (stepSystem base stairView).LogicallyEquivalent (knowConf [selfEq rootA]) (knowConf [selfEq rootB]) :=
  roots_agree

/-! ## Alternation separates the witness from every stair -/

/-- The colour atom of a parity. -/
def colorAtom : Bool → Color
  | true => .odd
  | false => .even

/-- The parity a colour atom reads. -/
def Fits : Bool → ℕ → Prop
  | true, m => m % 2 = 1
  | false, m => m % 2 = 0

theorem fits_not {b : Bool} {m : ℕ} (fits : Fits b m) : ¬ Fits (!b) m := by
  cases b
  · show ¬ (m % 2 = 1)
    have even : m % 2 = 0 := fits
    omega
  · show ¬ (m % 2 = 0)
    have odd : m % 2 = 1 := fits
    omega

/-- `k` alternations of colour, starting with the colour `b`. -/
def alt : ℕ → Bool → Formula Color Unit
  | 0, _ => .top
  | k + 1, b => .dia () (.conj (.atom (colorAtom b)) (alt k (!b)))

theorem colorAtom_stair (b : Bool) (m : ℕ) : T (.atom (colorAtom b)) m ↔ Fits b m := by
  cases b
  · exact atom_stair .even m
  · exact atom_stair .odd m

theorem colorAtom_not_junk (b : Bool) : ¬ J (.atom (colorAtom b)) := by
  rw [atom_junk]
  cases b <;> exact fun h => Color.noConfusion h

/-- **A stair with `m` steps left alternates at most `m + 1` times.** -/
theorem alt_upper : ∀ (k m : ℕ) (b : Bool), T (alt (k + 1) b) m →
    k ≤ m ∧ (¬ Fits b m → k + 1 ≤ m)
  | k, m, b, holds => by
      rcases (dia_stair _ m).mp holds with ⟨m', le, colour, rest⟩ | ⟨colour, _⟩
      · have fitsHere : Fits b m' := (colorAtom_stair b m').mp colour
        cases k with
        | zero =>
          refine ⟨Nat.zero_le m, fun notFit => ?_⟩
          have ne : m' ≠ m := fun same => notFit (same ▸ fitsHere)
          omega
        | succ k =>
          obtain ⟨_, step⟩ := alt_upper k m' (!b) rest
          have high := step (fits_not fitsHere)
          refine ⟨by omega, fun notFit => ?_⟩
          have ne : m' ≠ m := fun same => notFit (same ▸ fitsHere)
          omega
      · exact absurd colour (colorAtom_not_junk b)

/-- **A stair with at least `k` steps left alternates `k` times.** -/
theorem alt_lower : ∀ (k m : ℕ) (b : Bool), k ≤ m → T (alt k b) m
  | 0, _, _, _ => trivial
  | k + 1, m, b, le => by
      have choice : ∃ m', m' ≤ m ∧ k ≤ m' ∧ Fits b m' := by
        cases b
        · rcases Nat.mod_two_eq_zero_or_one m with even | odd
          · exact ⟨m, le_refl m, by omega, even⟩
          · exact ⟨m - 1, by omega, by omega, show (m - 1) % 2 = 0 by omega⟩
        · rcases Nat.mod_two_eq_zero_or_one m with even | odd
          · exact ⟨m - 1, by omega, by omega, show (m - 1) % 2 = 1 by omega⟩
          · exact ⟨m, le_refl m, by omega, odd⟩
      obtain ⟨m', le', low, fitsThere⟩ := choice
      exact (dia_stair _ m).mpr (Or.inl ⟨m', le', (colorAtom_stair b m').mpr fitsThere,
        alt_lower k m' (!b) low⟩)

/-- **The witness alternates without bound.** -/
theorem alt_wit : ∀ k, Y (alt k true)
  | 0 => trivial
  | k + 1 => (dia_wit _).mpr (Or.inr (Or.inl ⟨2 * k + 1,
      (colorAtom_stair true _).mpr (show (2 * k + 1) % 2 = 1 by omega),
      alt_lower k (2 * k + 1) false (by omega)⟩))

/-- **The two roots are not bisimilar.** -/
theorem staircase_not_bisimilar :
    ¬ (stepSystem base stairView).Bisimilar (knowConf [selfEq rootA]) (knowConf [selfEq rootB]) := by
  rintro ⟨R, bisimulation, related⟩
  have reach : Succ base (knowConf [selfEq rootB]) (knowConf witKnowledge) :=
    tell_step (E := [selfEq rootB]) (L := [selfEq wit]) (UnrestrictedStep.selfEquated_pair _ _)
  obtain ⟨C', step, relatedWit⟩ := bisimulation.2.1 related () reach
  have agree := fun φ : Formula Color Unit =>
    (stepSystem base stairView).sat_iff_of_isBisimulation bisimulation φ relatedWit
  obtain ⟨L, extended, selfC'⟩ := succ_extends step
  have extended' : C'.equations = Base.pre .a ++ L := extended
  by_cases shaped : Shaped C'.equations
  · have drawn : Shaped (Base.pre .a ++ L) := by
      rw [← extended']
      exact shaped
    rcases base_extension .a L drawn with rfl | ⟨impossible, _⟩ | ⟨n, i, le, onStairA⟩
    · have rootC' : Sat (.atom .root) C' :=
        (sat_knowledge (D := knowConf (Base.pre .a)) (extended'.trans (List.append_nil _)) _).mpr
          ((atom_root .a (fun h => Base.noConfusion h) .root).mpr rfl)
      exact Color.noConfusion ((atom_wit .root).mp ((agree _).mp rootC'))
    · exact Base.noConfusion impossible
    · have onC' : OnStair C'.equations (n - i) := ⟨.a, n, i, le, rfl, extended'.trans onStairA⟩
      have atWit := (agree (alt (n - i + 2) true)).mpr (alt_wit (n - i + 2))
      have atStair := (stair_sat onC' selfC' _).mp atWit
      obtain ⟨low, _⟩ := alt_upper (n - i + 1) (n - i) true atStair
      omega
  · have junkC' : Sat (.atom .junk) C' := (stairView_junk shaped .junk).mpr rfl
    exact Color.noConfusion ((atom_wit .junk).mp ((agree _).mp junkC'))

/-- **Without a finite program, finitary adequacy fails with four atoms**, invariant under renaming. -/
theorem staircase_adequacy_fails :
    ∃ observes : Color → Conf → Prop,
      (∀ (a : Color) (π : Equiv.Perm Occ) (C : Conf), Keeps Prod.fst π →
        (observes a (renameConf π C) ↔ observes a C)) ∧
      ∃ C D : Conf, (stepSystem base observes).LogicallyEquivalent C D ∧
        ¬ (stepSystem base observes).Bisimilar C D :=
  ⟨stairView, stairView_invariant, _, _, staircase_logicallyEquivalent, staircase_not_bisimilar⟩

#print axioms stair_eq
#print axioms shaped_of_append'
#print axioms stair_extension
#print axioms stair_sat
#print axioms dia_stair
#print axioms dia_wit
#print axioms dia_root
#print axioms period
#print axioms roots_agree
#print axioms staircase_logicallyEquivalent
#print axioms alt_upper
#print axioms alt_lower
#print axioms alt_wit
#print axioms staircase_not_bisimilar
#print axioms staircase_adequacy_fails

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Prices.StaircaseStep
