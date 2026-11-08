import Mettapedia.Logic.ASP.CNF
import Mettapedia.Logic.ASP.Solver

/-!
# Nogoods as clauses, and the SAT personality as completion

The answer set solver's nogoods refine to the compact CNF of `CNF`: a nogood is
the clause of its negated literals (`Nogood.clause`). A total assignment
satisfies the clause exactly when it does not violate the nogood
(`Nogood.eval_clause`), so a list of nogoods and its CNF have the same solutions
(`eval_nogoodCNF`). Unit propagation refines as well: a nogood falsified by the
trail is a conflicting clause, and a nogood unit on `l` is a clause whose only
open literal is the complement of `l` (`Nogood.mem_openLits_clause`,
`Nogood.openLits_clause_eq_nil`, `Nogood.openLits_clause_of_unitOn`).

## The trust bridge

* `Program.completionCNF` is the CNF of the completion nogoods, the formula the
  SAT discipline sees. Its admissible solutions are exactly the supported models
  with correct body variables (`completionCNF_eval_iff`).
* `Program.loopNogoodList` lists the loop nogoods of every set of program atoms
  without falsum atoms; for a supported model with correct body variables, sets
  with falsum atoms or atoms outside the program add nothing
  (`loopNogoodList_ok_iff`).
  `Program.stableCNF`, the CNF of completion and loop nogoods, has exactly the
  stable models as admissible solutions (`stableCNF_eval_iff`).
* For tight programs the two coincide (`completionCNF_eval_iff_stable`), by
  Fages' theorem.

## The numbered form

A runtime numbers the program variables `0, 1, …, n - 1` in the order of
`Program.varList` (`Program.index`); a numbered formula is a formula over `ℕ`
(`Program.numbered`), the format of DIMACS and LRAT. Any assignment of numbers
reads back as an admissible assignment of solver variables
(`Program.decode`), and every assignment of solver variables is read back from
one (`Program.encode`, `decode_encode`). In this form there is no admissibility
side condition:

* `completionNumbered_eval_iff`, `supported_iff_completionNumbered`: the models
  of the numbered completion are exactly the supported models;
* `stableNumbered_eval_iff`, `stable_iff_stableNumbered`: the models of the
  numbered completion and loop nogoods are exactly the stable models;
* `stable_iff_completionNumbered_of_tight`: for tight programs, the completion
  alone has exactly the stable models.

So a SAT certificate certifies an answer set result: a model of
`stableNumbered` is a stable model (`stable_of_stableNumbered`); for a program
that is not tight, a model of the completion is checked by the reduct checker
(`isStable_iff`); unsatisfiability of the completion
refutes every supported, hence every stable, model
(`not_stable_of_completionNumbered_unsat`); unsatisfiability of the completion
and loop nogoods refutes every stable model (`not_stable_of_stableNumbered_unsat`).

## As a translation of logics

Completion with loop nogoods translates the theory of the program's stable models
into the theory of a CNF; `Borrowing` states it as a conservative route of
`InstitutionBorrowing`. Completion alone always borrows soundly (its models
include the stable models) but loses theorems unless the program is tight.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ASP

open CNF

universe u

variable {A : Type u}

/-! ## Nogoods as clauses -/

/-- A solver literal as a CNF literal over solver variables. -/
def Lit.toLiteral (l : Lit A) : CNF.Literal (Var A) := ⟨l.var, l.sign⟩

theorem Lit.toLiteral_injective : Function.Injective (Lit.toLiteral : Lit A → CNF.Literal (Var A)) := by
  rintro ⟨x, b⟩ ⟨y, c⟩ h
  simp only [Lit.toLiteral, CNF.Literal.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

@[simp] theorem Lit.toLiteral_compl (l : Lit A) : l.compl.toLiteral = l.toLiteral.neg := rfl

@[simp] theorem Lit.eval_toLiteral (v : Valuation A) (l : Lit A) : l.toLiteral.eval v = true ↔ l.Sat v := by
  simp [Lit.toLiteral, CNF.Literal.eval_eq_true, Lit.Sat]

/-- **The clause of a nogood**: the disjunction of its negated literals. -/
def Nogood.clause (δ : Nogood A) : CNF.Clause (Var A) := δ.lits.map fun l => l.compl.toLiteral

/-- A total assignment satisfies the clause of a nogood exactly when it does not violate it. -/
theorem Nogood.eval_clause (v : Valuation A) (δ : Nogood A) : δ.clause.eval v = true ↔ ¬ δ.Violated v := by
  rw [Nogood.not_violated_iff, CNF.Clause.eval_eq_true, Nogood.clause]
  constructor
  · rintro ⟨_, hm, h⟩
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hm
    refine ⟨l, hl, fun sat => ?_⟩
    rw [Lit.toLiteral_compl, CNF.Literal.eval_neg, (Lit.eval_toLiteral v l).mpr sat] at h
    cases h
  · rintro ⟨l, hl, notSat⟩
    refine ⟨_, List.mem_map_of_mem hl, ?_⟩
    rw [Lit.toLiteral_compl, CNF.Literal.eval_neg]
    cases h : l.toLiteral.eval v
    · rfl
    · exact absurd ((Lit.eval_toLiteral v l).mp h) notSat

/-- The CNF of a list of nogoods. -/
def nogoodCNF (Δ : List (Nogood A)) : CNF.Formula (Var A) := Δ.map Nogood.clause

/-- **The solutions correspond**: a total assignment satisfies the CNF of a list of nogoods
exactly when it violates none of them. -/
theorem eval_nogoodCNF (v : Valuation A) (Δ : List (Nogood A)) :
    (nogoodCNF Δ).eval v = true ↔ ∀ δ ∈ Δ, ¬ δ.Violated v := by
  simp [nogoodCNF, CNF.Formula.eval_eq_true, Nogood.eval_clause]

@[simp] theorem nogoodCNF_append (Δ Γ : List (Nogood A)) : nogoodCNF (Δ ++ Γ) = nogoodCNF Δ ++ nogoodCNF Γ :=
  List.map_append

section Propagation

variable [DecidableEq A]

/-- The literals of a trail as a partial assignment of the CNF. -/
def trailAssignment (lits : List (Lit A)) : List (CNF.Literal (Var A)) := lits.map Lit.toLiteral

omit [DecidableEq A] in
theorem mem_trailAssignment {lits : List (Lit A)} {l : Lit A} : l.toLiteral ∈ trailAssignment lits ↔ l ∈ lits :=
  List.mem_map.trans ⟨fun ⟨_, hm, same⟩ => Lit.toLiteral_injective same ▸ hm, fun h => ⟨l, h, rfl⟩⟩

/-- The open literals of a nogood's clause are the complements of its literals not on the trail. -/
theorem Nogood.mem_openLits_clause (δ : Nogood A) (lits : List (Lit A)) (m : CNF.Literal (Var A)) :
    m ∈ δ.clause.openLits (trailAssignment lits) ↔ ∃ n ∈ δ.lits, n ∉ lits ∧ m = n.compl.toLiteral := by
  simp only [CNF.Clause.openLits, Nogood.clause, List.mem_filter, List.mem_map, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨n, hn, rfl⟩, notOn⟩
    refine ⟨n, hn, fun on => notOn ?_, rfl⟩
    rw [Lit.toLiteral_compl, CNF.Literal.neg_neg]
    exact mem_trailAssignment.mpr on
  · rintro ⟨n, hn, notOn, rfl⟩
    refine ⟨⟨n, hn, rfl⟩, fun on => notOn ?_⟩
    rw [Lit.toLiteral_compl, CNF.Literal.neg_neg] at on
    exact mem_trailAssignment.mp on

/-- **A falsified nogood is a conflicting clause.** -/
theorem Nogood.openLits_clause_eq_nil (s : State A) (δ : Nogood A) :
    δ.clause.openLits (trailAssignment s.lits) = [] ↔ s.Falsifies δ := by
  rw [List.eq_nil_iff_forall_not_mem]
  simp only [Nogood.mem_openLits_clause, not_exists, not_and, State.Falsifies]
  constructor
  · intro h l hl
    by_contra notOn
    exact h _ l hl notOn rfl
  · intro h m n hn notOn _
    exact notOn (h n hn)

/-- **A unit nogood is a unit clause**: its only open literal is the complement of the unit
literal, which is what the solver pushes. -/
theorem Nogood.openLits_clause_of_unitOn {s : State A} {δ : Nogood A} {l : Lit A} (unit : s.UnitOn δ l) :
    ∀ m ∈ δ.clause.openLits (trailAssignment s.lits), m = l.compl.toLiteral := by
  intro m hm
  obtain ⟨n, hn, notOn, rfl⟩ := (δ.mem_openLits_clause s.lits m).mp hm
  by_contra ne
  exact notOn (unit.2.1 n hn fun same => ne (same ▸ rfl))

end Propagation

namespace Program

variable [DecidableEq A] (P : Program A)

/-! ## Loop nogoods as a list -/

/-- The atoms of the program that are not falsum atoms. -/
def loopAtoms : List A := P.allAtoms.filter fun a => !P.falsum a

/-- The loop nogoods of every set of program atoms without falsum atoms, as a list. -/
def loopNogoodList : List (Nogood A) :=
  P.loopAtoms.sublists.flatMap fun L => L.map (P.loopNogood L.toFinset)

/-- **Loop nogoods over program atoms without falsum atoms suffice**: for an admissible total
assignment of a supported model with correct body variables, violating none of the listed loop
nogoods is violating no loop nogood at all. -/
theorem loopNogoodList_ok_iff (v : Valuation A) (admissible : P.Admissible v) (correct : P.BodiesCorrect v)
    (supported : P.Supported v.atoms) :
    (∀ δ ∈ P.loopNogoodList, ¬ δ.Violated v) ↔ P.LoopSolution v := by
  constructor
  · intro h
    refine (P.loopSolution_iff_stable v correct supported).mpr (P.stable_of_loops v correct supported ?_)
    intro U noFalsum a ha violated
    rw [loopNogood_violated] at violated
    have loopAtom : ∀ x ∈ U, x ∈ P.atomSet → x ∈ P.loopAtoms := fun x hx hxP =>
      List.mem_filter.mpr ⟨(P.mem_allAtoms).mpr hxP, by simpa using (P.falsum_eq_false_iff).mpr (noFalsum x hx)⟩
    have aIn : a ∈ P.loopAtoms := loopAtom a ha (admissible a violated.1)
    have mem : P.loopNogood (P.loopAtoms.filter (· ∈ U)).toFinset a ∈ P.loopNogoodList :=
      List.mem_flatMap.mpr ⟨_, List.mem_sublists.mpr List.filter_sublist,
        List.mem_map_of_mem (List.mem_filter.mpr ⟨aIn, by simpa using ha⟩)⟩
    apply h _ mem
    rw [loopNogood_violated]
    refine ⟨violated.1, fun r hr external => violated.2 r hr ⟨?_, fun b hb inside => ?_⟩⟩
    · exact (by simpa using external.1 : r.head ∈ P.loopAtoms ∧ r.head ∈ U).2
    · have bIn : b ∈ P.loopAtoms := loopAtom b inside ⟨r, hr, Or.inr (Or.inl hb)⟩
      exact external.2 b hb (by simpa [bIn] using inside)
  · intro h δ hδ
    obtain ⟨L, -, hδ⟩ := List.mem_flatMap.mp hδ
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hδ
    exact h L.toFinset a (List.mem_toFinset.mpr ha)

/-! ## The CNF of a program -/

/-- **The CNF of the completion nogoods**: what the SAT discipline sees. -/
def completionCNF : CNF.Formula (Var A) := nogoodCNF P.completionNogoods

/-- The CNF of the completion and loop nogoods. -/
def stableCNF : CNF.Formula (Var A) := nogoodCNF (P.completionNogoods ++ P.loopNogoodList)

/-- **The SAT personality is ASP restricted to completion**: the admissible solutions of the
completion CNF are exactly the supported models, with correct body variables. -/
theorem completionCNF_eval_iff (v : Valuation A) (admissible : P.Admissible v) :
    P.completionCNF.eval v = true ↔ P.Supported v.atoms ∧ P.BodiesCorrect v :=
  (eval_nogoodCNF v _).trans (P.completionSolution_iff v admissible)

/-- **Adding the loop nogoods gives exactly the stable models.** -/
theorem stableCNF_eval_iff (v : Valuation A) (admissible : P.Admissible v) :
    P.stableCNF.eval v = true ↔ P.Stable v.atoms ∧ P.BodiesCorrect v := by
  rw [stableCNF, eval_nogoodCNF, List.forall_mem_append]
  constructor
  · rintro ⟨completion, loops⟩
    obtain ⟨supported, correct⟩ := (P.completionSolution_iff v admissible).mp completion
    exact (P.solution_iff_stable v admissible).mp
      ⟨completion, (P.loopNogoodList_ok_iff v admissible correct supported).mp loops⟩
  · rintro ⟨stable, correct⟩
    obtain ⟨completion, loops⟩ := (P.solution_iff_stable v admissible).mpr ⟨stable, correct⟩
    obtain ⟨supported, -⟩ := (P.completionSolution_iff v admissible).mp completion
    exact ⟨completion, (P.loopNogoodList_ok_iff v admissible correct supported).mpr loops⟩

/-- **For tight programs the two coincide** (Fages). -/
theorem completionCNF_eval_iff_stable (tight : P.Tight) (v : Valuation A) (admissible : P.Admissible v) :
    P.completionCNF.eval v = true ↔ P.Stable v.atoms ∧ P.BodiesCorrect v := by
  rw [completionCNF_eval_iff P v admissible, P.stable_iff_supported_of_tight tight]

/-- The completion CNF is part of the stable CNF. -/
theorem stableCNF_eq : P.stableCNF = P.completionCNF ++ nogoodCNF P.loopNogoodList := nogoodCNF_append _ _

/-! ## Variables -/

/-- The program variables in a fixed order: atoms in order of last occurrence, then the bodies of
the rules of atoms that are not falsum atoms, except unit bodies, in order of last occurrence. -/
def varList : List (Var A) := (P.allAtoms.map Var.atom ++ P.bodyRules.map fun r => Var.body r.body).dedup

theorem mem_varList {x : Var A} : x ∈ P.varList ↔ P.IsVar x := by
  rw [← P.mem_varFinset, varList, List.mem_dedup, varFinset, List.mem_toFinset]

theorem nodup_varList : P.varList.Nodup := List.nodup_dedup _

instance (x : Var A) : Decidable (P.IsVar x) := decidable_of_iff _ P.mem_varList

theorem completionCNF_vars : P.completionCNF.VarsIn {x | P.IsVar x} := by
  intro c hc l hl
  obtain ⟨δ, hδ, rfl⟩ := List.mem_map.mp hc
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hl
  exact P.completionNogoods_vars hδ m hm

theorem loopNogoodList_vars {δ : Nogood A} (hδ : δ ∈ P.loopNogoodList) : ∀ l ∈ δ.lits, P.IsVar l.var := by
  obtain ⟨L, sub, hδ⟩ := List.mem_flatMap.mp hδ
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hδ
  have within : ∀ x ∈ L, x ∈ P.loopAtoms := fun x hx => (List.mem_sublists.mp sub).subset hx
  intro l hl
  rcases P.loopNogood_vars (fun b hb => (P.falsum_eq_false_iff).mp
      (by simpa using (List.mem_filter.mp (within b (List.mem_toFinset.mp hb))).2)) hl with rfl | isVar
  · exact (P.mem_allAtoms).mp (List.mem_filter.mp (within a ha)).1
  · exact isVar

theorem stableCNF_vars : P.stableCNF.VarsIn {x | P.IsVar x} := by
  intro c hc l hl
  obtain ⟨δ, hδ, rfl⟩ := List.mem_map.mp hc
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hl
  rcases List.mem_append.mp hδ with hδ | hδ
  · exact P.completionNogoods_vars hδ m hm
  · exact P.loopNogoodList_vars hδ m hm

/-! ## Numbering -/

/-- The number of a solver variable: its position in `varList`. -/
def index (x : Var A) : ℕ := P.varList.idxOf x

theorem index_lt {x : Var A} (h : P.IsVar x) : P.index x < P.varList.length :=
  List.idxOf_lt_length_of_mem ((P.mem_varList).mpr h)

theorem getElem?_index {x : Var A} (h : P.IsVar x) : P.varList[P.index x]? = some x :=
  List.getElem?_idxOf ((P.mem_varList).mpr h)

/-- A formula over solver variables, numbered. -/
def numbered (F : CNF.Formula (Var A)) : CNF.Formula ℕ := F.rename P.index

/-- An assignment of numbers read back as an assignment of solver variables, false outside the
program. -/
def decode (σ : ℕ → Bool) : Valuation A := fun x => decide (P.IsVar x) && σ (P.index x)

/-- An assignment of solver variables as an assignment of numbers. -/
def encode (v : Valuation A) : ℕ → Bool := fun i => (P.varList[i]?).elim false v

theorem decode_admissible (σ : ℕ → Bool) : P.Admissible (P.decode σ) := by
  intro a h
  simp only [decode, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem decode_of_isVar (σ : ℕ → Bool) {x : Var A} (h : P.IsVar x) : P.decode σ x = σ (P.index x) := by
  simp [decode, h]

theorem decode_encode (v : Valuation A) {x : Var A} (h : P.IsVar x) : P.decode (P.encode v) x = v x := by
  rw [decode_of_isVar P _ h, encode, P.getElem?_index h]
  rfl

/-- A numbered formula over program variables is evaluated by decoding. -/
theorem numbered_eval {F : CNF.Formula (Var A)} (vars : F.VarsIn {x | P.IsVar x}) (σ : ℕ → Bool) :
    (P.numbered F).eval σ = F.eval (P.decode σ) := by
  rw [numbered, CNF.Formula.eval_rename]
  exact CNF.Formula.eval_congr fun c hc l hl => (P.decode_of_isVar σ (vars c hc l hl)).symm

/-- Decoding the encoding of an assignment does not change the value of a formula over program
variables. -/
theorem eval_decode_encode {F : CNF.Formula (Var A)} (vars : F.VarsIn {x | P.IsVar x}) (v : Valuation A) :
    F.eval (P.decode (P.encode v)) = F.eval v :=
  CNF.Formula.eval_congr fun c hc l hl => P.decode_encode v (vars c hc l hl)

/-- Numbering is injective on program variables. -/
theorem index_injOn {x y : Var A} (hx : P.IsVar x) (hy : P.IsVar y) (h : P.index x = P.index y) : x = y := by
  have := P.getElem?_index hx
  rw [h, P.getElem?_index hy] at this
  exact (Option.some.inj this).symm

/-- The numbered completion. -/
def completionNumbered : CNF.Formula ℕ := P.numbered P.completionCNF

/-- The numbered completion and loop nogoods. -/
def stableNumbered : CNF.Formula ℕ := P.numbered P.stableCNF

theorem completionNumbered_eval_iff (σ : ℕ → Bool) :
    P.completionNumbered.eval σ = true ↔ P.Supported (P.decode σ).atoms ∧ P.BodiesCorrect (P.decode σ) := by
  rw [completionNumbered, P.numbered_eval P.completionCNF_vars]
  exact P.completionCNF_eval_iff _ (P.decode_admissible σ)

theorem stableNumbered_eval_iff (σ : ℕ → Bool) :
    P.stableNumbered.eval σ = true ↔ P.Stable (P.decode σ).atoms ∧ P.BodiesCorrect (P.decode σ) := by
  rw [stableNumbered, P.numbered_eval P.stableCNF_vars]
  exact P.stableCNF_eval_iff _ (P.decode_admissible σ)

theorem decode_encode_atoms {M : Set A} (within : M ⊆ P.atomSet) :
    (P.decode (P.encode (canonical M))).atoms = M := by
  ext a
  by_cases h : a ∈ P.atomSet
  · change P.decode _ (.atom a) = true ↔ a ∈ M
    rw [P.decode_encode _ (show P.IsVar (.atom a) from h)]
    simp [canonical]
  · change P.decode _ (.atom a) = true ↔ a ∈ M
    have : ¬ P.IsVar (.atom a) := h
    simp only [decode, this, decide_false, Bool.false_and, Bool.false_eq_true, false_iff]
    exact fun hM => h (within hM)

/-- **The models of the numbered completion are exactly the supported models.** -/
theorem supported_iff_completionNumbered (M : Set A) :
    P.Supported M ↔ ∃ σ, P.completionNumbered.eval σ = true ∧ (P.decode σ).atoms = M := by
  constructor
  · intro supported
    have within : M ⊆ P.atomSet := supported ▸ (P.step_subset_headSet M M).trans P.headSet_subset_atomSet
    refine ⟨P.encode (canonical M), ?_, P.decode_encode_atoms within⟩
    rw [completionNumbered, P.numbered_eval P.completionCNF_vars, P.eval_decode_encode P.completionCNF_vars]
    exact (eval_nogoodCNF _ _).mpr (P.completionSolution_canonical supported)
  · rintro ⟨σ, sat, rfl⟩
    exact ((P.completionNumbered_eval_iff σ).mp sat).1

/-- **The models of the numbered completion and loop nogoods are exactly the stable models.** -/
theorem stable_iff_stableNumbered (M : Set A) :
    P.Stable M ↔ ∃ σ, P.stableNumbered.eval σ = true ∧ (P.decode σ).atoms = M := by
  constructor
  · intro stable
    obtain ⟨admissible, correct, stable'⟩ := P.stable_canonical stable
    have within : M ⊆ P.atomSet := stable.subset_headSet.trans P.headSet_subset_atomSet
    refine ⟨P.encode (canonical M), ?_, P.decode_encode_atoms within⟩
    rw [stableNumbered, P.numbered_eval P.stableCNF_vars, P.eval_decode_encode P.stableCNF_vars]
    exact (P.stableCNF_eval_iff _ admissible).mpr ⟨stable', correct⟩
  · rintro ⟨σ, sat, rfl⟩
    exact ((P.stableNumbered_eval_iff σ).mp sat).1

/-- **For tight programs the numbered completion has exactly the stable models.** -/
theorem stable_iff_completionNumbered_of_tight (tight : P.Tight) (M : Set A) :
    P.Stable M ↔ ∃ σ, P.completionNumbered.eval σ = true ∧ (P.decode σ).atoms = M := by
  rw [P.stable_iff_supported_of_tight tight, supported_iff_completionNumbered]

/-! ## Certificates -/

/-- The true atoms of a numbered assignment, as a finite set. -/
def decodeModel (σ : ℕ → Bool) : Finset A := (P.allAtoms.filter fun a => σ (P.index (.atom a))).toFinset

theorem coe_decodeModel (σ : ℕ → Bool) : (↑(P.decodeModel σ) : Set A) = (P.decode σ).atoms := by
  ext a
  simp only [decodeModel, List.coe_toFinset, List.mem_filter, Set.mem_ofPred_eq, Valuation.atoms, decode,
    Bool.and_eq_true, decide_eq_true_eq, P.mem_allAtoms]
  rfl

/-- **A model of the numbered completion and loop nogoods is a stable model.** -/
theorem stable_of_stableNumbered {σ : ℕ → Bool} (h : P.stableNumbered.eval σ = true) :
    P.Stable ↑(P.decodeModel σ) := by
  rw [coe_decodeModel]
  exact ((P.stableNumbered_eval_iff σ).mp h).1

/-- **An unsatisfiable completion refutes every supported model.** -/
theorem not_supported_of_completionNumbered_unsat (h : P.completionNumbered.Unsat) (M : Set A) :
    ¬ P.Supported M := by
  intro supported
  obtain ⟨σ, sat, -⟩ := (P.supported_iff_completionNumbered M).mp supported
  rw [h σ] at sat
  cases sat

/-- An unsatisfiable completion refutes every stable model, of any program. -/
theorem not_stable_of_completionNumbered_unsat (h : P.completionNumbered.Unsat) (M : Set A) :
    ¬ P.Stable M :=
  fun stable => P.not_supported_of_completionNumbered_unsat h M (P.stable_supported stable)

/-- **Unsatisfiable completion and loop nogoods refute every stable model.** -/
theorem not_stable_of_stableNumbered_unsat (h : P.stableNumbered.Unsat) (M : Set A) : ¬ P.Stable M := by
  intro stable
  obtain ⟨σ, sat, -⟩ := (P.stable_iff_stableNumbered M).mp stable
  rw [h σ] at sat
  cases sat

end Program

end Mettapedia.Logic.ASP
