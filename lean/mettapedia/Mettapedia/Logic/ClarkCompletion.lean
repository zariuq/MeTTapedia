import Mettapedia.Logic.NormalProgramSemantics
import Mettapedia.Logic.PropositionalTseitin
import Mathlib.Data.List.NodupEquivFin

/-!
# Structural Clark completion of finite ground normal programs

An explicit finite atom table supplies the program variables. Independent
random choices occupy a separate block: a selected fact is one possible source
of support, and rules may derive the same atom when that choice is false.
Completion closes every atom in the table, including undefined query atoms.
No interpretation enumeration or least-model computation enters the emitter.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ClarkCompletion

open LP BDDCore NormalProgramSemantics PropositionalTseitin
open LO.Propositional (Formula)

structure AtomTable (A : Type*) where
  atoms : List A
  nodup : atoms.Nodup

namespace AtomTable

variable {A : Type*} [DecidableEq A] (table : AtomTable A)

def index (a : A) (member : a ∈ table.atoms) : Fin table.atoms.length :=
  (table.nodup.getEquiv table.atoms).symm ⟨a, member⟩

@[simp] theorem at_index (a : A) (member : a ∈ table.atoms) :
    table.atoms.get (table.index a member) = a :=
  congrArg Subtype.val ((table.nodup.getEquiv table.atoms).apply_symm_apply ⟨a, member⟩)

@[simp] theorem index_at (i : Fin table.atoms.length) :
    table.index (table.atoms.get i) (List.get_mem _ _) = i :=
  (table.nodup.getEquiv table.atoms).symm_apply_apply i

def read (values : Fin table.atoms.length → Bool) (a : A) : Bool :=
  if member : a ∈ table.atoms then values (table.index a member) else false

@[simp] theorem read_at (values : Fin table.atoms.length → Bool) (i : Fin table.atoms.length) :
    table.read values (table.atoms.get i) = values i := by
  rw [read, dif_pos (List.get_mem _ _), index_at]

def interpretation (values : Fin table.atoms.length → Bool) : Set A := {a | table.read values a = true}

theorem interpretation_injective : Function.Injective table.interpretation := by
  intro first second same
  funext i
  apply Bool.eq_iff_iff.mpr
  have h := Set.ext_iff.mp same (table.atoms.get i)
  change (table.read first (table.atoms.get i) = true ↔ table.read second (table.atoms.get i) = true) at h
  simpa only [read_at] using h

theorem eq_interpretation_iff (S : Set A) (contained : S ⊆ {a | a ∈ table.atoms})
    (values : Fin table.atoms.length → Bool) :
    S = table.interpretation values ↔ ∀ i, (table.atoms.get i ∈ S ↔ values i = true) := by
  constructor
  · intro same i
    rw [same]
    change (table.read values (table.atoms.get i) = true ↔ values i = true)
    rw [read_at]
  · intro agree
    ext a
    by_cases member : a ∈ table.atoms
    · have h := agree (table.index a member)
      rw [at_index] at h
      change (a ∈ S ↔ table.read values a = true)
      simpa only [read, dif_pos member] using h
    · have absent : a ∉ S := fun h => member (contained h)
      simp [interpretation, read, member, absent]

theorem interpretation_realize (S : Set A) (contained : S ⊆ {a | a ∈ table.atoms}) :
    table.interpretation (fun i => by classical exact decide (table.atoms.get i ∈ S)) = S := by
  classical
  apply ((eq_interpretation_iff table S contained _).mpr ?_).symm
  simp

end AtomTable

variable {σ : LPSignature} [DecidableEq (GroundAtom σ)]

def goalAtoms : GoalLit σ → List (GroundAtom σ)
  | .pos a | .neg a => [a]
  | .neq a b => [a, b]

def clauseAtoms (c : NormalClause σ) : List (GroundAtom σ) :=
  c.head :: c.body.flatMap goalAtoms

def programTable {n : Nat} (facts : Fin n → GroundAtom σ) (rules : List (NormalClause σ))
    (goals : List (GoalLit σ)) : AtomTable (GroundAtom σ) where
  atoms := (List.ofFn facts ++ rules.flatMap clauseAtoms ++ goals.flatMap goalAtoms).dedup
  nodup := List.nodup_dedup _

def Covers {n : Nat} (table : AtomTable (GroundAtom σ)) (facts : Fin n → GroundAtom σ)
    (rules : List (NormalClause σ)) : Prop :=
  (∀ i, facts i ∈ table.atoms) ∧ ∀ c ∈ rules, c.head ∈ table.atoms

theorem programTable_covers {n : Nat} (facts : Fin n → GroundAtom σ) (rules : List (NormalClause σ))
    (goals : List (GoalLit σ)) : Covers (programTable facts rules goals) facts rules := by
  constructor
  · intro i
    simp [programTable]
  · intro c hc
    simp only [programTable, List.mem_dedup, List.mem_append]
    exact Or.inl (Or.inr (List.mem_flatMap.mpr ⟨c, hc, by simp [clauseAtoms]⟩))

def chosenFacts {n : Nat} (facts : Fin n → GroundAtom σ) (choice : Fin n → Bool) : Set (GroundAtom σ) :=
  {a | ∃ i, choice i = true ∧ facts i = a}

omit [DecidableEq (GroundAtom σ)] in
theorem consequences_contained {n : Nat} (table : AtomTable (GroundAtom σ))
    (facts : Fin n → GroundAtom σ) (rules : List (NormalClause σ)) (covers : Covers table facts rules)
    (choice : Fin n → Bool) (S : Set (GroundAtom σ)) :
    chosenFacts facts choice ∪ T_normal rules S S ⊆ {a | a ∈ table.atoms} := by
  rintro a (⟨i, _, rfl⟩ | ⟨c, hc, rfl, _⟩)
  · exact covers.1 i
  · exact covers.2 c hc

@[simp] theorem eval_conj {α : Type*} (world : α → Bool) (formulas : List (Formula α)) :
    eval world formulas.conj = true ↔ ∀ f ∈ formulas, eval world f = true := by
  induction formulas <;> simp_all [List.conj, eval]

@[simp] theorem eval_disj {α : Type*} (world : α → Bool) (formulas : List (Formula α)) :
    eval world formulas.disj = true ↔ ∃ f ∈ formulas, eval world f = true := by
  induction formulas <;> simp_all [List.disj, eval]

theorem eval_equivalence {α : Type*} (world : α → Bool) (a b : Formula α) :
    eval world (.and (.imp a b) (.imp b a)) = true ↔ (eval world a = true ↔ eval world b = true) := by
  cases ha : eval world a <;> cases hb : eval world b <;> simp [eval, ha, hb]

def atomFormula (table : AtomTable (GroundAtom σ)) (n : Nat) (a : GroundAtom σ) :
    Formula (Fin (n + table.atoms.length)) :=
  if member : a ∈ table.atoms then .atom (Fin.natAdd n (table.index a member)) else .falsum

@[simp] theorem eval_atomFormula (table : AtomTable (GroundAtom σ)) {n : Nat}
    (choice : Fin n → Bool) (values : Fin table.atoms.length → Bool) (a : GroundAtom σ) :
    eval (Fin.addCases choice values) (atomFormula table n a) = table.read values a := by
  by_cases member : a ∈ table.atoms <;> simp [atomFormula, AtomTable.read, member, eval]

def goalFormula (table : AtomTable (GroundAtom σ)) (n : Nat) :
    GoalLit σ → Formula (Fin (n + table.atoms.length))
  | .pos a => atomFormula table n a
  | .neg a => .imp (atomFormula table n a) .falsum
  | .neq a b => if a = b then .falsum else .imp .falsum .falsum

@[simp] theorem eval_goalFormula (table : AtomTable (GroundAtom σ)) {n : Nat}
    (choice : Fin n → Bool) (values : Fin table.atoms.length → Bool) (g : GoalLit σ) :
    eval (Fin.addCases choice values) (goalFormula table n g) = true ↔
      goalLitHoldsIn (table.interpretation values) (table.interpretation values) g := by
  cases g <;> simp [goalFormula, eval, goalLitHoldsIn, AtomTable.interpretation]
  split_ifs <;> simp_all [eval]

def goalsFormula (table : AtomTable (GroundAtom σ)) (n : Nat) (goals : List (GoalLit σ)) :
    Formula (Fin (n + table.atoms.length)) := (goals.map (goalFormula table n)).conj

@[simp] theorem eval_goalsFormula (table : AtomTable (GroundAtom σ)) {n : Nat}
    (choice : Fin n → Bool) (values : Fin table.atoms.length → Bool) (goals : List (GoalLit σ)) :
    eval (Fin.addCases choice values) (goalsFormula table n goals) = true ↔
      ∀ g ∈ goals, goalLitHoldsIn (table.interpretation values) (table.interpretation values) g := by
  simp [goalsFormula]

def definingFormula {n : Nat} (table : AtomTable (GroundAtom σ)) (facts : Fin n → GroundAtom σ)
    (rules : List (NormalClause σ)) (a : GroundAtom σ) : Formula (Fin (n + table.atoms.length)) :=
  .or (((List.finRange n).filter (fun i => facts i = a)).map
      (fun i => Formula.atom (Fin.castAdd table.atoms.length i))).disj
    ((rules.filter (fun c => c.head = a)).map (fun c => goalsFormula table n c.body)).disj

theorem eval_definingFormula {n : Nat} (table : AtomTable (GroundAtom σ)) (facts : Fin n → GroundAtom σ)
    (rules : List (NormalClause σ)) (choice : Fin n → Bool) (values : Fin table.atoms.length → Bool)
    (a : GroundAtom σ) :
    eval (Fin.addCases choice values) (definingFormula table facts rules a) = true ↔
      a ∈ chosenFacts facts choice ∪ T_normal rules (table.interpretation values) (table.interpretation values) := by
  simp [definingFormula, eval, chosenFacts, T_normal, normalClauseBodyHolds, and_assoc, and_comm]

/-- All defined and undefined atoms are closed, while independent choices remain free. -/
def completion {n : Nat} (table : AtomTable (GroundAtom σ)) (facts : Fin n → GroundAtom σ)
    (rules : List (NormalClause σ)) : Formula (Fin (n + table.atoms.length)) :=
  ((List.finRange table.atoms.length).map fun i =>
    let atom := Formula.atom (Fin.natAdd n i)
    let body := definingFormula table facts rules (table.atoms.get i)
    Formula.and (.imp atom body) (.imp body atom)).conj

theorem completion_models {n : Nat} (table : AtomTable (GroundAtom σ)) (facts : Fin n → GroundAtom σ)
    (rules : List (NormalClause σ)) (covers : Covers table facts rules)
    (choice : Fin n → Bool) (values : Fin table.atoms.length → Bool) :
    eval (Fin.addCases choice values) (completion table facts rules) = true ↔
      SupportedModel rules (chosenFacts facts choice) (table.interpretation values) := by
  rw [SupportedModel, table.eq_interpretation_iff _ (consequences_contained table facts rules covers choice _) values]
  simp only [completion, eval_conj, List.mem_map, List.mem_finRange, true_and, forall_exists_index,
    forall_apply_eq_imp_iff]
  apply forall_congr'
  intro i
  rw [eval_equivalence]
  rw [show eval (Fin.addCases choice values) (Formula.atom (Fin.natAdd n i)) = values i by simp [eval]]
  rw [eval_definingFormula]
  exact iff_comm

theorem completion_stable {n : Nat} (table : AtomTable (GroundAtom σ)) (facts : Fin n → GroundAtom σ)
    (rules : List (NormalClause σ)) (covers : Covers table facts rules) (tight : Tight rules)
    (choice : Fin n → Bool) (values : Fin table.atoms.length → Bool) :
    eval (Fin.addCases choice values) (completion table facts rules) = true ↔
      StableModel rules (chosenFacts facts choice) (table.interpretation values) := by
  rw [completion_models table facts rules covers, stable_iff_supported tight]

noncomputable def modelValues {n : Nat} (table : AtomTable (GroundAtom σ))
    (facts : Fin n → GroundAtom σ) (rules : List (NormalClause σ))
    (s : Stratification σ) (choice : Fin n → Bool) : Fin table.atoms.length → Bool := by
  classical
  exact fun i => decide (table.atoms.get i ∈ fullStratifiedModel rules (chosenFacts facts choice) s)

theorem modelValues_interpretation {n : Nat} (table : AtomTable (GroundAtom σ))
    (facts : Fin n → GroundAtom σ) (rules : List (NormalClause σ)) (covers : Covers table facts rules)
    (s : Stratification σ) (stratified : ∀ c ∈ rules, respectsStratification c s) (choice : Fin n → Bool) :
    table.interpretation (modelValues table facts rules s choice) =
      fullStratifiedModel rules (chosenFacts facts choice) s := by
  apply table.interpretation_realize
  have supported := full_supported rules (chosenFacts facts choice) s stratified
  rw [← supported]
  exact consequences_contained table facts rules covers choice _

/-- The program valuation is uniquely determined by the random choices. -/
theorem completion_iff_modelValues {n : Nat} (table : AtomTable (GroundAtom σ))
    (facts : Fin n → GroundAtom σ) (rules : List (NormalClause σ)) (covers : Covers table facts rules)
    (tight : Tight rules) (s : Stratification σ) (stratified : ∀ c ∈ rules, respectsStratification c s)
    (choice : Fin n → Bool) (values : Fin table.atoms.length → Bool) :
    eval (Fin.addCases choice values) (completion table facts rules) = true ↔
      values = modelValues table facts rules s choice := by
  rw [completion_models table facts rules covers,
    supported_iff_eq_full rules (chosenFacts facts choice) s stratified tight,
    ← modelValues_interpretation table facts rules covers s stratified choice]
  exact table.interpretation_injective.eq_iff

theorem completion_unique_extension {n : Nat} (table : AtomTable (GroundAtom σ))
    (facts : Fin n → GroundAtom σ) (rules : List (NormalClause σ)) (covers : Covers table facts rules)
    (tight : Tight rules) (s : Stratification σ) (stratified : ∀ c ∈ rules, respectsStratification c s)
    (choice : Fin n → Bool) :
    ∃! values, eval (Fin.addCases choice values) (completion table facts rules) = true := by
  simp only [completion_iff_modelValues table facts rules covers tight s stratified]
  exact existsUnique_eq

def completionQuery {n : Nat} (table : AtomTable (GroundAtom σ)) (facts : Fin n → GroundAtom σ)
    (rules : List (NormalClause σ)) (goals : List (GoalLit σ)) : Formula (Fin (n + table.atoms.length)) :=
  .and (completion table facts rules) (goalsFormula table n goals)

theorem completionQuery_correct {n : Nat} (table : AtomTable (GroundAtom σ))
    (facts : Fin n → GroundAtom σ) (rules : List (NormalClause σ)) (covers : Covers table facts rules)
    (tight : Tight rules) (s : Stratification σ) (stratified : ∀ c ∈ rules, respectsStratification c s)
    (choice : Fin n → Bool) (values : Fin table.atoms.length → Bool) (goals : List (GoalLit σ)) :
    eval (Fin.addCases choice values) (completionQuery table facts rules goals) = true ↔
      values = modelValues table facts rules s choice ∧
        ∀ g ∈ goals, goalLitHoldsIn (fullStratifiedModel rules (chosenFacts facts choice) s)
          (fullStratifiedModel rules (chosenFacts facts choice) s) g := by
  simp only [completionQuery, eval, Bool.and_eq_true,
    completion_iff_modelValues table facts rules covers tight s stratified, eval_goalsFormula]
  apply and_congr_right
  intro same
  rw [same, modelValues_interpretation table facts rules covers s stratified choice]

end Mettapedia.Logic.ClarkCompletion
