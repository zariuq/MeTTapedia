import Mettapedia.Logic.PropositionalTseitin

/-!
# Polarity-directed structure-preserving clausification

The positive direction enforces `root → formula`; the negative direction
enforces `formula → root`. Implication reverses its antecedent's polarity.
The clauses are selected from the independent full Tseitin gate definitions,
using exactly the same postorder auxiliary names. Source-model projection is
exact, but auxiliary extensions need not be unique.

Reference: Plaisted and Greenbaum, *A Structure-preserving Clause Form
Translation* (1986), https://doi.org/10.1016/S0747-7171(86)80028-1.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.PropositionalPlaistedGreenbaum

open LO.Propositional (Formula)
open MarkovLogicClauseSemantics PropositionalTseitin

inductive Polarity where
  | positive | negative
  deriving DecidableEq, Repr

def Polarity.flip : Polarity → Polarity
  | .positive => .negative
  | .negative => .positive

def Polarity.accepts : Polarity → Bool → Bool
  | .positive, value => value
  | .negative, value => !value

/-- Directed gate meanings, stated independently of the emitted clauses. -/
def Polarity.Relates : Polarity → Bool → Bool → Prop
  | .positive, output, value => output = true → value = true
  | .negative, output, value => value = true → output = true

def leftPolarity (op : BinaryOp) (polarity : Polarity) : Polarity :=
  match op with | .imp => polarity.flip | _ => polarity

def directedGate {α : Type*} [DecidableEq α] (op : BinaryOp) (polarity : Polarity)
    (left right : Literal α) (output : α) : List (GroundClause α) :=
  match op, polarity with
  | .and, .positive | .or, .negative | .imp, .negative => (gateClauses op left right output).take 2
  | _, _ => (gateClauses op left right output).drop 2

theorem directedGate_correct {α : Type*} [DecidableEq α] (op : BinaryOp) (polarity : Polarity)
    (left right : Literal α) (output : α) (world : α → Bool) :
    evalCNF (directedGate op polarity left right output) world = true ↔
      polarity.Relates (world output) (op.eval (evalLiteral world left) (evalLiteral world right)) := by
  cases op <;> cases polarity <;> cases hl : evalLiteral world left <;> cases hr : evalLiteral world right <;>
    cases ho : world output <;> simp [directedGate, gateClauses, evalCNF, evalClause, BinaryOp.eval,
      Polarity.Relates, hl, hr, ho]

theorem directedGate_sublist {α : Type*} [DecidableEq α] (op : BinaryOp) (polarity : Polarity)
    (left right : Literal α) (output : α) :
    (directedGate op polarity left right output).Sublist (gateClauses op left right output) := by
  cases op <;> cases polarity <;> simp only [directedGate]
  all_goals first | exact List.take_sublist _ _ | exact List.drop_sublist _ _

theorem directedGate_length {α : Type*} [DecidableEq α] (op : BinaryOp) (polarity : Polarity)
    (left right : Literal α) (output : α) : (directedGate op polarity left right output).length ≤ 2 := by
  cases op <;> cases polarity <;> simp [directedGate, gateClauses]

def combine {n l r : Nat} (op : BinaryOp) (polarity : Polarity)
    (left : Encoding n l) (right : Encoding n r) : Encoding n (l + (r + 1)) where
  root := .pos (outputWire l r)
  clauses := renameCNF (leftWire r) left.clauses ++ renameCNF (rightWire l) right.clauses ++
    directedGate op polarity (renameLiteral (leftWire r) left.root)
      (renameLiteral (rightWire l) right.root) (outputWire l r)

def compile {n : Nat} : (polarity : Polarity) → (formula : Formula (Fin n)) → Encoding n (auxCount formula)
  | _, .atom a => ⟨.pos (.inl a), []⟩
  | .positive, .falsum => ⟨.pos (.inr (0 : Fin 1)), [{.neg (.inr (0 : Fin 1))}]⟩
  | .negative, .falsum => ⟨.pos (.inr (0 : Fin 1)), []⟩
  | polarity, .and a b => combine .and polarity (compile polarity a) (compile polarity b)
  | polarity, .or a b => combine .or polarity (compile polarity a) (compile polarity b)
  | polarity, .imp a b => combine .imp polarity (compile polarity.flip a) (compile polarity b)

@[simp] theorem compile_root {n : Nat} (polarity : Polarity) (formula : Formula (Fin n)) :
    (compile polarity formula).root = (PropositionalTseitin.compile formula).root := by
  cases formula <;> cases polarity <;> rfl

theorem compile_sublist {n : Nat} (polarity : Polarity) (formula : Formula (Fin n)) :
    (compile polarity formula).clauses.Sublist (PropositionalTseitin.compile formula).clauses := by
  induction formula generalizing polarity with
  | hatom => exact .refl _
  | hfalsum => cases polarity <;> simp [compile, PropositionalTseitin.compile]
  | hand a b ha hb | hor a b ha hb | himp a b ha hb =>
    simp only [compile, PropositionalTseitin.compile, combine, PropositionalTseitin.combine, compile_root]
    exact ((ha _).map _ |>.append ((hb _).map _)).append (directedGate_sublist _ _ _ _ _)

/-- Full semantic evaluation supplies an extension for both directed encodings. -/
theorem realized_satisfies {n : Nat} (polarity : Polarity) (formula : Formula (Fin n)) (input : Fin n → Bool) :
    evalCNF (compile polarity formula).clauses (read input (realizeAux input formula)) = true := by
  have full := (gates_iff formula input (realizeAux input formula)).mpr rfl
  simp only [evalCNF, List.all_eq_true] at full ⊢
  exact fun clause member => full clause ((compile_sublist polarity formula).subset member)

private theorem direction_compose (op : BinaryOp) (polarity : Polarity)
    (left right output actualLeft actualRight : Bool)
    (hl : (leftPolarity op polarity).Relates left actualLeft)
    (hr : polarity.Relates right actualRight)
    (gate : polarity.Relates output (op.eval left right)) :
    polarity.Relates output (op.eval actualLeft actualRight) := by
  cases op <;> cases polarity <;> cases left <;> cases right <;> cases output <;>
    cases actualLeft <;> cases actualRight <;>
    simp_all [leftPolarity, Polarity.flip, Polarity.Relates, BinaryOp.eval]

private theorem combine_clauses {n l r : Nat} (op : BinaryOp) (polarity : Polarity)
    (left : Encoding n l) (right : Encoding n r) (input : Fin n → Bool)
    (auxiliary : Fin (l + (r + 1)) → Bool) :
    evalCNF (combine op polarity left right).clauses (read input auxiliary) = true ↔
      evalCNF left.clauses (read input (leftAux auxiliary)) = true ∧
      evalCNF right.clauses (read input (rightAux auxiliary)) = true ∧
      polarity.Relates (lastAux auxiliary)
        (op.eval (evalLiteral (read input (leftAux auxiliary)) left.root)
          (evalLiteral (read input (rightAux auxiliary)) right.root)) := by
  simp only [combine, evalCNF_append, Bool.and_eq_true, evalCNF_rename, directedGate_correct,
    evalLiteral_rename, read_leftWire, read_rightWire, read_outputWire, and_assoc]

theorem compile_direction {n : Nat} (polarity : Polarity) (formula : Formula (Fin n))
    (input : Fin n → Bool) (auxiliary : Fin (auxCount formula) → Bool)
    (held : evalCNF (compile polarity formula).clauses (read input auxiliary) = true) :
    polarity.Relates (evalLiteral (read input auxiliary) (compile polarity formula).root) (eval input formula) := by
  induction formula generalizing polarity with
  | hatom a => cases polarity <;> simp [compile, eval, evalLiteral, PropositionalTseitin.read, Polarity.Relates]
  | hfalsum =>
    cases polarity with
    | positive =>
      change evalCNF [{.neg (.inr (0 : Fin 1))}] (read input auxiliary) = true at held
      have zero : auxiliary (0 : Fin 1) = false := by
        simp only [evalCNF, List.all_cons, List.all_nil, Bool.and_true,
          evalClause_singleton, evalLiteral] at held
        change (!auxiliary (0 : Fin 1)) = true at held
        simpa using held
      simpa [compile, eval, Polarity.Relates, evalLiteral, PropositionalTseitin.read, zero]
    | negative => simp [Polarity.Relates, eval]
  | hand a b ha hb =>
    obtain ⟨hl, hr, gate⟩ := (combine_clauses .and polarity _ _ input auxiliary).mp held
    exact direction_compose .and polarity _ _ _ _ _ (ha _ _ hl) (hb _ _ hr) gate
  | hor a b ha hb =>
    obtain ⟨hl, hr, gate⟩ := (combine_clauses .or polarity _ _ input auxiliary).mp held
    exact direction_compose .or polarity _ _ _ _ _ (ha _ _ hl) (hb _ _ hr) gate
  | himp a b ha hb =>
    obtain ⟨hl, hr, gate⟩ := (combine_clauses .imp polarity _ _ input auxiliary).mp held
    exact direction_compose .imp polarity _ _ _ _ _ (ha _ _ hl) (hb _ _ hr) gate

def signedRoot {α : Type*} (polarity : Polarity) (root : Literal α) : Literal α :=
  match polarity with | .positive => root | .negative => complement root

@[simp] theorem eval_signedRoot {α : Type*} (polarity : Polarity) (world : α → Bool) (root : Literal α) :
    evalLiteral world (signedRoot polarity root) = polarity.accepts (evalLiteral world root) := by
  cases polarity <;> simp [signedRoot, Polarity.accepts]

def asserted {n : Nat} (polarity : Polarity) (formula : Formula (Fin n)) : List (GroundClause (Wire n (auxCount formula))) :=
  (compile polarity formula).clauses ++ [{signedRoot polarity (compile polarity formula).root}]

/-- Arbitrary target assignments project to source assignments of the requested polarity. -/
theorem projects {n : Nat} (polarity : Polarity) (formula : Formula (Fin n)) (input : Fin n → Bool)
    (auxiliary : Fin (auxCount formula) → Bool)
    (held : evalCNF (asserted polarity formula) (read input auxiliary) = true) :
    polarity.accepts (eval input formula) = true := by
  simp only [asserted, evalCNF_append, Bool.and_eq_true] at held
  have gate := compile_direction polarity formula input auxiliary held.1
  have root : polarity.accepts (evalLiteral (read input auxiliary) (compile polarity formula).root) = true := by
    simpa only [evalCNF, List.all_cons, List.all_nil, Bool.and_true, evalClause_singleton, eval_signedRoot] using held.2
  have propagate (p : Polarity) (output value : Bool) :
      p.Relates output value → p.accepts output = true → p.accepts value = true := by
    cases p <;> cases output <;> cases value <;> simp [Polarity.Relates, Polarity.accepts]
  exact propagate polarity _ _ gate root

/-- Every source model has the independently computed canonical extension. -/
theorem extends_model {n : Nat} (polarity : Polarity) (formula : Formula (Fin n)) (input : Fin n → Bool)
    (held : polarity.accepts (eval input formula) = true) :
    evalCNF (asserted polarity formula) (read input (realizeAux input formula)) = true := by
  simp only [asserted, evalCNF_append, Bool.and_eq_true, realized_satisfies, true_and]
  simpa only [evalCNF, List.all_cons, List.all_nil, Bool.and_true, evalClause_singleton,
    eval_signedRoot, compile_root, root_eval] using held

theorem projection_exact {n : Nat} (polarity : Polarity) (formula : Formula (Fin n)) (input : Fin n → Bool) :
    (∃ auxiliary, evalCNF (asserted polarity formula) (read input auxiliary) = true) ↔
      polarity.accepts (eval input formula) = true :=
  ⟨fun ⟨auxiliary, held⟩ => projects polarity formula input auxiliary held,
    fun held => ⟨realizeAux input formula, extends_model polarity formula input held⟩⟩

theorem satisfiable_iff {n : Nat} (polarity : Polarity) (formula : Formula (Fin n)) :
    (∃ world, evalCNF (asserted polarity formula) world = true) ↔
      ∃ input, polarity.accepts (eval input formula) = true := by
  constructor
  · rintro ⟨world, held⟩
    have reconstruction : read (world ∘ Sum.inl) (world ∘ Sum.inr) = world := by funext w; cases w <;> rfl
    exact ⟨world ∘ Sum.inl, projects polarity formula _ _ (reconstruction.symm ▸ held)⟩
  · rintro ⟨input, held⟩
    exact ⟨read input (realizeAux input formula), extends_model polarity formula input held⟩

/-- Full defining clauses, with the same signed assertion as the directed encoding. -/
def fullAsserted {n : Nat} (polarity : Polarity) (formula : Formula (Fin n)) :
    List (GroundClause (Wire n (auxCount formula))) :=
  (PropositionalTseitin.compile formula).clauses ++ [{signedRoot polarity (PropositionalTseitin.compile formula).root}]

theorem asserted_sublist {n : Nat} (polarity : Polarity) (formula : Formula (Fin n)) :
    (asserted polarity formula).Sublist (fullAsserted polarity formula) := by
  simpa only [asserted, fullAsserted, compile_root] using
    (compile_sublist polarity formula).append (List.Sublist.refl [{signedRoot polarity (PropositionalTseitin.compile formula).root}])

theorem asserted_length_le_full {n : Nat} (polarity : Polarity) (formula : Formula (Fin n)) :
    (asserted polarity formula).length ≤ (fullAsserted polarity formula).length :=
  (asserted_sublist polarity formula).length_le

private theorem combine_length_bound {n l r : Nat} (op : BinaryOp) (polarity : Polarity)
    (left : Encoding n l) (right : Encoding n r)
    (hl : left.clauses.length ≤ 2*l) (hr : right.clauses.length ≤ 2*r) :
    (combine op polarity left right).clauses.length ≤ 2 * (l + (r+1)) := by
  have gate := directedGate_length op polarity
    (renameLiteral (leftWire r) left.root) (renameLiteral (rightWire l) right.root) (outputWire l r)
  simp only [combine, List.length_append, renameCNF, List.length_map]
  omega

theorem compile_length_le {n : Nat} (polarity : Polarity) (formula : Formula (Fin n)) :
    (compile polarity formula).clauses.length ≤ 2 * auxCount formula := by
  induction formula generalizing polarity with
  | hatom => simp [compile, auxCount]
  | hfalsum => cases polarity <;> simp [compile, auxCount]
  | hand a b ha hb => exact combine_length_bound .and polarity _ _ (ha polarity) (hb polarity)
  | hor a b ha hb => exact combine_length_bound .or polarity _ _ (ha polarity) (hb polarity)
  | himp a b ha hb => exact combine_length_bound .imp polarity _ _ (ha polarity.flip) (hb polarity)

theorem asserted_length_le {n : Nat} (polarity : Polarity) (formula : Formula (Fin n)) :
    (asserted polarity formula).length ≤ 2 * auxCount formula + 1 := by
  simpa only [asserted, List.length_append, List.length_singleton] using
    Nat.add_le_add_right (compile_length_le polarity formula) 1

def literalOccurrences {α : Type*} (clauses : List (GroundClause α)) : Nat :=
  (clauses.map Finset.card).sum

private theorem literalOccurrences_mono {α : Type*} {first second : List (GroundClause α)}
    (sublist : first.Sublist second) : literalOccurrences first ≤ literalOccurrences second := by
  induction sublist <;> simp_all [literalOccurrences]
  omega

theorem asserted_literalOccurrences_le {n : Nat} (polarity : Polarity) (formula : Formula (Fin n)) :
    literalOccurrences (asserted polarity formula) ≤ literalOccurrences (fullAsserted polarity formula) :=
  literalOccurrences_mono (asserted_sublist polarity formula)

theorem asserted_width {n : Nat} (polarity : Polarity) (formula : Formula (Fin n)) :
    ∀ clause ∈ asserted polarity formula, clause.card ≤ 3 := by
  intro clause member
  have member := (asserted_sublist polarity formula).subset member
  simp only [fullAsserted, List.mem_append, List.mem_singleton] at member
  rcases member with member | rfl
  · exact PropositionalTseitin.compile_width formula clause member
  · simp

end Mettapedia.Logic.PropositionalPlaistedGreenbaum
