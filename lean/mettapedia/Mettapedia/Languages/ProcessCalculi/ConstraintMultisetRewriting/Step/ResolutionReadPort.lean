import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSchematicStorage
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ResolutionFiring

/-!
# Resolution through the read port

A definite program is stored in the space: each clause is one occurrence whose row is an ordinary
stored schema (`ContextualStoredRows.store`), its variables private to the row. A resolution step
is one firing of the activated step (`ContextualActivatedStep`):

* it **takes** the selected goal occurrence, a shared row;
* it **reads** the clause occurrence; the read port opens the stored schema at the port's own scope
  (`ContextualStoredRows.prepared_read_store`), so the clause's variables become the firing's fresh
  helpers `ScopedVar.at s _`, at a scope `s` outside the occupied ledger and different from every
  other port of the firing;
* it **tells**, through its take and read equations, that the goal equals the opened head;
* it **makes** the body goals.

Terms are first-order: the signature `logic` has the program's function symbols, each predicate
among them, and one clause former per body length; every metavariable is a parameterless
first-order variable.

## Theorems

* **Admission is unification, the clause present, and freshness** (`resolve_valid_iff`,
  `readScope_fresh`, `readScope_ne_ruleScope`): the firing is admitted exactly when the goal and the
  clause are present and distinct, the made occurrences are distinct, fresh and carry the rule's body
  ports, and the transported knowledge together with "goal = opened head" is solvable.
* **The result is the resolvent with the clause still present** (`resolve_result_present`,
  `resolve_clause_stays`, `resolve_clause_row`): the goal is consumed, the body goals are made, every
  other occurrence survives, the clause occurrence among them, and its row is still the same
  unspecialized stored schema.
* **The built-in clause is the prepared special case** (`solvable_iff_builtIn`,
  `models_builtIn_of_models`, `models_of_models_builtIn`, `extend_off_rule`): the raw occurrence
  firing whose rule is `Resolution.builtInRule` on the clause already opened at the read scope (take
  the goal with the opened head, make the opened body) has, on the transported configuration, the
  same solutions as the read-port firing once the rule's own variables are forgotten: every solution
  of the read-port information solves the built-in one, and every solution of the built-in one
  extends, changing nothing off the rule scope, to a solution of the read-port one. In particular
  the two are solvable together. The one-frame `Resolution.resolve` is the same built-in rule
  prepared by a renaming instead of by the read port.
* **Two reads of one clause never share helpers** (`two_reads_apart`): successive firings reserve
  disjoint scopes, so the opened copies of one stored clause have disjoint fresh variables.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Resolution.ReadPort

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe u

/-! ## First-order terms with clause formers -/

/-- Function symbols, predicates among them, and one clause former per body length. -/
inductive Sym (F : Type) where
  | fn (f : F)
  | clause (n : ℕ)

/-- **The first-order signature of a program**: one sort, the function symbols with their arities,
and the clause former of `n` body atoms with `n + 1` arguments. -/
abbrev logic (F : Type) (arity : F → ℕ) : Signature where
  Srt := Unit
  Op _ := Sym F
  arity
    | .fn f => List.replicate (arity f) ([], ())
    | .clause n => List.replicate (n + 1) ([], ())

variable {F : Type} {arity : F → ℕ}

/-- Every metavariable is a parameterless first-order variable. -/
abbrev firstOrder (V : Type) : V → MetaArity (logic F arity) := fun _ => ([], ())

/-- First-order terms over a declaration family. -/
abbrev Tm {V : Type} (declaration : V → MetaArity (logic F arity)) :=
  Term (signature (logic F arity) declaration) [] ()

variable {V W : Type} {declaration : V → MetaArity (logic F arity)}
  {next : W → MetaArity (logic F arity)}

/-- The arguments of a first-order operator from a function of positions. -/
def argsOf : (n : ℕ) → (Fin n → Tm declaration) →
    Args (signature (logic F arity) declaration) (List.replicate n ([], ())) []
  | 0, _ => .nil
  | n + 1, terms => .cons (terms 0) (argsOf n fun i => terms i.succ)

theorem instantiateArgs_argsOf (assignment : Assignment declaration next) :
    ∀ (n : ℕ) (terms : Fin n → Tm declaration),
      instantiateArgs assignment (argsOf n terms) = argsOf n fun i => instantiate assignment (terms i)
  | 0, _ => rfl
  | n + 1, terms => by
      show Args.cons _ (instantiateArgs assignment (argsOf n fun i => terms i.succ)) = Args.cons _ _
      rw [instantiateArgs_argsOf assignment n]

theorem argsOf_injective : ∀ (n : ℕ) {first second : Fin n → Tm declaration},
    argsOf n first = argsOf n second → first = second
  | 0, _, _, _ => funext fun i => i.elim0
  | n + 1, first, second, same => by
      injection same with _ _ _ _ head tail
      have rest := argsOf_injective n tail
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact head
      · exact congrFun rest j

/-- **A clause as a term**: its head and its `n` body atoms. -/
def clauseTerm (n : ℕ) (head : Tm declaration) (body : Fin n → Tm declaration) : Tm declaration :=
  .op (.inl (.clause n)) (argsOf (n + 1) (Fin.cons head body))

theorem instantiate_clauseTerm (assignment : Assignment declaration next) (n : ℕ)
    (head : Tm declaration) (body : Fin n → Tm declaration) :
    instantiate assignment (clauseTerm n head body) =
      clauseTerm n (instantiate assignment head) fun i => instantiate assignment (body i) := by
  show Term.op (S := signature (logic F arity) next) (Sum.inl (Sym.clause n))
      (instantiateArgs assignment (argsOf (n + 1) (Fin.cons head body))) = Term.op _ _
  rw [instantiateArgs_argsOf]
  congr 2
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem clauseTerm_injective {n : ℕ} {head head' : Tm declaration} {body body' : Fin n → Tm declaration}
    (same : clauseTerm n head body = clauseTerm n head' body') : head = head' ∧ body = body' := by
  injection same with _ _ _ arguments
  have fields := argsOf_injective (n + 1) arguments
  exact ⟨by simpa using congrFun fields 0, funext fun i => by simpa using congrFun fields i.succ⟩

/-! ## The resolution rule and its firing -/

variable {Shared : Type} {O : Type u} [DecidableEq O]

/-- Clause variables and rule variables are named by `ℕ`; the caller's variables by `Shared`. -/
abbrev locals : ℕ → MetaArity (logic F arity) := firstOrder ℕ
abbrev captures : Shared → MetaArity (logic F arity) := firstOrder Shared

abbrev source := ContextualActivatedStep.source (locals (F := F) (arity := arity)) (captures (Shared := Shared))
abbrev target := ContextualActivatedStep.target (locals (F := F) (arity := arity)) (captures (Shared := Shared))

/-- The rule's goal variable `G`. -/
def goalVar : Tm (source (F := F) (arity := arity) (Shared := Shared)) := 
  generator (source (F := F) (arity := arity) (Shared := Shared)) (Sum.inl 0)

/-- The rule's body variables `B₀ … Bₙ₋₁`. -/
def bodyVar {n : ℕ} (i : Fin n) : Tm (source (F := F) (arity := arity) (Shared := Shared)) :=
  generator (source (F := F) (arity := arity) (Shared := Shared)) (Sum.inl (i.val + 1))

/-- **The resolution rule for clauses with `n` body atoms**: take `G`, read `clause(G, B)`, make `B`.
The take and read equations together tell that the goal equals the opened head. -/
def rule (n : ℕ) : RuleInstance (Tm (source (F := F) (arity := arity) (Shared := Shared))) :=
  ⟨[goalVar], [clauseTerm n goalVar bodyVar], [], [], List.ofFn (n := n) bodyVar⟩

/-- The selection: take the goal, read the clause, make the body goals. -/
def selection (goal clause : O) (made : List O) : Selection O := ⟨[goal], [clause], made⟩

/-- The rows: the goal's shared row, every clause a stored schema. -/
def rows (goal : O) (goalTerm : Tm (captures (F := F) (arity := arity) (Shared := Shared)))
    (stored : O → ContextualStoredRows.Row (locals (F := F) (arity := arity)) (captures (Shared := Shared)) [] ())
    (o : O) : ContextualStoredRows.Row (locals (F := F) (arity := arity)) (captures (Shared := Shared)) [] () :=
  if o = goal then .shared goalTerm else stored o

/-- The scope of the rule port. -/
def ruleScope (occupied : Finset ℕ) (goal clause : O) (made : List O) : ℕ :=
  ContextualActivationScopes.scopeAt occupied (ContextualActivationScopes.rulePort (selection goal clause made))

/-- **The scope of the read port**: the clause's fresh helpers live here. -/
def readScope (occupied : Finset ℕ) (goal clause : O) (made : List O) : ℕ :=
  ContextualActivationScopes.scopeAt occupied
    (ContextualActivationScopes.readPort (selection goal clause made) ⟨0, Nat.zero_lt_one⟩)

omit [DecidableEq O] in
/-- The read port's scope is outside the occupied ledger. -/
theorem readScope_fresh (occupied : Finset ℕ) (goal clause : O) (made : List O) :
    readScope occupied goal clause made ∉ occupied :=
  ContextualActivationScopes.at_fresh occupied _

omit [DecidableEq O] in
/-- The read port's scope differs from the rule's. -/
theorem readScope_ne_ruleScope (occupied : Finset ℕ) (goal clause : O) (made : List O) :
    readScope occupied goal clause made ≠ ruleScope occupied goal clause made :=
  fun same => ContextualActivationScopes.different_ports_have_different_scopes occupied
    (ContextualActivationScopes.rulePort_ne_readPort (selection goal clause made) ⟨0, Nat.zero_lt_one⟩)
    same.symm

/-- A clause variable opened at a scope. -/
def opened (scope : ℕ) : Assignment (locals (F := F) (arity := arity))
    (target (F := F) (arity := arity) (Shared := Shared)) :=
  ContextualStoredRows.instanceAt locals captures scope

/-- The goal in the target frame. -/
def lifted (goalTerm : Tm (captures (F := F) (arity := arity) (Shared := Shared))) :
    Tm (target (F := F) (arity := arity) (Shared := Shared)) :=
  instantiate (ContextualSelectionViews.capturedTarget locals captures) goalTerm

/-- The rule's variables at the rule scope. -/
def ruleAt (scope : ℕ) (identity : ℕ) : Tm (target (F := F) (arity := arity) (Shared := Shared)) :=
  generator (target (F := F) (arity := arity) (Shared := Shared)) (Sum.inl (ScopedVar.at scope identity))

/-- **The built-in clause opened at a scope**: `Resolution.builtInRule` with the stored clause's head
and body opened there. -/
def builtIn (scope n : ℕ) (head : Tm (locals (F := F) (arity := arity))) (body : Fin n → Tm (locals (F := F) (arity := arity))) :
    RuleInstance (Tm (target (F := F) (arity := arity) (Shared := Shared))) :=
  builtInRule (instantiate (opened scope) head) (List.ofFn fun i => instantiate (opened scope) (body i))

/-! ## The prepared firing -/

section Prepared

variable (occupied : Finset ℕ) (goal clause : O) (made : List O) (n : ℕ)
  (goalTerm : Tm (captures (F := F) (arity := arity) (Shared := Shared)))
  (stored : O → ContextualStoredRows.Row (locals (F := F) (arity := arity)) (captures (Shared := Shared)) [] ())
  (head : Tm (locals (F := F) (arity := arity))) (body : Fin n → Tm (locals (F := F) (arity := arity)))
  (before : Configuration (Tm (captures (F := F) (arity := arity) (Shared := Shared))) O)

/-- The prepared firing. -/
abbrev views :=
  ContextualActivatedStep.prepared locals captures occupied (selection goal clause made) (rule n)
    (rows goal goalTerm stored)

theorem ruleAt_generator (scope : ℕ) (identity : ℕ) :
    ContextualFreshening.termAt locals captures scope
        (generator (source (F := F) (arity := arity) (Shared := Shared)) (Sum.inl identity)) =
      ruleAt scope identity := by
  rw [ContextualFreshening.termAt, instantiate_generator]
  rfl

theorem views_take :
    (views (F := F) (arity := arity) occupied goal clause made n goalTerm stored).rule.take =
      [ruleAt (ruleScope occupied goal clause made) 0] := by
  show [ContextualFreshening.termAt locals captures _ goalVar] = _
  congr 1

theorem views_read :
    (views (F := F) (arity := arity) occupied goal clause made n goalTerm stored).rule.read =
      [clauseTerm n (ruleAt (ruleScope occupied goal clause made) 0)
        fun i => ruleAt (ruleScope occupied goal clause made) (i.val + 1)] := by
  show [instantiate (ContextualFreshening.assignment locals captures _) (clauseTerm n goalVar bodyVar)] = _
  rw [instantiate_clauseTerm]
  congr 2

theorem views_tell :
    (views (F := F) (arity := arity) occupied goal clause made n goalTerm stored).rule.tell = [] := rfl

theorem views_produce :
    (views (F := F) (arity := arity) occupied goal clause made n goalTerm stored).rule.produce =
      List.ofFn fun i : Fin n => ruleAt (ruleScope occupied goal clause made) (i.val + 1) := by
  show (List.ofFn (n := n) bodyVar).map (ContextualFreshening.termAt locals captures _) = _
  rw [List.map_ofFn]
  congr 1

theorem views_taken :
    (views (F := F) (arity := arity) occupied goal clause made n goalTerm stored).taken
        ⟨0, Nat.zero_lt_one⟩ = lifted goalTerm := by
  rw [ContextualActivatedStep.prepared_taken_view]
  show ContextualStoredRows.viewAt locals captures _ (rows goal goalTerm stored goal) = _
  rw [rows, if_pos rfl]
  rfl

theorem views_read_port (distinct : clause ≠ goal)
    (storedClause : stored clause = ContextualStoredRows.store locals captures (clauseTerm n head body)) :
    (views (F := F) (arity := arity) occupied goal clause made n goalTerm stored).read
        ⟨0, Nat.zero_lt_one⟩ =
      clauseTerm n (instantiate (opened (readScope occupied goal clause made)) head)
        fun i => instantiate (opened (readScope occupied goal clause made)) (body i) := by
  rw [ContextualStoredRows.prepared_read_store locals captures occupied (selection goal clause made)
    (rule n) (rows goal goalTerm stored) ⟨0, Nat.zero_lt_one⟩ (clauseTerm n head body)
    (by show rows goal goalTerm stored clause = _; rw [rows, if_neg distinct]; exact storedClause),
    instantiate_clauseTerm]
  rfl

/-- **The information of the read-port firing**: the transported knowledge, the take equation and
the read equation. -/
theorem problem_eq (distinct : clause ≠ goal)
    (storedClause : stored clause = ContextualStoredRows.store locals captures (clauseTerm n head body)) :
    ContextualActivatedStep.problem locals captures occupied (selection goal clause made) (rule n)
        (rows goal goalTerm stored) before =
      (ContextualActivatedStep.frame locals captures before).equations ++
        [(ruleAt (ruleScope occupied goal clause made) 0, lifted goalTerm)] ++
        [(clauseTerm n (ruleAt (ruleScope occupied goal clause made) 0)
            (fun i => ruleAt (ruleScope occupied goal clause made) (i.val + 1)),
          clauseTerm n (instantiate (opened (readScope occupied goal clause made)) head)
            fun i => instantiate (opened (readScope occupied goal clause made)) (body i))] ++ [] := by
  show (ContextualActivatedStep.frame locals captures before).equations ++
      ContextualActivatedStep.useEquations (views occupied goal clause made n goalTerm stored).rule.take
        (List.ofFn (views occupied goal clause made n goalTerm stored).taken) ++
      ContextualActivatedStep.useEquations (views occupied goal clause made n goalTerm stored).rule.read
        (List.ofFn (views occupied goal clause made n goalTerm stored).read) ++
      (views occupied goal clause made n goalTerm stored).rule.tell = _
  have taken : List.ofFn (views (F := F) (arity := arity) occupied goal clause made n goalTerm stored).taken =
      [lifted goalTerm] := by
    rw [← views_taken occupied goal clause made n goalTerm stored]
    rfl
  have read : List.ofFn (views (F := F) (arity := arity) occupied goal clause made n goalTerm stored).read =
      [clauseTerm n (instantiate (opened (readScope occupied goal clause made)) head)
        fun i => instantiate (opened (readScope occupied goal clause made)) (body i)] := by
    rw [← views_read_port occupied goal clause made n goalTerm stored head body distinct storedClause]
    rfl
  rw [taken, read, views_take, views_read, views_tell]
  rfl

end Prepared

/-! ## Admission is unification, the clause present, and freshness -/

/-- **A solution extended to the rule's variables**: at the rule scope, `G` reads `headValue` and
`Bᵢ` reads `bodyValue i`; every other variable is read as before. -/
def extend {Future : Type} {future : Future → MetaArity (logic F arity)} (scope n : ℕ)
    (base : Assignment (target (F := F) (arity := arity) (Shared := Shared)) future)
    (headValue : Tm future) (bodyValue : Fin n → Tm future) :
    Assignment (target (F := F) (arity := arity) (Shared := Shared)) future
  | .inl ⟨activation, name⟩ =>
      if activation = scope then
        if name = 0 then headValue
        else if h : name - 1 < n then bodyValue ⟨name - 1, h⟩ else base (.inl ⟨activation, name⟩)
      else base (.inl ⟨activation, name⟩)
  | .inr shared => base (.inr shared)

section Extend

variable {Future : Type} {future : Future → MetaArity (logic F arity)} (scope n : ℕ)
  (base : Assignment (target (F := F) (arity := arity) (Shared := Shared)) future)
  (headValue : Tm future) (bodyValue : Fin n → Tm future)

theorem extend_lifted (t : Tm (captures (F := F) (arity := arity) (Shared := Shared))) :
    instantiate (extend scope n base headValue bodyValue) (lifted t) = instantiate base (lifted t) := by
  simp only [lifted, instantiate_comp, ContextualSelectionViews.capturedTarget]
  rfl

theorem extend_opened {other : ℕ} (apart : other ≠ scope) (t : Tm (locals (F := F) (arity := arity))) :
    instantiate (extend scope n base headValue bodyValue) (instantiate (opened other) t) =
      instantiate base (instantiate (opened (Shared := Shared) other) t) := by
  simp only [opened, ContextualStoredRows.instanceAt, instantiate_comp]
  congr 1
  funext name
  have here : extend scope n base headValue bodyValue (.inl ⟨other, name⟩) = base (.inl ⟨other, name⟩) := by
    show (if other = scope then _ else base (.inl ⟨other, name⟩)) = base (.inl ⟨other, name⟩)
    rw [if_neg apart]
  exact (instantiate_generator _ _).trans (here.trans (instantiate_generator _ _).symm)

theorem extend_goal : instantiate (extend scope n base headValue bodyValue) (ruleAt scope 0) = headValue := by
  have here : extend scope n base headValue bodyValue (.inl ⟨scope, 0⟩) = headValue := by
    show (if scope = scope then (if (0 : ℕ) = 0 then headValue else _) else _) = headValue
    exact (if_pos rfl).trans (if_pos rfl)
  exact (instantiate_generator _ _).trans here

theorem extend_body (i : Fin n) :
    instantiate (extend scope n base headValue bodyValue) (ruleAt scope (i.val + 1)) = bodyValue i := by
  have here : extend scope n base headValue bodyValue (.inl ⟨scope, i.val + 1⟩) = bodyValue i := by
    show (if scope = scope then (if i.val + 1 = 0 then headValue
        else if h : i.val + 1 - 1 < n then bodyValue ⟨i.val + 1 - 1, h⟩ else _) else _) = bodyValue i
    exact (if_pos rfl).trans ((if_neg (Nat.succ_ne_zero _)).trans (dif_pos (by simp)))
  exact (instantiate_generator _ _).trans here

end Extend

theorem models_pair {Future : Type} {future : Future → MetaArity (logic F arity)}
    (candidate : Assignment (target (F := F) (arity := arity) (Shared := Shared)) future)
    (K : EquationStore (Tm (target (F := F) (arity := arity) (Shared := Shared))))
    (first second : Equation (Tm (target (F := F) (arity := arity) (Shared := Shared)))) :
    ContextualFrameUnifier.Models candidate (K ++ [first] ++ [second] ++ []) ↔
      ContextualFrameUnifier.Models candidate K ∧
        instantiate candidate first.1 = instantiate candidate first.2 ∧
          instantiate candidate second.1 = instantiate candidate second.2 := by
  simp only [ContextualFrameUnifier.models_append, List.append_nil]
  simp [ContextualFrameUnifier.Models, and_assoc]

theorem models_single {Future : Type} {future : Future → MetaArity (logic F arity)}
    (candidate : Assignment (target (F := F) (arity := arity) (Shared := Shared)) future)
    (K : EquationStore (Tm (target (F := F) (arity := arity) (Shared := Shared))))
    (first : Equation (Tm (target (F := F) (arity := arity) (Shared := Shared)))) :
    ContextualFrameUnifier.Models candidate (K ++ [first] ++ [] ++ []) ↔
      ContextualFrameUnifier.Models candidate K ∧
        instantiate candidate first.1 = instantiate candidate first.2 := by
  simp only [ContextualFrameUnifier.models_append, List.append_nil]
  simp [ContextualFrameUnifier.Models]

section Firing

variable (occupied : Finset ℕ) (goal clause : O) (made : List O) (n : ℕ)
  (goalTerm : Tm (captures (F := F) (arity := arity) (Shared := Shared)))
  (stored : O → ContextualStoredRows.Row (locals (F := F) (arity := arity)) (captures (Shared := Shared)) [] ())
  (head : Tm (locals (F := F) (arity := arity))) (body : Fin n → Tm (locals (F := F) (arity := arity)))
  (before : Configuration (Tm (captures (F := F) (arity := arity) (Shared := Shared))) O)
  (goalLabel : O → Tm (target (F := F) (arity := arity) (Shared := Shared)))

omit [DecidableEq O] in
theorem builtIn_problem :
    Selection.problem (builtInSelection goal made) goalLabel
        (builtIn (readScope occupied goal clause made) n head body)
        (ContextualActivatedStep.frame locals captures before) =
      (ContextualActivatedStep.frame locals captures before).equations ++
        [(instantiate (opened (readScope occupied goal clause made)) head, goalLabel goal)] ++ [] ++ [] := by
  rfl

/-- **Every solution of the read-port firing's information solves the built-in firing's.** -/
theorem models_builtIn_of_models (distinct : clause ≠ goal)
    (storedClause : stored clause = ContextualStoredRows.store locals captures (clauseTerm n head body))
    (labelled : goalLabel goal = lifted goalTerm)
    {Future : Type} {future : Future → MetaArity (logic F arity)}
    (candidate : Assignment (target (F := F) (arity := arity) (Shared := Shared)) future)
    (solved : ContextualFrameUnifier.Models candidate (ContextualActivatedStep.problem locals captures
      occupied (selection goal clause made) (rule n) (rows goal goalTerm stored) before)) :
    ContextualFrameUnifier.Models candidate (Selection.problem (builtInSelection goal made) goalLabel
      (builtIn (readScope occupied goal clause made) n head body)
      (ContextualActivatedStep.frame locals captures before)) := by
  rw [problem_eq occupied goal clause made n goalTerm stored head body before distinct storedClause]
    at solved
  rw [builtIn_problem, labelled]
  obtain ⟨frame, take, read⟩ := (models_pair candidate _ _ _).mp solved
  rw [instantiate_clauseTerm, instantiate_clauseTerm] at read
  obtain ⟨heads, -⟩ := clauseTerm_injective read
  exact (models_single candidate _ _).mpr ⟨frame, heads.symm.trans take⟩

/-- **Every solution of the built-in firing's information, extended to the rule's variables, solves
the read-port firing's.** The extension changes no variable outside the rule scope. -/
theorem models_of_models_builtIn (distinct : clause ≠ goal)
    (storedClause : stored clause = ContextualStoredRows.store locals captures (clauseTerm n head body))
    (labelled : goalLabel goal = lifted goalTerm)
    {Future : Type} {future : Future → MetaArity (logic F arity)}
    (candidate : Assignment (target (F := F) (arity := arity) (Shared := Shared)) future)
    (solved : ContextualFrameUnifier.Models candidate (Selection.problem (builtInSelection goal made)
      goalLabel (builtIn (readScope occupied goal clause made) n head body)
      (ContextualActivatedStep.frame locals captures before))) :
    ContextualFrameUnifier.Models
      (extend (ruleScope occupied goal clause made) n candidate
        (instantiate candidate (instantiate (opened (readScope occupied goal clause made)) head))
        fun i => instantiate candidate (instantiate (opened (readScope occupied goal clause made)) (body i)))
      (ContextualActivatedStep.problem locals captures occupied (selection goal clause made) (rule n)
        (rows goal goalTerm stored) before) := by
  rw [builtIn_problem, labelled] at solved
  rw [problem_eq occupied goal clause made n goalTerm stored head body before distinct storedClause]
  obtain ⟨frame, unified⟩ := (models_single candidate _ _).mp solved
  have apart := readScope_ne_ruleScope occupied goal clause made
  let r := ruleScope occupied goal clause made
  let s := readScope occupied goal clause made
  let extended := extend r n candidate (instantiate candidate (instantiate (opened s) head))
    fun i => instantiate candidate (instantiate (opened s) (body i))
  refine (models_pair extended _ _ _).mpr ⟨?_, ?_, ?_⟩
  · intro equation member
    obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
    have kept := frame _ (List.mem_map.mpr ⟨original, ‹_›, rfl⟩)
    exact (extend_lifted r n candidate _ _ original.1).trans
      (kept.trans (extend_lifted r n candidate _ _ original.2).symm)
  · show instantiate extended (ruleAt r 0) = instantiate extended (lifted goalTerm)
    rw [extend_goal, extend_lifted]
    exact unified
  · show instantiate extended (clauseTerm n (ruleAt r 0) fun i => ruleAt r (i.val + 1)) =
      instantiate extended (clauseTerm n (instantiate (opened s) head) fun i => instantiate (opened s) (body i))
    rw [instantiate_clauseTerm, instantiate_clauseTerm, extend_goal, extend_opened r n candidate _ _ apart]
    congr 1
    funext i
    rw [extend_body, extend_opened r n candidate _ _ apart]

/-- The extension agrees with the solution off the rule scope. -/
theorem extend_off_rule {Future : Type} {future : Future → MetaArity (logic F arity)} (scope n : ℕ)
    (base : Assignment (target (F := F) (arity := arity) (Shared := Shared)) future)
    (headValue : Tm future) (bodyValue : Fin n → Tm future) (activation name : ℕ)
    (apart : activation ≠ scope) :
    extend scope n base headValue bodyValue (.inl ⟨activation, name⟩) = base (.inl ⟨activation, name⟩) := by
  show (if activation = scope then _ else _) = _
  rw [if_neg apart]

/-- **The built-in clause is the prepared special case.** The read-port firing's information is
solvable exactly when the information of the raw firing whose rule is the clause opened at the
read scope is solvable on the transported configuration. -/
theorem solvable_iff_builtIn (distinct : clause ≠ goal)
    (storedClause : stored clause = ContextualStoredRows.store locals captures (clauseTerm n head body))
    (labelled : goalLabel goal = lifted goalTerm) :
    ContextualFrameUnifier.Solvable (ContextualActivatedStep.problem locals captures occupied
        (selection goal clause made) (rule n) (rows goal goalTerm stored) before) ↔
      ContextualFrameUnifier.Solvable (Selection.problem (builtInSelection goal made) goalLabel
        (builtIn (readScope occupied goal clause made) n head body)
        (ContextualActivatedStep.frame locals captures before)) := by
  constructor
  · rintro ⟨Future, future, candidate, solved⟩
    exact ⟨Future, future, candidate,
      models_builtIn_of_models occupied goal clause made n goalTerm stored head body before goalLabel
        distinct storedClause labelled candidate solved⟩
  · rintro ⟨Future, future, candidate, solved⟩
    exact ⟨Future, future, _,
      models_of_models_builtIn occupied goal clause made n goalTerm stored head body before goalLabel
        distinct storedClause labelled candidate solved⟩

/-- **Admission is unification, the clause present, and freshness.** The read-port resolution
firing is admitted exactly when the made occurrences are distinct and carry the rule's body ports,
the goal and the clause are present, the made occurrences are fresh, and the transported knowledge
with "opened head = goal" is solvable. The opened head lives at the read scope, which is outside the
occupied ledger and apart from the rule scope (`readScope_fresh`, `readScope_ne_ruleScope`). -/
theorem resolve_valid_iff (distinct : clause ≠ goal)
    (storedClause : stored clause = ContextualStoredRows.store locals captures (clauseTerm n head body))
    (labelled : goalLabel goal = lifted goalTerm)
    (outputLabel : O → Tm (target (F := F) (arity := arity) (Shared := Shared))) :
    ContextualActivatedStep.Valid locals captures occupied (selection goal clause made) (rule n)
        (rows goal goalTerm stored) before outputLabel ↔
      made.Nodup ∧ made.map outputLabel =
          List.ofFn (fun i : Fin n => ruleAt (ruleScope occupied goal clause made) (i.val + 1)) ∧
        goal ∈ before.present ∧ clause ∈ before.present ∧ (∀ x ∈ made, x ∉ before.present) ∧
          ContextualFrameUnifier.Solvable (Selection.problem (builtInSelection goal made) goalLabel
            (builtIn (readScope occupied goal clause made) n head body)
            (ContextualActivatedStep.frame locals captures before)) := by
  have solvable := solvable_iff_builtIn occupied goal clause made n goalTerm stored head body before
    goalLabel distinct storedClause labelled
  have produce := views_produce (F := F) (arity := arity) occupied goal clause made n goalTerm stored
  constructor
  · rintro ⟨-, -, nodup, -, -, outputs, occurrences, solved⟩
    refine ⟨nodup, outputs.trans produce, ?_, ?_, ?_, solvable.mp solved⟩
    · exact occurrences.taken_subset (by simp [selection, Selection.commit])
    · exact occurrences.kept_subset (by simp [selection, Selection.commit])
    · intro x member present
      exact Finset.disjoint_left.mp occurrences.fresh
        (by simpa [selection, Selection.commit] using member) present
  · rintro ⟨nodup, outputs, present, stays, fresh, solved⟩
    refine ⟨rfl, List.nodup_singleton goal, nodup, rfl, rfl, outputs.trans produce.symm,
      ⟨?_, ?_, ?_, ?_, ?_⟩, solvable.mpr solved⟩
    · intro x member
      have same : x = goal := by simpa [selection, Selection.commit] using member
      rw [same]
      exact present
    · intro x member
      have same : x = clause := by simpa [selection, Selection.commit] using member
      rw [same]
      exact stays
    · simpa [selection, Selection.commit] using distinct.symm
    · exact Finset.disjoint_left.mpr fun {x} member inPresent =>
        fresh x (by simpa [selection, Selection.commit] using member) inPresent
    · intro query member
      simp [selection, Selection.commit] at member

/-! ## The result is the resolvent with the clause still present -/

/-- **The goal is replaced by the body goals; every other occurrence survives.** -/
theorem resolve_result_present :
    (ContextualActivatedStep.result locals captures occupied (selection goal clause made) (rule n)
        (rows goal goalTerm stored) before).present = (before.present \ {goal}) ∪ made.toFinset := by
  simp [ContextualActivatedStep.result, fire, Selection.commit, selection]

/-- **The clause occurrence is still present**: the read leaves it in place. -/
theorem resolve_clause_stays (outputLabel : O → Tm (target (F := F) (arity := arity) (Shared := Shared)))
    (valid : ContextualActivatedStep.Valid locals captures occupied (selection goal clause made) (rule n)
      (rows goal goalTerm stored) before outputLabel) :
    clause ∈ (ContextualActivatedStep.result locals captures occupied (selection goal clause made) (rule n)
      (rows goal goalTerm stored) before).present :=
  ContextualActivatedStep.Valid.kept_survive locals captures valid
    (show clause ∈ [clause] from List.mem_singleton_self clause)

/-- **The clause row is still the same stored schema**, unspecialized by the firing's knowledge. -/
theorem resolve_clause_row (distinct : clause ≠ goal)
    (storedClause : stored clause = ContextualStoredRows.store locals captures (clauseTerm n head body))
    (outputLabel : O → Tm (target (F := F) (arity := arity) (Shared := Shared)))
    (valid : ContextualActivatedStep.Valid locals captures occupied (selection goal clause made) (rule n)
      (rows goal goalTerm stored) before outputLabel) :
    ContextualActivatedStep.resultRows locals captures (selection goal clause made) outputLabel
        (rows goal goalTerm stored) clause =
      ContextualStoredRows.store locals (target (F := F) (arity := arity) (Shared := Shared))
        (clauseTerm n head body) := by
  have present : clause ∈ before.present := valid.occurrences.kept_subset (by simp [selection, Selection.commit])
  have notMade : clause ∉ made := fun member => Finset.disjoint_left.mp valid.occurrences.fresh
    (by simpa [selection, Selection.commit] using member) present
  have notMade' : clause ∉ (selection goal clause made).made := notMade
  show (if clause ∈ (selection goal clause made).made then _ else _) = _
  rw [if_neg notMade', rows, if_neg distinct, storedClause, ContextualStoredRows.map_store]

/-- The result's knowledge is the firing's information. -/
theorem resolve_result_equations :
    (ContextualActivatedStep.result locals captures occupied (selection goal clause made) (rule n)
        (rows goal goalTerm stored) before).equations =
      ContextualActivatedStep.problem locals captures occupied (selection goal clause made) (rule n)
        (rows goal goalTerm stored) before := rfl

end Firing

omit [DecidableEq O] in
/-- **Two reads of one clause never share helpers**: the read scope of a later firing lies outside
every scope the earlier firing reserved, its own read scope among them. -/
theorem two_reads_apart (occupied : Finset ℕ) (goal clause : O) (made : List O)
    (goal' clause' : O) (made' : List O) :
    readScope (ContextualActivationScopes.after occupied (selection goal clause made)) goal' clause' made' ≠
      readScope occupied goal clause made := by
  intro same
  have outside := readScope_fresh (ContextualActivationScopes.after occupied (selection goal clause made))
    goal' clause' made'
  rw [same] at outside
  exact outside (Finset.mem_union_right _ (ContextualActivationScopes.at_mem_reserved occupied _ _))

#print axioms extend_lifted
#print axioms extend_opened
#print axioms extend_goal
#print axioms extend_body
#print axioms problem_eq
#print axioms builtIn_problem
#print axioms models_builtIn_of_models
#print axioms models_of_models_builtIn
#print axioms extend_off_rule
#print axioms solvable_iff_builtIn
#print axioms resolve_valid_iff
#print axioms resolve_result_present
#print axioms resolve_clause_stays
#print axioms resolve_clause_row
#print axioms resolve_result_equations
#print axioms two_reads_apart
#print axioms instantiateArgs_argsOf
#print axioms argsOf_injective
#print axioms instantiate_clauseTerm
#print axioms clauseTerm_injective
#print axioms readScope_fresh
#print axioms readScope_ne_ruleScope

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Resolution.ReadPort
