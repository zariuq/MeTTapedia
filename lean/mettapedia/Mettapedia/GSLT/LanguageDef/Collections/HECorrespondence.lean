import Mettapedia.GSLT.LanguageDef.Collections.Evaluation
import Mettapedia.Languages.MeTTa.HE.Eval

/-!
# HE's result rule against HE's interpreter

`Dialect.he` models the rule of the HE interpreter on calls: bindings are
substituted, a result whose declared type is `Atom` is returned as written,
and every other result is evaluated again. This module compares that rule
with HE's executable interpreter model (`Languages.MeTTa.HE.evalAtom`) on the
call fragment.

* **Evaluated again means evaluated once more, not twice.** HE's interpreter
  returns the raw result of a call, the substituted right-hand side or a
  native's output, as written at `Atom` (`he_atom_demand`) and otherwise
  evaluates it once at the declared type
  (`Languages.MeTTa.HE.ordinaryCallReturn_evaluate`). The value of that
  evaluation is the call's result; it is not evaluated a second time.
* **A counterexample to evaluating twice.** With `(: mk (-> Atom))`,
  `(= (mk) (h))`, `(= (h) 5)` and `(= (w) (mk))`, HE's interpreter answers
  `(h)` for `(w)` (`he_w`), as the hyperon-experimental interpreter does. The
  reading that evaluates the body of `w` and then that body's value again
  answers `5` (`twice_w`). The model's rule evaluates the substituted body
  once (`Evaluation.Returning.once`), and the model answers `(h)` and nothing
  else (`model_w`).
* **The model's rule is substitution followed by one evaluation.** Under the
  substituting binding rule, evaluating a term of the first-order call
  fragment in an environment of normal values is evaluating its instance
  (`eval_inst`); so the model's `once` evaluates the reduct of the call, as
  HE's interpreter does (`return_once_iff_inst`).
* **Native outputs.** HE's interpreter evaluates a native's output once at a
  declared type other than `Atom` and keeps it at `Atom` (`he_first`,
  `he_first_atom`); the model's output rule for HE does the same
  (`model_first`), while PeTTa's keeps the output (`petta_first`).
* **The probe table.** HE's interpreter reproduces the HE column of
  `EvaluationControls` at every budget of at least seventeen
  (`HECorrespondenceProbes`, `he_probe_table`).

HE's interpreter is fuel-indexed. Each HE-side theorem holds at every budget
from a stated one on, with the budget a variable of the proof: the
counterexample answers `(h)` at every budget of at least eleven, and otherwise
at ten (`he_w`, `he_w_least`). Below its first budget a run is cut short and
can answer something else, so one sampled budget would not settle an answer.
This is a comparison on the call fragment with `Atom` and undefined result
types, not an adequacy theorem for the whole HE language.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.HECorrespondence

open Mettapedia.Logic.Unification
open Mettapedia.Logic.Unification.ListSplice (Term splice splice_list splice_rest normalize_idempotent)
open Evaluation

/-! ## Substituting, then evaluating once -/

section Substitution

variable {Symbol Var : Type} [DecidableEq Symbol] [DecidableEq Var]

/-- The first-order call fragment: symbols, variables, list literals with a
prefix, and expressions headed by a symbol whose arguments are in the
fragment. -/
inductive CallTerm : Tm Symbol Var → Prop
  | symbol (a : Symbol) : CallTerm (.atom (.sym a))
  | var (x : Var) : CallTerm (.var x)
  | list (xs : List (Tm Symbol Var)) : CallTerm (.list xs)
  | rest (x : Tm Symbol Var) (xs : List (Tm Symbol Var)) (tail : Tm Symbol Var) :
      CallTerm (.rest (x :: xs) tail)
  | apply (f : Symbol) (args : List (Tm Symbol Var)) :
      (∀ arg ∈ args, CallTerm arg) → CallTerm (.expr (.atom (.sym f) :: args))

/-- An environment whose values are in splice normal form. -/
def NormalEnv (σ : Env Symbol Var) : Prop := ∀ x, ListSplice.normalize (σ x) = σ x

omit [DecidableEq Symbol] [DecidableEq Var] in
theorem subst_var_id : ∀ t : Tm Symbol Var, ListSplice.subst Term.var t = t
  | .atom _ => by rw [ListSplice.subst]
  | .var _ => by rw [ListSplice.subst]
  | .expr xs => by
      simp only [ListSplice.subst]
      congr 1
      conv_rhs => rw [← List.map_id xs]
      exact List.map_congr_left fun t _ => subst_var_id t
  | .list xs => by
      simp only [ListSplice.subst]
      congr 1
      conv_rhs => rw [← List.map_id xs]
      exact List.map_congr_left fun t _ => subst_var_id t
  | .rest xs tail => by
      simp only [ListSplice.subst, subst_var_id tail]
      congr 1
      conv_rhs => rw [← List.map_id xs]
      exact List.map_congr_left fun t _ => subst_var_id t

omit [DecidableEq Symbol] [DecidableEq Var] in
/-- Instances are normal forms. -/
theorem inst_inst (σ : Env Symbol Var) (t : Tm Symbol Var) : inst Term.var (inst σ t) = inst σ t := by
  simp only [inst, subst_var_id, normalize_idempotent]

omit [DecidableEq Symbol] [DecidableEq Var] in
theorem inst_atom (σ : Env Symbol Var) (a : Leaf Symbol) : inst σ (.atom a : Tm Symbol Var) = .atom a := by
  simp only [inst, ListSplice.subst, ListSplice.normalize]

omit [DecidableEq Symbol] [DecidableEq Var] in
theorem inst_expr (σ : Env Symbol Var) (xs : List (Tm Symbol Var)) :
    inst σ (.expr xs) = .expr (xs.map (inst σ)) := by
  simp [inst, ListSplice.normalize, ListSplice.subst, List.map_map, Function.comp_def]

variable {P : Program Symbol Var}

/-- A free variable evaluates to itself under the substituting rule. -/
theorem eval_var_free (code : P.lookup = .code) {θ : Env Symbol Var} {x : Var} (free : θ x = .var x)
    (v : Tm Symbol Var) : Eval P θ (.var x) v ↔ v = .var x := by
  constructor
  · intro h
    cases h with
    | variableData data => rw [code] at data; cases data
    | variableFree => rfl
    | variableCode _ bound _ => exact (bound free).elim
  · rintro rfl
    exact .variableFree free

/-- A list value evaluates to itself. -/
theorem eval_listValue {u : Tm Symbol Var} (shape : (∃ xs, u = .list xs) ∨ ∃ xs tail, u = .rest xs tail)
    (normal : inst Term.var u = u) (v : Tm Symbol Var) : Eval P Term.var u v ↔ v = u := by
  rcases shape with ⟨xs, rfl⟩ | ⟨xs, tail, rfl⟩
  · rw [eval_list_iff, normal]
  · rw [eval_rest_iff, normal]

omit [DecidableEq Symbol] [DecidableEq Var] in
/-- A list literal with a prefix normalizes to a list value. -/
theorem inst_rest_shape (σ : Env Symbol Var) (x : Tm Symbol Var) (xs : List (Tm Symbol Var))
    (tail : Tm Symbol Var) :
    (∃ ys, inst σ (.rest (x :: xs) tail) = .list ys) ∨
      ∃ ys rest, inst σ (.rest (x :: xs) tail) = .rest ys rest := by
  simp only [inst, ListSplice.subst, ListSplice.normalize, List.map_cons]
  generalize ListSplice.normalize (ListSplice.subst σ tail) = end_
  cases end_ with
  | list ys => exact Or.inl ⟨_, splice_list _ _⟩
  | rest ys r => exact Or.inr ⟨_, _, splice_rest _ _ _⟩
  | var v => exact Or.inr ⟨_, _, rfl⟩
  | atom a => exact Or.inr ⟨_, _, rfl⟩
  | expr ys => exact Or.inr ⟨_, _, rfl⟩

theorem evalAll_inst (σ : Env Symbol Var) :
    ∀ (args : List (Tm Symbol Var)),
      (∀ arg ∈ args, ∀ v, Eval P σ arg v ↔ Eval P Term.var (inst σ arg) v) →
      ∀ vs, EvalAll P σ args vs ↔ EvalAll P Term.var (args.map (inst σ)) vs
  | [], _, vs => by
      constructor <;> intro h <;> cases h <;> exact .nil
  | arg :: args, each, vs => by
      have rest := evalAll_inst σ args (fun a member => each a (List.mem_cons_of_mem _ member))
      constructor
      · intro h
        cases h with
        | cons first later =>
            exact .cons ((each arg List.mem_cons_self _).mp first) ((rest _).mp later)
      · intro h
        cases h with
        | cons first later =>
            exact .cons ((each arg List.mem_cons_self _).mpr first) ((rest _).mpr later)

theorem receive_inst (σ : Env Symbol Var) :
    ∀ (modes : List Passing) (args : List (Tm Symbol Var)),
      (∀ arg ∈ args, ∀ v, Eval P σ arg v ↔ Eval P Term.var (inst σ arg) v) →
      ∀ received, Receive P σ modes args received ↔ Receive P Term.var modes (args.map (inst σ)) received
  | [], [], _, received => by
      constructor <;> intro h <;> cases h <;> exact .nil
  | [], _ :: _, _, received => by
      constructor <;> intro h <;> cases h
  | _ :: _, [], _, received => by
      constructor <;> intro h <;> cases h
  | mode :: modes, arg :: args, each, received => by
      have rest := receive_inst σ modes args (fun a member => each a (List.mem_cons_of_mem _ member))
      constructor
      · intro h
        cases h with
        | data later =>
            have step := Receive.data (P := P) (θ := Term.var) (x := inst σ arg) ((rest _).mp later)
            rwa [inst_inst] at step
        | evaluated first later =>
            exact .evaluated ((each arg List.mem_cons_self _).mp first) ((rest _).mp later)
      · intro h
        cases h with
        | @data _ _ _ _ ys later =>
            have step := Receive.data (P := P) (θ := σ) (x := arg) ((rest _).mpr later)
            rwa [← inst_inst σ arg] at step
        | evaluated first later =>
            exact .evaluated ((each arg List.mem_cons_self _).mpr first) ((rest _).mpr later)

/-- **Substitution, then evaluation.** Under the substituting binding rule, a
term of the first-order call fragment evaluates in an environment of normal
values exactly as its instance evaluates. -/
theorem eval_inst (code : P.lookup = .code) (σ : Env Symbol Var) (normalEnv : NormalEnv σ) :
    ∀ t : Tm Symbol Var, CallTerm t → ∀ v, Eval P σ t v ↔ Eval P Term.var (inst σ t) v := by
  intro t call
  induction call with
  | symbol a =>
      intro v
      rw [inst_atom σ (.sym a), eval_sym_iff, eval_sym_iff]
  | var x =>
      intro v
      have image : inst σ (.var x : Tm Symbol Var) = σ x := by
        simp only [inst, ListSplice.subst, normalEnv x]
      rw [image]
      by_cases free : σ x = .var x
      · rw [eval_var_free code free, free, eval_var_free code rfl]
      · exact eval_var_code_iff code x free v
  | list xs =>
      intro v
      rw [eval_list_iff, eval_listValue (Or.inl ⟨xs.map (inst σ), inst_list xs⟩) (inst_inst σ _)]
  | rest x xs tail =>
      intro v
      rw [eval_rest_iff]
      rcases inst_rest_shape σ x xs tail with ⟨ys, same⟩ | ⟨ys, r, same⟩
      · rw [eval_listValue (Or.inl ⟨ys, same⟩) (inst_inst σ _)]
      · rw [eval_listValue (Or.inr ⟨ys, r, same⟩) (inst_inst σ _)]
  | apply f args _ each =>
      intro v
      rw [inst_expr, List.map_cons, inst_atom σ (.sym f),
        eval_call_iff, eval_call_iff]
      have head : ∀ a ∈ (.atom (.sym f) :: args : List (Tm Symbol Var)), ∀ w,
          Eval P σ a w ↔ Eval P Term.var (inst σ a) w := by
        intro a member w
        rcases List.mem_cons.mp member with rfl | later
        · rw [inst_atom σ (.sym f), eval_sym_iff, eval_sym_iff]
        · exact each a later w
      have all := evalAll_inst σ _ head
      simp only [List.map_cons, inst_atom σ (.sym f)] at all
      have receives := fun modes => receive_inst (P := P) σ modes args each
      constructor
      · rintro (⟨none_, vs, evaluated, rfl⟩ | ⟨modes, received, passing, receive, called⟩)
        · exact Or.inl ⟨none_, vs, (all vs).mp evaluated, rfl⟩
        · exact Or.inr ⟨modes, received, passing, (receives modes received).mp receive, called⟩
      · rintro (⟨none_, vs, evaluated, rfl⟩ | ⟨modes, received, passing, receive, called⟩)
        · exact Or.inl ⟨none_, vs, (all vs).mpr evaluated, rfl⟩
        · exact Or.inr ⟨modes, received, passing, (receives modes received).mpr receive, called⟩

/-- **The model's `once` is HE's single evaluation of the reduct**: under the
substituting rule, the result of a call whose body is in the call fragment is
the value of the substituted body. -/
theorem return_once_iff_inst (code : P.lookup = .code) (σ : Env Symbol Var) (normalEnv : NormalEnv σ)
    (body : Tm Symbol Var) (call : CallTerm body) (result : Tm Symbol Var) :
    Return P .once σ body result ↔ Eval P Term.var (inst σ body) result :=
  (return_once_iff σ body result).trans (eval_inst code σ normalEnv body call result)

end Substitution

/-! ## HE's interpreter returns an `Atom` demand as written -/

section HE

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-- At the demand `Atom`, HE's interpreter returns its input as written. -/
theorem he_atom_demand (space : Space) (dispatch : GroundedDispatch) (atom : Atom) (bindings : Bindings)
    (fuel : ℕ) (live : List Atom) :
    evalAtom space dispatch atom Atom.atomType bindings (fuel + 1) live = [(atom, bindings)] := by
  simp only [evalAtom]
  split <;> simp

end HE

/-! ## The counterexample, both sides -/

namespace Counterexample

/-- The symbols of the counterexample. -/
inductive Sym where
  | h | mk | w | five | p | q | a | b | first | firstData
  deriving DecidableEq, Repr

abbrev T := Tm Sym ℕ
abbrev s (x : Sym) : T := .atom (.sym x)
abbrev call (g : Sym) (args : List T) : T := .expr (s g :: args)

def passingOf : Sym → Option (List Passing)
  | .h | .mk | .w => some []
  | .p | .first | .firstData => some [.data]
  | .q => some [.evaluated]
  | _ => none

/-- `mk`, `p` and `first-data` are declared with result type `Atom`. -/
def resultTypeOf : Sym → ResultType
  | .mk | .p | .firstData => .data
  | _ => .undefined

/-- `(= (h) 5)`, `(= (mk) (h))`, `(= (w) (mk))`, `(= (p $x) (h))`,
`(= (q $x) (p $x))`. -/
def ruleOf : Sym → List T → Env Sym ℕ → T → Prop
  | .h, received, σ, rhs => received = [] ∧ σ = Term.var ∧ rhs = s .five
  | .mk, received, σ, rhs => received = [] ∧ σ = Term.var ∧ rhs = call .h []
  | .w, received, σ, rhs => received = [] ∧ σ = Term.var ∧ rhs = call .mk []
  | .p, received, σ, rhs => ∃ v, received = [v] ∧ σ = Program.bindOne Term.var 0 v ∧ rhs = call .h []
  | .q, received, σ, rhs => ∃ v, received = [v] ∧ σ = Program.bindOne Term.var 0 v ∧ rhs = call .p [.var 0]
  | _, _, _, _ => False

/-- `first` and `first-data` read the first element of an expression. -/
def nativeOf : Sym → List T → T → Prop
  | .first, received, value | .firstData, received, value => ∃ rest, received = [.expr (value :: rest)]
  | _, _, _ => False

def program (D : Dialect) : Program Sym ℕ where
  lookup := D.lookup
  stored := []
  passing := passingOf
  native := nativeOf
  rule := ruleOf
  returning g := D.returning (resultTypeOf g)
  nativeReturning g := D.nativeReturning (resultTypeOf g)

theorem inst_s (θ : Env Sym ℕ) (x : Sym) : inst θ (s x) = s x := inst_atom θ (.sym x)

theorem inst_call_nil (θ : Env Sym ℕ) (g : Sym) : inst θ (call g []) = call g [] := by
  rw [inst_expr]
  simp [inst_s]

theorem eval_s (D : Dialect) (θ : Env Sym ℕ) (x : Sym) (none_ : passingOf x = none) (v : T) :
    Eval (program D) θ (s x) v ↔ v = s x :=
  (eval_sym_iff x v).trans ⟨fun h => h.2, fun h => ⟨none_, h⟩⟩

/-- A call of a function without parameters or natives is its body under the
result rule. -/
theorem eval_nullary_iff (D : Dialect) (θ : Env Sym ℕ) (g : Sym) (body : T)
    (passes : passingOf g = some [])
    (rules : ∀ received σ rhs, ruleOf g received σ rhs ↔ received = [] ∧ σ = Term.var ∧ rhs = body)
    (noNative : ∀ received value, ¬ nativeOf g received value) (v : T) :
    Eval (program D) θ (call g []) v ↔ Return (program D) (D.returning (resultTypeOf g)) Term.var body v := by
  rw [eval_call_iff]
  constructor
  · rintro (⟨none_, -⟩ | ⟨modes, received, passing, receives, ⟨value, computed, -⟩ | ⟨σ, rhs, rule, returned⟩⟩)
    · change passingOf g = none at none_
      rw [passes] at none_
      cases none_
    · exact (noNative _ _ computed).elim
    · change passingOf g = some modes at passing
      rw [passes] at passing
      cases passing
      cases receives
      obtain ⟨-, rfl, rfl⟩ := (rules _ _ _).mp rule
      exact returned
  · intro returned
    exact Or.inr ⟨[], [], passes, .nil, Or.inr ⟨Term.var, body, (rules _ _ _).mpr ⟨rfl, rfl, rfl⟩, returned⟩⟩

/-- `(h)` is `5` under every rule considered. -/
theorem eval_h (D : Dialect) (θ : Env Sym ℕ) (undefinedRule : D.returning .undefined = .once) (v : T) :
    Eval (program D) θ (call .h []) v ↔ v = s .five := by
  rw [eval_nullary_iff D θ .h (s .five) rfl (fun _ _ _ => by simp [ruleOf]) (fun _ _ h => h)]
  change Return _ (D.returning .undefined) _ _ _ ↔ _
  rw [undefinedRule, return_once_iff]
  exact eval_s D _ .five rfl v

/-- HE returns the body of `mk`, declared `Atom`, as written. -/
theorem eval_mk_he (θ : Env Sym ℕ) (v : T) : Eval (program .he) θ (call .mk []) v ↔ v = call .h [] := by
  rw [eval_nullary_iff .he θ .mk (call .h []) rfl (fun _ _ _ => by simp [ruleOf]) (fun _ _ h => h)]
  change Return _ .asWritten _ _ _ ↔ _
  rw [return_asWritten_iff, inst_call_nil]

/-- **The model answers `(h)` for `(w)` under HE's rule, and nothing else.** -/
theorem model_w (v : T) : Eval (program .he) Term.var (call .w []) v ↔ v = call .h [] := by
  rw [eval_nullary_iff .he Term.var .w (call .mk []) rfl (fun _ _ _ => by simp [ruleOf]) (fun _ _ h => h)]
  change Return _ .once _ _ _ ↔ _
  rw [return_once_iff]
  exact eval_mk_he Term.var v

/-- **Evaluating the body and then its value again answers `5`.** -/
theorem twice_w (v : T) :
    (∃ u, Eval (program .he) Term.var (call .mk []) u ∧ Eval (program .he) Term.var u v) ↔ v = s .five := by
  constructor
  · rintro ⟨u, first, second⟩
    rw [eval_mk_he] at first
    subst first
    exact (eval_h .he Term.var rfl v).mp second
  · rintro rfl
    exact ⟨call .h [], (eval_mk_he _ _).mpr rfl, (eval_h .he _ rfl _).mpr rfl⟩

/-- The two readings differ. -/
theorem once_ne_twice : (call .h [] : T) ≠ s .five := by
  intro same
  cases same

/-- The candidate rule, which runs every body, answers `5`. -/
theorem candidate_w (v : T) : Eval (program .primeCandidate) Term.var (call .w []) v ↔ v = s .five := by
  rw [eval_nullary_iff .primeCandidate Term.var .w (call .mk []) rfl (fun _ _ _ => by simp [ruleOf])
    (fun _ _ h => h)]
  change Return _ .once _ _ _ ↔ _
  rw [return_once_iff, eval_nullary_iff .primeCandidate Term.var .mk (call .h []) rfl
    (fun _ _ _ => by simp [ruleOf]) (fun _ _ h => h)]
  change Return _ .once _ _ _ ↔ _
  rw [return_once_iff]
  exact eval_h .primeCandidate Term.var rfl v

theorem receive_data_single (D : Dialect) (θ : Env Sym ℕ) (x : T) (received : List T) :
    Receive (program D) θ [.data] [x] received ↔ received = [inst θ x] := receive_data_iff x received

/-- With a data parameter, `q` passes `$x` to `p`, whose `Atom` result `(h)` is
returned as written: `(q a)` answers `(h)`. -/
theorem model_q (v : T) : Eval (program .he) Term.var (call .q [s .a]) v ↔ v = call .h [] := by
  have pCall : ∀ (θ : Env Sym ℕ) (arg : T) (w : T),
      Eval (program .he) θ (call .p [arg]) w ↔ w = call .h [] := by
    intro θ arg w
    rw [eval_call_iff]
    constructor
    · rintro (⟨none_, -⟩ | ⟨modes, received, passing, receives, ⟨value, computed, -⟩ | ⟨σ, rhs, rule, returned⟩⟩)
      · cases none_
      · exact computed.elim
      · change passingOf .p = some modes at passing
        cases passing
        obtain ⟨v', -, rfl, rfl⟩ := rule
        change Return _ .asWritten _ _ _ at returned
        rw [return_asWritten_iff, inst_call_nil] at returned
        exact returned
    · rintro rfl
      refine Or.inr ⟨[.data], [inst θ arg], rfl, (receive_data_iff _ _).mpr rfl,
        Or.inr ⟨Program.bindOne Term.var 0 (inst θ arg), call .h [], ⟨_, rfl, rfl, rfl⟩, ?_⟩⟩
      change Return _ .asWritten _ _ _
      rw [return_asWritten_iff, inst_call_nil]
  rw [eval_call_iff]
  constructor
  · rintro (⟨none_, -⟩ | ⟨modes, received, passing, receives, ⟨value, computed, -⟩ | ⟨σ, rhs, rule, returned⟩⟩)
    · cases none_
    · exact computed.elim
    · change passingOf .q = some modes at passing
      cases passing
      obtain ⟨v', -, rfl, rfl⟩ := rule
      change Return _ .once _ _ _ at returned
      exact (pCall _ _ v).mp ((return_once_iff _ _ _).mp returned)
  · rintro rfl
    refine Or.inr ⟨[.evaluated], [s .a], rfl, .evaluated ((eval_s _ _ .a rfl _).mpr rfl) .nil,
      Or.inr ⟨Program.bindOne Term.var 0 (s .a), call .p [.var 0], ⟨_, rfl, rfl, rfl⟩, ?_⟩⟩
    change Return _ .once _ _ _
    exact .once ((pCall _ _ _).mpr rfl)

/-- A native reading the first element of `((h) b)`: its output `(h)`, then the
output rule. -/
theorem eval_first (D : Dialect) (g : Sym) (native : g = .first ∨ g = .firstData) (v : T) :
    Eval (program D) Term.var (call g [.expr [call .h [], s .b]]) v ↔
      Output (program D) (D.nativeReturning (resultTypeOf g)) (call .h []) v := by
  have inputs : inst Term.var (.expr [call .h [], s .b] : T) = .expr [call .h [], s .b] := by
    rw [inst_expr]
    simp [inst_call_nil, inst_s]
  rw [eval_call_iff]
  constructor
  · rintro (⟨none_, -⟩ | ⟨modes, received, passing, receives, ⟨value, computed, delivered⟩ | ⟨σ, rhs, rule, -⟩⟩)
    · rcases native with rfl | rfl <;> cases none_
    · rcases native with rfl | rfl <;>
      · cases passing
        rw [receive_data_iff, inputs] at receives
        subst receives
        obtain ⟨rest, same⟩ := computed
        simp only [List.cons.injEq, Term.expr.injEq, and_true] at same
        rw [same.1]
        exact delivered
    · rcases native with rfl | rfl <;> exact rule.elim
  · intro delivered
    refine Or.inr ⟨[.data], [.expr [call .h [], s .b]], ?_, by rw [receive_data_iff, inputs], Or.inl
      ⟨call .h [], ?_, delivered⟩⟩
    · rcases native with rfl | rfl <;> rfl
    · rcases native with rfl | rfl <;> exact ⟨[s .b], rfl⟩

/-- **HE runs a native's output** at a result type other than `Atom`. -/
theorem model_first (v : T) :
    Eval (program .he) Term.var (call .first [.expr [call .h [], s .b]]) v ↔ v = s .five := by
  rw [eval_first .he .first (Or.inl rfl)]
  change Output _ .once _ _ ↔ _
  rw [output_once_iff]
  exact eval_h .he Term.var rfl v

/-- At `Atom` the output is kept. -/
theorem model_firstData (v : T) :
    Eval (program .he) Term.var (call .firstData [.expr [call .h [], s .b]]) v ↔ v = call .h [] := by
  rw [eval_first .he .firstData (Or.inr rfl)]
  exact output_asWritten_iff _ _

/-- PeTTa keeps a native's output as data. -/
theorem petta_first (v : T) :
    Eval (program .petta) Term.var (call .first [.expr [call .h [], s .b]]) v ↔ v = call .h [] := by
  rw [eval_first .petta .first (Or.inl rfl)]
  exact output_asWritten_iff _ _

end Counterexample

/-! ## HE's interpreter on the counterexample and the probe table -/

namespace Interpreter

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

def symbol (name : String) : Atom := .symbol name
def apply (f : String) (args : List Atom) : Atom := .expression (symbol f :: args)
def equation (lhs rhs : Atom) : Atom := .expression [symbol "=", lhs, rhs]
def typed (f : String) (type_ : Atom) : Atom := .expression [symbol ":", symbol f, type_]
def arrow (types : List Atom) : Atom := .expression (symbol "->" :: types)

/-- The counterexample as an HE space: `(: mk (-> Atom))`, `(= (mk) (h))`,
`(= (h) 5)`, `(= (w) (mk))`, `(: p (-> Atom Atom))`, `(= (p $x) (h))`,
`(= (q $x) (p $x))`, `(: first (-> Expression %Undefined%))` and
`(: first-data (-> Expression Atom))`. -/
def space : Space := Space.ofList [
  typed "mk" (arrow [Atom.atomType]),
  equation (apply "mk" []) (apply "h" []),
  equation (apply "h" []) (symbol "5"),
  equation (apply "w" []) (apply "mk" []),
  typed "p" (arrow [Atom.atomType, Atom.atomType]),
  equation (apply "p" [.var "x"]) (apply "h" []),
  equation (apply "q" [.var "x"]) (apply "p" [.var "x"]),
  typed "first" (arrow [symbol "Expression", Atom.undefinedType]),
  typed "first-data" (arrow [symbol "Expression", Atom.atomType])]

/-- The natives `first` and `first-data`: the first element of an expression. -/
def dispatch : GroundedDispatch where
  isExecutable operator := operator == symbol "first" || operator == symbol "first-data"
  execute
    | _, [.expression (head :: _)] => .ok [(head, Bindings.empty)]
    | _, _ => .incorrectArgument

/-- HE's answers for an atom at budget `fuel`. -/
def answers (atom : Atom) (fuel : ℕ) : List Atom :=
  (evalAtom space dispatch atom Atom.undefinedType Bindings.empty fuel).map Prod.fst

set_option maxHeartbeats 4000000 in
/-- **HE's interpreter answers `(h)` for `(w)`**, not `5`, at every budget of
at least eleven. The budget is a variable of the proof, not a sampled value. -/
theorem he_w (fuel : ℕ) (enough : 11 ≤ fuel) : answers (apply "w" []) fuel = [apply "h" []] := by
  obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 11 := ⟨fuel - 11, by omega⟩
  cbv

set_option maxRecDepth 100000 in
/-- Eleven is the least such budget: at ten the run is cut short and answers
otherwise. -/
theorem he_w_least : answers (apply "w" []) 10 ≠ [apply "h" []] := by decide

set_option maxHeartbeats 4000000 in
theorem he_q (fuel : ℕ) (enough : 12 ≤ fuel) : answers (apply "q" [symbol "a"]) fuel = [apply "h" []] := by
  obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 12 := ⟨fuel - 12, by omega⟩
  cbv

set_option maxHeartbeats 4000000 in
/-- **HE's interpreter runs a native's output** at `%Undefined%`, and keeps it
at `Atom`, at every budget of at least nine. -/
theorem he_first (fuel : ℕ) (enough : 9 ≤ fuel) :
    answers (apply "first" [.expression [apply "h" [], symbol "b"]]) fuel = [symbol "5"] := by
  obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 9 := ⟨fuel - 9, by omega⟩
  cbv

set_option maxHeartbeats 4000000 in
theorem he_first_atom (fuel : ℕ) (enough : 9 ≤ fuel) :
    answers (apply "first-data" [.expression [apply "h" [], symbol "b"]]) fuel = [apply "h" []] := by
  obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 9 := ⟨fuel - 9, by omega⟩
  cbv

end Interpreter

end Mettapedia.GSLT.LanguageDef.Collections.HECorrespondence
