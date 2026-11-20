import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.Evaluation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RulesAsRows.Codes

/-!
# The function in the frame's equality: matching becomes matching modulo that equality

A frame action may contain a function's equations in its equality: a **call term** `call f t̄` is equal
to the value of the function at its arguments (`ComputingCall.graph_equal`), substitution goes inside the
call (`ComputingCall.apply_call`), and equal arguments give equal calls (`ComputingCall.congr`). The rule
then tells `r ≐ call f t̄` and the solver computes (the code algebra of `RulesAsRows.Codes` is such an
equality, with instantiation as the function; the dependent frames of `Step` contain conversion).

* `tell_iff_value`: **where every solution determines the arguments, the tell of the call is the tell of
  the value**: a solution solves `r ≐ call f t̄` exactly when it solves `r ≐ v`, `v` the value at the
  determined arguments. So the reading agrees, solution for solution, with the evaluation of
  `Evaluation` (which tells the value and asks the arguments).
* **Matching is then matching modulo the equality** (`take_of_call_admitted`,
  `take_of_call_refused_syntactically`): the equality acts on every equation of the information, matching
  included. A rule that **takes** the call term `call f ā` is admitted at a store whose row is the value
  `v` (it fires on its own normal form, the phenomenon
  `Interface.ComputationProfile.SemanticMatch.semantic_rule_can_fire_on_syntactic_normal_form` shows on the
  dependent frames); with syntactic equality the same rule, at the same store, is refused. This is what
  the frame's equality means, a different matching and not an error of it: the two readings have
  different firings exactly where a call term meets a pattern or a stored row.

So the frame-equality reading has the firings of the table read when the call term occurs in no take,
read, none queries, count or collect pattern and in no stored row (then matching sees no computation), and
the arguments are determined (then the tell is the value tell); with an undetermined argument the
equality leaves the call term as a solution of the tell (a value that is not a value of the function),
where the evaluation waits and the table read enumerates. The first two facts are proved here; the
statement on whole firings is not.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions

open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open OneFrame (Terms frames ext)

universe uF uT uS

variable {F : Type uF} {T : Type uT} {S : Type uS}

/-- **A function in the equality of a substitution action**: a call former, substitution inside calls,
equal arguments giving equal calls, and each call at arguments where the interpretation answers equal to
the value. -/
structure ComputingCall (A : SubstitutionAction T S) (I : F → List T → Option T) where
  call : F → List T → T
  apply_call : ∀ (σ : S) (f : F) (ts : List T), A.apply σ (call f ts) = call f (ts.map (A.apply σ))
  congr : ∀ (f : F) (ts us : List T), List.Forall₂ A.E ts us → A.E (call f ts) (call f us)
  graph_equal : ∀ (f : F) (args : List T) (v : T), I f args = some v → A.E (call f args) v

variable {A : SubstitutionAction T S} {I : F → List T → Option T}

/-- **Where a solution sends the arguments to the arguments of a value, the tell of the call is the tell of
the value.** -/
theorem tell_iff_value (K : ComputingCall A I) (σ : S) {f : F} {ts args : List T} {r v : T}
    (determined : List.Forall₂ A.E (ts.map (A.apply σ)) args) (answers : I f args = some v) :
    A.E (A.apply σ r) (A.apply σ (K.call f ts)) ↔ A.E (A.apply σ r) v := by
  have callValue : A.E (A.apply σ (K.call f ts)) v := by
    rw [K.apply_call]
    exact A.equivalence.trans (K.congr f _ _ determined) (K.graph_equal f args v answers)
  constructor
  · intro told
    exact A.equivalence.trans told callValue
  · intro told
    exact A.equivalence.trans told (A.equivalence.symm callValue)

/-! ## A take of the call fires on its own normal form -/

/-- The rule that takes the term `call`. -/
def takeCall (call : T) : Rule (Terms T) := ⟨PUnit.unit, ⟨[call], [], [], [], []⟩, []⟩

/-- The store whose one row is `v`. -/
def valueStore (v : T) : State (Terms T) ℕ := ⟨PUnit.unit, [], {0}, fun _ => v⟩

/-- The firing of `takeCall call` that takes the row `0`. -/
def takeCallFiring (A : SubstitutionAction T S) (call : T) :
    Firing ℕ (ext A) {takeCall call} PUnit.unit :=
  ⟨takeCall call, rfl, PUnit.unit, A.identity, ⟨[0], [], []⟩, []⟩

/-- **The take of a call term is admitted at the store of its value** when the equality equates them. -/
theorem take_of_call_admitted {call v : T} (fixedV : Fixed A v) (equated : A.E call v) :
    (step (frames A) ℕ (ext A) {takeCall call}).Admits (s := valueStore v) (takeCallFiring A call) := by
  refine (admits_iff _).mpr ⟨fun b g h => ⟨h, fun t mentioned => ?_, fun t inside => ?_⟩,
    ⟨List.nodup_singleton 0, List.nodup_nil, rfl, rfl, rfl, rfl⟩, ?_, ⟨PUnit.unit, A.identity, ?_⟩,
    fun c inside => absurd inside List.not_mem_nil, fun q inside => absurd inside List.not_mem_nil⟩
  · rcases mentioned with inKnowledge | inKnowledge | ⟨o, -, rfl⟩
    · exact absurd inKnowledge List.not_mem_nil
    · exact absurd inKnowledge List.not_mem_nil
    · show A.E (A.apply h (A.apply A.identity v)) (A.apply g v)
      rw [fixedV, fixedV, fixedV]
      exact A.equivalence.refl v
  · show A.E (A.apply h (A.apply A.identity t)) (A.apply h t)
    rw [A.apply_identity]
    exact A.equivalence.refl _
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [takeCallFiring, valueStore, Selection.commit]
  · intro e inside
    have information : (takeCallFiring A call).information (frames A) (valueStore v) =
        [(A.apply A.identity call, A.apply A.identity v)] := rfl
    rw [information, List.mem_singleton] at inside
    subst inside
    show A.E (A.apply A.identity (A.apply A.identity call)) (A.apply A.identity (A.apply A.identity v))
    rw [A.apply_identity, A.apply_identity, A.apply_identity, A.apply_identity]
    exact equated

/-- **With syntactic equality, the same rule at the same store is refused** when the call term is not the
value. -/
theorem take_of_call_refused_syntactically {call v : T} (A : SubstitutionAction T S)
    (syntactic : ∀ s t, A.E s t ↔ s = t) (fixedCall : Fixed A call) (fixedV : Fixed A v) (different : call ≠ v) :
    ¬ (step (frames A) ℕ (ext A) {takeCall call}).Admits (s := valueStore v) (takeCallFiring A call) := by
  intro admitted
  obtain ⟨-, -, -, ⟨_, σ, solved⟩, -⟩ := (admits_iff _).mp admitted
  have information : (takeCallFiring A call).information (frames A) (valueStore v) =
      [(A.apply A.identity call, A.apply A.identity v)] := rfl
  have holds := solved (A.apply A.identity call, A.apply A.identity v) (by
    rw [information]
    exact List.mem_singleton_self _)
  change A.E (A.apply σ (A.apply A.identity call)) (A.apply σ (A.apply A.identity v)) at holds
  rw [fixedCall, fixedCall, fixedV, fixedV] at holds
  exact different ((syntactic _ _).mp holds)

/-! ## Instances -/

section Instances

open RulesAsRows

/-- **Instantiating a code at an environment**, as a call. -/
def codeCall : Unit → List RulesAsRows.Expr → RulesAsRows.Expr
  | (), [c, e] => .drop c e
  | (), _ => .sym 0

/-- Its value: the normal form of the instantiation. -/
def codeValue : Unit → List RulesAsRows.Expr → Option RulesAsRows.Expr
  | (), [c, e] => some (RulesAsRows.Expr.nf (.drop c e))
  | (), _ => none

/-- **The code algebra contains the instantiation of codes in its equality.** -/
def codeComputing : ComputingCall RulesAsRows.Expr.action codeValue where
  call := codeCall
  apply_call σ f ts := by
    match f, ts with
    | (), [_, _] => rfl
    | (), [] => rfl
    | (), [_] => rfl
    | (), _ :: _ :: _ :: _ => rfl
  congr f ts us same := by
    match f, ts, us, same with
    | (), [c, e], [c', e'], .cons sameC (.cons sameE .nil) =>
        show RulesAsRows.Expr.nf (.drop c e) = RulesAsRows.Expr.nf (.drop c' e')
        have nfC : RulesAsRows.Expr.nf c = RulesAsRows.Expr.nf c' := sameC
        have nfE : RulesAsRows.Expr.nf e = RulesAsRows.Expr.nf e' := sameE
        simp only [RulesAsRows.Expr.nf, nfC, nfE]
    | (), [], [], .nil => rfl
    | (), [_], [_], .cons _ .nil => rfl
    | (), _ :: _ :: _ :: _, _ :: _ :: _ :: _, .cons _ (.cons _ (.cons _ _)) => rfl
  graph_equal f args v answers := by
    match f, args, answers with
    | (), [c, e], answers =>
        have isValue : RulesAsRows.Expr.nf (.drop c e) = v := Option.some.inj answers
        show RulesAsRows.Expr.nf (.drop c e) = RulesAsRows.Expr.nf v
        rw [← isValue, RulesAsRows.Expr.nf_nf]

/-- A call of the code algebra: the code of the unknown `0` at the environment `[5]`. -/
def codeCallTerm : RulesAsRows.Expr := .drop (.slot 0 0) (.cell (.sym 5) (.sym 0))

/-- **A take of that call is admitted at the store of its value `5`.** -/
theorem code_take_admitted :
    (step (frames RulesAsRows.Expr.action) ℕ (ext RulesAsRows.Expr.action) {takeCall codeCallTerm}).Admits
      (s := valueStore (.sym 5)) (takeCallFiring RulesAsRows.Expr.action codeCallTerm) :=
  take_of_call_admitted (fun _ => rfl) rfl

/-- **With syntactic equality on rows with unknowns, a take of a call term is refused at a store of another
row.** -/
theorem rows_take_refused :
    ¬ (step (frames Presentation.Schematic.A) ℕ (ext Presentation.Schematic.A)
        {takeCall (Presentation.Schematic.toTerm (.app (.sym 3) (.sym 2)))}).Admits
      (s := valueStore (Presentation.Schematic.toTerm (.sym 5)))
      (takeCallFiring Presentation.Schematic.A (Presentation.Schematic.toTerm (.app (.sym 3) (.sym 2)))) :=
  take_of_call_refused_syntactically Presentation.Schematic.A (fun _ _ => Iff.rfl) (fixed_toTerm _) (fixed_toTerm _)
    (fun same => absurd (Presentation.Schematic.toTerm_injective same) (by decide))

end Instances

#print axioms tell_iff_value
#print axioms take_of_call_admitted
#print axioms take_of_call_refused_syntactically
#print axioms codeComputing
#print axioms code_take_admitted
#print axioms rows_take_refused

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions
