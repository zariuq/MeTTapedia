import Mettapedia.Languages.MeTTa.PeTTa.Legacy.ContractTyping.Erasure

/-!
# The call contract

`call_contract` checks the arguments (the admissible declarations are those they fit; none is a
type error), runs the body once, and requires each answer to fit, jointly with the arguments,
some declaration. Routes (direct, overloaded, closure, partial application, `reduce`, dynamic
apply) differ only in the static evidence they hold. Compiling is partial evaluation: a test that
the argument's static type establishes against the declaration instance is dropped; a test that
remains tests the declared type (`declared_check_accepts`). `contract_route_independent`: every
route, with sound evidence, runs exactly as the contract with every check.

A function with one declaration checks its result in its own clauses and its parameters at its
entry (`single_declaration_entry`): with retention this is the same contract, evaluated at a
different place. `(brand N E)` is a check of `E` against `N`'s representation (`brand_sound`).

The joint result test ranges over every declaration and re-tests the arguments, and every passed
test is retained; `contract_call/5` ranges over the declarations admissible at entry and retains
only the result. Runs without type errors are the same (`erasure_preserves_observations`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Legacy.ContractTyping

universe u

/-- The runtime test (`typecheck_ok/2`) decides the value relation; the compile-time
establishment (`established/2`) is sound. -/
structure Checker (sig : Sig) where
  test : Term → Ty → Bool
  test_iff : ∀ v T, test v T = true ↔ Fits sig v T
  est : Ty → Ty → Bool
  est_sound : ∀ S T, est S T = true → Establishes sig S T

open Classical in
/-- A checker exists for every signature. -/
noncomputable def Checker.classical (sig : Sig) : Checker sig where
  test v T := decide (Fits sig v T)
  test_iff _ _ := decide_eq_true_iff
  est S T := decide (Establishes sig S T)
  est_sound _ _ := of_decide_eq_true

structure Decl where
  args : List Ty
  res : Ty

/-- An argument of a call: its value, and the static type the compiler holds for it. -/
structure Arg where
  term : Term
  static : Option Ty

/-- The static type is inst evidence. -/
def Arg.Sound (sig : Sig) (a : Arg) : Prop := ∀ S ∈ a.static, Has sig a.term S

variable {sig : Sig} (chk : Checker sig) {W : Type u}

namespace Checker

/-- A vector of values passes a vector of types. -/
def testAll : List Term → List Ty → Bool
  | [], [] => true
  | v :: vs, T :: Ts => chk.test v T && testAll vs Ts
  | _, _ => false

theorem testAll_iff : ∀ (vs : List Term) (Ts : List Ty), chk.testAll vs Ts = true ↔ FitsAll sig vs Ts
  | [], [] => by simp [testAll, FitsAll]
  | [], _ :: _ | _ :: _, [] => by simp [testAll, FitsAll]
  | v :: vs, T :: Ts => by
      rw [testAll, Bool.and_eq_true, chk.test_iff, testAll_iff vs Ts]
      simp [FitsAll]

/-- `(5)`: the runtime test of the arguments is against the declared types, whose variables are
unknown; it accepts every argument vector that the declaration instance `σ` accepts. -/
theorem declared_check_accepts (σ : Nat → Ty) {vs : List Term} {As : List Ty}
    (h : chk.testAll vs (As.map (Ty.subst σ)) = true) : chk.testAll vs As = true := by
  rw [testAll_iff] at h ⊢
  exact (List.forall₂_map_right_iff.1 h).imp fun _ T hv => hv.of_subst sig T rfl

/-- An argument meets a parameter type: established by its static type against the declaration
instance `σ`, when the route holds evidence; else by the runtime test of the declared type. -/
def passes (ev : Bool) (σ : Nat → Ty) (θ : Bindings) (a : Arg) (A : Ty) : Bool :=
  (ev && a.static.any (chk.est · (A.subst σ))) || chk.test (a.term.subst θ) A

/-- The arguments meet the parameter types of a declaration. -/
def admits (ev : Bool) (σ : Nat → Ty) (θ : Bindings) : List Arg → List Ty → Bool
  | [], [] => true
  | a :: as, A :: As => chk.passes ev σ θ a A && admits ev σ θ as As
  | _, _ => false

/-- The contract of a call to the declarations `decls`, the body binding `out` per answer. -/
def contract (ev : Bool) (σ : Nat → Ty) (decls : List Decl)
    (body : Bindings → W → List Bindings × W) (args : List Arg) (out : Term) : List (Step W) :=
  [.check (fun θ => decls.any fun d => chk.admits ev σ θ args d.args) id,
   .run body,
   .check (fun θ => decls.any fun d =>
      chk.admits ev σ θ args d.args && chk.test (out.subst θ) d.res) id]

/-- `call_contract` (`contract_call/5`, `dynamic_call/4`): every check made. -/
def callContract (decls : List Decl) (body : Bindings → W → List Bindings × W) (args : List Arg)
    (out : Term) : List (Step W) :=
  chk.contract false .var decls body args out

end Checker

inductive Route where
  | direct | overload | closure | partialApp | reduce | dynamicApply

/-- A call compiled where its callee is known holds the arguments' static types; a callee known
only at runtime (`dynamic_call/4`) holds none. -/
def Route.static : Route → Bool
  | .reduce | .dynamicApply => false
  | _ => true

namespace Checker

/-- The call as compiled on a route, with the instance `σ` its arguments chose: the contract,
partially evaluated on the route's evidence. -/
def compiledCall (r : Route) (σ : Nat → Ty) (decls : List Decl)
    (body : Bindings → W → List Bindings × W) (args : List Arg) (out : Term) : List (Step W) :=
  chk.contract r.static σ decls body args out

/-- A dropped test is one that would have passed, under every binding. -/
theorem passes_sound {a : Arg} (ha : a.Sound sig) (σ : Nat → Ty) (θ : Bindings) (A : Ty) :
    chk.passes true σ θ a A = chk.passes false .var θ a A := by
  unfold passes
  cases hs : a.static with
  | none => simp
  | some S =>
      by_cases he : chk.est S (A.subst σ) = true
      · have hfit := (establishes_sound (chk.est_sound S _ he) (ha S hs) θ).of_subst sig A rfl
        simp [(chk.test_iff _ _).2 hfit]
      · simp [he]

theorem admits_sound (σ : Nat → Ty) (θ : Bindings) :
    ∀ {args : List Arg}, (∀ a ∈ args, a.Sound sig) →
      ∀ As, chk.admits true σ θ args As = chk.admits false .var θ args As
  | [], _, [] | [], _, _ :: _ | _ :: _, _, [] => rfl
  | a :: as, h, A :: As => by
      simp only [admits, chk.passes_sound (h a List.mem_cons_self),
        admits_sound σ θ (fun b hb => h b (List.mem_cons_of_mem a hb)) As]

theorem admits_plain (σ : Nat → Ty) (θ : Bindings) (args : List Arg) (As : List Ty) :
    chk.admits false σ θ args As = chk.admits false .var θ args As := by
  induction args generalizing As with
  | nil => cases As <;> rfl
  | cons a as ih => cases As <;> simp [admits, passes, ih]

/-- Every route, with sound evidence, compiles to the contract with every check. -/
theorem compiledCall_eq (r : Route) (σ : Nat → Ty) (decls : List Decl)
    (body : Bindings → W → List Bindings × W) {args : List Arg} (hargs : ∀ a ∈ args, a.Sound sig)
    (out : Term) : chk.compiledCall r σ decls body args out = chk.callContract decls body args out := by
  unfold compiledCall callContract contract
  cases r.static
  · simp only [chk.admits_plain σ]
  · simp only [chk.admits_sound σ _ hargs]

/-- `contract_route_independent`: answers, effects and type errors of a call, in any
continuation, are those of the contract with every check, whatever the route, the instance its
arguments chose, and the sound evidence it holds. -/
theorem contract_route_independent (r : Route) (σ : Nat → Ty) (decls : List Decl)
    (body : Bindings → W → List Bindings × W) {args : List Arg} (hargs : ∀ a ∈ args, a.Sound sig)
    (out : Term) (ps : List (Step W)) (retain : Bool) (l : Local) (w : W) :
    exec retain (chk.compiledCall r σ decls body args out ++ ps) l w =
      exec retain (chk.callContract decls body args out ++ ps) l w := by
  rw [chk.compiledCall_eq r σ decls body hargs out]

/-- `(c)` at runtime: a function declared `(-> As R)`, called through a demanded arrow whose
`i`-th parameter conflicts with `As[i]` as atoms, with a ground argument fitting the demanded
parameter: the callee's contract raises. -/
theorem arrow_conflict_raises {As Bs : List Ty} {R : Ty} {i : Nat} (h₁ : i < As.length)
    (h₂ : i < Bs.length) (hc : Conflict sig As[i] Bs[i]) (hA : As[i].Atom) (hB : Bs[i].Atom)
    (body : Bindings → W → List Bindings × W) (args : List Arg) (out : Term) (ps : List (Step W))
    (retain : Bool) (l : Local) (w : W) (hi : i < args.length)
    (hg : (args[i].term.subst l.θ).Closed) (hfit : Fits sig (args[i].term.subst l.θ) Bs[i]) :
    exec retain (chk.callContract [⟨As, R⟩] body args out ++ ps) l w = .error w := by
  have hfail : ∀ (args : List Arg) (As : List Ty) (i : Nat) (hi : i < args.length)
      (h₁ : i < As.length), chk.passes false .var l.θ args[i] As[i] = false →
      chk.admits false .var l.θ args As = false := by
    intro args As i hi h₁ hp
    induction args generalizing As i with
    | nil => cases hi
    | cons a as ih =>
        cases As with
        | nil => cases h₁
        | cons A As =>
            cases i with
            | zero => simp only [List.getElem_cons_zero] at hp; simp [admits, hp]
            | succ i =>
                simp [admits, ih As i (by simpa using hi) (by simpa using h₁) (by simpa using hp)]
  have hp : chk.passes false .var l.θ args[i] As[i] = false := by
    simp only [passes, Bool.false_and, Bool.false_or, Bool.eq_false_iff]
    intro ht
    exact hc.atomic_apart hA hB hg ((chk.test_iff _ _).1 ht) hfit
  simp [callContract, contract, exec, hfail args As i hi h₁ hp]

/-- The check of a value at a type, as a condition on the bindings. -/
def fitsCond (v : Term) (T : Ty) : Cond := fun θ => chk.test (v.subst θ) T

/-- Inst evidence removes a check from every run. -/
theorem inst_check_erasable {v : Term} {T : Ty} (h : inst sig v T) (retain : Bool)
    (ps : List (Step W)) (l : Local) (w : W) :
    exec retain (.check (chk.fitsCond v T) id :: ps) l w = exec retain ps l w :=
  inst_check_redundant (fun θ => (chk.test_iff _ _).2 (h θ)) retain ps l w

/-- `(brand N E)`: a check of `E` against `N`'s representation `R`. -/
def brand (e : Term) (R : Ty) : Step W := .check (chk.fitsCond e R) id

/-- A branded value has the newtype as a sound static type, and the brand check is erased
where its argument is established: newtypes are erased at runtime. -/
theorem brand_sound {N : String} {R : Ty} (hN : sig.newtypes N = some R) {e : Term}
    (h : inst sig e R) (retain : Bool) (ps : List (Step W)) (l : Local) (w : W) :
    Has sig e (.newtype N) ∧ exec retain (chk.brand e R :: ps) l w = exec retain ps l w :=
  ⟨fun _ θ => .newtype hN (h θ), chk.inst_check_erasable h retain ps l w⟩

/-- A function with one declaration: its entry checks the parameters, its clauses the result. -/
def singleEntry (d : Decl) (body : Bindings → W → List Bindings × W) (args : List Arg)
    (out : Term) : List (Step W) :=
  [.check (fun θ => chk.admits false .var θ args d.args) id, .run body,
   .check (chk.fitsCond out d.res) id]

end Checker

/-- Replacing a check by one that agrees wherever the branch's obligations hold. -/
theorem exec_check_congr {c₁ c₂ : Cond} (retain : Bool) (e : W → W) (ps : List (Step W))
    (l : Local) (w : W) (hl : l.Live) (h : ∀ θ, l.obs.all (· θ) = true → c₁ θ = c₂ θ) :
    exec retain (.check c₁ e :: ps) l w = exec retain (.check c₂ e :: ps) l w := by
  simp only [exec, h l.θ hl]
  split
  · refine exec_congr retain ps _ rfl fun θ => ?_
    cases retain
    · rfl
    · by_cases ho : l.obs.all (· θ) = true
      · simp [h θ ho]
      · simp [ho]
  · rfl

namespace Checker

/-- With retention, the dynamic entry of a function with one declaration is its contract, in any
continuation: the parameters' obligations hold at every answer, so testing them again with the
result is redundant. -/
theorem single_declaration_entry (d : Decl) (body : Bindings → W → List Bindings × W)
    (args : List Arg) (out : Term) (ps : List (Step W)) (l : Local) (w : W) :
    exec true (chk.singleEntry d body args out ++ ps) l w =
      exec true (chk.callContract [d] body args out ++ ps) l w := by
  simp only [singleEntry, callContract, contract, List.any_cons, List.any_nil, Bool.or_false,
    List.cons_append, List.nil_append]
  simp only [exec, if_true]
  split
  · refine thread_congr (fun θ w' => ?_) _ _
    split
    · next hg =>
        have key := exec_check_congr true id ps
          ⟨θ, (fun θ => chk.admits false .var θ args d.args) :: l.obs⟩ w' hg
          (c₁ := chk.fitsCond out d.res)
          (c₂ := fun θ => chk.admits false .var θ args d.args && chk.test (out.subst θ) d.res)
          fun θ' ho => by
            simp only [List.all_cons, Bool.and_eq_true] at ho
            simp [fitsCond, ho.1]
        simpa only [exec, if_true, ↓reduceIte] using key
    · rfl
  · rfl

end Checker

end Mettapedia.Languages.MeTTa.PeTTa.Legacy.ContractTyping
