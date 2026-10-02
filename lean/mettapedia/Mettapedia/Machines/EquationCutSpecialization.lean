import Mettapedia.Machines.EquationCut

/-!
# Mode-checked specialization of ordered call/cut programs

A mode is an invariant of the actual incoming logical state, not a request to
enumerate from an empty state and filter later. A checked fact can select a
branch only when its test is constant on that invariant. Primitive operations
must preserve the invariant, including in called equations.

`compile` removes such branches from the existing equation/control language.
It neither sorts equations nor moves cuts or unification. Its correctness law
preserves the complete ordered answer states for arbitrary continuations,
including their substitutions, duplicate occurrences and failure suffixes.

This is specialization of the finite call/cut interpretation. Its call-depth
index is the existing model's bound, not a production limit. Host suspension,
faults and performed-world effects belong to the cursor protocol, rather than
being silently identified with failure here. No executable typing engine or
new intermediate control language is introduced.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.EquationCutSpecialization

open EquationCut

universe u
variable {Local : Type u}

/-- Proof-carrying facts about tests at this mode. `none` requests the original
dynamic test. Soundness concerns local tests, not the whole compiler theorem. -/
structure Facts (invariant : Local → Prop) where
  known : (Local → Bool) → Option Bool
  sound : ∀ test value, known test = some value →
    ∀ state, invariant state → test state = value

/-- Local closure obligations for the primitives mentioned by a body. -/
def Stable (invariant : Local → Prop) : Body Local → Prop
  | .done => True
  | .prim operation next =>
      (∀ state, invariant state → ∀ result ∈ operation state, invariant result) ∧
        Stable invariant next
  | .call _ next | .cut next => Stable invariant next
  | .branch _ yes no => Stable invariant yes ∧ Stable invariant no

def ProgramStable (invariant : Local → Prop) (program : Program Local) : Prop :=
  ∀ relation body, body ∈ program relation → Stable invariant body

/-- Partial evaluation changes code structure, retaining source order and
the position of each binding operation and commitment. -/
def compile (known : (Local → Bool) → Option Bool) : Body Local → Body Local
  | .done => .done
  | .prim operation next => .prim operation (compile known next)
  | .call relation next => .call relation (compile known next)
  | .cut next => .cut (compile known next)
  | .branch test yes no =>
      match known test with
      | some true => compile known yes
      | some false => compile known no
      | none => .branch test (compile known yes) (compile known no)

def compileProgram (known : (Local → Bool) → Option Bool)
    (program : Program Local) : Program Local :=
  fun relation => (program relation).map (compile known)

private theorem foldr_congr_on {Item Result : Type u}
    (items : List Item) (first second : Item → Result → Result) (suffix : Result)
    (agree : ∀ item ∈ items, ∀ rest, first item rest = second item rest) :
    items.foldr first suffix = items.foldr second suffix := by
  induction items with
  | nil => rfl
  | cons item items ih =>
      rw [List.foldr_cons, List.foldr_cons, agree item (by simp)]
      rw [ih (by intro value member; exact agree value (by simp [member]))]

/-- Agreement is required only on states reachable under the checked mode.
This allows fresh/refined bindings while avoiding an unjustified comparison
of continuations on states the mode excludes. -/
theorem compile_correct (program : Program Local) (invariant : Local → Prop)
    (facts : Facts invariant) (programStable : ProgramStable invariant program) :
    ∀ (depth : Nat) (body : Body Local), Stable invariant body →
    ∀ (state : Local), invariant state →
    ∀ (targetSuccess sourceSuccess : Local → List Local → List Local),
      (∀ result, invariant result → ∀ rest, targetSuccess result rest = sourceSuccess result rest) →
    ∀ (failure saved : List Local),
      den (compileProgram facts.known program) depth (compile facts.known body)
        state targetSuccess failure saved =
      den program depth body state sourceSuccess failure saved
  | _, .done, _, state, admitted, targetSuccess, sourceSuccess, agree, failure, _ => by
      rw [compile, den, den]
      exact agree state admitted failure
  | depth, .prim operation next, stable, state, admitted,
      targetSuccess, sourceSuccess, agree, failure, saved => by
      rw [compile, den, den]
      apply foldr_congr_on
      intro result member rest
      exact compile_correct program invariant facts programStable depth next stable.2
        result (stable.1 state admitted result member) targetSuccess sourceSuccess agree rest saved
  | depth, .cut next, stable, state, admitted,
      targetSuccess, sourceSuccess, agree, _, saved => by
      rw [compile, den, den]
      exact compile_correct program invariant facts programStable depth next stable
        state admitted targetSuccess sourceSuccess agree saved saved
  | depth, .branch test yes no, stable, state, admitted,
      targetSuccess, sourceSuccess, agree, failure, saved => by
      rw [compile, den]
      cases known : facts.known test with
      | none =>
          rw [den]
          cases test state
          · exact compile_correct program invariant facts programStable depth no stable.2
              state admitted targetSuccess sourceSuccess agree failure saved
          · exact compile_correct program invariant facts programStable depth yes stable.1
              state admitted targetSuccess sourceSuccess agree failure saved
      | some value =>
          have evaluated := facts.sound test value known state admitted
          cases value
          · simp only [evaluated, Bool.false_eq_true, ↓reduceIte]
            exact compile_correct program invariant facts programStable depth no stable.2
              state admitted targetSuccess sourceSuccess agree failure saved
          · simp only [evaluated, ↓reduceIte]
            exact compile_correct program invariant facts programStable depth yes stable.1
              state admitted targetSuccess sourceSuccess agree failure saved
  | 0, .call _ _, _, _, _, _, _, _, _, _ => by rw [compile, den, den]
  | depth + 1, .call relation next, stable, state, admitted,
      targetSuccess, sourceSuccess, agree, failure, saved => by
      rw [compile, den, den]
      simp only [compileProgram, List.foldr_map]
      apply foldr_congr_on
      intro equation member rest
      apply compile_correct program invariant facts programStable depth equation
        (programStable relation equation member) state admitted
      intro result refined suffix
      exact compile_correct program invariant facts programStable (depth + 1) next stable
        result refined targetSuccess sourceSuccess agree suffix saved
termination_by depth body _ _ _ _ _ _ _ _ => (depth, sizeOf body)

theorem ordered_answers_exact (program : Program Local) (invariant : Local → Prop)
    (facts : Facts invariant) (programStable : ProgramStable invariant program)
    (depth : Nat) (body : Body Local) (stable : Stable invariant body)
    (state : Local) (admitted : invariant state) :
    den (compileProgram facts.known program) depth (compile facts.known body)
      state List.cons [] [] = den program depth body state List.cons [] [] :=
  compile_correct program invariant facts programStable depth body stable state admitted
    List.cons List.cons (by intros; rfl) [] []

def nodes : Body Local → Nat
  | .done => 1
  | .prim _ next | .call _ next | .cut next => 1 + nodes next
  | .branch _ yes no => 1 + nodes yes + nodes no

/-- The specializer actually eliminates control structure, rather than
copying the reference body under a different name. -/
theorem compile_nodes_le (known : (Local → Bool) → Option Bool) (body : Body Local) :
    nodes (compile known body) ≤ nodes body := by
  induction body with
  | done => rfl
  | prim operation next ih | call relation next ih | cut next ih =>
      simpa only [compile, nodes] using Nat.add_le_add_left ih 1
  | branch test yes no yesIH noIH =>
      cases observed : known test with
      | none => simp only [compile, observed, nodes]; omega
      | some bit => cases bit <;> simp only [compile, observed, nodes] <;> omega

namespace Controls

inductive Kind where | number | foo deriving DecidableEq, Repr

structure Bindings where
  required : Option Kind
  witness : Nat
  deriving DecidableEq, Repr

def compatible (kind : Kind) (state : Bindings) : Bool :=
  state.required.isNone || state.required == some kind

def bind (kind : Kind) (witness : Nat) (state : Bindings) : List Bindings :=
  if compatible kind state then [⟨some kind, witness⟩] else []

def fail : Body Bindings := .prim (fun _ => []) .done

/-- Head compatibility precedes cut. Two authored occurrences share a value,
but retain their distinct binding witnesses. -/
def program : Program Bindings := fun _ =>
  [.branch (compatible .number) (.prim (bind .number 0) (.cut .done)) fail,
   .branch (compatible .foo) (.prim (bind .foo 1) .done) fail,
   .branch (compatible .foo) (.prim (bind .foo 2) .done) fail]

def mode (state : Bindings) : Prop := state.required = some .foo

/-- In this proof instance facts are indexed by the test functions. A source
compiler uses its finite test identifiers; no runtime function equality is proposed. -/
noncomputable def facts : Facts mode := by
  classical
  refine ⟨fun test => if test = compatible .number then some false
    else if test = compatible .foo then some true else none, ?_⟩
  intro test value known state admitted
  change state.required = some .foo at admitted
  by_cases number : test = compatible .number
  · simp only [if_pos number, Option.some.injEq] at known
    subst value
    subst test
    simp [compatible, admitted]
  · by_cases foo : test = compatible .foo
    · simp only [if_neg number, if_pos foo, Option.some.injEq] at known
      subst value
      subst test
      simp [compatible, admitted]
    · simp only [if_neg number, if_neg foo] at known
      cases known

theorem bind_preserves_mode (kind : Kind) (witness : Nat) (state : Bindings)
    (admitted : mode state) (result : Bindings) (member : result ∈ bind kind witness state) :
    mode result := by
  change state.required = some .foo at admitted
  cases kind <;> simp [bind, compatible, admitted] at member
  subst result
  rfl

theorem program_stable : ProgramStable mode program := by
  intro relation body member
  simp only [program, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;>
    simp only [Stable, fail, and_true] <;>
    constructor
  all_goals first
    | exact bind_preserves_mode _ _
    | intro state admitted result member; cases member

theorem specialized_bound_call_preserves_order_and_bindings :
    den (compileProgram facts.known program) 1 (compile facts.known (.call 0 .done))
      ⟨some .foo, 0⟩ List.cons [] [] = [⟨some .foo, 1⟩, ⟨some .foo, 2⟩] := by
  rw [ordered_answers_exact program mode facts program_stable 1 _ (by trivial)
    _ (by rfl)]
  simp [den, program, compatible, bind, fail]

theorem known_mode_removes_control :
    nodes (compile facts.known
      (.branch (compatible .number) (.prim (bind .number 0) (.cut .done)) fail)) = 2 ∧
    nodes (.branch (compatible .number) (.prim (bind .number 0) (.cut .done)) fail) = 6 := by
  simp [compile, facts, nodes, fail]

/-- Fresh enumeration followed by filtering cannot substitute for a bound
query: the earlier cut has already discarded its later authored equations. -/
theorem enumerate_then_filter_changes_the_mode :
    (den program 1 (.call 0 .done) ⟨none, 0⟩ List.cons [] []).filter
      (fun state => state.required == some .foo) = [] ∧
    den program 1 (.call 0 .done) ⟨some .foo, 0⟩ List.cons [] [] =
      [⟨some .foo, 1⟩, ⟨some .foo, 2⟩] := by
  simp [den, program, compatible, bind, fail]

theorem ignoring_a_mode_fact_changes_answers :
    den (compileProgram (fun _ => some false) program) 1 (.call 0 .done)
      ⟨some .foo, 0⟩ List.cons [] [] = [] ∧
    den program 1 (.call 0 .done) ⟨some .foo, 0⟩ List.cons [] [] ≠ [] := by
  simp [den, compileProgram, compile, program, compatible, bind, fail]

end Controls

end Mettapedia.Machines.EquationCutSpecialization
