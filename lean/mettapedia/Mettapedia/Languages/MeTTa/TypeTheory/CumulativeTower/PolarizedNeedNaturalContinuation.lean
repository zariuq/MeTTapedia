import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PolarizedNeedNaturalSemantics

/-!
# Source interpretation of effectful consumers

The independent source evaluation judgments contain no machine continuations.
This proof-layer interpretation explains what an existing continuation does
to a source answer. Function application may evaluate a captured body and
change the world; native pairing and faults do not invent an evaluation.

Its finite derivation weight supports contextual implementation proofs, not
termination of arbitrary source programs. The interpretation uses independent
source derivations and contains no machine-path premise.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace PolarizedNeedNaturalSemantics

open PrimeNeedReference PolarizedNeedMachine

variable {Head Operation Effect StableFault NativeFault : Type} {m : Nat}
  {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}

/-- Applying a computation-function answer executes its saved source body in
the current world, then interprets the remaining consumer. -/
inductive KontEval
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault) :
    Kont Head Operation Effect m → Outcome Head Operation Effect StableFault NativeFault m →
      NeedWorld Head Operation Effect StableFault NativeFault m →
      Outcome Head Operation Effect StableFault NativeFault m →
      NeedWorld Head Operation Effect StableFault NativeFault m → Type where
  | done (input : Outcome Head Operation Effect StableFault NativeFault m)
      (world : NeedWorld Head Operation Effect StableFault NativeFault m) :
      KontEval primitive .done input world input world
  | pairNative {rest : Kont Head Operation Effect m} (first second : Tm Head m)
      {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
      {outcome : Outcome Head Operation Effect StableFault NativeFault m} :
      KontEval primitive rest (.value (.returned (.native (.pair first second)))) world outcome final →
      KontEval primitive (.pair first rest) (.value (.returned (.native second))) world outcome final
  | pairMismatch (first : Tm Head m) (rest : Kont Head Operation Effect m)
      (answer : Answer Head Operation Effect m)
      (world : NeedWorld Head Operation Effect StableFault NativeFault m)
      (wrong : ∀ term, answer ≠ .returned (.native term)) :
      KontEval primitive (.pair first rest) (.value answer) world
        (.retryableFault (.domain .expectedNativeValue)) world
  | nativeApply {rest : Kont Head Operation Effect m} (argument : Tm Head m)
      (body : NativeBody Head Operation Effect m)
      {world selected final : NeedWorld Head Operation Effect StableFault NativeFault m}
      {result outcome : Outcome Head Operation Effect StableFault NativeFault m} :
      Eval primitive (body.open argument) world result selected →
      KontEval primitive rest result selected outcome final →
      KontEval primitive (.nativeApply argument rest) (.value (.nativeFunction body)) world outcome final
  | nativeMismatch (argument : Tm Head m) (rest : Kont Head Operation Effect m)
      (answer : Answer Head Operation Effect m)
      (world : NeedWorld Head Operation Effect StableFault NativeFault m)
      (wrong : ∀ body, answer ≠ .nativeFunction body) :
      KontEval primitive (.nativeApply argument rest) (.value answer) world
        (.retryableFault (.domain .expectedNativeFunction)) world
  | valueApply {rest : Kont Head Operation Effect m} (argument : RuntimeValue Head Operation Effect m)
      (body : ValueBody Head Operation Effect m)
      {world selected final : NeedWorld Head Operation Effect StableFault NativeFault m}
      {result outcome : Outcome Head Operation Effect StableFault NativeFault m} :
      Eval primitive (body.open argument) world result selected →
      KontEval primitive rest result selected outcome final →
      KontEval primitive (.valueApply argument rest) (.value (.valueFunction body)) world outcome final
  | valueMismatch (argument : RuntimeValue Head Operation Effect m) (rest : Kont Head Operation Effect m)
      (answer : Answer Head Operation Effect m)
      (world : NeedWorld Head Operation Effect StableFault NativeFault m)
      (wrong : ∀ body, answer ≠ .valueFunction body) :
      KontEval primitive (.valueApply argument rest) (.value answer) world
        (.retryableFault (.domain .expectedValueFunction)) world
  | stableFault (kont : Kont Head Operation Effect m) (fault : StableFault)
      (world : NeedWorld Head Operation Effect StableFault NativeFault m) :
      KontEval primitive kont (.stableFault fault) world (.stableFault fault) world
  | retryableFault (kont : Kont Head Operation Effect m) (reason : RetryReason (Fault NativeFault))
      (world : NeedWorld Head Operation Effect StableFault NativeFault m) :
      KontEval primitive kont (.retryableFault reason) world (.retryableFault reason) world

/-- A finite consumer proof counts its embedded source evaluations. The
weight is proof-side data, not the evaluator's fuel or work counter. -/
def KontEval.weight {kont : Kont Head Operation Effect m}
    {input outcome : Outcome Head Operation Effect StableFault NativeFault m}
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
    (evaluation : KontEval primitive kont input world outcome final) : Nat :=
  match evaluation with
  | .done _ _ => 0
  | .pairNative _ _ rest => 1 + rest.weight
  | .pairMismatch _ _ _ _ _ => 1
  | .nativeApply _ _ body rest => 1 + body.weight + rest.weight
  | .nativeMismatch _ _ _ _ _ => 1
  | .valueApply _ _ body rest => 1 + body.weight + rest.weight
  | .valueMismatch _ _ _ _ _ => 1
  | .stableFault _ _ _ => 0
  | .retryableFault _ _ _ => 0

theorem KontEval.done_exact
    {input outcome : Outcome Head Operation Effect StableFault NativeFault m}
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
    (evaluation : KontEval primitive .done input world outcome final) :
    outcome = input ∧ final = world := by
  cases evaluation <;> exact ⟨rfl, rfl⟩

theorem KontEval.stable_exact {kont : Kont Head Operation Effect m} {fault : StableFault}
    {outcome : Outcome Head Operation Effect StableFault NativeFault m}
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
    (evaluation : KontEval primitive kont (.stableFault fault) world outcome final) :
    outcome = .stableFault fault ∧ final = world := by
  cases evaluation <;> exact ⟨rfl, rfl⟩

theorem KontEval.retry_exact {kont : Kont Head Operation Effect m}
    {reason : RetryReason (Fault NativeFault)}
    {outcome : Outcome Head Operation Effect StableFault NativeFault m}
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
    (evaluation : KontEval primitive kont (.retryableFault reason) world outcome final) :
    outcome = .retryableFault reason ∧ final = world := by
  cases evaluation <;> exact ⟨rfl, rfl⟩

/-- Pairing and already-returned values cannot enter a computation function.
This recovers the runtime's pure finishing equation on precisely that input
class, rather than asserting it for computation-function answers. -/
theorem KontEval.returned_exact {kont : Kont Head Operation Effect m}
    {value : RuntimeValue Head Operation Effect m}
    {outcome : Outcome Head Operation Effect StableFault NativeFault m}
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
    (evaluation : KontEval primitive kont (.value (.returned value)) world outcome final) :
    outcome = finish (.value (.returned value)) kont ∧ final = world := by
  induction kont generalizing value with
  | done => exact evaluation.done_exact
  | pair first rest ih =>
      cases evaluation with
      | pairNative _ second evaluated => exact ih evaluated
      | pairMismatch _ _ _ _ wrong =>
          cases value with
          | native term => exact False.elim (wrong term rfl)
          | thunk _ _ _ _ => exact ⟨rfl, rfl⟩
          | packNative _ _ => exact ⟨rfl, rfl⟩
  | nativeApply argument rest =>
      cases evaluation
      exact ⟨rfl, rfl⟩
  | valueApply argument rest =>
      cases evaluation
      exact ⟨rfl, rfl⟩

theorem KontEval.fault_exact {kont : Kont Head Operation Effect m}
    {input outcome : Outcome Head Operation Effect StableFault NativeFault m}
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
    (evaluation : KontEval primitive kont input world outcome final)
    (fault : FaultOutcome input) : outcome = input ∧ final = world := by
  cases fault with
  | stableFault => exact evaluation.stable_exact
  | retryableFault => exact evaluation.retry_exact

theorem KontEval.done_iff
    {input outcome : Outcome Head Operation Effect StableFault NativeFault m}
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m} :
    Nonempty (KontEval primitive .done input world outcome final) ↔
      outcome = input ∧ final = world := by
  constructor
  · rintro ⟨evaluation⟩; exact evaluation.done_exact
  · rintro ⟨rfl, rfl⟩; exact ⟨.done _ _⟩

theorem KontEval.stable_iff {kont : Kont Head Operation Effect m} {fault : StableFault}
    {outcome : Outcome Head Operation Effect StableFault NativeFault m}
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m} :
    Nonempty (KontEval primitive kont (.stableFault fault) world outcome final) ↔
      outcome = .stableFault fault ∧ final = world := by
  constructor
  · rintro ⟨evaluation⟩; exact evaluation.stable_exact
  · rintro ⟨rfl, rfl⟩; exact ⟨.stableFault _ _ _⟩

theorem KontEval.retry_iff {kont : Kont Head Operation Effect m}
    {reason : RetryReason (Fault NativeFault)}
    {outcome : Outcome Head Operation Effect StableFault NativeFault m}
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m} :
    Nonempty (KontEval primitive kont (.retryableFault reason) world outcome final) ↔
      outcome = .retryableFault reason ∧ final = world := by
  constructor
  · rintro ⟨evaluation⟩; exact evaluation.retry_exact
  · rintro ⟨rfl, rfl⟩; exact ⟨.retryableFault _ _ _⟩

/-- Prepending native pairing retains the supplied consumer proof, or propagates
the precise mismatch/fault. At most one evidence node is added. -/
def KontEval.pair_input {kont : Kont Head Operation Effect m}
    {input outcome : Outcome Head Operation Effect StableFault NativeFault m}
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
    (first : Tm Head m)
    (evaluation : KontEval primitive kont (pairOutcome first input) world outcome final) :
    { paired : KontEval primitive (.pair first kont) input world outcome final //
      paired.weight ≤ 1 + evaluation.weight } := by
  cases input with
  | value answer =>
      cases answer with
      | returned value =>
          cases value with
          | native second => exact ⟨.pairNative first second evaluation, Nat.le_refl _⟩
          | thunk code native values needs =>
              obtain ⟨out, fin⟩ := evaluation.retry_exact
              subst outcome final
              exact ⟨.pairMismatch first kont _ world (by intro term impossible; cases impossible),
                Nat.le_add_right 1 _⟩
          | packNative index payload =>
              obtain ⟨out, fin⟩ := evaluation.retry_exact
              subst outcome final
              exact ⟨.pairMismatch first kont _ world (by intro term impossible; cases impossible),
                Nat.le_add_right 1 _⟩
      | nativeFunction body =>
          obtain ⟨out, fin⟩ := evaluation.retry_exact
          subst outcome final
          exact ⟨.pairMismatch first kont _ world (by intro term impossible; cases impossible),
            Nat.le_add_right 1 _⟩
      | valueFunction body =>
          obtain ⟨out, fin⟩ := evaluation.retry_exact
          subst outcome final
          exact ⟨.pairMismatch first kont _ world (by intro term impossible; cases impossible),
            Nat.le_add_right 1 _⟩
  | stableFault fault =>
      obtain ⟨out, fin⟩ := evaluation.stable_exact
      subst outcome final
      exact ⟨.stableFault _ fault world, Nat.zero_le _⟩
  | retryableFault reason =>
      obtain ⟨out, fin⟩ := evaluation.retry_exact
      subst outcome final
      exact ⟨.retryableFault _ reason world, Nat.zero_le _⟩

theorem KontEval.pair_iff {kont : Kont Head Operation Effect m}
    {input outcome : Outcome Head Operation Effect StableFault NativeFault m}
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
    (first : Tm Head m) :
    Nonempty (KontEval primitive (.pair first kont) input world outcome final) ↔
      Nonempty (KontEval primitive kont (pairOutcome first input) world outcome final) := by
  constructor
  · rintro ⟨evaluation⟩
    cases evaluation with
    | pairNative _ _ rest => exact ⟨rest⟩
    | pairMismatch _ _ answer _ wrong =>
        cases answer with
        | returned value =>
            cases value with
            | native term => exact False.elim (wrong term rfl)
            | thunk _ _ _ _ => exact ⟨.retryableFault _ _ _⟩
            | packNative _ _ => exact ⟨.retryableFault _ _ _⟩
        | nativeFunction _ => exact ⟨.retryableFault _ _ _⟩
        | valueFunction _ => exact ⟨.retryableFault _ _ _⟩
    | stableFault => exact ⟨.stableFault _ _ _⟩
    | retryableFault => exact ⟨.retryableFault _ _ _⟩
  · rintro ⟨evaluation⟩
    exact ⟨(KontEval.pair_input first evaluation).1⟩

/-- Returned values have a consumer derivation for the actual pure finishing
equation. This does not assert pure finishing for computation functions. -/
def KontEval.returned_input (kont : Kont Head Operation Effect m)
    (value : RuntimeValue Head Operation Effect m)
    (world : NeedWorld Head Operation Effect StableFault NativeFault m) :
    KontEval primitive kont (.value (.returned value)) world
      (finish (.value (.returned value)) kont) world :=
  match kont with
  | .done => .done _ _
  | .pair first rest =>
      match value with
      | .native second => .pairNative first second
          (KontEval.returned_input rest (.native (.pair first second)) world)
      | .thunk _ _ _ _ => .pairMismatch first rest _ world
          (by intro term impossible; cases impossible)
      | .packNative _ _ => .pairMismatch first rest _ world
          (by intro term impossible; cases impossible)
  | .nativeApply argument rest => .nativeMismatch argument rest _ world
      (by intro body impossible; cases impossible)
  | .valueApply argument rest => .valueMismatch argument rest _ world
      (by intro body impossible; cases impossible)
termination_by structural kont

theorem KontEval.returned_iff {kont : Kont Head Operation Effect m}
    {value : RuntimeValue Head Operation Effect m}
    {outcome : Outcome Head Operation Effect StableFault NativeFault m}
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m} :
    Nonempty (KontEval primitive kont (.value (.returned value)) world outcome final) ↔
      outcome = finish (.value (.returned value)) kont ∧ final = world := by
  constructor
  · rintro ⟨evaluation⟩; exact evaluation.returned_exact
  · rintro ⟨rfl, rfl⟩; exact ⟨KontEval.returned_input kont value _⟩

#print axioms KontEval.done_exact
#print axioms KontEval.stable_exact
#print axioms KontEval.retry_exact
#print axioms KontEval.returned_exact
#print axioms KontEval.fault_exact
#print axioms KontEval.pair_input
#print axioms KontEval.pair_iff
#print axioms KontEval.returned_input
#print axioms KontEval.returned_iff

end PolarizedNeedNaturalSemantics
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
