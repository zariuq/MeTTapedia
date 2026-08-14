/-
# Zero-family / Pure design memo (executable)

A design memo stated in Lean, so that every claim is either proved here or
pinned as a named open question with a machine-visible count.  Scope:

1. Abstract, modular *core capabilities* for grading minimal-language
   candidates, so the family of zeros is carrier-indexed data rather than
   prose (§1).
2. The candidate lattice: zero (match/let/emit), zero-prime (zero plus named
   abstraction), prime, and the mm2 point whose fused `exec` may or may not
   subsume match + sharing + emit.  The subsumption combinatorics is proved;
   whether the expansion is *semantically* justified is kept as a formal open
   question, not a verdict (§2).
3. The raw-versus-quotient placement principle, proved concretely on a
   miniature core: cost and evidence semantics live on RAW syntax — they
   provably do not factor through equality/deduplication quotients (§3–§4).
4. Acceptance shapes for the Pure-layer improvements: graded cost algebras,
   the operational↔type-theoretic core correspondence, and the strict
   level-raising quotation discipline (§5).
5. The open-question ledger with its count pinned (§6).

No claim is made that any candidate below is the final language; the real
carriers live in the runtime and in the native-type-theory derivation.  LLM
primer: `MiniTm` exists only to make the negative theorems concrete and
cheap — do not grow it into a real calculus here.  All proofs are
`decide`/`simp`/`rfl`/`omega`-grade by design.
-/
import Mathlib.Data.Multiset.Dedup

namespace Mettapedia.Languages.MeTTa.ZeroFamilyPureDesign

/-! ## §1 Abstract modular capabilities and carrier-indexed candidates -/

/-- Abstract, modular core capabilities.  Each is an observable criterion a
candidate language either exhibits or lacks; the family order is capability
inclusion.  New capabilities extend this enumeration without disturbing any
existing lattice fact. -/
inductive CoreCapability where
  /-- Eliminate by matching a pattern against a space. -/
  | patternMatch
  /-- Sharing (`let`) distinct from substitution — cost-relevant. -/
  | explicitSharing
  /-- Act on a space: emit / add-atom. -/
  | actEmit
  /-- Multiset (superposition) results. -/
  | collections
  /-- Pattern metavariables. -/
  | metavariables
  /-- Unknown symbols stay uninterpreted. -/
  | inertUnknowns
  /-- Named (rho-style) abstraction. -/
  | namedAbstraction
  /-- A single fused primitive combining match, binding use, and emission. -/
  | fusedExec
  deriving DecidableEq, Repr

/-- S-expressions over numbered symbols with pattern variables: the assumed
carrier of the mm2 point, and an adequate memo-level stand-in for the zero
carrier (the runtime's `Pattern` type is the real one). -/
inductive SExprVar where
  | sym : Nat → SExprVar
  | var : Nat → SExprVar
  | cons : SExprVar → SExprVar → SExprVar
  deriving DecidableEq, Repr

/-- A carrier-indexed candidate: `Carrier` is the data the language computes
over; `capabilities` is the declared capability set.  Distinct carriers give
distinct (incomparable-by-type) families, which is exactly the intended
"family of zeros" structure. -/
structure Candidate (Carrier : Type u) where
  name : String
  capabilities : List CoreCapability

/-- `Subsumes stronger weaker`: every declared capability of `weaker` is
declared by `stronger`. -/
def Subsumes {Carrier : Type u} (stronger weaker : Candidate Carrier) : Prop :=
  ∀ cap ∈ weaker.capabilities, cap ∈ stronger.capabilities

instance {Carrier : Type u} (s w : Candidate Carrier) :
    Decidable (Subsumes s w) :=
  List.decidableBAll _ _

/-! ## §2 The lattice: zero, zero-prime, prime, and the mm2 point -/

/-- The match/let/emit zero: minimal but cost-honest (sharing) and
act-capable (emit). -/
def zeroCandidate : Candidate SExprVar where
  name := "zero-match-let-emit"
  capabilities :=
    [.patternMatch, .explicitSharing, .actEmit,
     .collections, .metavariables, .inertUnknowns]

/-- Zero-prime: zero extended with named (rho-style) abstraction.  A rung
strictly between zero and prime — abstraction eases the correspondence with
the lambda-shaped type-theoretic core, at the price of no longer being
minimal. -/
def zeroPrimeCandidate : Candidate SExprVar where
  name := "zero-prime"
  capabilities := zeroCandidate.capabilities ++ [.namedAbstraction]

/-- The mm2 point as declared: fused `exec` instead of separate
match/let/emit, over S-expressions with variables. -/
def mm2Candidate : Candidate SExprVar where
  name := "mm2"
  capabilities := [.fusedExec, .collections, .metavariables, .inertUnknowns]

/-- The prime point: every capability in the current enumeration. -/
def primeCandidate : Candidate SExprVar where
  name := "prime"
  capabilities :=
    [.patternMatch, .explicitSharing, .actEmit, .collections,
     .metavariables, .inertUnknowns, .namedAbstraction, .fusedExec]

/-- Zero-prime subsumes zero. -/
theorem zeroPrime_subsumes_zero :
    Subsumes zeroPrimeCandidate zeroCandidate := by decide

/-- The inclusion is strict: zero lacks named abstraction. -/
theorem zero_not_subsumes_zeroPrime :
    ¬ Subsumes zeroCandidate zeroPrimeCandidate := by decide

/-- Prime subsumes zero-prime (and hence zero). -/
theorem prime_subsumes_zeroPrime :
    Subsumes primeCandidate zeroPrimeCandidate := by decide

/-- As *declared*, mm2 and zero are incomparable: mm2 lacks the separate
match/sharing/emit capabilities, zero lacks fused exec.  This is the honest
pre-debate state. -/
theorem mm2_zero_incomparable_as_declared :
    ¬ Subsumes mm2Candidate zeroCandidate ∧
      ¬ Subsumes zeroCandidate mm2Candidate := by decide

/-- The debated semantic claim about `exec`, as data: one fused primitive
that matches, uses its bindings (sharing), and emits.  Whether this expansion
is semantically faithful to mm2's two-rule specification is the open question
Q1 — the combinatorial consequences below are proved unconditionally. -/
def expandExec : CoreCapability → List CoreCapability
  | .fusedExec => [.patternMatch, .explicitSharing, .actEmit]
  | c => [c]

/-- Capabilities after granting the exec expansion. -/
def effectiveCapabilities {Carrier : Type u} (c : Candidate Carrier) :
    List CoreCapability :=
  c.capabilities.foldr (fun cap acc => expandExec cap ++ acc) []

/-- IF the exec expansion is semantically justified, mm2's effective
capabilities cover all of zero's: mm2 would then sit at-or-above zero in the
family. -/
theorem mm2_effective_covers_zero :
    ∀ cap ∈ zeroCandidate.capabilities,
      cap ∈ effectiveCapabilities mm2Candidate := by decide

/-- Even granting the exec expansion, zero-prime exceeds mm2: named
abstraction is not recoverable from exec.  The zero-prime rung is genuinely
new. -/
theorem zeroPrime_exceeds_mm2_even_effectively :
    ∃ cap ∈ zeroPrimeCandidate.capabilities,
      cap ∉ effectiveCapabilities mm2Candidate := by decide

/-! ## §3 Miniature raw core

Just enough syntax to prove the placement theorems concretely: numbered
symbols, de Bruijn variables, pairing, `let`, and quotation. -/

inductive MiniTm where
  | var : Nat → MiniTm
  | sym : Nat → MiniTm
  | pair : MiniTm → MiniTm → MiniTm
  /-- `lett e b` is `let x = e in b` with `b` binding de Bruijn index 0. -/
  | lett : MiniTm → MiniTm → MiniTm
  | quote : MiniTm → MiniTm
  deriving DecidableEq, Repr

namespace MiniTm

/-- Shift free variables at or above cutoff `d`. -/
def shift (d : Nat) : MiniTm → MiniTm
  | .var n => .var (if n < d then n else n + 1)
  | .sym s => .sym s
  | .pair a b => .pair (shift d a) (shift d b)
  | .lett a b => .lett (shift d a) (shift (d + 1) b)
  | .quote t => .quote (shift d t)

/-- Capture-avoiding substitution of `e` for de Bruijn index `k`. -/
def substAt (k : Nat) (e : MiniTm) : MiniTm → MiniTm
  | .var n =>
      if n = k then e else if n > k then .var (n - 1) else .var n
  | .sym s => .sym s
  | .pair a b => .pair (substAt k e a) (substAt k e b)
  | .lett a b => .lett (substAt k e a) (substAt (k + 1) (shift 0 e) b)
  | .quote t => .quote (substAt k e t)

/-- Syntactic size: the memo's stand-in cost measure. -/
def size : MiniTm → Nat
  | .var _ => 1
  | .sym _ => 1
  | .pair a b => size a + size b + 1
  | .lett a b => size a + size b + 1
  | .quote t => size t + 1

/-- Quotation nesting level. -/
def level : MiniTm → Nat
  | .var _ => 0
  | .sym _ => 0
  | .pair a b => max (level a) (level b)
  | .lett a b => max (level a) (level b)
  | .quote t => level t + 1

end MiniTm

/-- One-step let inlining: `let x = e in b  ↦  b[x := e]`.  Any equality
profile validating sharing-inlining must relate such pairs. -/
inductive LetInline : MiniTm → MiniTm → Prop where
  | inline (e b : MiniTm) : LetInline (.lett e b) (MiniTm.substAt 0 e b)

/-! ## §4 The placement theorems: cost and evidence live RAW

These are the load-bearing design facts.  They are the same
projection/factoring pattern throughout: the raw object is real, the quotient
is a lossy projection, and whether an interpretation factors through the
projection is a theorem, never an assumption. -/

/-- Sharing is cost-real: inlining a shared subterm can strictly *increase*
size.  Witness: `let x = e in (x, x)` versus `(e, e)`. -/
theorem sharing_is_cost_real :
    ∃ t t', LetInline t t' ∧ MiniTm.size t < MiniTm.size t' := by
  refine ⟨_, _,
    LetInline.inline (.pair (.sym 0) (.pair (.sym 0) (.sym 0)))
      (.pair (.var 0) (.var 0)), ?_⟩
  decide

/-- Inlining can also strictly *decrease* size (a dead `let`).  Together with
`sharing_is_cost_real`, cost moves in both directions across the equation. -/
theorem inlining_can_shrink :
    ∃ t t', LetInline t t' ∧ MiniTm.size t' < MiniTm.size t := by
  refine ⟨_, _, LetInline.inline (.sym 0) (.sym 1), ?_⟩
  decide

/-- **Cost does not factor through the equality profile.**  Any profile
validating let-inlining relates terms of different cost, so cost
interpretations must be algebras over raw syntax, below every such
quotient. -/
theorem cost_not_profile_invariant :
    ∃ t t', LetInline t t' ∧ MiniTm.size t ≠ MiniTm.size t' := by
  obtain ⟨t, t', hstep, hlt⟩ := sharing_is_cost_real
  exact ⟨t, t', hstep, Nat.ne_of_lt hlt⟩

/-- **Evidence does not factor through deduplication.**  Two distinct
derivation bags with the same underlying truth set: bag (evidence-counting)
semantics distinguishes what set (truth) semantics identifies, so evidence
lives on raw derivations and truth-level readouts are lossy projections. -/
theorem evidence_bag_finer_than_truth_set :
    ∃ a b : Multiset Nat, a ≠ b ∧ a.dedup = b.dedup := by
  refine ⟨0 ::ₘ {0}, {0}, ?_, ?_⟩
  · intro h
    have hcard := congrArg Multiset.card h
    simp at hcard
  · rw [Multiset.dedup_cons_of_mem (by simp)]

/-- **Quotation strictly raises level**: the syntactic no-same-level-reflection
discipline, stated computationally. -/
theorem quote_strictly_raises (t : MiniTm) :
    MiniTm.level (.quote t) = MiniTm.level t + 1 := rfl

/-- No term is its own quotation: syntactic self-reference at a single level
is unrepresentable. -/
theorem no_syntactic_self_quotation (t : MiniTm) : MiniTm.quote t ≠ t := by
  intro h
  have hs := congrArg MiniTm.size h
  simp only [MiniTm.size] at hs
  omega

/-! ## §5 Acceptance shapes for the Pure-layer improvements

Uninstantiated structures are completion targets (building the instance is
the work); each carries a nontriviality field so a degenerate instance is
unrepresentable. -/

/-- Acceptance shape for the graded-fold improvement: a cost algebra over a
raw syntax, with a monoidal grade and a measure.  The real-layer port must
additionally make the grade compositional along substitution. -/
structure GradedCostAlgebra (Tm : Type u) where
  Grade : Type v
  unit : Grade
  mul : Grade → Grade → Grade
  unit_mul : ∀ g, mul unit g = g
  mul_unit : ∀ g, mul g unit = g
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  measure : Tm → Grade
  /-- Blocks the constant-grade discharge. -/
  nondegenerate : ∃ a b : Tm, measure a ≠ measure b

/-- Positive instance: the miniature core with size grading.  The shape is
inhabited, so demanding it of the real layer is not vacuous. -/
def miniSizeAlgebra : GradedCostAlgebra MiniTm where
  Grade := Nat
  unit := 0
  mul := (· + ·)
  unit_mul := Nat.zero_add
  mul_unit := Nat.add_zero
  mul_assoc := Nat.add_assoc
  measure := MiniTm.size
  nondegenerate := ⟨.sym 0, .pair (.sym 0) (.sym 0), by decide⟩

/-- Acceptance shape for the operational↔type-theoretic core correspondence
(zero against the lambda-shaped raw core): a retraction with an explicitly
bounded cost overhead.  `nontrivial` blocks the empty and single-point
discharges. -/
structure CoreCorrespondence (Op TT : Type u) where
  encode : Op → TT
  decode : TT → Op
  decode_encode : ∀ p, decode (encode p) = p
  costOp : Op → Nat
  costTT : TT → Nat
  overhead : Nat
  cost_bounded : ∀ p, costTT (encode p) ≤ overhead * costOp p + overhead
  nontrivial : ∃ p q : Op, p ≠ q

/-! ## §6 Open-question ledger -/

def openDesignQuestions : List String :=
  [ "Q1-exec-subsumption: decide whether mm2's fused exec semantically \
     provides pattern-match + sharing + emit (justifying expandExec), \
     against its two-rule unification/S-expression specification"
  , "Q2-mm21-sinks: formalize the variant that schedules exec at the sinks; \
     compare description length against behavioral complexity honestly"
  , "Q3-zero-prime-calculus: the named-abstraction extension of zero — \
     operational rules, conservativity over zero, and its role as the \
     correspondence-friendly rung"
  , "Q4-zero-pure-correspondence: instantiate CoreCorrespondence between \
     the match/let/emit core and the lambda-shaped raw core, overhead \
     explicit; encoding may pass through the zero-prime rung"
  , "Q5-graded-fold-port: port GradedCostAlgebra to the real raw layer \
     with substitution-compositional grading and the raw-only placement \
     theorem generalizing cost_not_profile_invariant"
  , "Q6-evidence-adjunction: derivation-bag to truth-set adjunction on the \
     real raw layer, with the lossy strength-readout non-factoring witness \
     generalizing evidence_bag_finer_than_truth_set"
  , "Q7-quote-code-unification: one level-indexed quotation former serving \
     both staging and language codes, with the strict-level-raise law \
     generalizing quote_strictly_raises" ]

theorem openDesignQuestions_count : openDesignQuestions.length = 7 := rfl

end Mettapedia.Languages.MeTTa.ZeroFamilyPureDesign
