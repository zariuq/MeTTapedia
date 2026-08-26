import Mettapedia.Computability.KolmogorovComplexity.ConditionalInterpreter

/-!
# Plain conditional Kolmogorov complexity

This module places shortest-program reasoning on the computable conditional
interpreter constructed in `ConditionalInterpreter`.  It is intentionally named
*plain*: the universal interpreter has constant compiler overhead, but its raw
payload program is not claimed to be self-delimiting.

The prefix-free theory remains separate.  Results in this file provide a checked
computability baseline and must not be substituted for prefix-complexity chain or
symmetry theorems.
-/

namespace KolmogorovComplexity

open scoped Classical

/-- Program lengths producing `x` under auxiliary condition `condition`. -/
def conditionalPlainLengthsFor
    (U : ConditionalAlgorithm) (condition x : BinString) : Set Nat :=
  {n | ∃ p : BinString, x ∈ U p condition ∧ p.length = n}

/-- Plain conditional complexity relative to `U`.  As in `plainComplexity`, the
infimum of an empty set of natural lengths is `0`; range premises are explicit in
all shortest-program and invariance results. -/
noncomputable def plainConditionalComplexity
    (U : ConditionalAlgorithm) (x condition : BinString) : Nat :=
  sInf (conditionalPlainLengthsFor U condition x)

notation "Cc[" U "](" x " | " condition ")" =>
  plainConditionalComplexity U x condition

theorem plainConditionalComplexity_le_of_program
    (U : ConditionalAlgorithm) (condition x p : BinString)
    (hp : x ∈ U p condition) :
    Cc[U](x | condition) ≤ p.length := by
  unfold plainConditionalComplexity
  exact Nat.sInf_le ⟨p, hp, rfl⟩

theorem exists_program_of_plainConditionalComplexity
    (U : ConditionalAlgorithm) (condition x : BinString)
    (h : ∃ p, x ∈ U p condition) :
    ∃ p, x ∈ U p condition ∧ p.length = Cc[U](x | condition) := by
  have hnonempty : (conditionalPlainLengthsFor U condition x).Nonempty := by
    obtain ⟨p, hp⟩ := h
    exact ⟨p.length, p, hp, rfl⟩
  have hminimum : Cc[U](x | condition) ∈ conditionalPlainLengthsFor U condition x := by
    simpa [plainConditionalComplexity] using Nat.sInf_mem hnonempty
  exact hminimum

/-- The total conditional algorithm that ignores both inputs and returns `x`. -/
def constantConditionalAlgorithm (x : BinString) : ConditionalAlgorithm :=
  fun _program _condition => Part.some x

theorem constantConditionalAlgorithm_partrec (x : BinString) :
    Partrec₂ (constantConditionalAlgorithm x) := by
  exact ((Computable.const x :
    Computable (fun _ : BinString × BinString => x)).partrec).to₂

/-- A universal conditional interpreter represents every finite output under
every auxiliary condition. -/
theorem universalConditional_hasProgram
    (U : ConditionalAlgorithm) (hU : IsUniversalConditional U)
    (condition x : BinString) :
    ∃ p, x ∈ U p condition := by
  obtain ⟨compilerPrefix, hcompiler⟩ :=
    hU (constantConditionalAlgorithm x) (constantConditionalAlgorithm_partrec x)
  refine ⟨compilerPrefix, ?_⟩
  have hx : x ∈ constantConditionalAlgorithm x [] condition := by
    simp [constantConditionalAlgorithm]
  simpa using hcompiler [] condition x hx

/-- One-sided invariance with an explicit compiler-prefix constant. -/
theorem universal_plainConditionalComplexity_le
    (U V : ConditionalAlgorithm)
    (hU : IsUniversalConditional U) (hVrec : Partrec₂ V) :
    ∃ c : Nat, ∀ condition x,
      (∃ p, x ∈ V p condition) →
      Cc[U](x | condition) ≤ Cc[V](x | condition) + c := by
  obtain ⟨compilerPrefix, hcompiler⟩ := hU V hVrec
  refine ⟨compilerPrefix.length, ?_⟩
  intro condition x hx
  obtain ⟨p, hp, hlength⟩ :=
    exists_program_of_plainConditionalComplexity V condition x hx
  have hcompiled : x ∈ U (compilerPrefix ++ p) condition :=
    hcompiler p condition x hp
  calc
    Cc[U](x | condition) ≤ (compilerPrefix ++ p).length :=
      plainConditionalComplexity_le_of_program U condition x _ hcompiled
    _ = compilerPrefix.length + p.length := by simp
    _ = Cc[V](x | condition) + compilerPrefix.length := by
      omega

/-- Two computable universal conditional interpreters agree up to explicit
two-sided additive constants. -/
theorem plainConditionalComplexity_invariance
    (U V : ConditionalAlgorithm)
    (hU : IsUniversalConditional U) (hUrec : Partrec₂ U)
    (hV : IsUniversalConditional V) (hVrec : Partrec₂ V) :
    ∃ c : Nat, ∀ condition x,
      |((Cc[U](x | condition) : Int) - Cc[V](x | condition))| ≤ (c : Int) := by
  obtain ⟨cUV, hUV⟩ := universal_plainConditionalComplexity_le U V hU hVrec
  obtain ⟨cVU, hVU⟩ := universal_plainConditionalComplexity_le V U hV hUrec
  refine ⟨max cUV cVU, ?_⟩
  intro condition x
  have hxU := universalConditional_hasProgram U hU condition x
  have hxV := universalConditional_hasProgram V hV condition x
  have huv := hUV condition x hxV
  have hvu := hVU condition x hxU
  rw [abs_le]
  constructor <;> omega

/-- The canonical computable plain conditional complexity used by later
computability controls. -/
noncomputable def canonicalPlainConditionalComplexity
    (x condition : BinString) : Nat :=
  Cc[universalConditionalAlgorithm](x | condition)

notation "Kplain(" x " | " condition ")" =>
  canonicalPlainConditionalComplexity x condition

theorem canonicalPlainConditional_hasProgram (condition x : BinString) :
    ∃ p, x ∈ universalConditionalAlgorithm p condition :=
  universalConditional_hasProgram universalConditionalAlgorithm
    universalConditionalAlgorithm_isUniversal condition x

/-- Directional information for the canonical *plain* conditional theory.
The integer codomain exposes rather than truncates machine-dependent additive
differences. -/
noncomputable def plainDirectedAlgorithmicInformation
    (condition x : BinString) : Int :=
  (Kplain(x | []) : Int) - Kplain(x | condition)

#print axioms exists_program_of_plainConditionalComplexity
#print axioms plainConditionalComplexity_invariance
#print axioms canonicalPlainConditional_hasProgram

end KolmogorovComplexity
