import Mettapedia.GSLT.Meredith.GSLT

/-!
# Bisimulation Quotient and Distinction Events

Building on Core's `GSLT.Bisimilar` (greatest bisimulation), this file adds:

1. **BisimQuotient** — the quotient `T(S) / ∼` as Lean's `Quotient`
2. **Distinction events** — pairs of non-bisimilar terms
3. **Induced rewriting** — the rewrite relation descends to the quotient
4. **Bridge to weakness** — distinction events as the domain for quantale weakness

## Key Idea (Meredith 2026)

"The true ontology of a GSLT is its bisimulation quotient."

Behavioral identity here is strong unlabeled bisimilarity, with matching
branching transitions. A finite-formula observational characterization needs
its own adequacy hypotheses; equality of finite trace sets alone does not
define this quotient. The distinction events — pairs (p,q) with p ≁ q —
provide a domain on which independently declared quantale weights can be used.

## References

- Meredith, "Computation, Causality, and Consciousness" (2026), §2, §5
- Milner, "Communication and Concurrency" (1989)
-/

namespace Mettapedia.GSLT.Meredith.Bisimulation

open Mettapedia.GSLT

/-! ## The Bisimulation Quotient -/

/-- The bisimulation quotient `T(S) / ∼`.

    Meredith: "the bisimulation quotient is the true ontology."
    Two terms are identified iff they are bisimilar (operationally indistinguishable).
-/
def BisimQuotient (S : GSLT) := Quotient S.bisimSetoid

/-- Project a term to its bisimulation equivalence class. -/
def toBisimClass (S : GSLT) (t : S.Term) : BisimQuotient S :=
  Quotient.mk S.bisimSetoid t

/-- Two terms have the same class iff they are bisimilar. -/
theorem bisimClass_eq_iff (S : GSLT) (p q : S.Term) :
    toBisimClass S p = toBisimClass S q ↔ S.Bisimilar p q :=
  Quotient.eq (r := S.bisimSetoid)

/-! ## Distinction Events -/

/-- Two terms are distinguished if they are NOT bisimilar.

    This is the key concept connecting to weakness:
    the distinction events are exactly the domain over which
    quantale weakness is computed.
-/
def IsDistinguished (S : GSLT) (p q : S.Term) : Prop :=
  ¬ S.Bisimilar p q

/-- Distinguished terms have different bisimulation classes. -/
theorem distinguished_classes_ne (S : GSLT) {p q : S.Term}
    (h : IsDistinguished S p q) : toBisimClass S p ≠ toBisimClass S q := by
  intro heq
  exact h ((bisimClass_eq_iff S p q).mp heq)

/-- Different bisimulation classes correspond to distinguished terms. -/
theorem ne_classes_distinguished (S : GSLT) {p q : S.Term}
    (h : toBisimClass S p ≠ toBisimClass S q) : IsDistinguished S p q := by
  intro hbis
  exact h ((bisimClass_eq_iff S p q).mpr hbis)

/-- Distinction is symmetric. -/
theorem isDistinguished_symm (S : GSLT) {p q : S.Term}
    (h : IsDistinguished S p q) : IsDistinguished S q p :=
  fun hbis => h (S.bisimilar_symm hbis)

/-- Distinction is irreflexive (no term is distinguished from itself). -/
theorem not_isDistinguished_self (S : GSLT) (p : S.Term) :
    ¬ IsDistinguished S p p :=
  fun h => h (S.bisimilar_refl p)

/-! ## Induced Rewriting on the Quotient

    A quotient step retains an actual pair of stepping representatives.
    Bisimilar sources have matching reductions to the same successor class.
    A chosen target representative need not itself be a reduct: target
    comparison is by bisimilarity, not by raw term equality.
-/

/-- Rewriting is compatible with bisimilarity: if `p ∼ q` and `p ⇝ p'`,
    then ∃ q' with `q ⇝ q'` and `p' ∼ q'`.

    This is just the forward half of bisimulation, restated.
-/
theorem rewrites_compat_bisimilar (S : GSLT) {p q p' : S.Term}
    (hbis : S.Bisimilar p q) (hstep : S.rewrites p p') :
    ∃ q', S.rewrites q q' ∧ S.Bisimilar p' q' := by
  obtain ⟨R, ⟨hfwd, _⟩, hpq⟩ := hbis
  obtain ⟨q', hstep', hR'⟩ := hfwd hpq hstep
  exact ⟨q', hstep', R, ⟨hfwd, ‹_›⟩, hR'⟩

/-- A one-step reduction between behavioral classes has actual stepping
representatives. No exact-target saturation of the authored relation is
assumed beyond its equation response laws. -/
def quotientStep (S : GSLT) (source target : BisimQuotient S) : Prop :=
  ∃ redex contractum : S.Term,
    toBisimClass S redex = source ∧ S.Step redex contractum ∧
      toBisimClass S contractum = target

/-- Every authored one-step reduction projects to one quotient step. -/
theorem quotientStep_mk {S : GSLT} {source target : S.Term}
    (step : S.Step source target) :
    quotientStep S (toBisimClass S source) (toBisimClass S target) :=
  ⟨source, target, rfl, step, rfl⟩

/-- Every step leaving a source class can be lifted from any chosen source
representative. The lifted target lies in the prescribed behavioral class. -/
theorem quotientStep_from_class_iff (S : GSLT) (source : S.Term)
    (target : BisimQuotient S) :
    quotientStep S (toBisimClass S source) target ↔
      ∃ contractum : S.Term, S.Step source contractum ∧
        toBisimClass S contractum = target := by
  constructor
  · rintro ⟨redex, contractum, sourceClass, step, targetClass⟩
    obtain ⟨lifted, liftedStep, targetBisimilar⟩ :=
      rewrites_compat_bisimilar S ((bisimClass_eq_iff S _ _).mp sourceClass) step
    refine ⟨lifted, liftedStep, ?_⟩
    exact ((bisimClass_eq_iff S _ _).mpr (S.bisimilar_symm targetBisimilar)).trans
      targetClass
  · rintro ⟨contractum, step, targetClass⟩
    exact ⟨source, contractum, rfl, step, targetClass⟩

/-- Projection reflects reduction up to target bisimilarity, not exact
target equality. This is the representative-independent reading of a step. -/
theorem quotientStep_mk_iff (S : GSLT) (source target : S.Term) :
    quotientStep S (toBisimClass S source) (toBisimClass S target) ↔
      ∃ contractum : S.Term, S.Step source contractum ∧
        S.Bisimilar contractum target := by
  rw [quotientStep_from_class_iff]
  exact exists_congr fun contractum =>
    and_congr_right fun _ => bisimClass_eq_iff S contractum target

/-- Replacing either authored representative by a bisimilar one leaves the
quotient reduction unchanged. -/
theorem quotientStep_representative_independent (S : GSLT)
    {source source' target target' : S.Term}
    (sources : S.Bisimilar source source') (targets : S.Bisimilar target target') :
    quotientStep S (toBisimClass S source) (toBisimClass S target) ↔
      quotientStep S (toBisimClass S source') (toBisimClass S target') := by
  rw [(bisimClass_eq_iff S source source').mpr sources,
    (bisimClass_eq_iff S target target').mpr targets]

/-- Every finite computation projects to a path of behavioral classes. -/
theorem quotientPath_mk {S : GSLT} {source target : S.Term}
    (path : Relation.ReflTransGen S.Step source target) :
    Relation.ReflTransGen (quotientStep S)
      (toBisimClass S source) (toBisimClass S target) :=
  path.lift (toBisimClass S) (fun _ _ step => quotientStep_mk step)

/-- A finite path of behavioral classes lifts from any chosen source
representative. Every lifted edge is an actual one-step computation, while
the endpoint is compared by its class. This does not select an exact target
representative or identify the resource receipts of matching computations. -/
theorem quotientPath_from_class_iff (S : GSLT) (source : S.Term)
    (target : BisimQuotient S) :
    Relation.ReflTransGen (quotientStep S) (toBisimClass S source) target ↔
      ∃ contractum : S.Term, Relation.ReflTransGen S.Step source contractum ∧
        toBisimClass S contractum = target := by
  constructor
  · intro path
    induction path with
    | refl => exact ⟨source, .refl, rfl⟩
    | @tail previous next _ edge lifted =>
        obtain ⟨representative, actualPath, sameClass⟩ := lifted
        rw [← sameClass] at edge
        obtain ⟨contractum, actualStep, targetClass⟩ :=
          (quotientStep_from_class_iff S representative next).mp edge
        exact ⟨contractum, actualPath.tail actualStep, targetClass⟩
  · rintro ⟨contractum, path, targetClass⟩
    exact targetClass ▸ quotientPath_mk path

/-- Finite quotient reachability reflects actual computation up to target
bisimilarity, extending the one-step representative law. -/
theorem quotientPath_mk_iff (S : GSLT) (source target : S.Term) :
    Relation.ReflTransGen (quotientStep S)
        (toBisimClass S source) (toBisimClass S target) ↔
      ∃ contractum : S.Term, Relation.ReflTransGen S.Step source contractum ∧
        S.Bisimilar contractum target := by
  rw [quotientPath_from_class_iff]
  exact exists_congr fun contractum =>
    and_congr_right fun _ => bisimClass_eq_iff S contractum target

/-! ### An exact-target boundary

The four-state graph carries a phase bit and an identity bit. Each phase-false
state steps to the phase-true state with the same identity bit. Bisimilarity
forgets identity, but raw reduction does not. -/

namespace QuotientStepControls

/-- Two sources reduce to different terminal states; equations are equality. -/
def theory : GSLT where
  Term := Bool × Bool
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun source target => source.1 = false ∧ target = (true, source.2)
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

/-- The identity bit is not observed by the graph's transitions. -/
theorem bisimilar_of_same_phase {left right : Bool × Bool}
    (phase : left.1 = right.1) : theory.Bisimilar left right := by
  refine ⟨fun first second => first.1 = second.1, ⟨?_, ?_⟩, phase⟩
  · intro first second related next step
    change first.1 = false ∧ next = (true, first.2) at step
    rcases step with ⟨firstPhase, rfl⟩
    refine ⟨(true, second.2), ?_, rfl⟩
    exact ⟨related.symm.trans firstPhase, rfl⟩
  · intro first second related next step
    change second.1 = false ∧ next = (true, second.2) at step
    rcases step with ⟨secondPhase, rfl⟩
    refine ⟨(true, first.2), ?_, rfl⟩
    exact ⟨related.trans secondPhase, rfl⟩

/-- An actual reduction projects to a nonempty quotient reduction. -/
theorem projected_step :
    quotientStep theory (toBisimClass theory (false, false))
      (toBisimClass theory (true, false)) :=
  quotientStep_mk ⟨rfl, rfl⟩

/-- Raw exact-target stepping differs between bisimilar representatives,
while the quotient step is unchanged. -/
theorem raw_target_not_representative_independent :
    theory.Bisimilar (false, false) (false, true) ∧
      theory.Step (false, false) (true, false) ∧
      ¬ theory.Step (false, true) (true, false) ∧
      quotientStep theory (toBisimClass theory (false, true))
        (toBisimClass theory (true, false)) := by
  refine ⟨bisimilar_of_same_phase rfl, ⟨rfl, rfl⟩, ?_, ?_⟩
  · intro step
    exact Bool.noConfusion (congrArg Prod.snd step.2)
  · exact (quotientStep_mk_iff theory _ _).mpr
      ⟨(true, true), ⟨rfl, rfl⟩, bisimilar_of_same_phase rfl⟩

/-- A nonempty computation lifts to the requested terminal class even when
the chosen terminal representative cannot be reached from this source. -/
theorem quotient_path_does_not_require_exact_target :
    Relation.ReflTransGen (quotientStep theory)
        (toBisimClass theory (false, true)) (toBisimClass theory (true, false)) ∧
      ¬ Relation.ReflTransGen theory.Step (false, true) (true, false) := by
  refine ⟨.tail .refl raw_target_not_representative_independent.2.2.2, ?_⟩
  intro path
  have identityPreserved : ∀ {source target : Bool × Bool},
      Relation.ReflTransGen theory.Step source target → source.2 = target.2 := by
    intro source target computation
    induction computation with
    | refl => rfl
    | tail _ step sameIdentity =>
        exact sameIdentity.trans (congrArg Prod.snd step.2).symm
  exact Bool.noConfusion (identityPreserved path)

/-- The source and terminal classes remain distinct: the behavioral quotient
is neither a constant carrier nor a relation with all steps erased. -/
theorem source_and_terminal_classes_distinct :
    toBisimClass theory (false, false) ≠ toBisimClass theory (true, true) := by
  intro equal
  obtain ⟨next, terminalStep, _⟩ := rewrites_compat_bisimilar theory
    ((bisimClass_eq_iff theory _ _).mp equal)
    (show theory.Step (false, false) (true, false) from ⟨rfl, rfl⟩)
  exact Bool.noConfusion terminalStep.1

/-- A behavioral morphism can send an actual nonempty reduction to a
terminal class. Preserving bisimilarity alone is therefore not an operational
simulation or a proof that quotient reductions are transported. -/
theorem behavioral_morphism_need_not_preserve_quotient_steps :
    ∃ map : GSLT.Morphism theory theory,
      theory.Step (false, false) (true, false) ∧
        ¬ quotientStep theory
          (toBisimClass theory (map.toFun (false, false)))
          (toBisimClass theory (map.toFun (true, false))) := by
  refine ⟨{ toFun := fun _ => (true, false)
            preserves_bisim := fun _ => theory.bisimilar_refl _ },
    ⟨rfl, rfl⟩, ?_⟩
  intro quotientReduction
  obtain ⟨contractum, step, _⟩ :=
    (quotientStep_from_class_iff theory (true, false) _).mp quotientReduction
  exact Bool.noConfusion step.1

end QuotientStepControls

#print axioms quotientStep_from_class_iff
#print axioms quotientStep_mk_iff
#print axioms quotientStep_representative_independent
#print axioms quotientPath_mk
#print axioms quotientPath_from_class_iff
#print axioms quotientPath_mk_iff
#print axioms QuotientStepControls.raw_target_not_representative_independent
#print axioms QuotientStepControls.quotient_path_does_not_require_exact_target
#print axioms QuotientStepControls.source_and_terminal_classes_distinct
#print axioms QuotientStepControls.behavioral_morphism_need_not_preserve_quotient_steps

/-! ## Bridge to Quantale Weakness

    The quantale weakness framework (`Mettapedia.Algebra.QuantaleWeakness`)
    computes weakness over `Finset (U × U)` given a weight function `U → Q`.

    For a GSLT with a finite bisimulation quotient:
    - `U = BisimQuotient S` (the true ontology)
    - Weight function `μ : U → Q` assigns evidence/probability to each class
    - Distinction event = `{(u, v) | u ≠ v}` ⊆ U × U
    - Non-distinction event = `{(u, u) | u ∈ U}` (diagonal)
    - `weakness(distinction)` measures overall distinguishability
    - `weakness(non-distinction)` = the "self-similarity" measure

    The weakness of the distinction event is exactly Bennett's/Ellerman's
    logical entropy when `Q = ℝ≥0∞` and `μ` is a probability distribution.

    This connects operational distinctions to an evidence algebra through
    the independently supplied class weights. Bisimilarity itself assigns
    no evidence strength, probability, or resource cost.
-/

/-  `IsDistinguished` is defined as `¬ S.Bisimilar`, so the complement
observation is currently definitional. We keep that fact as an unfolding of the
definition rather than packaging it as a standalone theorem with no proof
content. -/

/-! ## GSLT Morphisms and the Quotient

    Morphisms descend to the quotient because they preserve bisimilarity.
-/

/-- A GSLT morphism induces a map on bisimulation quotients. -/
def quotientMap {S S' : GSLT} (f : GSLT.Morphism S S') :
    BisimQuotient S → BisimQuotient S' :=
  Quotient.map f.toFun (fun _ _ h => f.preserves_bisim h)

/-- The quotient map respects the projection. -/
theorem quotientMap_comm {S S' : GSLT} (f : GSLT.Morphism S S') (t : S.Term) :
    quotientMap f (toBisimClass S t) = toBisimClass S' (f.toFun t) :=
  rfl

-- NOTE: Quotient map does NOT preserve distinction in general —
-- morphisms can merge distinct classes. Preservation holds for
-- injective-on-quotient morphisms (embeddings).

end Mettapedia.GSLT.Meredith.Bisimulation
