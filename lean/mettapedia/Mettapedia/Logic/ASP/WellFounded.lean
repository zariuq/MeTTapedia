import Mettapedia.Logic.ASP.Checker
import Mettapedia.Logic.ASP.Approximation
import Mettapedia.GSLT.OpenEnded.PrologContrasts

/-!
# Approximation fixpoint theory for normal programs

The generic algebra of `Approximation`, instantiated to a program `P` over the
lattice `Set A`.

## Fitting's four-valued operator

`Program.fitting P` sends a pair `(x, y)` (certainly true, possibly true) to
`(step P x y, step P y x)`: a head is certainly true when some rule's positive
body is certainly true and its negated atoms are certainly false, and possibly
true when some rule's body is possibly true. It is a symmetric approximator
(`fitting_symmetric`) of the two-valued operator `M ↦ step P M M`
(`fitting_approximates`). Its lower operator at `y` is the reduct operator
(`stableLower_fitting`), so:

* its exact fixpoints are the supported models (`fitting_exact_fixed_iff`);
* its exact stable fixpoints are the Gelfond–Lifschitz stable models of
  `Kernel` (`stable_iff_isStableFixpoint`);
* its Kripke–Kleene fixpoint approximates every supported model
  (`kripkeKleeneModel_approximates`), and is the least evidence state of
  `PrologContrasts.evidenceStep` with every definition complete
  (`leastEvidence_eq_kripkeKleeneModel`);
* its well-founded fixpoint approximates every stable model
  (`wellFoundedModel_approximates`). This is the solver's sound preprocessing:
  atoms below the lower bound can be set true and atoms outside the upper bound
  false without losing a stable model. Both fixpoints are consistent; an exact
  well-founded fixpoint is the unique stable model
  (`stable_iff_of_wellFoundedModel_eq`).

## The well-founded model by unfounded sets

Van Gelder, Ross and Schlipf define the well-founded model over partial
interpretations `(T, F)` (atoms true, atoms false), ordered by knowledge. A set
`U` is **unfounded** with respect to `(T, F)` when every rule for an atom of `U`
has a body false in `(T, F)` or a positive body atom in `U` (`Unfounded`).
Unfounded sets are closed under unions (`unfounded_sUnion`), so there is a
greatest one (`greatestUnfounded`). Their operator `W_P(T, F) = (T_P(T, F),
U_P(T, F))` is monotone (`vgrs`), and its least fixed point (`vgrsModel`) is the
well-founded fixpoint of Fitting's operator, read as true and false atoms
(`vgrsModel_eq`). The proof is two prefixed points: the well-founded fixpoint is
a prefixed point of `W_P`, and the least fixed point of `W_P` is a prefixed
point of the stable operator.

## Computed

`Program.kripkeKleeneFin` and `Program.wellFoundedFin` iterate the two operators
on pairs of finite sets, from `(∅, heads)`, `2 · |heads|` times; that many steps
reach the fixed point (a strictly increasing measure bounded by `2 · |heads|`),
and the results are the two fixpoints (`coe_kripkeKleeneFin`,
`coe_wellFoundedFin`).

Reference: Denecker, Marek and Truszczyński, "Approximations, stable operators,
well-founded fixpoints and applications in nonmonotonic reasoning" (2000);
Van Gelder, Ross and Schlipf, "The well-founded semantics for general logic
programs" (JACM 1991).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ASP

open AFT AFT.Approx OrderDual

universe u

variable {A : Type u}

namespace Program

variable (P : Program A)

/-- **Fitting's four-valued immediate-consequence operator** on pairs (certainly true,
possibly true). -/
def fitting : Approx (Set A) →o Approx (Set A) where
  toFun p := mk (P.step p.lower p.upper) (P.step p.upper p.lower)
  monotone' _ _ h := ⟨P.step_mono h.1 h.2, P.step_mono h.2 h.1⟩

@[simp] theorem fitting_lower (p : Approx (Set A)) : (P.fitting p).lower = P.step p.lower p.upper := rfl
@[simp] theorem fitting_upper (p : Approx (Set A)) : (P.fitting p).upper = P.step p.upper p.lower := rfl

theorem fitting_symmetric : IsSymmetric P.fitting := fun _ _ => rfl

theorem fitting_approximates : Approximates P.fitting fun M => P.step M M := fun _ => rfl

theorem stableLower_fitting (y : Set A) : stableLower P.fitting y = P.glOp y := rfl

theorem stableUpper_fitting (x : Set A) : stableUpper P.fitting x = P.glOp x :=
  stableUpper_eq P.fitting_symmetric x

/-- The stable operator of Fitting's operator is the alternating Gelfond–Lifschitz operator. -/
theorem stableOp_fitting (p : Approx (Set A)) :
    stableOp P.fitting p = mk (P.glOp p.upper) (P.glOp p.lower) :=
  Approx.ext rfl (P.stableUpper_fitting _)

/-- Exact fixpoints of Fitting's operator are the supported models. -/
theorem fitting_exact_fixed_iff (M : Set A) : P.fitting (exact M) = exact M ↔ P.Supported M :=
  ⟨fun h => congrArg Approx.lower h, fun h => Approx.ext h h⟩

/-- **Exact stable fixpoints are the stable models.** -/
theorem stable_iff_isStableFixpoint (M : Set A) : P.Stable M ↔ IsStableFixpoint P.fitting (exact M) := by
  rw [isStableFixpoint_exact_iff_symm P.fitting_symmetric, stableLower_fitting, Stable, eq_comm]

/-- The Kripke–Kleene model: the least precise fixpoint of Fitting's operator. -/
def kripkeKleeneModel : Approx (Set A) := kripkeKleene P.fitting

/-- The well-founded model: the least precise fixpoint of the stable operator. -/
def wellFoundedModel : Approx (Set A) := wellFounded P.fitting

theorem kripkeKleeneModel_approximates {M : Set A} (h : P.Supported M) :
    P.kripkeKleeneModel.lower ⊆ M ∧ M ⊆ P.kripkeKleeneModel.upper :=
  le_exact_iff.mp (kripkeKleene_le_fixed ((P.fitting_exact_fixed_iff M).mpr h))

/-- **The well-founded model approximates every stable model.** -/
theorem wellFoundedModel_approximates {M : Set A} (h : P.Stable M) :
    P.wellFoundedModel.lower ⊆ M ∧ M ⊆ P.wellFoundedModel.upper :=
  le_exact_iff.mp (wellFounded_le ((P.stable_iff_isStableFixpoint M).mp h))

theorem kripkeKleeneModel_le_wellFoundedModel : P.kripkeKleeneModel ≤ P.wellFoundedModel :=
  kripkeKleene_le_wellFounded

theorem kripkeKleeneModel_consistent : P.kripkeKleeneModel.lower ⊆ P.kripkeKleeneModel.upper :=
  kripkeKleene_consistent P.fitting_symmetric

theorem wellFoundedModel_consistent : P.wellFoundedModel.lower ⊆ P.wellFoundedModel.upper :=
  wellFounded_consistent P.fitting_symmetric

/-- An exact well-founded model is the unique stable model. -/
theorem stable_iff_of_wellFoundedModel_eq {W : Set A} (h : P.wellFoundedModel = exact W) (M : Set A) :
    P.Stable M ↔ M = W := by
  rw [stable_iff_isStableFixpoint]
  exact exact_stable_iff_of_wellFounded_eq h M

/-- The bounds of the well-founded model are the Gelfond–Lifschitz revisions of each other. -/
theorem wellFoundedModel_lower : P.glOp P.wellFoundedModel.upper = P.wellFoundedModel.lower := by
  have := congrArg Approx.lower (wellFounded_isStableFixpoint (A := P.fitting))
  rw [stableOp_fitting] at this
  exact this

theorem wellFoundedModel_upper : P.glOp P.wellFoundedModel.lower = P.wellFoundedModel.upper := by
  have := congrArg Approx.upper (wellFounded_isStableFixpoint (A := P.fitting))
  rw [stableOp_fitting] at this
  exact this

/-! ## Unfounded sets and the operator of Van Gelder, Ross and Schlipf -/

/-- The body of `r` is true in the partial interpretation `(T, F)`. -/
def TrueIn (r : Rule A) (T F : Set A) : Prop := (∀ b ∈ r.pos, b ∈ T) ∧ ∀ b ∈ r.neg, b ∈ F

/-- The body of `r` is false in `(T, F)`: a positive atom is false or a negated atom is true. -/
def FalseIn (r : Rule A) (T F : Set A) : Prop := (∃ b ∈ r.pos, b ∈ F) ∨ ∃ b ∈ r.neg, b ∈ T

/-- **Unfounded set**: every rule for an atom of `U` has a body false in `(T, F)` or a positive
body atom in `U`. -/
def Unfounded (T F U : Set A) : Prop :=
  ∀ r ∈ P, r.head ∈ U → FalseIn r T F ∨ ∃ b ∈ r.pos, b ∈ U

theorem unfounded_sUnion {T F : Set A} {𝒰 : Set (Set A)} (h : ∀ U ∈ 𝒰, P.Unfounded T F U) :
    P.Unfounded T F (⋃₀ 𝒰) := by
  rintro r hr ⟨U, hU, head⟩
  rcases h U hU r hr head with false | ⟨b, hb, inU⟩
  · exact Or.inl false
  · exact Or.inr ⟨b, hb, U, hU, inU⟩

theorem unfounded_mono {T F T' F' U : Set A} (hT : T ⊆ T') (hF : F ⊆ F') (h : P.Unfounded T F U) :
    P.Unfounded T' F' U := by
  intro r hr head
  rcases h r hr head with (⟨b, hb, inF⟩ | ⟨b, hb, inT⟩) | inside
  · exact Or.inl (Or.inl ⟨b, hb, hF inF⟩)
  · exact Or.inl (Or.inr ⟨b, hb, hT inT⟩)
  · exact Or.inr inside

/-- The greatest unfounded set with respect to `(T, F)`. -/
def greatestUnfounded (T F : Set A) : Set A := ⋃₀ {U | P.Unfounded T F U}

theorem unfounded_greatestUnfounded (T F : Set A) : P.Unfounded T F (P.greatestUnfounded T F) :=
  P.unfounded_sUnion fun _ h => h

theorem subset_greatestUnfounded {T F U : Set A} (h : P.Unfounded T F U) : U ⊆ P.greatestUnfounded T F :=
  Set.subset_sUnion_of_mem h

/-- Heads of rules whose bodies are true in `(T, F)`. -/
def trueStep (T F : Set A) : Set A := {a | ∃ r ∈ P, r.head = a ∧ TrueIn r T F}

theorem trueStep_eq (T F : Set A) : P.trueStep T F = P.step T Fᶜ := by
  ext a
  simp only [trueStep, step, TrueIn, Rule.Holds, Set.mem_ofPred_eq, Set.mem_compl_iff, not_not]

/-- **The operator `W_P` of Van Gelder, Ross and Schlipf** on partial interpretations
(true atoms, false atoms), ordered by knowledge. -/
def vgrs : Set A × Set A →o Set A × Set A where
  toFun I := (P.trueStep I.1 I.2, P.greatestUnfounded I.1 I.2)
  monotone' I J h := by
    refine ⟨?_, ?_⟩
    · rintro a ⟨r, hr, head, pos, neg⟩
      exact ⟨r, hr, head, fun b hb => h.1 (pos b hb), fun b hb => h.2 (neg b hb)⟩
    · exact P.subset_greatestUnfounded (P.unfounded_mono h.1 h.2 (P.unfounded_greatestUnfounded _ _))

/-- The well-founded model of Van Gelder, Ross and Schlipf: true atoms and false atoms. -/
def vgrsModel : Set A × Set A := P.vgrs.lfp

/-- **The well-founded fixpoint is the well-founded model**: its lower bound is the set of true
atoms, and the complement of its upper bound is the greatest unfounded set reached. -/
theorem vgrsModel_eq : P.vgrsModel = (P.wellFoundedModel.lower, P.wellFoundedModel.upperᶜ) := by
  set W := P.wellFoundedModel
  rcases hTF : P.vgrsModel with ⟨T, F⟩
  have fixed : P.vgrs (T, F) = (T, F) := hTF ▸ OrderHom.map_lfp _
  have fixedT : P.trueStep T F = T := congrArg Prod.fst fixed
  have fixedF : P.greatestUnfounded T F = F := congrArg Prod.snd fixed
  -- The well-founded fixpoint, read as true and false atoms, is a prefixed point of `W_P`.
  have first : P.vgrsModel ≤ (W.lower, W.upperᶜ) := by
    apply OrderHom.lfp_le
    refine ⟨?_, ?_⟩
    · change P.trueStep W.lower W.upperᶜ ⊆ W.lower
      rw [trueStep_eq, compl_compl, ← P.wellFoundedModel_lower, P.glOp_fixed, P.wellFoundedModel_lower]
    · change P.greatestUnfounded W.lower W.upperᶜ ⊆ W.upperᶜ
      apply Set.sUnion_subset
      intro U unfounded
      have closed : P.glOp W.lower ⊆ P.glOp W.lower \ U := by
        apply OrderHom.lfp_le
        rintro a ⟨r, hr, rfl, pos, neg⟩
        refine ⟨P.glOp_fixed W.lower ▸ ⟨r, hr, rfl, fun b hb => (pos b hb).1, neg⟩, fun inU => ?_⟩
        rcases unfounded r hr inU with (⟨b, hb, outside⟩ | ⟨b, hb, inT⟩) | ⟨b, hb, inside⟩
        · rw [Set.mem_compl_iff, ← P.wellFoundedModel_upper] at outside
          exact outside (pos b hb).1
        · exact neg b hb inT
        · exact (pos b hb).2 inside
      intro a inU inUpper
      rw [← P.wellFoundedModel_upper] at inUpper
      exact (closed inUpper).2 inU
  -- The least fixed point of `W_P`, read as a pair of bounds, is a prefixed point of the
  -- stable operator.
  have second : W ≤ mk T Fᶜ := by
    apply OrderHom.lfp_le
    rw [stableOp_fitting]
    refine ⟨?_, ?_⟩
    · change P.glOp Fᶜ ⊆ T
      apply OrderHom.lfp_le_fixed
      rw [reductOp_apply, ← trueStep_eq, fixedT]
    · change Fᶜ ⊆ P.glOp T
      rw [Set.compl_subset_comm, ← fixedF]
      apply P.subset_greatestUnfounded
      intro r hr head
      by_contra neither
      simp only [not_or, FalseIn, not_exists, not_and] at neither
      obtain ⟨⟨_, notTrue⟩, notInside⟩ := neither
      apply head
      rw [← P.glOp_fixed T]
      refine ⟨r, hr, rfl, fun b hb => ?_, fun b hb inT => notTrue b hb inT⟩
      by_contra absent
      exact notInside b hb absent
  rw [hTF] at first
  have lowerEq : T = W.lower := le_antisymm first.1 second.1
  have upperEq : F = W.upperᶜ := le_antisymm first.2 (Set.compl_subset_comm.mp second.2)
  rw [lowerEq, upperEq]

/-! ## Fitting's operator is the evidence operator of `PrologContrasts` -/

/-- The rules of `P` as rules with sets of body atoms. -/
def ruleSet : Set (GSLT.OpenEnded.PrologContrasts.NormalRule A) :=
  {rule | ∃ r ∈ P, rule = ⟨r.head, {b | b ∈ r.pos}, {b | b ∈ r.neg}⟩}

/-- Pairs of bounds as (established, refuted) evidence: precision becomes knowledge. -/
def knowledgeIso : Approx (Set A) ≃o Set A × Set A where
  toFun p := (p.lower, p.upperᶜ)
  invFun q := mk q.1 q.2ᶜ
  left_inv p := Approx.ext rfl (compl_compl _)
  right_inv q := Prod.ext rfl (compl_compl _)
  map_rel_iff' := by
    intro p q
    change (p.lower ⊆ q.lower ∧ p.upperᶜ ⊆ q.upperᶜ) ↔ (p.lower ⊆ q.lower ∧ q.upper ⊆ p.upper)
    rw [Set.compl_subset_compl]

/-- **Kripke–Kleene is the least evidence state**: with every definition declared complete,
`PrologContrasts.leastEvidence` is the Kripke–Kleene model, read as established and refuted
atoms. -/
theorem leastEvidence_eq_kripkeKleeneModel :
    GSLT.OpenEnded.PrologContrasts.leastEvidence P.ruleSet Set.univ = knowledgeIso P.kripkeKleeneModel := by
  apply OrderIso.lfp_conj
  intro p
  apply Prod.ext
  · ext a
    simp only [GSLT.OpenEnded.PrologContrasts.evidenceStep, ruleSet, OrderHom.coe_mk, knowledgeIso,
      RelIso.coe_fn_mk, Equiv.coe_fn_mk, fitting_lower, step, Rule.Holds, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨_, ⟨r, hr, rfl⟩, head, pos, neg⟩
      exact ⟨r, hr, head, fun b hb => pos hb, fun b hb => neg hb⟩
    · rintro ⟨r, hr, head, pos, neg⟩
      exact ⟨_, ⟨r, hr, rfl⟩, head, fun b hb => pos b hb, fun b hb => neg b hb⟩
  · ext a
    change (a ∈ Set.univ ∧ ∀ rule ∈ P.ruleSet, rule.head = a →
        (∃ x ∈ rule.pos, x ∈ p.upperᶜ) ∨ ∃ x ∈ rule.neg, x ∈ p.lower) ↔ a ∈ (P.step p.upper p.lower)ᶜ
    constructor
    · rintro ⟨_, blocked⟩ ⟨r, hr, head, pos, neg⟩
      rcases blocked _ ⟨r, hr, rfl⟩ head with ⟨b, hb, outside⟩ | ⟨b, hb, inside⟩
      · exact outside (pos b hb)
      · exact neg b hb inside
    · intro unsupported
      refine ⟨Set.mem_univ a, ?_⟩
      rintro _ ⟨r, hr, rfl⟩ head
      by_contra neither
      simp only [not_or, not_exists, not_and] at neither
      exact unsupported ⟨r, hr, head, fun b hb => Classical.byContradiction fun out => neither.1 b hb out,
        fun b hb => neither.2 b hb⟩

/-! ## Computed Kripke–Kleene and well-founded models -/

section Computed

variable [DecidableEq A]

/-- Pairs of finite sets (certainly true, possibly true), ordered by precision. -/
abbrev FinApprox (A : Type u) := Finset A × (Finset A)ᵒᵈ

/-- The pair of sets of a finite pair. -/
def FinApprox.toApprox (q : FinApprox A) : Approx (Set A) := mk ↑q.1 ↑(ofDual q.2)

/-- One step of Fitting's operator, computed. -/
def fittingFin (q : FinApprox A) : FinApprox A :=
  (P.stepFin q.1 (ofDual q.2), toDual (P.stepFin (ofDual q.2) q.1))

/-- One step of the stable operator, computed: two least models of reducts. -/
def stableFin (q : FinApprox A) : FinApprox A := (P.lfpFin (ofDual q.2), toDual (P.lfpFin q.1))

/-- The least precise pair inside the head atoms. -/
def startFin : FinApprox A := (∅, toDual P.heads)

theorem fittingFin_mono : Monotone P.fittingFin := by
  intro p q h
  refine ⟨?_, ?_⟩
  · change P.stepFin p.1 (ofDual p.2) ⊆ P.stepFin q.1 (ofDual q.2)
    rw [← Finset.coe_subset, coe_stepFin, coe_stepFin]
    exact P.step_mono (Finset.coe_subset.mpr h.1) (Finset.coe_subset.mpr h.2)
  · change P.stepFin (ofDual q.2) q.1 ⊆ P.stepFin (ofDual p.2) p.1
    rw [← Finset.coe_subset, coe_stepFin, coe_stepFin]
    exact P.step_mono (Finset.coe_subset.mpr h.2) (Finset.coe_subset.mpr h.1)

theorem stableFin_mono : Monotone P.stableFin := by
  intro p q h
  refine ⟨?_, ?_⟩
  · change P.lfpFin (ofDual p.2) ⊆ P.lfpFin (ofDual q.2)
    rw [← Finset.coe_subset, coe_lfpFin, coe_lfpFin]
    exact P.glOp_anti (Finset.coe_subset.mpr h.2)
  · change P.lfpFin q.1 ⊆ P.lfpFin p.1
    rw [← Finset.coe_subset, coe_lfpFin, coe_lfpFin]
    exact P.glOp_anti (Finset.coe_subset.mpr h.1)

theorem toApprox_fittingFin (q : FinApprox A) : (P.fittingFin q).toApprox = P.fitting q.toApprox :=
  Approx.ext (P.coe_stepFin _ _) (P.coe_stepFin _ _)

theorem toApprox_stableFin (q : FinApprox A) :
    (P.stableFin q).toApprox = stableOp P.fitting q.toApprox := by
  rw [stableOp_fitting]
  exact Approx.ext (P.coe_lfpFin _) (P.coe_lfpFin _)

/-- The measure that strict precision steps inside the head atoms raise. -/
def measureFin (q : FinApprox A) : ℕ := q.1.card + (P.heads \ ofDual q.2).card

theorem measureFin_lt {p q : FinApprox A} (lt : p < q) (inside : ofDual p.2 ⊆ P.heads) :
    P.measureFin p < P.measureFin q := by
  obtain ⟨le, notGe⟩ := lt_iff_le_not_ge.mp lt
  have lower : p.1.card ≤ q.1.card := Finset.card_le_card le.1
  have upper : (P.heads \ ofDual p.2).card ≤ (P.heads \ ofDual q.2).card :=
    Finset.card_le_card (Finset.sdiff_subset_sdiff (subset_refl _) le.2)
  by_cases same : q.1 ⊆ p.1
  · have strict : ofDual q.2 ⊂ ofDual p.2 := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨le.2, fun equal => notGe ⟨same, ?_⟩⟩
      change ofDual p.2 ⊆ ofDual q.2
      rw [equal]
    obtain ⟨a, inP, notQ⟩ := Finset.exists_of_ssubset strict
    have grows : (P.heads \ ofDual p.2).card < (P.heads \ ofDual q.2).card := by
      apply Finset.card_lt_card
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset_sdiff (subset_refl _) le.2, fun equal => ?_⟩
      have : a ∈ P.heads \ ofDual q.2 := Finset.mem_sdiff.mpr ⟨inside inP, notQ⟩
      rw [← equal] at this
      exact (Finset.mem_sdiff.mp this).2 inP
    unfold measureFin
    omega
  · have grows : p.1.card < q.1.card :=
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨le.1, fun equal => same (equal ▸ subset_refl _)⟩)
    unfold measureFin
    omega

theorem measureFin_le (q : FinApprox A) : P.measureFin q ≤ q.1.card + P.heads.card :=
  Nat.add_le_add_left (Finset.card_le_card Finset.sdiff_subset) _

/-- Iterating a monotone operator whose values lie in the head atoms, from `startFin`, reaches a
fixed point after `2 · |heads|` steps. -/
theorem iterate_startFin_fixed {f : FinApprox A → FinApprox A} (mono : Monotone f)
    (inside : ∀ q, (f q).1 ⊆ P.heads ∧ ofDual (f q).2 ⊆ P.heads)
    (start : P.startFin ≤ f P.startFin) :
    f (f^[2 * P.heads.card] P.startFin) = f^[2 * P.heads.card] P.startFin := by
  have within : ∀ k, (f^[k] P.startFin).1 ⊆ P.heads ∧ ofDual (f^[k] P.startFin).2 ⊆ P.heads := by
    intro k
    cases k with
    | zero => exact ⟨Finset.empty_subset _, subset_refl _⟩
    | succ k =>
      rw [Function.iterate_succ_apply']
      exact inside _
  apply iterate_fixed_of_measure mono start P.measureFin
  · exact fun k lt => P.measureFin_lt lt (within k).2
  · intro k
    have := P.measureFin_le (f^[k] P.startFin)
    have := Finset.card_le_card (within k).1
    omega

/-- The Kripke–Kleene model, computed. -/
def kripkeKleeneFin : FinApprox A := P.fittingFin^[2 * P.heads.card] P.startFin

/-- The well-founded model, computed: the alternating fixpoint. -/
def wellFoundedFin : FinApprox A := P.stableFin^[2 * P.heads.card] P.startFin

theorem startFin_le_wellFoundedModel : P.startFin.toApprox ≤ P.wellFoundedModel := by
  refine ⟨fun a ha => by simp [FinApprox.toApprox, startFin, mk] at ha, ?_⟩
  change P.wellFoundedModel.upper ⊆ ↑P.heads
  rw [coe_heads, ← P.wellFoundedModel_upper]
  exact P.glOp_subset_headSet _

theorem startFin_le_kripkeKleeneModel : P.startFin.toApprox ≤ P.kripkeKleeneModel := by
  refine ⟨fun a ha => by simp [FinApprox.toApprox, startFin, mk] at ha, ?_⟩
  change P.kripkeKleeneModel.upper ⊆ ↑P.heads
  have fixed := congrArg Approx.upper (OrderHom.map_lfp P.fitting)
  change P.step P.kripkeKleeneModel.upper P.kripkeKleeneModel.lower = P.kripkeKleeneModel.upper at fixed
  rw [coe_heads, ← fixed]
  exact P.step_subset_headSet _ _

/-- **The computed well-founded model is the well-founded model.** -/
theorem coe_wellFoundedFin : P.wellFoundedFin.toApprox = P.wellFoundedModel := by
  apply iterate_eq_lfp P.stableFin (stableOp P.fitting) FinApprox.toApprox P.toApprox_stableFin
    P.startFin_le_wellFoundedModel
  apply P.iterate_startFin_fixed P.stableFin_mono
  · exact fun q => ⟨P.lfpFin_subset_heads _, P.lfpFin_subset_heads _⟩
  · exact ⟨Finset.empty_subset _, P.lfpFin_subset_heads _⟩

/-- **The computed Kripke–Kleene model is the Kripke–Kleene model.** -/
theorem coe_kripkeKleeneFin : P.kripkeKleeneFin.toApprox = P.kripkeKleeneModel := by
  apply iterate_eq_lfp P.fittingFin P.fitting FinApprox.toApprox P.toApprox_fittingFin
    P.startFin_le_kripkeKleeneModel
  apply P.iterate_startFin_fixed P.fittingFin_mono
  · exact fun q => ⟨P.stepFin_subset_heads _ _, P.stepFin_subset_heads _ _⟩
  · exact ⟨Finset.empty_subset _, P.stepFin_subset_heads _ _⟩

/-- **Sound preprocessing, computed**: every stable model contains the computed true atoms and is
contained in the computed possible atoms. -/
theorem wellFoundedFin_approximates {M : Set A} (h : P.Stable M) :
    ↑P.wellFoundedFin.1 ⊆ M ∧ M ⊆ ↑(ofDual P.wellFoundedFin.2) := by
  have := P.wellFoundedModel_approximates h
  rw [← coe_wellFoundedFin] at this
  exact this

end Computed

end Program

end Mettapedia.Logic.ASP
