import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ObservationModulo
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Controls

/-!
# Rows modulo the knowledge: the first-order profile and controls

## The first-order profile

Every consistent store of the first-order profile has a principal answer
(`FirstOrder.accepted_principal`), so there equivalence modulo the knowledge is pointwise
equivalence (`firstOrder_moduloEquivalent_iff_pointwise`) and is fully abstract
(`firstOrder_moduloEquivalent_iff_observes`).

## Controls (`ModuloControls`), over the first-order profile

Labels: `20 : X`, `21 : Y`, `22 : X`, `23 : Y`, `24 : Z`.

* **C2, positive** (`c2_equivalent`): the rows `20 : X` and `21 : Y` under the knowledge `X = Y`,
  nothing escaped, are equivalent modulo the knowledge, and every permitted probe agrees on them
  (`c2_probes_agree`); private equivalence keeps them apart (`c2_not_private`).
* **A region that reads labels syntactically breaks respect** (`syntactic_region_separates`): the
  run layer's query whose region asks for the label `Y` itself, naming nothing, holds at the first C2
  state and fails at the second. It is not a region that reads through solutions
  (`syntactic_not_region`).
* **Negative: a renaming that moves an escaped identity** (`c2_escaped_not_equivalent`).
* **Negative: labels equal at some solutions but not all** (`free_not_equivalent`): `X` and `Y`
  with empty knowledge.
* **Negative: multiplicity** (`two_copies_not_one`): the row `20` against the rows `20` and `21`
  under `X = Y`, one class with two copies against one copy.
* **The run layer's probes are not fully abstract** (`existing_probes_agree`, `uniform_not_abstract`):
  the rows `X, Y, X` and `X, Y, Y` with empty knowledge are told apart by no probe of the run layer,
  not even by queries with syntactic regions, yet they are not pointwise equivalent, so not
  equivalent modulo the knowledge and not privately equivalent; a tally separates them. A count
  that must be the same number at every solution cannot see a multiplicity that varies with the
  solution (`uniform_count_iff`).
* **Evidence outlives its record** (`evidence_outlives_record_modulo`): joint ends keep the evidence
  ledger, modulo the knowledge as privately.
* **Inconsistent knowledge** (`inconsistent_pointwise`): with no solution, every probe but presence
  is vacuous, so pointwise equivalence relates one row to two, which equivalence modulo the
  knowledge does not.

## Without a principal answer (`NonPrincipal`)

A three-element action with two solutions of the knowledge `x = 0`: under the first, `x, y, u, v`
read `0, 1, 0, 1`; under the second, `0, 1, 1, 0`. The rows `x, y` and `u, v` are pointwise
equivalent and not equivalent modulo the knowledge (`pointwise_not_modulo`), so the knowledge has
no principal answer (`no_principal`), and equivalence modulo the knowledge is not fully abstract
there: pointwise equivalence is.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Observation

open AnnotatedRuns
open GuardFreeProcessOrders (SameUpTo)
open MeTTaCalculus.OccurrenceCommits (regionOf)
open Mettapedia.Logic.LP

universe uO

/-! ## The first-order profile -/

section FirstOrderProfile

variable {signature : LPSignature} [DecidableEq signature.vars] [DecidableEq signature.constants]
  [DecidableEq signature.functionSymbols] {O : Type uO} [DecidableEq O]
  (label : O → Term signature) (E : Finset O)

omit [DecidableEq O] in
/-- **In the first-order profile, equivalence modulo consistent knowledge is pointwise
equivalence.** -/
theorem firstOrder_moduloEquivalent_iff_pointwise {C D : Configuration (Term signature) O}
    (consistent : (FirstOrder.action signature).Consistent C.equations) :
    ModuloEquivalent (FirstOrder.action signature) label E C D ↔
      PointwiseEquivalent (FirstOrder.action signature) label E C D := by
  obtain ⟨answer, accepted⟩ := (FirstOrder.accepted_iff_consistent C.equations).mpr consistent
  exact moduloEquivalent_iff_pointwise _ label E
    (FirstOrder.accepted_principal C.equations answer accepted)

/-- **In the first-order profile, equivalence modulo consistent knowledge is fully abstract.** -/
theorem firstOrder_moduloEquivalent_iff_observes {C D : Configuration (Term signature) O}
    (consistent : (FirstOrder.action signature).Consistent C.equations) :
    ModuloEquivalent (FirstOrder.action signature) label E C D ↔
      ∀ p : ModuloProbe (FirstOrder.action signature) O, p.names ⊆ E →
        (p.Observes label C ↔ p.Observes label D) := by
  obtain ⟨answer, accepted⟩ := (FirstOrder.accepted_iff_consistent C.equations).mpr consistent
  exact moduloEquivalent_iff_observes_of_principal label E
    (FirstOrder.accepted_principal C.equations answer accepted)

end FirstOrderProfile

/-! ## Controls -/

namespace ModuloControls

open ConstraintMultisetRewriting.Controls (signature A)
open AnnotatedRuns.Controls (zeros)

/-- Terms of the controls. -/
abbrev Tm := Term signature

abbrev X : Tm := .var 0
abbrev Y : Tm := .var 1
abbrev Z : Tm := .var 2

/-- Labels: `20 : X`, `21 : Y`, `22 : X`, `23 : Y`, `24 : Z`, otherwise the constant `2`. -/
def label : ℕ → Tm
  | 20 => X
  | 21 => Y
  | 22 => X
  | 23 => Y
  | 24 => Z
  | _ => .const 2

theorem X_ne_Y : X ≠ Y := fun same => absurd (Term.var.inj same) (by decide)

theorem solves_id_iff (s t : Tm) : A.Solves (Subst.id signature) (s, t) ↔ s = t := by
  show (Subst.id signature).applyTerm s = (Subst.id signature).applyTerm t ↔ s = t
  rw [Subst.applyTerm_id, Subst.applyTerm_id]

/-! ### C2 -/

/-- The knowledge `X = Y`. -/
def knowsXY : EquationStore Tm := [(X, Y)]

/-- **C2**: one row `o` under the knowledge `X = Y`. -/
def c2 (o : ℕ) : Configuration Tm ℕ := ⟨knowsXY, {o}⟩

theorem entailed_XY : Entailed A knowsXY X Y :=
  fun _ solved => solved (X, Y) (List.mem_singleton_self _)

theorem zeros_solves : A.Models zeros knowsXY := by
  intro e member
  rw [show e = (X, Y) from List.mem_singleton.mp member]
  rfl

/-- **C2 is equivalent modulo the knowledge.** -/
theorem c2_equivalent : ModuloEquivalent A label ∅ (c2 20) (c2 21) := by
  refine (moduloEquivalent_iff A label ∅ (c2 20) (c2 21)).mpr
    ⟨fun _ => Iff.rfl, fun o member => absurd member (Finset.notMem_empty o), ?_⟩
  show ({20} : Finset ℕ).val.map (fun o => Quotient.mk (entailedSetoid A knowsXY) (label o)) =
    ({21} : Finset ℕ).val.map (fun o => Quotient.mk (entailedSetoid A knowsXY) (label o))
  rw [Finset.singleton_val, Finset.singleton_val, Multiset.map_singleton, Multiset.map_singleton]
  exact congrArg (fun c => ({c} : Multiset _)) (Quotient.sound entailed_XY)

/-- **Every permitted probe agrees on C2.** -/
theorem c2_probes_agree (p : ModuloProbe A ℕ) (named : p.names ⊆ ∅) :
    p.Observes label (c2 20) ↔ p.Observes label (c2 21) :=
  c2_equivalent.observes named

/-- **Private equivalence keeps C2 apart**: the labels differ syntactically. -/
theorem c2_not_private : ¬ PrivatelyEquivalent A label ∅ (c2 20) (c2 21) := by
  intro h
  have bags := h.labels_eq
  simp only [c2, Finset.singleton_val, Multiset.map_singleton, Multiset.singleton_inj] at bags
  exact X_ne_Y bags

open Classical in
/-- The run layer's query whose region asks for the label `Y` itself, naming nothing. -/
noncomputable def syntacticY : PredicateQueryAdmission.Query Tm (Subst signature) ℕ :=
  ⟨fun _ t => decide (t = Y), ∅⟩

/-- **A region that reads labels syntactically separates C2.** -/
theorem syntactic_region_separates :
    (Probe.ask syntacticY : Probe Tm (Subst signature) ℕ).names ⊆ ∅ ∧
      (Probe.ask syntacticY).Observes A label (c2 20) ∧
      ¬ (Probe.ask syntacticY).Observes A label (c2 21) := by
  refine ⟨fun _ member => member, fun σ _ => ?_, fun observed => ?_⟩
  · show regionOf label {20} (syntacticY.region σ) = ∅
    have notY : syntacticY.region σ (label 20) = false := by
      classical
      show decide (X = Y) = false
      exact decide_eq_false X_ne_Y
    simp only [regionOf, Finset.filter_singleton, notY, Bool.false_eq_true, if_false]
  · have atZeros : regionOf label {21} (syntacticY.region zeros) = ∅ := observed zeros zeros_solves
    have isY : syntacticY.region zeros (label 21) = true := by
      classical
      show decide (Y = Y) = true
      exact decide_eq_true rfl
    simp only [regionOf, Finset.filter_singleton, isY, if_true] at atZeros
    exact Finset.singleton_ne_empty 21 atZeros

/-- **That region does not read labels through solutions**: `zeros` identifies `X` and `Y`. -/
theorem syntactic_not_region :
    ¬ ∃ region : Region A, ∀ σ t, region.test σ t = syntacticY.region σ t := by
  rintro ⟨region, same⟩
  have identified := region.respects zeros (s := X) (t := Y) rfl
  rw [same, same] at identified
  simp [syntacticY] at identified

/-! ### Negative controls -/

/-- **A renaming that moves an escaped identity**: once `20` has escaped, C2 is not equivalent. -/
theorem c2_escaped_not_equivalent :
    ¬ RenamingUpTo (entailedSetoid A knowsXY) label {20} (Equiv.swap 20 21) ∧
      ¬ ModuloEquivalent A label {20} (c2 20) (c2 21) := by
  refine ⟨fun k => ?_, fun h => ?_⟩
  · have fixed := k.fixes 20 (Finset.mem_singleton_self 20)
    rw [Equiv.swap_apply_left] at fixed
    exact absurd fixed (by decide)
  · have moved := (h.escaped_iff (Finset.mem_singleton_self 20)).mp (Finset.mem_singleton_self 20)
    exact absurd moved (by decide)

/-- One row `o` with empty knowledge. -/
def free (o : ℕ) : Configuration Tm ℕ := ⟨[], {o}⟩

/-- **Labels equal at some solutions but not all**: `zeros` identifies `X` and `Y`, the identity
does not, and the rows `20 : X` and `21 : Y` with empty knowledge are neither pointwise equivalent
nor equivalent modulo the knowledge. -/
theorem free_not_equivalent :
    A.Solves zeros (label 20, label 21) ∧ ¬ A.Solves (Subst.id signature) (label 20, label 21) ∧
      ¬ PointwiseEquivalent A label ∅ (free 20) (free 21) ∧
      ¬ ModuloEquivalent A label ∅ (free 20) (free 21) := by
  have notPointwise : ¬ PointwiseEquivalent A label ∅ (free 20) (free 21) := by
    intro h
    obtain ⟨π, k, onto⟩ := h.2.2 (Subst.id signature) (A.models_nil _)
    have image : π 20 = 21 := by
      have member : π 20 ∈ ({21} : Finset ℕ) := by
        rw [← show ({20} : Finset ℕ).map π.toEmbedding = {21} from onto]
        exact Finset.mem_map_of_mem _ (Finset.mem_singleton_self 20)
      exact Finset.mem_singleton.mp member
    have kept := (solves_id_iff _ _).mp (k.keeps 20)
    rw [image] at kept
    exact X_ne_Y kept.symm
  exact ⟨rfl, fun same => X_ne_Y ((solves_id_iff _ _).mp same), notPointwise,
    fun h => notPointwise (h.pointwise)⟩

/-- **A probe separates them**, by full abstraction. -/
theorem free_separated :
    ∃ p : ModuloProbe A ℕ, p.names ⊆ ∅ ∧ ¬ (p.Observes label (free 20) ↔ p.Observes label (free 21)) := by
  by_contra none
  refine free_not_equivalent.2.2.1 ((pointwiseEquivalent_iff_observes label ∅ _ _).mpr fun p named => ?_)
  by_contra differ
  exact none ⟨p, named, differ⟩

/-- **Multiplicity**: under `X = Y` the rows `20` and `21` carry one class, and two copies are not
one. -/
theorem two_copies_not_one :
    ¬ PointwiseEquivalent A label ∅ (c2 20) ⟨knowsXY, {20, 21}⟩ ∧
      ¬ ModuloEquivalent A label ∅ (c2 20) ⟨knowsXY, {20, 21}⟩ := by
  have notPointwise : ¬ PointwiseEquivalent A label ∅ (c2 20) ⟨knowsXY, {20, 21}⟩ := by
    intro h
    obtain ⟨π, -, onto⟩ := h.2.2 zeros zeros_solves
    have counts := congrArg Finset.card onto
    rw [Finset.card_map] at counts
    exact absurd counts (by decide)
  exact ⟨notPointwise, fun h => notPointwise h.pointwise⟩

/-! ### The run layer's probes are not fully abstract -/

/-- The rows `20 : X`, `21 : Y`, `22 : X` with empty knowledge. -/
def twoX : Configuration Tm ℕ := ⟨[], {20, 21, 22}⟩

/-- The rows `20 : X`, `21 : Y`, `23 : Y` with empty knowledge. -/
def twoY : Configuration Tm ℕ := ⟨[], {20, 21, 23}⟩

theorem forall_twoX (φ : Tm → Prop) : (∀ o ∈ twoX.present, φ (label o)) ↔ φ X ∧ φ Y := by
  simp only [twoX, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, h.1⟩⟩

theorem forall_twoY (φ : Tm → Prop) : (∀ o ∈ twoY.present, φ (label o)) ↔ φ X ∧ φ Y := by
  simp only [twoY, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, h.2⟩⟩

theorem entails_nil (φ : Subst signature → Prop) : A.Entails [] φ ↔ ∀ σ, φ σ :=
  ⟨fun asked σ => asked σ (A.models_nil σ), fun all σ _ => all σ⟩

theorem regionOf_eq_empty_iff (P : Finset ℕ) (region : Tm → Bool) :
    regionOf label P region = ∅ ↔ ∀ o ∈ P, region (label o) = false := by
  simp only [regionOf, Finset.filter_eq_empty_iff, Bool.not_eq_true]

/-- **A count that is the same number at every solution is zero** on rows whose labels are the
unknowns `X` and `Y`, both present: the substitution `zeros` matches all rows or none, and the
identity never matches all. -/
theorem uniform_count_iff {P : Finset ℕ} (onlyXY : ∀ o ∈ P, label o = X ∨ label o = Y)
    (hasX : ∃ o ∈ P, label o = X) (hasY : ∃ o ∈ P, label o = Y) (pattern : Tm) (n : ℕ) :
    (∀ σ, (Check.matches A σ label P pattern).card = n) ↔
      n = 0 ∧ ∀ σ, ∀ o ∈ P, ¬ A.E (A.apply σ pattern) (A.apply σ (label o)) := by
  classical
  constructor
  · intro uniform
    have atIdentity : n < P.card := by
      rw [← uniform (Subst.id signature)]
      unfold Check.matches
      refine Finset.card_lt_card (Finset.filter_ssubset.mpr ?_)
      by_cases isX : pattern = X
      · obtain ⟨o, member, labelled⟩ := hasY
        refine ⟨o, member, fun matched => X_ne_Y ?_⟩
        have same := (solves_id_iff pattern (label o)).mp matched
        rw [← isX, same, labelled]
      · obtain ⟨o, member, labelled⟩ := hasX
        refine ⟨o, member, fun matched => isX ?_⟩
        rw [(solves_id_iff pattern (label o)).mp matched, labelled]
    have atZeros : n = 0 ∨ n = P.card := by
      rw [← uniform zeros]
      unfold Check.matches
      have allZero : ∀ o ∈ P, A.apply zeros (label o) = .const 0 := by
        intro o member
        rcases onlyXY o member with labelled | labelled <;> rw [labelled] <;> rfl
      by_cases hit : A.apply zeros pattern = .const 0
      · right
        rw [Finset.filter_true_of_mem fun o member => by
          show A.apply zeros pattern = A.apply zeros (label o)
          rw [hit, allZero o member]]
      · left
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro o member matched
        exact hit (matched.trans (allZero o member))
    have zero : n = 0 := atZeros.resolve_right (Nat.ne_of_lt atIdentity)
    refine ⟨zero, fun σ o member matched => ?_⟩
    have empty := uniform σ
    rw [zero, Finset.card_eq_zero] at empty
    unfold Check.matches at empty
    exact Finset.filter_eq_empty_iff.mp empty member matched
  · rintro ⟨rfl, none⟩ σ
    unfold Check.matches
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact fun o member => none σ o member

theorem twoX_shape : (∀ o ∈ twoX.present, label o = X ∨ label o = Y) ∧
    (∃ o ∈ twoX.present, label o = X) ∧ ∃ o ∈ twoX.present, label o = Y :=
  ⟨(forall_twoX fun t => t = X ∨ t = Y).mpr ⟨Or.inl rfl, Or.inr rfl⟩,
    ⟨20, by simp [twoX], rfl⟩, ⟨21, by simp [twoX], rfl⟩⟩

theorem twoY_shape : (∀ o ∈ twoY.present, label o = X ∨ label o = Y) ∧
    (∃ o ∈ twoY.present, label o = X) ∧ ∃ o ∈ twoY.present, label o = Y :=
  ⟨(forall_twoY fun t => t = X ∨ t = Y).mpr ⟨Or.inl rfl, Or.inr rfl⟩,
    ⟨20, by simp [twoY], rfl⟩, ⟨21, by simp [twoY], rfl⟩⟩

/-- **No probe of the run layer tells `X, Y, X` from `X, Y, Y`**, not even a query whose region
reads labels syntactically. -/
theorem existing_probes_agree (p : Probe Tm (Subst signature) ℕ) (named : p.names ⊆ ∅) :
    p.Observes A label twoX ↔ p.Observes A label twoY := by
  cases p with
  | present reference =>
      exact absurd (named (Finset.mem_singleton_self reference)) (Finset.notMem_empty _)
  | ask query =>
      have empty : query.seen = ∅ := Finset.subset_empty.mp named
      show A.Entails [] (fun σ => regionOf label twoX.present (query.region σ) = query.seen) ↔
        A.Entails [] (fun σ => regionOf label twoY.present (query.region σ) = query.seen)
      rw [empty, entails_nil, entails_nil]
      refine forall_congr' fun σ => ?_
      rw [regionOf_eq_empty_iff, regionOf_eq_empty_iff]
      exact (forall_twoX fun t => query.region σ t = false).trans
        (forall_twoY fun t => query.region σ t = false).symm
  | check guard =>
      cases guard with
      | equal left right => exact Iff.rfl
      | absent pattern =>
          show A.Entails [] (fun σ => ∀ o ∈ twoX.present,
              ¬ A.E (A.apply σ pattern) (A.apply σ (label o))) ↔
            A.Entails [] (fun σ => ∀ o ∈ twoY.present,
              ¬ A.E (A.apply σ pattern) (A.apply σ (label o)))
          rw [entails_nil, entails_nil]
          refine forall_congr' fun σ => ?_
          exact (forall_twoX fun t => ¬ A.E (A.apply σ pattern) (A.apply σ t)).trans
            (forall_twoY fun t => ¬ A.E (A.apply σ pattern) (A.apply σ t)).symm
      | count pattern number =>
          show A.Entails [] (fun σ => (Check.matches A σ label twoX.present pattern).card = number) ↔
            A.Entails [] (fun σ => (Check.matches A σ label twoY.present pattern).card = number)
          rw [entails_nil, entails_nil,
            uniform_count_iff twoX_shape.1 twoX_shape.2.1 twoX_shape.2.2 pattern number,
            uniform_count_iff twoY_shape.1 twoY_shape.2.1 twoY_shape.2.2 pattern number]
          refine and_congr_right fun _ => forall_congr' fun σ => ?_
          exact (forall_twoX fun t => ¬ A.E (A.apply σ pattern) (A.apply σ t)).trans
            (forall_twoY fun t => ¬ A.E (A.apply σ pattern) (A.apply σ t)).symm

/-- **Yet they are not pointwise equivalent**: at the identity, a label-keeping bijection would send
both `X` rows to the one `X` row. -/
theorem twoX_not_pointwise : ¬ PointwiseEquivalent A label ∅ twoX twoY := by
  intro h
  obtain ⟨π, k, onto⟩ := h.2.2 (Subst.id signature) (A.models_nil _)
  have onlyX : ∀ o, o ∈ twoX.present → label (π o) = X → π o = 20 := by
    intro o member labelled
    have inside : π o ∈ twoY.present := by
      rw [← onto]
      exact Finset.mem_map_of_mem _ member
    simp only [twoY, Finset.mem_insert, Finset.mem_singleton] at inside
    rcases inside with is20 | is21 | is23
    · exact is20
    · rw [is21] at labelled
      exact absurd labelled.symm X_ne_Y
    · rw [is23] at labelled
      exact absurd labelled.symm X_ne_Y
  have keepsX : ∀ o, label o = X → label (π o) = X := fun o labelled =>
    ((solves_id_iff _ _).mp (k.keeps o)).trans labelled
  have first := onlyX 20 (by simp [twoX]) (keepsX 20 rfl)
  have second := onlyX 22 (by simp [twoX]) (keepsX 22 rfl)
  exact absurd (π.injective (first.trans second.symm)) (by decide)

/-- **The run layer's probes are not fully abstract**: they agree on two states that are not
pointwise equivalent, hence neither equivalent modulo the knowledge nor privately equivalent, and a
tally separates them. -/
theorem uniform_not_abstract :
    (∀ p : Probe Tm (Subst signature) ℕ, p.names ⊆ ∅ →
        (p.Observes A label twoX ↔ p.Observes A label twoY)) ∧
      ¬ PointwiseEquivalent A label ∅ twoX twoY ∧ ¬ ModuloEquivalent A label ∅ twoX twoY ∧
      ¬ PrivatelyEquivalent A label ∅ twoX twoY ∧
      ∃ p : ModuloProbe A ℕ, p.names ⊆ ∅ ∧ ¬ (p.Observes label twoX ↔ p.Observes label twoY) := by
  refine ⟨existing_probes_agree, twoX_not_pointwise, fun h => twoX_not_pointwise h.pointwise,
    fun h => twoX_not_pointwise (PrivatelyEquivalent.modulo h).pointwise, ?_⟩
  by_contra none
  refine twoX_not_pointwise ((pointwiseEquivalent_iff_observes label ∅ _ _).mpr fun p named => ?_)
  by_contra differ
  exact none ⟨p, named, differ⟩

/-! ### Joint ends -/

/-- **A record that escaped into evidence outlives its row, modulo the knowledge too**: two
histories end in one state, one after recording the row `20` as evidence; their states are
equivalent and their joint ends are not. -/
theorem evidence_outlives_record_modulo :
    ModuloEquivalent A label ∅ (free 30) (free 30) ∧
      ¬ JointModuloEquivalent A label ∅ (free 30, ⟨[], ∅, {20}, ∅⟩) (free 30, ⟨[], ∅, ∅, ∅⟩) := by
  refine ⟨ModuloEquivalent.refl _, fun h => ?_⟩
  have counts : ({20} : Finset ℕ).card = (∅ : Finset ℕ).card := h.evidence_card
  simp at counts

/-! ### Inconsistent knowledge -/

/-- The knowledge `0 = 1`, which has no solution. -/
def clash : EquationStore Tm := [(.const 0, .const 1)]

/-- **With no solution, pointwise equivalence relates one row to two**; equivalence modulo the
knowledge keeps the number of rows. -/
theorem inconsistent_pointwise :
    PointwiseEquivalent A label ∅ ⟨clash, {20}⟩ ⟨clash, {20, 21}⟩ ∧
      ¬ ModuloEquivalent A label ∅ ⟨clash, {20}⟩ ⟨clash, {20, 21}⟩ := by
  refine ⟨⟨fun _ => Iff.rfl, fun o member => absurd member (Finset.notMem_empty o),
    fun σ solved => ?_⟩, fun h => ?_⟩
  · have clashes : (Term.const 0 : Tm) = .const 1 := solved _ (List.mem_singleton_self _)
    exact absurd (Term.const.inj clashes) (by decide)
  · have counts := h.card_eq
    exact absurd counts (by decide)

end ModuloControls

/-! ## Without a principal answer -/

namespace NonPrincipal

/-- Four unknowns and two values. -/
inductive Atom where
  | x | y | u | v | zero | one
  deriving DecidableEq

/-- The identity and two choices of values. -/
inductive Choice where
  | identity | first | second
  deriving DecidableEq

/-- Under `first`, `x, y, u, v` read `0, 1, 0, 1`; under `second`, `0, 1, 1, 0`. Values are fixed. -/
def Choice.apply : Choice → Atom → Atom
  | .first, .x => .zero
  | .first, .y => .one
  | .first, .u => .zero
  | .first, .v => .one
  | .second, .x => .zero
  | .second, .y => .one
  | .second, .u => .one
  | .second, .v => .zero
  | _, a => a

/-- Composition: a choice followed by anything is that choice. -/
def Choice.compose : Choice → Choice → Choice
  | outer, .identity => outer
  | _, inner => inner

/-- **A substitution action with two incomparable solutions.** -/
def action : SubstitutionAction Atom Choice where
  E := Eq
  equivalence := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  apply := Choice.apply
  identity := .identity
  compose := Choice.compose
  apply_identity _ := rfl
  apply_compose outer inner t := by cases outer <;> cases inner <;> cases t <;> rfl
  preserves σ _ _ same := congrArg (Choice.apply σ) same

/-- The knowledge `x = 0`: its solutions are the two choices. -/
def knowledge : EquationStore Atom := [(.x, .zero)]

/-- Labels: `1 : x`, `2 : y`, `3 : u`, `4 : v`. -/
def label : ℕ → Atom
  | 1 => .x
  | 2 => .y
  | 3 => .u
  | 4 => .v
  | _ => .zero

def left : Configuration Atom ℕ := ⟨knowledge, {1, 2}⟩
def right : Configuration Atom ℕ := ⟨knowledge, {3, 4}⟩

theorem not_identity : ¬ action.Models Choice.identity knowledge := fun solved => by
  have clash : Atom.x = Atom.zero := solved _ (List.mem_singleton_self _)
  exact absurd clash (by decide)

theorem first_solves : action.Models Choice.first knowledge := by
  intro e member
  rw [List.mem_singleton.mp member]
  rfl

theorem second_solves : action.Models Choice.second knowledge := by
  intro e member
  rw [List.mem_singleton.mp member]
  rfl

/-- A renaming that keeps labels at a solution, checked on the four rows. -/
theorem keeps_of_rows {σ : Choice} {π : ℕ ≃ ℕ}
    (outside : ∀ o, o ≠ 1 → o ≠ 2 → o ≠ 3 → o ≠ 4 → π o = o)
    (rows : ∀ o ∈ ({1, 2, 3, 4} : Finset ℕ), Choice.apply σ (label (π o)) = Choice.apply σ (label o)) :
    RenamingUpTo (solutionSetoid action σ) label ∅ π := by
  refine ⟨fun o => ?_, fun o member => absurd member (Finset.notMem_empty o)⟩
  show Choice.apply σ (label (π o)) = Choice.apply σ (label o)
  by_cases inside : o ∈ ({1, 2, 3, 4} : Finset ℕ)
  · exact rows o inside
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at inside
    rw [outside o inside.1 inside.2.1 inside.2.2.1 inside.2.2.2]

/-- `1 ↦ 3`, `2 ↦ 4`. -/
def straight : ℕ ≃ ℕ := (Equiv.swap 1 3).trans (Equiv.swap 2 4)

/-- `1 ↦ 4`, `2 ↦ 3`. -/
def crossed : ℕ ≃ ℕ := (Equiv.swap 1 4).trans (Equiv.swap 2 3)

theorem straight_outside : ∀ o, o ≠ 1 → o ≠ 2 → o ≠ 3 → o ≠ 4 → straight o = o := by
  intro o h1 h2 h3 h4
  simp only [straight, Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne h1 h3,
    Equiv.swap_apply_of_ne_of_ne h2 h4]

theorem crossed_outside : ∀ o, o ≠ 1 → o ≠ 2 → o ≠ 3 → o ≠ 4 → crossed o = o := by
  intro o h1 h2 h3 h4
  simp only [crossed, Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne h1 h4,
    Equiv.swap_apply_of_ne_of_ne h2 h3]

/-- **Pointwise equivalent**: `straight` serves the first solution and `crossed` the second. -/
theorem pointwise : PointwiseEquivalent action label ∅ left right := by
  refine ⟨fun _ => Iff.rfl, fun o member => absurd member (Finset.notMem_empty o), ?_⟩
  intro σ solved
  cases σ with
  | identity => exact absurd solved not_identity
  | first =>
      refine ⟨straight, keeps_of_rows straight_outside ?_, by decide⟩
      intro o member
      simp only [Finset.mem_insert, Finset.mem_singleton] at member
      rcases member with rfl | rfl | rfl | rfl <;> rfl
  | second =>
      refine ⟨crossed, keeps_of_rows crossed_outside ?_, by decide⟩
      intro o member
      simp only [Finset.mem_insert, Finset.mem_singleton] at member
      rcases member with rfl | rfl | rfl | rfl <;> rfl

/-- **Not equivalent modulo the knowledge**: `x` is entailed equal to neither `u` nor `v`. -/
theorem not_modulo : ¬ ModuloEquivalent action label ∅ left right := by
  rintro ⟨π, k, same⟩
  have image : π 1 ∈ ({3, 4} : Finset ℕ) := by
    rw [← show ({1, 2} : Finset ℕ).map π.toEmbedding = {3, 4} from same.2]
    exact Finset.mem_map_of_mem _ (by simp)
  have kept := k.keeps 1
  simp only [Finset.mem_insert, Finset.mem_singleton] at image
  rcases image with is3 | is4
  · have atSecond := kept Choice.second second_solves
    rw [is3] at atSecond
    have clash : Atom.one = Atom.zero := atSecond
    exact absurd clash (by decide)
  · have atFirst := kept Choice.first first_solves
    rw [is4] at atFirst
    have clash : Atom.one = Atom.zero := atFirst
    exact absurd clash (by decide)

/-- **Pointwise equivalence is strictly coarser without a principal answer.** -/
theorem pointwise_not_modulo :
    PointwiseEquivalent action label ∅ left right ∧ ¬ ModuloEquivalent action label ∅ left right :=
  ⟨pointwise, not_modulo⟩

/-- **The knowledge `x = 0` has no principal answer here.** -/
theorem no_principal : ¬ ∃ answer, action.Principal knowledge answer := by
  rintro ⟨answer, principal⟩
  exact not_modulo (PointwiseEquivalent.modulo_of_principal (C := left) principal pointwise)

/-- **Equivalence modulo the knowledge is not fully abstract without a principal answer**: every
permitted probe agrees on the two states. -/
theorem probes_agree (p : ModuloProbe action ℕ) (named : p.names ⊆ ∅) :
    p.Observes label left ↔ p.Observes label right :=
  pointwise.observes named

end NonPrincipal

#print axioms firstOrder_moduloEquivalent_iff_pointwise
#print axioms firstOrder_moduloEquivalent_iff_observes
#print axioms ModuloControls.c2_equivalent
#print axioms ModuloControls.c2_probes_agree
#print axioms ModuloControls.c2_not_private
#print axioms ModuloControls.syntactic_region_separates
#print axioms ModuloControls.syntactic_not_region
#print axioms ModuloControls.c2_escaped_not_equivalent
#print axioms ModuloControls.free_not_equivalent
#print axioms ModuloControls.free_separated
#print axioms ModuloControls.two_copies_not_one
#print axioms ModuloControls.uniform_count_iff
#print axioms ModuloControls.existing_probes_agree
#print axioms ModuloControls.twoX_not_pointwise
#print axioms ModuloControls.uniform_not_abstract
#print axioms ModuloControls.inconsistent_pointwise
#print axioms ModuloControls.evidence_outlives_record_modulo
#print axioms NonPrincipal.action
#print axioms NonPrincipal.pointwise
#print axioms NonPrincipal.not_modulo
#print axioms NonPrincipal.pointwise_not_modulo
#print axioms NonPrincipal.no_principal
#print axioms NonPrincipal.probes_agree

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Observation
