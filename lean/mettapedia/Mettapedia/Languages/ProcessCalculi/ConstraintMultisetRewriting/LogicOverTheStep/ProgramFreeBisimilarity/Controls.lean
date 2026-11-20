import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.ProgramFreeBisimilarity.Characterization
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ObservationModuloControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.ProgramAdequacy

/-!
# Instances and controls of the characterization

## Instances

* **Bags read through a function** (`bag_eq_iff_of_kernel`): when a function decides the classes,
  equal bags of classes are equal bags of images.
Both instances assume a fresh supply of identities for every label.

* **The ground instance** (`ground_bisimilar_iff`): over an action whose substitutions fix every
  term and whose equality is syntactic, a consistent configuration is bisimilar to another exactly
  when the other is consistent and carries the same bag of labels; on the ground step of the tree
  (`issuing_ground_bisimilar_iff`).
* **The first-order instance** (`firstOrder_bisimilar_iff`): bisimilar exactly when the knowledge has
  the same unifiers and, under the most general unifier of the first, the rows carry the same bag of
  instantiated labels. On the first-order step bisimilarity is therefore agreement on every static
  probe modulo the knowledge (`firstOrder_bisimilar_iff_observes`).

## Controls (`ProgramFreeControls`)

Each hypothesis of the characterization, and each probe it uses, fails somewhere; each control of
`ruleOffers_bisimilar_iff` (a fresh supply, consistency) fails one of its two hypotheses only:

* **Consistency** (`consistency_alone`): under the labelling by parity, which has a fresh supply
  (`parity_supply`), the rows `0` and `0, 2` under the knowledge `0 = 1` are bisimilar, since neither
  moves, and not equivalent modulo the knowledge for any escaped identities. No firing reaches them.
  `consistency_needed` shows the same under the labelling of C2, which has no fresh supply
  (`not_freshSupply`): it is the control of `moduloEquivalent_of_bisimilar`, whose one hypothesis is
  consistency, and it fails both hypotheses of `ruleOffers_bisimilar_iff`.
* **A fresh supply** (`freshSupply_needed`): the configurations of C2 (rows `20 : X` and `21 : Y`
  under `X = Y`) have consistent knowledge, are equivalent modulo the knowledge and bisimilar for the
  probe step, but only `20` and `22` carry `X`, so the rule that makes two rows `X` moves at the
  second and not at the first. Both are reached from one row by the tell of `X = Y` (`c2_reached`).
* **Guards alone** (`guards_alone_coarser`): they see the solutions only; one row against none.
* **Takes alone** (`takes_alone_coarser`): without rows they see only consistency; `X = 0` against
  nothing.
* **No checks at all** (`checkFree_coarser`): over a signature with one constant and no function
  symbol every store is consistent, so takes, reads, makes and tells see no knowledge; `x = c`
  against nothing. A tell asks that some solution remain; a guard asks something of every solution.

Neighbouring equivalences, against the characterization:

* **Private equivalence is too fine** (`private_too_fine`): rows `0 : X` and `1 : Y` under `X = Y`,
  with labels carried by every identity of their parity, are bisimilar and not privately equivalent.
* **Pointwise equivalence is too coarse** (`pointwise_too_coarse`): the two stores of the action
  without a principal answer are pointwise equivalent and not bisimilar.
* **The run layer's static probes are too coarse** (`runProbes_too_coarse`): `X, Y, X` and `X, Y, Y`
  with empty knowledge are told apart by no probe of the run layer, and they are not bisimilar.

What the program-free step sees of the knowledge:

* **Knowledge about an unknown that no row mentions** (`unmentioned_knowledge_visible`).
* **History** (`history_visible`): from one row `X`, the take under `Y` and the take under `X` leave
  no rows, and only the first remembers `Y = X`; the results are not bisimilar.

Every configuration of the controls is a start state or is reached from rows without knowledge by one
tell (`c2_reached`, `controls_reached`); the inconsistent ones of `consistency_needed` are reached by
no move.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.ProgramFreeBisimilarity

open AnnotatedRuns
open Semantic (ruleOffers FreshSupply)
open Observation (ModuloEquivalent PointwiseEquivalent PrivatelyEquivalent entailedSetoid Entailed
  moduloEquivalent_iff)
open MeTTaCalculus.OccurrenceCommits (fire)
open Mettapedia.Logic.LP

universe uT uS uO

/-! ## Instances -/

section Instances

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
  {A : SubstitutionAction T S} {label : O → T}

omit [DecidableEq O] in
/-- **Bags of classes read through a function that decides the classes.** -/
theorem bag_eq_iff_of_kernel {U : Type*} {r : Setoid T} (g : T → U)
    (kernel : ∀ s t, r s t ↔ g s = g t) (P Q : Finset O) :
    P.val.map (fun o => Quotient.mk r (label o)) = Q.val.map (fun o => Quotient.mk r (label o)) ↔
      P.val.map (fun o => g (label o)) = Q.val.map (fun o => g (label o)) := by
  let φ : Quotient r → U := Quotient.lift g fun a b related => (kernel a b).mp related
  have injective : Function.Injective φ := by
    intro a b same
    induction a using Quotient.ind
    induction b using Quotient.ind
    exact Quotient.sound ((kernel _ _).mpr same)
  have through : ∀ X : Finset O, X.val.map (fun o => g (label o)) =
      (X.val.map fun o => Quotient.mk r (label o)).map φ := by
    intro X
    rw [Multiset.map_map]
    rfl
  rw [through P, through Q]
  exact (Multiset.map_injective injective).eq_iff.symm

/-- **The ground instance**: over an action whose substitutions fix every term and whose equality is
syntactic, a configuration with consistent knowledge is bisimilar to another exactly when the other
is consistent and carries the same bag of labels. -/
theorem ground_bisimilar_iff (fixes : ∀ σ t, A.apply σ t = t) (syntactic : ∀ s t, A.E s t ↔ s = t)
    (supply : FreshSupply label) {C D : Configuration T O} (consistent : A.Consistent C.equations) :
    Race.Bisimilar A label (ruleOffers A) C D ↔
      A.Consistent D.equations ∧ C.present.val.map label = D.present.val.map label := by
  have models : ∀ σ (K : EquationStore T), A.Models σ K ↔ ∀ e ∈ K, e.1 = e.2 := by
    intro σ K
    refine forall₂_congr fun e _ => ?_
    show A.E (A.apply σ e.1) (A.apply σ e.2) ↔ e.1 = e.2
    rw [fixes, fixes, syntactic]
  have kernel : ∀ s t, entailedSetoid A C.equations s t ↔ id s = id t := by
    intro s t
    obtain ⟨σ, solved⟩ := consistent
    constructor
    · intro entailed
      have identified : A.E (A.apply σ s) (A.apply σ t) := entailed σ solved
      rw [fixes, fixes, syntactic] at identified
      exact identified
    · intro same τ _
      show A.E (A.apply τ s) (A.apply τ t)
      rw [fixes, fixes, syntactic]
      exact same
  have equivalentIff : A.Equivalent C.equations D.equations ↔ A.Consistent D.equations := by
    constructor
    · intro same
      obtain ⟨σ, solved⟩ := consistent
      exact ⟨σ, (same σ).mp solved⟩
    · rintro ⟨τ, solvedD⟩ σ
      obtain ⟨σ₀, solvedC⟩ := consistent
      exact ⟨fun _ => (models σ _).mpr ((models τ _).mp solvedD),
        fun _ => (models σ _).mpr ((models σ₀ _).mp solvedC)⟩
  rw [ruleOffers_bisimilar_iff supply consistent, exists_moduloEquivalent_iff, moduloEquivalent_iff,
    bag_eq_iff_of_kernel id kernel, equivalentIff]
  exact ⟨fun ⟨consistentD, _, bags⟩ => ⟨consistentD, bags⟩,
    fun ⟨consistentD, bags⟩ => ⟨consistentD, fun o member => absurd member (Finset.notMem_empty o), bags⟩⟩

end Instances

section GroundStep

open NamesOnTheStep.IssuingControls (ground Occ Conf)

/-- **The ground instance on the tree's ground step**: occurrences are labels with copy numbers,
so every label has fresh identities. -/
theorem issuing_ground_bisimilar_iff {C D : Conf} (consistent : ground.Consistent C.equations) :
    Race.Bisimilar ground (Prod.fst : Occ → _) (ruleOffers ground) C D ↔
      ground.Consistent D.equations ∧ C.present.val.map Prod.fst = D.present.val.map Prod.fst :=
  ground_bisimilar_iff (fun _ _ => rfl) (fun _ _ => Iff.rfl)
    (fun o G => ProgramAdequacy.occSupply G o.1) consistent

end GroundStep

section FirstOrderInstance

variable {signature : LPSignature} [DecidableEq signature.vars] [DecidableEq signature.constants]
  [DecidableEq signature.functionSymbols] {O : Type uO} [DecidableEq O] {label : O → Term signature}

/-- **The first-order instance**: with a fresh supply, a configuration whose knowledge has the most
general unifier `θ` is bisimilar to another exactly when their knowledge has the same unifiers and
their rows carry the same bag of labels instantiated by `θ`. -/
theorem firstOrder_bisimilar_iff (supply : FreshSupply label) {C D : Configuration (Term signature) O}
    {θ : Subst signature} (mgu : unifyTotal C.equations = some θ) :
    Race.Bisimilar (FirstOrder.action signature) label (ruleOffers (FirstOrder.action signature)) C D ↔
      (FirstOrder.action signature).Equivalent C.equations D.equations ∧
        C.present.val.map (fun o => θ.applyTerm (label o)) =
          D.present.val.map (fun o => θ.applyTerm (label o)) := by
  have principal := FirstOrder.accepted_principal C.equations θ mgu
  have consistent : (FirstOrder.action signature).Consistent C.equations := ⟨θ, principal.sound⟩
  have kernel : ∀ s t, entailedSetoid (FirstOrder.action signature) C.equations s t ↔
      θ.applyTerm s = θ.applyTerm t := by
    intro s t
    constructor
    · intro entailed
      exact entailed θ principal.sound
    · intro same
      exact Setoid.le_def.mp (Observation.solution_le_entailedSetoid principal) same
  rw [ruleOffers_bisimilar_iff supply consistent, exists_moduloEquivalent_iff, moduloEquivalent_iff,
    bag_eq_iff_of_kernel _ kernel]
  exact ⟨fun ⟨same, _, bags⟩ => ⟨same, bags⟩,
    fun ⟨same, bags⟩ => ⟨same, fun o member => absurd member (Finset.notMem_empty o), bags⟩⟩

/-- **On the first-order step, bisimilarity of the program-free step is agreement on every static
probe modulo the knowledge** (the tree's full abstraction of equivalence modulo the knowledge). -/
theorem firstOrder_bisimilar_iff_observes (supply : FreshSupply label)
    {C D : Configuration (Term signature) O}
    (consistent : (FirstOrder.action signature).Consistent C.equations) :
    Race.Bisimilar (FirstOrder.action signature) label (ruleOffers (FirstOrder.action signature)) C D ↔
      ∀ p : Observation.ModuloProbe (FirstOrder.action signature) O, p.names ⊆ ∅ →
        (p.Observes label C ↔ p.Observes label D) := by
  rw [ruleOffers_bisimilar_iff supply consistent, exists_moduloEquivalent_iff]
  exact Observation.firstOrder_moduloEquivalent_iff_observes label ∅ consistent

end FirstOrderInstance

/-! ## Rule forms -/

section Forms

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
  {A : SubstitutionAction T S} {label : O → T}

/-- **Reached by one tell**: from rows without knowledge, the tell of a consistent equation. -/
theorem reached_by_tell {P : Finset O} {l r : T} (consistent : A.Consistent [(l, r)]) :
    Race.Moves A label (ruleOffers A) ⟨[], P⟩ (tellRule l r) ⟨[(l, r)], P⟩ :=
  moves_tell_iff.mpr ⟨consistent, rfl⟩

/-- Guards only. -/
def IsGuard (ρ : RuleInstance T) : Prop := ∃ l r, ρ = guardRule l r

/-- Takes only. -/
def IsTake (ρ : RuleInstance T) : Prop := ∃ ps, ρ = takeRule ps

/-- Rules without checks: takes, reads, tells and makes. -/
def CheckFree (ρ : RuleInstance T) : Prop := ρ.checks = []

/-- **Guards alone see the solutions only**: configurations with the same solutions are bisimilar
for the guards, whatever their rows. -/
theorem guardBisimilar_of_equivalent {C D : Configuration T O}
    (same : A.Equivalent C.equations D.equations) :
    Race.Bisimilar A label (formOffers A IsGuard) C D := by
  refine ⟨fun X Y => A.Equivalent X.equations Y.equations, ⟨?_, ?_, fun _ _ _ atom => atom.elim⟩, same⟩
  · rintro X Y related ρ X' moved
    obtain ⟨⟨l, r, rfl⟩, moved⟩ := moves_formOffers_iff.mp moved
    obtain ⟨⟨consistent, entailed⟩, rfl⟩ := moves_guard_iff.mp moved
    refine ⟨Y, moves_formOffers_iff.mpr ⟨⟨l, r, rfl⟩, moves_guard_iff.mpr ⟨⟨?_, ?_⟩, rfl⟩⟩, related⟩
    · exact (SubstitutionAction.equivalent_consistent A related).mp consistent
    · exact fun σ solved => entailed σ ((related σ).mpr solved)
  · rintro X Y related ρ Y' moved
    obtain ⟨⟨l, r, rfl⟩, moved⟩ := moves_formOffers_iff.mp moved
    obtain ⟨⟨consistent, entailed⟩, rfl⟩ := moves_guard_iff.mp moved
    refine ⟨X, moves_formOffers_iff.mpr ⟨⟨l, r, rfl⟩, moves_guard_iff.mpr ⟨⟨?_, ?_⟩, rfl⟩⟩, related⟩
    · exact (SubstitutionAction.equivalent_consistent A related).mpr consistent
    · exact fun σ solved => entailed σ ((related σ).mp solved)

/-- **Takes alone see no knowledge without rows**: consistent configurations without rows are
bisimilar for the takes. -/
theorem takeBisimilar_of_empty {C D : Configuration T O} (emptyC : C.present = ∅)
    (emptyD : D.present = ∅) (consistentC : A.Consistent C.equations)
    (consistentD : A.Consistent D.equations) :
    Race.Bisimilar A label (formOffers A IsTake) C D := by
  have nilOf : ∀ {X X' : Configuration T O} {ps : List T}, X.present = ∅ →
      Race.Moves A label (ruleOffers A) X (takeRule ps) X' → ps = [] := by
    intro X X' ps empty moved
    obtain ⟨taken, -, lengths, inside, -, -⟩ := moves_take_iff.mp moved
    have takenNil : taken = [] := List.eq_nil_iff_forall_not_mem.mpr fun o member => by
      have present := inside o member
      rw [empty] at present
      exact Finset.notMem_empty o present
    rw [takenNil] at lengths
    exact List.eq_nil_of_length_eq_zero lengths
  refine ⟨fun X Y => X.present = ∅ ∧ Y.present = ∅ ∧ A.Consistent X.equations ∧
      A.Consistent Y.equations, ⟨?_, ?_, fun _ _ _ atom => atom.elim⟩,
    emptyC, emptyD, consistentC, consistentD⟩
  · rintro X Y related ρ X' moved
    obtain ⟨⟨ps, rfl⟩, moved⟩ := moves_formOffers_iff.mp moved
    obtain rfl := nilOf related.1 moved
    obtain ⟨-, rfl⟩ := moves_takeNil_iff.mp moved
    exact ⟨Y, moves_formOffers_iff.mpr ⟨⟨[], rfl⟩, moves_takeNil_iff.mpr ⟨related.2.2.2, rfl⟩⟩, related⟩
  · rintro X Y related ρ Y' moved
    obtain ⟨⟨ps, rfl⟩, moved⟩ := moves_formOffers_iff.mp moved
    obtain rfl := nilOf related.2.1 moved
    obtain ⟨-, rfl⟩ := moves_takeNil_iff.mp moved
    exact ⟨X, moves_formOffers_iff.mpr ⟨⟨[], rfl⟩, moves_takeNil_iff.mpr ⟨related.2.2.1, rfl⟩⟩, related⟩

/-- **Without checks, a step whose every store is consistent sees no knowledge**: configurations
with the same rows are bisimilar for the rules without checks. -/
theorem checkFreeBisimilar_of_present (allConsistent : ∀ K : EquationStore T, A.Consistent K)
    {C D : Configuration T O} (same : C.present = D.present) :
    Race.Bisimilar A label (formOffers A CheckFree) C D := by
  have transfer : ∀ {X Y : Configuration T O}, X.present = Y.present → ∀ (ρ : RuleInstance T)
      (X' : Configuration T O), Race.Moves A label (formOffers A CheckFree) X ρ X' →
        ∃ Y', Race.Moves A label (formOffers A CheckFree) Y ρ Y' ∧ X'.present = Y'.present := by
    intro X Y related ρ X' moved
    obtain ⟨free, moved⟩ := moves_formOffers_iff.mp moved
    obtain ⟨selection, valid, rfl⟩ := moves_iff_step.mp moved
    have enabled := valid.occurrences
    rw [related] at enabled
    have valid' : selection.Valid A label ρ Y :=
      ⟨valid.take_distinct, valid.output_distinct, valid.take_length, valid.read_length,
        valid.outputs, enabled, allConsistent _, fun check member => by
          rw [show ρ.checks = [] from free] at member
          cases member⟩
    refine ⟨_, moves_formOffers_iff.mpr ⟨free, moves_iff_step.mpr ⟨selection, valid', rfl⟩⟩, ?_⟩
    show fire X.present _ = fire Y.present _
    rw [related]
  refine ⟨fun X Y => X.present = Y.present, ⟨?_, ?_, fun _ _ _ atom => atom.elim⟩, same⟩
  · intro X Y related ρ X' moved
    exact transfer related ρ X' moved
  · intro X Y related ρ Y' moved
    obtain ⟨X', moved', related'⟩ := transfer related.symm ρ Y' moved
    exact ⟨X', moved', related'.symm⟩

end Forms

/-! ## Controls -/

namespace ProgramFreeControls

open Observation.ModuloControls (Tm X Y label c2 knowsXY clash twoX twoY entailed_XY zeros_solves
  c2_equivalent X_ne_Y solves_id_iff)
open ConstraintMultisetRewriting.Controls (signature A)
open AnnotatedRuns.Controls (zeros)

/-! ### Consistency -/

theorem clash_inconsistent : ¬ A.Consistent clash := by
  rintro ⟨σ, solved⟩
  have clashes : (Term.const 0 : Tm) = .const 1 := solved _ (List.mem_singleton_self _)
  exact absurd (Term.const.inj clashes) (by decide)

/-- **Consistency is needed for `moduloEquivalent_of_bisimilar`**, whose one hypothesis it is: one row
against two under the knowledge `0 = 1` are bisimilar, since neither moves, and not equivalent modulo
the knowledge for any escaped identities. No move reaches them. The labelling of C2 has no fresh
supply (`not_freshSupply`), so for `ruleOffers_bisimilar_iff` this pair fails both hypotheses; its
control for consistency alone is `consistency_alone`. -/
theorem consistency_needed :
    Race.Bisimilar A label (ruleOffers A) ⟨clash, {20}⟩ ⟨clash, {20, 21}⟩ ∧
      ¬ (∃ E, ModuloEquivalent A label E ⟨clash, {20}⟩ ⟨clash, {20, 21}⟩) ∧
      ∀ (C : Configuration Tm ℕ) (ρ : RuleInstance Tm) (present : Finset ℕ),
        ¬ Race.Moves A label (ruleOffers A) C ρ ⟨clash, present⟩ :=
  ⟨Race.bisimilar_of_halted (fun _ _ => Semantic.no_moves_of_inconsistent clash_inconsistent)
      (fun _ _ => Semantic.no_moves_of_inconsistent clash_inconsistent),
    fun h => Observation.ModuloControls.inconsistent_pointwise.2 (exists_moduloEquivalent_iff.mp h),
    fun _ _ _ moved => clash_inconsistent (consistent_of_moves moved)⟩

/-! ### A fresh supply -/

/-- The rule that makes two rows `X`. -/
def makeTwoX : RuleInstance Tm := ⟨[], [], [], [], [X, X]⟩

/-- Only `20` and `22` carry `X`. -/
theorem label_eq_X {o : ℕ} (labelled : label o = X) : o = 20 ∨ o = 22 := by
  unfold Observation.ModuloControls.label at labelled
  split at labelled <;> simp_all

/-- **The labels of C2 have no fresh supply.** -/
theorem not_freshSupply : ¬ FreshSupply label := by
  intro supply
  obtain ⟨o, outside, labelled⟩ := supply 20 {20, 22}
  rcases label_eq_X labelled with rfl | rfl <;> simp at outside

/-- **C2 is reached**: from one row, by the tell of `X = Y`. -/
theorem c2_reached (o : ℕ) : Race.Moves A label (ruleOffers A) ⟨[], {o}⟩ (tellRule X Y) (c2 o) :=
  moves_tell_iff.mpr ⟨⟨zeros, zeros_solves⟩, rfl⟩

theorem makeTwoX_at_21 : Race.Sat A label (ruleOffers A) (.dia makeTwoX .top) (c2 21) := by
  refine Race.sat_dia.mpr ⟨_, moves_iff_step.mpr ⟨⟨[], [], [20, 22]⟩, ?_, rfl⟩, Race.sat_top _⟩
  refine ⟨List.nodup_nil, by decide, rfl, rfl, rfl, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨zeros, ?_⟩, ?_⟩
  · simp [Selection.commit]
  · simp [Selection.commit]
  · simp [Selection.commit]
  · simp [Selection.commit, c2]
  · simp [Selection.commit]
  · intro e member
    have known : e ∈ knowsXY := by
      simpa [Selection.problem, Selection.equations, makeTwoX, c2] using member
    exact zeros_solves e known
  · intro check member
    simp [makeTwoX] at member

theorem makeTwoX_not_at_20 : ¬ Race.Sat A label (ruleOffers A) (.dia makeTwoX .top) (c2 20) := by
  rintro ⟨C', moved, -⟩
  obtain ⟨⟨taken, read, made⟩, valid, -⟩ := moves_iff_step.mp moved
  have outputs : made.map label = [X, X] := valid.outputs
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp (by simpa using congrArg List.length outputs)
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at outputs
  have fresh : Disjoint ([a, b].toFinset) ({20} : Finset ℕ) := valid.occurrences.fresh
  have nodup : ([a, b] : List ℕ).Nodup := valid.output_distinct
  rcases label_eq_X outputs.1 with rfl | rfl
  · exact absurd fresh (by simp)
  · rcases label_eq_X outputs.2.1 with rfl | rfl
    · exact absurd fresh (by simp)
    · exact absurd nodup (by decide)

/-- **A fresh supply is needed**: C2 has consistent knowledge, is equivalent modulo the knowledge and
bisimilar for the probe step, but its labels have no fresh supply, and it is not bisimilar for the
program-free step: the rule that makes two rows `X` moves at the second state only. The one
hypothesis of `ruleOffers_bisimilar_iff` that fails is the fresh supply. -/
theorem freshSupply_needed :
    A.Consistent (c2 20).equations ∧ ModuloEquivalent A label ∅ (c2 20) (c2 21) ∧
      ¬ FreshSupply label ∧ Race.Bisimilar A label (probeOffers A) (c2 20) (c2 21) ∧
      ¬ Race.Bisimilar A label (ruleOffers A) (c2 20) (c2 21) :=
  ⟨⟨zeros, zeros_solves⟩, c2_equivalent, not_freshSupply,
    probeBisimilar_of_moduloEquivalent c2_equivalent,
    fun h => makeTwoX_not_at_20 ((Race.sat_iff_of_bisimilar h _).mpr makeTwoX_at_21)⟩

/-! ### Rule forms -/

/-- **Guards alone are too coarse**: one row against none. -/
theorem guards_alone_coarser :
    Race.Bisimilar A label (formOffers A IsGuard) ⟨[], {20}⟩ ⟨[], ∅⟩ ∧
      ¬ ModuloEquivalent A label ∅ ⟨[], {20}⟩ ⟨[], ∅⟩ :=
  ⟨guardBisimilar_of_equivalent fun _ => Iff.rfl, fun h => absurd h.card_eq (by decide)⟩

/-- **Takes alone are too coarse**: without rows, the knowledge `X = 0` against none. -/
theorem takes_alone_coarser :
    Race.Bisimilar A label (formOffers A IsTake) ⟨[(X, .const 0)], ∅⟩ ⟨[], ∅⟩ ∧
      ¬ ModuloEquivalent A label ∅ ⟨[(X, .const 0)], ∅⟩ ⟨[], ∅⟩ := by
  refine ⟨takeBisimilar_of_empty rfl rfl ⟨zeros, fun e member => ?_⟩ ⟨zeros, A.models_nil _⟩,
    fun h => ?_⟩
  · rw [List.mem_singleton.mp member]
    rfl
  · have atIdentity := (h.solutions (Subst.id signature)).mpr (A.models_nil _)
    have solved := (solves_id_iff X (.const 0)).mp (atIdentity _ (List.mem_singleton_self _))
    exact absurd solved (by simp)

/-- **A signature with one constant and no function symbol.** -/
abbrev oneConstant : LPSignature where
  constants := Unit
  vars := ℕ
  relationSymbols := Unit
  relationArity _ := 0
  functionSymbols := Empty
  functionArity e := e.elim

/-- **Every store over one constant is consistent**: send every unknown to the constant. -/
theorem oneConstant_consistent (K : EquationStore (Term oneConstant)) :
    (FirstOrder.action oneConstant).Consistent K := by
  have collapse : ∀ t : Term oneConstant, Subst.applyTerm (fun _ => .const ()) t = .const () := by
    intro t
    cases t with
    | var v => rfl
    | const c => rfl
    | app f _ => exact f.elim
  refine ⟨fun _ => .const (), fun e _ => ?_⟩
  show Subst.applyTerm _ e.1 = Subst.applyTerm _ e.2
  rw [collapse, collapse]

/-- **Without checks the knowledge is invisible there**: the knowledge `x = c` against none, with no
rows, are bisimilar for every rule without checks (takes, reads, tells and makes), and not
equivalent modulo the knowledge. -/
theorem checkFree_coarser :
    Race.Bisimilar (FirstOrder.action oneConstant) (fun _ : ℕ => .var 0)
        (formOffers (FirstOrder.action oneConstant) CheckFree) ⟨[(.var 0, .const ())], ∅⟩ ⟨[], ∅⟩ ∧
      ¬ ModuloEquivalent (FirstOrder.action oneConstant) (fun _ : ℕ => .var 0) ∅
        ⟨[(.var 0, .const ())], ∅⟩ ⟨[], ∅⟩ := by
  refine ⟨checkFreeBisimilar_of_present oneConstant_consistent rfl, fun h => ?_⟩
  have atIdentity := (h.solutions (Subst.id oneConstant)).mpr ((FirstOrder.action oneConstant).models_nil _)
  have solved : (Term.var 0 : Term oneConstant) = .const () := atIdentity _ (List.mem_singleton_self _)
  exact absurd solved (by simp)

/-! ### Neighbouring equivalences -/

/-- Labels by parity: `X` on even identities, `Y` on odd ones. -/
def labelParity (n : ℕ) : Tm := if n % 2 = 0 then X else Y

theorem parity_supply : FreshSupply labelParity := by
  intro o G
  refine ⟨o + 2 * (G.sup id + 1), fun member => ?_, ?_⟩
  · have bound := Finset.le_sup (f := id) member
    simp only [id] at bound
    omega
  · simp [labelParity, Nat.add_mul_mod_self_left]

/-- **Consistency is needed, with a fresh supply**: under the labelling by parity, which has a fresh
supply, one row against two under the knowledge `0 = 1` are bisimilar for the program-free step,
since neither moves, and not equivalent modulo the knowledge for any escaped identities. The one
hypothesis of `ruleOffers_bisimilar_iff` that fails is consistency. -/
theorem consistency_alone :
    FreshSupply labelParity ∧ ¬ A.Consistent clash ∧
      Race.Bisimilar A labelParity (ruleOffers A) ⟨clash, {0}⟩ ⟨clash, {0, 2}⟩ ∧
      ¬ (∃ E, ModuloEquivalent A labelParity E ⟨clash, {0}⟩ ⟨clash, {0, 2}⟩) := by
  refine ⟨parity_supply, clash_inconsistent, ?_, ?_⟩
  · exact Race.bisimilar_of_halted
      (fun _ _ => Semantic.no_moves_of_inconsistent clash_inconsistent)
      (fun _ _ => Semantic.no_moves_of_inconsistent clash_inconsistent)
  · rintro ⟨E, h⟩
    exact absurd h.card_eq (by decide)

theorem parity_equivalent : ModuloEquivalent A labelParity ∅ ⟨knowsXY, {0}⟩ ⟨knowsXY, {1}⟩ := by
  refine (moduloEquivalent_iff A labelParity ∅ _ _).mpr
    ⟨fun _ => Iff.rfl, fun o member => absurd member (Finset.notMem_empty o), ?_⟩
  show ({0} : Finset ℕ).val.map (fun o => Quotient.mk (entailedSetoid A knowsXY) (labelParity o)) =
    ({1} : Finset ℕ).val.map (fun o => Quotient.mk (entailedSetoid A knowsXY) (labelParity o))
  rw [Finset.singleton_val, Finset.singleton_val, Multiset.map_singleton, Multiset.map_singleton]
  exact congrArg (fun c => ({c} : Multiset _)) (Quotient.sound entailed_XY)

/-- **Private equivalence is too fine**: rows `0 : X` and `1 : Y` under `X = Y`, with a fresh supply,
are bisimilar for the program-free step and not privately equivalent. -/
theorem private_too_fine :
    Race.Bisimilar A labelParity (ruleOffers A) ⟨knowsXY, {0}⟩ ⟨knowsXY, {1}⟩ ∧
      ¬ PrivatelyEquivalent A labelParity ∅ ⟨knowsXY, {0}⟩ ⟨knowsXY, {1}⟩ := by
  refine ⟨(ruleOffers_bisimilar_iff parity_supply ⟨zeros, zeros_solves⟩).mpr ⟨∅, parity_equivalent⟩,
    fun h => ?_⟩
  have bags := h.labels_eq
  simp only [Finset.singleton_val, Multiset.map_singleton, Multiset.singleton_inj] at bags
  exact X_ne_Y bags

/-- **Pointwise equivalence is too coarse**: the stores of the action without a principal answer are
pointwise equivalent and not bisimilar. -/
theorem pointwise_too_coarse :
    PointwiseEquivalent Observation.NonPrincipal.action Observation.NonPrincipal.label ∅
        Observation.NonPrincipal.left Observation.NonPrincipal.right ∧
      ¬ Race.Bisimilar Observation.NonPrincipal.action Observation.NonPrincipal.label
        (ruleOffers Observation.NonPrincipal.action)
        Observation.NonPrincipal.left Observation.NonPrincipal.right :=
  ⟨Observation.NonPrincipal.pointwise, fun h => Observation.NonPrincipal.not_modulo
    (moduloEquivalent_of_bisimilar h ⟨_, Observation.NonPrincipal.first_solves⟩)⟩

/-- **The run layer's static probes are too coarse**: they agree on `X, Y, X` and `X, Y, Y` with empty
knowledge, which are not bisimilar. -/
theorem runProbes_too_coarse :
    (∀ p : Observation.Probe Tm (Subst signature) ℕ, p.names ⊆ ∅ →
        (p.Observes A label twoX ↔ p.Observes A label twoY)) ∧
      ¬ Race.Bisimilar A label (ruleOffers A) twoX twoY :=
  ⟨Observation.ModuloControls.existing_probes_agree, fun h =>
    Observation.ModuloControls.uniform_not_abstract.2.2.1
      (moduloEquivalent_of_bisimilar h ⟨Subst.id signature, A.models_nil _⟩)⟩

/-! ### What the program-free step sees of the knowledge -/

/-- **Knowledge about an unknown that no row mentions is seen**: without rows, `X = 0` against no
knowledge are not bisimilar for the program-free step; the guard `X = 0` tells them apart. -/
theorem unmentioned_knowledge_visible :
    ¬ Race.Bisimilar A label (ruleOffers A) ⟨[(X, .const 0)], ∅⟩ ⟨[], ∅⟩ :=
  fun h => takes_alone_coarser.2 (moduloEquivalent_of_bisimilar h ⟨zeros, fun e member => by
    rw [List.mem_singleton.mp member]
    rfl⟩)

/-- **The store remembers its history, and the program-free step sees it**: from the row `20 : X`
alone, the take under the pattern `Y` and the take under the pattern `X` remove the same row; the
first remembers `Y = X`, and the two results are not bisimilar. -/
theorem history_visible :
    Race.Moves A label (ruleOffers A) (Observation.ModuloControls.free 20) (takeRule [Y])
        ⟨[(Y, X)], ∅⟩ ∧
      Race.Moves A label (ruleOffers A) (Observation.ModuloControls.free 20) (takeRule [X])
        ⟨[(X, X)], ∅⟩ ∧
      ¬ Race.Bisimilar A label (ruleOffers A) ⟨[(Y, X)], ∅⟩ ⟨[(X, X)], ∅⟩ := by
  have taking : ∀ p : Tm, A.Consistent [(p, X)] →
      Race.Moves A label (ruleOffers A) (Observation.ModuloControls.free 20) (takeRule [p])
        ⟨[(p, X)], ∅⟩ := by
    intro p consistent
    refine moves_take_iff.mpr ⟨[20], by decide, rfl, by simp [Observation.ModuloControls.free],
      consistent, ?_⟩
    rw [Configuration.mk.injEq]
    exact ⟨rfl, by simp [Observation.ModuloControls.free]⟩
  have consistentYX : A.Consistent [(Y, X)] := ⟨zeros, fun e member => by
    rw [List.mem_singleton.mp member]
    rfl⟩
  have consistentXX : A.Consistent [(X, X)] := ⟨zeros, fun e member => by
    rw [List.mem_singleton.mp member]
    rfl⟩
  refine ⟨taking Y consistentYX, taking X consistentXX, fun h => ?_⟩
  have same := (moduloEquivalent_of_bisimilar h consistentYX).solutions (Subst.id signature)
  have solved : A.Models (Subst.id signature) [(Y, X)] := same.mpr fun e member => by
    rw [List.mem_singleton.mp member]
    rfl
  exact X_ne_Y ((solves_id_iff Y X).mp (solved _ (List.mem_singleton_self _))).symm

/-! ### The multiplicity probe -/

open Classical in
/-- The rows of C2 whose labels the knowledge `X = Y` entails equal to `Y`: the row `20 : X`. -/
theorem c2_class_Y :
    ((c2 20).present.filter fun o => Entailed A (c2 20).equations Y (label o)).card = 1 := by
  have entailedYX : Entailed A (c2 20).equations Y (label 20) := fun σ solved =>
    A.equivalence.symm (entailed_XY σ solved)
  rw [show (c2 20).present = {20} from rfl, Finset.filter_singleton, if_pos entailedYX,
    Finset.card_singleton]

open Classical in
/-- Without knowledge, no row is entailed equal to `Y`: the row `20 : X` is not. -/
theorem free_class_Y :
    ((Observation.ModuloControls.free 20).present.filter fun o =>
      Entailed A (Observation.ModuloControls.free 20).equations Y (label o)).card = 0 := by
  have notEntailed : ¬ Entailed A (Observation.ModuloControls.free 20).equations Y (label 20) :=
    fun entailed =>
    X_ne_Y ((solves_id_iff Y X).mp (entailed (Subst.id signature) (A.models_nil _))).symm
  rw [show (Observation.ModuloControls.free 20).present = {20} from rfl, Finset.filter_singleton,
    if_neg notEntailed, Finset.card_empty]

/-- **The multiplicity probe on labels equal modulo the knowledge**: under `X = Y`, the take of one
`Y` takes the row `20 : X` and learns nothing, and the take of two `Y` cannot; without the
knowledge, the take of one `Y` cannot take the row without learning `Y = X` (`history_visible`). -/
theorem multiplicity_examples :
    (∃ C', Race.Moves A label (ruleOffers A) (c2 20) (takeRule (List.replicate 1 Y)) C' ∧
        A.Equivalent C'.equations (c2 20).equations) ∧
      ¬ (∃ C', Race.Moves A label (ruleOffers A) (c2 20) (takeRule (List.replicate 2 Y)) C' ∧
        A.Equivalent C'.equations (c2 20).equations) ∧
      ¬ (∃ C', Race.Moves A label (ruleOffers A) (Observation.ModuloControls.free 20)
        (takeRule (List.replicate 1 Y)) C' ∧
          A.Equivalent C'.equations (Observation.ModuloControls.free 20).equations) := by
  have consistentC2 : A.Consistent (c2 20).equations := ⟨zeros, zeros_solves⟩
  have consistentFree : A.Consistent (Observation.ModuloControls.free 20).equations :=
    ⟨zeros, A.models_nil _⟩
  refine ⟨(moves_takeCopies_iff consistentC2).mpr ?_, fun h => ?_, fun h => ?_⟩
  · rw [c2_class_Y]
  · have counted := (moves_takeCopies_iff consistentC2).mp h
    rw [c2_class_Y] at counted
    omega
  · have counted := (moves_takeCopies_iff consistentFree).mp h
    rw [free_class_Y] at counted
    omega

/-- **The controls' configurations are reached**: each from rows without knowledge, by one tell. -/
theorem controls_reached :
    Race.Moves A label (ruleOffers A) ⟨[], ∅⟩ (tellRule X (.const 0)) ⟨[(X, .const 0)], ∅⟩ ∧
      Race.Moves A labelParity (ruleOffers A) ⟨[], {0}⟩ (tellRule X Y) ⟨knowsXY, {0}⟩ ∧
      Race.Moves A labelParity (ruleOffers A) ⟨[], {1}⟩ (tellRule X Y) ⟨knowsXY, {1}⟩ ∧
      Race.Moves (FirstOrder.action oneConstant) (fun _ : ℕ => .var 0)
        (ruleOffers (FirstOrder.action oneConstant)) ⟨[], ∅⟩ (tellRule (.var 0) (.const ()))
        ⟨[(.var 0, .const ())], ∅⟩ ∧
      Race.Moves Observation.NonPrincipal.action Observation.NonPrincipal.label
        (ruleOffers Observation.NonPrincipal.action) ⟨[], {1, 2}⟩
        (tellRule Observation.NonPrincipal.Atom.x Observation.NonPrincipal.Atom.zero)
        Observation.NonPrincipal.left ∧
      Race.Moves Observation.NonPrincipal.action Observation.NonPrincipal.label
        (ruleOffers Observation.NonPrincipal.action) ⟨[], {3, 4}⟩
        (tellRule Observation.NonPrincipal.Atom.x Observation.NonPrincipal.Atom.zero)
        Observation.NonPrincipal.right :=
  ⟨reached_by_tell ⟨zeros, fun e member => by
      rw [List.mem_singleton.mp member]
      rfl⟩,
    reached_by_tell ⟨zeros, zeros_solves⟩, reached_by_tell ⟨zeros, zeros_solves⟩,
    reached_by_tell (oneConstant_consistent _),
    reached_by_tell ⟨_, Observation.NonPrincipal.first_solves⟩,
    reached_by_tell ⟨_, Observation.NonPrincipal.first_solves⟩⟩

end ProgramFreeControls

#print axioms bag_eq_iff_of_kernel
#print axioms ground_bisimilar_iff
#print axioms issuing_ground_bisimilar_iff
#print axioms firstOrder_bisimilar_iff
#print axioms firstOrder_bisimilar_iff_observes
#print axioms guardBisimilar_of_equivalent
#print axioms takeBisimilar_of_empty
#print axioms checkFreeBisimilar_of_present
#print axioms ProgramFreeControls.consistency_needed
#print axioms ProgramFreeControls.label_eq_X
#print axioms ProgramFreeControls.not_freshSupply
#print axioms ProgramFreeControls.c2_reached
#print axioms ProgramFreeControls.freshSupply_needed
#print axioms ProgramFreeControls.guards_alone_coarser
#print axioms ProgramFreeControls.takes_alone_coarser
#print axioms ProgramFreeControls.oneConstant_consistent
#print axioms ProgramFreeControls.checkFree_coarser
#print axioms ProgramFreeControls.parity_supply
#print axioms ProgramFreeControls.consistency_alone
#print axioms ProgramFreeControls.private_too_fine
#print axioms ProgramFreeControls.pointwise_too_coarse
#print axioms ProgramFreeControls.runProbes_too_coarse
#print axioms reached_by_tell
#print axioms ProgramFreeControls.unmentioned_knowledge_visible
#print axioms ProgramFreeControls.history_visible
#print axioms ProgramFreeControls.controls_reached
#print axioms ProgramFreeControls.c2_class_Y
#print axioms ProgramFreeControls.free_class_Y
#print axioms ProgramFreeControls.multiplicity_examples

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.ProgramFreeBisimilarity
