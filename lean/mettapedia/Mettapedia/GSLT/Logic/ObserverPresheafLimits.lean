import Mettapedia.GSLT.Logic.ObserverPresheafControls

/-!
# Limits of observer towers

A directed family of admissible classes has a supremum in the observer lattice, and
the supremum admits exactly the contexts of the family (`admissible_iSup_iff`).
Does the supremum observe more than all members of the family together?

* **Continuity under image-finiteness** (`relEquiv_iSup_iff`).  When every filled
  term has finitely many reducts up to the equations, the relative equivalence of
  the supremum is the intersection of the relative equivalences of the family.
  The comparison map from the stage of the supremum into the family of stages is
  then injective (`limitComparison_injective`): the limit observer's stage is
  determined by the finite stages.  The proof is a pigeonhole argument over the
  finitely many reducts and uses classical logic.
* **Positive control.**  The oracle tower is image-finite, so its limit stage is
  continuous (`OracleTower.relEquiv_iSup_stage_iff`).
* **Negative control.**  In a branching tower, a term with infinitely many
  reducts is equivalent at every finite stage to a term with one reduct more, and
  separated at the limit (`BranchingTower.not_continuous`): without
  image-finiteness the limit observer sees what no finite stage sees.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.AdmissibleContextCongruence

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.MinimalEnablingContext

universe uS uContext uRule uAtom uι

namespace AdmissibleClass

variable {S : GSLT.{uS}} {rules : ContextualRules.{uContext, uRule} S}
variable {ι : Type uι} (F : ι → AdmissibleClass rules)

/-- The union of a nonempty directed family of classes is a class. -/
def directedUnion (base : ι) (directed : Directed (· ≤ ·) F) : AdmissibleClass rules where
  Admissible context := ∃ i, (F i).Admissible context
  identity_mem := ⟨base, (F base).identity_mem⟩
  compose_mem := by
    rintro outer inner ⟨i, outerIn⟩ ⟨j, innerIn⟩
    obtain ⟨k, ik, jk⟩ := directed i j
    exact ⟨k, (F k).compose_mem (ik _ outerIn) (jk _ innerIn)⟩

/-- **The supremum of a nonempty directed family admits exactly the contexts of
its members.** -/
theorem admissible_iSup_iff (base : ι) (directed : Directed (· ≤ ·) F)
    {context : rules.Context} :
    (⨆ i, F i).Admissible context ↔ ∃ i, (F i).Admissible context := by
  constructor
  · intro admissible
    exact (iSup_le fun i _ member => ⟨i, member⟩ :
      (⨆ i, F i) ≤ directedUnion F base directed) context admissible
  · rintro ⟨i, member⟩
    exact (le_iSup F i) context member

/-- A finite list of indices has an upper bound in a nonempty directed family. -/
theorem exists_upper_bound (base : ι) (directed : Directed (· ≤ ·) F) (indices : List ι) :
    ∃ k, ∀ i ∈ indices, F i ≤ F k := by
  induction indices with
  | nil => exact ⟨base, fun _ member => (List.not_mem_nil member).elim⟩
  | cons i rest ih =>
    obtain ⟨k, below⟩ := ih
    obtain ⟨k', ik', kk'⟩ := directed i k
    refine ⟨k', fun j member => ?_⟩
    rcases List.mem_cons.mp member with rfl | inRest
    · exact ik'
    · exact le_trans (below j inRest) kk'

/-- Every filled term has finitely many reducts up to the equations. -/
def FilledImageFinite (rules : ContextualRules.{uContext, uRule} S) : Prop :=
  ∀ (context : rules.Context) (term : S.Term), ∃ reducts : List S.Term,
    ∀ target, S.Step (rules.plug context term) target → ∃ reduct ∈ reducts, S.Equiv target reduct

variable (observations : ContextualRules.Observations.{uAtom} S)

open Classical in
/-- The pigeonhole step: finitely many candidates, each refuted at some index,
are all refuted at one index. -/
private theorem exists_index_refuting_all (base : ι) (directed : Directed (· ≤ ·) F)
    (candidate : S.Term → Prop) (left : S.Term) (candidates : List S.Term)
    (refuted : ∀ u ∈ candidates, candidate u → ¬ ∀ i, (F i).RelEquiv observations left u) :
    ∃ k, ∀ u ∈ candidates, candidate u → ¬ (F k).RelEquiv observations left u := by
  induction candidates with
  | nil => exact ⟨base, fun _ member => (List.not_mem_nil member).elim⟩
  | cons u rest ih =>
    obtain ⟨k, belowRest⟩ := ih fun v member => refuted v (List.mem_cons_of_mem u member)
    by_cases isCandidate : candidate u
    · obtain ⟨i, notAtI⟩ := not_forall.mp (refuted u (List.mem_cons_self) isCandidate)
      obtain ⟨k', ik', kk'⟩ := directed i k
      refine ⟨k', fun v member vCandidate relatedK' => ?_⟩
      rcases List.mem_cons.mp member with rfl | inRest
      · exact notAtI (AdmissibleClass.relEquiv_antitone observations ik' relatedK')
      · exact belowRest v inRest vCandidate (AdmissibleClass.relEquiv_antitone observations kk' relatedK')
    · refine ⟨k, fun v member vCandidate => ?_⟩
      rcases List.mem_cons.mp member with rfl | inRest
      · exact (isCandidate vCandidate).elim
      · exact belowRest v inRest vCandidate

open Classical in
/-- One direction of the transfer property of the intersection of the family's
equivalences, for a label of the supremum. -/
private theorem intersection_forward (base : ι) (directed : Directed (· ≤ ·) F)
    (finite : FilledImageFinite rules) {left right : S.Term}
    (related : ∀ i, (F i).RelEquiv observations left right)
    {context : rules.Context} (admissible : (⨆ i, F i).Admissible context)
    {left' : S.Term} (step : S.Step (rules.plug context left) left') :
    ∃ right', S.Step (rules.plug context right) right' ∧
      ∀ i, (F i).RelEquiv observations left' right' := by
  obtain ⟨m, atM⟩ := (admissible_iSup_iff F base directed).mp admissible
  obtain ⟨reducts, covers⟩ := finite context right
  -- at every index, some listed reduct is a matching step
  have atEvery : ∀ i, ∃ u ∈ reducts, S.Step (rules.plug context right) u ∧
      (F i).RelEquiv observations left' u := by
    intro i
    obtain ⟨k, ik, mk⟩ := directed i m
    obtain ⟨right', rightStep, relatedK⟩ := AdmissibleContextCongruence.bisimilar_forward
      (related k) (⟨context, mk _ atM⟩ : ((F k).saturated observations).Label) step
    obtain ⟨u, member, equivalent⟩ := covers right' rightStep
    exact ⟨u, member, S.rewrites_resp_right rightStep equivalent,
      AdmissibleClass.relEquiv_antitone observations ik
        ((F k).relEquiv_trans observations relatedK ((F k).relEquiv_of_equiv observations equivalent))⟩
  by_contra none
  have refuted : ∀ u ∈ reducts, S.Step (rules.plug context right) u →
      ¬ ∀ i, (F i).RelEquiv observations left' u :=
    fun u _ uStep good => none ⟨u, uStep, good⟩
  obtain ⟨k, allRefuted⟩ := exists_index_refuting_all F observations base directed
    (fun u => S.Step (rules.plug context right) u) left' reducts refuted
  obtain ⟨u, member, uStep, relatedK⟩ := atEvery k
  exact allRefuted u member uStep relatedK

/-- **Continuity at directed suprema under image-finiteness**: the supremum's
relative equivalence is the intersection of the family's. -/
theorem relEquiv_iSup_iff (base : ι) (directed : Directed (· ≤ ·) F)
    (finite : FilledImageFinite rules) (left right : S.Term) :
    (⨆ i, F i).RelEquiv observations left right ↔ ∀ i, (F i).RelEquiv observations left right := by
  constructor
  · intro related i
    exact AdmissibleClass.relEquiv_antitone observations (le_iSup F i) related
  · intro related
    refine ⟨fun first second => ∀ i, (F i).RelEquiv observations first second,
      ⟨?_, ?_, ?_⟩, related⟩
    · intro first second held label first' step
      exact intersection_forward F observations base directed finite held label.2 step
    · intro first second held label second' step
      obtain ⟨first', firstStep, related'⟩ := intersection_forward F observations base directed
        finite (fun i => (F i).relEquiv_symm observations (held i)) label.2 step
      exact ⟨first', firstStep, fun i => (F i).relEquiv_symm observations (related' i)⟩
    · intro first second held atom
      obtain ⟨m, atM⟩ := (admissible_iSup_iff F base directed).mp atom.2.2
      exact AdmissibleContextCongruence.bisimilar_observes (held m)
        (atom.1, ⟨atom.2.1, atM⟩)

/-- **The limit stage is determined by the finite stages**: the comparison map from
the stage of the supremum into the family of stages is injective. -/
theorem limitComparison_injective (base : ι) (directed : Directed (· ≤ ·) F)
    (finite : FilledImageFinite rules) :
    Function.Injective (fun x : Stage observations (⨆ i, F i) =>
      fun i => restrict observations (le_iSup F i) x) := by
  intro x y equal
  induction x using Quotient.inductionOn with
  | _ left =>
    induction y using Quotient.inductionOn with
    | _ right =>
      apply (stageClass_eq_iff observations (⨆ i, F i) left right).mpr
      apply (relEquiv_iSup_iff F observations base directed finite left right).mpr
      intro i
      exact (stageClass_eq_iff observations (F i) left right).mp (congrFun equal i)

end AdmissibleClass

namespace ObserverPresheafControls

open AdmissibleClass

/-! ## Positive control: the oracle tower is continuous at its limit -/

namespace OracleTower

theorem stage_directed : Directed (· ≤ ·) stage :=
  fun m n => ⟨max m n, stage_monotone (le_max_left m n), stage_monotone (le_max_right m n)⟩

theorem opens_target {source target : Tm} (step : Opens source target) : target = .opened := by
  cases step
  rfl

/-- Every filled term has at most one reduct, the opened residue. -/
theorem filledImageFinite : FilledImageFinite towerRules :=
  fun _ _ => ⟨[.opened], fun _ step => ⟨.opened, List.mem_singleton_self _, opens_target step⟩⟩

/-- **The limit of the oracle tower sees exactly what its finite stages see.** -/
theorem relEquiv_iSup_stage_iff (left right : Tm) :
    (⨆ n, stage n).RelEquiv silent left right ↔ ∀ n, (stage n).RelEquiv silent left right :=
  relEquiv_iSup_iff stage silent 0 stage_directed filledImageFinite left right

end OracleTower

/-! ## Negative control: a branching tower is not continuous -/

namespace BranchingTower

/-- Leaves, the opened residue, probes, and two branching terms. -/
inductive Tm where
  | leaf (level : ℕ) (live : Bool)
  | opened
  | probe (level : ℕ) (body : Tm)
  | many
  | manyPlus
  deriving DecidableEq

/-- Probes open live leaves of their level; `many` reduces to every live leaf;
`manyPlus` reduces to every live leaf and to the opened residue. -/
inductive Steps : Tm → Tm → Prop where
  | fire (level : ℕ) : Steps (.probe level (.leaf level true)) .opened
  | branch (level : ℕ) : Steps .many (.leaf level true)
  | branchPlus (level : ℕ) : Steps .manyPlus (.leaf level true)
  | extra : Steps .manyPlus .opened

abbrev branchingGSLT : GSLT where
  Term := Tm
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := Steps
  rewrites_resp_left := by
    intro source source' target equal step
    subst equal
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst equal
    exact step

def plugProbes (levels : List ℕ) (term : Tm) : Tm :=
  levels.foldr Tm.probe term

abbrev branchingRules : ContextualRules branchingGSLT where
  Context := List ℕ
  identity := []
  compose outer inner := outer ++ inner
  plug := plugProbes
  plug_identity _ := rfl
  plug_compose _ _ _ := List.foldr_append
  plug_resp context := by
    intro left right equal
    subst equal
    rfl
  Rule := Unit
  fires _ := Steps
  fires_resp_left := by
    intro _ left right target equal fires
    subst equal
    exact ⟨target, fires, rfl⟩
  fires_resp_right := by
    intro _ source target target' fires equal
    subst equal
    exact fires
  fires_step := fun fires => fires

abbrev silent : ContextualRules.Observations branchingGSLT where
  Atom := Empty
  observes atom _ := atom.elim
  observes_resp atom := atom.elim

def below (n : ℕ) : AdmissibleClass branchingRules where
  Admissible levels := ∀ level ∈ levels, level < n
  identity_mem := fun _ member => (List.not_mem_nil member).elim
  compose_mem := by
    intro outer inner outerBelow innerBelow level member
    rcases List.mem_append.mp member with inOuter | inInner
    · exact outerBelow level inOuter
    · exact innerBelow level inInner

def stage (n : ℕ) : AdmissibleClass branchingRules :=
  AdmissibleClass.generatedBy {levels | ∃ level < n, levels = [level]}

theorem stage_le_below (n : ℕ) : stage n ≤ below n := by
  apply AdmissibleClass.generatedBy_le_iff.mpr
  rintro _ ⟨level, lt, rfl⟩ k member
  rw [List.mem_singleton] at member
  exact member ▸ lt

theorem probe_admissible {n level : ℕ} (lt : level < n) : (stage n).Admissible [level] :=
  AdmissibleClass.generator_mem ⟨level, lt, rfl⟩

/-- Under a non-empty list of probes, a term steps only when the innermost probe
meets a live leaf of its level directly under a single probe. -/
theorem step_plug_cons {level : ℕ} {rest : List ℕ} {term target : Tm}
    (step : Steps (plugProbes (level :: rest) term) target) :
    rest = [] ∧ term = .leaf level true := by
  match rest, step with
  | [], step =>
    cases step
    exact ⟨rfl, rfl⟩
  | _ :: _, step => cases step

/-- Terms with no step under any context of stage `n`. -/
def Quiet (n : ℕ) (term : Tm) : Prop :=
  term = .opened ∨ ∃ level, n ≤ level ∧ ∃ live, term = .leaf level live

theorem quiet_no_step {n : ℕ} {term : Tm} (quiet : Quiet n term) {levels : List ℕ}
    (admissible : (stage n).Admissible levels) {target : Tm}
    (step : Steps (plugProbes levels term) target) : False := by
  cases levels with
  | nil =>
    rcases quiet with rfl | ⟨_, _, _, rfl⟩ <;> cases step
  | cons level rest =>
    obtain ⟨_, rfl⟩ := step_plug_cons step
    rcases quiet with equal | ⟨k, le, _, equal⟩
    · exact Tm.noConfusion equal
    · obtain ⟨rfl, _⟩ := Tm.leaf.inj equal
      have lt := stage_le_below n _ admissible level (List.Mem.head rest)
      exact absurd le (Nat.not_le.mpr lt)

/-- The relation used at stage `n`. -/
def Related (n : ℕ) (left right : Tm) : Prop :=
  left = right ∨ (left = .many ∧ right = .manyPlus) ∨ (left = .manyPlus ∧ right = .many) ∨
    (Quiet n left ∧ Quiet n right)

/-- Matching one step of a related pair at stage `n`. -/
theorem related_forward {n : ℕ} {left right : Tm} (held : Related n left right)
    {levels : List ℕ} (admissible : (stage n).Admissible levels) {left' : Tm}
    (step : Steps (plugProbes levels left) left') :
    ∃ right', Steps (plugProbes levels right) right' ∧ Related n left' right' := by
  rcases held with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨quietLeft, _⟩
  · exact ⟨left', step, Or.inl rfl⟩
  · cases levels with
    | nil =>
      cases step with
      | branch level => exact ⟨.leaf level true, Steps.branchPlus level, Or.inl rfl⟩
    | cons level rest =>
      obtain ⟨_, impossible⟩ := step_plug_cons step
      exact Tm.noConfusion impossible
  · cases levels with
    | nil =>
      cases step with
      | branchPlus level => exact ⟨.leaf level true, Steps.branch level, Or.inl rfl⟩
      | extra =>
        exact ⟨.leaf n true, Steps.branch n,
          Or.inr (Or.inr (Or.inr ⟨Or.inl rfl, Or.inr ⟨n, le_rfl, true, rfl⟩⟩))⟩
    | cons level rest =>
      obtain ⟨_, impossible⟩ := step_plug_cons step
      exact Tm.noConfusion impossible
  · exact (quiet_no_step quietLeft admissible step).elim

theorem related_symm {n : ℕ} {left right : Tm} (held : Related n left right) :
    Related n right left := by
  rcases held with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨quietLeft, quietRight⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · exact Or.inr (Or.inr (Or.inr ⟨quietRight, quietLeft⟩))

/-- **At every finite stage, `many` and `manyPlus` are equivalent**: the extra
reduct `opened` is matched by a live leaf too deep for the stage's probes. -/
theorem stage_relEquiv (n : ℕ) : (stage n).RelEquiv silent .many .manyPlus := by
  refine ⟨Related n, ⟨?_, ?_, ?_⟩, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  · intro left right held label left' step
    exact related_forward held label.2 step
  · intro left right held label right' step
    obtain ⟨left', leftStep, related'⟩ := related_forward (related_symm held) label.2 step
    exact ⟨left', leftStep, related_symm related'⟩
  · intro _ _ _ atom
    exact atom.1.elim

/-- **At the limit, they are separated**: the extra reduct `opened` can only be
matched by a live leaf, which the probe of its level opens. -/
theorem not_iSup_relEquiv : ¬ (⨆ n, stage n).RelEquiv silent .many .manyPlus := by
  intro related
  obtain ⟨leaf, leafStep, leafRelated⟩ := AdmissibleContextCongruence.bisimilar_backward related
    (⟨[], (⨆ n, stage n).identity_mem⟩ : ((⨆ n, stage n).saturated silent).Label) Steps.extra
  change Steps .many leaf at leafStep
  cases leafStep with
  | branch level =>
    have admissible : (⨆ n, stage n).Admissible [level] :=
      (le_iSup stage (level + 1)) [level] (probe_admissible (Nat.lt_succ_self level))
    obtain ⟨_, openedStep, _⟩ := AdmissibleContextCongruence.bisimilar_forward leafRelated
      (⟨[level], admissible⟩ : ((⨆ n, stage n).saturated silent).Label) (Steps.fire level)
    change Steps (Tm.probe level .opened) _ at openedStep
    cases openedStep

/-- **Continuity fails without image-finiteness**: the limit observer separates a
pair that every finite stage identifies. -/
theorem not_continuous :
    (∀ n, (stage n).RelEquiv silent .many .manyPlus) ∧
      ¬ (⨆ n, stage n).RelEquiv silent .many .manyPlus :=
  ⟨stage_relEquiv, not_iSup_relEquiv⟩

end BranchingTower

end ObserverPresheafControls

end Mettapedia.GSLT.AdmissibleContextCongruence
