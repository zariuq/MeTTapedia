import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Eventually.Instances
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaConversion

/-!
# Consequences: the conversion budget of the round and of the converting step

The unifier's round and the computable converting step call the executable comparison through two wrappers:
the comparison of the annotations of two typed terms and of the terms (`Conversion.compareTypes`,
`Conversion.compare`), and the round's scan, which removes from a store every equation that comparison accepts
(`Conversion.scan`).

* **Every equation that holds is accepted from some budget on** (`frame_compare_eventually`), and no
  equation that does not hold is ever accepted.
* **The round's scan has no cliff on typed stores** (`scan_eventually`): from some budget on it returns the
  same store at every budget, and that store holds exactly the equations that do not hold. So in this part of
  the round the fixed fuel can be replaced by the search for the least budget at which the scan stops
  changing. For the vectors package this holds under strong normalization of its typed terms
  (`vectors_scan_eventually`).
* **The converting step's row checks** (`vecChecksAt`): for a firing whose made rows have types equal to their
  frame types along the settled answer, the check does not depend on the conversion budget from some budget
  on (`vecChecksAt_eventually`); for a firing without guards or queries that the families settle, neither
  does the computable admission (`vecAdmits_eventually`).

The other part of the round, defining the newest declaration, runs the executable checker; its eventual
success needs the checker's class (open here), and so does the definition checker.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing.Eventually

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ExecutableReduction ExecutableConversion
open ContextualDependentEta (frames)
open Interface.DependentFull (State Firing)

/-- **Finitely many eventual properties hold together eventually.** -/
theorem list_eventually {α : Type} (l : List α) (P : Nat → α → Prop)
    (each : ∀ a ∈ l, ∃ g, ∀ k, g ≤ k → P k a) : ∃ g, ∀ k, g ≤ k → ∀ a ∈ l, P k a := by
  induction l with
  | nil => exact ⟨0, fun _ _ _ member => by cases member⟩
  | cons a l ih =>
      obtain ⟨g₁, h₁⟩ := each a List.mem_cons_self
      obtain ⟨g₂, h₂⟩ := ih fun b member => each b (List.mem_cons_of_mem _ member)
      refine ⟨g₁ + g₂, fun k le b member => ?_⟩
      rcases List.mem_cons.mp member with rfl | inner
      · exact h₁ k (by omega)
      · exact h₂ k (by omega) b inner

/-! ## The frame comparison and the round's scan -/

section Frames

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable [DecidableEq Head] [DecidableRel S.R.headEq] [∀ head, Decidable (S.R.isUniverse head)]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (complete : AlgorithmicComplete S.R S.roles)
  {red : Reducer S.R} (stable : Stable S.R red) (eventually : WhnfEventually S red)

include facts roots heads algebra complete stable eventually in
/-- **Equal annotations are accepted from some budget on.** -/
theorem compareTypes_eventually {Γ : Context S.R} {first second : TypeOver Γ}
    (equal : TypeEq S.R Γ.raw first.code second.code) :
    ∃ fuel₀, ∀ fuel, fuel₀ ≤ fuel →
      (ContextualDependentEta.Conversion.compareTypes facts roots heads algebra red fuel first
        second).isSome = true := by
  obtain ⟨f₁, c₁, h₁⟩ := types_eventually facts roots heads algebra complete stable eventually Γ.formed equal
  refine ⟨f₁, fun fuel le => ?_⟩
  simp [ContextualDependentEta.Conversion.compareTypes, h₁ fuel le]

include facts roots heads algebra complete stable eventually in
/-- **Every equation that holds is accepted by the frame comparison from some budget on.** -/
theorem frame_compare_eventually {Γ : Context S.R} {first second : TotalTerm Γ}
    (equal : (frames S.levels).E first second) :
    ∃ fuel₀, ∀ fuel, fuel₀ ≤ fuel →
      (ContextualDependentEta.Conversion.compare facts roots heads algebra red fuel first second).isSome =
        true := by
  obtain ⟨eT, eTm⟩ := (ContextualDependentEta.equivalent_iff S.levels first second).mp equal
  obtain ⟨f₁, c₁, h₁⟩ := types_eventually facts roots heads algebra complete stable eventually Γ.formed eT
  obtain ⟨f₂, c₂, h₂⟩ := compare_eventually facts roots heads algebra complete stable eventually Γ.formed eTm
  refine ⟨f₁ + f₂, fun fuel le => ?_⟩
  simp [ContextualDependentEta.Conversion.compare, ContextualDependentEta.Conversion.compareTypes,
    h₁ fuel (by omega), h₂ fuel (by omega)]

include facts roots heads algebra complete stable eventually in
/-- **The round's scan has no cliff on typed stores**: from some budget on it returns the same store at
every budget, and that store holds exactly the equations that do not hold. -/
theorem scan_eventually {Γ : Context S.R} :
    ∀ problem : EquationStore (TotalTerm Γ), ∃ fuel₀, ∀ fuel, fuel₀ ≤ fuel →
      ContextualDependentEta.Conversion.scan facts roots heads algebra red fuel problem =
          ContextualDependentEta.Conversion.scan facts roots heads algebra red fuel₀ problem ∧
        ∀ equation ∈ ContextualDependentEta.Conversion.scan facts roots heads algebra red fuel problem,
          ¬ (frames S.levels).E equation.1 equation.2
  | [] => ⟨0, fun _ _ => ⟨rfl, fun _ member => by cases member⟩⟩
  | equation :: rest => by
      obtain ⟨f₀, hrest⟩ := scan_eventually rest
      by_cases holds : (frames S.levels).E equation.1 equation.2
      · obtain ⟨f₁, h₁⟩ := frame_compare_eventually facts roots heads algebra complete stable eventually holds
        refine ⟨f₀ + f₁, fun fuel le => ?_⟩
        obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp (h₁ fuel (by omega))
        obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp (h₁ (f₀ + f₁) (by omega))
        obtain ⟨same, none'⟩ := hrest fuel (by omega)
        obtain ⟨same', _⟩ := hrest (f₀ + f₁) (by omega)
        simp only [ContextualDependentEta.Conversion.scan, hc, hc']
        exact ⟨same.trans same'.symm, none'⟩
      · refine ⟨f₀, fun fuel le => ?_⟩
        have never : ∀ k,
            ContextualDependentEta.Conversion.compare facts roots heads algebra red k equation.1 equation.2 =
              none := fun k => by
          cases h : ContextualDependentEta.Conversion.compare facts roots heads algebra red k equation.1
              equation.2 with
          | none => rfl
          | some c => exact absurd c.down holds
        obtain ⟨same, none'⟩ := hrest fuel le
        simp only [ContextualDependentEta.Conversion.scan, never fuel, never f₀]
        refine ⟨by rw [same], fun e member => ?_⟩
        rcases List.mem_cons.mp member with rfl | inner
        · exact holds
        · exact none' e inner

end Frames

/-! ## The vectors package: the round's scan and the converting step -/

section Vectors

open ProgrammingOnTheStep.IndexedFamilies.Eliminator (level1)

/-- **The vectors round's scan has no cliff**, under strong normalization of the package's typed terms. -/
theorem vectors_scan_eventually (sn : TypedSN Vectors.vecS.R) {Γ : Context Vectors.vecS.R}
    (problem : EquationStore (TotalTerm Γ)) :
    ∃ fuel₀, ∀ fuel, fuel₀ ≤ fuel →
      ContextualDependentEta.Conversion.scan (S := Vectors.vecS) (TowerVectorsModel.facts level1)
          (TowerVectorsModel.roots level1) (TowerVectorsModel.heads level1) (TowerVectorsModel.algebra level1)
          (Vectors.vecReducer level1) fuel problem =
        ContextualDependentEta.Conversion.scan (S := Vectors.vecS) (TowerVectorsModel.facts level1)
          (TowerVectorsModel.roots level1) (TowerVectorsModel.heads level1) (TowerVectorsModel.algebra level1)
          (Vectors.vecReducer level1) fuel₀ problem ∧
      ∀ equation ∈ ContextualDependentEta.Conversion.scan (S := Vectors.vecS) (TowerVectorsModel.facts level1)
          (TowerVectorsModel.roots level1) (TowerVectorsModel.heads level1) (TowerVectorsModel.algebra level1)
          (Vectors.vecReducer level1) fuel problem,
        ¬ (frames Vectors.vecS.levels).E equation.1 equation.2 :=
  scan_eventually (TowerVectorsModel.facts level1) (TowerVectorsModel.roots level1)
    (TowerVectorsModel.heads level1) (TowerVectorsModel.algebra level1) (Vectors.vq level1).complete
    (normalize_stable (S := Vectors.vecS) (Vectors.vecRoot level1))
    (normalize_whnfEventually sn (Vectors.vecRoot level1) (vecRoot_complete level1)) problem

/-- **The converting step's row checks stop depending on the conversion budget**: for a firing whose made
rows have types equal to their frame types along the answer, under strong normalization of the package's
typed terms. -/
theorem vecChecksAt_eventually (sn : TypedSN Vectors.vecS.R) {s : State Vectors.vecS.R Nat}
    (f : Firing Vectors.vecS.levels s)
    (frameType : ∀ m ∈ f.makes, Σ' B : TypeOver f.helpers.frame, FrameTypedAt m.2 B)
    {M : Context Vectors.vecS.R} (σ : M ⟶ f.helpers.frame)
    (rows : ∀ m (member : m ∈ f.makes),
      TypeEq Vectors.vecS.R M.raw ((frameType m member).1.reindex σ).code (m.2.type.reindex σ).code) :
    ∃ fuel₀, ∀ fuel, fuel₀ ≤ fuel →
      Vectors.vecChecksAt fuel f frameType σ = Vectors.vecChecksAt fuel₀ f frameType σ := by
  obtain ⟨g, hg⟩ := list_eventually f.makes.attach
    (fun k m => (ContextualDependentEta.Conversion.compareTypes (S := Vectors.vecS)
      (TowerVectorsModel.facts level1) (TowerVectorsModel.roots level1) (TowerVectorsModel.heads level1)
      (TowerVectorsModel.algebra level1) (Vectors.vecReducer level1) k ((frameType m.1 m.2).1.reindex σ)
      (m.1.2.type.reindex σ)).isSome = true)
    (fun m _ => compareTypes_eventually (TowerVectorsModel.facts level1) (TowerVectorsModel.roots level1)
      (TowerVectorsModel.heads level1) (TowerVectorsModel.algebra level1) (Vectors.vq level1).complete
      (normalize_stable (S := Vectors.vecS) (Vectors.vecRoot level1))
      (normalize_whnfEventually sn (Vectors.vecRoot level1) (vecRoot_complete level1)) (rows m.1 m.2))
  refine ⟨g, fun fuel le => ?_⟩
  have allAt : ∀ k, g ≤ k → f.makes.attach.all (fun m => (ContextualDependentEta.Conversion.compareTypes
      (S := Vectors.vecS) (TowerVectorsModel.facts level1) (TowerVectorsModel.roots level1)
      (TowerVectorsModel.heads level1) (TowerVectorsModel.algebra level1) (Vectors.vecReducer level1) k
      ((frameType m.1 m.2).1.reindex σ) (m.1.2.type.reindex σ)).isSome) = true :=
    fun k hk => List.all_eq_true.mpr fun m member => hg k hk m member
  unfold Vectors.vecChecksAt
  rw [allAt fuel le, allAt g le_rfl]

/-- **The computable admission stops depending on the conversion budget**: for a firing without guards or
queries that the families settle, whose made rows have types equal to their frame types along the answer. -/
theorem vecAdmits_eventually (sn : TypedSN Vectors.vecS.R) {families : List (Family Vectors.vecS.levels)}
    {s : State Vectors.vecS.R Nat} (f : Firing Vectors.vecS.levels s)
    (frameType : ∀ m ∈ f.makes, Σ' B : TypeOver f.helpers.frame, FrameTypedAt m.2 B)
    {M : Context Vectors.vecS.R} {σ : M ⟶ f.helpers.frame}
    {initial : UnificationWithLevels.InitialSolution (frames Vectors.vecS.levels) f.information σ}
    (settled : firstDecisionAt Vectors.vecS.levels f.information families = .settled M σ initial)
    (rows : ∀ m (member : m ∈ f.makes),
      TypeEq Vectors.vecS.R M.raw ((frameType m member).1.reindex σ).code (m.2.type.reindex σ).code) :
    ∃ fuel₀, ∀ fuel, fuel₀ ≤ fuel →
      Vectors.vecAdmits? families fuel f frameType = Vectors.vecAdmits? families fuel₀ f frameType := by
  obtain ⟨g, hg⟩ := vecChecksAt_eventually sn f frameType σ rows
  refine ⟨g, fun fuel le => ?_⟩
  unfold Vectors.vecAdmits?
  by_cases empty : (f.guards.isEmpty && f.queries.isEmpty) = true
  · rw [if_pos empty, if_pos empty, settled]
    simp only [Vectors.vecAdmitsAt?, hg fuel le]
  · rw [if_neg empty, if_neg empty]

end Vectors

end NativeTypesOnTheStep.Computing.Eventually

section Audit
open NativeTypesOnTheStep.Computing.Eventually
#print axioms list_eventually
#print axioms compareTypes_eventually
#print axioms frame_compare_eventually
#print axioms scan_eventually
#print axioms vectors_scan_eventually
#print axioms vecChecksAt_eventually
#print axioms vecAdmits_eventually
end Audit

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
