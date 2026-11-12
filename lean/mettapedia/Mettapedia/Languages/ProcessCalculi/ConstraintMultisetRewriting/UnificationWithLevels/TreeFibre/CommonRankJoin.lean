import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.CommonRank
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.GlbJoinSolver
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.GlbJoinInitial

/-!
# The glb join and the flex–rigid rules with codomains lower the common rank

* **The glb join** (`glbJoinRoundK_commonRank`): a deletion removes an equation; the join step sends the left unknown to
  the η-expansion of the right one, declared again at the joined domains (as many) and a greatest lower bound, and
  re-reads every other side (`support_joinSide`): the left unknown leaves the store (`occ_joinStore`) and the arities of
  the others stay (`weight_joinStore_lt`).
* **The flex–rigid rules with codomains** (`flexCodRound_commonRank`): on their fragment, a store of the fragment of arrow
  codes, the common rank is the rank of the arrow solver, which deletion and narrowing-and-solving lower.

So every rule of the Miller solver, of the solver of arrow codes, of the flex–rigid solver with codomains and of the
glb-join solver lowers one rank, the weight then the size.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist

variable {Head L : Type} [UniverseLevel.LevelOrder L]

/-! ## The glb join -/

section Join

/-- An η-expansion mentions the unknowns of what it expands. -/
theorem mem_support_etaExp_of : ∀ (k : Nat) {n : Nat} (t : Tm Head n) {j : Fin n},
    j ∈ t.support → j ∈ (etaExp k t).support
  | 0, _, _, _, h => h
  | k + 1, _, t, j, h => by
      change j ∈ (Tm.lam (etaExp k (.app (Presentation.rename wk t) (.var 0)))).support
      simp only [Tm.support, mem_outerSupport]
      apply mem_support_etaExp_of k
      simp only [Tm.support, Finset.mem_union]
      left
      rw [ContextualDependentSupport.support_rename, Finset.mem_image]
      exact ⟨j, h, rfl⟩

theorem mem_support_etaExp_var {n : Nat} (k : Nat) (x : Fin n) : x ∈ (etaExp k (.var x) : Tm Head n).support :=
  mem_support_etaExp_of k _ (by simp only [Tm.support, Finset.mem_singleton])

variable {S : Setting Head L} [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)]
  [DecidableRel S.R.cumulative]

/-- **The unknowns of a side after the glb join**: its own without the left unknown, or the right unknown. -/
theorem support_joinSide {Θ : Context S.R} (families : Miller.Families Θ) {e : Equation (TotalTerm Θ)} (v : FlexK e)
    {psJ : List Head} (joins : JoinsK S.R v.psl v.psr psJ) {m : Head} (hm : S.R.isUniverse m)
    (lowL : S.R.cumulative m v.cl) (lowR : S.R.cumulative m v.cr) (side : TotalTerm Θ) {j : Fin Θ.arity}
    (h : j ∈ (joinSide families v joins hm lowL lowR side).2.code.support) :
    (j ∈ side.2.code.support ∧ j ≠ v.left) ∨ j = v.right := by
  rcases joinSide_cases families v joins hm lowL lowR side with ⟨ps', q', hr, same⟩ | same
  · rw [same] at h
    have h' : j ∈ (etaExp ps'.length (.var v.right) : Tm Head Θ.arity).support := h
    exact .inr (Finset.mem_singleton.mp (mem_support_etaExp ps'.length _ h'))
  · rw [same] at h
    change j ∈ (Presentation.subst (joinKSub v.ps.length v.left v.right) side.2.code).support at h
    obtain ⟨u, hu, hj⟩ := Miller.support_subst_sub side.2.code _ h
    by_cases hl : u = v.left
    · rw [hl, joinKSub_left] at hj
      exact .inr (Finset.mem_singleton.mp (mem_support_etaExp _ _ hj))
    · by_cases hr : u = v.right
      · rw [hr, joinKSub_right] at hj
        exact .inr (Finset.mem_singleton.mp (mem_support_etaExp _ _ hj))
      · rw [joinKSub_ne _ _ _ hl hr] at hj
        have same : j = u := Finset.mem_singleton.mp hj
        subst same
        exact .inl ⟨hu, hl⟩

/-- **The left unknown leaves the store** after the glb join. -/
theorem occ_joinStore {Θ : Context S.R} (families : Miller.Families Θ) {e : Equation (TotalTerm Θ)} (v : FlexK e)
    {psJ : List Head} (joins : JoinsK S.R v.psl v.psr psJ) {m : Head} (hm : S.R.isUniverse m)
    (lowL : S.R.cumulative m v.cl) (lowR : S.R.cumulative m v.cr) (rest : EquationStore (TotalTerm Θ))
    (distinct : v.left ≠ v.right) :
    Miller.occ (joinStore families v joins hm lowL lowR rest) ⊆ (Miller.occ (e :: rest)).erase v.left := by
  have rightIn : v.right ∈ Miller.occ (e :: rest) :=
    Miller.mem_occ.mpr ⟨e, List.mem_cons_self, .inr (by rw [v.side_right]; exact mem_support_etaExp_var _ _)⟩
  intro j hj
  obtain ⟨e', m', side'⟩ := Miller.mem_occ.mp hj
  obtain ⟨e₀, m₀, rfl⟩ := List.mem_map.mp m'
  have back : ∀ (s : TotalTerm Θ), (s = e₀.1 ∨ s = e₀.2) →
      j ∈ (joinSide families v joins hm lowL lowR s).2.code.support → j ∈ (Miller.occ (e :: rest)).erase v.left := by
    intro s which hs
    rcases support_joinSide families v joins hm lowL lowR s hs with ⟨inner, ne⟩ | isRight
    · refine Finset.mem_erase.mpr ⟨ne, Miller.mem_occ.mpr ⟨e₀, List.mem_cons_of_mem _ m₀, ?_⟩⟩
      rcases which with rfl | rfl
      · exact .inl inner
      · exact .inr inner
    · rw [isRight]
      exact Finset.mem_erase.mpr ⟨fun same => distinct same.symm, rightIn⟩
  rcases side' with hs | hs
  · exact back _ (.inl rfl) hs
  · exact back _ (.inr rfl) hs

/-- **The glb join lowers the weight.** -/
theorem weight_joinStore_lt {Θ : Context S.R} (families : Miller.Families Θ) {e : Equation (TotalTerm Θ)}
    (v : FlexK e) {psJ : List Head} (joins : JoinsK S.R v.psl v.psr psJ) {m : Head} (hm : S.R.isUniverse m)
    (lowL : S.R.cumulative m v.cl) (lowR : S.R.cumulative m v.cr) (rest : EquationStore (TotalTerm Θ))
    (distinct : v.left ≠ v.right) :
    Miller.weight (joinStore families v joins hm lowL lowR rest) < Miller.weight (e :: rest) := by
  have occL : v.left ∈ Miller.occ (e :: rest) :=
    Miller.mem_occ.mpr ⟨e, List.mem_cons_self, .inl (by rw [v.side_left]; exact mem_support_etaExp_var _ _)⟩
  have arities : ∀ i ∈ (Miller.occ (e :: rest)).erase v.left,
      Miller.famArity (Ctx.lookup (joinedMK Θ families v joins hm).raw i) = Miller.famArity (Ctx.lookup Θ.raw i) := by
    intro i _
    by_cases hi : i = v.right
    · rw [hi, joinedMK_self, v.declared_right, Miller.famArity_famCode, Miller.famArity_famCode]
      exact (forall₂_length joins.right).symm
    · rw [joinedMK_ne Θ families v joins hm hi]
  unfold Miller.weight
  calc ∑ i ∈ Miller.occ (joinStore families v joins hm lowL lowR rest),
        (Miller.famArity (Ctx.lookup (joinedMK Θ families v joins hm).raw i) + 1)
      ≤ ∑ i ∈ (Miller.occ (e :: rest)).erase v.left,
          (Miller.famArity (Ctx.lookup (joinedMK Θ families v joins hm).raw i) + 1) :=
        Finset.sum_le_sum_of_subset (occ_joinStore families v joins hm lowL lowR rest distinct)
    _ = ∑ i ∈ (Miller.occ (e :: rest)).erase v.left, (Miller.famArity (Ctx.lookup Θ.raw i) + 1) :=
        Finset.sum_congr rfl fun i member => by rw [arities i member]
    _ < (Miller.famArity (Ctx.lookup Θ.raw v.left) + 1) +
          ∑ i ∈ (Miller.occ (e :: rest)).erase v.left, (Miller.famArity (Ctx.lookup Θ.raw i) + 1) := by
        omega
    _ = ∑ i ∈ Miller.occ (e :: rest), (Miller.famArity (Ctx.lookup Θ.raw i) + 1) :=
        Finset.add_sum_erase _ (fun i => Miller.famArity (Ctx.lookup Θ.raw i) + 1) occL

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)
  (headsTyped : ∀ {h u u' : Head}, S.R.headTyping h u → S.R.headTyping h u' → u = u')
  (join : Head → Head → Option Head)
  (joinSound : ∀ {u v w : Head}, join u v = some w → S.R.isUniverse w ∧ IsLub S.R w u v)
  (meet : Head → Head → Option Head)
  (meetSound : ∀ {u v g : Head}, meet u v = some g → IsGlb S.R g u v)

/-- **Every round of the glb-join solver lowers the common rank.** -/
theorem glbJoinRoundK_commonRank {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}
    {update : Update S.levels problem}
    {smaller : ContextualDependentWorklist.Below (storeRank update.remaining) (storeRank problem)}
    (progressed : glbJoinRoundK facts roots heads algebra rigid complete headsTyped join joinSound meet meetSound
      problem = .progress update smaller) :
    Below (commonRank update.remaining) (commonRank problem) := by
  cases problem with
  | nil => cases progressed
  | cons e rest =>
      simp only [glbJoinRoundK] at progressed
      split_ifs at progressed with hfam
      split at progressed
      · rename_i d hd
        unfold stepGlbJoinK at progressed
        split_ifs at progressed with h1 h2
        · cases progressed
          exact commonRank_drop e rest
        · split at progressed
          · rename_i gl hg
            split at progressed
            · rename_i psJ hj
              cases progressed
              exact Prod.Lex.left _ _ (weight_joinStore_lt hfam (viewOfK hd) (joinsOf_sound join joinSound hj)
                (meetSound hg).1 (meetSound hg).2.1 (meetSound hg).2.2.1 rest h1)
            · cases progressed
          · cases progressed
      · cases progressed

end Join

/-! ## The flex–rigid rules with codomains -/

section FlexCod

variable {S : Setting Head L} [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)]
  [DecidableRel S.R.cumulative]
variable (choices : ExecutableChecking.HeadChoices S.R) (glb : Head → Head → Option Head)
  (spec : ∀ {a b g : Head}, glb a b = some g → IsGlb S.R g a b)
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (declared : DeclaredTypesFormed S.R)

/-- **Every round of the flex–rigid solver with codomains lowers the common rank** on its fragment. -/
theorem flexCodRound_commonRank {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}
    {update : Update S.levels problem}
    {smaller : ContextualDependentWorklist.Below (storeRank update.remaining) (storeRank problem)}
    (inside : InFlexCod choices problem)
    (progressed : flexCodRound choices glb spec facts roots heads algebra rigid complete headTypingUnique declared
      problem = .progress update smaller) :
    Below (commonRank update.remaining) (commonRank problem) := by
  have after := inArrowsCod_of_flexCod (flexCodRound_stable choices glb spec facts roots heads algebra rigid complete
    headTypingUnique declared inside progressed)
  have before := inArrowsCod_of_flexCod inside
  rw [commonRank_eq_codRank before.occurring, commonRank_eq_codRank after.occurring]
  cases problem with
  | nil => cases progressed
  | cons e rest =>
      simp only [flexCodRound] at progressed
      split at progressed
      · unfold stepFlexCod at progressed
        split at progressed
        · cases progressed
          exact codRank_drop e rest
        · split at progressed
          · cases progressed
          · split at progressed
            · cases progressed
            · split at progressed
              · cases progressed
                exact codRank_solved glb spec algebra _ _ (inArrowsCod_drop before).codes
              · cases progressed
      · cases progressed

end FlexCod

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
