import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.CommonRankJoin
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.GlbGroups

/-!
# The rules of the glb groups lower the common rank

The solver of glb groups has delete, domain raising, the true meet and the greatest-lower-bound rule, each in both
orientations. Every rule but delete sends one unknown `G` to `λ x. F x` and re-reads the other sides
(`support_contractSide`): `G` leaves the store (`occ_contractStore`), and the lowerings before it change codomains
only, so they keep the weight (`weight_lowerHom`, `Miller.weight_lowered`). So every round lowers the weight, or deletes
an equation (`glbGroupRound_commonRank`).
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

section Contract

variable {S : Setting Head L} [DecidableEq Head] [DecidableRel S.R.cumulative] (algebra : CumulativeAlgebra S.R)

/-- **The unknowns of a side after domain raising**: its own without `G`, or `F`. -/
theorem support_contractSide {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FitsView e) (all : AllFamilies Θ)
    (side : TotalTerm Θ) {j : Fin Θ.arity} (h : j ∈ (contractSide algebra v all side).2.code.support) :
    (j ∈ side.2.code.support ∧ j ≠ v.G) ∨ j = v.F := by
  rcases contractSide_cases algebra v all side with ⟨p', q', hr, same⟩ | same
  · rw [same] at h
    have h' : j ∈ (etaExp 1 (.var v.F) : Tm Head Θ.arity).support := h
    exact .inr (Finset.mem_singleton.mp (mem_support_etaExp 1 _ h'))
  · rw [same] at h
    change j ∈ (Presentation.subst (raiseSub v.F v.G) side.2.code).support at h
    obtain ⟨u, hu, hj⟩ := Miller.support_subst_sub side.2.code _ h
    by_cases hg : u = v.G
    · rw [hg, raiseSub_self] at hj
      exact .inr (Finset.mem_singleton.mp (mem_support_etaExp _ _ hj))
    · rw [raiseSub_ne _ _ hg] at hj
      have same : j = u := Finset.mem_singleton.mp hj
      subst same
      exact .inl ⟨hu, hg⟩

/-- **Domain raising lowers the weight**: `G` leaves the store, `F` was in it, and the telescope is the same. -/
theorem weight_contract_lt {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FitsView e) (all : AllFamilies Θ)
    (rest : EquationStore (TotalTerm Θ)) :
    Miller.weight (contractStore algebra v all rest) < Miller.weight (e :: rest) := by
  have occG : v.G ∈ Miller.occ (e :: rest) :=
    Miller.mem_occ.mpr ⟨e, List.mem_cons_self, .inl (by rw [v.side_left]; exact mem_support_etaExp_var _ _)⟩
  have occF : v.F ∈ Miller.occ (e :: rest) :=
    Miller.mem_occ.mpr ⟨e, List.mem_cons_self, .inr (by rw [v.side_right]; exact mem_support_etaExp_var _ _)⟩
  have sub : Miller.occ (contractStore algebra v all rest) ⊆ (Miller.occ (e :: rest)).erase v.G := by
    intro j hj
    obtain ⟨e', m', side'⟩ := Miller.mem_occ.mp hj
    obtain ⟨e₀, m₀, rfl⟩ := List.mem_map.mp m'
    have back : ∀ (s : TotalTerm Θ), (s = e₀.1 ∨ s = e₀.2) →
        j ∈ (contractSide algebra v all s).2.code.support → j ∈ (Miller.occ (e :: rest)).erase v.G := by
      intro s which hs
      rcases support_contractSide algebra v all s hs with ⟨inner, ne⟩ | isF
      · refine Finset.mem_erase.mpr ⟨ne, Miller.mem_occ.mpr ⟨e₀, List.mem_cons_of_mem _ m₀, ?_⟩⟩
        rcases which with rfl | rfl
        · exact .inl inner
        · exact .inr inner
      · rw [isF]
        exact Finset.mem_erase.mpr ⟨v.distinct, occF⟩
    rcases side' with hs | hs
    · exact back _ (.inl rfl) hs
    · exact back _ (.inr rfl) hs
  unfold Miller.weight
  calc ∑ i ∈ Miller.occ (contractStore algebra v all rest), (Miller.famArity (Ctx.lookup Θ.raw i) + 1)
      ≤ ∑ i ∈ (Miller.occ (e :: rest)).erase v.G, (Miller.famArity (Ctx.lookup Θ.raw i) + 1) :=
        Finset.sum_le_sum_of_subset sub
    _ < (Miller.famArity (Ctx.lookup Θ.raw v.G) + 1) +
          ∑ i ∈ (Miller.occ (e :: rest)).erase v.G, (Miller.famArity (Ctx.lookup Θ.raw i) + 1) := by
        omega
    _ = ∑ i ∈ Miller.occ (e :: rest), (Miller.famArity (Ctx.lookup Θ.raw i) + 1) :=
        Finset.add_sum_erase _ (fun i => Miller.famArity (Ctx.lookup Θ.raw i) + 1) occG

end Contract

section Weights

variable {S : Setting Head L}

/-- Swapping the sides of the first equation keeps the weight. -/
theorem weight_swap {Θ : Context S.R} (e : Equation (TotalTerm Θ)) (rest : EquationStore (TotalTerm Θ)) :
    Miller.weight (((e.2, e.1) : Equation (TotalTerm Θ)) :: rest) = Miller.weight (e :: rest) := by
  unfold Miller.weight
  congr 1
  show e.2.2.code.support ∪ e.1.2.code.support ∪ Miller.occ rest =
    e.1.2.code.support ∪ e.2.2.code.support ∪ Miller.occ rest
  rw [Finset.union_comm e.2.2.code.support]

/-- **The true meet's lowering keeps the weight.** -/
theorem weight_lowerHom {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FitFlex e) (meets : Meets v)
    (store : EquationStore (TotalTerm Θ)) :
    Miller.weight ((frames S.levels).applyStore (lowerHom Θ v meets) store) = Miller.weight store := by
  have codes : ∀ t : TotalTerm Θ, ((frames S.levels).act (lowerHom Θ v meets) t).2.code = t.2.code := fun t => by
    change Presentation.subst ids t.2.code = t.2.code
    exact subst_ids _
  have occSame : ∀ store : EquationStore (TotalTerm Θ),
      Miller.occ ((frames S.levels).applyStore (lowerHom Θ v meets) store) = Miller.occ store := by
    intro store
    induction store with
    | nil => rfl
    | cons e' rest ih =>
        show ((frames S.levels).act (lowerHom Θ v meets) e'.1).2.code.support ∪
            ((frames S.levels).act (lowerHom Θ v meets) e'.2).2.code.support ∪
              Miller.occ ((frames S.levels).applyStore (lowerHom Θ v meets) rest) =
            e'.1.2.code.support ∪ e'.2.2.code.support ∪ Miller.occ rest
        rw [codes, codes, ih]
        rfl
  unfold Miller.weight
  rw [occSame store]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : i = v.right
  · rw [h, lowered_self, v.declared_right, Miller.famArity_famCode, Miller.famArity_famCode]
  · rw [lowered_ne Θ v meets h]
    rfl

end Weights

/-! ## The round -/

section Round

variable {S : Setting Head L} [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)]
  [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (glb : Head → Head → Option Head) (spec : ∀ {a b g : Head}, glb a b = some g → IsGlb S.R g a b)

/-- **Every round of the solver of glb groups lowers the common rank.** -/
theorem glbGroupRound_commonRank {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}
    {update : Update S.levels problem}
    {smaller : ContextualDependentWorklist.Below (storeRank update.remaining) (storeRank problem)}
    (progressed : glbGroupRound facts roots heads algebra rigid complete headTypingUnique glb spec problem =
      .progress update smaller) :
    Below (commonRank update.remaining) (commonRank problem) := by
  cases problem with
  | nil => cases progressed
  | cons e rest =>
      simp only [glbGroupRound] at progressed
      split_ifs at progressed with hall
      split at progressed
      · rename_i d hd
        unfold stepGlbGroup at progressed
        split_ifs at progressed with h1 h2 h3 h4 h5
        · cases progressed
          exact commonRank_drop e rest
        · cases progressed
          exact Prod.Lex.left _ _ (weight_contract_lt algebra _ _ rest)
        · cases progressed
          refine Prod.Lex.left _ _ ?_
          rw [← weight_swap e rest]
          exact weight_contract_lt algebra _ _ rest
        · cases progressed
          refine Prod.Lex.left _ _ ?_
          have lt := weight_contract_lt algebra (meetFits (viewOfFit hd) h4 (fun h => h1 h.symm))
            (lowered_families (viewOfFit hd) h4 (allFamilies_of_B hall))
            ((frames S.levels).applyStore (lowerHom _ (viewOfFit hd) h4) rest)
          rw [← weight_lowerHom (viewOfFit hd) h4 (e :: rest)]
          exact lt
        · cases progressed
          refine Prod.Lex.left _ _ ?_
          have lt := weight_contract_lt algebra (meetFits (viewOfFit hd).swap h5 h1)
            (lowered_families (viewOfFit hd).swap h5 (allFamilies_of_B hall))
            ((frames S.levels).applyStore (lowerHom _ (viewOfFit hd).swap h5) rest)
          rw [← weight_swap e rest, ← weight_lowerHom (viewOfFit hd).swap h5 (((e.2, e.1) : Equation _) :: rest)]
          exact lt
        · unfold glbBranch at progressed
          split at progressed
          · rename_i g hg
            split_ifs at progressed with hl hr
            · cases progressed
              refine Prod.Lex.left _ _ ?_
              have glbm : GlbMeets (viewOfFit hd) g := ⟨spec hg, hl.1, hl.2.1, hl.2.2⟩
              have distinct : (viewOfFit hd).right ≠ (viewOfFit hd).left := fun h => h1 h.symm
              have lt := weight_contract_lt algebra (glbFits algebra (viewOfFit hd) glbm distinct)
                ((glbLowerRight (viewOfFit hd) glbm distinct).families
                  ((glbLowerLeft (viewOfFit hd) glbm).families (allFamilies_of_B hall)))
                ((frames S.levels).applyStore (glbLowerRight (viewOfFit hd) glbm distinct).hom
                  ((frames S.levels).applyStore (glbLowerLeft (viewOfFit hd) glbm).hom rest))
              exact lt.trans_eq ((Miller.weight_lowered (glbLowerRight (viewOfFit hd) glbm distinct) _).trans
                (Miller.weight_lowered (glbLowerLeft (viewOfFit hd) glbm) (e :: rest)))
            · cases progressed
              refine Prod.Lex.left _ _ ?_
              have glbm : GlbMeets (viewOfFit hd).swap g := ⟨(spec hg).symm, hr.1, hr.2.1, hr.2.2⟩
              have distinct : (viewOfFit hd).swap.right ≠ (viewOfFit hd).swap.left := h1
              have lt := weight_contract_lt algebra (glbFits algebra (viewOfFit hd).swap glbm distinct)
                ((glbLowerRight (viewOfFit hd).swap glbm distinct).families
                  ((glbLowerLeft (viewOfFit hd).swap glbm).families (allFamilies_of_B hall)))
                ((frames S.levels).applyStore (glbLowerRight (viewOfFit hd).swap glbm distinct).hom
                  ((frames S.levels).applyStore (glbLowerLeft (viewOfFit hd).swap glbm).hom rest))
              rw [← weight_swap e rest]
              exact lt.trans_eq ((Miller.weight_lowered (glbLowerRight (viewOfFit hd).swap glbm distinct) _).trans
                (Miller.weight_lowered (glbLowerLeft (viewOfFit hd).swap glbm)
                  (((e.2, e.1) : Equation (TotalTerm _)) :: rest)))
          · cases progressed
      · cases progressed

end Round

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
