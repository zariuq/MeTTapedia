import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.WideMiller
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.OneSolver

/-!
# Miller patterns mixed with glb-join families, in one rank

A glb join answers `X, Y := λ x̄. Y' x̄`, `Y'` declared again in `Y`'s slot at least upper bounds of both domains. A
Miller side of `X` elsewhere, `λ ȳ. X y_a`, instantiated, is a β-redex no reader reads. **Re-read** through the join's
answer for `X` (`joinAnswer`, the answer data of the Miller re-reading), it becomes `λ ȳ. Y' y_a`: a wide side of `Y'`,
whose domains lie above the binders'. The direction by domain order then solves the Miller side against it
(`Miller.wideSolveRound`).

* **Typing an opening at wider domains** (`opened_typedW`): an unknown of a family is applied to binders of smaller
  universes.
* **The join with Miller re-reading** (`joinMillerUpdate`): the glb join's answer, the other equations re-read side by
  side for the Miller sides of the left unknown; exact, by the join's forcing (`glbJoinK_forces`) and the re-reading's
  equality. It lowers the common rank (`occ_joinMiller`, `weight_joinMiller_lt`): the left unknown leaves the store,
  and every side that mentioned it now mentions the right one.
* **One solver, the common rank** (`mixWideSolver`): the equations of families with parameters first; an equation whose
  sides are the same code is deleted; a family equation is joined; otherwise a Miller equation takes the Miller round;
  otherwise a Miller side against a wide side takes the direction by domain order. Every round lowers the common rank.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

namespace Miller

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist

variable {Head L : Type} [UniverseLevel.LevelOrder L]

/-! ## Openings at wider domains -/

section Opening

variable {S : Setting Head L}

/-- **An unknown applied to binders of smaller universes is typed**: the opening at `qs` of a function of the family
at `ps`, when each universe of `qs` lies below the corresponding one of `ps`. -/
theorem opened_typedW : ∀ {qs ps : List Head}, List.Forall₂ S.R.cumulative qs ps →
    ∀ {n : Nat} {Γ : Ctx Head n} {d : Head} {s : Tm Head n},
      Typed S.R Γ s (famCode ps d) → Typed S.R (ctx Γ qs) (opened qs s) (.head d)
  | [], [], .nil, _, _, _, _, typed => typed
  | q :: _, p :: _, .cons le rest, _, Γ, _, s, typed => by
      apply opened_typedW rest
      have weak := typed.rename (CtxRen.wk Γ (.head q))
      rw [famCode_rename] at weak
      have arg : Typed S.R (.snoc Γ (.head q)) (.var 0) (.head p) :=
        Derivable.cumul (var_head_typed (S := S) Γ q) le
      have step := Derivable.appElim weak arg
      simpa only [famCode_cons, inst0, famCode_subst] using step

end Opening

/-! ## The glb join with the Miller sides re-read -/

section Join

variable {S : Setting Head L}

/-- **The join's answer for the left unknown, as answer data**: `X := λ x̄. Y' x̄`, typed at `X`'s family through the
wider domains of `Y'`. -/
def joinAnswer {Θ : Context S.R} (families : Families Θ) {e : Equation (TotalTerm Θ)} (v : FlexK e)
    {psJ : List Head} (joins : JoinsK S.R v.psl v.psr psJ) {m : Head} (hm : S.R.isUniverse m)
    (lowL : S.R.cumulative m v.cl) (lowR : S.R.cumulative m v.cr) :
    AnswerData (joinMKHom Θ families v joins hm lowL lowR) where
  X := v.left
  psX := v.psl
  cX := v.cl
  declared := v.declared_left
  universesX := v.universes_left
  universe_cX := v.universe_cl
  val := opened v.psl (.var v.right)
  typed := by
    have tY : Typed S.R (joinedMK Θ families v joins hm).raw (.var v.right) (famCode psJ m) := by
      have typed := Derivable.var (R := S.R) (Γ := (joinedMK Θ families v joins hm).raw) v.right
      rw [joinedMK_self] at typed
      exact typed
    exact Derivable.cumul (opened_typedW joins.left tY) lowL
  answer_self := by
    show joinKSub v.ps.length v.left v.right v.left = lams v.psl (opened v.psl (.var v.right))
    rw [joinKSub_left, lams_opened, lengths_left v]

variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]

/-- **The glb join, the other equations re-read for the Miller sides of the left unknown.** Exact when the join's
forcing holds. -/
def joinMillerUpdate {Θ : Context S.R} (families : Families Θ) {e : Equation (TotalTerm Θ)} (v : FlexK e)
    {psJ : List Head} (joins : JoinsK S.R v.psl v.psr psJ) {m : Head} (hm : S.R.isUniverse m)
    (lowL : S.R.cumulative m v.cl) (lowR : S.R.cumulative m v.cr) (forces : JoinForces v psJ m)
    (rest : EquationStore (TotalTerm Θ)) : Update S.levels (e :: rest) :=
  replaceUpdate (joinMKHom Θ families v joins hm lowL lowR)
    (rereadStoreW (joinAnswer families v joins hm lowL lowR) rest)
    (fun g => (rereadStoreW_models _ rest g).trans
      ((Frames.models_applyStore (X := frames S.levels) _ g rest).trans
        (Iff.trans ⟨fun h => ⟨joinMK_head_solved families v joins hm lowL lowR g, h⟩, fun h => h.2⟩
          ((ContextualDependentInPlace.models_cons _ e rest).symm.trans
            (Frames.models_applyStore (X := frames S.levels) _ g (e :: rest)).symm))))
    (fun f solved => joinMK_factors families v joins hm lowL lowR forces f (solved e List.mem_cons_self))

theorem joinMillerUpdate_remaining {Θ : Context S.R} (families : Families Θ) {e : Equation (TotalTerm Θ)}
    (v : FlexK e) {psJ : List Head} (joins : JoinsK S.R v.psl v.psr psJ) {m : Head} (hm : S.R.isUniverse m)
    (lowL : S.R.cumulative m v.cl) (lowR : S.R.cumulative m v.cr) (forces : JoinForces v psJ m)
    (rest : EquationStore (TotalTerm Θ)) :
    (joinMillerUpdate families v joins hm lowL lowR forces rest).remaining =
      rereadStoreW (joinAnswer families v joins hm lowL lowR) rest := rfl

omit [∀ head, Decidable (S.R.isUniverse head)] in
/-- A side re-read on its own is instantiated, or replaced by the answer's value read at its locals. -/
theorem rereadSideW_code {Θ Θ' : Context S.R} {σ : Θ' ⟶ Θ} (A : AnswerData σ) (Y : TotalTerm Θ) {qs : List Head}
    {d : Head} (annotation : Y.1.code = famCode qs d) (universes : AllUniverses S.R qs) (hd : S.R.isUniverse d) :
    (rereadSideW A Y annotation universes hd).2.code = Presentation.subst σ.substitution Y.2.code ∨
      ∃ img : Fin A.psX.length → Fin qs.length,
        (rereadSideW A Y annotation universes hd).2.code = lams qs (Presentation.rename (sideRen qs A.psX img) A.val) := by
  unfold rereadSideW
  split
  · exact rereadSide_code A Y annotation universes hd _
  · exact .inl rfl

/-- **Each side of an equation re-read side by side** is instantiated, or replaced by the answer's value read at its
locals. -/
theorem rereadEqW_codes {Θ Θ' : Context S.R} {σ : Θ' ⟶ Θ} (A : AnswerData σ) (e : Equation (TotalTerm Θ)) :
    ((rereadEqW A e).1.2.code = Presentation.subst σ.substitution e.1.2.code ∨
        ∃ (qs : List Head) (img : Fin A.psX.length → Fin qs.length),
          (rereadEqW A e).1.2.code = lams qs (Presentation.rename (sideRen qs A.psX img) A.val)) ∧
      ((rereadEqW A e).2.2.code = Presentation.subst σ.substitution e.2.2.code ∨
        ∃ (qs : List Head) (img : Fin A.psX.length → Fin qs.length),
          (rereadEqW A e).2.2.code = lams qs (Presentation.rename (sideRen qs A.psX img) A.val)) := by
  unfold rereadEqW
  cases hr : readFam e.1.1.code with
  | none => exact ⟨.inl rfl, .inl rfl⟩
  | some r =>
      dsimp only
      by_cases h : e.1.1.code = famCode r.1 r.2 ∧ e.2.1.code = famCode r.1 r.2 ∧ AllUniverses S.R r.1 ∧
          S.R.isUniverse r.2
      · rw [dif_pos h]
        refine ⟨?_, ?_⟩
        · rcases rereadSideW_code A e.1 h.1 h.2.2.1 h.2.2.2 with same | ⟨img, same⟩
          · exact .inl same
          · exact .inr ⟨_, img, same⟩
        · rcases rereadSideW_code A e.2 h.2.1 h.2.2.1 h.2.2.2 with same | ⟨img, same⟩
          · exact .inl same
          · exact .inr ⟨_, img, same⟩
      · rw [dif_neg h]
        exact ⟨.inl rfl, .inl rfl⟩

/-- **The left unknown leaves the store** after the join with the Miller sides re-read. -/
theorem occ_joinMiller {Θ : Context S.R} (families : Families Θ) {e : Equation (TotalTerm Θ)} (v : FlexK e)
    {psJ : List Head} (joins : JoinsK S.R v.psl v.psr psJ) {m : Head} (hm : S.R.isUniverse m)
    (lowL : S.R.cumulative m v.cl) (lowR : S.R.cumulative m v.cr) (rest : EquationStore (TotalTerm Θ))
    (distinct : v.left ≠ v.right) :
    occ (rereadStoreW (joinAnswer families v joins hm lowL lowR) rest) ⊆ (occ (e :: rest)).erase v.left := by
  have rightIn : v.right ∈ occ (e :: rest) :=
    mem_occ.mpr ⟨e, List.mem_cons_self, .inr (by rw [v.side_right]; exact mem_support_etaExp_var _ _)⟩
  have rightOK : v.right ∈ (occ (e :: rest)).erase v.left :=
    Finset.mem_erase.mpr ⟨fun same => distinct same.symm, rightIn⟩
  intro j hj
  obtain ⟨e', m', side'⟩ := mem_occ.mp hj
  obtain ⟨e₀, m₀, rfl⟩ := List.mem_map.mp m'
  have viaSubst : ∀ (code : Tm Head Θ.arity), code.support ⊆ occ (e :: rest) →
      j ∈ (Presentation.subst (joinKSub v.ps.length v.left v.right) code).support →
        j ∈ (occ (e :: rest)).erase v.left := by
    intro code within h
    obtain ⟨u, hu, hju⟩ := support_subst_sub code _ h
    by_cases hl : u = v.left
    · rw [hl, joinKSub_left] at hju
      rw [Finset.mem_singleton.mp (mem_support_etaExp _ _ hju)]
      exact rightOK
    · by_cases hr : u = v.right
      · rw [hr, joinKSub_right] at hju
        rw [Finset.mem_singleton.mp (mem_support_etaExp _ _ hju)]
        exact rightOK
      · rw [joinKSub_ne _ _ _ hl hr] at hju
        have same : j = u := Finset.mem_singleton.mp hju
        subst same
        exact Finset.mem_erase.mpr ⟨hl, within hu⟩
  have viaReread : ∀ (qs : List Head) (img : Fin v.psl.length → Fin qs.length),
      j ∈ (lams qs (Presentation.rename (sideRen qs v.psl img) (opened v.psl (.var v.right))) :
        Tm Head Θ.arity).support → j ∈ (occ (e :: rest)).erase v.left := by
    intro qs img h
    have h' := support_reread qs v.psl img (opened v.psl (.var v.right)) h
    rw [lams_opened] at h'
    rw [Finset.mem_singleton.mp (mem_support_etaExp _ _ h')]
    exact rightOK
  have left₀ : e₀.1.2.code.support ⊆ occ (e :: rest) := fun w hw =>
    mem_occ.mpr ⟨e₀, List.mem_cons_of_mem _ m₀, .inl hw⟩
  have right₀ : e₀.2.2.code.support ⊆ occ (e :: rest) := fun w hw =>
    mem_occ.mpr ⟨e₀, List.mem_cons_of_mem _ m₀, .inr hw⟩
  obtain ⟨c1, c2⟩ := rereadEqW_codes (joinAnswer families v joins hm lowL lowR) e₀
  rcases side' with hs | hs
  · rcases c1 with same | ⟨qs, img, same⟩
    · rw [same] at hs
      exact viaSubst _ left₀ hs
    · rw [same] at hs
      exact viaReread qs img hs
  · rcases c2 with same | ⟨qs, img, same⟩
    · rw [same] at hs
      exact viaSubst _ right₀ hs
    · rw [same] at hs
      exact viaReread qs img hs

/-- **The join with the Miller sides re-read lowers the weight.** -/
theorem weight_joinMiller_lt {Θ : Context S.R} (families : Families Θ) {e : Equation (TotalTerm Θ)} (v : FlexK e)
    {psJ : List Head} (joins : JoinsK S.R v.psl v.psr psJ) {m : Head} (hm : S.R.isUniverse m)
    (lowL : S.R.cumulative m v.cl) (lowR : S.R.cumulative m v.cr) (rest : EquationStore (TotalTerm Θ))
    (distinct : v.left ≠ v.right) :
    weight (rereadStoreW (joinAnswer families v joins hm lowL lowR) rest) < weight (e :: rest) := by
  have occL : v.left ∈ occ (e :: rest) :=
    mem_occ.mpr ⟨e, List.mem_cons_self, .inl (by rw [v.side_left]; exact mem_support_etaExp_var _ _)⟩
  have arities : ∀ i ∈ (occ (e :: rest)).erase v.left,
      famArity (Ctx.lookup (joinedMK Θ families v joins hm).raw i) = famArity (Ctx.lookup Θ.raw i) := by
    intro i _
    by_cases hi : i = v.right
    · rw [hi, joinedMK_self, v.declared_right, famArity_famCode, famArity_famCode]
      exact (forall₂_length joins.right).symm
    · rw [joinedMK_ne Θ families v joins hm hi]
  unfold weight
  calc ∑ i ∈ occ (rereadStoreW (joinAnswer families v joins hm lowL lowR) rest),
        (famArity (Ctx.lookup (joinedMK Θ families v joins hm).raw i) + 1)
      ≤ ∑ i ∈ (occ (e :: rest)).erase v.left, (famArity (Ctx.lookup (joinedMK Θ families v joins hm).raw i) + 1) :=
        Finset.sum_le_sum_of_subset (occ_joinMiller families v joins hm lowL lowR rest distinct)
    _ = ∑ i ∈ (occ (e :: rest)).erase v.left, (famArity (Ctx.lookup Θ.raw i) + 1) :=
        Finset.sum_congr rfl fun i member => by rw [arities i member]
    _ < (famArity (Ctx.lookup Θ.raw v.left) + 1) +
          ∑ i ∈ (occ (e :: rest)).erase v.left, (famArity (Ctx.lookup Θ.raw i) + 1) := by
        omega
    _ = ∑ i ∈ occ (e :: rest), (famArity (Ctx.lookup Θ.raw i) + 1) :=
        Finset.add_sum_erase _ (fun i => famArity (Ctx.lookup Θ.raw i) + 1) occL

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)
  (headsTyped : ∀ {h u u' : Head}, S.R.headTyping h u → S.R.headTyping h u' → u = u')
  (join : Head → Head → Option Head)
  (joinSound : ∀ {u v w : Head}, join u v = some w → S.R.isUniverse w ∧ IsLub S.R w u v)
  (glb : Head → Head → Option Head) (spec : ∀ {a b g : Head}, glb a b = some g → IsGlb S.R g a b)

/-- **The join step on a family equation**: when the two unknowns differ, every position crosses, and the greatest
lower bound and the least upper bounds exist. It lowers the common rank (`weight_joinMiller_lt`). -/
def joinMillerStep {Θ : Context S.R} (families : Families Θ) {e : Equation (TotalTerm Θ)} (v : FlexK e)
    (rest : EquationStore (TotalTerm Θ)) : Round S.levels commonRank (e :: rest) :=
  if hsame : v.left = v.right then .stuck
  else if hx : List.Forall₂ (CrossAt S.R v.cl v.cr) v.psl v.psr then
    match hg : glb v.cl v.cr with
    | some _ =>
        match hj : joinsOf join v.psl v.psr with
        | some _ =>
            .progress (joinMillerUpdate families v (joinsOf_sound join joinSound hj) (spec hg).1 (spec hg).2.1
                (spec hg).2.2.1
                (glbJoinK_forces facts roots heads algebra rigid complete headsTyped v (spec hg)
                  (joinsOf_sound join joinSound hj) hx) rest)
              (Prod.Lex.left _ _ (weight_joinMiller_lt families v (joinsOf_sound join joinSound hj) (spec hg).1
                (spec hg).2.1 (spec hg).2.2.1 rest hsame))
        | none => .stuck
    | none => .stuck
  else .stuck

end Join

/-! ## One solver, the common rank -/

section Solver

variable {S : Setting Head L}
variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)
  (inh : Inhabitants S.R)
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (join : Head → Head → Option Head)
  (joinSound : ∀ {u v w : Head}, join u v = some w → S.R.isUniverse w ∧ IsLub S.R w u v)
  (glb : Head → Head → Option Head) (spec : ∀ {a b g : Head}, glb a b = some g → IsGlb S.R g a b)

/-- **The round on a store with its family equations first**: an equation whose sides are the same code is deleted; a
family equation is joined; a Miller equation takes the Miller round; a Miller side against a wide side takes the
direction by domain order. -/
def mixWideRound0 : {Γ : Context S.R} → (problem : EquationStore (TotalTerm Γ)) → Round S.levels commonRank problem
  | _, [] => .stuck
  | Γ, e :: rest =>
      if same : e.1.1.code = e.2.1.code ∧ e.1.2.code = e.2.2.code then
        .progress (deleteSame same.1 same.2 rest) (commonRank_drop e rest)
      else if hfam : Families Γ then
        match hd : readFlexK (S := S) e with
        | some _ =>
            joinMillerStep facts roots heads algebra rigid complete headTypingUnique join joinSound glb spec hfam
              (viewOfK hd) rest
        | none =>
            match readEq (S := S) e with
            | some _ =>
                retarget (millerGlbRound facts roots heads algebra rigid complete normalizes inh headTypingUnique glb
                    spec (e :: rest))
                  (fun _ _ progressed => millerGlbRound_commonRank facts roots heads algebra rigid complete normalizes
                    inh headTypingUnique glb spec progressed)
            | none => wideRound facts roots heads algebra rigid complete inh (e :: rest)
      else .stuck

/-- **The round of the mixed wide solver**: the equations of families with parameters first. -/
def mixWideRound {Γ : Context S.R} (problem : EquationStore (TotalTerm Γ)) : Round S.levels commonRank problem :=
  transport (equivalent_perm (joinFirst_perm problem).symm) (commonRank_perm (joinFirst_perm problem))
    (mixWideRound0 facts roots heads algebra rigid complete normalizes inh headTypingUnique join joinSound glb spec
      (joinFirst problem))

/-- **One solver of the tree's driver for Miller patterns mixed with glb-join families**, one rank: the common rank. -/
def mixWideSolver : ContextualDependentWorklist.Solver S.levels where
  rank := commonRank
  round := mixWideRound facts roots heads algebra rigid complete normalizes inh headTypingUnique join joinSound glb spec

end Solver

end Miller

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
