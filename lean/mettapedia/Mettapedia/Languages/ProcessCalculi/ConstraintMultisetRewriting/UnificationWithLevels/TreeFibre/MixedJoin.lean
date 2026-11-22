import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MixedSolver
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.CommonRankJoin

/-!
# Stores mixing glb-join families and arrow codes, decided by one solver

**A glb-join step keeps an equation between arrow codes one** (`arrowEq_joinSide`). The step sends the left unknown and
the right one to the η-expansion of the right one at as many parameters as their families have. An unknown met by an
equation between arrow codes is declared at a universe, a family of no parameters, so there the step is the renaming of
the left unknown to the right one, declared again at a universe; elsewhere it does nothing (`arrowCod_subst_vars`).

**A mixed join store** (`MixedJoinStore`): over a telescope of universe families, a store that is, up to order, a store
of the glb-join fragment followed by equations between arrow codes.

**The solver** (`mixedJoinSolver`, rank `commonRank`): the arrow round when every equation is between arrow codes;
otherwise the families with parameters first (`joinFirst`) and the glb-join round. Kept, never stuck, **decided**
(`mixedJoin_decided`).
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

/-! ## Substitutions of variables for variables keep arrow codes -/

section Vars

/-- **A substitution sending the unknowns of an arrow code to unknowns keeps it an arrow code.** -/
theorem arrowCod_subst_vars {n : Nat} {t : Tm Head n} (code : ArrowCod t) :
    ∀ {m : Nat} (σ : Sub Head n m), (∀ i ∈ t.support, ∃ j, σ i = .var j) →
      ArrowCod (Presentation.subst σ t) := by
  induction code with
  | var Y =>
      intro m σ vars
      obtain ⟨j, hj⟩ := vars Y (by simp [Tm.support])
      change ArrowCod (σ Y)
      rw [hj]
      exact .var j
  | head h => intro m σ _; exact .head h
  | @pi A B _ _ ihA ihB =>
      intro m σ vars
      change ArrowCod (.pi (Presentation.subst σ A) (Presentation.subst (liftSub σ) (Presentation.rename wk B)))
      rw [subst_liftSub_wk]
      exact .pi (ihA σ fun i h => vars i (mem_support_pi_wk.mpr (.inl h)))
        (ihB σ fun i h => vars i (mem_support_pi_wk.mpr (.inr h)))

/-- **Such a substitution keeps the heads.** -/
theorem codHeads_subst_vars {n : Nat} {t : Tm Head n} (code : ArrowCod t) :
    ∀ {m : Nat} (σ : Sub Head n m), (∀ i ∈ t.support, ∃ j, σ i = .var j) →
      codHeads (Presentation.subst σ t) = codHeads t := by
  induction code with
  | var Y =>
      intro m σ vars
      obtain ⟨j, hj⟩ := vars Y (by simp [Tm.support])
      change codHeads (σ Y) = codHeads (Tm.var Y)
      rw [hj]
      rfl
  | head h => intro m σ _; rfl
  | @pi A B _ _ ihA ihB =>
      intro m σ vars
      change codHeads (.pi (Presentation.subst σ A) (Presentation.subst (liftSub σ) (Presentation.rename wk B))) =
        codHeads (Tm.pi A (Presentation.rename wk B))
      rw [subst_liftSub_wk]
      simp only [codHeads, codHeads_rename]
      rw [ihA σ fun i h => vars i (mem_support_pi_wk.mpr (.inl h)),
        ihB σ fun i h => vars i (mem_support_pi_wk.mpr (.inr h))]

end Vars

/-! ## A glb-join step keeps an equation between arrow codes one -/

section JoinArrows

variable {S : Setting Head L} [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)]
  [DecidableRel S.R.cumulative]

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative] in
/-- **The join substitution, on the unknowns of an equation between arrow codes, sends unknowns to unknowns declared at
universes.** -/
theorem joinKSub_on_arrows {Θ : Context S.R} (families : Miller.Families Θ) {e : Equation (TotalTerm Θ)}
    (v : FlexK e) {psJ : List Head} (joins : JoinsK S.R v.psl v.psr psJ) {m : Head} (hm : S.R.isUniverse m)
    {t : Tm Head Θ.arity} (occ : AtUniverses (S := S) Θ.raw t) :
    ∀ i ∈ t.support, ∃ j, joinKSub (Head := Head) v.ps.length v.left v.right i = .var j ∧
      ∃ w, Ctx.lookup (joinedMK Θ families v joins hm).raw j = .head w ∧ S.R.isUniverse w := by
  intro i member
  obtain ⟨w, hw, uw⟩ := occ i member
  by_cases hl : i = v.left
  · have nil : v.psl = [] := by
      have decl := v.declared_left
      rw [← hl, hw] at decl
      exact Miller.famCode_eq_head decl.symm
    have zero : v.ps.length = 0 := by rw [lengths_left v, nil]; rfl
    have nilJ : psJ = [] := List.eq_nil_of_length_eq_zero (by
      rw [← joins.length_left, nil]; rfl)
    refine ⟨v.right, by rw [hl, joinKSub_left, zero]; rfl, m, ?_, hm⟩
    rw [joinedMK_self]
    subst nilJ
    rfl
  · by_cases hr : i = v.right
    · have nil : v.psr = [] := by
        have decl := v.declared_right
        rw [← hr, hw] at decl
        exact Miller.famCode_eq_head decl.symm
      have zero : v.ps.length = 0 := by rw [lengths_right v, nil]; rfl
      have nilJ : psJ = [] := List.eq_nil_of_length_eq_zero (by
        rw [← forall₂_length joins.right, nil]; rfl)
      refine ⟨v.right, by rw [hr, joinKSub_right, zero]; rfl, m, ?_, hm⟩
      rw [joinedMK_self]
      subst nilJ
      rfl
    · refine ⟨i, joinKSub_ne _ _ _ hl hr, w, ?_, uw⟩
      rw [joinedMK_ne Θ families v joins hm hr, hw]

/-- **A glb-join step keeps an equation between arrow codes one.** -/
theorem arrowEq_joinSide (choices : ExecutableChecking.HeadChoices S.R) {Θ : Context S.R}
    (families : Miller.Families Θ) {e : Equation (TotalTerm Θ)} (v : FlexK e) {psJ : List Head}
    (joins : JoinsK S.R v.psl v.psr psJ) {m : Head} (hm : S.R.isUniverse m) (lowL : S.R.cumulative m v.cl)
    (lowR : S.R.cumulative m v.cr) {e' : Equation (TotalTerm Θ)} (inside : InArrowsCod choices [e']) :
    InArrowsCod choices
      [((joinSide families v joins hm lowL lowR e'.1, joinSide families v joins hm lowL lowR e'.2) :
        Equation (TotalTerm (joinedMK Θ families v joins hm)))] := by
  have self := List.mem_singleton_self e'
  obtain ⟨w⟩ := inside.shapes e' self
  obtain ⟨occL, occR⟩ := inside.occurring e' self
  obtain ⟨headsL, headsR⟩ := inside.typedHeads e' self
  -- each side's code after the step: a renaming of its unknowns
  have side : ∀ (s : TotalTerm Θ), s.1.code = .head w.v → ArrowCod s.2.code → AtUniverses (S := S) Θ.raw s.2.code →
      (∀ h ∈ codHeads s.2.code, (choices.typing h).isSome = true) →
      (joinSide families v joins hm lowL lowR s).1.code = .head w.v ∧
        ArrowCod (joinSide families v joins hm lowL lowR s).2.code ∧
        AtUniverses (S := S) (joinedMK Θ families v joins hm).raw (joinSide families v joins hm lowL lowR s).2.code ∧
        ∀ h ∈ codHeads (joinSide families v joins hm lowL lowR s).2.code, (choices.typing h).isSome = true := by
    intro s annotation code occ heads'
    rcases joinSide_cases families v joins hm lowL lowR s with ⟨ps', q', hr, same⟩ | same
    · have nil : ps' = [] := Miller.famCode_eq_head (hr.1.symm.trans annotation)
      rw [same]
      refine ⟨?_, ?_, ?_, ?_⟩
      · change Presentation.subst (joinKSub v.ps.length v.left v.right) s.1.code = .head w.v
        rw [annotation]
        rfl
      · change ArrowCod (etaExp ps'.length (.var v.right))
        rw [nil]
        exact .var _
      · change AtUniverses (S := S) _ (etaExp ps'.length (.var v.right))
        rw [nil]
        intro j member
        have same' : j = v.right := Finset.mem_singleton.mp member
        subst same'
        rcases hr.2.1 with codeL | codeR
        · rw [codeL, nil] at occ
          obtain ⟨wl, hwl, _⟩ := occ v.left (Finset.mem_singleton_self _)
          have nilL : v.psl = [] := Miller.famCode_eq_head (v.declared_left.symm.trans hwl)
          have nilJ : psJ = [] := List.eq_nil_of_length_eq_zero (by rw [← joins.length_left, nilL]; rfl)
          exact ⟨m, by rw [joinedMK_self]; subst nilJ; rfl, hm⟩
        · rw [codeR, nil] at occ
          obtain ⟨wr, hwr, _⟩ := occ v.right (Finset.mem_singleton_self _)
          have nilR : v.psr = [] := Miller.famCode_eq_head (v.declared_right.symm.trans hwr)
          have nilJ : psJ = [] := List.eq_nil_of_length_eq_zero (by
            rw [← forall₂_length joins.right, nilR]; rfl)
          exact ⟨m, by rw [joinedMK_self]; subst nilJ; rfl, hm⟩
      · change ∀ h ∈ codHeads (etaExp ps'.length (.var v.right) : Tm Head Θ.arity), _
        rw [nil]
        intro h member
        cases member
    · rw [same]
      have vars := joinKSub_on_arrows families v joins hm occ
      refine ⟨?_, ?_, ?_, ?_⟩
      · change Presentation.subst (joinKSub v.ps.length v.left v.right) s.1.code = .head w.v
        rw [annotation]
        rfl
      · exact arrowCod_subst_vars code _ fun i h => (vars i h).elim fun j hj => ⟨j, hj.1⟩
      · intro j member
        obtain ⟨i, hi, hj⟩ := Miller.support_subst_sub s.2.code _ member
        obtain ⟨j', eq, w', hw', uw'⟩ := vars i hi
        change j ∈ (joinKSub (Head := Head) v.ps.length v.left v.right i).support at hj
        rw [eq] at hj
        have same' : j = j' := Finset.mem_singleton.mp hj
        subst same'
        exact ⟨w', hw', uw'⟩
      · change ∀ h ∈ codHeads (Presentation.subst (joinKSub v.ps.length v.left v.right) s.2.code), _
        rw [codHeads_subst_vars code _ fun i h => (vars i h).elim fun j hj => ⟨j, hj.1⟩]
        exact heads'
  obtain ⟨aL, cL, oL, hL⟩ := side e'.1 w.annotation_left w.code_left occL headsL
  obtain ⟨aR, cR, oR, hR⟩ := side e'.2 w.annotation_right w.code_right occR headsR
  have families' : Miller.Families (joinedMK Θ families v joins hm) :=
    Miller.redecl_families Θ families v.right psJ m joins.universes hm
  refine ⟨fun e'' m' => ?_, fun e'' m' => ?_, fun e'' m' => ?_, fun e'' m' => ?_⟩
  · obtain rfl := List.mem_singleton.mp m'
    exact ⟨oL, oR⟩
  · obtain rfl := List.mem_singleton.mp m'
    exact Miller.sidesApart_of_families families' _ _
  · obtain rfl := List.mem_singleton.mp m'
    exact ⟨⟨w.v, aL, aR, w.universe_v, cL, cR⟩⟩
  · obtain rfl := List.mem_singleton.mp m'
    exact ⟨hL, hR⟩

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative] in
/-- **A flex–flex equation of families of no parameters is an equation between arrow codes**, over a telescope of
universe families. -/
theorem arrows_of_flexK_nil (choices : ExecutableChecking.HeadChoices S.R) {Θ : Context S.R}
    (families : Miller.Families Θ) {e : Equation (TotalTerm Θ)} (v : FlexK e) (nil : v.ps = []) :
    InArrowsCod choices [e] := by
  have nilL : v.psl = [] := by
    have := forall₂_length v.domain_left
    rw [nil] at this
    exact List.eq_nil_of_length_eq_zero this.symm
  have nilR : v.psr = [] := by
    have := forall₂_length v.domain_right
    rw [nil] at this
    exact List.eq_nil_of_length_eq_zero this.symm
  have codeL : e.1.2.code = .var v.left := by rw [v.side_left, nil]; rfl
  have codeR : e.2.2.code = .var v.right := by rw [v.side_right, nil]; rfl
  have annL : e.1.1.code = .head v.q := by rw [v.annotation_left, nil]; rfl
  have annR : e.2.1.code = .head v.q := by rw [v.annotation_right, nil]; rfl
  have occ : ∀ (X : Fin Θ.arity) {ps : List Head} {c : Head}, Ctx.lookup Θ.raw X = famCode ps c → ps = [] →
      S.R.isUniverse c → AtUniverses (S := S) Θ.raw (.var X) := by
    intro X ps c decl empty uc j member
    have same : j = X := Finset.mem_singleton.mp member
    subst same
    exact ⟨c, by rw [decl, empty]; rfl, uc⟩
  refine ⟨fun e' m => ?_, fun e' m => ?_, fun e' m => ?_, fun e' m => ?_⟩
  · obtain rfl := List.mem_singleton.mp m
    rw [codeL, codeR]
    exact ⟨occ v.left v.declared_left nilL v.universe_cl, occ v.right v.declared_right nilR v.universe_cr⟩
  · obtain rfl := List.mem_singleton.mp m
    exact Miller.sidesApart_of_families families _ _
  · obtain rfl := List.mem_singleton.mp m
    exact ⟨⟨v.q, annL, annR, v.universe_q, by rw [codeL]; exact .var _, by rw [codeR]; exact .var _⟩⟩
  · obtain rfl := List.mem_singleton.mp m
    rw [codeL, codeR]
    exact ⟨fun h member => (by cases member), fun h member => (by cases member)⟩

end JoinArrows

/-! ## Mixed join stores -/

section Mixed

variable {S : Setting Head L}

/-- A sub-store of a store of the glb-join fragment lies in it. -/
theorem InGlbJoinFragmentK.sub {Θ : Context S.R} {F Q : EquationStore (TotalTerm Θ)} (inside : InGlbJoinFragmentK F)
    (within : ∀ e ∈ Q, e ∈ F) : InGlbJoinFragmentK Q := by
  obtain ⟨group, grouped, compat⟩ := inside.grouped
  exact ⟨inside.families, fun e m => inside.shapes e (within e m),
    ⟨group, fun e m => grouped e (within e m), compat⟩⟩

/-- **A store mixing glb-join families and arrow codes**: up to order, a store of the glb-join fragment followed by
equations between arrow codes, over a telescope of universe families. -/
structure MixedJoinStore (choices : ExecutableChecking.HeadChoices S.R) {Θ : Context S.R}
    (problem : EquationStore (TotalTerm Θ)) : Prop where
  families : Miller.Families Θ
  split : ∃ F A : EquationStore (TotalTerm Θ), problem.Perm (F ++ A) ∧ InGlbJoinFragmentK F ∧
    ∀ e ∈ A, InArrowsCod choices [e]

variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]

/-- **A flex–flex equation of families with parameters**, read off the codes. -/
def isFamEq {Θ : Context S.R} (e : Equation (TotalTerm Θ)) : Bool :=
  match readFlexK (S := S) e with
  | some d => !d.ps.isEmpty
  | none => false

theorem isFamEq_of_view {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexK e) (params : v.ps ≠ []) :
    isFamEq e = true := by
  unfold isFamEq
  rw [readFlexK_complete v]
  simp [params]

theorem not_arrows_of_isFamEq (choices : ExecutableChecking.HeadChoices S.R) {Θ : Context S.R}
    {e : Equation (TotalTerm Θ)} (fam : isFamEq e = true) : ¬ InArrowsCod choices [e] := by
  intro arrows
  obtain ⟨w⟩ := arrows.shapes e (List.mem_singleton_self _)
  unfold isFamEq at fam
  cases hd : readFlexK (S := S) e with
  | none => rw [hd] at fam; cases fam
  | some d =>
      rw [hd] at fam
      have nil : d.ps = [] := Miller.famCode_eq_head ((readFlexK_sound hd).1.symm.trans w.annotation_left)
      dsimp only at fam
      rw [nil] at fam
      simp at fam

/-- **The families with parameters first.** -/
def joinFirst {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : EquationStore (TotalTerm Θ) :=
  problem.filter (fun e => isFamEq e) ++ problem.filter (fun e => !isFamEq e)

theorem joinFirst_perm {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    (joinFirst problem).Perm problem :=
  List.filter_append_perm _ _

/-- **Families with parameters first, the rest after**: the first part lies in the glb-join fragment, the rest are
equations between arrow codes. -/
theorem joinFirst_parts (choices : ExecutableChecking.HeadChoices S.R) {Θ : Context S.R}
    {problem : EquationStore (TotalTerm Θ)} (mixed : MixedJoinStore choices problem) :
    InGlbJoinFragmentK (problem.filter (fun e => isFamEq e)) ∧
      ∀ e ∈ problem.filter (fun e => !isFamEq e), InArrowsCod choices [e] := by
  obtain ⟨F, A, perm, inF, inA⟩ := mixed.split
  have whereFrom : ∀ e ∈ problem, e ∈ F ∨ e ∈ A := fun e m => List.mem_append.mp (perm.mem_iff.mp m)
  refine ⟨inF.sub fun e m => ?_, fun e m => ?_⟩
  · obtain ⟨member, fam⟩ := List.mem_filter.mp m
    rcases whereFrom e member with inside | arrow
    · exact inside
    · exact absurd (inA e arrow) (not_arrows_of_isFamEq choices fam)
  · obtain ⟨member, notFam⟩ := List.mem_filter.mp m
    rcases whereFrom e member with inside | arrow
    · obtain ⟨v⟩ := inF.shapes e inside
      by_cases params : v.ps = []
      · exact arrows_of_flexK_nil choices mixed.families v params
      · have := isFamEq_of_view v params
        simp [this] at notFam
    · exact inA e arrow

end Mixed

/-! ## The solver -/

section Solver

variable {S : Setting Head L}
variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
  [DecidableRel S.R.headEq]
variable (choices : ExecutableChecking.HeadChoices S.R)
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (declared : DeclaredTypesFormed S.R)
  (strengthening : ContextualDependentIntersectionGeneral.EqualStrengthening S.R)
  (join : Head → Head → Option Head)
  (joinSound : ∀ {u v w : Head}, join u v = some w → S.R.isUniverse w ∧ IsLub S.R w u v)
  (glb : Head → Head → Option Head) (spec : ∀ {a b g : Head}, glb a b = some g → IsGlb S.R g a b)

omit [DecidableRel S.R.headEq] in
/-- **The glb-join round on a mixed join store keeps it mixed**: the families stay in the fragment, the equations
between arrow codes stay such. -/
theorem glbJoinRoundK_mixed {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {F A : EquationStore (TotalTerm Θ)}
    {Q : EquationStore (TotalTerm Θ)} (hQ : Q = (e :: F) ++ A)
    (inF : InGlbJoinFragmentK (e :: F)) (inA : ∀ a ∈ A, InArrowsCod choices [a])
    {update : Update S.levels Q}
    {smaller : ContextualDependentWorklist.Below (storeRank update.remaining) (storeRank Q)}
    (progressed : glbJoinRoundK facts roots heads algebra rigid complete headTypingUnique join joinSound glb spec
      Q = .progress update smaller) :
    MixedJoinStore choices update.remaining := by
  subst hQ
  simp only [List.cons_append, glbJoinRoundK] at progressed
  split_ifs at progressed with hfam
  split at progressed
  · rename_i d hd
    unfold stepGlbJoinK at progressed
    split_ifs at progressed with h1 h2
    · cases progressed
      exact ⟨hfam, F, A, List.Perm.refl _, inGlbJoinFragmentK_delete inF, inA⟩
    · split at progressed
      · rename_i gl hg
        split at progressed
        · rename_i psJ hj
          cases progressed
          refine ⟨Miller.redecl_families Θ hfam _ psJ _ (joinsOf_sound join joinSound hj).universes
            (spec hg).1,
            joinStore hfam (viewOfK hd) (joinsOf_sound join joinSound hj) (spec hg).1 (spec hg).2.1 (spec hg).2.2.1 F,
            joinStore hfam (viewOfK hd) (joinsOf_sound join joinSound hj) (spec hg).1 (spec hg).2.1 (spec hg).2.2.1 A,
            ?_, inGlbJoinFragmentK_step algebra inF (viewOfK hd) (spec hg)
              (joinsOf_sound join joinSound hj), fun a member => ?_⟩
          · exact List.Perm.of_eq (List.map_append ..)
          · obtain ⟨a₀, m₀, rfl⟩ := List.mem_map.mp member
            exact arrowEq_joinSide choices hfam (viewOfK hd) (joinsOf_sound join joinSound hj) (spec hg).1
              (spec hg).2.1 (spec hg).2.2.1 (inA a₀ m₀)
        · cases progressed
      · cases progressed
  · cases progressed

variable (joinTotal : ∀ {u v : Head}, S.R.isUniverse u → S.R.isUniverse v → ∃ w, join u v = some w)
  (glbTotal : ∀ {a b : Head}, S.R.isUniverse a → S.R.isUniverse b → ∃ g, glb a b = some g)

omit [DecidableRel S.R.headEq] in
include joinTotal glbTotal in
/-- **The glb-join round is not stuck on a store whose first equation lies in the glb-join fragment.** -/
theorem glbJoinRoundK_ne_stuck_head {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {F A : EquationStore (TotalTerm Θ)}
    {Q : EquationStore (TotalTerm Θ)} (hQ : Q = (e :: F) ++ A) (inF : InGlbJoinFragmentK (e :: F)) :
    glbJoinRoundK facts roots heads algebra rigid complete headTypingUnique join joinSound glb spec Q ≠ .stuck := by
  subst hQ
  obtain ⟨v⟩ := inF.shapes e List.mem_cons_self
  obtain ⟨group, grouped, compat⟩ := inF.grouped
  have hd := readFlexK_complete v
  simp only [List.cons_append, glbJoinRoundK, dif_pos inF.families]
  split
  · rename_i d hd'
    let w := viewOfK hd'
    have lengths : w.psl.length = w.psr.length := (lengths_left w).symm.trans (lengths_right w)
    obtain ⟨ws, hws⟩ := joinsOf_total join joinTotal lengths w.universes_left w.universes_right
    obtain ⟨g, hg⟩ := glbTotal w.universe_cl w.universe_cr
    unfold stepGlbJoinK
    split_ifs with h1 h2
    · intro h; cases h
    · split
      · split
        · intro h; cases h
        · rename_i hj
          rw [hws] at hj
          cases hj
      · rename_i hg'
        rw [hg] at hg'
        cases hg'
    · exact absurd (compat w.left w.right h1 (grouped e List.mem_cons_self w) w.psl w.cl w.psr w.cr
        w.declared_left w.declared_right lengths) h2
  · rename_i hd'
    rw [hd] at hd'
    cases hd'

/-- **The round of the mixed join solver.** -/
def mixedJoinRound {Γ : Context S.R} (problem : EquationStore (TotalTerm Γ)) : Round S.levels commonRank problem :=
  if hA : inArrowsCodB choices problem = true then
    retarget (arrowCodRound choices glb spec facts roots heads algebra rigid complete headTypingUnique declared
        strengthening problem)
      (fun _ _ progressed => arrowCodRound_commonRank choices glb spec facts roots heads algebra rigid complete
        headTypingUnique declared strengthening (inArrowsCod_of_B choices hA) progressed)
  else
    transport (equivalent_perm (joinFirst_perm problem).symm) (commonRank_perm (joinFirst_perm problem))
      (retarget (glbJoinRoundK facts roots heads algebra rigid complete headTypingUnique join joinSound glb spec
          (joinFirst problem))
        (fun _ _ progressed => glbJoinRoundK_commonRank facts roots heads algebra rigid complete headTypingUnique join
          joinSound glb spec progressed))

/-- **The mixed join solver**: one rank, the piece read at every round. -/
def mixedJoinSolver : ContextualDependentWorklist.Solver S.levels where
  rank := commonRank
  round := mixedJoinRound choices facts roots heads algebra rigid complete headTypingUnique declared strengthening join
    joinSound glb spec

/-- **Its fragment**: the fragment of arrow codes, or a mixed join store. -/
def InMixedJoin {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Prop :=
  InArrowsCod choices problem ∨ MixedJoinStore choices problem

omit [DecidableRel S.R.cumulative] [DecidableRel S.R.headEq] in
theorem mixedJoin_of_not_arrows {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (inside : InMixedJoin choices problem) (notArrows : ¬ inArrowsCodB choices problem = true) :
    MixedJoinStore choices problem := by
  rcases inside with arrows | mixed
  · exact absurd (Miller.inArrowsCodB_of choices arrows) notArrows
  · exact mixed

omit [DecidableRel S.R.headEq] in
/-- Outside the fragment of arrow codes, a mixed join store has a family with parameters, and it comes first. -/
theorem joinFirst_cons {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (mixed : MixedJoinStore choices problem) (notArrows : ¬ InArrowsCod choices problem) :
    ∃ e F, problem.filter (fun e => isFamEq e) = e :: F := by
  obtain ⟨F, A, perm, inF, inA⟩ := mixed.split
  obtain ⟨e₀, m₀, notArrow⟩ : ∃ e ∈ problem, ¬ InArrowsCod choices [e] := by
    by_contra none
    apply notArrows
    apply Miller.inArrowsCod_iff.mpr
    intro e m
    by_contra h
    exact none ⟨e, m, h⟩
  have inFe : e₀ ∈ F := by
    rcases List.mem_append.mp (perm.mem_iff.mp m₀) with inside | arrow
    · exact inside
    · exact absurd (inA e₀ arrow) notArrow
  obtain ⟨v⟩ := inF.shapes e₀ inFe
  have params : v.ps ≠ [] := fun nil => notArrow (arrows_of_flexK_nil choices mixed.families v nil)
  have inFilter : e₀ ∈ problem.filter (fun e => isFamEq e) :=
    List.mem_filter.mpr ⟨m₀, isFamEq_of_view v params⟩
  cases hf : problem.filter (fun e => isFamEq e) with
  | nil => rw [hf] at inFilter; cases inFilter
  | cons e F' => exact ⟨e, F', rfl⟩

/-- **The rounds keep the fragment.** -/
theorem mixedJoinRound_stable {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}
    {update : Update S.levels problem}
    {smaller : ContextualDependentWorklist.Below (commonRank update.remaining) (commonRank problem)}
    (inside : InMixedJoin choices problem)
    (progressed : mixedJoinRound choices facts roots heads algebra rigid complete headTypingUnique declared
      strengthening join joinSound glb spec problem = .progress update smaller) :
    InMixedJoin choices update.remaining := by
  unfold mixedJoinRound at progressed
  split at progressed
  · rename_i hA
    obtain ⟨_, inner⟩ := retarget_progress progressed
    exact .inl (arrowCodRound_stable choices glb spec facts roots heads algebra rigid complete headTypingUnique
      declared strengthening (inArrowsCod_of_B choices hA) inner)
  · rename_i hA
    obtain ⟨inner, _, isInner, rfl⟩ := transport_progress progressed
    obtain ⟨_, isJoin⟩ := retarget_progress isInner
    have mixed := mixedJoin_of_not_arrows choices inside hA
    have notArrows : ¬ InArrowsCod choices problem := fun arrows => hA (Miller.inArrowsCodB_of choices arrows)
    obtain ⟨inF, inA⟩ := joinFirst_parts choices mixed
    obtain ⟨e, F, hf⟩ := joinFirst_cons choices mixed notArrows
    rw [hf] at inF
    have hQ : joinFirst problem = (e :: F) ++ problem.filter (fun e => !isFamEq e) := by
      unfold joinFirst
      rw [hf]
    exact .inr (glbJoinRoundK_mixed choices facts roots heads algebra rigid complete headTypingUnique join joinSound
      glb spec hQ inF inA isJoin)

include joinTotal glbTotal in
/-- **Progress on the fragment**: a nonempty store is never stuck. -/
theorem mixedJoinRound_ne_stuck {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}
    (inside : InMixedJoin choices problem) (nonempty : problem ≠ []) :
    mixedJoinRound choices facts roots heads algebra rigid complete headTypingUnique declared strengthening join
      joinSound glb spec problem ≠ .stuck := by
  unfold mixedJoinRound
  split
  · rename_i hA
    exact retarget_ne_stuck (arrowCodRound_ne_stuck choices glb spec facts roots heads algebra rigid complete
      headTypingUnique declared strengthening glbTotal (inArrowsCod_of_B choices hA) nonempty)
  · rename_i hA
    apply transport_ne_stuck
    apply retarget_ne_stuck
    have mixed := mixedJoin_of_not_arrows choices inside hA
    have notArrows : ¬ InArrowsCod choices problem := fun arrows => hA (Miller.inArrowsCodB_of choices arrows)
    obtain ⟨inF, _⟩ := joinFirst_parts choices mixed
    obtain ⟨e, F, hf⟩ := joinFirst_cons choices mixed notArrows
    rw [hf] at inF
    have hQ : joinFirst problem = (e :: F) ++ problem.filter (fun e => !isFamEq e) := by
      unfold joinFirst
      rw [hf]
    exact glbJoinRoundK_ne_stuck_head facts roots heads algebra rigid complete headTypingUnique join joinSound glb spec
      joinTotal glbTotal hQ inF

include joinTotal glbTotal in
/-- **The fragment of the mixed join solver.** -/
def mixedJoinFragment :
    ContextualDependentWorklist.Fragment
      (mixedJoinSolver choices facts roots heads algebra rigid complete headTypingUnique declared strengthening join
        joinSound glb spec) where
  holds := InMixedJoin choices
  stable := fun inside progressed =>
    mixedJoinRound_stable choices facts roots heads algebra rigid complete headTypingUnique declared strengthening join
      joinSound glb spec inside progressed
  decisive := fun inside nonempty =>
    mixedJoinRound_ne_stuck choices facts roots heads algebra rigid complete headTypingUnique declared strengthening
      join joinSound glb spec joinTotal glbTotal inside nonempty

include joinTotal glbTotal in
/-- **Stores mixing glb-join families and arrow codes are decided by one solver with one rank.** -/
theorem mixedJoin_decided {Θ : Context S.R} {original : EquationStore (TotalTerm Θ)}
    (inside : InMixedJoin choices original) :
    ∃ fuel, ∀ larger, fuel ≤ larger →
      run (mixedJoinSolver choices facts roots heads algebra rigid complete headTypingUnique declared strengthening join
          joinSound glb spec) original larger =
        run (mixedJoinSolver choices facts roots heads algebra rigid complete headTypingUnique declared strengthening
          join joinSound glb spec) original fuel ∧
        ((∃ state finished,
              run (mixedJoinSolver choices facts roots heads algebra rigid complete headTypingUnique declared
                  strengthening join joinSound glb spec) original larger = .solved state finished ∧
                (frames S.levels).Principal original state.answer) ∨
          (∃ absent,
            run (mixedJoinSolver choices facts roots heads algebra rigid complete headTypingUnique declared strengthening
              join joinSound glb spec) original larger = .refuted absent)) :=
  (mixedJoinFragment choices facts roots heads algebra rigid complete headTypingUnique declared strengthening join
    joinSound glb spec joinTotal glbTotal).decided inside

end Solver

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
