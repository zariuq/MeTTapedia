import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.JoinForcing
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MillerSolver

/-!
# The join rule: two unknowns of incomparable domains

At `λ x̄. F x̄ ≐ λ x̄. G x̄`, with `F : Π (x̄ : U_{p̄F}). U_{cF}` and `G : Π (x̄ : U_{p̄G}). U_{cG}` over a telescope of
families, the rule declares `G` again at `Π (x̄ : U_{p̄J}). U_m`, with `p̄J` least upper bounds of the domains and `m`
below both codomains, and sends both `F` and the old `G` to its η-expansion (`joinMKHom`). The equation is solved by
the answer (`joinMK_head_solved`). When every solution sends `F` and `G` to η-expansions of one family of the new
declaration (`JoinForces`), every solution factors through the answer (`joinMK_factors`) and the step is exact
(`joinMK_exact`), whether or not the domains are comparable.

With one codomain the forcing is `joinK_forced`; this is the join (`joinKHom`, `joinK_exact`). With two codomains
it is the join with a meet (`JoinMeet`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentUniverseInjective ContextualDependentCumulative

variable {Head L : Type} [UniverseLevel.LevelOrder L]

/-! ## The answer -/

section Answer

/-- `F, G := λ x̄. G x̄` at `k` parameters, the identity elsewhere, on codes. -/
def joinKSub {n : Nat} (k : Nat) (F G : Fin n) : Sub Head n n :=
  fun i => if i = F ∨ i = G then etaExp k (.var G) else .var i

theorem joinKSub_left {n : Nat} (k : Nat) (F G : Fin n) : joinKSub (Head := Head) k F G F = etaExp k (.var G) := by
  simp [joinKSub]

theorem joinKSub_right {n : Nat} (k : Nat) (F G : Fin n) : joinKSub (Head := Head) k F G G = etaExp k (.var G) := by
  simp [joinKSub]

theorem joinKSub_ne {n : Nat} (k : Nat) (F G : Fin n) {i : Fin n} (hF : i ≠ F) (hG : i ≠ G) :
    joinKSub (Head := Head) k F G i = .var i := by
  simp [joinKSub, hF, hG]

variable {S : Setting Head L}

/-- **The telescope with the right unknown declared again** at `Π (x̄ : U_{p̄J}). U_m`. -/
abbrev joinedMK (Θ : Context S.R) (families : Miller.Families Θ) {e : Equation (TotalTerm Θ)} (v : FlexK e)
    {psJ : List Head} (joins : JoinsK S.R v.psl v.psr psJ) {m : Head} (hm : S.R.isUniverse m) : Context S.R :=
  Miller.redecl Θ families v.right psJ m joins.universes hm

theorem joinedMK_self (Θ : Context S.R) (families : Miller.Families Θ) {e : Equation (TotalTerm Θ)} (v : FlexK e)
    {psJ : List Head} (joins : JoinsK S.R v.psl v.psr psJ) {m : Head} (hm : S.R.isUniverse m) :
    Ctx.lookup (joinedMK Θ families v joins hm).raw v.right = famCode psJ m :=
  Miller.redecl_self Θ families v.right psJ m joins.universes hm

theorem joinedMK_ne (Θ : Context S.R) (families : Miller.Families Θ) {e : Equation (TotalTerm Θ)} (v : FlexK e)
    {psJ : List Head} (joins : JoinsK S.R v.psl v.psr psJ) {m : Head} (hm : S.R.isUniverse m) {i : Fin Θ.arity}
    (ne : i ≠ v.right) : Ctx.lookup (joinedMK Θ families v joins hm).raw i = Ctx.lookup Θ.raw i :=
  Miller.redecl_ne Θ families v.right psJ m joins.universes hm ne

theorem lengths_left {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexK e) : v.ps.length = v.psl.length :=
  forall₂_length v.domain_left

theorem lengths_right {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexK e) : v.ps.length = v.psr.length :=
  forall₂_length v.domain_right

/-- **The answer**: `left, right := λ x̄. right x̄`, `right` declared again. -/
def joinMKHom (Θ : Context S.R) (families : Miller.Families Θ) {e : Equation (TotalTerm Θ)} (v : FlexK e)
    {psJ : List Head} (joins : JoinsK S.R v.psl v.psr psJ) {m : Head} (hm : S.R.isUniverse m)
    (lowL : S.R.cumulative m v.cl) (lowR : S.R.cumulative m v.cr) : joinedMK Θ families v joins hm ⟶ Θ where
  substitution := joinKSub v.ps.length v.left v.right
  typed := by
    intro i
    obtain ⟨psi, ci, hi, _, _⟩ := families i
    rw [hi, famCode_subst]
    have tG : Typed S.R (joinedMK Θ families v joins hm).raw (.var v.right) (famCode psJ m) := by
      have typed := Derivable.var (R := S.R) (Γ := (joinedMK Θ families v joins hm).raw) v.right
      rw [joinedMK_self] at typed
      exact typed
    by_cases hl : i = v.left
    · rw [hl] at hi ⊢
      rw [joinKSub_left, hi.symm.trans v.declared_left, lengths_left v]
      exact raisedK_typed joins.left v.universes_left v.universe_cl lowL (joinedMK Θ families v joins hm).formed tG
    · by_cases hr : i = v.right
      · rw [hr] at hi ⊢
        rw [joinKSub_right, hi.symm.trans v.declared_right, lengths_right v]
        exact raisedK_typed joins.right v.universes_right v.universe_cr lowR (joinedMK Θ families v joins hm).formed
          tG
      · rw [joinKSub_ne _ _ _ hl hr]
        have typed := Derivable.var (R := S.R) (Γ := (joinedMK Θ families v joins hm).raw) i
        rw [joinedMK_ne Θ families v joins hm hr, hi] at typed
        exact typed

/-- **The answer solves the equation**: both sides become the same code. -/
theorem joinMK_head_solved {Θ Δ : Context S.R} (families : Miller.Families Θ) {e : Equation (TotalTerm Θ)}
    (v : FlexK e) {psJ : List Head} (joins : JoinsK S.R v.psl v.psr psJ) {m : Head} (hm : S.R.isUniverse m)
    (lowL : S.R.cumulative m v.cl) (lowR : S.R.cumulative m v.cr) (g : Δ ⟶ joinedMK Θ families v joins hm) :
    (frames S.levels).Solves (g ≫ joinMKHom Θ families v joins hm lowL lowR) e := by
  have tG : Typed S.R Δ.raw (g.substitution v.right) (famCode psJ m) := by
    have typed := g.typed v.right
    rw [joinedMK_self, famCode_subst] at typed
    exact typed
  have tL := raisedK_typed joins.left v.universes_left v.universe_cl lowL Δ.formed tG
  have tEta := raisedK_typed v.domain_left v.universes v.universe_q v.codomain_left Δ.formed tL
  rw [← lengths_left v] at tEta
  refine (equivalent_iff S.levels _ _).mpr ⟨?_, ?_⟩
  · change TypeEq S.R Δ.raw
      (Presentation.subst (subComp g.substitution (joinKSub v.ps.length v.left v.right)) e.1.1.code)
      (Presentation.subst (subComp g.substitution (joinKSub v.ps.length v.left v.right)) e.2.1.code)
    rw [v.annotation_left, v.annotation_right, famCode_subst]
    exact (Typed.isType tEta Δ.formed).refl
  · change Equal S.R Δ.raw
      (Presentation.subst (subComp g.substitution (joinKSub v.ps.length v.left v.right)) e.1.2.code)
      (Presentation.subst (subComp g.substitution (joinKSub v.ps.length v.left v.right)) e.2.2.code)
      (Presentation.subst (subComp g.substitution (joinKSub v.ps.length v.left v.right)) e.1.1.code)
    rw [v.side_left, v.side_right, v.annotation_left, subst_etaExp, subst_etaExp, famCode_subst]
    change Equal S.R Δ.raw
      (etaExp v.ps.length (Presentation.subst g.substitution (joinKSub v.ps.length v.left v.right v.left)))
      (etaExp v.ps.length (Presentation.subst g.substitution (joinKSub v.ps.length v.left v.right v.right)))
      (famCode v.ps v.q)
    rw [joinKSub_left, joinKSub_right, subst_etaExp]
    exact .refl tEta

/-! ### One codomain -/

theorem cr_below_cl {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexK e) (same : v.cl = v.cr) :
    S.R.cumulative v.cr v.cl := by
  rw [same]
  exact S.levels.cumulative_refl v.universe_cr

/-- **The telescope with the right unknown declared at the join** `Π (x̄ : U_{p̄l ⊔ p̄r}). U_{cr}`. -/
abbrev joinedK (Θ : Context S.R) (families : Miller.Families Θ) {e : Equation (TotalTerm Θ)} (v : FlexK e)
    {psJ : List Head} (joins : JoinsK S.R v.psl v.psr psJ) : Context S.R :=
  joinedMK Θ families v joins v.universe_cr

theorem joinedK_self (Θ : Context S.R) (families : Miller.Families Θ) {e : Equation (TotalTerm Θ)} (v : FlexK e)
    {psJ : List Head} (joins : JoinsK S.R v.psl v.psr psJ) :
    Ctx.lookup (joinedK Θ families v joins).raw v.right = famCode psJ v.cr :=
  joinedMK_self Θ families v joins v.universe_cr

theorem joinedK_ne (Θ : Context S.R) (families : Miller.Families Θ) {e : Equation (TotalTerm Θ)} (v : FlexK e)
    {psJ : List Head} (joins : JoinsK S.R v.psl v.psr psJ) {i : Fin Θ.arity} (ne : i ≠ v.right) :
    Ctx.lookup (joinedK Θ families v joins).raw i = Ctx.lookup Θ.raw i :=
  joinedMK_ne Θ families v joins v.universe_cr ne

/-- **The answer of the join**: `left, right := λ x̄. right x̄`, `right` declared at the join. -/
def joinKHom (Θ : Context S.R) (families : Miller.Families Θ) {e : Equation (TotalTerm Θ)} (v : FlexK e)
    (same : v.cl = v.cr) {psJ : List Head} (joins : JoinsK S.R v.psl v.psr psJ) : joinedK Θ families v joins ⟶ Θ :=
  joinMKHom Θ families v joins v.universe_cr (cr_below_cl v same) (S.levels.cumulative_refl v.universe_cr)

theorem joinK_head_solved {Θ Δ : Context S.R} (families : Miller.Families Θ) {e : Equation (TotalTerm Θ)}
    (v : FlexK e) (same : v.cl = v.cr) {psJ : List Head} (joins : JoinsK S.R v.psl v.psr psJ)
    (g : Δ ⟶ joinedK Θ families v joins) :
    (frames S.levels).Solves (g ≫ joinKHom Θ families v same joins) e :=
  joinMK_head_solved families v joins v.universe_cr _ _ g

end Answer

/-! ## The rule on a whole store -/

section Store

variable {S : Setting Head L}

/-- **What the rule needs**: every solution sends both unknowns to η-expansions of one family of the new
declaration. -/
def JoinForces {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexK e) (psJ : List Head) (m : Head) : Prop :=
  ∀ {Δ : Context S.R} (f : Δ ⟶ Θ), (frames S.levels).Solves f e →
    ∃ h, Typed S.R Δ.raw h (famCode psJ m) ∧
      Equal S.R Δ.raw (f.substitution v.left) (etaExp v.psl.length h) (famCode v.psl v.cl) ∧
      Equal S.R Δ.raw (f.substitution v.right) (etaExp v.psr.length h) (famCode v.psr v.cr)

/-- **Every solution factors through the answer**, up to the frame's equality, when the rule's forcing holds. -/
theorem joinMK_factors {Θ Δ : Context S.R} (families : Miller.Families Θ) {e : Equation (TotalTerm Θ)} (v : FlexK e)
    {psJ : List Head} (joins : JoinsK S.R v.psl v.psr psJ) {m : Head} (hm : S.R.isUniverse m)
    (lowL : S.R.cumulative m v.cl) (lowR : S.R.cumulative m v.cr) (forces : JoinForces v psJ m) (f : Δ ⟶ Θ)
    (solved : (frames S.levels).Solves f e) :
    ∃ g : Δ ⟶ joinedMK Θ families v joins hm,
      homTypedEquality S.R f (g ≫ joinMKHom Θ families v joins hm lowL lowR) := by
  obtain ⟨h, tH, eL, eR⟩ := forces f solved
  have typed : SubstMor S.R (joinedMK Θ families v joins hm).raw Δ.raw (replaceAt f.substitution v.right h) := by
    intro i
    obtain ⟨psi, ci, hi, _, _⟩ := families i
    by_cases hr : i = v.right
    · rw [hr, joinedMK_self, replaceAt_self, famCode_subst]
      exact tH
    · rw [joinedMK_ne Θ families v joins hm hr, hi, famCode_subst, replaceAt_ne _ _ hr]
      have tf := f.typed i
      rw [hi, famCode_subst] at tf
      exact tf
  refine ⟨⟨replaceAt f.substitution v.right h, typed⟩, ?_⟩
  refine ⟨f.typed, fun i => ?_⟩
  change Equal S.R Δ.raw (f.substitution i)
    (Presentation.subst (replaceAt f.substitution v.right h) (joinKSub v.ps.length v.left v.right i))
    (Presentation.subst f.substitution (Ctx.lookup Θ.raw i))
  by_cases hl : i = v.left
  · rw [hl, joinKSub_left, subst_etaExp, v.declared_left, famCode_subst]
    change Equal S.R Δ.raw (f.substitution v.left) (etaExp v.ps.length (replaceAt f.substitution v.right h v.right))
      (famCode v.psl v.cl)
    rw [replaceAt_self, lengths_left v]
    exact eL
  · by_cases hr : i = v.right
    · rw [hr, joinKSub_right, subst_etaExp, v.declared_right, famCode_subst]
      change Equal S.R Δ.raw (f.substitution v.right)
        (etaExp v.ps.length (replaceAt f.substitution v.right h v.right)) (famCode v.psr v.cr)
      rw [replaceAt_self, lengths_right v]
      exact eR
    · rw [joinKSub_ne _ _ _ hl hr]
      change Equal S.R Δ.raw (f.substitution i) (replaceAt f.substitution v.right h i) _
      rw [replaceAt_ne _ _ hr]
      exact .refl (f.typed i)

/-- **The rule, with several parameters**: the solved equation is removed, the others are transported. -/
def joinMKUpdate {Θ : Context S.R} (families : Miller.Families Θ) {e : Equation (TotalTerm Θ)} (v : FlexK e)
    {psJ : List Head} (joins : JoinsK S.R v.psl v.psr psJ) {m : Head} (hm : S.R.isUniverse m)
    (lowL : S.R.cumulative m v.cl) (lowR : S.R.cumulative m v.cr) (forces : JoinForces v psJ m)
    (rest : EquationStore (TotalTerm Θ)) : Update S.levels (e :: rest) where
  target := joinedMK Θ families v joins hm
  answer := joinMKHom Θ families v joins hm lowL lowR
  remaining := (frames S.levels).applyStore (joinMKHom Θ families v joins hm lowL lowR) rest
  sound := by
    intro Δ g solved e' member
    rcases List.mem_cons.mp member with rfl | member
    · exact joinMK_head_solved families v joins hm lowL lowR g
    · exact (Frames.models_applyStore (X := frames S.levels) _ g rest).mp solved e' member
  complete := by
    intro Δ f solved
    obtain ⟨g, factored⟩ := joinMK_factors families v joins hm lowL lowR forces f (solved e List.mem_cons_self)
    refine ⟨g, ?_, act_equal_of_substEq S.levels factored⟩
    apply (Frames.models_applyStore (X := frames S.levels) _ g rest).mpr
    exact (Elimination.models_pointwise S.levels (act_equal_of_substEq S.levels factored) rest).mp
      (fun e' member => solved e' (List.mem_cons_of_mem _ member))

/-- **The rule is exact** when its forcing holds, domains not necessarily comparable. -/
theorem joinMK_exact {Θ : Context S.R} (families : Miller.Families Θ) {e : Equation (TotalTerm Θ)} (v : FlexK e)
    {psJ : List Head} (joins : JoinsK S.R v.psl v.psr psJ) {m : Head} (hm : S.R.isUniverse m)
    (lowL : S.R.cumulative m v.cl) (lowR : S.R.cumulative m v.cr) (forces : JoinForces v psJ m)
    (rest : EquationStore (TotalTerm Θ)) :
    Exact (frames S.levels) (e :: rest) (joinMKHom Θ families v joins hm lowL lowR)
      ((frames S.levels).applyStore (joinMKHom Θ families v joins hm lowL lowR) rest) :=
  (DependentFibre.exact_iff_update (levels := S.levels) _ _).mpr
    ⟨joinMKUpdate families v joins hm lowL lowR forces rest, rfl, rfl, rfl⟩

/-! ### One codomain: the join -/

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)
  (headsTyped : ∀ {h u u' : Head}, S.R.headTyping h u → S.R.headTyping h u' → u = u')

include facts roots heads algebra rigid complete headsTyped in
/-- With one codomain, the join forces (`joinK_forced`). -/
theorem joinK_forces {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexK e) (same : v.cl = v.cr)
    {psJ : List Head} (joins : JoinsK S.R v.psl v.psr psJ) : JoinForces v psJ v.cr :=
  fun f solved => joinK_forced facts roots heads algebra rigid complete headsTyped v same joins f solved

include facts roots heads algebra rigid complete headsTyped in
/-- **Every solution of the equation factors through the join**, up to the frame's equality. -/
theorem joinK_factors {Θ Δ : Context S.R} (families : Miller.Families Θ) {e : Equation (TotalTerm Θ)} (v : FlexK e)
    (same : v.cl = v.cr) {psJ : List Head} (joins : JoinsK S.R v.psl v.psr psJ) (f : Δ ⟶ Θ)
    (solved : (frames S.levels).Solves f e) :
    ∃ g : Δ ⟶ joinedK Θ families v joins, homTypedEquality S.R f (g ≫ joinKHom Θ families v same joins) :=
  joinMK_factors families v joins v.universe_cr _ _
    (joinK_forces facts roots heads algebra rigid complete headsTyped v same joins) f solved

/-- **The join, with several parameters**: the solved equation is removed, the others are transported. -/
def joinKUpdate {Θ : Context S.R} (families : Miller.Families Θ) {e : Equation (TotalTerm Θ)} (v : FlexK e)
    (same : v.cl = v.cr) {psJ : List Head} (joins : JoinsK S.R v.psl v.psr psJ)
    (rest : EquationStore (TotalTerm Θ)) : Update S.levels (e :: rest) :=
  joinMKUpdate families v joins v.universe_cr (cr_below_cl v same) (S.levels.cumulative_refl v.universe_cr)
    (joinK_forces facts roots heads algebra rigid complete headsTyped v same joins) rest

include facts roots heads algebra rigid complete headsTyped in
/-- **The join is exact**, with several parameters and domains not necessarily comparable. -/
theorem joinK_exact {Θ : Context S.R} (families : Miller.Families Θ) {e : Equation (TotalTerm Θ)} (v : FlexK e)
    (same : v.cl = v.cr) {psJ : List Head} (joins : JoinsK S.R v.psl v.psr psJ)
    (rest : EquationStore (TotalTerm Θ)) :
    Exact (frames S.levels) (e :: rest) (joinKHom Θ families v same joins)
      ((frames S.levels).applyStore (joinKHom Θ families v same joins) rest) :=
  joinMK_exact families v joins v.universe_cr _ _
    (joinK_forces facts roots heads algebra rigid complete headsTyped v same joins) rest

end Store

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
