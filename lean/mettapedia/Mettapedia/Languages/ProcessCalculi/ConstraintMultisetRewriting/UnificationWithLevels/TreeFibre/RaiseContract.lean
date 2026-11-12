import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.DomainRaising
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.FamilySolver

/-!
# Domain raising on a whole store: the other equations re-read without the new redex

The answer `G := λ x. F x` of domain raising turns a side `λ y. G y` of another equation into `λ y. (λ x. F x) y`.
That side is typed-equal to `λ y. F y` at its own annotation whenever `F`'s view fits it. So the residual store
re-reads such a side as `λ y. F y` (`contractSide`), and leaves every other side instantiated.

* `etaExp_congr`: equal families stay equal under η-expansion at a narrower domain and a wider codomain.
* `contract_sound`, `contract_complete`: the re-read side is equal, in the frame, to the instantiated side, for the
  residual solutions and for the original solutions.
* **The rule on a whole store** (`raiseContractUpdate`, `raiseContract_exact`): `G := λ x. F x`, with the solved
  equation removed and the other sides re-read; an update of the tree's driver, hence exact.
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

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-! ## η-expansion is a congruence -/

/-- **Equal families stay equal under η-expansion**, at a narrower domain and a wider codomain. -/
theorem etaExp_congr {n : Nat} {Γ : Ctx Head n} {s t : Tm Head n} {pG cG p' q' : Head}
    (equal : Equal S.R Γ s t (famCode [pG] cG)) (domain : S.R.cumulative p' pG) (codomain : S.R.cumulative cG q')
    (formedPi : IsType S.R Γ (famCode [p'] q')) :
    Equal S.R Γ (etaExp 1 s) (etaExp 1 t) (famCode [p'] q') := by
  obtain ⟨u, hu, tPi⟩ := formedPi
  have weak := equal.rename (CtxRen.wk Γ (.head p'))
  rw [famCode_rename] at weak
  have argument : Equal S.R (.snoc Γ (.head p')) (.var 0) (.var 0) (.head pG) :=
    .refl (Derivable.cumul (var_head_typed Γ p') domain)
  have applied := Derivable.appCong weak argument
  have body : Equal S.R (.snoc Γ (.head p')) (.app (Presentation.rename wk s) (.var 0))
      (.app (Presentation.rename wk t) (.var 0)) (.head q') := .subEq applied (.subUniv codomain)
  exact Derivable.lamCong tPi hu body

/-! ## Re-reading a side -/

variable [DecidableEq Head] [DecidableRel S.R.cumulative]

/-- The conditions under which a side `λ y. G y` at `Π (y : U_{p'}). U_{q'}` is re-read as `λ y. F y`. -/
def Rereads {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FitsView e) (side : TotalTerm Θ)
    (p' q' : Head) : Prop :=
  side.1.code = famCode [p'] q' ∧ side.2.code = etaExp 1 (.var v.G) ∧ S.R.cumulative p' v.pG ∧
    S.R.cumulative v.cG q'

instance {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FitsView e) (side : TotalTerm Θ) (p' q' : Head) :
    Decidable (Rereads v side p' q') := by
  unfold Rereads
  infer_instance

variable (algebra : CumulativeAlgebra S.R)

/-- The re-read side: `λ y. F y`, typed at the side's annotation. -/
def rereadTerm {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FitsView e) (side : TotalTerm Θ)
    {p' q' : Head} (h : Rereads v side p' q') : Term Θ side.1 :=
  ⟨etaExp 1 (.var v.F), by
    rw [h.1]
    have tF : Typed S.R Θ.raw (.var v.F) (famCode [v.pF] v.cF) := by
      have typed := Derivable.var (R := S.R) (Γ := Θ.raw) v.F
      rw [v.declared_F] at typed
      exact typed
    have formed : IsType S.R Θ.raw (famCode [p'] q') := h.1 ▸ side.1.isType
    exact (raised_typed tF formed (algebra.trans h.2.2.1 v.domain_F)
      (algebra.trans v.codomain_F h.2.2.2)).2⟩

/-- The domain and codomain of a unary family annotation, read off its code. -/
def unaryCandidate {Θ : Context S.R} (side : TotalTerm Θ) : Option (Head × Head) :=
  match readFam side.1.code with
  | some ([p'], q') => some (p', q')
  | _ => none

/-- **A side after domain raising**: re-read as `λ y. F y` where it is `λ y. G y` at a fitting annotation, and
instantiated otherwise. -/
def contractSide {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FitsView e) (all : AllFamilies Θ)
    (side : TotalTerm Θ) : TotalTerm Θ :=
  match unaryCandidate side with
  | some (p', q') =>
      if h : Rereads v side p' q' then ⟨side.1, rereadTerm algebra v side h⟩ else side.reindex (raise Θ all v)
  | none => side.reindex (raise Θ all v)

/-- The residual store of domain raising. -/
def contractStore {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FitsView e) (all : AllFamilies Θ)
    (rest : EquationStore (TotalTerm Θ)) : EquationStore (TotalTerm Θ) :=
  rest.map fun e' => (contractSide algebra v all e'.1, contractSide algebra v all e'.2)

/-- Either a side is re-read, or it is instantiated. -/
theorem contractSide_cases {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FitsView e) (all : AllFamilies Θ)
    (side : TotalTerm Θ) :
    (∃ p' q' h, contractSide algebra v all side = ⟨side.1, rereadTerm algebra v side (p' := p') (q' := q') h⟩) ∨
      contractSide algebra v all side = side.reindex (raise Θ all v) := by
  unfold contractSide
  cases hc : unaryCandidate side with
  | none => exact .inr rfl
  | some pq =>
      cases pq with
      | mk p' q' =>
          by_cases h : Rereads v side p' q'
          · exact .inl ⟨p', q', h, dif_pos h⟩
          · exact .inr (dif_neg h)

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (rigid : ∀ name, S.roles name = .rigid) (complete : AlgorithmicComplete S.R S.roles)

include facts algebra in
/-- **The re-read side agrees with the instantiated side for the residual solutions.** -/
theorem contract_sound {Θ Δ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FitsView e) (all : AllFamilies Θ)
    (side : TotalTerm Θ) (g : Δ ⟶ Θ) :
    (frames S.levels).E ((contractSide algebra v all side).reindex g) (side.reindex (g ≫ raise Θ all v)) := by
  have _ := facts
  rcases contractSide_cases algebra v all side with ⟨p', q', h, same⟩ | same
  · rw [same]
    have isPq : IsType S.R Δ.raw (famCode [p'] q') := by
      have formed := (side.1.reindex g).isType
      change IsType S.R Δ.raw (Presentation.subst g.substitution side.1.code) at formed
      rw [h.1, famCode_subst] at formed
      exact formed
    have tF : Typed S.R Δ.raw (g.substitution v.F) (famCode [v.pF] v.cF) := by
      have typed := g.typed v.F
      rw [v.declared_F, famCode_subst] at typed
      exact typed
    have tEta := (raised_typed tF isPq (algebra.trans h.2.2.1 v.domain_F) (algebra.trans v.codomain_F h.2.2.2)).2
    refine (equivalent_iff S.levels _ _).mpr ⟨?_, ?_⟩
    · change TypeEq S.R Δ.raw (Presentation.subst g.substitution side.1.code)
        (Presentation.subst (subComp g.substitution (raiseSub v.F v.G)) side.1.code)
      rw [h.1, famCode_subst, famCode_subst]
      exact isPq.refl
    · change Equal S.R Δ.raw (Presentation.subst g.substitution (etaExp 1 (.var v.F)))
        (Presentation.subst (subComp g.substitution (raiseSub v.F v.G)) side.2.code)
        (Presentation.subst g.substitution side.1.code)
      rw [h.2.1, h.1, famCode_subst, subst_etaExp, subst_etaExp]
      change Equal S.R Δ.raw (etaExp 1 (g.substitution v.F))
        (etaExp 1 (Presentation.subst g.substitution (raiseSub v.F v.G v.G))) (famCode [p'] q')
      rw [raiseSub_self, subst_etaExp]
      exact .symm (etaExp_equal [p'] Δ.formed tEta)
  · rw [same, ← ContextualDependentEta.reindex_comp]
    exact ((frames S.levels).equivalence Δ).refl _

include facts roots heads algebra rigid complete in
/-- **The re-read side agrees with the side itself for every original solution.** -/
theorem contract_complete {Θ Δ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FitsView e) (all : AllFamilies Θ)
    (side : TotalTerm Θ) (f : Δ ⟶ Θ) (solved : (frames S.levels).Solves f e)
    (same : homTypedEquality S.R f (f ≫ raise Θ all v)) :
    (frames S.levels).E ((contractSide algebra v all side).reindex f) (side.reindex f) := by
  rcases contractSide_cases algebra v all side with ⟨p', q', h, isSame⟩ | isSame
  · rw [isSame]
    have isPq : IsType S.R Δ.raw (famCode [p'] q') := by
      have formed := (side.1.reindex f).isType
      change IsType S.R Δ.raw (Presentation.subst f.substitution side.1.code) at formed
      rw [h.1, famCode_subst] at formed
      exact formed
    have tF : Typed S.R Δ.raw (f.substitution v.F) (famCode [v.pF] v.cF) := by
      have typed := f.typed v.F
      rw [v.declared_F, famCode_subst] at typed
      exact typed
    have tEta := (raised_typed tF isPq (algebra.trans h.2.2.1 v.domain_F) (algebra.trans v.codomain_F h.2.2.2)).2
    have key := raise_forced facts roots heads algebra rigid complete v f solved
    have congr := etaExp_congr key h.2.2.1 h.2.2.2 isPq
    refine (equivalent_iff S.levels _ _).mpr ⟨?_, ?_⟩
    · change TypeEq S.R Δ.raw (Presentation.subst f.substitution side.1.code)
        (Presentation.subst f.substitution side.1.code)
      exact (side.1.reindex f).isType.refl
    · change Equal S.R Δ.raw (Presentation.subst f.substitution (etaExp 1 (.var v.F)))
        (Presentation.subst f.substitution side.2.code) (Presentation.subst f.substitution side.1.code)
      rw [h.2.1, h.1, famCode_subst, subst_etaExp, subst_etaExp]
      exact .trans (.symm (etaExp_equal [p'] Δ.formed tEta)) (.symm congr)
  · rw [isSame, ← ContextualDependentEta.reindex_comp]
    exact ((frames S.levels).equivalence Δ).symm (act_equal_of_substEq S.levels same side)

/-! ## The rule on a whole store -/

omit [DecidableEq Head] [DecidableRel S.R.cumulative] in
include facts algebra in
/-- The solved equation holds after domain raising, for every residual solution. -/
theorem raise_head_solved {Θ Δ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FitsView e)
    (all : AllFamilies Θ) (g : Δ ⟶ Θ) : (frames S.levels).Solves (g ≫ raise Θ all v) e := by
  have _ := facts
  have isPq : IsType S.R Δ.raw (famCode [v.p] v.q) := by
    have formed := (e.1.1.reindex (g ≫ raise Θ all v)).isType
    change IsType S.R Δ.raw (Presentation.subst (subComp g.substitution (raiseSub v.F v.G)) e.1.1.code)
      at formed
    rw [v.annotation_left, famCode_subst] at formed
    exact formed
  have tF : Typed S.R Δ.raw (g.substitution v.F) (famCode [v.pF] v.cF) := by
    have typed := g.typed v.F
    rw [v.declared_F, famCode_subst] at typed
    exact typed
  have tEta := (raised_typed tF isPq (algebra.trans v.domain_G v.domain_F)
    (algebra.trans v.codomain_F v.codomain_G)).2
  refine (equivalent_iff S.levels _ _).mpr ⟨?_, ?_⟩
  · change TypeEq S.R Δ.raw (Presentation.subst (subComp g.substitution (raiseSub v.F v.G)) e.1.1.code)
      (Presentation.subst (subComp g.substitution (raiseSub v.F v.G)) e.2.1.code)
    rw [v.annotation_left, v.annotation_right, famCode_subst]
    exact isPq.refl
  · change Equal S.R Δ.raw (Presentation.subst (subComp g.substitution (raiseSub v.F v.G)) e.1.2.code)
      (Presentation.subst (subComp g.substitution (raiseSub v.F v.G)) e.2.2.code)
      (Presentation.subst (subComp g.substitution (raiseSub v.F v.G)) e.1.1.code)
    rw [v.side_left, v.side_right, v.annotation_left, subst_etaExp, subst_etaExp, famCode_subst]
    change Equal S.R Δ.raw (etaExp 1 (Presentation.subst g.substitution (raiseSub v.F v.G v.G)))
      (etaExp 1 (Presentation.subst g.substitution (raiseSub v.F v.G v.F))) (famCode [v.p] v.q)
    rw [raiseSub_self, raiseSub_ne _ _ v.distinct, subst_etaExp]
    exact etaExp_equal [v.p] Δ.formed tEta

/-- **Domain raising on a whole store**: `G := λ x. F x`; the solved equation is removed and the other sides are
re-read. -/
def raiseContractUpdate {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FitsView e) (all : AllFamilies Θ)
    (rest : EquationStore (TotalTerm Θ)) : Update S.levels (e :: rest) where
  target := Θ
  answer := raise Θ all v
  remaining := contractStore algebra v all rest
  sound := by
    intro Δ g solved e' member
    rcases List.mem_cons.mp member with rfl | member
    · exact raise_head_solved algebra facts v all g
    · have contracted := solved _ (List.mem_map.mpr ⟨e', member, rfl⟩)
      exact ((frames S.levels).equivalence Δ).trans
        (((frames S.levels).equivalence Δ).symm (contract_sound algebra facts v all e'.1 g))
        (((frames S.levels).equivalence Δ).trans contracted (contract_sound algebra facts v all e'.2 g))
  complete := by
    intro Δ f solved
    have equation := solved e List.mem_cons_self
    have key := raise_forced facts roots heads algebra rigid complete v f equation
    have same : homTypedEquality S.R f (f ≫ raise Θ all v) := by
      refine ⟨f.typed, fun i => ?_⟩
      change Equal S.R Δ.raw (f.substitution i) (Presentation.subst f.substitution (raiseSub v.F v.G i))
        (Presentation.subst f.substitution (Ctx.lookup Θ.raw i))
      by_cases h : i = v.G
      · rw [h, raiseSub_self, v.declared_G, famCode_subst, subst_etaExp]
        exact key
      · rw [raiseSub_ne _ _ h]
        exact .refl (f.typed i)
    refine ⟨f, ?_, act_equal_of_substEq S.levels same⟩
    intro e'' member
    obtain ⟨e', inRest, rfl⟩ := List.mem_map.mp member
    have held := solved e' (List.mem_cons_of_mem _ inRest)
    exact ((frames S.levels).equivalence Δ).trans
      (contract_complete algebra facts roots heads rigid complete v all e'.1 f equation same)
      (((frames S.levels).equivalence Δ).trans held
        (((frames S.levels).equivalence Δ).symm
          (contract_complete algebra facts roots heads rigid complete v all e'.2 f equation same)))

include facts roots heads algebra rigid complete in
/-- **Domain raising on a whole store is exact.** -/
theorem raiseContract_exact {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FitsView e) (all : AllFamilies Θ)
    (rest : EquationStore (TotalTerm Θ)) :
    Exact (frames S.levels) (e :: rest) (raise Θ all v) (contractStore algebra v all rest) :=
  (DependentFibre.exact_iff_update (levels := S.levels) _ _).mpr
    ⟨raiseContractUpdate algebra facts roots heads rigid complete v all rest, rfl, rfl, rfl⟩

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
