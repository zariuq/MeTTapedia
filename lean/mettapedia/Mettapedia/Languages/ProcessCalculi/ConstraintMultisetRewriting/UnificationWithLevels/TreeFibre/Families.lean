import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.PostponingFragments
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentUniverseInjective

/-!
# Universe families in the tree's own fibre: codes, η-long sides, and exact rules

The fibre is the tree's (`ContextualDependentEta.frames`): typed telescopes, typed terms up to typed βη-equality
with cumulative subtyping, typed context morphisms. Its unknowns are the declarations of a telescope, and a
solution is a typed context morphism into any later telescope.

* **A universe family** (`famCode ps c`) is the closed code `Π (x₁ : U_{p₁}) … (x_k : U_{p_k}). U_c`: a type
  family over universes, valued in the universe `U_c`. It reads the same at every arity (`famCode_rename`,
  `famCode_subst`).
* **An η-long unknown** (`etaExp k (var F)`) is `λ x₁ … x_k. F x₁ … x_k`, the Miller pattern of `F` at all its
  locals in order. It is typed-equal to `F` at every family it is typed at (`etaExp_equal`).
* **A flex-flex equation of families** (`FlexFlex`): `λ x̄. F x̄ ≐ λ x̄. G x̄`, both sides annotated at one family
  `Π x̄ : U_{p̄}. U_q`, with `F` and `G` declared at families over the same domains `p̄`.

Two rules act on such an equation, each an `Update` of the tree's driver, hence exact (`exact_iff_update`):

* **delete** (`deleteUpdate`, `delete_exact`): when `F` and `G` are the same unknown;
* **inversion** (`invertUpdate`, `invert_exact`): when `F`'s codomain lies below `G`'s, the answer `G := F`. It is
  the pattern inversion of `G x̄ ≐ F x̄` at the identity renaming, written η-short. It is typed because the
  tree's subtyping takes a family to a family over the same domains with a larger codomain (`Lowers.usable`).
  It loses no solution: every solution sends `G` to a value equal to its value of `F` at `G`'s own declaration
  (`flex_values_equal`), because two values of the smaller family equal at the annotation are equal at it
  (`Lowers.equal_iff`).

No rule here reads a level valuation. The only comparison is `S.R.cumulative` between two codomain heads; in the
tower it is the order of level expressions **under every valuation**, so it is an entailment, not a reading of
one valuation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentUniverseInjective

variable {Head L : Type} [UniverseLevel.LevelOrder L]

/-! ## Universe families -/

section Codes

/-- **A universe family**: `Π (x₁ : U_{p₁}) … (x_k : U_{p_k}). U_c`, a closed code at every arity. -/
def famCode : {n : Nat} → List Head → Head → Tm Head n
  | _, [], c => .head c
  | _, p :: ps, c => .pi (.head p) (famCode ps c)

@[simp] theorem famCode_nil {n : Nat} (c : Head) : (famCode [] c : Tm Head n) = .head c := rfl

@[simp] theorem famCode_cons {n : Nat} (p : Head) (ps : List Head) (c : Head) :
    (famCode (p :: ps) c : Tm Head n) = .pi (.head p) (famCode ps c) := rfl

/-- A family is closed: renaming leaves it unchanged. -/
theorem famCode_rename (ps : List Head) (c : Head) :
    ∀ {n m : Nat} (ρ : Ren n m), Presentation.rename ρ (famCode ps c : Tm Head n) = famCode ps c := by
  induction ps with
  | nil => intro n m ρ; rfl
  | cons p ps ih => intro n m ρ; simp only [famCode_cons, Presentation.rename, ih]

/-- A family is closed: substitution leaves it unchanged. -/
theorem famCode_subst (ps : List Head) (c : Head) :
    ∀ {n m : Nat} (σ : Sub Head n m), Presentation.subst σ (famCode ps c : Tm Head n) = famCode ps c := by
  induction ps with
  | nil => intro n m σ; rfl
  | cons p ps ih => intro n m σ; simp only [famCode_cons, Presentation.subst, ih]

/-- The code of a family determines its domains and its codomain. -/
theorem famCode_inj {ps : List Head} :
    ∀ {ps' : List Head} {c c' : Head} {n : Nat}, (famCode ps c : Tm Head n) = famCode ps' c' → ps = ps' ∧ c = c' := by
  induction ps with
  | nil =>
      intro ps' c c' n h
      cases ps' with
      | nil => exact ⟨rfl, Tm.head.inj h⟩
      | cons p' ps' => cases h
  | cons p ps ih =>
      intro ps' c c' n h
      cases ps' with
      | nil => cases h
      | cons p' ps' =>
          obtain ⟨hA, hB⟩ := Tm.pi.inj h
          obtain ⟨rfl, rfl⟩ := ih hB
          exact ⟨by rw [Tm.head.inj hA], rfl⟩

/-- **The η-expansion of a term at `k` locals**: `λ x₁ … x_k. t x₁ … x_k`. -/
def etaExp : {n : Nat} → Nat → Tm Head n → Tm Head n
  | _, 0, t => t
  | _, k + 1, t => .lam (etaExp k (.app (Presentation.rename wk t) (.var 0)))

/-- Substitution commutes with η-expansion. -/
theorem subst_etaExp : ∀ (k : Nat) {n m : Nat} (σ : Sub Head n m) (t : Tm Head n),
    Presentation.subst σ (etaExp k t) = etaExp k (Presentation.subst σ t)
  | 0, _, _, _, _ => rfl
  | k + 1, _, _, σ, t => by
      simp only [etaExp, Presentation.subst]
      rw [subst_etaExp k (liftSub σ)]
      simp only [Presentation.subst, subst_liftSub_wk, liftSub_zero]

/-- Renaming by `wk` is injective. -/
theorem rename_wk_inj {n : Nat} {t t' : Tm Head n} (same : Presentation.rename wk t = Presentation.rename wk t') :
    t = t' := by
  have exact := ContextualDependentInversion.lookup_exact (wk : Ren n (n + 1)) (Fin.succ_injective n)
  have first := ContextualDependentInversion.invert_rename t wk _ exact
  rw [same, ContextualDependentInversion.invert_rename t' wk _ exact] at first
  exact (Option.some.inj first).symm

/-- η-expansion at `k` locals is injective. -/
theorem etaExp_inj : ∀ (k : Nat) {n : Nat} {t t' : Tm Head n}, etaExp k t = etaExp k t' → t = t'
  | 0, _, _, _, h => h
  | k + 1, _, t, t', h => by
      have inner := etaExp_inj k (Tm.lam.inj h)
      exact rename_wk_inj (Tm.app.inj inner).1

end Codes

/-! ## Typing -/

section Typing

variable {S : Setting Head L}

/-- **`small` lies below `large` at the end of a family.** -/
theorem lowers_famCode (ps : List Head) {c c' : Head} (hc : S.R.isUniverse c) (hc' : S.R.isUniverse c')
    (below : S.R.cumulative c c') : ∀ {n : Nat}, Lowers S.R (famCode ps c : Tm Head n) (famCode ps c') := by
  induction ps with
  | nil => intro n; exact .sort hc hc' below
  | cons p ps ih => intro n; exact .pi ih

/-- **An η-long unknown is its unknown**: at a family, the η-expansion at all its locals is typed-equal to the
term. -/
theorem etaExp_equal {c : Head} : ∀ (ps : List Head) {n : Nat} {Γ : Ctx Head n} {t : Tm Head n},
    CtxFormed S.R Γ → Typed S.R Γ t (famCode ps c) → Equal S.R Γ (etaExp ps.length t) t (famCode ps c)
  | [], _, _, _, _, typed => .refl typed
  | p :: ps, _, Γ, t, formed, typed => by
      obtain ⟨u, hu, tPi⟩ := Typed.isType typed formed
      have generation : GenerationAt S.R _ (.pi _ _) (.head u) := Typed.generation tPi
      obtain ⟨u₁, _, _, tA, hu₁, _, _, _, _⟩ := generation
      have formed' : CtxFormed S.R (.snoc Γ (.head p)) := formed.snoc ⟨u₁, hu₁, tA⟩
      have applied : Typed S.R (.snoc Γ (.head p)) (.app (Presentation.rename wk t) (.var 0)) (famCode ps c) := by
        have weak := typed.rename (CtxRen.wk Γ (.head p))
        rw [famCode_rename] at weak
        have step := Derivable.appElim weak (Derivable.var (R := S.R) (Γ := .snoc Γ (.head p)) 0)
        simpa only [famCode_cons, Ctx.lookup, Presentation.rename, Fin.cases_zero, inst0, famCode_subst]
          using step
      have inner := etaExp_equal ps formed' applied
      have tBody : Typed S.R (.snoc Γ (.head p)) (etaExp ps.length (.app (Presentation.rename wk t) (.var 0)))
          (famCode ps c) := (Equal.typed inner formed').1
      have tLam : Typed S.R Γ (.lam (etaExp ps.length (.app (Presentation.rename wk t) (.var 0))))
          (.pi (.head p) (famCode ps c)) := Derivable.lamIntro tPi hu tBody
      have beta : Equal S.R (.snoc Γ (.head p))
          (.app (Presentation.rename wk (.lam (etaExp ps.length (.app (Presentation.rename wk t) (.var 0)))))
            (.var 0))
          (etaExp ps.length (.app (Presentation.rename wk t) (.var 0))) (famCode ps c) := by
        have step := Derivable.betaPi (tPi.rename (CtxRen.wk Γ (.head p))) hu
          (tBody.rename ((CtxRen.wk Γ (.head p)).snoc (.head p)))
          (Derivable.var (R := S.R) (Γ := .snoc Γ (.head p)) 0)
        simpa only [Presentation.rename, Ctx.lookup, Products.fresh_instantiation] using step
      have eta := Derivable.etaPi tLam typed (.trans beta inner)
      simpa only [etaExp, List.length_cons, famCode_cons] using eta

end Typing

/-! ## Flex-flex equations of families -/

section Equations

variable {S : Setting Head L}

/-- Every declaration of the telescope is a universe family. -/
def AllFamilies (Θ : Context S.R) : Prop :=
  ∀ i : Fin Θ.arity, ∃ (ps : List Head) (c : Head), Ctx.lookup Θ.raw i = famCode ps c

/-- **A flex-flex equation of families**: `λ x̄. F x̄ ≐ λ x̄. G x̄`, both sides annotated at the family
`Π x̄ : U_{p̄}. U_q`, with `F : Π x̄ : U_{p̄}. U_{cl}` and `G : Π x̄ : U_{p̄}. U_{cr}`, both codomains below `q`. -/
structure FlexFlex {Θ : Context S.R} (e : Equation (TotalTerm Θ)) where
  ps : List Head
  q : Head
  left : Fin Θ.arity
  right : Fin Θ.arity
  cl : Head
  cr : Head
  annotation_left : e.1.1.code = famCode ps q
  annotation_right : e.2.1.code = famCode ps q
  side_left : e.1.2.code = etaExp ps.length (.var left)
  side_right : e.2.2.code = etaExp ps.length (.var right)
  declared_left : Ctx.lookup Θ.raw left = famCode ps cl
  declared_right : Ctx.lookup Θ.raw right = famCode ps cr
  universe_q : S.R.isUniverse q
  universe_left : S.R.isUniverse cl
  universe_right : S.R.isUniverse cr
  below_left : S.R.cumulative cl q
  below_right : S.R.cumulative cr q

/-- Two total terms with the same codes are equal in the frame. -/
theorem e_of_codes {Γ : Context S.R} {X Y : TotalTerm Γ} (sameType : X.1.code = Y.1.code)
    (sameTerm : X.2.code = Y.2.code) : (frames S.levels).E X Y := by
  refine (equivalent_iff S.levels X Y).mpr ⟨?_, ?_⟩
  · rw [← sameType]
    exact X.1.isType.refl
  · rw [← sameTerm]
    exact .refl X.2.typed

/-- **An equation between one unknown is solved by every morphism.** -/
theorem solves_same {Θ Δ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexFlex e) (same : v.left = v.right)
    (f : Δ ⟶ Θ) : (frames S.levels).Solves f e := by
  apply e_of_codes
  · change Presentation.subst f.substitution e.1.1.code = Presentation.subst f.substitution e.2.1.code
    rw [v.annotation_left, v.annotation_right]
  · change Presentation.subst f.substitution e.1.2.code = Presentation.subst f.substitution e.2.2.code
    rw [v.side_left, v.side_right, same]

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

include facts roots heads algebra rigid complete in
/-- **What a flex-flex equation forces**: every solution sends the unknown with the larger codomain to a value
equal, at its own declaration, to its value of the other unknown. -/
theorem flex_values_equal {Θ Δ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexFlex e) (f : Δ ⟶ Θ)
    (solved : (frames S.levels).Solves f e) (below : S.R.cumulative v.cl v.cr) :
    Equal S.R Δ.raw (f.substitution v.right) (f.substitution v.left) (famCode v.ps v.cr) := by
  have equal := ((equivalent_iff S.levels _ _).mp solved).2
  change Equal S.R Δ.raw (Presentation.subst f.substitution e.1.2.code)
    (Presentation.subst f.substitution e.2.2.code) (Presentation.subst f.substitution e.1.1.code) at equal
  rw [v.side_left, v.side_right, v.annotation_left, subst_etaExp, subst_etaExp, famCode_subst] at equal
  change Equal S.R Δ.raw (etaExp v.ps.length (f.substitution v.left)) (etaExp v.ps.length (f.substitution v.right))
    (famCode v.ps v.q) at equal
  have tL : Typed S.R Δ.raw (f.substitution v.left) (famCode v.ps v.cl) := by
    have typed := f.typed v.left
    rw [v.declared_left, famCode_subst] at typed
    exact typed
  have tR : Typed S.R Δ.raw (f.substitution v.right) (famCode v.ps v.cr) := by
    have typed := f.typed v.right
    rw [v.declared_right, famCode_subst] at typed
    exact typed
  have isL : IsType S.R Δ.raw (famCode v.ps v.cl) := Typed.isType tL Δ.formed
  have isR : IsType S.R Δ.raw (famCode v.ps v.cr) := Typed.isType tR Δ.formed
  have isQ : IsType S.R Δ.raw (famCode v.ps v.q) := by
    have formed := (e.1.1.reindex f).isType
    change IsType S.R Δ.raw (Presentation.subst f.substitution e.1.1.code) at formed
    rw [v.annotation_left, famCode_subst] at formed
    exact formed
  have tLq : Typed S.R Δ.raw (f.substitution v.left) (famCode v.ps v.q) :=
    .sub tL ((lowers_famCode v.ps v.universe_left v.universe_q v.below_left).usable isL isQ)
  have tRq : Typed S.R Δ.raw (f.substitution v.right) (famCode v.ps v.q) :=
    .sub tR ((lowers_famCode v.ps v.universe_right v.universe_q v.below_right).usable isR isQ)
  have etaL := etaExp_equal v.ps Δ.formed tLq
  have etaR := etaExp_equal v.ps Δ.formed tRq
  have large : Equal S.R Δ.raw (f.substitution v.right) (f.substitution v.left) (famCode v.ps v.q) :=
    .trans (.symm etaR) (.trans (.symm equal) etaL)
  have tLr : Typed S.R Δ.raw (f.substitution v.left) (famCode v.ps v.cr) :=
    .sub tL ((lowers_famCode v.ps v.universe_left v.universe_right below).usable isL isR)
  exact ((lowers_famCode v.ps v.universe_right v.universe_q v.below_right).equal_iff facts roots heads algebra
    rigid complete Δ.formed isR isQ tR tLr).mp large

/-! ## The answers -/

/-- `G := F`, the identity elsewhere, on codes. -/
def assignSub {n : Nat} (F G : Fin n) : Sub Head n n := fun i => if i = G then .var F else .var i

theorem assignSub_left {n : Nat} (F G : Fin n) : assignSub (Head := Head) F G F = .var F := by
  unfold assignSub
  split_ifs with h
  · rfl
  · rfl

theorem assignSub_right {n : Nat} (F G : Fin n) : assignSub (Head := Head) F G G = .var F := by
  unfold assignSub
  rw [if_pos rfl]

/-- **The answer `G := F`** as a typed endomorphism of a telescope of families, where `F`'s codomain lies below
`G`'s and both are families over the same domains. `G` stays declared and is no longer used. -/
def assign (Θ : Context S.R) (all : AllFamilies Θ) {F G : Fin Θ.arity} {ps : List Head} {cF cG : Head}
    (declF : Ctx.lookup Θ.raw F = famCode ps cF) (declG : Ctx.lookup Θ.raw G = famCode ps cG)
    (hF : S.R.isUniverse cF) (hG : S.R.isUniverse cG) (below : S.R.cumulative cF cG) : Θ ⟶ Θ where
  substitution := assignSub F G
  typed := by
    intro i
    obtain ⟨psi, ci, hi⟩ := all i
    rw [hi, famCode_subst]
    by_cases h : i = G
    · subst h
      have sameDecl : (famCode psi ci : Tm Head Θ.arity) = famCode ps cG := hi.symm.trans declG
      rw [assignSub_right, sameDecl]
      have tF : Typed S.R Θ.raw (.var F) (famCode ps cF) := by
        have typed := Derivable.var (R := S.R) (Γ := Θ.raw) F
        rw [declF] at typed
        exact typed
      have isF : IsType S.R Θ.raw (famCode ps cF) := declF ▸ Θ.formed.lookup F
      have isG : IsType S.R Θ.raw (famCode ps cG) := declG ▸ Θ.formed.lookup i
      exact .sub tF ((lowers_famCode ps hF hG below).usable isF isG)
    · have typed := Derivable.var (R := S.R) (Γ := Θ.raw) i
      rw [hi] at typed
      unfold assignSub
      rw [if_neg h]
      exact typed

/-! ## The rules -/

/-- **Delete**: an equation between one unknown is removed; the answer is the identity. -/
def deleteUpdate {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexFlex e) (same : v.left = v.right)
    (rest : EquationStore (TotalTerm Θ)) : Update S.levels (e :: rest) where
  target := Θ
  answer := 𝟙 Θ
  remaining := rest
  sound := by
    intro Δ residual solved
    rw [Category.comp_id]
    intro e' member
    rcases List.mem_cons.mp member with rfl | member
    · exact solves_same v same residual
    · exact solved e' member
  complete := by
    intro Δ solution solved
    refine ⟨solution, fun e' member => solved e' (List.mem_cons_of_mem _ member), fun term => ?_⟩
    rw [Category.comp_id]
    exact ((frames S.levels).equivalence Δ).refl _

/-- **Inversion**: `G := F`, where `F`'s codomain lies below `G`'s. The solved equation is removed and the rest
of the store is instantiated. -/
def invertUpdate {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexFlex e) (all : AllFamilies Θ)
    (below : S.R.cumulative v.cl v.cr) (rest : EquationStore (TotalTerm Θ)) : Update S.levels (e :: rest) where
  target := Θ
  answer := assign Θ all v.declared_left v.declared_right v.universe_left v.universe_right below
  remaining := (frames S.levels).applyStore
    (assign Θ all v.declared_left v.declared_right v.universe_left v.universe_right below) rest
  sound := by
    intro Δ g solved e' member
    rcases List.mem_cons.mp member with rfl | member
    · apply e_of_codes
      · change Presentation.subst (subComp g.substitution (assignSub v.left v.right)) e'.1.1.code =
          Presentation.subst (subComp g.substitution (assignSub v.left v.right)) e'.2.1.code
        rw [v.annotation_left, v.annotation_right]
      · change Presentation.subst (subComp g.substitution (assignSub v.left v.right)) e'.1.2.code =
          Presentation.subst (subComp g.substitution (assignSub v.left v.right)) e'.2.2.code
        rw [v.side_left, v.side_right, subst_etaExp, subst_etaExp]
        simp only [Presentation.subst, subComp, assignSub_left, assignSub_right]
    · exact (Frames.models_applyStore (X := frames S.levels) _ g rest).mp solved e' member
  complete := by
    intro Δ f solved
    have equation := solved e List.mem_cons_self
    have key := flex_values_equal facts roots heads algebra rigid complete v f equation below
    have same : homTypedEquality S.R f
        (f ≫ assign Θ all v.declared_left v.declared_right v.universe_left v.universe_right below) := by
      refine ⟨f.typed, fun i => ?_⟩
      change Equal S.R Δ.raw (f.substitution i)
        (Presentation.subst f.substitution (assignSub v.left v.right i))
        (Presentation.subst f.substitution (Ctx.lookup Θ.raw i))
      by_cases h : i = v.right
      · subst h
        rw [assignSub_right, v.declared_right, famCode_subst]
        exact key
      · unfold assignSub
        rw [if_neg h]
        exact .refl (f.typed i)
    refine ⟨f, ?_, act_equal_of_substEq S.levels same⟩
    apply (Frames.models_applyStore (X := frames S.levels) _ f rest).mpr
    exact (Elimination.models_pointwise S.levels (act_equal_of_substEq S.levels same) rest).mp
      (fun e' member => solved e' (List.mem_cons_of_mem _ member))

/-! ## Exactness, through the driver's updates -/

/-- **Delete is exact.** -/
theorem delete_exact {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexFlex e) (same : v.left = v.right)
    (rest : EquationStore (TotalTerm Θ)) : Exact (frames S.levels) (e :: rest) (𝟙 Θ) rest :=
  (DependentFibre.exact_iff_update (levels := S.levels) (𝟙 Θ) rest).mpr ⟨deleteUpdate v same rest, rfl, rfl, rfl⟩

include facts roots heads algebra rigid complete in
/-- **Inversion is exact.** -/
theorem invert_exact {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexFlex e) (all : AllFamilies Θ)
    (below : S.R.cumulative v.cl v.cr) (rest : EquationStore (TotalTerm Θ)) :
    Exact (frames S.levels) (e :: rest)
      (assign Θ all v.declared_left v.declared_right v.universe_left v.universe_right below)
      ((frames S.levels).applyStore
        (assign Θ all v.declared_left v.declared_right v.universe_left v.universe_right below) rest) :=
  (DependentFibre.exact_iff_update (levels := S.levels) _ _).mpr
    ⟨invertUpdate facts roots heads algebra rigid complete v all below rest, rfl, rfl, rfl⟩

end Equations

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
