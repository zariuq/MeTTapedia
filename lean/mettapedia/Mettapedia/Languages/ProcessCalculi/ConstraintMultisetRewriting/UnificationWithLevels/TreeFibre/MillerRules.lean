import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MillerReading

/-!
# The Miller rules as exact updates of the tree's driver

Every rule of the Miller solver gives one unknown `X : Π (x̄ : U_{p̄}). U_c` the answer `X := λ x̄. val`:

* **solve**: `val = F x_σ` for another unknown `F` (inversion of a permutation pattern);
* **project**: `val = x_j` (a flex side against a rigid local);
* **prune** and **intersect**: `val = X' x_K`, where `X` is **declared again in place** at the family of the kept
  binders `K` (a fresh unknown of smaller arity in `X`'s slot).

The target telescope is `redecl Θ X ps' c'`: `Θ` with `X` declared at `Π (x̄ : U_{ps'}). U_{c'}` (for solve and project
`X`'s own family, so `X` is no longer used). The answer is a typed morphism (`answerHom`).

**Exactness.** An update built from an answer is exact as soon as every solution of the store factors through the
answer up to typed equality (`replaceUpdate`). Its residual store is the store instantiated by the answer and then
**re-read**: each Miller side of `X`, instantiated, is a β-redex `λ ȳ. (λ x̄. val) y_a`, and is replaced by the equal
code `λ ȳ. val[x̄ := y_a]` (`reread_equal`, by the tree's typed β along the spine). The re-read store has the same
solutions as the instantiated one (`rereadStore_models`).

**Factoring** (`factor_of_opened`): a solution factors through the answer when its value of `X`, opened, equals
`val` instantiated by the residual, at any universe above `X`'s codomain. The equality at the family follows by
opening, η, and the reflection of equalities from a larger family to a smaller one (the tree's `Lowers.equal_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

namespace Miller

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentUniverseInjective

variable {Head L : Type} [UniverseLevel.LevelOrder L]

/-! ## Telescopes of families -/

section Telescopes

variable {S : Setting Head L}

/-- **Every declaration is a family over universes valued in a universe.** -/
def Families (Θ : Context S.R) : Prop :=
  ∀ i : Fin Θ.arity, ∃ (ps : List Head) (c : Head), Ctx.lookup Θ.raw i = famCode ps c ∧ AllUniverses S.R ps ∧
    S.R.isUniverse c

/-- **The declared codomains form a chain.** -/
def Chain (Θ : Context S.R) : Prop :=
  ∀ (i j : Fin Θ.arity) (ps ps' : List Head) (c c' : Head), Ctx.lookup Θ.raw i = famCode ps c →
    Ctx.lookup Θ.raw j = famCode ps' c' → S.R.cumulative c c' ∨ S.R.cumulative c' c

theorem lookup_eq_of_snoc {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {ps : List Head} {c : Head}
    (h : Ctx.lookup (.snoc Γ A) 0 = famCode ps c) : A = famCode ps c := by
  apply rename_wk_inj
  rw [famCode_rename]
  exact h

theorem lookup_succ_eq {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {i : Fin n} {ps : List Head} {c : Head}
    (h : Ctx.lookup (.snoc Γ A) i.succ = famCode ps c) : Ctx.lookup Γ i = famCode ps c := by
  apply rename_wk_inj
  rw [famCode_rename]
  exact h

/-- A telescope of families stays formed when one family is declared again. -/
theorem setFamAt_formed_families : ∀ {n : Nat} (Γ : Ctx Head n), CtxFormed S.R Γ →
    (∀ i, ∃ (ps : List Head) (c : Head), Ctx.lookup Γ i = famCode ps c ∧ AllUniverses S.R ps ∧ S.R.isUniverse c) →
    ∀ (X : Fin n) (ps : List Head) (c : Head), AllUniverses S.R ps → S.R.isUniverse c →
      CtxFormed S.R (setFamAt Γ X ps c) := by
  intro n Γ
  induction Γ with
  | nil => intro _ _ X; exact X.elim0
  | snoc Γ A ih =>
      intro formed families X ps c universes hc
      cases formed with
      | snoc formedΓ _ =>
          have inner : ∀ i, ∃ (ps : List Head) (c : Head), Ctx.lookup Γ i = famCode ps c ∧ AllUniverses S.R ps ∧
              S.R.isUniverse c := by
            intro i
            obtain ⟨ps', c', h, u, hc'⟩ := families i.succ
            exact ⟨ps', c', lookup_succ_eq h, u, hc'⟩
          cases X using Fin.cases with
          | zero =>
              simp only [setFamAt, Fin.cases_zero]
              exact formedΓ.snoc (famCode_isType ps universes hc formedΓ)
          | succ X =>
              simp only [setFamAt, Fin.cases_succ]
              obtain ⟨ps₀, c₀, h₀, u₀, hc₀⟩ := families 0
              have hA := lookup_eq_of_snoc h₀
              have formedInner := ih formedΓ inner X ps c universes hc
              rw [hA]
              exact formedInner.snoc (famCode_isType ps₀ u₀ hc₀ formedInner)

/-- **The telescope with `X` declared again** at `Π (x̄ : U_{ps}). U_c`. -/
abbrev redecl (Θ : Context S.R) (families : Families Θ) (X : Fin Θ.arity) (ps : List Head) (c : Head)
    (universes : AllUniverses S.R ps) (hc : S.R.isUniverse c) : Context S.R where
  arity := Θ.arity
  raw := setFamAt Θ.raw X ps c
  formed := setFamAt_formed_families Θ.raw Θ.formed families X ps c universes hc

theorem redecl_self (Θ : Context S.R) (families : Families Θ) (X : Fin Θ.arity) (ps : List Head) (c : Head)
    (universes : AllUniverses S.R ps) (hc : S.R.isUniverse c) :
    Ctx.lookup (redecl Θ families X ps c universes hc).raw X = famCode ps c :=
  lookup_setFamAt_self Θ.raw X ps c

theorem redecl_ne (Θ : Context S.R) (families : Families Θ) (X : Fin Θ.arity) (ps : List Head) (c : Head)
    (universes : AllUniverses S.R ps) (hc : S.R.isUniverse c) {i : Fin Θ.arity} (ne : i ≠ X) :
    Ctx.lookup (redecl Θ families X ps c universes hc).raw i = Ctx.lookup Θ.raw i :=
  lookup_setFamAt_ne Θ.raw X i ps c ne

theorem redecl_families (Θ : Context S.R) (families : Families Θ) (X : Fin Θ.arity) (ps : List Head) (c : Head)
    (universes : AllUniverses S.R ps) (hc : S.R.isUniverse c) :
    Families (redecl Θ families X ps c universes hc) := by
  intro i
  by_cases h : i = X
  · rw [h]
    exact ⟨ps, c, redecl_self Θ families X ps c universes hc, universes, hc⟩
  · rw [redecl_ne Θ families X ps c universes hc h]
    exact families i

/-- Declaring `X` again with its own codomain keeps the chain. -/
theorem redecl_chain (Θ : Context S.R) (families : Families Θ) (X : Fin Θ.arity) {psX : List Head} {cX : Head}
    (declared : Ctx.lookup Θ.raw X = famCode psX cX) (ps : List Head) (universes : AllUniverses S.R ps)
    (hc : S.R.isUniverse cX) (chain : Chain Θ) : Chain (redecl Θ families X ps cX universes hc) := by
  have back : ∀ (i : Fin Θ.arity) (ps' : List Head) (c' : Head),
      Ctx.lookup (redecl Θ families X ps cX universes hc).raw i = famCode ps' c' →
        ∃ ps'', Ctx.lookup Θ.raw i = famCode ps'' c' := by
    intro i ps' c' h
    by_cases hi : i = X
    · subst hi
      rw [redecl_self] at h
      obtain ⟨_, rfl⟩ := famCode_inj h
      exact ⟨psX, declared⟩
    · rw [redecl_ne Θ families X ps cX universes hc hi] at h
      exact ⟨ps', h⟩
  intro i j ps₁ ps₂ c₁ c₂ h₁ h₂
  obtain ⟨_, h₁'⟩ := back i ps₁ c₁ h₁
  obtain ⟨_, h₂'⟩ := back j ps₂ c₂ h₂
  exact chain i j _ _ c₁ c₂ h₁' h₂'

end Telescopes

/-! ## The answer -/

section Answer

variable {S : Setting Head L}

/-- `X := λ x̄. val`, the identity elsewhere. -/
def answerSub {N : Nat} (X : Fin N) (psX : List Head) (val : Tm Head (arity N psX)) : Sub Head N N :=
  fun i => if i = X then lams psX val else .var i

theorem answerSub_self {N : Nat} (X : Fin N) (psX : List Head) (val : Tm Head (arity N psX)) :
    answerSub X psX val X = lams psX val := by
  unfold answerSub
  rw [if_pos rfl]

theorem answerSub_ne {N : Nat} (X : Fin N) (psX : List Head) (val : Tm Head (arity N psX)) {i : Fin N}
    (ne : i ≠ X) : answerSub X psX val i = .var i := by
  unfold answerSub
  rw [if_neg ne]

/-- **The answer, a morphism of telescopes.** -/
def answerHom (Θ : Context S.R) (families : Families Θ) (X : Fin Θ.arity) {psX : List Head} {cX : Head}
    (declared : Ctx.lookup Θ.raw X = famCode psX cX) (universesX : AllUniverses S.R psX) (hcX : S.R.isUniverse cX)
    (ps' : List Head) (c' : Head) (universes' : AllUniverses S.R ps') (hc' : S.R.isUniverse c')
    (val : Tm Head (arity Θ.arity psX))
    (typed : Typed S.R (ctx (setFamAt Θ.raw X ps' c') psX) val (.head cX)) :
    redecl Θ families X ps' c' universes' hc' ⟶ Θ where
  substitution := answerSub X psX val
  typed := by
    intro i
    show Typed S.R (setFamAt Θ.raw X ps' c') (answerSub X psX val i)
      (Presentation.subst (answerSub X psX val) (Ctx.lookup Θ.raw i))
    obtain ⟨ps, c, hi, _, _⟩ := families i
    rw [hi, famCode_subst]
    by_cases h : i = X
    · subst h
      obtain ⟨rfl, rfl⟩ := famCode_inj (hi.symm.trans declared)
      rw [answerSub_self]
      exact lams_typed ps (redecl Θ families i ps' c' universes' hc').formed universesX hcX typed
    · rw [answerSub_ne X psX val h]
      have v := Derivable.var (R := S.R) (Γ := setFamAt Θ.raw X ps' c') i
      rw [lookup_setFamAt_ne Θ.raw X i ps' c' h, hi] at v
      exact v

end Answer

/-! ## Exactness from factoring -/

section Exactness

variable {S : Setting Head L}

/-- **An update from an answer and a re-read residual store**, exact as soon as every solution factors through the
answer. -/
def replaceUpdate {Θ Θ' : Context S.R} {problem : EquationStore (TotalTerm Θ)} (σ : Θ' ⟶ Θ)
    (remaining : EquationStore (TotalTerm Θ'))
    (rereads : ∀ {Δ : Context S.R} (g : Δ ⟶ Θ'),
      (frames S.levels).Models g remaining ↔ (frames S.levels).Models g ((frames S.levels).applyStore σ problem))
    (factor : ∀ {Δ : Context S.R} (f : Δ ⟶ Θ), (frames S.levels).Models f problem →
      ∃ g : Δ ⟶ Θ', homTypedEquality S.R f (g ≫ σ)) : Update S.levels problem where
  target := Θ'
  answer := σ
  remaining := remaining
  sound := by
    intro Δ g solved
    exact (Frames.models_applyStore (X := frames S.levels) σ g problem).mp ((rereads g).mp solved)
  complete := by
    intro Δ f solved
    obtain ⟨g, same⟩ := factor f solved
    refine ⟨g, ?_, act_equal_of_substEq S.levels same⟩
    apply (rereads g).mpr
    apply (Frames.models_applyStore (X := frames S.levels) σ g problem).mpr
    exact (Elimination.models_pointwise S.levels (act_equal_of_substEq S.levels same) problem).mp solved

theorem replace_exact {Θ Θ' : Context S.R} {problem : EquationStore (TotalTerm Θ)} (σ : Θ' ⟶ Θ)
    (remaining : EquationStore (TotalTerm Θ'))
    (rereads : ∀ {Δ : Context S.R} (g : Δ ⟶ Θ'),
      (frames S.levels).Models g remaining ↔ (frames S.levels).Models g ((frames S.levels).applyStore σ problem))
    (factor : ∀ {Δ : Context S.R} (f : Δ ⟶ Θ), (frames S.levels).Models f problem →
      ∃ g : Δ ⟶ Θ', homTypedEquality S.R f (g ≫ σ)) :
    Exact (frames S.levels) problem σ remaining :=
  (DependentFibre.exact_iff_update (levels := S.levels) σ remaining).mpr
    ⟨replaceUpdate σ remaining rereads factor, rfl, rfl, rfl⟩

/-- A substitution typed into a telescope stays typed under the binders. -/
theorem liftSubs_substMor : ∀ {n m : Nat} {Γ : Ctx Head n} {Γ' : Ctx Head m} (qs : List Head) {σ : Sub Head n m},
    SubstMor S.R Γ Γ' σ → SubstMor S.R (ctx Γ qs) (ctx Γ' qs) (liftSubs qs σ)
  | _, _, _, _, [], _, typed => typed
  | _, _, Γ, Γ', q :: qs, σ, typed => by
      have lifted : SubstMor S.R (.snoc Γ (.head q)) (.snoc Γ' (.head q)) (liftSub σ) := typed.lift (.head q)
      exact liftSubs_substMor (Γ := .snoc Γ (.head q)) (Γ' := .snoc Γ' (.head q)) qs lifted

/-- **β for the opening of an abstraction.** -/
theorem opened_lams {n : Nat} {Γ : Ctx Head n} (ps : List Head) {c : Head} {M : Tm Head (arity n ps)}
    (formed : CtxFormed S.R Γ) (universes : AllUniverses S.R ps) (hc : S.R.isUniverse c)
    (typed : Typed S.R (ctx Γ ps) M (.head c)) : Equal S.R (ctx Γ ps) (opened ps (lams ps M)) M (.head c) := by
  have tLams := lams_typed ps formed universes hc typed
  have eta := eta_opened ps formed tLams
  exact (lams_equal_iff ps formed universes hc (opened_typed ps tLams) typed).mp eta

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

include facts roots heads algebra rigid complete in
/-- **Factoring from the opened value.** A solution factors through `X := λ x̄. val` when its value of `X`, opened,
equals `val` instantiated by the residual, at a universe above `X`'s codomain, and the residual agrees with the
solution elsewhere. -/
theorem factor_of_opened {Θ Θ' Δ : Context S.R} (X : Fin Θ.arity) {psX : List Head}
    {cX d : Head} (declared : Ctx.lookup Θ.raw X = famCode psX cX) (universesX : AllUniverses S.R psX)
    (hcX : S.R.isUniverse cX) (hd : S.R.isUniverse d) (below : S.R.cumulative cX d)
    (σ : Θ' ⟶ Θ) (val : Tm Head (arity Θ'.arity psX)) (hσ : σ.substitution X = lams psX val)
    (typed : Typed S.R (ctx Θ'.raw psX) val (.head cX)) (f : Δ ⟶ Θ) (g : Δ ⟶ Θ')
    (elsewhere : ∀ i, i ≠ X → Presentation.subst g.substitution (σ.substitution i) = f.substitution i)
    (opened_equal : Equal S.R (ctx Δ.raw psX) (opened psX (f.substitution X))
      (Presentation.subst (liftSubs psX g.substitution) val) (.head d)) :
    homTypedEquality S.R f (g ≫ σ) := by
  refine ⟨f.typed, fun i => ?_⟩
  change Equal S.R Δ.raw (f.substitution i) (Presentation.subst g.substitution (σ.substitution i))
    (Presentation.subst f.substitution (Ctx.lookup Θ.raw i))
  by_cases h : i = X
  · subst h
    rw [hσ, subst_lams, declared, famCode_subst]
    have tV : Typed S.R (ctx Δ.raw psX) (Presentation.subst (liftSubs psX g.substitution) val) (.head cX) :=
      typed.substitute (liftSubs_substMor psX g.typed)
    have tF : Typed S.R Δ.raw (f.substitution i) (famCode psX cX) := by
      have t := f.typed i
      rw [declared, famCode_subst] at t
      exact t
    have tOpen := opened_typed psX tF
    have opens := (lams_equal_iff psX Δ.formed universesX hd (Derivable.cumul tOpen below)
      (Derivable.cumul tV below)).mpr opened_equal
    have isC : IsType S.R Δ.raw (famCode psX cX) := famCode_isType psX universesX hcX Δ.formed
    have isD : IsType S.R Δ.raw (famCode psX d) := famCode_isType psX universesX hd Δ.formed
    have lowers := lowers_famCode (S := S) psX hcX hd below (n := Δ.arity)
    have eta : Equal S.R Δ.raw (f.substitution i) (lams psX (opened psX (f.substitution i))) (famCode psX d) :=
      .subEq (eta_opened psX Δ.formed tF).symm (lowers.usable isC isD)
    have large := eta.trans opens
    exact (lowers.equal_iff facts roots heads algebra rigid complete Δ.formed isC isD tF
      (lams_typed psX Δ.formed universesX hcX tV)).mp large
  · rw [elsewhere i h]
    exact .refl (f.typed i)

end Exactness

/-! ## Re-reading -/

section Reread

variable {S : Setting Head L}

/-- A total term with its code replaced by an equal code. -/
def replaceCode {Γ : Context S.R} (Y : TotalTerm Γ) (code : Tm Head Γ.arity)
    (equal : Equal S.R Γ.raw Y.2.code code Y.1.code) : TotalTerm Γ :=
  ⟨Y.1, ⟨code, (Equal.typed equal Γ.formed).2⟩⟩

theorem replaceCode_E {Γ : Context S.R} (Y : TotalTerm Γ) (code : Tm Head Γ.arity)
    (equal : Equal S.R Γ.raw Y.2.code code Y.1.code) : (frames S.levels).E Y (replaceCode Y code equal) :=
  (equivalent_iff S.levels _ _).mpr ⟨Y.1.isType.refl, equal⟩

/-- **β re-reading of one Miller side of `X`.** The instantiated side `λ ȳ. (λ x̄. val) y_a` equals
`λ ȳ. val[x̄ := y_a]`. -/
theorem reread_equal {Θ Θ' : Context S.R} (σ : Θ' ⟶ Θ) (X : Fin Θ.arity) {psX : List Head} {cX : Head}
    (val : Tm Head (arity Θ'.arity psX)) (hσ : σ.substitution X = lams psX val)
    (typed : Typed S.R (ctx Θ'.raw psX) val (.head cX)) (universesX : AllUniverses S.R psX)
    (qs : List Head) {d : Head} (img : Fin psX.length → Fin qs.length) (universes : AllUniverses S.R qs)
    (hd : S.R.isUniverse d) (domains : ∀ j, psX.get j = qs.get (img j)) (below : S.R.cumulative cX d)
    (hcX : S.R.isUniverse cX) :
    Equal S.R Θ'.raw (Presentation.subst σ.substitution (flexSide qs psX X img))
      (lams qs (Presentation.rename (sideRen qs psX img) val)) (famCode qs d) := by
  rw [subst_flexSide, hσ]
  have beta := beta_apps (S := S) (Γ := Θ'.raw) (Γ' := ctx Θ'.raw qs) psX (shift qs) (fun j => loc qs (img j))
    Θ'.formed (ctx_formed qs Θ'.formed universes) universesX hcX (shift_ctxRen Θ'.raw qs)
    (fun j => by rw [lookup_loc, domains j]) typed
  have beta' := Derivable.cumulEq beta below
  obtain ⟨tl, tr⟩ := Equal.typed beta' (ctx_formed qs Θ'.formed universes)
  exact (lams_equal_iff qs Θ'.formed universes hd tl tr).mpr beta'

/-- The arguments of a side read at a binder list equal to `psX`. -/
def castImg {qs ps psX : List Head} (img : Fin ps.length → Fin qs.length) (same : ps = psX) :
    Fin psX.length → Fin qs.length :=
  fun j => img (Fin.cast (congrArg List.length same).symm j)

theorem flexSide_cast {N : Nat} {qs ps psX : List Head} (F : Fin N) (img : Fin ps.length → Fin qs.length)
    (same : ps = psX) : flexSide qs ps F img = flexSide qs psX F (castImg img same) := by
  subst same
  rfl

theorem domains_cast {qs ps psX : List Head} {img : Fin ps.length → Fin qs.length} (same : ps = psX)
    (domains : ∀ j, ps.get j = qs.get (img j)) : ∀ j, psX.get j = qs.get (castImg img same j) := by
  subst same
  exact domains

theorem injective_cast {qs ps psX : List Head} {img : Fin ps.length → Fin qs.length} (same : ps = psX)
    (injective : Function.Injective img) : Function.Injective (castImg img same) := by
  subst same
  exact injective

/-- **The data of an answer**, for re-reading. -/
structure AnswerData {Θ Θ' : Context S.R} (σ : Θ' ⟶ Θ) where
  X : Fin Θ.arity
  psX : List Head
  cX : Head
  declared : Ctx.lookup Θ.raw X = famCode psX cX
  universesX : AllUniverses S.R psX
  universe_cX : S.R.isUniverse cX
  val : Tm Head (arity Θ'.arity psX)
  typed : Typed S.R (ctx Θ'.raw psX) val (.head cX)
  answer_self : σ.substitution X = lams psX val

variable [DecidableEq Head]

/-- **Re-read one side**: a Miller side of `X` is replaced by its β-contracted instance, every other side is
instantiated. -/
def rereadSide {Θ Θ' : Context S.R} {σ : Θ' ⟶ Θ} (A : AnswerData σ) (Y : TotalTerm Θ) {qs : List Head} {d : Head}
    (annotation : Y.1.code = famCode qs d) (universes : AllUniverses S.R qs) (hd : S.R.isUniverse d)
    (view : SideView (S := S) Θ.raw qs d Y.2.code) : TotalTerm Θ' :=
  match view with
  | .flex data below =>
      if h : data.unknown = A.X ∧ data.ps = A.psX then
        replaceCode ((frames S.levels).act σ Y)
          (lams qs (Presentation.rename (sideRen qs A.psX (castImg data.img h.2)) A.val)) (by
            have hc : data.c = A.cX := by
              have decl := data.declared
              rw [h.1, A.declared] at decl
              exact (famCode_inj decl).2.symm
            have equal := reread_equal σ A.X A.val A.answer_self A.typed A.universesX qs (castImg data.img h.2)
              universes hd (domains_cast h.2 data.domains) (hc ▸ below) A.universe_cX
            have hside : Y.2.code = flexSide qs A.psX A.X (castImg data.img h.2) :=
              data.side.trans ((flexSide_cast data.unknown data.img h.2).trans
                (congrArg (fun F => flexSide qs A.psX F (castImg data.img h.2)) h.1))
            have e1 : Presentation.subst σ.substitution Y.2.code =
                Presentation.subst σ.substitution (flexSide qs A.psX A.X (castImg data.img h.2)) :=
              congrArg _ hside
            have e2 : Presentation.subst σ.substitution Y.1.code = famCode qs d := by
              rw [annotation, famCode_subst]
            change Equal S.R Θ'.raw (Presentation.subst σ.substitution Y.2.code) _
              (Presentation.subst σ.substitution Y.1.code)
            rw [e1, e2]
            exact equal)
      else (frames S.levels).act σ Y
  | .rigid _ _ _ => (frames S.levels).act σ Y

theorem rereadSide_E {Θ Θ' : Context S.R} {σ : Θ' ⟶ Θ} (A : AnswerData σ) (Y : TotalTerm Θ) {qs : List Head}
    {d : Head} (annotation : Y.1.code = famCode qs d) (universes : AllUniverses S.R qs) (hd : S.R.isUniverse d)
    (view : SideView (S := S) Θ.raw qs d Y.2.code) :
    (frames S.levels).E ((frames S.levels).act σ Y) (rereadSide A Y annotation universes hd view) := by
  unfold rereadSide
  split
  · split
    · exact replaceCode_E _ _ _
    · exact ((frames S.levels).equivalence Θ').refl _
  · exact ((frames S.levels).equivalence Θ').refl _

variable [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]

/-- Re-read one equation. -/
def rereadEq {Θ Θ' : Context S.R} {σ : Θ' ⟶ Θ} (A : AnswerData σ) (e : Equation (TotalTerm Θ)) :
    Equation (TotalTerm Θ') :=
  match readEq (S := S) e with
  | some v => (rereadSide A e.1 v.annotation_left v.universes v.universe_d v.left,
      rereadSide A e.2 v.annotation_right v.universes v.universe_d v.right)
  | none => ((frames S.levels).act σ e.1, (frames S.levels).act σ e.2)

theorem rereadEq_E {Θ Θ' : Context S.R} {σ : Θ' ⟶ Θ} (A : AnswerData σ) (e : Equation (TotalTerm Θ)) :
    (frames S.levels).E ((frames S.levels).act σ e.1) (rereadEq A e).1 ∧
      (frames S.levels).E ((frames S.levels).act σ e.2) (rereadEq A e).2 := by
  unfold rereadEq
  cases h : readEq (S := S) e with
  | none => exact ⟨((frames S.levels).equivalence Θ').refl _, ((frames S.levels).equivalence Θ').refl _⟩
  | some v =>
      exact ⟨rereadSide_E A e.1 v.annotation_left v.universes v.universe_d v.left,
        rereadSide_E A e.2 v.annotation_right v.universes v.universe_d v.right⟩

/-- **The re-read store.** -/
def rereadStore {Θ Θ' : Context S.R} {σ : Θ' ⟶ Θ} (A : AnswerData σ) (problem : EquationStore (TotalTerm Θ)) :
    EquationStore (TotalTerm Θ') :=
  problem.map (rereadEq A)

/-- **The re-read store has the solutions of the instantiated store.** -/
theorem rereadStore_models {Θ Θ' : Context S.R} {σ : Θ' ⟶ Θ} (A : AnswerData σ)
    (problem : EquationStore (TotalTerm Θ)) {Δ : Context S.R} (g : Δ ⟶ Θ') :
    (frames S.levels).Models g (rereadStore A problem) ↔
      (frames S.levels).Models g ((frames S.levels).applyStore σ problem) := by
  have equivalence := (frames S.levels).equivalence Δ
  constructor
  · intro solved e member
    obtain ⟨e₀, member₀, rfl⟩ := List.mem_map.mp member
    have sides := rereadEq_E A e₀
    have read := solved (rereadEq A e₀) (List.mem_map.mpr ⟨e₀, member₀, rfl⟩)
    have one := (frames S.levels).preserves g sides.1
    have two := (frames S.levels).preserves g sides.2
    exact equivalence.trans one (equivalence.trans read (equivalence.symm two))
  · intro solved e member
    obtain ⟨e₀, member₀, rfl⟩ := List.mem_map.mp member
    have sides := rereadEq_E A e₀
    have read := solved ((frames S.levels).act σ e₀.1, (frames S.levels).act σ e₀.2)
      (List.mem_map.mpr ⟨e₀, member₀, rfl⟩)
    have one := (frames S.levels).preserves g sides.1
    have two := (frames S.levels).preserves g sides.2
    exact equivalence.trans (equivalence.symm one) (equivalence.trans read two)

end Reread

end Miller

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
