import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MillerOpening
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPatternFiringInstance
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentNormalEqualizer

/-!
# What a Miller equation forces, read by substitution

**Sides.** Under the locals `ȳ : U_{q̄}`, the side `flexSide qs ps F img` is `λ ȳ. F y_{img 0} … y_{img (k-1)}` for an
unknown `F : Π (x̄ : U_{p̄}). U_c`, and `localSide qs l` is `λ ȳ. y_l`. Instantiating a flex side by a solution `f`
gives the renaming of the opening of `f F` that reads `F`'s binders as the locals `img` (`subst_flexSide_opened`).
When the arguments have exactly the universes of `F`'s domains, that renaming is typed (`sideRen_ctxRen`).

**Solutions, opened** (`solves_opened`, `solves_of_opened`): a morphism solves a Miller equation exactly when the
instantiated bodies are equal at `U_d` under the locals.

**The pull-back** (`pullSub`): along an injective `img`, each local goes to the binder of `ps` read as it, and every
other local to an **inhabitant** of its universe (`Inhabitants`: a head typed in every universe; in the tower,
`legacyGround : U0`, below every universe). It undoes the renaming of the side (`pull_cancel`) and is typed.

**Forcing** (each by one substitution, no normal form):
* `flexFlex_forced`: from `λ ȳ. F y_a ≐ λ ȳ. G y_b`, every solution sends `G` to `λ z̄. F` applied to `a` read
  through `b⁻¹`, with inhabitants where a local of `a` is not among `b`. When every local of `a` is among `b`, this is
  the inversion `G := λ z̄. F z_{b⁻¹ a}`; when not, it says that `F`'s value uses only the positions whose locals are
  among `b` (pruning).
* `flexLocal_forced`: from `λ ȳ. F y_a ≐ λ ȳ. y_l`, every solution sends `F` to the projection on `a⁻¹ l`.
* `scope_refutes`: if `l` is not among `a`, there is no solution: the local `y_l` would equal an inhabitant, a head,
  and a variable and a head have different supports (`equal_support`).
* `locals_refute`: `λ ȳ. y_l ≐ λ ȳ. y_m` with `l ≠ m` has no solution.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

namespace Miller

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta

variable {Head L : Type} [UniverseLevel.LevelOrder L]

/-! ## Inhabitants -/

/-- **Inhabitants**: a head typed in every universe, in every telescope. -/
structure Inhabitants (R : Rules Head) where
  pick : Head → Head
  typed : ∀ {q : Head}, R.isUniverse q → ∀ {n : Nat} (Γ : Ctx Head n), Typed R Γ (.head (pick q)) (.head q)

/-! ## Sides -/

section Sides

/-- `F` applied to the locals `img 0, …, img (k - 1)`, under the binders `qs`. -/
def flexBody {N : Nat} (qs ps : List Head) (F : Fin N) (img : Fin ps.length → Fin qs.length) :
    Tm Head (arity N qs) :=
  apps (.var (shift qs F)) (spineArgs ps fun j => loc qs (img j))

/-- **A Miller side** `λ ȳ. F y_{img 0} … y_{img (k - 1)}`. -/
def flexSide {N : Nat} (qs ps : List Head) (F : Fin N) (img : Fin ps.length → Fin qs.length) : Tm Head N :=
  lams qs (flexBody qs ps F img)

/-- **A rigid local** `λ ȳ. y_l`. -/
def localSide {N : Nat} (qs : List Head) (l : Fin qs.length) : Tm Head N :=
  lams qs (.var (loc qs l))

/-- The renaming that reads the binders of `ps` as the locals `img`. -/
abbrev sideRen {n : Nat} (qs ps : List Head) (img : Fin ps.length → Fin qs.length) :
    Ren (arity n ps) (arity n qs) :=
  spineRen ps (shift qs) fun j => loc qs (img j)

theorem map_spineArgs_rename {m k : Nat} (ps : List Head) (img : Fin ps.length → Fin m) (ρ : Ren m k) :
    (spineArgs ps img).map (Presentation.rename ρ) = spineArgs ps fun j => ρ (img j) := by
  unfold spineArgs
  rw [List.map_map]
  rfl

theorem map_spineArgs_subst {m k : Nat} (ps : List Head) (img : Fin ps.length → Fin m) (σ : Sub Head m k) :
    (spineArgs ps img).map (Presentation.subst σ) = (List.finRange ps.length).map fun j => σ (img j) := by
  unfold spineArgs
  rw [List.map_map]
  rfl

/-- The renamed opening of a function is the function applied to the renamed locals. -/
theorem rename_opened {n m : Nat} (ps : List Head) (ρ : Ren n m) (img : Fin ps.length → Fin m) (t : Tm Head n) :
    Presentation.rename (spineRen ps ρ img) (opened ps t) = apps (Presentation.rename ρ t) (spineArgs ps img) := by
  rw [opened_eq, rename_apps, rename_comp, map_spineArgs_rename]
  congr 1
  · exact rename_ext (fun v => spineRen_shift ps ρ img v) t
  · congr 1
    funext j
    exact spineRen_loc ps ρ img j

/-- Instantiating a flex side. -/
theorem subst_flexSide {N M : Nat} (qs ps : List Head) (F : Fin N) (img : Fin ps.length → Fin qs.length)
    (σ : Sub Head N M) :
    Presentation.subst σ (flexSide qs ps F img) =
      lams qs (apps (Presentation.rename (shift qs) (σ F)) (spineArgs ps fun j => loc qs (img j))) := by
  unfold flexSide flexBody
  rw [subst_lams, subst_apps, map_spineArgs_subst]
  congr 2
  · exact liftSubs_shift qs σ F
  · unfold spineArgs
    congr 1
    funext j
    exact liftSubs_loc qs σ (img j)

/-- **Instantiating a flex side reads the opening of the value at the locals.** -/
theorem subst_flexSide_opened {N M : Nat} (qs ps : List Head) (F : Fin N) (img : Fin ps.length → Fin qs.length)
    (σ : Sub Head N M) :
    Presentation.subst σ (flexSide qs ps F img) = lams qs (Presentation.rename (sideRen qs ps img) (opened ps (σ F))) := by
  rw [subst_flexSide, rename_opened]

/-- A rigid local is closed in the outer telescope. -/
theorem subst_localSide {N M : Nat} (qs : List Head) (l : Fin qs.length) (σ : Sub Head N M) :
    Presentation.subst σ (localSide (N := N) qs l) = localSide (N := M) qs l := by
  unfold localSide
  rw [subst_lams]
  congr 1
  exact liftSubs_loc qs σ l

/-- The body of a flex side is the renamed opening of its unknown. -/
theorem flexBody_eq {N : Nat} (qs ps : List Head) (F : Fin N) (img : Fin ps.length → Fin qs.length) :
    flexBody qs ps F img = Presentation.rename (sideRen qs ps img) (opened ps (.var F)) := by
  rw [rename_opened]
  rfl

end Sides

/-! ## Typing of sides -/

section SideTyping

variable {S : Setting Head L}

/-- The side's renaming is typed when the arguments have exactly the universes of the domains. -/
theorem sideRen_ctxRen {n : Nat} (Γ : Ctx Head n) (qs ps : List Head) (img : Fin ps.length → Fin qs.length)
    (domains : ∀ j, ps.get j = qs.get (img j)) : CtxRen (ctx Γ ps) (ctx Γ qs) (sideRen qs ps img) :=
  spineRen_ctxRen ps (shift qs) _ (shift_ctxRen Γ qs) fun j => by rw [lookup_loc, domains j]

/-- The opening of an unknown's value. -/
theorem value_opened_typed {Θ Δ : Context S.R} (f : Δ ⟶ Θ) {F : Fin Θ.arity} {ps : List Head} {c : Head}
    (declared : Ctx.lookup Θ.raw F = famCode ps c) :
    Typed S.R (ctx Δ.raw ps) (opened ps (f.substitution F)) (.head c) := by
  have typed := f.typed F
  rw [declared, famCode_subst] at typed
  exact opened_typed ps typed

/-- The instantiated body of a flex side, at the annotation's codomain. -/
theorem flexBody_value_typed {Θ Δ : Context S.R} (f : Δ ⟶ Θ) (qs : List Head) {F : Fin Θ.arity} {ps : List Head}
    {c d : Head} (img : Fin ps.length → Fin qs.length) (declared : Ctx.lookup Θ.raw F = famCode ps c)
    (domains : ∀ j, ps.get j = qs.get (img j)) (below : S.R.cumulative c d) :
    Typed S.R (ctx Δ.raw qs) (Presentation.rename (sideRen qs ps img) (opened ps (f.substitution F))) (.head d) := by
  have renamed := (value_opened_typed f declared).rename (sideRen_ctxRen Δ.raw qs ps img domains)
  exact Derivable.cumul renamed below

/-- A rigid local, at the annotation's codomain. -/
theorem local_typed {n : Nat} (Γ : Ctx Head n) (qs : List Head) {d : Head} (l : Fin qs.length)
    (below : S.R.cumulative (qs.get l) d) : Typed S.R (ctx Γ qs) (.var (loc qs l)) (.head d) := by
  have typed := Derivable.var (R := S.R) (Γ := ctx Γ qs) (loc qs l)
  rw [lookup_loc] at typed
  exact Derivable.cumul typed below

/-- A flex side is a function of the annotation's family. -/
theorem flexSide_typed {Θ : Context S.R} (qs : List Head) {F : Fin Θ.arity} {ps : List Head} {c d : Head}
    (img : Fin ps.length → Fin qs.length) (declared : Ctx.lookup Θ.raw F = famCode ps c)
    (domains : ∀ j, ps.get j = qs.get (img j)) (below : S.R.cumulative c d) (universes : AllUniverses S.R qs)
    (hd : S.R.isUniverse d) : Typed S.R Θ.raw (flexSide qs ps F img) (famCode qs d) := by
  have tF : Typed S.R Θ.raw (.var F) (famCode ps c) := by
    have typed := Derivable.var (R := S.R) (Γ := Θ.raw) F
    rw [declared] at typed
    exact typed
  have body : Typed S.R (ctx Θ.raw qs) (flexBody qs ps F img) (.head d) := by
    rw [flexBody_eq]
    exact Derivable.cumul ((opened_typed ps tF).rename (sideRen_ctxRen Θ.raw qs ps img domains)) below
  exact lams_typed qs Θ.formed universes hd body

end SideTyping

/-! ## Solutions, opened -/

section Opened

variable {S : Setting Head L}

/-- **A solution of a Miller equation equates the instantiated bodies under the locals.** -/
theorem solves_opened {Θ Δ : Context S.R} {e : Equation (TotalTerm Θ)} {qs : List Head} {d : Head}
    {left right : Tm Head (arity Θ.arity qs)} (annotation : e.1.1.code = famCode qs d)
    (sideL : e.1.2.code = lams qs left) (sideR : e.2.2.code = lams qs right) (universes : AllUniverses S.R qs)
    (hd : S.R.isUniverse d) (f : Δ ⟶ Θ)
    (tl : Typed S.R (ctx Δ.raw qs) (Presentation.subst (liftSubs qs f.substitution) left) (.head d))
    (tr : Typed S.R (ctx Δ.raw qs) (Presentation.subst (liftSubs qs f.substitution) right) (.head d))
    (solved : (frames S.levels).Solves f e) :
    Equal S.R (ctx Δ.raw qs) (Presentation.subst (liftSubs qs f.substitution) left)
      (Presentation.subst (liftSubs qs f.substitution) right) (.head d) := by
  have equal := ((equivalent_iff S.levels _ _).mp solved).2
  change Equal S.R Δ.raw (Presentation.subst f.substitution e.1.2.code) (Presentation.subst f.substitution e.2.2.code)
    (Presentation.subst f.substitution e.1.1.code) at equal
  rw [sideL, sideR, annotation, subst_lams, subst_lams, famCode_subst] at equal
  exact (lams_equal_iff qs Δ.formed universes hd tl tr).mp equal

/-- **Equal instantiated bodies solve the Miller equation.** -/
theorem solves_of_opened {Θ Δ : Context S.R} {e : Equation (TotalTerm Θ)} {qs : List Head} {d : Head}
    {left right : Tm Head (arity Θ.arity qs)} (annotation : e.1.1.code = famCode qs d)
    (annotationR : e.2.1.code = famCode qs d) (sideL : e.1.2.code = lams qs left) (sideR : e.2.2.code = lams qs right)
    (universes : AllUniverses S.R qs) (hd : S.R.isUniverse d) (f : Δ ⟶ Θ)
    (tl : Typed S.R (ctx Δ.raw qs) (Presentation.subst (liftSubs qs f.substitution) left) (.head d))
    (tr : Typed S.R (ctx Δ.raw qs) (Presentation.subst (liftSubs qs f.substitution) right) (.head d))
    (equal : Equal S.R (ctx Δ.raw qs) (Presentation.subst (liftSubs qs f.substitution) left)
      (Presentation.subst (liftSubs qs f.substitution) right) (.head d)) :
    (frames S.levels).Solves f e := by
  apply (equivalent_iff S.levels _ _).mpr
  constructor
  · change TypeEq S.R Δ.raw (Presentation.subst f.substitution e.1.1.code) (Presentation.subst f.substitution e.2.1.code)
    rw [annotation, annotationR, famCode_subst]
    exact (famCode_isType qs universes hd Δ.formed).refl
  · change Equal S.R Δ.raw (Presentation.subst f.substitution e.1.2.code) (Presentation.subst f.substitution e.2.2.code)
      (Presentation.subst f.substitution e.1.1.code)
    rw [sideL, sideR, annotation, subst_lams, subst_lams, famCode_subst]
    exact (lams_equal_iff qs Δ.formed universes hd tl tr).mpr equal

end Opened

/-! ## The pull-back -/

section Pullback

variable {S : Setting Head L} (inh : Inhabitants S.R)

/-- The binder of `ps` read as the local `l`, if any. -/
def posOf {qs ps : List Head} (img : Fin ps.length → Fin qs.length) (l : Fin qs.length) : Option (Fin ps.length) :=
  (List.finRange ps.length).find? fun j => decide (img j = l)

theorem posOf_img {qs ps : List Head} {img : Fin ps.length → Fin qs.length} (injective : Function.Injective img)
    (j : Fin ps.length) : posOf img (img j) = some j := by
  unfold posOf
  cases found : (List.finRange ps.length).find? (fun i => decide (img i = img j)) with
  | none =>
      have missing := List.find?_eq_none.mp found j (List.mem_finRange j)
      simp at missing
  | some i =>
      have hit := List.find?_some found
      simp only [decide_eq_true_eq] at hit
      rw [injective hit]

theorem posOf_some {qs ps : List Head} {img : Fin ps.length → Fin qs.length} {l : Fin qs.length} {j : Fin ps.length}
    (found : posOf img l = some j) : img j = l := by
  have hit := List.find?_some found
  simpa using hit

theorem posOf_none {qs ps : List Head} {img : Fin ps.length → Fin qs.length} {l : Fin qs.length}
    (found : posOf img l = none) (j : Fin ps.length) : img j ≠ l := by
  intro same
  have missing := List.find?_eq_none.mp found j (List.mem_finRange j)
  simp [same] at missing

theorem posOf_none_of {qs ps : List Head} {img : Fin ps.length → Fin qs.length} {l : Fin qs.length}
    (missing : ∀ j, img j ≠ l) : posOf img l = none := by
  cases found : posOf img l with
  | none => rfl
  | some j => exact absurd (posOf_some found) (missing j)

/-- The image of a local under the pull-back. -/
def pullImg {n : Nat} (qs ps : List Head) (img : Fin ps.length → Fin qs.length) (l : Fin qs.length) :
    Tm Head (arity n ps) :=
  match posOf img l with
  | some j => .var (loc ps j)
  | none => .head (inh.pick (qs.get l))

/-- **The pull-back along `img`**: the locals of `img` back to the binders of `ps`, the others to inhabitants. -/
def pullSub {n : Nat} (qs ps : List Head) (img : Fin ps.length → Fin qs.length) :
    Sub Head (arity n qs) (arity n ps) :=
  subsAt qs (fun v => .var (shift ps v)) (pullImg inh qs ps img)

theorem pullImg_img {n : Nat} {qs ps : List Head} {img : Fin ps.length → Fin qs.length}
    (injective : Function.Injective img) (j : Fin ps.length) :
    pullImg (n := n) inh qs ps img (img j) = .var (loc ps j) := by
  unfold pullImg
  rw [posOf_img injective j]

theorem pullImg_missing {n : Nat} {qs ps : List Head} {img : Fin ps.length → Fin qs.length} {l : Fin qs.length}
    (missing : ∀ j, img j ≠ l) : pullImg (n := n) inh qs ps img l = .head (inh.pick (qs.get l)) := by
  unfold pullImg
  rw [posOf_none_of missing]

theorem pullSub_shift {n : Nat} (qs ps : List Head) (img : Fin ps.length → Fin qs.length) (v : Fin n) :
    pullSub inh qs ps img (shift qs v) = .var (shift ps v) := by
  unfold pullSub
  rw [subsAt_shift]

theorem pullSub_loc {n : Nat} (qs ps : List Head) (img : Fin ps.length → Fin qs.length) (l : Fin qs.length) :
    pullSub (n := n) inh qs ps img (loc qs l) = pullImg inh qs ps img l := by
  unfold pullSub
  rw [subsAt_loc]

/-- **The pull-back undoes the side's renaming.** -/
theorem pull_cancel {n : Nat} (qs ps : List Head) (img : Fin ps.length → Fin qs.length)
    (injective : Function.Injective img) (X : Tm Head (arity n ps)) :
    Presentation.subst (pullSub inh qs ps img) (Presentation.rename (sideRen qs ps img) X) = X := by
  rw [subst_rename]
  conv_rhs => rw [← subst_ids X]
  apply subst_ext
  intro i
  rcases index_cases ps i with ⟨v, rfl⟩ | ⟨j, rfl⟩
  · show pullSub inh qs ps img (spineRen ps (shift qs) _ (shift ps v)) = .var (shift ps v)
    rw [spineRen_shift, pullSub_shift]
  · show pullSub inh qs ps img (spineRen ps (shift qs) _ (loc ps j)) = .var (loc ps j)
    rw [spineRen_loc, pullSub_loc, pullImg_img inh injective]

/-- The pull-back keeps an outer term. -/
theorem pull_outer {n : Nat} (qs ps : List Head) (img : Fin ps.length → Fin qs.length) (t : Tm Head n) :
    Presentation.subst (pullSub inh qs ps img) (Presentation.rename (shift qs) t) =
      Presentation.rename (shift ps) t := by
  rw [subst_rename, ← subst_renSub]
  apply subst_ext
  intro v
  rw [pullSub_shift]
  rfl

/-- **The pull-back is typed.** -/
theorem pullSub_substMor {n : Nat} (Γ : Ctx Head n) (qs ps : List Head) (img : Fin ps.length → Fin qs.length)
    (universes : AllUniverses S.R qs) (domains : ∀ j, ps.get j = qs.get (img j)) :
    SubstMor S.R (ctx Γ qs) (ctx Γ ps) (pullSub inh qs ps img) := by
  apply subsAt_substMor
  · intro v
    show Typed S.R (ctx Γ ps) (.var (shift ps v)) (Presentation.subst (renSub (shift ps)) (Ctx.lookup Γ v))
    rw [subst_renSub]
    have typed := Derivable.var (R := S.R) (Γ := ctx Γ ps) (shift ps v)
    rw [lookup_shift] at typed
    exact typed
  · intro l
    unfold pullImg
    cases found : posOf img l with
    | some j =>
        have typed := Derivable.var (R := S.R) (Γ := ctx Γ ps) (loc ps j)
        rw [lookup_loc, domains j, posOf_some found] at typed
        exact typed
    | none => exact inh.typed (universes _ (List.get_mem qs l)) _

end Pullback

/-! ## Forcing -/

section Forcing

variable {S : Setting Head L} (inh : Inhabitants S.R)

/-- **What a flex-flex Miller equation forces.** From `λ ȳ. F y_a ≐ λ ȳ. G y_b`, every solution sends `G`, opened,
to `F` applied to `a` read through the pull-back along `b`. -/
theorem flexFlex_forced {Θ Δ : Context S.R} (f : Δ ⟶ Θ) (qs : List Head) {d : Head} {F G : Fin Θ.arity}
    {psF psG : List Head} (imgF : Fin psF.length → Fin qs.length) (imgG : Fin psG.length → Fin qs.length)
    (universes : AllUniverses S.R qs) (domainsG : ∀ j, psG.get j = qs.get (imgG j))
    (injectiveG : Function.Injective imgG)
    (equal : Equal S.R (ctx Δ.raw qs) (Presentation.rename (sideRen qs psF imgF) (opened psF (f.substitution F)))
      (Presentation.rename (sideRen qs psG imgG) (opened psG (f.substitution G))) (.head d)) :
    Equal S.R (ctx Δ.raw psG)
      (apps (Presentation.rename (shift psG) (f.substitution F))
        ((List.finRange psF.length).map fun i => pullImg inh qs psG imgG (imgF i)))
      (opened psG (f.substitution G)) (.head d) := by
  have moved := equal.substitute (pullSub_substMor inh Δ.raw qs psG imgG universes domainsG)
  rw [pull_cancel inh qs psG imgG injectiveG, rename_opened, subst_apps, map_spineArgs_subst, pull_outer] at moved
  simpa only [Presentation.subst, pullSub_loc] using moved

/-- **What a flex-local equation forces.** From `λ ȳ. F y_a ≐ λ ȳ. y_l`, every solution sends `F`, opened, to the
pull-back of the local `l`. -/
theorem flexLocal_forced {Θ Δ : Context S.R} (f : Δ ⟶ Θ) (qs : List Head) {d : Head} {F : Fin Θ.arity}
    {psF : List Head} (imgF : Fin psF.length → Fin qs.length) (universes : AllUniverses S.R qs)
    (domainsF : ∀ j, psF.get j = qs.get (imgF j)) (injectiveF : Function.Injective imgF) (l : Fin qs.length)
    (equal : Equal S.R (ctx Δ.raw qs) (Presentation.rename (sideRen qs psF imgF) (opened psF (f.substitution F)))
      (.var (loc qs l)) (.head d)) :
    Equal S.R (ctx Δ.raw psF) (opened psF (f.substitution F)) (pullImg inh qs psF imgF l) (.head d) := by
  have moved := equal.substitute (pullSub_substMor inh Δ.raw qs psF imgF universes domainsF)
  rw [pull_cancel inh qs psF imgF injectiveF] at moved
  simpa only [Presentation.subst, pullSub_loc] using moved

variable (rigid : ∀ name, S.roles name = .rigid) (complete : AlgorithmicComplete S.R S.roles)

include rigid complete in
/-- **A variable is never equal to a head.** -/
theorem var_ne_head {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) (i : Fin n) (h : Head) {A : Tm Head n}
    (equal : Equal S.R Γ (.var i) (.head h) A) : False := by
  have supports := ContextualDependentNormalSupport.equal_support rigid complete formed equal
    (ContextualDependentNormalObservations.normal_var rigid i) (ContextualDependentPatternFiring.normal_head rigid h)
  have member : i ∈ (Tm.var i : Tm Head n).support := by simp [Tm.support]
  rw [supports] at member
  simp [Tm.support] at member

include rigid complete in
/-- **Two different variables are never equal.** -/
theorem var_ne_var {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {i j : Fin n} (different : i ≠ j)
    {A : Tm Head n} (equal : Equal S.R Γ (.var i) (.var j) A) : False := by
  have supports := ContextualDependentNormalSupport.equal_support rigid complete formed equal
    (ContextualDependentNormalObservations.normal_var rigid i) (ContextualDependentNormalObservations.normal_var rigid j)
  have member : i ∈ (Tm.var i : Tm Head n).support := by simp [Tm.support]
  rw [supports] at member
  simp [Tm.support] at member
  exact different member

include inh rigid complete in
/-- **A local escaping the scope of the unknown refutes.** From `λ ȳ. F y_a ≐ λ ȳ. y_l` with `l` not among `a`, no
solution: `y_l` would equal an inhabitant, a head. -/
theorem scope_refutes {Θ Δ : Context S.R} (f : Δ ⟶ Θ) (qs : List Head) {d : Head} {F : Fin Θ.arity}
    {psF : List Head} (imgF : Fin psF.length → Fin qs.length) (universes : AllUniverses S.R qs)
    (domainsF : ∀ j, psF.get j = qs.get (imgF j)) (injectiveF : Function.Injective imgF) (l : Fin qs.length)
    (missing : ∀ j, imgF j ≠ l)
    (equal : Equal S.R (ctx Δ.raw qs) (Presentation.rename (sideRen qs psF imgF) (opened psF (f.substitution F)))
      (.var (loc qs l)) (.head d)) : False := by
  have forced := flexLocal_forced inh f qs imgF universes domainsF injectiveF l equal
  rw [pullImg_missing inh missing] at forced
  have renamed := forced.rename (sideRen_ctxRen Δ.raw qs psF imgF domainsF)
  have clash : Equal S.R (ctx Δ.raw qs) (.var (loc qs l)) (.head (inh.pick (qs.get l))) (.head d) :=
    equal.symm.trans renamed
  exact var_ne_head rigid complete (ctx_formed qs Δ.formed universes) _ _ clash

include rigid complete in
/-- **Two different rigid locals refute.** -/
theorem locals_refute {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) (qs : List Head) {d : Head}
    (universes : AllUniverses S.R qs) {l m : Fin qs.length} (different : l ≠ m)
    (equal : Equal S.R (ctx Γ qs) (.var (loc qs l)) (.var (loc qs m)) (.head d)) : False :=
  var_ne_var rigid complete (ctx_formed qs formed universes) (fun same => different (loc_injective qs same)) equal

end Forcing

end Miller

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
