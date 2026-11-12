import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MillerRules

/-!
# The Miller steps: delete, value, prune, and the refutations

* `deleteSame`: an equation whose two sides and annotations are the same code is removed.
* `valueUpdate`: `X := λ x̄. val` for a body `val` that every solution's value of `X` opens to (**solve**, from a
  permutation pattern, and **project**, from a rigid local). The residual of a solution is the solution itself.
* `pruneUpdate`: `X := λ x̄. X' x_K`, with `X` declared again at the kept binders `K`, for a store whose every
  solution's value of `X` is pruned to `K` (**prune** and **intersect**). The residual of a solution sends `X'` to
  the value read at the kept binders, the others to inhabitants.
* `locals_unsolvable`, `scope_unsolvable`: two different rigid locals, and a local escaping the unknown's scope, have
  no solution.

Each update is exact through `replace_exact` (or the tree's `exact_iff_update`), and its residual store is the
β-re-read instance of the whole store.
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

/-! ## Opened sides -/

section OpenedSides

variable {S : Setting Head L}

/-- Instantiating the body of a Miller side. -/
theorem subst_flexBody_opened {N M : Nat} (qs ps : List Head) (F : Fin N) (img : Fin ps.length → Fin qs.length)
    (σ : Sub Head N M) :
    Presentation.subst (liftSubs qs σ) (flexBody qs ps F img) =
      Presentation.rename (sideRen qs ps img) (opened ps (σ F)) := by
  unfold flexBody
  rw [subst_apps, map_spineArgs_subst, rename_opened]
  congr 1
  · exact liftSubs_shift qs σ F
  · unfold spineArgs
    congr 1
    funext j
    exact liftSubs_loc qs σ (img j)

/-- The body of a side. -/
def sideBody {N : Nat} {Γ : Ctx Head N} {qs : List Head} {d : Head} {code : Tm Head N} :
    SideView (S := S) Γ qs d code → Tm Head (arity N qs)
  | .flex data _ => flexBody qs data.ps data.unknown data.img
  | .rigid l _ _ => .var (loc qs l)

theorem sideBody_code {N : Nat} {Γ : Ctx Head N} {qs : List Head} {d : Head} {code : Tm Head N}
    (view : SideView (S := S) Γ qs d code) : code = lams qs (sideBody view) := by
  cases view with
  | flex data _ => exact data.side
  | rigid _ side _ => exact side

theorem sideBody_typed {Θ Δ : Context S.R} {qs : List Head} {d : Head} {code : Tm Head Θ.arity}
    (view : SideView (S := S) Θ.raw qs d code) (f : Δ ⟶ Θ) :
    Typed S.R (ctx Δ.raw qs) (Presentation.subst (liftSubs qs f.substitution) (sideBody view)) (.head d) := by
  cases view with
  | flex data below =>
      show Typed S.R _ (Presentation.subst _ (flexBody qs data.ps data.unknown data.img)) _
      rw [subst_flexBody_opened]
      exact flexBody_value_typed f qs data.img data.declared data.domains below
  | rigid l _ below =>
      show Typed S.R _ (liftSubs qs f.substitution (loc qs l)) _
      rw [liftSubs_loc]
      exact local_typed Δ.raw qs l below

/-- **The opened equation of a Miller equation** at a solution. -/
theorem eq_opened {Θ Δ : Context S.R} {e : Equation (TotalTerm Θ)} (v : EqView (S := S) e) (f : Δ ⟶ Θ)
    (solved : (frames S.levels).Solves f e) :
    Equal S.R (ctx Δ.raw v.qs) (Presentation.subst (liftSubs v.qs f.substitution) (sideBody v.left))
      (Presentation.subst (liftSubs v.qs f.substitution) (sideBody v.right)) (.head v.d) :=
  solves_opened v.annotation_left (sideBody_code v.left) (sideBody_code v.right) v.universes v.universe_d f
    (sideBody_typed v.left f) (sideBody_typed v.right f) solved

end OpenedSides

/-! ## Delete -/

section Delete

variable {S : Setting Head L}

/-- **Delete** an equation whose sides and annotations are the same codes. -/
def deleteSame {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (sameType : e.1.1.code = e.2.1.code)
    (sameTerm : e.1.2.code = e.2.2.code) (rest : EquationStore (TotalTerm Θ)) : Update S.levels (e :: rest) where
  target := Θ
  answer := 𝟙 Θ
  remaining := rest
  sound := by
    intro Δ residual solved
    rw [Category.comp_id]
    intro e' member
    rcases List.mem_cons.mp member with rfl | member
    · exact e_of_codes
        (by change Presentation.subst residual.substitution e'.1.1.code = Presentation.subst residual.substitution e'.2.1.code
            rw [sameType])
        (by change Presentation.subst residual.substitution e'.1.2.code = Presentation.subst residual.substitution e'.2.2.code
            rw [sameTerm])
    · exact solved e' member
  complete := by
    intro Δ solution solved
    refine ⟨solution, fun e' member => solved e' (List.mem_cons_of_mem _ member), fun term => ?_⟩
    rw [Category.comp_id]
    exact ((frames S.levels).equivalence Δ).refl _

theorem deleteSame_exact {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (sameType : e.1.1.code = e.2.1.code)
    (sameTerm : e.1.2.code = e.2.2.code) (rest : EquationStore (TotalTerm Θ)) :
    Exact (frames S.levels) (e :: rest) (𝟙 Θ) rest :=
  (DependentFibre.exact_iff_update (levels := S.levels) _ _).mpr ⟨deleteSame sameType sameTerm rest, rfl, rfl, rfl⟩

end Delete

/-! ## Values and pruning -/

section Updates

variable {S : Setting Head L}

/-- The same solution, read into the telescope with `X` declared again at its own family. -/
def sameHom {Δ : Context S.R} (Θ : Context S.R) (families : Families Θ) (X : Fin Θ.arity) {ps : List Head}
    {c : Head} (declared : Ctx.lookup Θ.raw X = famCode ps c) (universes : AllUniverses S.R ps)
    (hc : S.R.isUniverse c) (f : Δ ⟶ Θ) : Δ ⟶ redecl Θ families X ps c universes hc where
  substitution := f.substitution
  typed := by
    intro i
    have same : Ctx.lookup (setFamAt Θ.raw X ps c) i = Ctx.lookup Θ.raw i := by
      by_cases h : i = X
      · rw [h, lookup_setFamAt_self, declared]
      · exact lookup_setFamAt_ne Θ.raw X i ps c h
    show Typed S.R Δ.raw (f.substitution i) (Presentation.subst f.substitution (Ctx.lookup (setFamAt Θ.raw X ps c) i))
    rw [same]
    exact f.typed i

/-- The residual of a pruning: `X'` sent to the value of `X` read at the kept binders. -/
def prunedHom {Δ : Context S.R} (inh : Inhabitants S.R) (Θ : Context S.R) (families : Families Θ)
    (X : Fin Θ.arity) {ps : List Head} {c : Head} (declared : Ctx.lookup Θ.raw X = famCode ps c)
    (universes : AllUniverses S.R ps) (hc : S.R.isUniverse c) (K : List (Fin ps.length)) (f : Δ ⟶ Θ) :
    Δ ⟶ redecl Θ families X (keptDomains ps K) c (keptDomains_universes K universes) hc where
  substitution := fun i => if i = X then
      lams (keptDomains ps K) (Presentation.subst (pullSub inh ps (keptDomains ps K) (keptPos ps K))
        (opened ps (f.substitution X)))
    else f.substitution i
  typed := by
    intro i
    obtain ⟨psi, ci, hi, _, _⟩ := families i
    by_cases h : i = X
    · rw [h]
      show Typed S.R Δ.raw (if X = X then _ else _)
        (Presentation.subst _ (Ctx.lookup (setFamAt Θ.raw X (keptDomains ps K) c) X))
      rw [if_pos rfl, lookup_setFamAt_self, famCode_subst]
      have tOpen := value_opened_typed f declared
      have moved := tOpen.substitute (pullSub_substMor inh Δ.raw ps (keptDomains ps K) (keptPos ps K) universes
        (keptPos_domains ps K))
      exact lams_typed (keptDomains ps K) Δ.formed (keptDomains_universes K universes) hc moved
    · show Typed S.R Δ.raw (if i = X then _ else _)
        (Presentation.subst _ (Ctx.lookup (setFamAt Θ.raw X (keptDomains ps K) c) i))
      rw [if_neg h, lookup_setFamAt_ne Θ.raw X i _ c h, hi, famCode_subst]
      have t := f.typed i
      rw [hi, famCode_subst] at t
      exact t

variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles) (inh : Inhabitants S.R)

/-- The answer of a value rule. -/
def valueHom {Θ : Context S.R} (families : Families Θ) (X : Fin Θ.arity) {psX : List Head} {cX : Head}
    (declared : Ctx.lookup Θ.raw X = famCode psX cX) (universesX : AllUniverses S.R psX) (hcX : S.R.isUniverse cX)
    (val : Tm Head (arity Θ.arity psX))
    (typed : Typed S.R (ctx (setFamAt Θ.raw X psX cX) psX) val (.head cX)) :
    redecl Θ families X psX cX universesX hcX ⟶ Θ :=
  answerHom Θ families X declared universesX hcX psX cX universesX hcX val typed

/-- Its data, for re-reading. -/
def valueData {Θ : Context S.R} (families : Families Θ) (X : Fin Θ.arity) {psX : List Head} {cX : Head}
    (declared : Ctx.lookup Θ.raw X = famCode psX cX) (universesX : AllUniverses S.R psX) (hcX : S.R.isUniverse cX)
    (val : Tm Head (arity Θ.arity psX))
    (typed : Typed S.R (ctx (setFamAt Θ.raw X psX cX) psX) val (.head cX)) :
    AnswerData (valueHom families X declared universesX hcX val typed) where
  X := X
  psX := psX
  cX := cX
  declared := declared
  universesX := universesX
  universe_cX := hcX
  val := val
  typed := typed
  answer_self := answerSub_self X psX val

include facts roots heads algebra rigid complete in
/-- **The value rule** `X := λ x̄. val`, for a store whose every solution opens `X` to `val`. -/
def valueUpdate {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (rest : EquationStore (TotalTerm Θ))
    (families : Families Θ) (X : Fin Θ.arity) {psX : List Head} {cX d : Head}
    (declared : Ctx.lookup Θ.raw X = famCode psX cX) (universesX : AllUniverses S.R psX) (hcX : S.R.isUniverse cX)
    (hd : S.R.isUniverse d) (below : S.R.cumulative cX d) (val : Tm Head (arity Θ.arity psX))
    (typed : Typed S.R (ctx (setFamAt Θ.raw X psX cX) psX) val (.head cX))
    (forced : ∀ {Δ : Context S.R} (f : Δ ⟶ Θ), (frames S.levels).Models f (e :: rest) →
      Equal S.R (ctx Δ.raw psX) (opened psX (f.substitution X))
        (Presentation.subst (liftSubs psX f.substitution) val) (.head d)) : Update S.levels (e :: rest) :=
  replaceUpdate (valueHom families X declared universesX hcX val typed)
    (rereadStore (valueData families X declared universesX hcX val typed) (e :: rest))
    (fun g => rereadStore_models _ (e :: rest) g)
    (fun f solved => ⟨sameHom Θ families X declared universesX hcX f,
      factor_of_opened facts roots heads algebra rigid complete X declared universesX hcX hd below
        (valueHom families X declared universesX hcX val typed) val
        (answerSub_self X psX val) typed f (sameHom Θ families X declared universesX hcX f)
        (fun i ne => by
          show Presentation.subst f.substitution (answerSub X psX val i) = f.substitution i
          rw [answerSub_ne X psX val ne]
          rfl)
        (forced f solved)⟩)

/-- The answer of a pruning. -/
def pruneHom {Θ : Context S.R} (families : Families Θ) (X : Fin Θ.arity) {psX : List Head} {cX : Head}
    (declared : Ctx.lookup Θ.raw X = famCode psX cX) (universesX : AllUniverses S.R psX) (hcX : S.R.isUniverse cX)
    (K : List (Fin psX.length)) :
    redecl Θ families X (keptDomains psX K) cX (keptDomains_universes K universesX) hcX ⟶ Θ :=
  answerHom Θ families X declared universesX hcX (keptDomains psX K) cX (keptDomains_universes K universesX) hcX
    (flexBody psX (keptDomains psX K) X (keptPos psX K)) (by
      have tX : Typed S.R (setFamAt Θ.raw X (keptDomains psX K) cX) (.var X) (famCode (keptDomains psX K) cX) := by
        have v := Derivable.var (R := S.R) (Γ := setFamAt Θ.raw X (keptDomains psX K) cX) X
        rw [lookup_setFamAt_self] at v
        exact v
      rw [flexBody_eq]
      exact (opened_typed (keptDomains psX K) tX).rename
        (sideRen_ctxRen _ psX (keptDomains psX K) (keptPos psX K) (keptPos_domains psX K)))

/-- Its data, for re-reading. -/
def pruneData {Θ : Context S.R} (families : Families Θ) (X : Fin Θ.arity) {psX : List Head} {cX : Head}
    (declared : Ctx.lookup Θ.raw X = famCode psX cX) (universesX : AllUniverses S.R psX) (hcX : S.R.isUniverse cX)
    (K : List (Fin psX.length)) : AnswerData (pruneHom families X declared universesX hcX K) where
  X := X
  psX := psX
  cX := cX
  declared := declared
  universesX := universesX
  universe_cX := hcX
  val := flexBody psX (keptDomains psX K) X (keptPos psX K)
  typed := by
    have tX : Typed S.R (setFamAt Θ.raw X (keptDomains psX K) cX) (.var X) (famCode (keptDomains psX K) cX) := by
      have v := Derivable.var (R := S.R) (Γ := setFamAt Θ.raw X (keptDomains psX K) cX) X
      rw [lookup_setFamAt_self] at v
      exact v
    rw [flexBody_eq]
    exact (opened_typed (keptDomains psX K) tX).rename
      (sideRen_ctxRen _ psX (keptDomains psX K) (keptPos psX K) (keptPos_domains psX K))
  answer_self := answerSub_self X psX _

include facts roots heads algebra rigid complete in
/-- **The pruning rule** `X := λ x̄. X' x_K`, `X'` declared in `X`'s slot at the kept binders, for a store whose every
solution's value of `X` is pruned to `K`. -/
def pruneUpdate {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (rest : EquationStore (TotalTerm Θ))
    (families : Families Θ) (X : Fin Θ.arity) {psX : List Head} {cX d : Head}
    (declared : Ctx.lookup Θ.raw X = famCode psX cX) (universesX : AllUniverses S.R psX) (hcX : S.R.isUniverse cX)
    (hd : S.R.isUniverse d) (below : S.R.cumulative cX d) (K : List (Fin psX.length))
    (pruned : ∀ {Δ : Context S.R} (f : Δ ⟶ Θ), (frames S.levels).Models f (e :: rest) →
      Pruned inh Δ.raw psX K d (f.substitution X)) : Update S.levels (e :: rest) :=
  replaceUpdate (pruneHom families X declared universesX hcX K)
    (rereadStore (pruneData families X declared universesX hcX K) (e :: rest))
    (fun g => rereadStore_models _ (e :: rest) g)
    (fun {Δ} f solved => ⟨prunedHom inh Θ families X declared universesX hcX K f,
      factor_of_opened facts roots heads algebra rigid complete X declared universesX hcX hd below
        (pruneHom families X declared universesX hcX K)
        (flexBody psX (keptDomains psX K) X (keptPos psX K)) (answerSub_self X psX _)
        (pruneData families X declared universesX hcX K).typed f
        (prunedHom inh Θ families X declared universesX hcX K f)
        (fun i ne => by
          show Presentation.subst (prunedHom inh Θ families X declared universesX hcX K f).substitution
            (answerSub X psX _ i) = f.substitution i
          rw [answerSub_ne X psX _ ne]
          show (if i = X then _ else f.substitution i) = f.substitution i
          rw [if_neg ne])
        (by
          have held := pruned f solved
          rw [subst_flexBody_opened]
          have hX : (prunedHom inh Θ families X declared universesX hcX K f).substitution X =
              lams (keptDomains psX K) (Presentation.subst (pullSub inh psX (keptDomains psX K) (keptPos psX K))
                (opened psX (f.substitution X))) := by
            show (if X = X then _ else _) = _
            rw [if_pos rfl]
          rw [hX]
          have tOpen := value_opened_typed f declared
          have tM := tOpen.substitute (pullSub_substMor inh Δ.raw psX (keptDomains psX K) (keptPos psX K)
            universesX (keptPos_domains psX K))
          have beta := opened_lams (keptDomains psX K) Δ.formed (keptDomains_universes K universesX) hcX tM
          have renamed := beta.rename (sideRen_ctxRen Δ.raw psX (keptDomains psX K) (keptPos psX K)
            (keptPos_domains psX K))
          exact held.trans (Derivable.cumulEq renamed below).symm)⟩)

end Updates

/-! ## Refutations -/

section Refutations

variable {S : Setting Head L}
variable (rigid : ∀ name, S.roles name = .rigid) (complete : AlgorithmicComplete S.R S.roles)
  (inh : Inhabitants S.R)

include rigid complete in
/-- **Two different rigid locals**: no solution. -/
theorem locals_unsolvable {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (rest : EquationStore (TotalTerm Θ))
    {qs : List Head} {d : Head} (annotation : e.1.1.code = famCode qs d) (universes : AllUniverses S.R qs)
    (hd : S.R.isUniverse d) {l m : Fin qs.length} (hl : e.1.2.code = localSide qs l)
    (hm : e.2.2.code = localSide qs m) (belowL : S.R.cumulative (qs.get l) d)
    (belowM : S.R.cumulative (qs.get m) d) (different : l ≠ m) :
    ¬ (frames S.levels).Solvable (e :: rest) := by
  rintro ⟨Δ, f, solved⟩
  have tl : Typed S.R (ctx Δ.raw qs) (Presentation.subst (liftSubs qs f.substitution) (.var (loc qs l))) (.head d) := by
    show Typed S.R _ (liftSubs qs f.substitution (loc qs l)) _
    rw [liftSubs_loc]
    exact local_typed Δ.raw qs l belowL
  have tm : Typed S.R (ctx Δ.raw qs) (Presentation.subst (liftSubs qs f.substitution) (.var (loc qs m))) (.head d) := by
    show Typed S.R _ (liftSubs qs f.substitution (loc qs m)) _
    rw [liftSubs_loc]
    exact local_typed Δ.raw qs m belowM
  have opened := solves_opened annotation hl hm universes hd f tl tm (solved e List.mem_cons_self)
  change Equal S.R _ (liftSubs qs f.substitution (loc qs l)) (liftSubs qs f.substitution (loc qs m)) _ at opened
  rw [liftSubs_loc, liftSubs_loc] at opened
  exact locals_refute rigid complete Δ.formed qs universes different opened

include inh rigid complete in
/-- **A local escaping the unknown's scope**: no solution. The opened equation is given at every solution, in
either orientation. -/
theorem scope_unsolvable {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} {qs : List Head} {d : Head}
    (universes : AllUniverses S.R qs) {F : Fin Θ.arity} {ps : List Head} (img : Fin ps.length → Fin qs.length)
    (domains : ∀ j, ps.get j = qs.get (img j)) (injective : Function.Injective img) (l : Fin qs.length)
    (missing : ∀ j, img j ≠ l)
    (opens : ∀ {Δ : Context S.R} (f : Δ ⟶ Θ), (frames S.levels).Models f problem →
      Equal S.R (ctx Δ.raw qs) (Presentation.rename (sideRen qs ps img) (opened ps (f.substitution F)))
        (.var (loc qs l)) (.head d)) :
    ¬ (frames S.levels).Solvable problem := by
  rintro ⟨Δ, f, solved⟩
  exact scope_refutes inh rigid complete f qs img universes domains injective l missing (opens f solved)

end Refutations

end Miller

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
