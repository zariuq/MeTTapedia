import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.Trimming

/-!
# Pattern-covered answers are epimorphisms; the trimming theorem for answers that prune in place

The trimming theorem (`initial_of_trimmed`) asks every unknown an answer mentions to be **fixed** by it. Pruning in
place breaks that: the pruned unknown `X` is declared again at fewer arguments and the answer sends the old `X` to
`λ x̄. X x_K`, which mentions `X` without fixing it. What the epimorphism needs is weaker.

* **Pattern-covered** (`PatternCovered`): an unknown `j` of the answer's telescope is covered when some unknown `i` of
  the store's telescope is sent, up to the fibre's equality at `i`'s declaration, to `λ ȳ. j y_K` with distinct locals
  `K`, each of exactly `j`'s domain, at a codomain above `j`'s. A fixed unknown is the case `K` = all locals
  (`fixed_patternCovered`).
* **Pattern injectivity** (`pattern_injective`): two morphisms that agree on `λ ȳ. j y_K` agree on `j`. Open both
  sides at the locals, pull back along `K` with inhabitants of the universes at the other locals (the pull-back
  cancels `K` because `K` is injective), lower the universe, and close by η.
* **Covered answers are epimorphisms** (`epi_of_patternCovered`), hence **principal and covered is initial**
  (`initial_of_patternCovered`).
* **The trimming theorem for patterns** (`initial_of_patternTrimmed`): delete the unknowns the answer does not mention;
  when every unknown it mentions is pattern-covered, the trimmed answer is the initial solution.
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
open ContextualDependentUniverseInjective

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-! ## Pattern-covered unknowns -/

section Covered

/-- **`j` is covered by a pattern of `σ`**: some unknown `i` of the store's telescope is sent, up to the fibre's
equality at its declaration, to `λ ȳ. j y_K`, with distinct locals `K` each of exactly `j`'s domain, at a codomain
above `j`'s. -/
def PatternCovered {Δ Θ : Context S.R} (σ : Δ ⟶ Θ) (j : Fin Δ.arity) : Prop :=
  ∃ (i : Fin Θ.arity) (ps qs : List Head) (c c' : Head) (K : Fin ps.length → Fin qs.length),
    Ctx.lookup Δ.raw j = famCode ps c ∧ Ctx.lookup Θ.raw i = famCode qs c' ∧ AllUniverses S.R ps ∧
      AllUniverses S.R qs ∧ S.R.isUniverse c ∧ S.R.isUniverse c' ∧ S.R.cumulative c c' ∧ Function.Injective K ∧
      (∀ k, ps.get k = qs.get (K k)) ∧ Equal S.R Δ.raw (σ.substitution i) (flexSide qs ps j K) (famCode qs c')

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles) (inh : Inhabitants S.R)

include facts roots heads algebra rigid complete inh in
/-- **Pattern injectivity**: two morphisms that agree on `λ ȳ. j y_K`, with `K` injective, agree on `j`. -/
theorem pattern_injective {b Δ : Context S.R} (g h : b ⟶ Δ) {j : Fin Δ.arity} {ps qs : List Head} {c c' : Head}
    {K : Fin ps.length → Fin qs.length} (dj : Ctx.lookup Δ.raw j = famCode ps c) (ups : AllUniverses S.R ps)
    (uqs : AllUniverses S.R qs) (uc : S.R.isUniverse c) (uc' : S.R.isUniverse c') (below : S.R.cumulative c c')
    (injective : Function.Injective K) (domains : ∀ k, ps.get k = qs.get (K k))
    (equal : Equal S.R b.raw (Presentation.subst g.substitution (flexSide qs ps j K))
      (Presentation.subst h.substitution (flexSide qs ps j K)) (famCode qs c')) :
    Equal S.R b.raw (g.substitution j) (h.substitution j) (famCode ps c) := by
  have tg : Typed S.R b.raw (g.substitution j) (famCode ps c) := by
    have typed := g.typed j
    rw [dj, famCode_subst] at typed
    exact typed
  have th : Typed S.R b.raw (h.substitution j) (famCode ps c) := by
    have typed := h.typed j
    rw [dj, famCode_subst] at typed
    exact typed
  rw [subst_flexSide_opened, subst_flexSide_opened] at equal
  have rg : Typed S.R (ctx b.raw qs) (Presentation.rename (sideRen qs ps K) (opened ps (g.substitution j)))
      (.head c') :=
    Derivable.cumul ((opened_typed ps tg).rename (sideRen_ctxRen b.raw qs ps K domains)) below
  have rh : Typed S.R (ctx b.raw qs) (Presentation.rename (sideRen qs ps K) (opened ps (h.substitution j)))
      (.head c') :=
    Derivable.cumul ((opened_typed ps th).rename (sideRen_ctxRen b.raw qs ps K domains)) below
  have opened' := (lams_equal_iff qs b.formed uqs uc' rg rh).mp equal
  have pulled := opened'.substitute (pullSub_substMor inh b.raw qs ps K uqs domains)
  rw [pull_cancel inh qs ps K injective, pull_cancel inh qs ps K injective] at pulled
  have pulled' : Equal S.R (ctx b.raw ps) (opened ps (g.substitution j)) (opened ps (h.substitution j))
      (.head c') := pulled
  have formedP : CtxFormed S.R (ctx b.raw ps) := ctx_formed ps b.formed ups
  have atC := universe_injective facts roots heads algebra rigid complete formedP uc uc'
    (opened_typed ps tg) (opened_typed ps th) pulled'
  have lifted := (lams_equal_iff ps b.formed ups uc (opened_typed ps tg) (opened_typed ps th)).mpr atC
  exact ((eta_opened ps b.formed tg).symm.trans lifted).trans (eta_opened ps b.formed th)

include facts roots heads algebra rigid complete inh in
/-- **Pattern-covered answers are epimorphisms on terms.** -/
theorem epi_of_patternCovered {Δ Θ : Context S.R} (σ : Δ ⟶ Θ) (covered : ∀ j, PatternCovered σ j) :
    EpiOnTerms (frames S.levels) σ := by
  intro b g h agree
  refine act_equal_of_substEq S.levels ⟨g.typed, fun j => ?_⟩
  obtain ⟨i, ps, qs, c, c', K, dj, di, ups, uqs, uc, uc', below, injective, domains, cov⟩ := covered j
  have e := (agree (unknownTerm Θ i)).2
  change Equal S.R b.raw (Presentation.subst g.substitution (Presentation.subst σ.substitution (.var i)))
    (Presentation.subst h.substitution (Presentation.subst σ.substitution (.var i)))
    (Presentation.subst g.substitution (Presentation.subst σ.substitution (Ctx.lookup Θ.raw i))) at e
  rw [di, famCode_subst, famCode_subst] at e
  change Equal S.R b.raw (Presentation.subst g.substitution (σ.substitution i))
    (Presentation.subst h.substitution (σ.substitution i)) (famCode qs c') at e
  have cg := cov.substitute g.typed
  have ch := cov.substitute h.typed
  rw [famCode_subst] at cg ch
  rw [dj, famCode_subst]
  exact pattern_injective facts roots heads algebra rigid complete inh g h dj ups uqs uc uc' below injective domains
    ((cg.symm.trans e).trans ch)

include facts roots heads algebra rigid complete inh in
/-- **A principal answer that is pattern-covered is the initial solution.** -/
theorem initial_of_patternCovered {Δ Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} {σ : Δ ⟶ Θ}
    (principal : (frames S.levels).Principal problem σ) (covered : ∀ j, PatternCovered σ j) :
    InitialSolution (frames S.levels) problem σ :=
  Principal.initial principal (epi_of_patternCovered facts roots heads algebra rigid complete inh σ covered)

/-- The locals `0, …, k - 1` in order: the pattern of a fixed unknown. -/
theorem flexSide_all {N : Nat} (ps : List Head) (j : Fin N) :
    flexSide ps ps j (fun k => k) = lams ps (opened ps (.var j)) := by
  unfold flexSide
  rw [flexBody_eq]
  congr 1
  conv_rhs => rw [← rename_id (opened ps (.var j))]
  apply rename_ext
  intro u
  rcases index_cases ps u with ⟨w, rfl⟩ | ⟨k, rfl⟩
  · exact spineRen_shift ps (shift ps) _ w
  · exact spineRen_loc ps (shift ps) _ k

/-- **A fixed unknown is pattern-covered**: its pattern is its η-expansion. -/
theorem fixed_patternCovered {Δ Θ : Context S.R} (σ : Δ ⟶ Θ) {i : Fin Θ.arity} {j : Fin Δ.arity}
    {ps : List Head} {c c' : Head} (fixed : σ.substitution i = .var j) (dj : Ctx.lookup Δ.raw j = famCode ps c)
    (di : Ctx.lookup Θ.raw i = famCode ps c') (ups : AllUniverses S.R ps) (uc : S.R.isUniverse c)
    (uc' : S.R.isUniverse c') (below : S.R.cumulative c c') : PatternCovered σ j := by
  refine ⟨i, ps, ps, c, c', fun k => k, dj, di, ups, ups, uc, uc', below, fun _ _ h => h, fun _ => rfl, ?_⟩
  rw [fixed, flexSide_all]
  have tj : Typed S.R Δ.raw (.var j) (famCode ps c) := by
    have typed := Derivable.var (R := S.R) (Γ := Δ.raw) j
    rw [dj] at typed
    exact typed
  have tj' : Typed S.R Δ.raw (.var j) (famCode ps c') :=
    Derivable.sub tj ((lowers_famCode ps uc uc' below).usable (famCode_isType ps ups uc Δ.formed)
      (famCode_isType ps ups uc' Δ.formed))
  exact (eta_opened ps Δ.formed tj').symm

end Covered

/-! ## The trimming theorem for patterns -/

section Trimmed

/-- The unknowns an answer mentions, in order. -/
def mentionedOf {Δ Θ : Context S.R} (σ : Δ ⟶ Θ) : List (Fin Δ.arity) :=
  (List.finRange Δ.arity).filter fun j => decide (∃ i, j ∈ (σ.substitution i).support)

theorem mentionedOf_nodup {Δ Θ : Context S.R} (σ : Δ ⟶ Θ) : (mentionedOf σ).Nodup :=
  (List.nodup_finRange _).filter _

theorem mem_mentionedOf {Δ Θ : Context S.R} (σ : Δ ⟶ Θ) (j : Fin Δ.arity) :
    j ∈ mentionedOf σ ↔ ∃ i, j ∈ (σ.substitution i).support := by
  simp [mentionedOf, List.mem_filter, List.mem_finRange]

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles) (inh : Inhabitants S.R)

include facts roots heads algebra rigid complete in
/-- **Deleting the unknowns an answer does not mention makes a principal answer the initial solution**, when every
unknown it mentions is pattern-covered. -/
theorem initial_of_patternTrimmed {Δ Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} {σ : Δ ⟶ Θ}
    (principal : (frames S.levels).Principal problem σ)
    (view : Fin Δ.arity → List Head × Head) (declared : ∀ j, Ctx.lookup Δ.raw j = famCode (view j).1 (view j).2)
    (universes : ∀ j, AllUniverses S.R (view j).1 ∧ S.R.isUniverse (view j).2)
    (covered : ∀ j, (∃ i, j ∈ (σ.substitution i).support) → PatternCovered σ j) :
    InitialSolution (frames S.levels) problem (trimOut view declared universes inh (mentionedOf σ) ≫ σ) := by
  have memKs := mem_mentionedOf σ
  have back : trimIn view declared universes (mentionedOf σ) ≫
      (trimOut view declared universes inh (mentionedOf σ) ≫ σ) = σ := by
    apply Hom.ext
    funext i
    exact trim_back view declared universes inh (mentionedOf σ) (σ.substitution i)
      (fun j member => (memKs j).mpr ⟨i, member⟩)
  refine initial_of_patternCovered facts roots heads algebra rigid complete inh ⟨?_, ?_⟩ ?_
  · exact Frames.models_comp principal.sound _
  · intro b f solved
    obtain ⟨r, fr⟩ := principal.factors b f solved
    refine ⟨r ≫ trimIn view declared universes (mentionedOf σ), fun t => ?_⟩
    have eq : (frames S.levels).comp (r ≫ trimIn view declared universes (mentionedOf σ))
        (trimOut view declared universes inh (mentionedOf σ) ≫ σ) = (frames S.levels).comp r σ := by
      change (r ≫ trimIn view declared universes (mentionedOf σ)) ≫
        (trimOut view declared universes inh (mentionedOf σ) ≫ σ) = r ≫ σ
      rw [Category.assoc, back]
    rw [eq]
    exact fr t
  · intro k
    have inKs : (mentionedOf σ).get k ∈ mentionedOf σ := List.get_mem _ k
    obtain ⟨i, ps, qs, c, c', K, dj, di, ups, uqs, uc, uc', below, injective, domains, cov⟩ :=
      covered _ ((memKs _).mp inKs)
    obtain ⟨hps, hc⟩ := famCode_inj ((declared _).symm.trans dj)
    have dk : Ctx.lookup (trimCtx view universes (mentionedOf σ)).raw k = famCode ps c := by
      change Ctx.lookup (famTeleOf view (mentionedOf σ)) k = _
      rw [lookup_famTeleOf, hps, hc]
    refine ⟨i, ps, qs, c, c', K, dk, di, ups, uqs, uc, uc', below, injective, domains, ?_⟩
    have moved := cov.substitute (trimOut view declared universes inh (mentionedOf σ)).typed
    rw [famCode_subst, subst_flexSide] at moved
    have image : (trimOut view declared universes inh (mentionedOf σ)).substitution ((mentionedOf σ).get k) =
        .var k := by
      change (if h : (mentionedOf σ).get k ∈ mentionedOf σ then Tm.var (keptAt _ h) else _) = _
      rw [dif_pos inKs]
      congr 1
      exact Fin.ext (List.get_idxOf (mentionedOf_nodup σ) k)
    rw [image] at moved
    exact moved

end Trimmed

end Miller

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
