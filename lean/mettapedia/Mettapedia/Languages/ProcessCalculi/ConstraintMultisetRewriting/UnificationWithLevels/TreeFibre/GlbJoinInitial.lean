import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.GlbJoinSolver
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.PatternInitiality

/-!
# Initial solutions of join answers

The join rules keep the left unknown `F` declared and send it, with the right one, to the η-expansion of the
redeclared unknown, whose domains are least upper bounds of theirs. So the answer is not an epimorphism as it stands:
`F` is a free choice of every factor. Deleting the unknowns the answer does not mention repairs this, as for glb groups
and Miller patterns; what the epimorphism needs is a new kind of covering.

* **Widening-covered** (`WideCovered`): an unknown `j` of the answer's telescope is covered when some unknown `i` of the
  store's telescope is sent, up to the fibre's equality, to the η-expansion of `j` at `i`'s declaration, whose domains
  lie below `j`'s and whose codomain lies above `j`'s.
* **Equality comes back up the domains** (`wide_equal`): two functions of `Π (x̄ : U_{p̄}). U_c` whose η-expansions are
  equal at `Π (x̄ : U_{q̄}). U_{c'}`, with `q̄` below `p̄` and `c` below `c'`, are equal at their own type. Under each binder
  the equality over the narrower declaration is reflected to the wider one (`equal_of_narrows`), and the codomain is
  lowered at the end (`universe_injective`).
* **Covered answers are epimorphisms** (`epi_of_wideCovered`); **the trimming theorem** for them
  (`initial_of_wideTrimmed`).
* **The run invariant** (`JoinInv`): every unknown the answer mentions, and both unknowns of every remaining equation,
  are covered. The join step keeps it for any codomain below both (`JoinInv.join`): an unknown kept is transported, and
  the redeclared one is covered through the left unknown's covering (`WideCovered.joined`).
* **Every solved run of the glb-join solver, trimmed, is the initial solution** (`glbJoin_solved_initial`), and every
  solvable store of its fragment has an initial solution (`glbJoin_initial`). The fragment contains the join-meet
  fragment, so join answers with a meet are covered too.
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

/-! ## A fact of syntax -/

/-- The free variables of an η-expansion are those of the expanded term. -/
theorem mem_support_etaExp : ∀ (k : Nat) {n : Nat} (t : Tm Head n) {j : Fin n},
    j ∈ (etaExp k t).support → j ∈ t.support
  | 0, _, _, _, h => h
  | k + 1, _, t, j, h => by
      change j ∈ (Tm.lam (etaExp k (.app (Presentation.rename wk t) (.var 0)))).support at h
      simp only [Tm.support, mem_outerSupport] at h
      have h' := mem_support_etaExp k _ h
      simp only [Tm.support, Finset.mem_union, Finset.mem_singleton] at h'
      rcases h' with h' | h'
      · rw [ContextualDependentSupport.support_rename, Finset.mem_image] at h'
        obtain ⟨a, ha, same⟩ := h'
        have aj : a = j := Fin.succ_injective _ same
        rw [← aj]
        exact ha
      · exact absurd h' (Fin.succ_ne_zero j)

/-! ## Widening-covered answers -/

section Covered

variable {S : Setting Head L}

/-- **`j` is covered by a widening of `σ`**: some unknown `i` of the store's telescope is sent, up to the fibre's
equality at its declaration, to the η-expansion of `j`, with `i`'s domains below `j`'s and `j`'s codomain below
`i`'s. -/
def WideCovered {Δ Θ : Context S.R} (σ : Δ ⟶ Θ) (j : Fin Δ.arity) : Prop :=
  ∃ (i : Fin Θ.arity) (ps qs : List Head) (c c' : Head),
    Ctx.lookup Δ.raw j = famCode ps c ∧ Ctx.lookup Θ.raw i = famCode qs c' ∧ AllUniverses S.R ps ∧
      AllUniverses S.R qs ∧ S.R.isUniverse c ∧ S.R.isUniverse c' ∧ S.R.cumulative c c' ∧
      List.Forall₂ S.R.cumulative qs ps ∧
      Equal S.R Δ.raw (σ.substitution i) (etaExp qs.length (.var j)) (famCode qs c')

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

include facts roots heads algebra rigid complete in
/-- **Equality comes back up the domains.** -/
theorem wide_equal : ∀ {qs ps : List Head}, List.Forall₂ S.R.cumulative qs ps →
    ∀ {n : Nat} {Γ : Ctx Head n} {f h : Tm Head n} {c c' : Head}, CtxFormed S.R Γ → AllUniverses S.R ps →
      AllUniverses S.R qs → S.R.isUniverse c → S.R.isUniverse c' → S.R.cumulative c c' →
      Typed S.R Γ f (famCode ps c) → Typed S.R Γ h (famCode ps c) →
      Equal S.R Γ (etaExp qs.length f) (etaExp qs.length h) (famCode qs c') → Equal S.R Γ f h (famCode ps c) := by
  intro qs ps domains
  induction domains with
  | nil =>
      intro n Γ f h c c' formed _ _ hc hc' _ tf th equal
      exact universe_injective facts roots heads algebra rigid complete formed hc hc' tf th equal
  | @cons q p qs' ps' qp _ ih =>
      intro n Γ f h c c' formed ups uqs hc hc' cc tf th equal
      change Equal S.R Γ (.lam (etaExp qs'.length (.app (Presentation.rename wk f) (.var 0))))
        (.lam (etaExp qs'.length (.app (Presentation.rename wk h) (.var 0)))) (.pi (.head q) (famCode qs' c'))
        at equal
      have opened := ContextualDependentUniverseInjective.equal_of_lam (S := S) facts formed equal
      have hp := ups.head
      have hq := uqs.head
      have formedP : CtxFormed S.R (.snoc Γ (.head p)) := formed.snoc (IsType.head_of_universe hp)
      have formedQ : CtxFormed S.R (.snoc Γ (.head q)) := formed.snoc (IsType.head_of_universe hq)
      have narrows : CtxNarrows S.R (.snoc Γ (.head p)) (.snoc Γ (.head q)) := .lower (CtxNarrows.refl Γ) qp
      have inner := ih formedQ ups.tail uqs.tail hc hc' cc (openK_typed tf qp) (openK_typed th qp) opened
      have wide := equal_of_narrows facts roots heads algebra rigid complete narrows formedP formedQ
        (openK_typed tf (S.levels.cumulative_refl hp)) (openK_typed th (S.levels.cumulative_refl hp)) inner
      exact Derivable.etaPi tf th wide

include facts roots heads algebra rigid complete in
/-- **Widening-covered answers are epimorphisms on terms.** -/
theorem epi_of_wideCovered {Δ Θ : Context S.R} (σ : Δ ⟶ Θ) (covered : ∀ j, WideCovered σ j) :
    EpiOnTerms (frames S.levels) σ := by
  intro b g h agree
  refine act_equal_of_substEq S.levels ⟨g.typed, fun j => ?_⟩
  obtain ⟨i, ps, qs, c, c', dj, di, ups, uqs, uc, uc', below, domains, cov⟩ := covered j
  have e := (agree (unknownTerm Θ i)).2
  change Equal S.R b.raw (Presentation.subst g.substitution (Presentation.subst σ.substitution (.var i)))
    (Presentation.subst h.substitution (Presentation.subst σ.substitution (.var i)))
    (Presentation.subst g.substitution (Presentation.subst σ.substitution (Ctx.lookup Θ.raw i))) at e
  rw [di, famCode_subst, famCode_subst] at e
  change Equal S.R b.raw (Presentation.subst g.substitution (σ.substitution i))
    (Presentation.subst h.substitution (σ.substitution i)) (famCode qs c') at e
  have cg := cov.substitute g.typed
  have ch := cov.substitute h.typed
  rw [famCode_subst, subst_etaExp] at cg ch
  have cg' : Equal S.R b.raw (Presentation.subst g.substitution (σ.substitution i))
      (etaExp qs.length (g.substitution j)) (famCode qs c') := cg
  have ch' : Equal S.R b.raw (Presentation.subst h.substitution (σ.substitution i))
      (etaExp qs.length (h.substitution j)) (famCode qs c') := ch
  have tg : Typed S.R b.raw (g.substitution j) (famCode ps c) := by
    have typed := g.typed j
    rw [dj, famCode_subst] at typed
    exact typed
  have th : Typed S.R b.raw (h.substitution j) (famCode ps c) := by
    have typed := h.typed j
    rw [dj, famCode_subst] at typed
    exact typed
  rw [dj, famCode_subst]
  exact wide_equal facts roots heads algebra rigid complete domains b.formed ups uqs uc uc' below tg th
    ((cg'.symm.trans e).trans ch')

include facts roots heads algebra rigid complete in
/-- **A principal answer that is widening-covered is the initial solution.** -/
theorem initial_of_wideCovered {Δ Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} {σ : Δ ⟶ Θ}
    (principal : (frames S.levels).Principal problem σ) (covered : ∀ j, WideCovered σ j) :
    InitialSolution (frames S.levels) problem σ :=
  Principal.initial principal (epi_of_wideCovered facts roots heads algebra rigid complete σ covered)

/-- **A fixed unknown is covered** by itself. -/
theorem fixed_wideCovered {Δ Θ : Context S.R} (σ : Δ ⟶ Θ) {i : Fin Θ.arity} {j : Fin Δ.arity}
    {ps : List Head} {c c' : Head} (fixed : σ.substitution i = .var j) (dj : Ctx.lookup Δ.raw j = famCode ps c)
    (di : Ctx.lookup Θ.raw i = famCode ps c') (ups : AllUniverses S.R ps) (uc : S.R.isUniverse c)
    (uc' : S.R.isUniverse c') (below : S.R.cumulative c c') : WideCovered σ j := by
  refine ⟨i, ps, ps, c, c', dj, di, ups, ups, uc, uc', below,
    List.forall₂_same.mpr (fun x hx => S.levels.cumulative_refl (ups x hx)), ?_⟩
  rw [fixed]
  have tj : Typed S.R Δ.raw (.var j) (famCode ps c) := by
    have typed := Derivable.var (R := S.R) (Γ := Δ.raw) j
    rw [dj] at typed
    exact typed
  have tj' : Typed S.R Δ.raw (.var j) (famCode ps c') :=
    Derivable.sub tj ((lowers_famCode ps uc uc' below).usable (famCode_isType ps ups uc Δ.formed)
      (famCode_isType ps ups uc' Δ.formed))
  exact (etaExp_equal ps Δ.formed tj').symm

variable (inh : Miller.Inhabitants S.R)

include facts roots heads algebra rigid complete in
/-- **Deleting the unknowns an answer does not mention makes a principal answer the initial solution**, when every
unknown it mentions is widening-covered. -/
theorem initial_of_wideTrimmed {Δ Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} {σ : Δ ⟶ Θ}
    (principal : (frames S.levels).Principal problem σ)
    (view : Fin Δ.arity → List Head × Head) (declared : ∀ j, Ctx.lookup Δ.raw j = famCode (view j).1 (view j).2)
    (universes : ∀ j, AllUniverses S.R (view j).1 ∧ S.R.isUniverse (view j).2)
    (covered : ∀ j, (∃ i, j ∈ (σ.substitution i).support) → WideCovered σ j) :
    InitialSolution (frames S.levels) problem
      (trimOut view declared universes inh (Miller.mentionedOf σ) ≫ σ) := by
  have memKs := Miller.mem_mentionedOf σ
  have back : trimIn view declared universes (Miller.mentionedOf σ) ≫
      (trimOut view declared universes inh (Miller.mentionedOf σ) ≫ σ) = σ := by
    apply Hom.ext
    funext i
    exact trim_back view declared universes inh (Miller.mentionedOf σ) (σ.substitution i)
      (fun j member => (memKs j).mpr ⟨i, member⟩)
  refine initial_of_wideCovered facts roots heads algebra rigid complete ⟨?_, ?_⟩ ?_
  · exact Frames.models_comp principal.sound _
  · intro b f solved
    obtain ⟨r, fr⟩ := principal.factors b f solved
    refine ⟨r ≫ trimIn view declared universes (Miller.mentionedOf σ), fun t => ?_⟩
    have eq : (frames S.levels).comp (r ≫ trimIn view declared universes (Miller.mentionedOf σ))
        (trimOut view declared universes inh (Miller.mentionedOf σ) ≫ σ) = (frames S.levels).comp r σ := by
      change (r ≫ trimIn view declared universes (Miller.mentionedOf σ)) ≫
        (trimOut view declared universes inh (Miller.mentionedOf σ) ≫ σ) = r ≫ σ
      rw [Category.assoc, back]
    rw [eq]
    exact fr t
  · intro k
    have inKs : (Miller.mentionedOf σ).get k ∈ Miller.mentionedOf σ := List.get_mem _ k
    obtain ⟨i, ps, qs, c, c', dj, di, ups, uqs, uc, uc', below, domains, cov⟩ :=
      covered _ ((memKs _).mp inKs)
    obtain ⟨hps, hc⟩ := famCode_inj ((declared _).symm.trans dj)
    have dk : Ctx.lookup (trimCtx view universes (Miller.mentionedOf σ)).raw k = famCode ps c := by
      change Ctx.lookup (famTeleOf view (Miller.mentionedOf σ)) k = _
      rw [lookup_famTeleOf, hps, hc]
    refine ⟨i, ps, qs, c, c', dk, di, ups, uqs, uc, uc', below, domains, ?_⟩
    have moved := cov.substitute (trimOut view declared universes inh (Miller.mentionedOf σ)).typed
    rw [famCode_subst, subst_etaExp] at moved
    have image : (trimOut view declared universes inh (Miller.mentionedOf σ)).substitution
        ((Miller.mentionedOf σ).get k) = .var k := by
      change (if h : (Miller.mentionedOf σ).get k ∈ Miller.mentionedOf σ then Tm.var (keptAt _ h) else _) = _
      rw [dif_pos inKs]
      congr 1
      exact Fin.ext (List.get_idxOf (Miller.mentionedOf_nodup σ) k)
    have moved' : Equal S.R (trimCtx view universes (Miller.mentionedOf σ)).raw
        (Presentation.subst (trimOut view declared universes inh (Miller.mentionedOf σ)).substitution
          (σ.substitution i))
        (etaExp qs.length ((trimOut view declared universes inh (Miller.mentionedOf σ)).substitution
          ((Miller.mentionedOf σ).get k))) (famCode qs c') := moved
    rw [image] at moved'
    exact moved'

end Covered

/-! ## The run invariant -/

section Invariant

variable {S : Setting Head L}

/-- **The run invariant**: every unknown the answer mentions, and both unknowns of every remaining equation, are
widening-covered by the answer. -/
structure JoinInv {Γ Θ : Context S.R} (σ : Θ ⟶ Γ) (remaining : EquationStore (TotalTerm Θ)) : Prop where
  covered : ∀ j, (∃ i, j ∈ (σ.substitution i).support) → WideCovered σ j
  occurs : ∀ e ∈ remaining, ∀ w : FlexK e, WideCovered σ w.left ∧ WideCovered σ w.right

/-- **At the start**, the identity covers every unknown by its η-expansion. -/
theorem JoinInv.pending {Γ : Context S.R} (families : Miller.Families Γ) (problem : EquationStore (TotalTerm Γ)) :
    JoinInv (𝟙 Γ) problem := by
  have all : ∀ j, WideCovered (𝟙 Γ) j := fun j => by
    obtain ⟨ps, c, dj, ups, uc⟩ := families j
    exact fixed_wideCovered (𝟙 Γ) rfl dj dj ups uc uc (S.levels.cumulative_refl uc)
  exact ⟨fun j _ => all j, fun _ _ w => ⟨all w.left, all w.right⟩⟩

/-- **Deleting the first equation keeps the invariant.** -/
theorem JoinInv.delete {Γ Θ : Context S.R} {σ : Θ ⟶ Γ} {e : Equation (TotalTerm Θ)}
    {rest : EquationStore (TotalTerm Θ)} (inv : JoinInv σ (e :: rest)) : JoinInv (𝟙 Θ ≫ σ) rest := by
  rw [Category.id_comp]
  exact ⟨inv.covered, fun e' member w => inv.occurs e' (List.mem_cons_of_mem _ member) w⟩

/-- **An unknown sent to an unknown keeps its covering**, when the new declaration has domains above and a codomain
no higher. -/
theorem WideCovered.transport {Γ Θ Θ' : Context S.R} {σ : Θ ⟶ Γ}
    (trans : ∀ {u v w : Head}, S.R.cumulative u v → S.R.cumulative v w → S.R.cumulative u w)
    (τ : Θ' ⟶ Θ) {k : Fin Θ.arity} {k' : Fin Θ'.arity} (cov : WideCovered σ k) (fixed : τ.substitution k = .var k')
    (decl : ∀ (ps : List Head) (c : Head), Ctx.lookup Θ.raw k = famCode ps c →
      ∃ ps₀ c₀, Ctx.lookup Θ'.raw k' = famCode ps₀ c₀ ∧ AllUniverses S.R ps₀ ∧ S.R.isUniverse c₀ ∧
        List.Forall₂ S.R.cumulative ps ps₀ ∧ S.R.cumulative c₀ c) :
    WideCovered (τ ≫ σ) k' := by
  obtain ⟨i, ps, qs, c, c', dk, di, _, uqs, _, uc', below, domains, eq⟩ := cov
  obtain ⟨ps₀, c₀, dk', ups₀, uc₀, dom₀, low⟩ := decl ps c dk
  refine ⟨i, ps₀, qs, c₀, c', dk', di, ups₀, uqs, uc₀, uc', trans low below, forall₂_trans trans domains dom₀, ?_⟩
  have moved := eq.substitute τ.typed
  rw [famCode_subst, subst_etaExp] at moved
  have moved' : Equal S.R Θ'.raw (Presentation.subst τ.substitution (σ.substitution i))
      (etaExp qs.length (τ.substitution k)) (famCode qs c') := moved
  rw [fixed] at moved'
  exact moved'

/-- **An unknown sent to the η-expansion of a redeclared one covers it**, when the redeclared unknown has domains above
and a codomain no higher. -/
theorem WideCovered.joined {Γ Θ Θ' : Context S.R} {σ : Θ ⟶ Γ} (algebra : CumulativeAlgebra S.R)
    (τ : Θ' ⟶ Θ) {F : Fin Θ.arity} {G : Fin Θ'.arity} {psF psJ : List Head} {cF m : Head} {len : Nat}
    (cov : WideCovered σ F) (declF : Ctx.lookup Θ.raw F = famCode psF cF)
    (declG : Ctx.lookup Θ'.raw G = famCode psJ m) (upsJ : AllUniverses S.R psJ) (hm : S.R.isUniverse m)
    (dom : List.Forall₂ S.R.cumulative psF psJ) (low : S.R.cumulative m cF) (length : len = psF.length)
    (image : τ.substitution F = etaExp len (.var G)) : WideCovered (τ ≫ σ) G := by
  obtain ⟨i, ps, qs, c, c', dF, di, _, uqs, _, uc', below, domains, eq⟩ := cov
  obtain ⟨hps, hc⟩ := famCode_inj (dF.symm.trans declF)
  subst hps
  subst hc
  have domainsJ : List.Forall₂ S.R.cumulative qs psJ := forall₂_trans algebra.trans domains dom
  refine ⟨i, psJ, qs, m, c', declG, di, upsJ, uqs, hm, uc', algebra.trans low below, domainsJ, ?_⟩
  have moved := eq.substitute τ.typed
  rw [famCode_subst, subst_etaExp] at moved
  have moved' : Equal S.R Θ'.raw (Presentation.subst τ.substitution (σ.substitution i))
      (etaExp qs.length (τ.substitution F)) (famCode qs c') := moved
  have lengths : len = qs.length := length.trans (forall₂_length domains).symm
  rw [image, lengths] at moved'
  have tG : Typed S.R Θ'.raw (.var G) (famCode psJ m) := by
    have typed := Derivable.var (R := S.R) (Γ := Θ'.raw) G
    rw [declG] at typed
    exact typed
  have tEta := raisedK_typed domainsJ uqs uc' (algebra.trans low below) Θ'.formed tG
  exact moved'.trans (etaExp_equal qs Θ'.formed tEta)

variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]

/-- **The join step keeps the invariant**, for any codomain below both: the kept unknowns are transported, and the
redeclared one is covered through the left unknown's covering. -/
theorem JoinInv.join {Γ Θ : Context S.R} {σ : Θ ⟶ Γ} {e : Equation (TotalTerm Θ)}
    {rest : EquationStore (TotalTerm Θ)} (algebra : CumulativeAlgebra S.R) (families : Miller.Families Θ)
    (shapes : ∀ e' ∈ rest, Nonempty (FlexK e')) (inv : JoinInv σ (e :: rest)) (v : FlexK e) {psJ : List Head}
    (joins : JoinsK S.R v.psl v.psr psJ) {m : Head} (hm : S.R.isUniverse m) (lowL : S.R.cumulative m v.cl)
    (lowR : S.R.cumulative m v.cr) :
    JoinInv (joinMKHom Θ families v joins hm lowL lowR ≫ σ) (joinStore families v joins hm lowL lowR rest) := by
  have keep : ∀ k, k ≠ v.left → k ≠ v.right → WideCovered σ k →
      WideCovered (joinMKHom Θ families v joins hm lowL lowR ≫ σ) k := by
    intro k neL neR cov
    refine WideCovered.transport algebra.trans (joinMKHom Θ families v joins hm lowL lowR) cov
      (joinKSub_ne _ _ _ neL neR) fun ps c dk => ?_
    obtain ⟨ups, uc⟩ := Miller.famFacts families dk
    exact ⟨ps, c, (joinedMK_ne Θ families v joins hm neR).trans dk, ups, uc,
      List.forall₂_same.mpr (fun x hx => S.levels.cumulative_refl (ups x hx)), S.levels.cumulative_refl uc⟩
  have head := inv.occurs e List.mem_cons_self v
  have newCovered : WideCovered (joinMKHom Θ families v joins hm lowL lowR ≫ σ) v.right :=
    WideCovered.joined algebra (joinMKHom Θ families v joins hm lowL lowR) head.1 v.declared_left
      (joinedMK_self Θ families v joins hm) joins.universes hm joins.left lowL (lengths_left v)
      (joinKSub_left _ _ _)
  constructor
  · rintro j ⟨i, hj⟩
    change j ∈ (Presentation.subst (joinKSub v.ps.length v.left v.right) (σ.substitution i)).support at hj
    obtain ⟨k, hk, hjk⟩ := Miller.support_subst_sub _ (joinKSub v.ps.length v.left v.right) hj
    by_cases hkl : k = v.left ∨ k = v.right
    · have image : joinKSub (Head := Head) v.ps.length v.left v.right k = etaExp v.ps.length (.var v.right) := by
        unfold joinKSub
        rw [if_pos hkl]
      rw [image] at hjk
      have hjr : j ∈ (Tm.var v.right : Tm Head _).support := mem_support_etaExp _ _ hjk
      have jr : j = v.right := by simpa [Tm.support] using hjr
      rw [jr]
      exact newCovered
    · have neL : k ≠ v.left := fun h => hkl (.inl h)
      have neR : k ≠ v.right := fun h => hkl (.inr h)
      rw [joinKSub_ne _ _ _ neL neR] at hjk
      have jk : j = k := by simpa [Tm.support] using hjk
      rw [jk]
      exact keep k neL neR (inv.covered k ⟨i, hk⟩)
  · intro e'' member u
    obtain ⟨e', inRest, rfl⟩ := List.mem_map.mp member
    obtain ⟨w⟩ := shapes e' inRest
    obtain ⟨t, tl, tr, _, _⟩ := join_viewK algebra families v joins hm lowL lowR w
    obtain ⟨ul, ur⟩ := FlexK.unique u t
    have old := inv.occurs e' (List.mem_cons_of_mem _ inRest) w
    have moved : ∀ Z, WideCovered σ Z → WideCovered (joinMKHom Θ families v joins hm lowL lowR ≫ σ)
        (joinVar v.left v.right Z) := by
      intro Z cov
      unfold joinVar
      split_ifs with hZ
      · exact newCovered
      · exact keep Z (fun h => hZ (.inl h)) (fun h => hZ (.inr h)) cov
    rw [ul, ur, tl, tr]
    exact ⟨moved w.left old.1, moved w.right old.2⟩

end Invariant

/-! ## The glb-join solver: solved runs are initial -/

section Rounds

variable {S : Setting Head L}
variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)
  (headsTyped : ∀ {h u u' : Head}, S.R.headTyping h u → S.R.headTyping h u' → u = u')
  (join : Head → Head → Option Head)
  (joinSound : ∀ {u v w : Head}, join u v = some w → S.R.isUniverse w ∧ IsLub S.R w u v)
  (meet : Head → Head → Option Head)
  (meetSound : ∀ {u v g : Head}, meet u v = some g → IsGlb S.R g u v)

/-- **Every round keeps the invariant.** -/
theorem glbJoinRoundK_inv {Γ Θ : Context S.R} {σ : Θ ⟶ Γ} {problem : EquationStore (TotalTerm Θ)}
    {update : Update S.levels problem}
    {smaller : ContextualDependentWorklist.Below (storeRank update.remaining) (storeRank problem)}
    (inside : InGlbJoinFragmentK problem) (inv : JoinInv σ problem)
    (progressed : glbJoinRoundK facts roots heads algebra rigid complete headsTyped join joinSound meet meetSound
      problem = .progress update smaller) :
    JoinInv (update.answer ≫ σ) update.remaining := by
  cases problem with
  | nil => cases progressed
  | cons e rest =>
      simp only [glbJoinRoundK] at progressed
      split_ifs at progressed with hfam
      split at progressed
      · rename_i d hd
        unfold stepGlbJoinK at progressed
        split_ifs at progressed with h1 h2
        · cases progressed
          exact inv.delete
        · split at progressed
          · split at progressed
            · cases progressed
              exact JoinInv.join algebra hfam (fun e' member => inside.shapes e' (List.mem_cons_of_mem _ member)) inv
                (viewOfK hd) _ _ _ _
            · cases progressed
          · cases progressed
      · cases progressed

/-- **The driver keeps the invariant and the fragment.** -/
theorem drive_joinInv {Γ : Context S.R} {original : EquationStore (TotalTerm Γ)} (fuel : Nat) :
    ∀ (state : Update S.levels original), JoinInv state.answer state.remaining →
      InGlbJoinFragmentK state.remaining → ∀ (final : Update S.levels original) (finished : final.remaining = []),
        drive (glbJoinSolverK facts roots heads algebra rigid complete headsTyped join joinSound meet meetSound)
            fuel state = .solved final finished →
          JoinInv final.answer final.remaining ∧ InGlbJoinFragmentK final.remaining := by
  induction fuel with
  | zero =>
      intro state _ _ final finished h
      cases h
  | succ fuel ih =>
      intro state inv inside final finished h
      rw [drive] at h
      cases ha : advance (glbJoinSolverK facts roots heads algebra rigid complete headsTyped join joinSound meet
        meetSound) state with
      | done outcome =>
          simp only [ha] at h
          unfold advance at ha
          split at ha
          · cases ha
            cases h
            exact ⟨inv, inside⟩
          · split at ha
            · cases ha
            · cases ha
              cases h
            · cases ha
              cases h
      | next next =>
          simp only [ha] at h
          unfold advance at ha
          split at ha
          · cases ha
          · split at ha
            · rename_i update smaller hround
              cases ha
              have inv' := glbJoinRoundK_inv facts roots heads algebra rigid complete headsTyped join joinSound meet
                meetSound inside inv hround
              have inside' := glbJoinRoundK_stable facts roots heads algebra rigid complete headsTyped join joinSound
                meet meetSound inside hround
              exact ih (state.then update) inv' inside' final finished h
            · cases ha
            · cases ha

variable (inh : Miller.Inhabitants S.R)

include facts roots heads algebra rigid complete headsTyped joinSound meetSound inh in
/-- **Every solved run of the glb-join solver ends with an answer whose trimming is the initial solution.** -/
theorem glbJoin_solved_initial {Θ : Context S.R} {original : EquationStore (TotalTerm Θ)}
    (inside : InGlbJoinFragmentK original) {fuel : Nat} {state : Update S.levels original}
    {finished : state.remaining = []}
    (solved : run (glbJoinSolverK facts roots heads algebra rigid complete headsTyped join joinSound meet meetSound)
      original fuel = .solved state finished) :
    ∃ (Δ : Context S.R) (answer : Δ ⟶ Θ), InitialSolution (frames S.levels) original answer := by
  obtain ⟨inv, insideFinal⟩ := drive_joinInv facts roots heads algebra rigid complete headsTyped join joinSound meet
    meetSound fuel (Update.pending S.levels original) (JoinInv.pending inside.families original) inside state
    finished solved
  choose ps c hd hu huc using insideFinal.families
  exact ⟨_, _, initial_of_wideTrimmed facts roots heads algebra rigid complete inh (state.completed finished)
    (fun j => (ps j, c j)) hd (fun j => ⟨hu j, huc j⟩) inv.covered⟩

variable (joinTotal : ∀ {u v : Head}, S.R.isUniverse u → S.R.isUniverse v → ∃ w, join u v = some w)
  (meetTotal : ∀ {u v : Head}, S.R.isUniverse u → S.R.isUniverse v → ∃ g, meet u v = some g)

include facts roots heads algebra rigid complete headsTyped joinSound meetSound inh joinTotal meetTotal in
/-- **Every store of the glb-join fragment has an initial solution**: the fragment's stores are never refuted, and a
solved run, trimmed, is initial. -/
theorem glbJoin_initial {Θ : Context S.R} {original : EquationStore (TotalTerm Θ)}
    (inside : InGlbJoinFragmentK original) :
    ∃ (Δ : Context S.R) (answer : Δ ⟶ Θ), InitialSolution (frames S.levels) original answer := by
  obtain ⟨fuel, decided⟩ := glbJoinK_decided facts roots heads algebra rigid complete headsTyped join joinSound meet
    meetSound joinTotal meetTotal inside
  rcases (decided fuel le_rfl).2 with ⟨state, finished, solved, _⟩ | ⟨absent, refuted⟩
  · exact glbJoin_solved_initial facts roots heads algebra rigid complete headsTyped join joinSound meet meetSound inh
      inside solved
  · exact absurd refuted (drive_ne_refuted
      (glbJoinSolverK facts roots heads algebra rigid complete headsTyped join joinSound meet meetSound)
      (fun problem absent =>
        glbJoinRoundK_ne_refuted facts roots heads algebra rigid complete headsTyped join joinSound meet meetSound
          problem absent)
      fuel _ absent)

end Rounds

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
