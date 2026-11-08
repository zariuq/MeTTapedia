import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramNested

/-!
# Unmatched calls as values: an absence query at the call's cut

MeTTa returns a call that no equation reduces as itself (`metta_call`: when the query
`(= atom $X)` has no answer, the result is the atom). Here a call `ap w K` whose data `w` unifies
with no left-hand side of the installed version `u` returns `w` to its continuation and cites `u`
(`UStep.unmatched`). That is a negative condition, so it cannot be an ordinary take-and-make
schema: it is one firing of the ordinary step with a **predicate query** (`absentQuery`).

* **The query** reads the call occurrence through the firing's solutions and asks whether some
  equation of `u`, renamed apart, unifies with its data (`matchedBy`); it must see nothing. Its
  region reads labels through solutions (`absentQuery_semantic`), so the firing is a firing of the
  ordinary step (`unmatchedFiring_semantic`), not of reflection.
* **Exactness at the cut** (`unmatched_fire`): the firing on a call occurrence and the version row
  is admitted exactly when no equation of `u` unifies with the call's data, and its result
  represents the call returned as its own value, with the citation of `u`.
* **Adequacy** (`usound`, `ucomplete`, `u_execution`): the machine with the unmatched rule and its
  translation (the compiled machine plus the unmatched firings) correspond both ways, and every
  translated run is a reference run in evaluation contexts (`uruns_unload`).
* **Why the cut is the right one** (`absence_stable`, `unmatched_cites`, `ucitations_persist`):
  every later instance of an unmatched call is still unmatched, so later two-way bindings never
  invalidate an answer given at the cut; the answer cites the version the firing read; citations are
  never removed; and a redefinition changes only the version row
  (`redefinition_keeps_other_rows`), so a later-installed equation does not change an earlier
  answer. What a later version would say is a recheck (`UnmatchedRecheck`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramNested

open Mettapedia.Logic.LP
open ProgramRows ProgramTranslation ProgramEquationsOpen ProgramEquations
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramEquations.Versions

/-! ## Matching, renamed apart -/

/-- A scope above every variable of a term. -/
def scopeBound (w : Tm) : ℕ := w.freeVars.sup (fun v => v.1) + 1

theorem bounded_scopeBound (w : Tm) : Bounded (scopeBound w) w := fun _ hv =>
  Nat.lt_succ_of_le (Finset.le_sup (f := fun v : ℕ × ℕ => v.1) hv)

/-- **Whether some equation's left-hand side, renamed apart, unifies with the data `w`.** -/
def matchedBy (eqs : List NEquation) (w : Tm) : Bool :=
  eqs.any fun e => (unifyTotal [(e.lhs.at (scopeBound w), w)]).isSome

/-- Move the variables of scope `m'` to scope `m`, and read the others through `σ`. -/
def rescope (δ σ : Subst rows) (m m' : ℕ) : Subst rows := fun v =>
  if v.1 = m' then δ (m, v.2) else δ.applyTerm (σ v)

theorem rescope_at (δ σ : Subst rows) (m m' : ℕ) : ∀ p : Pat,
    (rescope δ σ m m').applyTerm (p.at m') = δ.applyTerm (p.at m)
  | .var x => by
      show rescope δ σ m m' (m', x) = δ (m, x)
      rw [rescope, if_pos rfl]
  | .sym _ => rfl
  | .cell a b => by
      rw [Pat.at, apply_node, rescope_at δ σ m m' a, rescope_at δ σ m m' b, Pat.at, apply_node]

/-- **A unifier for an instance of the data gives a unifier for the data**, at any scope the
data does not name. -/
theorem unify_rescope {p : Pat} {m m' : ℕ} {w : Tm} (bounded : Bounded m' w) (σ : Subst rows)
    {δ : Subst rows} (unifies : Unifies δ [(p.at m, σ.applyTerm w)]) :
    Unifies (rescope δ σ m m') [(p.at m', w)] := by
  rw [unifies_single_iff] at unifies ⊢
  have right : (rescope δ σ m m').applyTerm w = δ.applyTerm (σ.applyTerm w) := by
    rw [← Subst.applyTerm_comp]
    refine Subst.applyTerm_congr fun v hv => ?_
    have lt := bounded v hv
    rw [rescope, if_neg (by omega)]
    rfl
  rw [rescope_at, right]
  exact unifies

theorem matchedBy_iff (eqs : List NEquation) (w : Tm) :
    matchedBy eqs w = true ↔ ∃ e ∈ eqs, ∃ δ : Subst rows, Unifies δ [(e.lhs.at (scopeBound w), w)] := by
  rw [matchedBy, List.any_eq_true]
  refine exists_congr fun e => and_congr Iff.rfl ?_
  rw [Option.isSome_iff_exists]
  constructor
  · rintro ⟨θ, accepted⟩
    exact ⟨θ, unifyTotal_sound _ θ accepted⟩
  · intro unifiable
    exact unifyTotal_complete unifiable

/-- **The query's test is the negative condition** at any scope the data does not name. -/
theorem unmatched_iff {eqs : List NEquation} {w : Tm} {n : ℕ} (bounded : Bounded n w) :
    matchedBy eqs w = false ↔ ∀ e ∈ eqs, ∀ δ : Subst rows, ¬ Unifies δ [(e.lhs.at n, w)] := by
  constructor
  · intro none e member δ unifies
    have moved := unify_rescope (m' := scopeBound w) (bounded_scopeBound w) (Subst.id rows)
      (δ := δ) (by rwa [Subst.applyTerm_id])
    have : matchedBy eqs w = true := (matchedBy_iff eqs w).mpr ⟨e, member, _, moved⟩
    rw [none] at this
    cases this
  · intro none
    cases h : matchedBy eqs w with
    | false => rfl
    | true =>
        obtain ⟨e, member, δ, unifies⟩ := (matchedBy_iff eqs w).mp h
        have moved := unify_rescope (m' := n) bounded (Subst.id rows) (δ := δ)
          (by rwa [Subst.applyTerm_id])
        exact absurd moved (none e member _)

/-- **An unmatched call stays unmatched under every later binding**: no equation unifies with any
instance of its data, at any scope. -/
theorem absence_stable {eqs : List NEquation} {w : Tm} {n : ℕ} (bounded : Bounded n w)
    (none : ∀ e ∈ eqs, ∀ δ : Subst rows, ¬ Unifies δ [(e.lhs.at n, w)]) (σ : Subst rows) (m : ℕ) :
    ∀ e ∈ eqs, ∀ δ : Subst rows, ¬ Unifies δ [(e.lhs.at m, σ.applyTerm w)] := fun e member _ unifies =>
  none e member _ (unify_rescope bounded σ unifies)

/-! ## The reference semantics with unmatched calls -/

/-- **The machine with unmatched calls as values**: every machine step, and a call whose data
unifies with no left-hand side of the installed version, returned as its own value. -/
inductive UStep (defs : Defs) : Multiset SRow × ℕ → Multiset SRow × ℕ → Prop
  | machine {s s' : Multiset SRow × ℕ} (step : KStep defs s s') : UStep defs s s'
  | unmatched (u : ℕ) (w : Tm) (K : List Frame) (F : Multiset SRow) (n : ℕ)
      (none : ∀ e ∈ defs u, ∀ δ : Subst rows, ¬ Unifies δ [(e.lhs.at n, w)]) :
      UStep defs (.ap w K ::ₘ .version u ::ₘ F, n)
        (.ret w K ::ₘ .citation u ::ₘ .version u ::ₘ F, n + 1)

/-- **Reduction in evaluation contexts with unmatched calls as values.** -/
inductive UCStep (defs : Defs) : Multiset Tm × ℕ → Multiset Tm × ℕ → Prop
  | reference {s s' : Multiset Tm × ℕ} (step : CStep defs s s') : UCStep defs s s'
  | unmatched (u : ℕ) (E : ECtx) (w : Tm) (F : Multiset Tm) (n m : ℕ) (fresh : n ≤ m)
      (none : ∀ e ∈ defs u, ∀ δ : Subst rows, ¬ Unifies δ [(e.lhs.at m, w)]) :
      UCStep defs (thread (encE (E.fill (.call (.val w)))) ::ₘ ver u ::ₘ F, n)
        (thread (encE (E.fill (.val w))) ::ₘ cite u ::ₘ ver u ::ₘ F, m + 1)

theorem ustep_unload {defs : Defs} {s s' : Multiset SRow × ℕ} (step : UStep defs s s') {m : ℕ}
    (le : m ≤ s.2) :
    ∃ m', m' ≤ s'.2 ∧ Relation.ReflGen (UCStep defs) (unloadAll s.1, m) (unloadAll s'.1, m') := by
  cases step with
  | machine step =>
      obtain ⟨m', le', path⟩ := kstep_unload step le
      exact ⟨m', le', Relation.ReflGen.mono (fun _ _ h => UCStep.reference h) _ _ path⟩
  | unmatched u w K F n none =>
      refine ⟨n + 1, le_rfl, .single ?_⟩
      simp only [unloadAll_cons]
      show UCStep defs (thread (encE (plug K (.call (.val w)))) ::ₘ ver u ::ₘ unloadAll F, m)
        (thread (encE (plug K (.val w))) ::ₘ cite u ::ₘ ver u ::ₘ unloadAll F, n + 1)
      rw [plug_ctxOf, plug_ctxOf]
      exact .unmatched u (ctxOf K) w (unloadAll F) m n le none

/-- **Every run with unmatched calls is a reference run of its unloading.** -/
theorem uruns_unload {defs : Defs} {s s' : Multiset SRow × ℕ}
    (run : Relation.ReflTransGen (UStep defs) s s') {m : ℕ} (le : m ≤ s.2) :
    ∃ m', m' ≤ s'.2 ∧ Relation.ReflTransGen (UCStep defs) (unloadAll s.1, m) (unloadAll s'.1, m') := by
  induction run with
  | refl => exact ⟨m, le, .refl⟩
  | tail _ step ih =>
      obtain ⟨m₁, le₁, path⟩ := ih
      obtain ⟨m₂, le₂, last⟩ := ustep_unload step le₁
      exact ⟨m₂, le₂, path.trans last.to_reflTransGen⟩

/-! ## The absence query and the unmatched firing -/

/-- The schema of an unmatched call at version `u`: take the call with its continuation, read the
version row, make the call's data returned to the continuation and the citation. -/
def unmatchedSchema (u : ℕ) : Schema :=
  ⟨[pap (.var 0) (.var 1)], [ptag 41 (.sym u)], [pret (.var 0) (.var 1), ptag 42 (.sym u)]⟩

open Classical in
/-- **The absence query**: the region is the call occurrence, read through the solution, when some
equation of version `u` unifies with its data; the query must see nothing. -/
noncomputable def absentQuery (defs : Defs) (u n : ℕ) :
    PredicateQueryAdmission.Query Tm (Subst rows) Occ :=
  ⟨fun σ t => if σ.applyTerm t = σ.applyTerm ((pap (.var 0) (.var 1)).at n) then
    matchedBy (defs u) (σ (n, 0)) else false, ∅⟩

/-- **The unmatched firing**: the schema's instance at scope `n`, with the absence query. -/
noncomputable def unmatchedFiring (defs : Defs) (u n : ℕ) (taken read : List Occ) :
    AnnotatedRuns.Firing Tm (Subst rows) Occ :=
  ⟨(unmatchedSchema u).rule n, [absentQuery defs u n],
    ⟨taken, read, madeAt n 0 (unmatchedSchema u).make⟩⟩

/-- **The absence query reads labels through solutions.** -/
theorem absentQuery_semantic (defs : Defs) (u n : ℕ) :
    Semantic.ReadsThroughSolutions A (absentQuery defs u n) := by
  intro σ s t solves
  have same : σ.applyTerm s = σ.applyTerm t := solves
  dsimp only [absentQuery]
  rw [same]

/-- **The unmatched firing is a firing of the ordinary step.** -/
theorem unmatchedFiring_semantic (defs : Defs) (u n : ℕ) (taken read : List Occ) :
    Semantic.IsSemantic A (unmatchedFiring defs u n taken read) := by
  intro query member
  rw [show (unmatchedFiring defs u n taken read).queries = [absentQuery defs u n] from rfl,
    List.mem_singleton] at member
  rw [member]
  exact absentQuery_semantic defs u n

theorem unmatched_valid_iff {defs : Defs} {u n : ℕ} {taken read : List Occ} {C : Config} :
    (unmatchedFiring defs u n taken read).Valid A Occ.label C ↔
      ((unmatchedSchema u).firing n taken read).Valid A Occ.label C ∧
        (absentQuery defs u n).Ask A
          ((((unmatchedSchema u).firing n taken read).selection).problem Occ.label
            ((unmatchedSchema u).rule n) C) Occ.label C.present := by
  constructor
  · intro valid
    exact ⟨⟨valid.firing, fun q h => by cases h⟩, valid.observations _ (List.mem_singleton_self _)⟩
  · rintro ⟨valid, ask⟩
    refine ⟨valid.firing, fun q h => ?_⟩
    rw [show (unmatchedFiring defs u n taken read).queries = [absentQuery defs u n] from rfl,
      List.mem_singleton] at h
    rw [h]
    exact ask

theorem unmatched_result (defs : Defs) (u n : ℕ) (taken read : List Occ) (C : Config) :
    (unmatchedFiring defs u n taken read).result Occ.label C =
      ((unmatchedSchema u).firing n taken read).result Occ.label C := rfl

/-- Appending pairs whose sides are equal and ground keeps a most general unifier. -/
theorem isMGU_append_ground {P : List (Tm × Tm)} {θ : Subst rows} (mgu : IsMGU P θ) {c : Tm}
    (ground : c.freeVars = ∅) : IsMGU (P ++ [(c, c)]) θ := by
  refine mgu.congr (fun δ => ?_) ?_
  · rw [unifies_append]
    simp [Unifies]
  · have : ∀ Q : List (Tm × Tm), eqVars (Q ++ [(c, c)]) = eqVars Q := by
      intro Q
      induction Q with
      | nil => simp [eqVars, ground]
      | cons e Q ih =>
          obtain ⟨s, t⟩ := e
          simp only [List.cons_append, eqVars, ih]
    exact (this P).symm

/-- **The unmatched firing at its cut, both ways**: on a call occurrence and the version row, it is
admitted exactly when no equation of the version unifies with the call's data, and its result
represents the call returned as its own value, citing the version. -/
theorem unmatched_fire {defs : Defs} {C : Config} {n : ℕ} {μ : Subst rows} (solved : SolvedForm C n μ)
    {Ws : Multiset SRow} (image : C.present.val.map (readAt μ) = Ws.map SRow.enc)
    {o o' : Occ} (oIn : o ∈ C.present) (o'In : o' ∈ C.present) (apart : o ≠ o')
    {u : ℕ} {w : Tm} {K : List Frame} {F : Multiset SRow}
    (shape : Ws = .ap w K ::ₘ .version u ::ₘ F)
    (reads : readAt μ o = (SRow.ap w K).enc) (reads' : readAt μ o' = (SRow.version u).enc) :
    ((unmatchedFiring defs u n [o] [o']).Valid A Occ.label C ↔
        ∀ e ∈ defs u, ∀ δ : Subst rows, ¬ Unifies δ [(e.lhs.at n, w)]) ∧
      ORepresents ((unmatchedFiring defs u n [o] [o']).result Occ.label C)
        ((.ret w K ::ₘ .citation u ::ₘ .version u ::ₘ F).map SRow.enc) (n + 1) := by
  have bounded := image_bounded solved image
  have sIn : SRow.ap w K ∈ Ws := by rw [shape]; simp
  have apBounded := bounded_node (bounded _ sIn)
  have vals : ∀ t ∈ [w, encK K], Bounded n t := by
    intro t h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact apBounded.1
    · exact apBounded.2
  set θ := matcher n [w, encK K] with hθ
  have callMGU : IsMGU [((pap (.var 0) (.var 1)).at n, Pat.fill [w, encK K] (pap (.var 0) (.var 1)))] θ :=
    matcher_isMGU vals (fun x hx => (show ∀ x < 2, x ∈ (pap (.var 0) (.var 1)).vars by decide) x hx)
      (fun x hx => (show ∀ x ∈ (pap (.var 0) (.var 1)).vars, x < 2 by decide) x hx)
  have mgu : IsMGU (schemaProblem (unmatchedSchema u) n μ [o] [o']) θ := by
    have problem : schemaProblem (unmatchedSchema u) n μ [o] [o'] =
        [((pap (.var 0) (.var 1)).at n, readAt μ o), ((ptag 41 (.sym u)).at n, readAt μ o')] := rfl
    rw [problem, reads, reads']
    exact isMGU_append_ground callMGU (by
      show Term.freeVars (tagged 41 (Term.const u)) = ∅
      rw [freeVars_tagged]
      rfl)
  obtain ⟨valid₀, solved', reading⟩ := ofire_at (r := unmatchedSchema u) (taken := [o]) (read := [o'])
    solved (List.nodup_singleton o) (fun x h => by rw [List.mem_singleton.mp h]; exact oIn)
    (fun x h => by rw [List.mem_singleton.mp h]; exact o'In)
    (fun x h h' => by
      rw [List.mem_singleton] at h h'
      exact apart (h.symm.trans h'))
    rfl rfl mgu
  -- the reading of the call and of the schema's scope variables at the composite solution
  have atCall : (θ ∘ₛ μ).applyTerm o.label = (SRow.ap w K).enc := by
    rw [Subst.applyTerm_comp, show μ.applyTerm o.label = readAt μ o from rfl, reads]
    exact matcher_fixes (bounded _ sIn)
  have atPattern : (θ ∘ₛ μ).applyTerm ((pap (.var 0) (.var 1)).at n) = (SRow.ap w K).enc := by
    rw [Subst.applyTerm_comp, solved.fixes_at, hθ,
      matcher_at (n := n) (vals := [w, encK K]) _ fun x hx => (show ∀ x ∈ (pap (.var 0) (.var 1)).vars, x < 2 by decide) x hx]
    rfl
  have data : (θ ∘ₛ μ) (n, 0) = w := by
    show θ.applyTerm (μ (n, 0)) = w
    rw [solved.fixes (n, 0) le_rfl, Subst.applyTerm_var, hθ, matcher, if_pos ⟨rfl, Nat.succ_pos 1⟩]
    rfl
  have atData : ∀ σ : Subst rows, σ.Absorbs (θ ∘ₛ μ) → σ (n, 0) = σ.applyTerm w := by
    intro σ absorbs
    rw [← absorbs (n, 0), data]
  refine ⟨⟨fun valid => ?_, fun none => ?_⟩, ?_⟩
  · -- admitted: at the composite solution the call is in the region unless nothing matches
    have ask := (unmatched_valid_iff.mp valid).2
    have models : A.Models (θ ∘ₛ μ) (((unmatchedSchema u).firing n [o] [o']).selection.problem
        Occ.label ((unmatchedSchema u).rule n) C) := (solved'.solutions _).mpr solved'.idempotent
    have empty := ask (θ ∘ₛ μ) models
    have outside : (absentQuery defs u n).region (θ ∘ₛ μ) o.label = false := by
      cases h : (absentQuery defs u n).region (θ ∘ₛ μ) o.label with
      | false => rfl
      | true =>
          have : o ∈ MeTTaCalculus.OccurrenceCommits.regionOf Occ.label C.present
              ((absentQuery defs u n).region (θ ∘ₛ μ)) := Finset.mem_filter.mpr ⟨oIn, h⟩
          have empty' : MeTTaCalculus.OccurrenceCommits.regionOf Occ.label C.present
              ((absentQuery defs u n).region (θ ∘ₛ μ)) = ∅ := empty
          rw [empty'] at this
          exact absurd this (Finset.notMem_empty o)
    dsimp only [absentQuery] at outside
    rw [if_pos (atCall.trans atPattern.symm), data] at outside
    exact (unmatched_iff apBounded.1).mp outside
  · -- nothing matches: no solution puts any occurrence in the region
    refine unmatched_valid_iff.mpr ⟨valid₀, fun σ models => ?_⟩
    have absorbs : σ.Absorbs (θ ∘ₛ μ) := (solved'.solutions σ).mp models
    refine Finset.eq_empty_of_forall_notMem fun o₂ member => ?_
    have inRegion := (Finset.mem_filter.mp member).2
    dsimp only [absentQuery, PredicateQueryAdmission.Query.atSolution] at inRegion
    split_ifs at inRegion with h
    have matched := inRegion
    rw [atData σ absorbs, matchedBy_iff] at matched
    obtain ⟨e, eIn, δ, unifies⟩ := matched
    exact none e eIn _ (unify_rescope apBounded.1 σ unifies)
  · refine ⟨θ ∘ₛ μ, solved', ?_⟩
    have erased : Ws.erase (.ap w K) = .version u ::ₘ F := by rw [shape, Multiset.erase_cons_head]
    rw [unmatched_result, reading, sdiff_singleton, erase_image image oIn sIn reads, erased]
    have fixedRest : ((SRow.version u ::ₘ F).map SRow.enc).map θ.applyTerm =
        (SRow.version u ::ₘ F).map SRow.enc := by
      rw [Multiset.map_map]
      refine Multiset.map_congr rfl fun s member => matcher_fixes (bounded s ?_)
      rw [shape]
      exact Multiset.mem_cons_of_mem member
    rw [fixedRest, add_comm]
    show ((([θ.applyTerm ((pret (.var 0) (.var 1)).at n), θ.applyTerm ((ptag 42 (.sym u)).at n)] :
      List Tm)) : Multiset Tm) + _ = _
    rw [hθ, matcher_at (n := n) (vals := [w, encK K]) _ fun x hx => (show ∀ x ∈ (pret (.var 0) (.var 1)).vars, x < 2 by decide) x hx,
      matcher_at (n := n) (vals := [w, encK K]) _ fun x hx => by simp [ptag, Pat.vars] at hx, pair_add]
    simp only [Multiset.map_cons]
    rfl


/-! ## The translation with unmatched calls, and its adequacy -/

/-- **Translated steps with unmatched calls**: the compiled machine's firings, and unmatched
firings with their absence query. -/
inductive UTranslated (defs : Defs) : Config × ℕ → Config × ℕ → Prop
  | machine {p q : Config × ℕ} (firing : Translated (kschema defs) p q) : UTranslated defs p q
  | unmatched {C : Config} {n : ℕ} (u : ℕ) (taken read : List Occ)
      (valid : (unmatchedFiring defs u n taken read).Valid A Occ.label C) :
      UTranslated defs (C, n) ((unmatchedFiring defs u n taken read).result Occ.label C, n + 1)

/-- **Every translated step is one admitted firing of the ordinary step**: its queries read labels
through solutions. -/
theorem utranslated_semantic {defs : Defs} {p q : Config × ℕ} (step : UTranslated defs p q) :
    ∃ f : AnnotatedRuns.Firing Tm (Subst rows) Occ, Semantic.IsSemantic A f ∧
      f.Valid A Occ.label p.1 ∧ q = (f.result Occ.label p.1, p.2 + 1) := by
  cases step with
  | machine firing =>
      cases firing with
      | fire i taken read valid => exact ⟨_, firing_isSemantic _ _ _ _, valid, rfl⟩
  | unmatched u taken read valid => exact ⟨_, unmatchedFiring_semantic defs u _ taken read, valid, rfl⟩

/-- **Soundness**: every step with unmatched calls, from represented rows, is one admitted firing. -/
theorem usound {defs : Defs} {C : Config} {Ws : Multiset SRow} {n : ℕ}
    (rep : ORepresents C (Ws.map SRow.enc) n) {s' : Multiset SRow × ℕ} (step : UStep defs (Ws, n) s') :
    ∃ D, UTranslated defs (C, n) (D, s'.2) ∧ ORepresents D (s'.1.map SRow.enc) s'.2 := by
  cases step with
  | machine step =>
      obtain ⟨D, firing, rep'⟩ := nested_sound rep step
      exact ⟨D, .machine firing, rep'⟩
  | unmatched u w K F n none =>
      obtain ⟨μ, solved, image⟩ := rep
      obtain ⟨o, oIn, reads⟩ := pick_source image (Multiset.mem_cons_self _ _)
      have erased : (C.present.erase o).val.map (readAt μ) = (SRow.version u ::ₘ F).map SRow.enc := by
        rw [erase_image image oIn (Multiset.mem_cons_self _ _) reads, Multiset.erase_cons_head]
      obtain ⟨o', o'In, reads'⟩ := pick_source erased (Multiset.mem_cons_self _ _)
      have ne : o ≠ o' := fun h => by
        rw [← h] at o'In
        exact Finset.notMem_erase o _ o'In
      obtain ⟨admitted, rep'⟩ := unmatched_fire (defs := defs) solved image oIn
        (Finset.mem_of_mem_erase o'In) ne rfl reads reads'
      exact ⟨_, .unmatched u [o] [o'] (admitted.mpr none), rep'⟩

/-- **Completeness**: every admitted translated firing from represented well-formed rows is one
step with unmatched calls. -/
theorem ucomplete {defs : Defs} {C : Config} {Ws : Multiset SRow} {n : ℕ}
    (rep : ORepresents C (Ws.map SRow.enc) n) (good : ∀ s ∈ Ws, s.Good) {q : Config × ℕ}
    (step : UTranslated defs (C, n) q) :
    ∃ Ws', UStep defs (Ws, n) (Ws', q.2) ∧ ORepresents q.1 (Ws'.map SRow.enc) q.2 := by
  cases step with
  | machine firing =>
      obtain ⟨Ws', step, rep'⟩ := nested_complete rep good firing
      exact ⟨Ws', .machine step, rep'⟩
  | unmatched u taken read valid =>
      obtain ⟨μ, solved, image⟩ := rep
      have valid₀ := (unmatched_valid_iff.mp valid).1
      obtain ⟨-, takenIn, readIn, apart, takeLength, readLength⟩ := valid_shape valid₀
      obtain ⟨o, rfl⟩ : ∃ o, taken = [o] := List.length_eq_one_iff.mp (by rw [← takeLength]; rfl)
      obtain ⟨o', rfl⟩ : ∃ o', read = [o'] := List.length_eq_one_iff.mp (by rw [← readLength]; rfl)
      have oIn := takenIn o (List.mem_singleton_self o)
      have o'In := readIn o' (List.mem_singleton_self o')
      have ne : o ≠ o' := fun h => apart o (List.mem_singleton_self o) (h ▸ List.mem_singleton_self o')
      obtain ⟨σ, unifies⟩ := valid_unifiable solved valid₀
      obtain ⟨s, sIn, reads⟩ := read_source image oIn
      have erased := erase_image image oIn sIn reads
      obtain ⟨s₂, s₂In, reads'⟩ := read_source erased (Finset.mem_erase.mpr ⟨fun h => ne h.symm, o'In⟩)
      have first : σ.applyTerm ((pap (.var 0) (.var 1)).at n) = σ.applyTerm s.enc := by
        have := unifies _ (show ((pap (.var 0) (.var 1)).at n, readAt μ o) ∈
          schemaProblem (unmatchedSchema u) n μ [o] [o'] by simp [schemaProblem, problem, unmatchedSchema])
        rwa [reads] at this
      have second : σ.applyTerm ((ptag 41 (.sym u)).at n) = σ.applyTerm s₂.enc := by
        have := unifies _ (show ((ptag 41 (.sym u)).at n, readAt μ o') ∈
          schemaProblem (unmatchedSchema u) n μ [o] [o'] by simp [schemaProblem, problem, unmatchedSchema])
        rwa [reads'] at this
      obtain ⟨tag, -⟩ := tag_forced (k := 122) first
      obtain ⟨w, K, rfl⟩ := good_ap (good s sIn) tag
      obtain ⟨tag₂, body₂⟩ := tag_forced (k := 41) second
      obtain ⟨u₂, rfl⟩ := good_version (good s₂ (Multiset.mem_of_mem_erase s₂In)) tag₂
      have uu : u = u₂ := const_forced body₂
      subst uu
      have shape : Ws = .ap w K ::ₘ .version u ::ₘ (Ws.erase (.ap w K)).erase (.version u) := by
        rw [Multiset.cons_erase s₂In, Multiset.cons_erase sIn]
      obtain ⟨admitted, rep'⟩ := unmatched_fire (defs := defs) solved image oIn o'In ne shape reads reads'
      refine ⟨_, ?_, rep'⟩
      have step := UStep.unmatched (defs := defs) u w K ((Ws.erase (.ap w K)).erase (.version u)) n
        (admitted.mp valid)
      rw [← shape] at step
      exact step

theorem ustep_good {defs : Defs} {s s' : Multiset SRow × ℕ} (step : UStep defs s s')
    (good : ∀ r ∈ s.1, r.Good) : ∀ r ∈ s'.1, r.Good := by
  cases step with
  | machine step => exact kstep_good step good
  | unmatched u w K F n none =>
      intro r member
      simp only [Multiset.mem_cons] at member
      rcases member with rfl | rfl | rfl | member
      · trivial
      · trivial
      · trivial
      · exact good r (by simp [member])

theorem uruns_sound {defs : Defs} {s s' : Multiset SRow × ℕ}
    (run : Relation.ReflTransGen (UStep defs) s s') {C : Config}
    (rep : ORepresents C (s.1.map SRow.enc) s.2) :
    ∃ D, Relation.ReflTransGen (UTranslated defs) (C, s.2) (D, s'.2) ∧
      ORepresents D (s'.1.map SRow.enc) s'.2 := by
  induction run with
  | refl => exact ⟨C, .refl, rep⟩
  | @tail b c _ step ih =>
      obtain ⟨D, path, rep'⟩ := ih
      obtain ⟨W, m⟩ := b
      obtain ⟨E, firing, rep''⟩ := usound rep' step
      exact ⟨E, path.tail firing, rep''⟩

theorem uruns_complete {defs : Defs} {p q : Config × ℕ}
    (run : Relation.ReflTransGen (UTranslated defs) p q) {Ws : Multiset SRow}
    (rep : ORepresents p.1 (Ws.map SRow.enc) p.2) (good : ∀ s ∈ Ws, s.Good) :
    ∃ Ws', Relation.ReflTransGen (UStep defs) (Ws, p.2) (Ws', q.2) ∧
      ORepresents q.1 (Ws'.map SRow.enc) q.2 ∧ ∀ s ∈ Ws', s.Good := by
  induction run with
  | refl => exact ⟨Ws, .refl, rep, good⟩
  | @tail b c _ firing ih =>
      obtain ⟨Ws', path, rep', good'⟩ := ih
      obtain ⟨D, m⟩ := b
      obtain ⟨Ws'', step, rep''⟩ := ucomplete rep' good' firing
      exact ⟨Ws'', path.tail step, rep'', ustep_good step good'⟩

/-- **Adequacy with unmatched calls as values, on the ordinary step.** -/
theorem u_execution (defs : Defs) (l : List SRow) (good : ∀ s ∈ l, s.Good)
    (bounded : ∀ s ∈ l, Bounded 1 s.enc) (Ws : Multiset SRow) (m : ℕ) :
    (Relation.ReflTransGen (UStep defs) ((l : Multiset SRow), 1) (Ws, m) →
      ∃ D, Relation.ReflTransGen (UTranslated defs) (openInitial (l.map SRow.enc), 1) (D, m) ∧
        ORepresents D (Ws.map SRow.enc) m) ∧
    (∀ D, Relation.ReflTransGen (UTranslated defs) (openInitial (l.map SRow.enc), 1) (D, m) →
      ∃ Ws', Relation.ReflTransGen (UStep defs) ((l : Multiset SRow), 1) (Ws', m) ∧
        ORepresents D (Ws'.map SRow.enc) m) := by
  have rep : ORepresents (openInitial (l.map SRow.enc)) (((l : Multiset SRow)).map SRow.enc) 1 := by
    rw [Multiset.map_coe]
    exact openInitial_represents _ fun t member => by
      obtain ⟨s, sIn, rfl⟩ := List.mem_map.mp member
      exact bounded s sIn
  refine ⟨fun run => uruns_sound run rep, fun D run => ?_⟩
  obtain ⟨Ws', path, rep', -⟩ := uruns_complete run rep fun s member => good s member
  exact ⟨Ws', path, rep'⟩

/-- **Translated runs with unmatched calls are reference runs in evaluation contexts.** -/
theorem u_translated_is_reference (defs : Defs) (l : List SRow) (good : ∀ s ∈ l, s.Good)
    (bounded : ∀ s ∈ l, Bounded 1 s.enc) (D : Config) (m : ℕ)
    (run : Relation.ReflTransGen (UTranslated defs) (openInitial (l.map SRow.enc), 1) (D, m)) :
    ∃ Ws', ORepresents D (Ws'.map SRow.enc) m ∧ ∃ m', m' ≤ m ∧
      Relation.ReflTransGen (UCStep defs) (unloadAll (l : Multiset SRow), 1) (unloadAll Ws', m') := by
  obtain ⟨Ws', path, rep⟩ := (u_execution defs l good bounded 0 m).2 D run
  obtain ⟨m', le, reference⟩ := uruns_unload path (le_refl 1)
  exact ⟨Ws', rep, m', le, reference⟩

/-! ## The cut, versions and citations -/

/-- **The absence query is asked at its own cut**: admission of an unmatched firing depends only on
the solutions of the configuration's knowledge and its present occurrences. -/
theorem absence_at_cut {defs : Defs} {u n : ℕ} {taken read : List Occ} {C D : Config}
    (same : GuardFreeProcessOrders.SameUpTo A C D) :
    (unmatchedFiring defs u n taken read).Valid A Occ.label C ↔
      (unmatchedFiring defs u n taken read).Valid A Occ.label D :=
  AnnotatedRuns.Firing.valid_congr A Occ.label same

/-- **The recheck of an unmatched answer against a version**: no equation of that version unifies
with the answer's data. -/
def UnmatchedRecheck (defs : Defs) (u n : ℕ) (w : Tm) : Prop :=
  ∀ e ∈ defs u, ∀ δ : Subst rows, ¬ Unifies δ [(e.lhs.at n, w)]

theorem subst_eq_citation {s : SRow} {θ : Subst rows} {u : ℕ} (h : s.subst θ = .citation u) :
    s = .citation u := by
  cases s <;> first | rfl | exact h | cases h

/-- **Every new citation is made by a step that read the version it cites.** -/
theorem ucitation_reads_version {defs : Defs} {s s' : Multiset SRow × ℕ} (step : UStep defs s s')
    {u : ℕ} (made : SRow.citation u ∈ s'.1) (fresh : SRow.citation u ∉ s.1) : SRow.version u ∈ s.1 := by
  cases step with
  | machine step =>
      cases step with
      | val t K F n | pair a b K F n | call a K F n | left v b K F n | right v w K F n | arg w K F n =>
          rcases Multiset.mem_cons.mp made with h | h
          · cases h
          · exact absurd (Multiset.mem_cons_of_mem h) fresh
      | apply u' j w K F n θ mgu =>
          simp only [Multiset.mem_cons] at made
          rcases made with h | h | h | h
          · cases h
          · cases h
            simp
          · cases h
          · obtain ⟨r, rIn, hr⟩ := Multiset.mem_map.mp h
            rw [subst_eq_citation hr] at rIn
            exact absurd (by simp [rIn]) fresh
      | redefine u₀ u' F n =>
          simp only [Multiset.mem_cons] at made
          rcases made with h | h | h
          · cases h
          · cases h
          · exact absurd (by simp [h]) fresh
  | unmatched u' w K F n none =>
      simp only [Multiset.mem_cons] at made
      rcases made with h | h | h | h
      · cases h
      · cases h
        simp
      · cases h
      · exact absurd (by simp [h]) fresh

/-- **No step removes a citation.** -/
theorem ucitations_persist {defs : Defs} {s s' : Multiset SRow × ℕ} (step : UStep defs s s')
    {u : ℕ} (present : SRow.citation u ∈ s.1) : SRow.citation u ∈ s'.1 := by
  cases step with
  | machine step =>
      cases step with
      | val t K F n | pair a b K F n | call a K F n | left v b K F n | right v w K F n | arg w K F n =>
          rcases Multiset.mem_cons.mp present with h | h
          · cases h
          · exact Multiset.mem_cons_of_mem h
      | apply u' j w K F n θ mgu =>
          simp only [Multiset.mem_cons] at present ⊢
          rcases present with h | h | h
          · cases h
          · cases h
          · exact .inr (.inr (.inr (Multiset.mem_map.mpr ⟨_, h, rfl⟩)))
      | redefine u₀ u' F n =>
          simp only [Multiset.mem_cons] at present ⊢
          rcases present with h | h | h
          · cases h
          · cases h
          · exact .inr (.inr h)
  | unmatched u' w K F n none =>
      simp only [Multiset.mem_cons] at present ⊢
      rcases present with h | h | h
      · cases h
      · cases h
      · exact .inr (.inr (.inr h))

/-- **A redefinition changes only the version row**: every other row, an earlier answer and its
citation included, stays as it is. -/
theorem redefinition_keeps_other_rows {defs : Defs} {u u' : ℕ} {F : Multiset SRow} {n : ℕ} :
    UStep defs (.redef u' ::ₘ .version u ::ₘ F, n) (.finished ::ₘ .version u' ::ₘ F, n + 1) :=
  .machine (.redefine u u' F n)

#print axioms bounded_scopeBound
#print axioms unify_rescope
#print axioms matchedBy_iff
#print axioms unmatched_iff
#print axioms absence_stable
#print axioms ustep_unload
#print axioms uruns_unload
#print axioms absentQuery_semantic
#print axioms unmatchedFiring_semantic
#print axioms unmatched_valid_iff
#print axioms isMGU_append_ground
#print axioms unmatched_fire
#print axioms utranslated_semantic
#print axioms usound
#print axioms ucomplete
#print axioms ustep_good
#print axioms uruns_sound
#print axioms uruns_complete
#print axioms u_execution
#print axioms u_translated_is_reference
#print axioms absence_at_cut
#print axioms subst_eq_citation
#print axioms ucitation_reads_version
#print axioms ucitations_persist
#print axioms redefinition_keeps_other_rows

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramNested
