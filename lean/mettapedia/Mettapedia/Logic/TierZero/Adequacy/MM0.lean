import Mettapedia.Logic.TierZero.Adequacy.MM0Complete

/-!
# MM0 adequacy of the tier-0 kernel on thinned terms

**The theorem** (`kernel_accepts_iff_derives`): for an MM0 environment whose statements mention
only their own formals (`MM0Env.WF`) and a context whose regular variables depend on bound
variables only, the kernel on thinned terms (`Claim.verdictR`) accepts the MM0 claim of `Γ ⊢ H ⇒ e`
with some proof exactly when Mettapedia's MM0 kernel derives `e` (`Derives`).

The MM0 claim (`mm0Claim`) has the context's variables as its formals: a bound variable is a
**scope** formal (a fresh name others may depend on), a regular variable is a **name over its
dependencies' names**; its hypotheses are the binders' sort judgments and MM0's hypotheses.

The rules generated from an MM0 environment are determined (`rules_determined`): each formal is
bound by a judgment premise, and the independence and freshness conditions come after them.

`Controls`: a theory with a bound sort and a binding constructor `all`; `nf` (`φ → ∀x φ` for a `φ`
independent of `x`) is accepted for a `ψ` that does not depend on `x`, and refused for a `φ` that
does (the independence check asks whether the formula's value mentions `x`'s name).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.MM0

open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources
open Mettapedia.Logic.TierZero
open Mettapedia.Logic.TierZero.Kernel2
open Mettapedia.Languages.MM0.Kernel

/-! ## Variables of patterns -/

theorem mem_patsVars {k : ℕ} : ∀ {ps : List Pat}, k ∈ patsVars ps ↔ ∃ p ∈ ps, k ∈ p.vars
  | [] => by simp [patsVars]
  | p :: ps => by
      rw [patsVars_cons, Finset.mem_union, mem_patsVars]
      simp

theorem mem_kindsVars {k : ℕ} : ∀ {ks : List Kind}, k ∈ kindsVars ks ↔ ∃ kd ∈ ks, k ∈ kd.vars
  | [] => by simp [kindsVars]
  | kd :: ks => by
      rw [kindsVars_cons, Finset.mem_union, mem_kindsVars]
      simp

theorem vars_pjd (h : String) (ps : List Pat) {k : ℕ} :
    k ∈ (pjd h ps).vars ↔ ∃ p ∈ ps, k ∈ p.vars := by
  have : ∀ qs : List Pat, k ∈ TreePatFields.vars (pflds qs) ↔ ∃ p ∈ qs, k ∈ p.vars := by
    intro qs
    induction qs with
    | nil => simp [pflds, TreePatFields.vars]
    | cons q qs ih => simp [pflds, TreePatFields.vars, ih]
  simp [pjd, pex, TreePat.vars, this, psym, TreePatFields.vars]

theorem vars_pv (v k : ℕ) : k ∈ (pv v).vars ↔ k = v := by simp [pv, TreePat.vars]

theorem vars_pnum (s k : ℕ) : k ∉ (pnum s).vars := by simp [pnum, TreePat.vars, TreePatFields.vars]

theorem vars_patOf {k : ℕ} : ∀ p : Preterm, k ∈ (patOf p).vars ↔ Preterm.Occurs k p
  | .var i => by
      simp only [patOf, TreePat.vars, Finset.mem_singleton]
      exact ⟨fun h => h ▸ .var, fun h => by cases h; rfl⟩
  | .term c => by
      rw [patOf]
      exact ⟨fun h => absurd h (vars_pnum c k), fun h => by cases h⟩
  | .app f a => by
      simp only [patOf, pex, TreePat.vars, pflds, TreePatFields.vars, Finset.mem_union,
        Finset.notMem_empty, or_false]
      rw [vars_patOf f, vars_patOf a]
      exact ⟨fun h => h.elim .function .argument, fun h => by cases h <;> simp_all⟩

theorem occurs_spine {k c : ℕ} : ∀ (off n : ℕ),
    Preterm.Occurs k (Preterm.applyArgs (.term c) (varsP off n)) → off ≤ k ∧ k < off + n
  | off, 0, h => by simp [varsP] at h; cases h
  | off, n + 1, h => by
      rw [show varsP off (n + 1) = varsP off n ++ [.var (off + n)] by
        simp [varsP, List.range'_concat]] at h
      rw [Preterm.applyArgs_append] at h
      simp only [Preterm.applyArgs] at h
      cases h with
      | function h' => have := occurs_spine off n h'; omega
      | argument h' => cases h'; omega

theorem patOf_vars_sub {n : ℕ} {p : Preterm} (h : Preterm.VarsBelow n p) : (patOf p).vars ⊆ Finset.range n := by
  intro k m
  rw [vars_patOf] at m
  exact Finset.mem_range.mpr (h.occurs_lt m)

/-! ## Determined rules -/

theorem detKinds_append (D : Finset ℕ) :
    ∀ (ks ks' : List Kind), detKinds (ks ++ ks') D = (detKinds ks D).bind fun D' => detKinds ks' D'
  | [], ks' => rfl
  | .consume q :: ks, ks' => by simp only [List.cons_append, detKinds]; exact detKinds_append _ ks ks'
  | .check ins ok :: ks, ks' => by
      simp only [List.cons_append, detKinds]
      split
      · exact detKinds_append _ ks ks'
      · rfl
  | .compute r ins f :: ks, ks' => by
      simp only [List.cons_append, detKinds]
      split
      · exact detKinds_append _ ks ks'
      · rfl
  | .each l x p :: ks, ks' => by
      simp only [List.cons_append, detKinds]
      split
      · exact detKinds_append _ ks ks'
      · rfl

theorem detKinds_consumes : ∀ (qs : List Pat) (D : Finset ℕ),
    detKinds (qs.map Kind.consume) D = some (D ∪ patsVars qs)
  | [], D => by simp [detKinds, patsVars]
  | q :: qs, D => by
      simp only [List.map_cons, detKinds, detKinds_consumes qs, patsVars_cons, Finset.union_assoc]

theorem detKinds_checks (D : Finset ℕ) :
    ∀ (ks : List Kind), (∀ k ∈ ks, ∃ ins ok, k = Kind.check ins ok ∧ patsVars ins ⊆ D) →
      detKinds ks D = some D
  | [], _ => rfl
  | k :: ks, h => by
      obtain ⟨ins, ok, rfl, sub⟩ := h k List.mem_cons_self
      simp only [detKinds, sub, ↓reduceIte]
      exact detKinds_checks D ks fun k' m => h k' (List.mem_cons_of_mem _ m)

/-- **A rule whose premises are judgments binding every formal, then checks on formals, is
determined.** -/
theorem determined_of {ru : Rule} (qs : List Pat) (cs : List Kind)
    (hk : ru.kinds = qs.map Kind.consume ++ cs)
    (qsIn : ∀ q ∈ qs, q.vars ⊆ Finset.range ru.nformals)
    (cover : Finset.range ru.nformals ⊆ patsVars qs)
    (csOk : ∀ k ∈ cs, ∃ ins ok, k = Kind.check ins ok ∧ patsVars ins ⊆ Finset.range ru.nformals)
    (conclIn : ru.concl.vars ⊆ Finset.range ru.nformals) : ru.determinedB = true := by
  have pv : patsVars qs ⊆ Finset.range ru.nformals := by
    intro v m
    obtain ⟨q, mq, mv⟩ := mem_patsVars.mp m
    exact qsIn q mq mv
  have eqD : patsVars qs = Finset.range ru.nformals := Finset.Subset.antisymm pv cover
  have det : detKinds ru.kinds ∅ = some (patsVars qs) := by
    rw [hk, detKinds_append, detKinds_consumes, Finset.empty_union]
    simp only [Option.bind_some]
    exact detKinds_checks _ cs fun k m => by
      obtain ⟨ins, ok, rfl, sub⟩ := csOk k m
      exact ⟨ins, ok, rfl, eqD ▸ sub⟩
  unfold Rule.determinedB
  simp only [det, Bool.and_eq_true, decide_eq_true_eq]
  have past : ru.kinds.all (Kind.localPast ru.nformals) = true := by
    rw [List.all_eq_true]
    intro k mk
    rw [hk] at mk
    rcases List.mem_append.mp mk with mk | mk
    · obtain ⟨q, _, rfl⟩ := List.mem_map.mp mk
      rfl
    · obtain ⟨ins, ok, rfl, _⟩ := csOk _ mk
      rfl
  refine ⟨⟨⟨?_, conclIn⟩, past⟩, eqD ▸ Finset.Subset.refl _⟩
  intro v m
  obtain ⟨kd, mk, mv⟩ := mem_kindsVars.mp m
  rw [hk] at mk
  rcases List.mem_append.mp mk with mk | mk
  · obtain ⟨q, mq, rfl⟩ := List.mem_map.mp mk
    exact qsIn q mq mv
  · obtain ⟨ins, ok, rfl, sub⟩ := csOk _ mk
    exact sub mv

/-- The patterns of the fit premises. -/
def fitPats (off : ℕ) (Φ : Context) : List Pat := (Φ.zipIdx off).map fun x => fitPat x.1 x.2

theorem fits_kinds (off : ℕ) (Φ : Context) : (fits off Φ).map Premise.kind = (fitPats off Φ).map Kind.consume := by
  simp [fits, fitPats, Premise.kind, Function.comp_def]

theorem vars_fitPat (b : Binder) (k v : ℕ) : v ∈ (fitPat b k).vars ↔ v = k := by
  cases b <;> simp [fitPat, bvP, tyP, vars_pjd, vars_pv, TreePat.vars, pnum,
    TreePatFields.vars]

theorem mem_fitPats_vars {off : ℕ} {Φ : Context} {v : ℕ} :
    v ∈ patsVars (fitPats off Φ) ↔ off ≤ v ∧ v < off + Φ.length := by
  rw [mem_patsVars]
  simp only [fitPats, List.mem_map]
  constructor
  · rintro ⟨_, ⟨⟨b, k⟩, mk, rfl⟩, mv⟩
    rw [vars_fitPat] at mv
    subst mv
    have := List.mem_zipIdx mk
    omega
  · rintro ⟨le, lt⟩
    obtain ⟨b, hb⟩ : ∃ b, Φ[v - off]? = some b := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    refine ⟨fitPat b v, ⟨(b, v), List.mem_zipIdx_iff_le_and_getElem?_sub.mpr ⟨le, hb⟩, rfl⟩, ?_⟩
    rw [vars_fitPat]

/-- MM0 statements mention only their own formals. -/
structure MM0Env.WF (E : MM0Env) : Prop where
  thms : ∀ t d, E.thms t = some d →
    (∀ h ∈ d.hypotheses, Preterm.VarsBelow d.arguments.length h) ∧
      Preterm.VarsBelow d.arguments.length d.conclusion
  defs : ∀ c d b, E.sig c = some d → E.defs c = some b →
    Preterm.VarsBelow (d.arguments.length + b.dummies.length) b.expression

theorem absent_check (p q : ℕ) : ∃ ins ok, (Premise.absent (pv p) (pv q)).kind = Kind.check ins ok ∧
    patsVars ins = {p, q} := by
  refine ⟨[pv p, pv q], _, rfl, ?_⟩
  ext v
  simp [patsVars, vars_pv]

/-- **Every rule of a well-formed MM0 environment is determined.** -/
theorem rules_determined {E : MM0Env} (wf : E.WF) : EnvDetermined (rules E) := by
  intro r ru hr
  cases r with
  | con c =>
      simp only [rules, Option.map_eq_some_iff] at hr
      obtain ⟨d, hd, rfl⟩ := hr
      refine determined_of (fitPats 0 d.arguments) [] (by simp [conRule, Rule.kinds, fits_kinds])
        (fun q mq v mv => ?_) (fun v mv => ?_) (by simp) ?_
      · simp only [fitPats, List.mem_map] at mq
        obtain ⟨⟨b, k⟩, mk, rfl⟩ := mq
        rw [vars_fitPat] at mv; subst mv
        simpa [conRule] using (List.mem_zipIdx mk).2.1
      · simpa [mem_fitPats_vars, conRule] using mv
      · intro v mv
        simp only [conRule, tyP, vars_pjd, List.mem_cons, List.not_mem_nil, or_false] at mv
        obtain ⟨p, rfl | rfl | ⟨⟩, mv⟩ := mv
        · exact absurd mv (vars_pnum _ _)
        · rw [vars_patOf] at mv
          simpa [conRule] using (occurs_spine 0 _ mv).2
  | thm t =>
      simp only [rules, Option.map_eq_some_iff] at hr
      obtain ⟨d, hd, rfl⟩ := hr
      obtain ⟨hyps, concl⟩ := wf.thms t d hd
      refine determined_of (fitPats 0 d.arguments ++ d.hypotheses.map fun h => pfP (patOf h))
        ((indep d.arguments).map Premise.kind) ?_ (fun q mq => ?_) (fun v mv => ?_) (fun k mk => ?_) ?_
      · simp [thmRule, Rule.kinds, fits_kinds, Premise.kind, Function.comp_def]
      · rcases List.mem_append.mp mq with mq | mq
        · simp only [fitPats, List.mem_map] at mq
          obtain ⟨⟨b, k⟩, mk, rfl⟩ := mq
          intro v mv
          rw [vars_fitPat] at mv; subst mv
          simpa [thmRule] using (List.mem_zipIdx mk).2.1
        · obtain ⟨h, mh, rfl⟩ := List.mem_map.mp mq
          intro v mv
          simp only [pfP, vars_pjd, List.mem_cons, List.not_mem_nil, or_false] at mv
          obtain ⟨p, rfl, mv⟩ := mv
          exact patOf_vars_sub (hyps h mh) mv
      · rw [mem_patsVars]
        have : v ∈ patsVars (fitPats 0 d.arguments) := by simpa [mem_fitPats_vars, thmRule] using mv
        obtain ⟨p, mp, pv'⟩ := mem_patsVars.mp this
        exact ⟨p, List.mem_append_left _ mp, pv'⟩
      · obtain ⟨pr, mpr, rfl⟩ := List.mem_map.mp mk
        obtain ⟨p, q, s, b', rfl, hp, hq, -⟩ := indep_decode mpr
        obtain ⟨ins, ok, he, hv⟩ := absent_check p q
        refine ⟨ins, ok, he, ?_⟩
        rw [hv]
        intro v mv
        simp only [Finset.mem_insert, Finset.mem_singleton] at mv
        simp only [thmRule, Finset.mem_range]
        rcases mv with rfl | rfl
        · exact (List.getElem?_eq_some_iff.mp hp).1
        · exact (List.getElem?_eq_some_iff.mp hq).1
      · intro v mv
        simp only [thmRule, pfP, vars_pjd, List.mem_cons, List.not_mem_nil, or_false] at mv
        obtain ⟨p, rfl, mv⟩ := mv
        exact patOf_vars_sub concl mv
  | cvRefl s =>
      simp only [rules, Option.some.injEq] at hr
      subst hr
      refine determined_of [tyP (pnum s) (pv 0)] [] (by simp [cvReflRule, Rule.kinds, Premise.kind])
        (fun q mq v mv => ?_) (fun v mv => ?_) (by simp) (fun v mv => ?_)
      · simp only [List.mem_singleton] at mq
        subst mq
        simp only [tyP, vars_pjd, List.mem_cons, List.not_mem_nil, or_false] at mv
        obtain ⟨p, rfl | rfl, mv⟩ := mv
        · exact absurd mv (vars_pnum _ _)
        · rw [vars_pv] at mv; subst mv; simp [cvReflRule]
      · simp only [cvReflRule, Finset.mem_range] at mv
        rw [mem_patsVars]
        exact ⟨tyP (pnum s) (pv 0), List.mem_singleton_self _, by
          simp [tyP, vars_pjd, vars_pv]; omega⟩
      · simp only [cvReflRule, cvP, vars_pjd, List.mem_cons, List.not_mem_nil, or_false] at mv
        obtain ⟨p, rfl | rfl | rfl, mv⟩ := mv
        · exact absurd mv (vars_pnum _ _)
        · rw [vars_pv] at mv; subst mv; simp [cvReflRule]
        · rw [vars_pv] at mv; subst mv; simp [cvReflRule]
  | cvSymm => simp only [rules, Option.some.injEq] at hr; subst hr; decide
  | cvTrans => simp only [rules, Option.some.injEq] at hr; subst hr; decide
  | conv => simp only [rules, Option.some.injEq] at hr; subst hr; decide
  | cvCong c =>
      simp only [rules, Option.map_eq_some_iff] at hr
      obtain ⟨d, hd, rfl⟩ := hr
      set n := d.arguments.length with hn
      refine determined_of (fitPats 0 d.arguments ++ fitPats n d.arguments ++
          d.arguments.zipIdx.map fun x => cvP (pnum x.1.sort) (pv x.2) (pv (n + x.2))) [] ?_
        (fun q mq => ?_) (fun v mv => ?_) (by simp) ?_
      · simp [cvCongRule, Rule.kinds, fits_kinds, Premise.kind, Function.comp_def, hn]
      · intro v mv
        simp only [cvCongRule, Finset.mem_range]
        rcases List.mem_append.mp mq with mq | mq
        · rcases List.mem_append.mp mq with mq | mq
          · simp only [fitPats, List.mem_map] at mq
            obtain ⟨⟨b, k⟩, mk, rfl⟩ := mq
            rw [vars_fitPat] at mv; subst mv
            have := (List.mem_zipIdx mk).2.1; omega
          · simp only [fitPats, List.mem_map] at mq
            obtain ⟨⟨b, k⟩, mk, rfl⟩ := mq
            rw [vars_fitPat] at mv; subst mv
            have := (List.mem_zipIdx mk).2.1; omega
        · obtain ⟨⟨b, k⟩, mk, rfl⟩ := List.mem_map.mp mq
          have := (List.mem_zipIdx mk).2.1
          simp only [cvP, vars_pjd, List.mem_cons, List.not_mem_nil, or_false] at mv
          obtain ⟨p, rfl | rfl | rfl, mv⟩ := mv
          · exact absurd mv (vars_pnum _ _)
          · rw [vars_pv] at mv; omega
          · rw [vars_pv] at mv; omega
      · rw [mem_patsVars]
        simp only [cvCongRule, Finset.mem_range] at mv
        by_cases small : v < n
        · have : v ∈ patsVars (fitPats 0 d.arguments) := mem_fitPats_vars.mpr ⟨by omega, by omega⟩
          obtain ⟨p, mp, pv'⟩ := mem_patsVars.mp this
          exact ⟨p, List.mem_append_left _ (List.mem_append_left _ mp), pv'⟩
        · have : v ∈ patsVars (fitPats n d.arguments) := mem_fitPats_vars.mpr ⟨by omega, by omega⟩
          obtain ⟨p, mp, pv'⟩ := mem_patsVars.mp this
          exact ⟨p, List.mem_append_left _ (List.mem_append_right _ mp), pv'⟩
      · intro v mv
        simp only [cvCongRule, cvP, vars_pjd, List.mem_cons, List.not_mem_nil, or_false,
          Finset.mem_range] at mv ⊢
        obtain ⟨p, rfl | rfl | rfl, mv⟩ := mv
        · exact absurd mv (vars_pnum _ _)
        · rw [vars_patOf] at mv; have := occurs_spine 0 _ mv; omega
        · rw [vars_patOf] at mv; have := occurs_spine _ _ mv; omega
  | unfold c =>
      simp only [rules] at hr
      cases hs : E.sig c with
      | none => rw [hs] at hr; cases hr
      | some d =>
          cases hdf : E.defs c with
          | none => rw [hs, hdf] at hr; cases hr
          | some b =>
              rw [hs, hdf] at hr
              simp only [Option.some.injEq] at hr
              subst hr
              have body := wf.defs c d b hs hdf
              set n := d.arguments.length with hn
              set m := b.dummies.length with hm
              refine determined_of (fitPats 0 d.arguments ++ (b.dummies.zipIdx n).map (fun x => bvP x.1 (pv x.2)) ++
                  [tyP (pnum d.resultSort) (patOf b.expression)]) ((fresh n m).map Premise.kind) ?_
                (fun q mq => ?_) (fun v mv => ?_) (fun k mk => ?_) ?_
              · simp [unfoldRule, Rule.kinds, fits_kinds, Premise.kind, dummyFits, Function.comp_def, hn, hm]
              · intro v mv
                simp only [unfoldRule, Finset.mem_range]
                rcases List.mem_append.mp mq with mq | mq
                · rcases List.mem_append.mp mq with mq | mq
                  · simp only [fitPats, List.mem_map] at mq
                    obtain ⟨⟨b', k⟩, mk, rfl⟩ := mq
                    rw [vars_fitPat] at mv; subst mv
                    have := (List.mem_zipIdx mk).2.1; omega
                  · obtain ⟨⟨s, k⟩, mk, rfl⟩ := List.mem_map.mp mq
                    simp only [bvP, vars_pjd, List.mem_cons, List.not_mem_nil, or_false] at mv
                    obtain ⟨p, rfl | rfl, mv⟩ := mv
                    · exact absurd mv (vars_pnum _ _)
                    · rw [vars_pv] at mv; have := (List.mem_zipIdx mk).2.1; omega
                · simp only [List.mem_singleton] at mq
                  subst mq
                  simp only [tyP, vars_pjd, List.mem_cons, List.not_mem_nil, or_false] at mv
                  obtain ⟨p, rfl | rfl, mv⟩ := mv
                  · exact absurd mv (vars_pnum _ _)
                  · exact Finset.mem_range.mp (patOf_vars_sub body mv)
              · rw [mem_patsVars]
                simp only [unfoldRule, Finset.mem_range] at mv
                by_cases small : v < n
                · have : v ∈ patsVars (fitPats 0 d.arguments) := mem_fitPats_vars.mpr ⟨by omega, by omega⟩
                  obtain ⟨p, mp, pv'⟩ := mem_patsVars.mp this
                  exact ⟨p, List.mem_append_left _ (List.mem_append_left _ mp), pv'⟩
                · obtain ⟨s, hsv⟩ : ∃ s, b.dummies[v - n]? = some s := ⟨_, List.getElem?_eq_getElem (by omega)⟩
                  refine ⟨bvP s (pv v), List.mem_append_left _ (List.mem_append_right _ ?_), ?_⟩
                  · exact List.mem_map.mpr ⟨(s, v), List.mem_zipIdx_iff_le_and_getElem?_sub.mpr ⟨by omega, hsv⟩, rfl⟩
                  · simp [bvP, vars_pjd, vars_pv]
              · simp only [fresh, List.map_flatMap, List.mem_flatMap, List.mem_range, List.map_map,
                  List.mem_map, Function.comp_def] at mk
                obtain ⟨j, jlt, k, klt, rfl⟩ := mk
                obtain ⟨ins, ok, he, hv⟩ := absent_check (n + j) k
                refine ⟨ins, ok, he, ?_⟩
                rw [hv]
                intro v mv
                simp only [Finset.mem_insert, Finset.mem_singleton] at mv
                simp only [unfoldRule, Finset.mem_range]
                rcases mv with rfl | rfl <;> omega
              · intro v mv
                simp only [unfoldRule, cvP, vars_pjd, List.mem_cons, List.not_mem_nil, or_false,
                  Finset.mem_range] at mv ⊢
                obtain ⟨p, rfl | rfl | rfl, mv⟩ := mv
                · exact absurd mv (vars_pnum _ _)
                · rw [vars_patOf] at mv; have := occurs_spine 0 _ mv; omega
                · exact Finset.mem_range.mp (patOf_vars_sub body mv)

/-! ## The MM0 claim -/

/-- How a context variable is freshened: a bound variable is a scope variable, a regular variable a
name over its dependencies. -/
def kindOf : Binder → FormalKind
  | .bound _ => .scope
  | .regular _ D => .dep (depList D)

/-- The binders' judgments, over the formals. -/
def ctxPats (Γ : Context) : List Pat :=
  Γ.zipIdx.flatMap fun x => match x.1 with
    | .bound s => [bvP s (pv x.2), tyP (pnum s) (pv x.2)]
    | .regular s _ => [tyP (pnum s) (pv x.2)]

/-- The name declarations of a context: each bound variable is a name, `(atom-kind x name)`. -/
def nameDecls (Γ : Context) : List Premise :=
  Γ.zipIdx.filterMap fun x => match x.1 with
    | .bound _ => some (.atomKind (pv x.2) (psym "name"))
    | .regular _ _ => none

/-- **The MM0 claim** `Γ ⊢ H ⇒ e` with a proof: the context's variables are its formals; its
hypotheses are the binders' judgments and MM0's hypotheses, then the independence conditions of
its binders (as in the rule of an MM0 theorem) and the name declarations of its bound variables,
which the rule it becomes checks at every instance. -/
def mm0Claim (id : Name) (Γ : Context) (H : List Preterm) (e : Preterm)
    (proof : List (CProofNode Name)) (root : CKid) : Claim Name :=
  ⟨id, Γ.map kindOf, [], (ctxPats Γ ++ H.map (fun h => pfP (patOf h))).map Premise.judg ++ indep Γ ++
    nameDecls Γ, [], [], pfP (patOf e), [], proof, root⟩

theorem nameDecls_decode {Φ : Context} {pr : Premise} (m : pr ∈ nameDecls Φ) :
    ∃ i s, pr = .atomKind (pv i) (psym "name") ∧ Φ[i]? = some (.bound s) := by
  simp only [nameDecls, List.mem_filterMap] at m
  obtain ⟨⟨b, i⟩, mi, hr⟩ := m
  have hi : Φ[i]? = some b := List.mem_zipIdx_iff_getElem?.mp mi
  cases b with
  | bound s => simp only [Option.some.injEq] at hr; exact ⟨i, s, hr.symm, hi⟩
  | regular _ _ => simp at hr

theorem judgPats_append : ∀ xs ys : List Premise, judgPats (xs ++ ys) = judgPats xs ++ judgPats ys
  | [], _ => rfl
  | x :: xs, ys => by
      cases h : x.judgPat? <;> simp [judgPats, h, judgPats_append xs ys]

theorem judgPats_of_none : ∀ {ps : List Premise}, (∀ p ∈ ps, p.judgPat? = none) → judgPats ps = []
  | [], _ => rfl
  | p :: ps, h => by
      simp only [judgPats, h p List.mem_cons_self]
      exact judgPats_of_none fun q m => h q (List.mem_cons_of_mem _ m)

theorem judgPats_sides (Γ : Context) : judgPats (indep Γ ++ nameDecls Γ) = [] := by
  apply judgPats_of_none
  intro p m
  rcases List.mem_append.mp m with m | m
  · obtain ⟨_, _, _, _, rfl, -⟩ := indep_decode m; rfl
  · obtain ⟨_, _, rfl, -⟩ := nameDecls_decode m; rfl

/-- The side hypotheses of an MM0 claim are checks on formals. -/
theorem sides_checks {Γ : Context} {k : Kind} (m : k ∈ (indep Γ ++ nameDecls Γ).map Premise.kind) :
    ∃ ins ok, k = Kind.check ins ok ∧ patsVars ins ⊆ Finset.range Γ.length := by
  obtain ⟨pr, mpr, rfl⟩ := List.mem_map.mp m
  rcases List.mem_append.mp mpr with m | m
  · obtain ⟨p, q, s, b', rfl, hp, hq, -⟩ := indep_decode m
    refine ⟨_, _, rfl, ?_⟩
    intro v mv
    simp only [patsVars, List.foldr, Finset.union_empty, Finset.mem_union, vars_pv] at mv
    rw [Finset.mem_range]
    rcases mv with rfl | rfl
    · exact (List.getElem?_eq_some_iff.mp hp).1
    · exact (List.getElem?_eq_some_iff.mp hq).1
  · obtain ⟨i, s, rfl, hi⟩ := nameDecls_decode m
    refine ⟨_, _, rfl, ?_⟩
    intro v mv
    simp only [patsVars, List.foldr, Finset.union_empty, Finset.mem_union, vars_pv] at mv
    rw [Finset.mem_range]
    rcases mv with rfl | mv
    · exact (List.getElem?_eq_some_iff.mp hi).1
    · simp [psym, TreePat.vars, TreePatFields.vars] at mv

/-- Regular variables depend on bound variables. -/
def DepsBound (Γ : Context) : Prop :=
  ∀ (i s : ℕ) (D : Finset ℕ), Γ[i]? = some (.regular s D) → ∀ d ∈ D, ∃ s' : ℕ, Γ[d]? = some (.bound s')

variable {Γ : Context} {H : List Preterm} {e : Preterm} {id : Name} {proof : List (CProofNode Name)}
  {root : CKid}

theorem kindOf_value (Γ : Context) {i : ℕ} {b : Binder} (hb : Γ[i]? = some b) :
    (kindOf b).value i = encVar Γ i := by
  cases b <;> simp [kindOf, FormalKind.value, encVar, hb]

theorem mm0Claim_σ : (mm0Claim id Γ H e proof root).σ =
    substOf (((List.range Γ.length).map Preterm.var).map (enc Γ)) := by
  funext k
  simp only [Claim.σ, Claim.vals, mm0Claim, List.append_nil, substOf, List.getElem?_mapIdx,
    List.getElem?_map]
  by_cases lt : k < Γ.length
  · rw [List.getElem?_range lt, List.getElem?_eq_getElem lt]
    simp [kindOf_value Γ (List.getElem?_eq_getElem lt), enc]
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]
    rfl

theorem substitute_identity (n : ℕ) : ∀ p : Preterm, Preterm.VarsBelow n p →
    Preterm.substitute (Substitution.ofList ((List.range n).map Preterm.var)) p = some p
  | .var k, h => by simp [Preterm.substitute, Substitution.ofList, List.getElem?_range (show k < n from h)]
  | .term c, _ => rfl
  | .app f a, h => by
      simp [Preterm.substitute, substitute_identity n f h.1, substitute_identity n a h.2]

theorem inst_claim {p : Preterm} (h : Preterm.VarsBelow Γ.length p) :
    (patOf p).inst (mm0Claim id Γ H e proof root).σ = some (enc Γ p) := by
  rw [mm0Claim_σ, inst_patOf, substitute_identity _ p h]; rfl

theorem instAll_flatMap {α : Type} (σ : Subst ℕ Tm) (f : α → List Pat) (g : α → List Tm) :
    ∀ l : List α, (∀ x ∈ l, instAll σ (f x) = some (g x)) → instAll σ (l.flatMap f) = some (l.flatMap g)
  | [], _ => rfl
  | x :: l, h => by
      simp only [List.flatMap_cons, Claim.instAll_append, h x List.mem_cons_self,
        instAll_flatMap σ f g l fun y m => h y (List.mem_cons_of_mem _ m), Option.bind_some, Option.map_some]

theorem instAll_ctx : instAll (mm0Claim id Γ H e proof root).σ (ctxPats Γ) = some (ctxHyps Γ) := by
  apply instAll_flatMap
  rintro ⟨b, i⟩ m
  have hb : Γ[i]? = some b := List.mem_zipIdx_iff_getElem?.mp m
  have lt : i < Γ.length := (List.getElem?_eq_some_iff.mp hb).1
  have σi : (mm0Claim id Γ H e proof root).σ i = some (encVar Γ i) := by
    rw [mm0Claim_σ]; simp [substOf, List.getElem?_range lt, enc]
  cases b with
  | bound s =>
      simp [bvP, tyP, inst_pjd, instAll, inst_pnum, inst_pv, σi, encVar, hb, bvJ, tyJ]
  | regular s D =>
      simp [tyP, inst_pjd, instAll, inst_pnum, inst_pv, σi, encVar, hb, tyJ]

theorem judgPats_judg : ∀ ps : List Pat, judgPats (ps.map Premise.judg) = ps
  | [] => rfl
  | p :: ps => by simp [judgPats, Premise.judgPat?, judgPats_judg ps]

theorem inst_pfP_claim {h : Preterm} (hv : Preterm.VarsBelow Γ.length h) :
    (pfP (patOf h)).inst (mm0Claim id Γ H e proof root).σ = some (pfJ (enc Γ h)) := by
  simp only [pfP, inst_pjd, instAll, inst_claim hv, Option.map_some]
  rfl

theorem instAll_hyps (hH : ∀ h ∈ H, Preterm.VarsBelow Γ.length h) :
    instAll (mm0Claim id Γ H e proof root).σ (H.map fun h => pfP (patOf h)) =
      some (H.map fun h => pfJ (enc Γ h)) := by
  have : ∀ l : List Preterm, (∀ h ∈ l, Preterm.VarsBelow Γ.length h) →
      instAll (mm0Claim id Γ H e proof root).σ (l.map fun h => pfP (patOf h)) =
        some (l.map fun h => pfJ (enc Γ h)) := by
    intro l hl
    induction l with
    | nil => rfl
    | cons h l ih =>
        rw [List.map_cons, List.map_cons]
        simp only [instAll, inst_pfP_claim (hl h List.mem_cons_self),
          ih fun x m => hl x (List.mem_cons_of_mem _ m)]
  exact this H hH

theorem hypPats_mm0 : (mm0Claim id Γ H e proof root).hypPats = ctxPats Γ ++ H.map (fun h => pfP (patOf h)) := by
  simp only [Claim.hypPats, mm0Claim, List.map_nil, List.append_nil]
  rw [List.append_assoc, judgPats_append, judgPats_judg, judgPats_sides, List.append_nil]

theorem mm0Claim_cbHyps (hH : ∀ h ∈ H, Preterm.VarsBelow Γ.length h) :
    (mm0Claim id Γ H e proof root).cbHyps = some (hypsOf Γ H) := by
  rw [Claim.cbHyps_eq, hypPats_mm0, Claim.instAll_append, instAll_ctx, instAll_hyps hH]
  rfl

theorem mm0Claim_goal (he : Preterm.VarsBelow Γ.length e) :
    (mm0Claim id Γ H e proof root).goal = some (pfJ (enc Γ e)) :=
  inst_pfP_claim he

/-! ## The MM0 claim passes the admission checks -/

theorem ctxPats_vars {q : Pat} (m : q ∈ ctxPats Γ) : q.vars ⊆ Finset.range Γ.length := by
  simp only [ctxPats, List.mem_flatMap] at m
  obtain ⟨⟨b, i⟩, mi, mq⟩ := m
  have lt : i < Γ.length := (List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp mi)).1
  intro v mv
  rw [Finset.mem_range]
  cases b with
  | bound s =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mq
      rcases mq with rfl | rfl <;>
      · simp only [bvP, tyP, vars_pjd, List.mem_cons, List.not_mem_nil, or_false] at mv
        obtain ⟨p, rfl | rfl, mv⟩ := mv
        · exact absurd mv (vars_pnum _ _)
        · rw [vars_pv] at mv; omega
  | regular s D =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mq
      subst mq
      simp only [tyP, vars_pjd, List.mem_cons, List.not_mem_nil, or_false] at mv
      obtain ⟨p, rfl | rfl, mv⟩ := mv
      · exact absurd mv (vars_pnum _ _)
      · rw [vars_pv] at mv; omega

theorem ctxPats_cover : Finset.range Γ.length ⊆ patsVars (ctxPats Γ) := by
  intro v mv
  rw [Finset.mem_range] at mv
  rw [mem_patsVars]
  obtain ⟨b, hb⟩ : ∃ b, Γ[v]? = some b := ⟨_, List.getElem?_eq_getElem mv⟩
  refine ⟨tyP (pnum b.sort) (pv v), ?_, by simp [tyP, vars_pjd, vars_pv]⟩
  simp only [ctxPats, List.mem_flatMap]
  refine ⟨(b, v), List.mem_zipIdx_iff_getElem?.mpr hb, ?_⟩
  cases b <;> simp [Binder.sort]

theorem mm0Claim_stmtOk (deps : DepsBound Γ) (hH : ∀ h ∈ H, Preterm.VarsBelow Γ.length h)
    (he : Preterm.VarsBelow Γ.length e) : (mm0Claim id Γ H e proof root).stmtOk = true := by
  have qsIn : ∀ q ∈ ctxPats Γ ++ H.map (fun h => pfP (patOf h)), q.vars ⊆ Finset.range Γ.length := by
    intro q mq
    rcases List.mem_append.mp mq with mq | mq
    · exact ctxPats_vars mq
    · obtain ⟨h, mh, rfl⟩ := List.mem_map.mp mq
      intro v mv
      simp only [pfP, vars_pjd, List.mem_cons, List.not_mem_nil, or_false] at mv
      obtain ⟨p, rfl, mv⟩ := mv
      exact patOf_vars_sub (hH h mh) mv
  have kinds : (mm0Claim id Γ H e proof root).hyps.map Premise.kind =
      (ctxPats Γ ++ H.map (fun h => pfP (patOf h))).map Kind.consume ++
        (indep Γ ++ nameDecls Γ).map Premise.kind := by
    simp [mm0Claim, Premise.kind, Function.comp_def, List.append_assoc]
  have conclIn : (pfP (patOf e)).vars ⊆ Finset.range Γ.length := by
    intro v mv
    simp only [pfP, vars_pjd, List.mem_cons, List.not_mem_nil, or_false] at mv
    obtain ⟨p, rfl, mv⟩ := mv
    exact patOf_vars_sub he mv
  have prems : Claim.premsVars (mm0Claim id Γ H e proof root).hyps ⊆ Finset.range Γ.length := by
    intro v mv
    unfold Claim.premsVars at mv
    rw [kinds, mem_kindsVars] at mv
    obtain ⟨kd, mk, mv⟩ := mv
    rcases List.mem_append.mp mk with mk | mk
    · obtain ⟨q, mq, rfl⟩ := List.mem_map.mp mk
      exact qsIn q mq mv
    · obtain ⟨ins, ok, rfl, sub⟩ := sides_checks mk
      exact sub mv
  have det : (mm0Claim id Γ H e proof root).toRule.determinedB = true := by
    refine determined_of (ctxPats Γ ++ H.map (fun h => pfP (patOf h))) ((indep Γ ++ nameDecls Γ).map Premise.kind)
      ?_ ?_ ?_ ?_ ?_
    · simp only [Claim.toRule, Rule.kinds]; exact kinds
    · simpa [Claim.toRule, Claim.nformals, mm0Claim] using qsIn
    · intro v mv
      simp only [Claim.toRule, Claim.nformals, mm0Claim, List.length_map] at mv
      obtain ⟨p, mp, pv'⟩ := mem_patsVars.mp (ctxPats_cover mv)
      exact mem_patsVars.mpr ⟨p, List.mem_append_left _ mp, pv'⟩
    · intro k mk
      obtain ⟨ins, ok, rfl, sub⟩ := sides_checks mk
      exact ⟨ins, ok, rfl, by simpa [Claim.toRule, Claim.nformals, mm0Claim] using sub⟩
    · simpa [Claim.toRule, Claim.nformals, mm0Claim] using conclIn
  have kok : ((mm0Claim id Γ H e proof root).formals ++ (mm0Claim id Γ H e proof root).dummies).all
      (mm0Claim id Γ H e proof root).kindOk = true := by
    rw [List.all_eq_true]
    intro κ mκ
    simp only [mm0Claim, List.append_nil, List.mem_map] at mκ
    obtain ⟨b, mb, rfl⟩ := mκ
    cases b with
    | bound s => rfl
    | regular s D =>
        obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp mb
        simp only [kindOf, Claim.kindOk, List.all_eq_true, beq_iff_eq]
        intro d md
        have mdD : d ∈ D := by simpa [depList] using md
        obtain ⟨s', hs'⟩ := deps i s D hi d mdD
        simp [Claim.kindOf, mm0Claim, List.getElem?_map, hs', kindOf]
  simp only [Claim.stmtOk, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨by simp [mm0Claim], ?_⟩, ?_⟩, det⟩, by simp [mm0Claim]⟩, by simp [mm0Claim]⟩,
    by simp [mm0Claim]⟩, kok⟩
  · simpa [Claim.nformals, mm0Claim] using prems
  · simpa [Claim.nformals, mm0Claim] using conclIn

/-! ## MM0 adequacy of the kernel on thinned terms -/

/-- **MM0 adequacy**: the kernel on thinned terms accepts the MM0 claim of `Γ ⊢ H ⇒ e` with some
proof exactly when Mettapedia's MM0 kernel derives `e` from `H` in `Γ`. -/
theorem kernel_accepts_iff_derives {E : MM0Env} (wf : E.WF) (deps : DepsBound Γ)
    (hH : ∀ h ∈ H, Preterm.VarsBelow Γ.length h) (he : Preterm.VarsBelow Γ.length e) (id : Name) :
    (∃ proof root, (mm0Claim id Γ H e proof root).verdictR (rules E) = true) ↔
      Derives E.sig E.defs E.thms Γ H e := by
  constructor
  · rintro ⟨proof, root, h⟩
    obtain ⟨hs, g, hh, hg, d⟩ := verdictR_sound (rules_determined wf) h
    rw [mm0Claim_cbHyps hH] at hh
    rw [mm0Claim_goal he] at hg
    cases hh; cases hg
    exact derivable_pf_derives _ d
  · intro d
    have c0 := mm0Claim id Γ H e [] (.node 0)
    obtain ⟨proof, root, h⟩ := verdictR_complete (rules_determined wf) (c := mm0Claim id Γ H e [] (.node 0))
      (mm0Claim_stmtOk deps hH he) (mm0Claim_cbHyps hH) (mm0Claim_goal he) (pf_derivable d)
    exact ⟨proof, root, h⟩

/-! ## Controls -/

namespace Controls

/-- `(imp a b)`. -/
def imp (a b : Preterm) : Preterm := .app (.app (.term 0) a) b

/-- `(all x φ)`: the bound slot `x`, and `φ` may depend on `x`. -/
def all (x p : Preterm) : Preterm := .app (.app (.term 1) x) p

/-- Sorts `0` (formulas) and `1` (variables); terms `imp` and `all`. -/
def sig : TermSignature
  | 0 => some ⟨[.regular 0 ∅, .regular 0 ∅], 0, ∅⟩
  | 1 => some ⟨[.bound 1, .regular 0 {0}], 0, ∅⟩
  | _ => none

/-- One axiom, `nf`: `φ → ∀x φ` for a `φ` that does not depend on `x`. -/
def thms : TheoremSignature
  | 0 => some ⟨[.bound 1, .regular 0 ∅], [], imp (.var 1) (all (.var 0) (.var 1))⟩
  | _ => none

def E : MM0Env := ⟨sig, fun _ => none, thms⟩

/-- `x` bound; `ψ` regular, independent of `x`. -/
def ctx₁ : Context := [.bound 1, .regular 0 ∅]

/-- `x` bound; `φ` regular, depending on `x`. -/
def ctx₂ : Context := [.bound 1, .regular 0 {0}]

/-- `ψ → ∀x ψ`. -/
def goal : Preterm := imp (.var 1) (all (.var 0) (.var 1))

/-- One node: `nf` at `x` (hypothesis 0, `(bv 1 x)`) and the formula (hypothesis 2, its sort). -/
def nfProof : List (CProofNode Name) := [⟨0, .thm 0, [.hyp 0, .hyp 2]⟩]

/-- Positive: `ψ` does not depend on `x`, so `nf` applies: `ψ`'s value, a name over no names, does not
mention `x`. -/
theorem nf_accepted : (mm0Claim (.thm 1) ctx₁ [] goal nfProof (.node 0)).verdictR (rules E) = true := by
  decide +kernel

/-- Negative: `φ` depends on `x` (its value is a name over `x`), so the same proof is refused. -/
theorem nf_refused : (mm0Claim (.thm 1) ctx₂ [] goal nfProof (.node 0)).verdictR (rules E) = false := by
  decide +kernel

end Controls

end Mettapedia.Logic.TierZero.Adequacy.MM0
