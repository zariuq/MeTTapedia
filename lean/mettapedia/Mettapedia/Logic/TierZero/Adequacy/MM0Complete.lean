import Mettapedia.Logic.TierZero.Adequacy.MM0Sound

/-!
# MM0 adequacy, completeness: what MM0 derives, the kernel derives

Every MM0 judgment has a derivation in the presentation of its environment:

* `ty_derivable`: a saturated preterm of sort `s` has `(ty s E)`, by the `con` rules over the
  context's hypotheses;
* `cv_derivable`: MM0's conversion gives `(cv s E F)`, by the conversion rules (a conversion is a
  proof node at tier 0);
* `pf_derivable`: MM0's `Derives` gives `(pf E)`; a theorem application's independence conditions
  hold because MM0's admissible substitution keeps each bound image out of the support of every
  argument whose binder does not depend on it.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.MM0

open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources
open Mettapedia.Logic.TierZero
open Mettapedia.Logic.TierZero.Kernel2
open Mettapedia.Languages.MM0.Kernel

variable {E : MM0Env} {Γ : Context} {H : List Preterm} {fr : Frame}

/-- Derivability in the presentation from the claim's hypotheses. -/
abbrev D (E : MM0Env) (Γ : Context) (H : List Preterm) (fr : Frame) (j : Tm) : Prop :=
  Derivable (presOf (rules E) fr) (hypsOf Γ H) j

/-! ## Applying a rule -/

/-- A rule whose premises are no list premises has no list kind. -/
theorem kinds_noEach_of {ru : Rule} (h : ∀ pr ∈ ru.prems, ∀ x l q, pr ≠ .each x l q) :
    ∀ l x p, Kind.each l x p ∉ ru.kinds := by
  intro l x p m
  simp only [Rule.kinds, List.mem_map] at m
  obtain ⟨pr, mpr, e⟩ := m
  cases pr <;> simp [Premise.kind] at e
  obtain ⟨rfl, rfl, rfl⟩ := e
  exact h _ mpr _ _ _ rfl

theorem fits_judg {off : ℕ} {Φ : Context} {pr : Premise} (m : pr ∈ fits off Φ) : ∃ q, pr = .judg q := by
  simp only [fits, List.mem_map] at m
  obtain ⟨_, _, rfl⟩ := m
  exact ⟨_, rfl⟩

theorem dummyFits_judg {n : ℕ} {ds : List ℕ} {pr : Premise} (m : pr ∈ dummyFits n ds) : ∃ q, pr = .judg q := by
  simp only [dummyFits, List.mem_map] at m
  obtain ⟨_, _, rfl⟩ := m
  exact ⟨_, rfl⟩

theorem indep_absent {Φ : Context} {pr : Premise} (m : pr ∈ indep Φ) : ∃ x b, pr = .absent x b := by
  simp only [indep, List.mem_flatMap] at m
  obtain ⟨⟨b, i⟩, _, m⟩ := m
  cases b with
  | bound s =>
      simp only [List.mem_filterMap] at m
      obtain ⟨y, _, hy⟩ := m
      split_ifs at hy
      cases hy
      exact ⟨_, _, rfl⟩
  | regular s D => simp at m

theorem fresh_absent {n m : ℕ} {pr : Premise} (h : pr ∈ fresh n m) : ∃ x b, pr = .absent x b := by
  simp only [fresh, List.mem_flatMap, List.mem_map] at h
  obtain ⟨_, _, _, _, rfl⟩ := h
  exact ⟨_, _, rfl⟩

/-- **The MM0 presentation has no list premises.** -/
theorem rules_noEach {r : Name} {ru : Rule} (hr : rules E r = some ru) :
    ∀ l x p, Kind.each l x p ∉ ru.kinds := by
  apply kinds_noEach_of
  intro pr mpr x l q e
  subst e
  cases r with
  | con c =>
      simp only [rules] at hr
      cases hs : E.sig c <;> rw [hs] at hr <;> simp at hr
      subst hr
      obtain ⟨_, h⟩ := fits_judg (by simpa [conRule] using mpr)
      cases h
  | thm t =>
      simp only [rules] at hr
      cases ht : E.thms t <;> rw [ht] at hr <;> simp at hr
      subst hr
      simp only [thmRule, List.mem_append, List.mem_map] at mpr
      rcases mpr with (m | ⟨_, _, h⟩) | m
      · obtain ⟨_, h⟩ := fits_judg m; cases h
      · cases h
      · obtain ⟨_, _, h⟩ := indep_absent m; cases h
  | cvRefl s => simp [rules, cvReflRule] at hr; subst hr; simp at mpr
  | cvSymm => simp [rules, cvSymmRule] at hr; subst hr; simp at mpr
  | cvTrans => simp [rules, cvTransRule] at hr; subst hr; simp at mpr
  | cvCong c =>
      simp only [rules] at hr
      cases hs : E.sig c <;> rw [hs] at hr <;> simp at hr
      subst hr
      simp only [cvCongRule, List.mem_append, List.mem_map] at mpr
      rcases mpr with (m | m) | ⟨_, _, h⟩
      · obtain ⟨_, h⟩ := fits_judg m; cases h
      · obtain ⟨_, h⟩ := fits_judg m; cases h
      · cases h
  | unfold c =>
      simp only [rules] at hr
      cases hs : E.sig c <;> cases hd : E.defs c <;> rw [hs, hd] at hr <;> simp at hr
      subst hr
      simp only [unfoldRule, List.mem_append, List.mem_singleton] at mpr
      rcases mpr with ((m | m) | h) | m
      · obtain ⟨_, h⟩ := fits_judg m; cases h
      · obtain ⟨_, h⟩ := dummyFits_judg m; cases h
      · cases h
      · obtain ⟨_, _, h⟩ := fresh_absent m; cases h
  | conv => simp [rules, convRule] at hr; subst hr; simp at mpr

/-- **Applying a rule**: values for its formals that make every premise kind hold, and whose
consumed premises are derivable, derive its conclusion. -/
theorem apply_rule {r : Name} {ru : Rule} (hr : rules E r = some ru) {a : List Tm} {c : Tm}
    (len : a.length = ru.nformals) (holds : ∀ k ∈ ru.kinds, KindHolds fr (substOf a) k)
    (hc : ru.concl.inst (substOf a) = some c)
    (prem : ∀ q, Kind.consume q ∈ ru.kinds → ∀ j, q.inst (substOf a) = some j → D E Γ H fr j) :
    D E Γ H fr c := by
  obtain ⟨ps, hps⟩ := instKinds_of_holds fr (substOf a) ru.kinds holds
  have hi : (presOf (rules E) fr).inst r a = some (ps, c) := by
    simp only [presOf, hr]
    exact (instance_iff fr ru a ps c).mpr ⟨len, hps, hc⟩
  refine Derivable.rule hi fun p mp _ => ?_
  rcases instKinds_mem fr _ hps p mp with ⟨q, mq, iq⟩ | ⟨l, x, p', es, me, -, -⟩
  · exact prem q mq p iq
  · exact absurd me (rules_noEach hr l x p')

theorem holds_consume {σ : Subst ℕ Tm} {q : Pat} {j : Tm} (h : q.inst σ = some j) :
    KindHolds fr σ (.consume q) := by simp [KindHolds, h]

/-! ## The context's hypotheses -/

theorem hyp_ctx {j : Tm} (m : j ∈ ctxHyps Γ) : D E Γ H fr j :=
  Derivable.hyp (List.mem_append_left _ m)

theorem bv_hyp {i s : ℕ} (hb : Γ[i]? = some (.bound s)) : D E Γ H fr (bvJ s (fvar i)) := by
  apply hyp_ctx
  simp only [ctxHyps, List.mem_flatMap]
  exact ⟨(.bound s, i), List.mem_zipIdx_iff_getElem?.mpr hb, by simp⟩

theorem ty_var {i : ℕ} {b : Binder} (hb : Γ[i]? = some b) : D E Γ H fr (tyJ b.sort (enc Γ (.var i))) := by
  apply hyp_ctx
  simp only [ctxHyps, List.mem_flatMap]
  refine ⟨(b, i), List.mem_zipIdx_iff_getElem?.mpr hb, ?_⟩
  cases b with
  | bound s => simp [enc, encVar, hb, Binder.sort]
  | regular s Dp => simp [enc, encVar, hb, Binder.sort]

/-! ## Typing -/

/-- The fit judgment of an argument. -/
def FitD (E : MM0Env) (Γ : Context) (H : List Preterm) (fr : Frame) (x : Preterm) (b : Binder) : Prop :=
  D E Γ H fr (fitJ b (enc Γ x))

theorem inst_fits_holds {Φ : Context} {off : ℕ} {a : List Tm} (len : off + Φ.length ≤ a.length) :
    ∀ k ∈ (fits off Φ).map Premise.kind, KindHolds fr (substOf a) k := by
  intro k mk
  simp only [fits, List.map_map, List.mem_map, Function.comp_def] at mk
  obtain ⟨⟨b, i⟩, mi, rfl⟩ := mk
  obtain ⟨le, -⟩ := List.mem_zipIdx_iff_le_and_getElem?_sub.mp mi
  have lt : i < a.length := by
    have := (List.mem_zipIdx mi).2.1; omega
  simp [Premise.kind, KindHolds, inst_fitPat, substOf, List.getElem?_eq_getElem lt]

/-- The consumed fit premises of an instance whose arguments fit. -/
theorem fits_prem {Φ : Context} {off : ℕ} {args : List Preterm} {pre : List Tm}
    (hpre : pre.length = off) (fitsD : List.Forall₂ (FitD E Γ H fr) args Φ) {post : List Tm} {q : Pat}
    (mq : Kind.consume q ∈ (fits off Φ).map Premise.kind) {j : Tm}
    (iq : q.inst (substOf (pre ++ args.map (enc Γ) ++ post)) = some j) : D E Γ H fr j := by
  simp only [fits, List.map_map, List.mem_map, Function.comp_def] at mq
  obtain ⟨⟨b, i⟩, mi, hq⟩ := mq
  simp only [Premise.kind, Kind.consume.injEq] at hq
  subst hq
  obtain ⟨le, hb⟩ := List.mem_zipIdx_iff_le_and_getElem?_sub.mp mi
  have len := fitsD.length_eq
  have lt : i - off < args.length := by rw [len]; exact (List.getElem?_eq_some_iff.mp hb).1
  have get : (pre ++ args.map (enc Γ) ++ post)[i]? = some (enc Γ args[i - off]) := by
    rw [List.append_assoc, List.getElem?_append_right (by omega), hpre, List.getElem?_append_left (by simpa using lt)]
    simp [List.getElem?_eq_getElem lt]
  rw [inst_fitPat, substOf, get] at iq
  simp only [Option.map_some, Option.some.injEq] at iq
  subst iq
  exact forall₂_get fitsD (List.getElem?_eq_getElem lt) hb

/-- **The `con` rule for a saturated application.** -/
theorem con_derivable {c : ℕ} {d : TermDecl} (hs : E.sig c = some d) {args : List Preterm}
    (fitsD : List.Forall₂ (FitD E Γ H fr) args d.arguments) :
    D E Γ H fr (tyJ d.resultSort (enc Γ (Preterm.applyArgs (.term c) args))) := by
  have len := fitsD.length_eq
  refine apply_rule (r := .con c) (ru := conRule c d) (a := args.map (enc Γ)) (by simp [rules, hs])
    (by simp [conRule, len]) (inst_fits_holds (by simp [len])) ?_ ?_
  · simp only [conRule, tyP, inst_pjd, instAll, inst_pnum]
    rw [← len, inst_spine c args 0 args.length (by simp), take_length_eq]
    rfl
  · intro q mq j iq
    exact fits_prem (pre := []) (post := []) rfl fitsD mq (by simpa using iq)

/-- What typing a preterm gives: a variable, or a spine of a term symbol whose arguments so far fit
their binders. -/
theorem spine_of_typed {e : Preterm} {rem : Context} {s : ℕ} (h : Preterm.HasType E.sig Γ e rem s) :
    (∃ i b, e = .var i ∧ Γ[i]? = some b ∧ rem = [] ∧ s = b.sort) ∨
      (∃ c d args consumed, e = Preterm.applyArgs (.term c) args ∧ E.sig c = some d ∧
        d.arguments = consumed ++ rem ∧ d.resultSort = s ∧
        List.Forall₂ (FitD E Γ H fr) args consumed) := by
  induction h with
  | var lookup => exact Or.inl ⟨_, _, rfl, lookup, rfl, rfl⟩
  | term lookup => exact Or.inr ⟨_, _, [], [], rfl, lookup, rfl, rfl, .nil⟩
  | @bound f index sort result remaining _ lookup ih =>
      rcases ih with ⟨i, b, rfl, -, hrem, -⟩ | ⟨c, d, args, consumed, rfl, hs, hargs, hres, fitsD⟩
      · cases hrem
      · refine Or.inr ⟨c, d, args ++ [.var index], consumed ++ [.bound sort], ?_, hs, by simp [hargs], hres, ?_⟩
        · rw [Preterm.applyArgs_append]; rfl
        · refine List.rel_append fitsD (.cons ?_ .nil)
          show D E Γ H fr (bvJ _ (enc Γ (.var _)))
          rw [enc_bound lookup]
          exact bv_hyp lookup
  | @regular f arg sort result deps remaining _ ha ihf iha =>
      rcases ihf with ⟨i, b, rfl, -, hrem, -⟩ | ⟨c, d, args, consumed, rfl, hs, hargs, hres, fitsD⟩
      · cases hrem
      · refine Or.inr ⟨c, d, args ++ [arg], consumed ++ [.regular sort deps], ?_, hs, by simp [hargs], hres, ?_⟩
        · rw [Preterm.applyArgs_append]; rfl
        · refine List.rel_append fitsD (.cons ?_ .nil)
          show D E Γ H fr (tyJ _ (enc Γ _))
          rcases iha with ⟨i, b, rfl, hb, -, rfl⟩ | ⟨c', d', args', consumed', rfl, hs', hargs', hres', fitsD'⟩
          · exact ty_var hb
          · simp only [List.append_nil] at hargs'
            rw [← hres']
            exact con_derivable hs' (hargs' ▸ fitsD')

/-- **Typing gives the `ty` judgment.** -/
theorem ty_derivable {e : Preterm} {s : ℕ} (h : Preterm.HasType E.sig Γ e [] s) :
    D E Γ H fr (tyJ s (enc Γ e)) := by
  rcases spine_of_typed (H := H) (fr := fr) h with ⟨i, b, rfl, hb, -, rfl⟩ | ⟨c, d, args, consumed, rfl, hs, hargs, hres, fitsD⟩
  · exact ty_var hb
  · simp only [List.append_nil] at hargs
    rw [← hres]
    exact con_derivable hs (hargs ▸ fitsD)

/-- **A fitting argument gives its fit judgment.** -/
theorem fit_derivable {e : Preterm} {b : Binder} (h : Preterm.FitsBinder E.sig Γ e b) :
    FitD E Γ H fr e b := by
  cases h with
  | bound hb => show D E Γ H fr (bvJ _ (enc Γ (.var _))); rw [enc_bound hb]; exact bv_hyp hb
  | regular ht => exact ty_derivable ht

theorem fits_derivable {es : List Preterm} {Φ : Context}
    (h : List.Forall₂ (Preterm.FitsBinder E.sig Γ) es Φ) : List.Forall₂ (FitD E Γ H fr) es Φ :=
  h.imp fun _ _ f => fit_derivable f

/-! ## Small rules -/

theorem substOf_get (a : List Tm) (k : ℕ) (lt : k < a.length) : substOf a k = some a[k] := by
  simp [substOf, List.getElem?_eq_getElem lt]

theorem cvRefl_derivable {e : Preterm} {s : ℕ} (typed : Preterm.HasType E.sig Γ e [] s) :
    D E Γ H fr (cvJ s (enc Γ e) (enc Γ e)) := by
  refine apply_rule (r := .cvRefl s) (ru := cvReflRule s) (a := [enc Γ e]) rfl rfl ?_ ?_ ?_
  · intro k mk
    simp only [cvReflRule, Rule.kinds, Premise.kind, List.map_cons, List.map_nil, List.mem_singleton] at mk
    subst mk
    exact holds_consume (j := tyJ s (enc Γ e)) (by simp [tyP, inst_pjd, instAll, inst_pnum, inst_pv, substOf, tyJ])
  · simp [cvReflRule, cv_inst, instAll, inst_pnum, inst_pv, substOf, cvJ]
  · intro q mq j iq
    simp only [cvReflRule, Rule.kinds, Premise.kind, List.map_cons, List.map_nil, List.mem_singleton,
      Kind.consume.injEq] at mq
    subst mq
    simp only [tyP, inst_pjd, instAll, inst_pnum, inst_pv, substOf] at iq
    simp only [List.getElem?_cons_zero, Option.map_some, Option.some.injEq] at iq
    subst iq
    exact ty_derivable typed

theorem cvSymm_derivable {e f : Preterm} {s : ℕ} (h : D E Γ H fr (cvJ s (enc Γ e) (enc Γ f))) :
    D E Γ H fr (cvJ s (enc Γ f) (enc Γ e)) := by
  refine apply_rule (r := .cvSymm) (ru := cvSymmRule) (a := [num s, enc Γ e, enc Γ f]) rfl rfl ?_ ?_ ?_
  · intro k mk
    simp only [cvSymmRule, Rule.kinds, Premise.kind, List.map_cons, List.map_nil, List.mem_singleton] at mk
    subst mk
    exact holds_consume (j := cvJ s (enc Γ e) (enc Γ f)) (by simp [cv_inst, instAll, inst_pv, substOf, cvJ])
  · simp [cvSymmRule, cv_inst, instAll, inst_pv, substOf, cvJ]
  · intro q mq j iq
    simp only [cvSymmRule, Rule.kinds, Premise.kind, List.map_cons, List.map_nil, List.mem_singleton,
      Kind.consume.injEq] at mq
    subst mq
    simp only [cv_inst, instAll, inst_pv, substOf] at iq
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.map_some, Option.some.injEq] at iq
    subst iq
    exact h

theorem cvTrans_derivable {e m f : Preterm} {s : ℕ} (h1 : D E Γ H fr (cvJ s (enc Γ e) (enc Γ m)))
    (h2 : D E Γ H fr (cvJ s (enc Γ m) (enc Γ f))) : D E Γ H fr (cvJ s (enc Γ e) (enc Γ f)) := by
  refine apply_rule (r := .cvTrans) (ru := cvTransRule) (a := [num s, enc Γ e, enc Γ m, enc Γ f]) rfl rfl ?_ ?_ ?_
  · intro k mk
    simp only [cvTransRule, Rule.kinds, Premise.kind, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at mk
    rcases mk with rfl | rfl
    · exact holds_consume (j := cvJ s (enc Γ e) (enc Γ m)) (by simp [cv_inst, instAll, inst_pv, substOf, cvJ])
    · exact holds_consume (j := cvJ s (enc Γ m) (enc Γ f)) (by simp [cv_inst, instAll, inst_pv, substOf, cvJ])
  · simp [cvTransRule, cv_inst, instAll, inst_pv, substOf, cvJ]
  · intro q mq j iq
    simp only [cvTransRule, Rule.kinds, Premise.kind, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false, Kind.consume.injEq] at mq
    rcases mq with rfl | rfl
    · simp only [cv_inst, instAll, inst_pv, substOf, List.getElem?_cons_zero, List.getElem?_cons_succ,
        Option.map_some, Option.some.injEq] at iq
      subst iq; exact h1
    · simp only [cv_inst, instAll, inst_pv, substOf, List.getElem?_cons_zero, List.getElem?_cons_succ,
        Option.map_some, Option.some.injEq] at iq
      subst iq; exact h2

theorem conv_derivable {e f : Preterm} {s : ℕ} (h1 : D E Γ H fr (cvJ s (enc Γ e) (enc Γ f)))
    (h2 : D E Γ H fr (pfJ (enc Γ e))) : D E Γ H fr (pfJ (enc Γ f)) := by
  refine apply_rule (r := .conv) (ru := convRule) (a := [num s, enc Γ e, enc Γ f]) rfl rfl ?_ ?_ ?_
  · intro k mk
    simp only [convRule, Rule.kinds, Premise.kind, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at mk
    rcases mk with rfl | rfl
    · exact holds_consume (j := cvJ s (enc Γ e) (enc Γ f)) (by simp [cv_inst, instAll, inst_pv, substOf, cvJ])
    · exact holds_consume (j := pfJ (enc Γ e)) (by simp [pfP, inst_pjd, instAll, inst_pv, substOf, pfJ])
  · simp [convRule, pfP, inst_pjd, instAll, inst_pv, substOf, pfJ]
  · intro q mq j iq
    simp only [convRule, Rule.kinds, Premise.kind, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false, Kind.consume.injEq] at mq
    rcases mq with rfl | rfl
    · simp only [cv_inst, instAll, inst_pv, substOf, List.getElem?_cons_zero, List.getElem?_cons_succ,
        Option.map_some, Option.some.injEq] at iq
      subst iq; exact h1
    · simp only [pfP, inst_pjd, instAll, inst_pv, substOf, List.getElem?_cons_zero, List.getElem?_cons_succ,
        Option.map_some, Option.some.injEq] at iq
      subst iq; exact h2

/-! ## Congruence and unfolding -/

theorem cong_derivable {c : ℕ} {d : TermDecl} (hs : E.sig c = some d) {ls rs : List Preterm}
    (fitL : List.Forall₂ (FitD E Γ H fr) ls d.arguments) (fitR : List.Forall₂ (FitD E Γ H fr) rs d.arguments)
    (each : ∀ (k : ℕ) (b : Binder) (l r : Preterm), d.arguments[k]? = some b → ls[k]? = some l →
      rs[k]? = some r → D E Γ H fr (cvJ b.sort (enc Γ l) (enc Γ r))) :
    D E Γ H fr (cvJ d.resultSort (enc Γ (Preterm.applyArgs (.term c) ls))
      (enc Γ (Preterm.applyArgs (.term c) rs))) := by
  set n := d.arguments.length with hn
  have hl : ls.length = n := fitL.length_eq
  have hr : rs.length = n := fitR.length_eq
  have vals : (ls ++ rs).map (enc Γ) = [] ++ ls.map (enc Γ) ++ rs.map (enc Γ) := by simp
  have vals' : (ls ++ rs).map (enc Γ) = ls.map (enc Γ) ++ rs.map (enc Γ) ++ [] := by simp
  have kindsEq : (cvCongRule c d).kinds = (fits 0 d.arguments).map Premise.kind ++
      (fits n d.arguments).map Premise.kind ++
      (d.arguments.zipIdx.map fun x => Premise.judg (cvP (pnum x.1.sort) (pv x.2) (pv (n + x.2)))).map
        Premise.kind := by
    simp [cvCongRule, Rule.kinds, List.map_append, hn]
  refine apply_rule (r := .cvCong c) (ru := cvCongRule c d) (a := (ls ++ rs).map (enc Γ))
    (by simp [rules, hs]) (by simp [cvCongRule, hl, hr, hn]) ?_ ?_ ?_
  · rw [kindsEq]
    intro k mk
    rcases List.mem_append.mp mk with mk | mk
    · rcases List.mem_append.mp mk with mk | mk
      · exact inst_fits_holds (by simp [hl, hr]; omega) k mk
      · exact inst_fits_holds (by simp [hl, hr]; omega) k mk
    · simp only [List.map_map, List.mem_map, Function.comp_def] at mk
      obtain ⟨⟨b, i⟩, mi, rfl⟩ := mk
      have lt : i < n := by have := (List.mem_zipIdx mi).2.1; omega
      have hi1 : i < (ls ++ rs).length := by simp; omega
      have hi2 : n + i < (ls ++ rs).length := by simp; omega
      have g1 : ((ls ++ rs).map (enc Γ))[i]? = some (enc Γ ((ls ++ rs)[i]'hi1)) := by
        rw [List.getElem?_map, List.getElem?_eq_getElem hi1]; rfl
      have g2 : ((ls ++ rs).map (enc Γ))[n + i]? = some (enc Γ ((ls ++ rs)[n + i]'hi2)) := by
        rw [List.getElem?_map, List.getElem?_eq_getElem hi2]; rfl
      exact holds_consume (q := cvP (pnum b.sort) (pv i) (pv (n + i)))
        (j := cvJ b.sort (enc Γ ((ls ++ rs)[i]'hi1)) (enc Γ ((ls ++ rs)[n + i]'hi2)))
        (by simp only [cv_inst, instAll, inst_pnum, inst_pv, substOf, g1, g2]; rfl)
  · have sl := inst_spine (Γ := Γ) c (ls ++ rs) 0 n (by simp [hl, hr])
    have sr := inst_spine (Γ := Γ) c (ls ++ rs) n n (by simp [hl, hr])
    rw [show ((ls ++ rs).drop 0).take n = ls by simp [← hl]] at sl
    rw [show ((ls ++ rs).drop n).take n = rs by
      rw [List.drop_left' hl, List.take_of_length_le (le_of_eq hr)]] at sr
    simp only [cvCongRule, ← hn, cv_inst, instAll, inst_pnum, sl, sr]
    rfl
  · intro q mq j iq
    rw [kindsEq] at mq
    rcases List.mem_append.mp mq with mq | mq
    · rcases List.mem_append.mp mq with mq | mq
      · rw [vals] at iq; exact fits_prem (pre := []) (post := rs.map (enc Γ)) rfl fitL mq iq
      · rw [vals'] at iq
        exact fits_prem (pre := ls.map (enc Γ)) (post := []) (by simp [hl]) fitR mq iq
    · simp only [List.map_map, List.mem_map, Function.comp_def, Premise.kind, Kind.consume.injEq] at mq
      obtain ⟨⟨b, i⟩, mi, rfl⟩ := mq
      have hb : d.arguments[i]? = some b := List.mem_zipIdx_iff_getElem?.mp mi
      have lt : i < n := by rw [hn]; exact (List.getElem?_eq_some_iff.mp hb).1
      have g1 : (ls ++ rs)[i]? = some ls[i] := by
        rw [List.getElem?_append_left (by omega)]; exact List.getElem?_eq_getElem (by omega)
      have g2 : (ls ++ rs)[n + i]? = some rs[i] := by
        rw [List.getElem?_append_right (by omega), hl, show n + i - n = i by omega]
        exact List.getElem?_eq_getElem (by omega)
      simp only [cv_inst, instAll, inst_pnum, inst_pv_map, g1, g2, Option.map_some,
        Option.some.injEq] at iq
      subst iq
      exact each i b _ _ hb (List.getElem?_eq_getElem (by omega)) (List.getElem?_eq_getElem (by omega))

/-- What fresh dummies give, pointwise. -/
theorem freshDummies_get :
    ∀ {args : List Preterm} {ds images : List ℕ}, Definition.FreshDummies Γ args ds images →
      images.length = ds.length ∧
      (∀ (j s i : ℕ), ds[j]? = some s → images[j]? = some i → Γ[i]? = some (.bound s)) ∧
      (∀ (j i : ℕ) (e : Preterm), images[j]? = some i → e ∈ args ++ (images.take j).map Preterm.var →
        ¬ Preterm.HasVar Γ i e)
  | _, _, _, .nil _ => ⟨rfl, fun _ _ _ h => by simp at h, fun _ _ _ h => by simp at h⟩
  | args, s :: ds, i :: images, .cons hb fresh rest => by
      obtain ⟨len, bound, fr⟩ := freshDummies_get rest
      refine ⟨by simp [len], fun j s' i' h1 h2 => ?_, fun j i' e h me => ?_⟩
      · cases j with
        | zero => simp at h1 h2; subst h1 h2; exact hb
        | succ j => exact bound j s' i' (by simpa using h1) (by simpa using h2)
      · cases j with
        | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at h
            subst h
            simp only [List.take_zero, List.map_nil, List.append_nil] at me
            exact (fresh e me).2
        | succ j =>
            refine fr j i' e (by simpa using h) ?_
            simp only [List.take_succ_cons, List.map_cons, List.mem_append, List.mem_cons] at me ⊢
            tauto

theorem unfold_derivable {c : ℕ} {d : TermDecl} (hs : E.sig c = some d) {args : List Preterm}
    {images : List ℕ} {result : Preterm} (unf : Definition.Unfolds E.sig E.defs Γ c args images result)
    (typed : Preterm.HasType E.sig Γ result [] d.resultSort) :
    D E Γ H fr (cvJ d.resultSort (enc Γ (Preterm.applyArgs (.term c) args)) (enc Γ result)) := by
  obtain ⟨hs', hd, fitA, freshD, sub⟩ := unf
  rw [hs] at hs'
  cases hs'
  rename_i b
  set n := d.arguments.length with hn
  set m := b.dummies.length with hm
  obtain ⟨hlen, bound, frD⟩ := freshDummies_get freshD
  have hal : args.length = n := fitA.length_eq
  set vals := args ++ images.map Preterm.var with hvals
  have encImg : ∀ (j i : ℕ), j < m → images[j]? = some i → enc Γ (.var i) = fvar i := by
    intro j i lt hi
    obtain ⟨s, hs2⟩ : ∃ s, b.dummies[j]? = some s := ⟨_, List.getElem?_eq_getElem lt⟩
    exact enc_bound (bound j s i hs2 hi)
  have kindsEq : (unfoldRule c d b).kinds = (fits 0 d.arguments).map Premise.kind ++
      (dummyFits n b.dummies).map Premise.kind ++ [Kind.consume (tyP (pnum d.resultSort) (patOf b.expression))] ++
      (fresh n m).map Premise.kind := by
    simp [unfoldRule, Rule.kinds, List.map_append, hn, hm, Premise.kind]
  have instBody : (patOf b.expression).inst (substOf (vals.map (enc Γ))) = some (enc Γ result) := by
    rw [inst_patOf]
    have e := sub.eval
    change Preterm.substitute (Substitution.ofList vals) b.expression = some result at e
    rw [e]; rfl
  have valsGet : ∀ k (lt : k < vals.length), (vals.map (enc Γ))[k]? = some (enc Γ vals[k]) := by
    intro k lt; simp [List.getElem?_eq_getElem lt]
  have vlen : vals.length = n + m := by simp [hvals, hal, hlen, hm]
  refine apply_rule (r := .unfold c) (ru := unfoldRule c d b) (a := vals.map (enc Γ))
    (by simp [rules, hs, hd]) (by simp [unfoldRule, vlen, hn, hm]) ?_ ?_ ?_
  · rw [kindsEq]
    intro k mk
    rcases List.mem_append.mp mk with mk | mk
    · rcases List.mem_append.mp mk with mk | mk
      · rcases List.mem_append.mp mk with mk | mk
        · exact inst_fits_holds (by simp [vlen, hn]) k mk
        · simp only [dummyFits, List.map_map, List.mem_map, Function.comp_def] at mk
          obtain ⟨⟨s, i⟩, mi, rfl⟩ := mk
          have lt : i < n + m := by have := (List.mem_zipIdx mi).2.1; omega
          exact holds_consume (j := bvJ s (enc Γ vals[i]))
            (by simp [bvP, inst_pjd, instAll, inst_pnum, inst_pv, substOf, bvJ, valsGet i (by omega)])
      · simp only [List.mem_singleton] at mk
        subst mk
        exact holds_consume (j := tyJ d.resultSort (enc Γ result))
          (by simp [tyP, inst_pjd, instAll, inst_pnum, instBody, tyJ])
    · simp only [fresh, List.map_flatMap, List.mem_flatMap, List.mem_range, List.map_map, List.mem_map,
        Function.comp_def] at mk
      obtain ⟨j, jlt, k, klt, rfl⟩ := mk
      obtain ⟨i, hi⟩ : ∃ i, images[j]? = some i := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      have nj : vals[n + j]? = some (.var i) := by
        rw [hvals, List.getElem?_append_right (by omega), hal, show n + j - n = j by omega,
          List.getElem?_map, hi]; rfl
      have kv : k < vals.length := by omega
      refine (holds_absent fr _ _ _).mpr ⟨enc Γ (.var i), enc Γ vals[k], ?_, ?_, ?_⟩
      · rw [inst_pv, substOf, List.getElem?_map, nj]; rfl
      · rw [inst_pv, substOf, valsGet k kv]
      · obtain ⟨s, hs2⟩ : ∃ s, b.dummies[j]? = some s := ⟨_, List.getElem?_eq_getElem (by omega)⟩
        refine (absentOk_enc Γ (bound j s i hs2 hi) _).mpr (frD j i _ hi ?_)
        have mem : vals[k] ∈ vals.take (n + j) := by
          have hk2 : k < (vals.take (n + j)).length := by simp; omega
          have := List.getElem_mem hk2
          rwa [List.getElem_take] at this
        have : vals.take (n + j) = args ++ (images.take j).map Preterm.var := by
          rw [hvals, List.take_append, List.take_of_length_le (by omega), hal,
            show n + j - n = j by omega, List.map_take]
        rw [this] at mem
        exact mem
  · simp only [unfoldRule, ← hn, cv_inst, instAll, inst_pnum, instBody]
    rw [inst_spine c vals 0 n (by simp [vlen]), show (vals.drop 0).take n = args by
      rw [List.drop_zero, hvals, List.take_append, List.take_of_length_le (le_of_eq hal), hal,
        Nat.sub_self, List.take_zero, List.append_nil]]
    rfl
  · intro q mq j iq
    rw [kindsEq] at mq
    rcases List.mem_append.mp mq with mq | mq
    · rcases List.mem_append.mp mq with mq | mq
      · rcases List.mem_append.mp mq with mq | mq
        · rw [show vals.map (enc Γ) = [] ++ args.map (enc Γ) ++ (images.map Preterm.var).map (enc Γ) by
            simp [hvals]] at iq
          exact fits_prem (pre := []) rfl (fits_derivable fitA) mq iq
        · simp only [dummyFits, List.map_map, List.mem_map, Function.comp_def, Premise.kind,
            Kind.consume.injEq] at mq
          obtain ⟨⟨s, k⟩, mk, rfl⟩ := mq
          obtain ⟨le, hsk⟩ := List.mem_zipIdx_iff_le_and_getElem?_sub.mp mk
          have jlt : k - n < m := by rw [hm]; exact (List.getElem?_eq_some_iff.mp hsk).1
          obtain ⟨i, hi⟩ : ∃ i, images[k - n]? = some i := ⟨_, List.getElem?_eq_getElem (by omega)⟩
          have nk : vals[k]? = some (.var i) := by
            rw [hvals, List.getElem?_append_right (by omega), hal, List.getElem?_map, hi]; rfl
          simp only [bvP, inst_pjd, instAll, inst_pnum, inst_pv, substOf, List.getElem?_map, nk,
            Option.map_some, Option.some.injEq] at iq
          subst iq
          have hb := bound (k - n) s i hsk hi
          rw [enc_bound hb]
          exact bv_hyp hb
      · simp only [List.mem_singleton, Kind.consume.injEq] at mq
        subst mq
        simp only [tyP, inst_pjd, instAll, inst_pnum, instBody, Option.map_some, Option.some.injEq] at iq
        subst iq
        exact ty_derivable typed
    · simp only [fresh, List.map_flatMap, List.mem_flatMap, List.mem_range, List.map_map, List.mem_map,
        Function.comp_def, Premise.kind] at mq
      obtain ⟨_, _, _, _, h⟩ := mq
      cases h

/-! ## Conversion -/

/-- **MM0's conversion gives the `cv` judgment.** -/
theorem cv_derivable {e f : Preterm} {s : ℕ} (h : Converts E.sig E.defs Γ e f s) :
    D E Γ H fr (cvJ s (enc Γ e) (enc Γ f)) := by
  induction h using Converts.rec
      (motive_2 := fun ls rs Φ _ => List.Forall₂ (FitD E Γ H fr) ls Φ ∧ List.Forall₂ (FitD E Γ H fr) rs Φ ∧
        ∀ (k : ℕ) (b : Binder) (l r : Preterm), Φ[k]? = some b → ls[k]? = some l → rs[k]? = some r →
          D E Γ H fr (cvJ b.sort (enc Γ l) (enc Γ r))) with
  | refl typed => exact cvRefl_derivable typed
  | symm _ ih => exact cvSymm_derivable ih
  | trans _ _ ih1 ih2 => exact cvTrans_derivable ih1 ih2
  | congruence lookup _ ih => exact cong_derivable lookup ih.1 ih.2.1 ih.2.2
  | unfold lookup unfolded typed => exact unfold_derivable lookup unfolded typed
  | nil => exact ⟨.nil, .nil, fun k b l r h => by simp at h⟩
  | cons fl fr' _ _ ihc iht =>
      refine ⟨.cons (fit_derivable fl) iht.1, .cons (fit_derivable fr') iht.2.1, fun k b l r hb hl hr => ?_⟩
      cases k with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hb hl hr
          subst hb hl hr
          exact ihc
      | succ k => exact iht.2.2 k b l r (by simpa using hb) (by simpa using hl) (by simpa using hr)

/-! ## Theorem application -/

theorem forall₂_left_mem {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ x ∈ l₁, ∃ y ∈ l₂, R x y
  | [], [], _, x, m => by simp at m
  | a :: as, b :: bs, .cons hab rest, x, m => by
      rcases List.mem_cons.mp m with rfl | m
      · exact ⟨b, List.mem_cons_self, hab⟩
      · obtain ⟨y, my, r⟩ := forall₂_left_mem rest x m
        exact ⟨y, List.mem_cons_of_mem _ my, r⟩

theorem indep_decode {Φ : Context} {pr : Premise} (m : pr ∈ indep Φ) :
    ∃ p q s b', pr = .absent (pv p) (pv q) ∧ Φ[p]? = some (.bound s) ∧ Φ[q]? = some b' ∧
      ¬ b'.DependsOn q p := by
  simp only [indep, List.mem_flatMap] at m
  obtain ⟨⟨b, p⟩, mp, mr⟩ := m
  have hp : Φ[p]? = some b := List.mem_zipIdx_iff_getElem?.mp mp
  cases b with
  | regular _ _ => simp at mr
  | bound s =>
      simp only [List.mem_filterMap] at mr
      obtain ⟨⟨b', q⟩, mq, hr⟩ := mr
      have hq : Φ[q]? = some b' := List.mem_zipIdx_iff_getElem?.mp mq
      by_cases nd : b'.DependsOn q p
      · simp [nd] at hr
      · simp only [nd, ↓reduceIte, Option.some.injEq] at hr
        exact ⟨p, q, s, b', hr.symm, hp, hq, nd⟩

theorem thm_derivable {t : ℕ} {d : TheoremDecl} (ht : E.thms t = some d) {es : List Preterm}
    {inst : TheoremInstance} (hinst : TheoremDecl.Instantiates E.sig Γ d es inst)
    (hyps : ∀ x ∈ inst.hypotheses, D E Γ H fr (pfJ (enc Γ x))) :
    D E Γ H fr (pfJ (enc Γ inst.conclusion)) := by
  obtain ⟨⟨typed, independent⟩, hypsSub, conclSub⟩ := hinst
  have len : es.length = d.arguments.length := typed.length_eq
  have kindsEq : (thmRule d).kinds = (fits 0 d.arguments).map Premise.kind ++
      (d.hypotheses.map fun h => Premise.judg (pfP (patOf h))).map Premise.kind ++
      (indep d.arguments).map Premise.kind := by
    simp [thmRule, Rule.kinds, List.map_append]
  have hypInst : ∀ h ∈ d.hypotheses, ∃ r ∈ inst.hypotheses,
      (pfP (patOf h)).inst (substOf (es.map (enc Γ))) = some (pfJ (enc Γ r)) := by
    intro h mh
    obtain ⟨r, mr, sub⟩ := forall₂_left_mem hypsSub h mh
    refine ⟨r, mr, ?_⟩
    simp only [pfP, inst_pjd, instAll, inst_patOf, sub.eval, Option.map_some]
    rfl
  have esGet : ∀ k (lt : k < es.length), (es.map (enc Γ))[k]? = some (enc Γ es[k]) := by
    intro k lt; simp [List.getElem?_eq_getElem lt]
  refine apply_rule (r := .thm t) (ru := thmRule d) (a := es.map (enc Γ)) (by simp [rules, ht])
    (by simp [thmRule, len]) ?_ ?_ ?_
  · rw [kindsEq]
    intro k mk
    rcases List.mem_append.mp mk with mk | mk
    · rcases List.mem_append.mp mk with mk | mk
      · exact inst_fits_holds (by simp [len]) k mk
      · simp only [List.map_map, List.mem_map, Function.comp_def] at mk
        obtain ⟨h, mh, rfl⟩ := mk
        obtain ⟨r, -, hr⟩ := hypInst h mh
        exact holds_consume hr
    · simp only [List.mem_map] at mk
      obtain ⟨pr, mpr, rfl⟩ := mk
      obtain ⟨p, q, s, b', rfl, hp, hq, nd⟩ := indep_decode mpr
      have pl : p < es.length := by rw [len]; exact (List.getElem?_eq_some_iff.mp hp).1
      have ql : q < es.length := by rw [len]; exact (List.getElem?_eq_some_iff.mp hq).1
      have fp := forall₂_get typed (List.getElem?_eq_getElem pl) hp
      cases hfp : es[p] with
      | var image =>
          rw [hfp] at fp
          cases fp with
          | bound hbound =>
              refine (holds_absent fr _ _ _).mpr ⟨enc Γ (.var image), enc Γ es[q], ?_, ?_, ?_⟩
              · rw [inst_pv, substOf, esGet p pl, hfp]
              · rw [inst_pv, substOf, esGet q ql]
              · refine (absentOk_enc Γ hbound _).mpr ?_
                have me : ((.bound s, .var image), p) ∈ Substitution.entries d.arguments es := by
                  apply List.mem_zipIdx_iff_getElem?.mpr
                  exact List.getElem?_zip_eq_some.mpr ⟨hp, by rw [List.getElem?_eq_getElem pl, hfp]⟩
                have mo : ((b', es[q]), q) ∈ Substitution.entries d.arguments es := by
                  apply List.mem_zipIdx_iff_getElem?.mpr
                  exact List.getElem?_zip_eq_some.mpr ⟨hq, List.getElem?_eq_getElem ql⟩
                exact independent _ me s image rfl _ mo nd
      | term c => rw [hfp] at fp; cases fp
      | app f x => rw [hfp] at fp; cases fp
  · simp only [thmRule, pfP, inst_pjd, instAll, inst_patOf, conclSub.eval, Option.map_some]
    rfl
  · intro q mq j iq
    rw [kindsEq] at mq
    rcases List.mem_append.mp mq with mq | mq
    · rcases List.mem_append.mp mq with mq | mq
      · rw [show es.map (enc Γ) = [] ++ es.map (enc Γ) ++ [] by simp] at iq
        exact fits_prem (pre := []) rfl (fits_derivable typed) mq iq
      · simp only [List.map_map, List.mem_map, Function.comp_def, Premise.kind, Kind.consume.injEq] at mq
        obtain ⟨h, mh, rfl⟩ := mq
        obtain ⟨r, mr, hr⟩ := hypInst h mh
        rw [hr] at iq
        cases iq
        exact hyps r mr
    · simp only [List.mem_map] at mq
      obtain ⟨pr, mpr, hpr⟩ := mq
      obtain ⟨p, q', s, b', rfl, -, -, -⟩ := indep_decode mpr
      cases hpr

/-! ## Derivations -/

/-- **MM0's derivations give the `pf` judgment.** -/
theorem pf_derivable {e : Preterm} (h : Derives E.sig E.defs E.thms Γ H e) :
    D E Γ H fr (pfJ (enc Γ e)) := by
  induction h using Derives.rec (motive_2 := fun es _ => ∀ x ∈ es, D E Γ H fr (pfJ (enc Γ x))) with
  | hypothesis m => exact Derivable.hyp (List.mem_append_right _ (List.mem_map_of_mem m))
  | theoremApp lookup inst _ ih => exact thm_derivable lookup inst ih
  | conversion conv _ ih => exact conv_derivable (cv_derivable conv) ih
  | nil => rename_i x m; simp at m
  | cons _ _ ih1 ih2 =>
      rename_i x m
      rcases List.mem_cons.mp m with rfl | m
      · exact ih1
      · exact ih2 x m

/-- **MM0 adequacy of the presentation**: from the context's hypotheses and the claim's
hypotheses, the presentation derives `(pf E)` exactly when Mettapedia's MM0 kernel derives `E`. -/
theorem derivable_iff_derives (fr : Frame) (e : Preterm) :
    Derivable (presOf (rules E) fr) (hypsOf Γ H) (pfJ (enc Γ e)) ↔ Derives E.sig E.defs E.thms Γ H e :=
  ⟨derivable_pf_derives fr, pf_derivable⟩

end Mettapedia.Logic.TierZero.Adequacy.MM0
