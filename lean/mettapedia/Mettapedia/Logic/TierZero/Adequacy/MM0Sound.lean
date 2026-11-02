import Mettapedia.Logic.TierZero.Adequacy.MM0Pres

/-!
# MM0 adequacy, soundness: what the kernel derives, MM0 derives

Every judgment derivable in the presentation of an MM0 environment, from the context's hypotheses
and the claim's hypotheses, means what it says in Mettapedia's MM0 kernel (`Good`):

* `(bv s X)`: `X` is a bound variable of sort `s` of the context;
* `(ty s E)`: `E` encodes a preterm of sort `s` (`HasType … [] s`);
* `(cv s E F)`: `E`, `F` encode convertible preterms (`Converts … s`);
* `(pf E)`: `E` encodes a preterm MM0 derives (`Derives`).

`derivable_good` is proved rule by rule. The independence conditions of a theorem's rule are, by
`occursIn_enc`, exactly MM0's `Admissible.independent`; the dummies' freshness conditions of an
unfolding are exactly `FreshDummies`.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.MM0

open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources
open Mettapedia.Logic.TierZero
open Mettapedia.Logic.TierZero.Kernel2
open Mettapedia.Languages.MM0.Kernel

/-! ## Instantiating judgment patterns -/

theorem inst_pflds (σ : Subst ℕ Tm) : ∀ ps : List Pat, TreePatFields.inst σ (pflds ps) = (instAll σ ps).map flds
  | [] => rfl
  | p :: ps => by
      simp only [pflds, TreePatFields.inst, inst_pflds σ ps, instAll]
      cases p.inst σ <;> cases instAll σ ps <;> rfl

theorem inst_pjd (σ : Subst ℕ Tm) (h : String) (ps : List Pat) :
    (pjd h ps).inst σ = (instAll σ ps).map (jd h) := by
  simp only [pjd, pex, TreePat.inst, inst_pflds, instAll, psym, TreePatFields.inst]
  cases instAll σ ps <;> rfl

theorem inst_pnum (σ : Subst ℕ Tm) (s : ℕ) : (pnum s).inst σ = some (num s) := rfl

theorem inst_pv (σ : Subst ℕ Tm) (k : ℕ) : (pv k).inst σ = σ k := rfl

theorem inst_fitPat (σ : Subst ℕ Tm) (b : Binder) (k : ℕ) :
    (fitPat b k).inst σ = (σ k).map (fitJ b) := by
  cases b with
  | bound s =>
      simp only [fitPat, bvP, inst_pjd, instAll, inst_pnum, inst_pv]
      cases σ k <;> rfl
  | regular s D =>
      simp only [fitPat, tyP, inst_pjd, instAll, inst_pnum, inst_pv]
      cases σ k <;> rfl

/-! ## Judgments are told apart by their heads -/

theorem flds_inj : ∀ {as bs : List Tm}, flds as = flds bs → as = bs
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [flds] at h
  | _ :: _, [], h => by simp [flds] at h
  | a :: as, b :: bs, h => by
      simp only [flds, Fields.cons.injEq, true_and] at h
      rw [h.1, flds_inj h.2]

theorem jd_inj {h h' : String} {as bs : List Tm} (e : jd h as = jd h' bs) : h = h' ∧ as = bs := by
  simp only [jd, ex, Term.node.injEq, true_and] at e
  have := flds_inj e
  simp only [List.cons.injEq, sym, Term.node.injEq, Head.sym.injEq, and_true] at this
  exact this

/-! ## What derivable judgments mean -/

variable (E : MM0Env) (Γ : Context) (H : List Preterm)

/-- **The meaning of a judgment in MM0.** -/
def Good (j : Tm) : Prop :=
  (∃ s i, j = bvJ s (fvar i) ∧ Γ[i]? = some (.bound s)) ∨
    (∃ s e, j = tyJ s (enc Γ e) ∧ Preterm.HasType E.sig Γ e [] s) ∨
    (∃ s e f, j = cvJ s (enc Γ e) (enc Γ f) ∧ Converts E.sig E.defs Γ e f s) ∨
    (∃ e, j = pfJ (enc Γ e) ∧ Derives E.sig E.defs E.thms Γ H e)

/-- The hypotheses of a claim in the context `Γ` with MM0 hypotheses `H`. -/
def hypsOf : List Tm := ctxHyps Γ ++ H.map (fun h => pfJ (enc Γ h))

variable {E Γ H}

theorem num_inj {s s' : ℕ} (h : num s = num s') : s = s' := by
  simpa [num] using h

theorem good_bv {s : ℕ} {x : Tm} (h : Good E Γ H (bvJ s x)) :
    ∃ i, x = fvar i ∧ Γ[i]? = some (.bound s) := by
  rcases h with ⟨s', i, e, hb⟩ | ⟨s', e', eq, _⟩ | ⟨s', e', f', eq, _⟩ | ⟨e', eq, _⟩
  · obtain ⟨-, args⟩ := jd_inj e
    simp only [List.cons.injEq, and_true] at args
    rw [num_inj args.1] at *
    exact ⟨i, args.2, hb⟩
  · exact absurd (jd_inj eq).1 (by decide)
  · exact absurd (jd_inj eq).1 (by decide)
  · exact absurd (jd_inj eq).1 (by decide)

theorem good_ty {s : ℕ} {x : Tm} (h : Good E Γ H (tyJ s x)) :
    ∃ e, x = enc Γ e ∧ Preterm.HasType E.sig Γ e [] s := by
  rcases h with ⟨s', i, eq, _⟩ | ⟨s', e', eq, ht⟩ | ⟨s', e', f', eq, _⟩ | ⟨e', eq, _⟩
  · exact absurd (jd_inj eq).1 (by decide)
  · obtain ⟨-, args⟩ := jd_inj eq
    simp only [List.cons.injEq, and_true] at args
    rw [num_inj args.1]
    exact ⟨e', args.2, ht⟩
  · exact absurd (jd_inj eq).1 (by decide)
  · exact absurd (jd_inj eq).1 (by decide)

theorem good_cv {sx x y : Tm} (h : Good E Γ H (jd "cv" [sx, x, y])) :
    ∃ s e f, sx = num s ∧ x = enc Γ e ∧ y = enc Γ f ∧ Converts E.sig E.defs Γ e f s := by
  rcases h with ⟨s', i, eq, _⟩ | ⟨s', e', eq, _⟩ | ⟨s', e', f', eq, hc⟩ | ⟨e', eq, _⟩
  · exact absurd (jd_inj eq).1 (by decide)
  · exact absurd (jd_inj eq).1 (by decide)
  · obtain ⟨-, args⟩ := jd_inj eq
    simp only [List.cons.injEq, and_true] at args
    exact ⟨s', e', f', args.1, args.2.1, args.2.2, hc⟩
  · exact absurd (jd_inj eq).1 (by decide)

theorem good_pf {x : Tm} (h : Good E Γ H (pfJ x)) :
    ∃ e, x = enc Γ e ∧ Derives E.sig E.defs E.thms Γ H e := by
  rcases h with ⟨s', i, eq, _⟩ | ⟨s', e', eq, _⟩ | ⟨s', e', f', eq, _⟩ | ⟨e', eq, hd⟩
  · exact absurd (jd_inj eq).1 (by decide)
  · exact absurd (jd_inj eq).1 (by decide)
  · exact absurd (jd_inj eq).1 (by decide)
  · obtain ⟨-, args⟩ := jd_inj eq
    simp only [List.cons.injEq, and_true] at args
    exact ⟨e', args, hd⟩

/-! ## The context's hypotheses mean what they say -/

theorem enc_bound {i s : ℕ} (h : Γ[i]? = some (.bound s)) : enc Γ (.var i) = fvar i := by
  simp [enc, encVar, h]

theorem good_ctxHyps {j : Tm} (m : j ∈ ctxHyps Γ) : Good E Γ H j := by
  simp only [ctxHyps, List.mem_flatMap] at m
  obtain ⟨⟨b, i⟩, mb, mj⟩ := m
  have hb : Γ[i]? = some b := List.mem_zipIdx_iff_getElem?.mp mb
  cases b with
  | bound s =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mj
      rcases mj with rfl | rfl
      · exact Or.inl ⟨s, i, rfl, hb⟩
      · refine Or.inr (Or.inl ⟨s, .var i, by rw [enc_bound hb], ?_⟩)
        exact .var hb
  | regular s D =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mj
      subst mj
      refine Or.inr (Or.inl ⟨s, .var i, by simp [enc, encVar, hb], ?_⟩)
      exact .var hb

theorem good_hyps {j : Tm} (m : j ∈ hypsOf Γ H) : Good E Γ H j := by
  rcases List.mem_append.mp m with m | m
  · exact good_ctxHyps m
  · obtain ⟨h, mh, rfl⟩ := List.mem_map.mp m
    exact Or.inr (Or.inr (Or.inr ⟨h, rfl, .hypothesis mh⟩))

/-! ## Reading the arguments of an instance -/

/-- The judgment premise of a binder, as a kind of `fits`. -/
theorem fit_mem {off : ℕ} {Φ : Context} {k : ℕ} {b : Binder} (hk : Φ[k]? = some b) :
    Kind.consume (fitPat b (off + k)) ∈ (fits off Φ).map Premise.kind := by
  simp only [fits, List.map_map, List.mem_map, Function.comp_def]
  refine ⟨(b, off + k), ?_, rfl⟩
  rw [List.mem_zipIdx_iff_le_and_getElem?_sub]
  simpa using hk

/-- **Each argument of an instance fits its binder.** -/
theorem fit_decode {fr : Frame} {a ps : List Tm} {ks : List Kind} {off : ℕ} {Φ : Context}
    (hi : instKinds fr (substOf a) ks = some ps) (sub : ∀ k ∈ (fits off Φ).map Premise.kind, k ∈ ks)
    (good : ∀ j ∈ ps, Good E Γ H j) {k : ℕ} {b : Binder} (hk : Φ[k]? = some b) :
    ∃ e, a[off + k]? = some (enc Γ e) ∧ Preterm.FitsBinder E.sig Γ e b := by
  obtain ⟨j, mj, ij⟩ := instKinds_consume _ _ hi _ (sub _ (fit_mem hk))
  rw [inst_fitPat] at ij
  cases ha : a[off + k]? with
  | none => simp [substOf, ha] at ij
  | some v =>
      simp only [substOf, ha, Option.map_some, Option.some.injEq] at ij
      subst ij
      cases b with
      | bound s =>
          obtain ⟨i, rfl, hb⟩ := good_bv (good _ mj)
          exact ⟨.var i, by rw [enc_bound hb], .bound hb⟩
      | regular s D =>
          obtain ⟨e, rfl, ht⟩ := good_ty (good _ mj)
          exact ⟨e, rfl, .regular ht⟩

/-- Read the arguments back as a list. -/
def readArgs (a : List Tm) (off n : ℕ) : List Preterm :=
  (List.range n).map fun k => ((a[off + k]?).bind dec).getD (.term 0)

theorem readArgs_get {a : List Tm} {off n k : ℕ} (lt : k < n) {e : Preterm}
    (h : a[off + k]? = some (enc Γ e)) : (readArgs a off n)[k]? = some e := by
  simp [readArgs, List.getElem?_range lt, h, dec_enc]

theorem length_readArgs (a : List Tm) (off n : ℕ) : (readArgs a off n).length = n := by
  simp [readArgs]

/-- **The arguments of an instance, read back, fit their binders.** -/
theorem read_fits {fr : Frame} {a ps : List Tm} {ks : List Kind} {off : ℕ} {Φ : Context}
    (hi : instKinds fr (substOf a) ks = some ps) (sub : ∀ k ∈ (fits off Φ).map Premise.kind, k ∈ ks)
    (good : ∀ j ∈ ps, Good E Γ H j) :
    List.Forall₂ (Preterm.FitsBinder E.sig Γ) (readArgs a off Φ.length) Φ ∧
      ∀ k < Φ.length, a[off + k]? = (readArgs a off Φ.length)[k]?.map (enc Γ) := by
  have each : ∀ k (lt : k < Φ.length), ∃ e, a[off + k]? = some (enc Γ e) ∧
      Preterm.FitsBinder E.sig Γ e Φ[k] := fun k lt =>
    fit_decode hi sub good (List.getElem?_eq_getElem lt)
  refine ⟨List.forall₂_iff_zip.mpr ⟨length_readArgs _ _ _, ?_⟩, ?_⟩
  · intro e b m
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp m
    rw [List.getElem?_zip_eq_some] at hk
    obtain ⟨he, hb⟩ := hk
    have lt : k < Φ.length := (List.getElem?_eq_some_iff.mp hb).1
    obtain ⟨e', ha, fit⟩ := each k lt
    rw [readArgs_get lt ha] at he
    cases he
    rw [List.getElem?_eq_getElem lt] at hb
    cases hb
    exact fit
  · intro k lt
    obtain ⟨e', ha, -⟩ := each k lt
    rw [readArgs_get lt ha, ha]; rfl

/-! ## Substituting the formals of a spine -/

theorem substitutes_vars (vals : List Preterm) :
    ∀ (off n : ℕ), off + n ≤ vals.length →
      List.Forall₂ (Preterm.Substitutes (Substitution.ofList vals)) (varsP off n) ((vals.drop off).take n)
  | _, 0, _ => by simp [varsP]
  | off, n + 1, le => by
      have lt : off < vals.length := by omega
      have rest := substitutes_vars vals (off + 1) n (by omega)
      rw [show varsP off (n + 1) = .var off :: varsP (off + 1) n by simp [varsP, List.range'_succ]]
      rw [show (vals.drop off).take (n + 1) = vals[off] :: (vals.drop (off + 1)).take n by
        rw [List.drop_eq_getElem_cons lt, List.take_succ_cons]]
      exact .cons (.var (by simp [Substitution.ofList, List.getElem?_eq_getElem lt])) rest

/-- **The spine of formals, instantiated, is the spine of the arguments.** -/
theorem inst_spine (c : ℕ) (vals : List Preterm) (off n : ℕ) (le : off + n ≤ vals.length) :
    (patOf (Preterm.applyArgs (.term c) (varsP off n))).inst (substOf (vals.map (enc Γ))) =
      some (enc Γ (Preterm.applyArgs (.term c) ((vals.drop off).take n))) := by
  rw [inst_patOf, (Preterm.Substitutes.applyArgs _ _ _ _ _ (.term c) (substitutes_vars vals off n le)).eval]
  rfl

theorem take_length_eq {α : Type} (l : List α) : (l.drop 0).take l.length = l := by simp

/-- The values of an instance whose arguments are read back. -/
theorem vals_eq {a : List Tm} {es : List Preterm} (len : a.length = es.length)
    (each : ∀ k < es.length, a[k]? = es[k]?.map (enc Γ)) : a = es.map (enc Γ) := by
  apply List.ext_getElem?
  intro k
  by_cases lt : k < es.length
  · rw [each k lt, List.getElem?_map]
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]

/-! ## Soundness, rule by rule -/

theorem sound_con {fr : Frame} {c : ℕ} {d : TermDecl} (hs : E.sig c = some d) {a ps : List Tm} {cl : Tm}
    (hi : (conRule c d).instance fr a = some (ps, cl)) (good : ∀ j ∈ ps, Good E Γ H j) :
    Good E Γ H cl := by
  obtain ⟨len, hk, hc⟩ := (instance_iff fr _ a ps cl).mp hi
  obtain ⟨fit, agree⟩ := read_fits (off := 0) hk (fun k m => m) good
  set es := readArgs a 0 d.arguments.length
  have hes : es.length = d.arguments.length := length_readArgs _ _ _
  have ha : a = es.map (enc Γ) := vals_eq (by rw [len, hes]; rfl)
    (fun k lt => by rw [hes] at lt; simpa using agree k lt)
  rw [ha] at hc
  simp only [conRule, tyP, inst_pjd, instAll, inst_pnum] at hc
  rw [show d.arguments.length = es.length from hes.symm] at hc
  rw [inst_spine c es 0 es.length (by simp), take_length_eq] at hc
  simp only [Option.map_some, Option.some.injEq] at hc
  subst hc
  refine Or.inr (Or.inl ⟨d.resultSort, Preterm.applyArgs (.term c) es, rfl, ?_⟩)
  exact (Preterm.HasType.applyArgs_iff _ _ _ _ _ _).mpr ⟨d.arguments, by simpa using Preterm.HasType.term hs, fit⟩

/-! ## Lists -/

theorem forall₂_get {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ {i : ℕ} {x : α} {y : β},
      l₁[i]? = some x → l₂[i]? = some y → R x y
  | [], [], _, i, x, y, h, _ => by simp at h
  | a :: as, b :: bs, .cons hab rest, i, x, y, hx, hy => by
      cases i with
      | zero => simp at hx hy; subst hx hy; exact hab
      | succ i => simp at hx hy; exact forall₂_get rest hx hy

theorem forall₂_right_mem {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ y ∈ l₂, ∃ x ∈ l₁, R x y
  | [], [], _, y, m => by simp at m
  | a :: as, b :: bs, .cons hab rest, y, m => by
      rcases List.mem_cons.mp m with rfl | m
      · exact ⟨a, List.mem_cons_self, hab⟩
      · obtain ⟨x, mx, r⟩ := forall₂_right_mem rest y m
        exact ⟨x, List.mem_cons_of_mem _ mx, r⟩

theorem substituteList_exists (σ : Substitution) :
    ∀ (l : List Preterm), (∀ h ∈ l, ∃ r, Preterm.substitute σ h = some r) →
      ∃ rs, Substitution.substituteList σ l = some rs
  | [], _ => ⟨[], rfl⟩
  | h :: l, all => by
      obtain ⟨r, hr⟩ := all h List.mem_cons_self
      obtain ⟨rs, hrs⟩ := substituteList_exists σ l fun h' m => all h' (List.mem_cons_of_mem _ m)
      exact ⟨r :: rs, by simp [Substitution.substituteList, hr, hrs]⟩

theorem mem_entries {Φ : Context} {es : List Preterm} {b : Binder} {e : Preterm} {p : ℕ}
    (m : ((b, e), p) ∈ Substitution.entries Φ es) : Φ[p]? = some b ∧ es[p]? = some e := by
  have := List.mem_zipIdx_iff_getElem?.mp m
  exact List.getElem?_zip_eq_some.mp this

theorem indep_mem {Φ : Context} {p q s : ℕ} {b' : Binder} (hp : Φ[p]? = some (.bound s))
    (hq : Φ[q]? = some b') (nd : ¬ b'.DependsOn q p) : Premise.absent (pv p) (pv q) ∈ indep Φ := by
  simp only [indep, List.mem_flatMap]
  refine ⟨(.bound s, p), List.mem_zipIdx_iff_getElem?.mpr hp, ?_⟩
  simp only [List.mem_filterMap]
  exact ⟨(b', q), List.mem_zipIdx_iff_getElem?.mpr hq, by simp [nd]⟩

theorem inst_pv_map (es : List Preterm) (k : ℕ) :
    (pv k).inst (substOf (es.map (enc Γ))) = es[k]?.map (enc Γ) := by
  simp [inst_pv, substOf, List.getElem?_map]

theorem sound_thm {fr : Frame} {t : ℕ} {d : TheoremDecl} (ht : E.thms t = some d) {a ps : List Tm}
    {cl : Tm} (hi : (thmRule d).instance fr a = some (ps, cl)) (good : ∀ j ∈ ps, Good E Γ H j) :
    Good E Γ H cl := by
  obtain ⟨len, hk, hc⟩ := (instance_iff fr _ a ps cl).mp hi
  have kindsEq : (thmRule d).kinds = (fits 0 d.arguments).map Premise.kind ++
      (d.hypotheses.map fun h => Premise.judg (pfP (patOf h))).map Premise.kind ++
      (indep d.arguments).map Premise.kind := by
    simp [thmRule, Rule.kinds, List.map_append]
  obtain ⟨fit, agree⟩ := read_fits (off := 0) hk
    (fun k m => by rw [kindsEq]; exact List.mem_append_left _ (List.mem_append_left _ m)) good
  set es := readArgs a 0 d.arguments.length with hesDef
  have hes : es.length = d.arguments.length := length_readArgs _ _ _
  have ha : a = es.map (enc Γ) := vals_eq (by rw [len, hes]; rfl)
    (fun k lt => by rw [hes] at lt; simpa using agree k lt)
  -- the hypotheses
  have hyp : ∀ h ∈ d.hypotheses, ∃ r, Preterm.substitute (Substitution.ofList es) h = some r ∧
      Derives E.sig E.defs E.thms Γ H r := by
    intro h mh
    have mk : Kind.consume (pfP (patOf h)) ∈ (thmRule d).kinds := by
      rw [kindsEq]
      refine List.mem_append_left _ (List.mem_append_right _ ?_)
      simp only [List.map_map, List.mem_map, Function.comp_def]
      exact ⟨h, mh, rfl⟩
    obtain ⟨j, mj, ij⟩ := instKinds_consume _ _ hk _ mk
    rw [ha] at ij
    simp only [pfP, inst_pjd, instAll, inst_patOf] at ij
    cases hsub : Preterm.substitute (Substitution.ofList es) h with
    | none => rw [hsub] at ij; simp at ij
    | some r =>
        rw [hsub] at ij
        simp only [Option.map_some, Option.some.injEq] at ij
        subst ij
        obtain ⟨e', eq, hd⟩ := good_pf (good _ mj)
        rw [← enc_inj eq] at hd
        exact ⟨r, rfl, hd⟩
  obtain ⟨hs, hhs⟩ := substituteList_exists _ d.hypotheses fun h m => by
    obtain ⟨r, hr, -⟩ := hyp h m; exact ⟨r, hr⟩
  have hsF := (Substitution.substituteList_eq_some_iff _ _ _).mp hhs
  have dl : DerivesList E.sig E.defs E.thms Γ H hs := by
    rw [derivesList_iff]
    intro r mr
    obtain ⟨h, mh, sub⟩ := forall₂_right_mem hsF r mr
    obtain ⟨r', hr', hd⟩ := hyp h mh
    rw [sub.eval] at hr'
    cases hr'
    exact hd
  -- the conclusion
  rw [ha] at hc
  simp only [thmRule, pfP, inst_pjd, instAll, inst_patOf] at hc
  cases hcs : Preterm.substitute (Substitution.ofList es) d.conclusion with
  | none => rw [hcs] at hc; simp at hc
  | some rc =>
      rw [hcs] at hc
      simp only [Option.map_some, Option.some.injEq] at hc
      subst hc
      -- independence
      have indepOk : ∀ entry ∈ Substitution.entries d.arguments es,
          Substitution.RowIndependent Γ (Substitution.entries d.arguments es) entry := by
        rintro ⟨⟨b, e⟩, p⟩ mentry sort image heq ⟨⟨b', e'⟩, q⟩ mother nd
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        obtain ⟨hp, hep⟩ := mem_entries mentry
        obtain ⟨hq, heq'⟩ := mem_entries mother
        have mk : (Premise.absent (pv p) (pv q)).kind ∈ (thmRule d).kinds := by
          rw [kindsEq]
          exact List.mem_append_right _ (List.mem_map_of_mem (indep_mem hp hq nd))
        obtain ⟨xv, bv, hx, hb, hok⟩ := (holds_absent fr _ _ _).mp (instKinds_holds fr _ hk _ mk)
        rw [ha, inst_pv_map, hep] at hx
        rw [ha, inst_pv_map, heq'] at hb
        simp only [Option.map_some, Option.some.injEq] at hx hb
        subst hx hb
        have fp := forall₂_get fit hep hp
        cases fp with
        | bound hbound => exact (absentOk_enc Γ hbound e').mp hok
      have inst : TheoremDecl.Instantiates E.sig Γ d es ⟨hs, rc⟩ :=
        ⟨⟨fit, indepOk⟩, hsF, Preterm.substitute_sound hcs⟩
      exact Or.inr (Or.inr (Or.inr ⟨rc, rfl, Derives.theoremApp ht inst dl⟩))

/-! ## Conversion rules -/

theorem cv_inst (σ : Subst ℕ Tm) (s x y : Pat) :
    (cvP s x y).inst σ = (instAll σ [s, x, y]).map (jd "cv") := inst_pjd σ "cv" [s, x, y]

theorem sound_cvRefl {fr : Frame} {s : ℕ} {a ps : List Tm} {cl : Tm}
    (hi : (cvReflRule s).instance fr a = some (ps, cl)) (good : ∀ j ∈ ps, Good E Γ H j) :
    Good E Γ H cl := by
  obtain ⟨len, hk, hc⟩ := (instance_iff fr _ a ps cl).mp hi
  obtain ⟨j, mj, ij⟩ := instKinds_consume _ _ hk (tyP (pnum s) (pv 0)) (by simp [cvReflRule, Rule.kinds, Premise.kind])
  simp only [tyP, inst_pjd, instAll, inst_pnum, inst_pv] at ij
  simp only [cvReflRule, cvP, inst_pjd, instAll, inst_pnum, inst_pv] at hc
  cases h0 : substOf a 0 with
  | none => rw [h0] at ij; simp at ij
  | some v =>
      rw [h0] at ij hc
      simp only [Option.map_some, Option.some.injEq] at ij hc
      subst ij hc
      obtain ⟨e, rfl, ht⟩ := good_ty (good _ mj)
      exact Or.inr (Or.inr (Or.inl ⟨s, e, e, rfl, .refl ht⟩))

theorem sound_cvSymm {fr : Frame} {a ps : List Tm} {cl : Tm}
    (hi : cvSymmRule.instance fr a = some (ps, cl)) (good : ∀ j ∈ ps, Good E Γ H j) :
    Good E Γ H cl := by
  obtain ⟨len, hk, hc⟩ := (instance_iff fr _ a ps cl).mp hi
  obtain ⟨j, mj, ij⟩ := instKinds_consume _ _ hk (cvP (pv 0) (pv 1) (pv 2)) (by simp [cvSymmRule, Rule.kinds, Premise.kind])
  simp only [cv_inst, instAll, inst_pv] at ij
  simp only [cvSymmRule, cv_inst, instAll, inst_pv] at hc
  cases h0 : substOf a 0 <;> cases h1 : substOf a 1 <;> cases h2 : substOf a 2 <;>
    simp only [h0, h1, h2, Option.map_some, Option.map_none, Option.some.injEq, reduceCtorEq] at ij hc
  subst ij hc
  obtain ⟨s, e, f, rfl, rfl, rfl, hcv⟩ := good_cv (good _ mj)
  exact Or.inr (Or.inr (Or.inl ⟨s, f, e, rfl, .symm hcv⟩))

theorem sound_cvTrans {fr : Frame} {a ps : List Tm} {cl : Tm}
    (hi : cvTransRule.instance fr a = some (ps, cl)) (good : ∀ j ∈ ps, Good E Γ H j) :
    Good E Γ H cl := by
  obtain ⟨len, hk, hc⟩ := (instance_iff fr _ a ps cl).mp hi
  obtain ⟨j, mj, ij⟩ := instKinds_consume _ _ hk (cvP (pv 0) (pv 1) (pv 2)) (by simp [cvTransRule, Rule.kinds, Premise.kind])
  obtain ⟨j', mj', ij'⟩ := instKinds_consume _ _ hk (cvP (pv 0) (pv 2) (pv 3)) (by simp [cvTransRule, Rule.kinds, Premise.kind])
  simp only [cv_inst, instAll, inst_pv] at ij ij'
  simp only [cvTransRule, cv_inst, instAll, inst_pv] at hc
  cases h0 : substOf a 0 <;> cases h1 : substOf a 1 <;> cases h2 : substOf a 2 <;> cases h3 : substOf a 3 <;>
    simp only [h0, h1, h2, h3, Option.map_some, Option.map_none, Option.some.injEq, reduceCtorEq] at ij ij' hc
  subst ij ij' hc
  obtain ⟨s, e, f, hs, rfl, hf, hcv⟩ := good_cv (good _ mj)
  obtain ⟨s', f', g, hs', hf', rfl, hcv'⟩ := good_cv (good _ mj')
  rw [hs] at hs'
  cases num_inj hs'
  rw [hf] at hf'
  cases enc_inj hf'
  subst hs hf
  exact Or.inr (Or.inr (Or.inl ⟨s, e, g, rfl, .trans hcv hcv'⟩))

theorem sound_conv {fr : Frame} {a ps : List Tm} {cl : Tm}
    (hi : convRule.instance fr a = some (ps, cl)) (good : ∀ j ∈ ps, Good E Γ H j) :
    Good E Γ H cl := by
  obtain ⟨len, hk, hc⟩ := (instance_iff fr _ a ps cl).mp hi
  obtain ⟨j, mj, ij⟩ := instKinds_consume _ _ hk (cvP (pv 0) (pv 1) (pv 2)) (by simp [convRule, Rule.kinds, Premise.kind])
  obtain ⟨j', mj', ij'⟩ := instKinds_consume _ _ hk (pfP (pv 1)) (by simp [convRule, Rule.kinds, Premise.kind])
  simp only [cv_inst, pfP, inst_pjd, instAll, inst_pv] at ij ij'
  simp only [convRule, pfP, inst_pjd, instAll, inst_pv] at hc
  cases h0 : substOf a 0 <;> cases h1 : substOf a 1 <;> cases h2 : substOf a 2 <;>
    simp only [h0, h1, h2, Option.map_some, Option.map_none, Option.some.injEq, reduceCtorEq] at ij ij' hc
  subst ij ij' hc
  obtain ⟨s, e, f, -, he, rfl, hcv⟩ := good_cv (good _ mj)
  obtain ⟨e', he', hd⟩ := good_pf (good _ mj')
  rw [he] at he'
  cases enc_inj he'
  exact Or.inr (Or.inr (Or.inr ⟨f, rfl, .conversion hcv hd⟩))

/-! ## Congruence -/

theorem convertsArgs_of_get :
    ∀ {Φ : Context} {ls rs : List Preterm}, ls.length = Φ.length → rs.length = Φ.length →
      (∀ (k : ℕ) (b : Binder) (l r : Preterm), Φ[k]? = some b → ls[k]? = some l → rs[k]? = some r →
        Preterm.FitsBinder E.sig Γ l b ∧ Preterm.FitsBinder E.sig Γ r b ∧ Converts E.sig E.defs Γ l r b.sort) →
      ConvertsArgs E.sig E.defs Γ ls rs Φ
  | [], [], [], _, _, _ => .nil
  | b :: Φ, l :: ls, r :: rs, hl, hr, each => by
      obtain ⟨fl, fr, cv⟩ := each 0 b l r rfl rfl rfl
      exact .cons fl fr cv (convertsArgs_of_get (by simpa using hl) (by simpa using hr)
        fun k b' l' r' hb hl' hr' => each (k + 1) b' l' r' (by simpa using hb) (by simpa using hl')
          (by simpa using hr'))
  | [], _ :: _, _, hl, _, _ => by simp at hl
  | [], [], _ :: _, _, hr, _ => by simp at hr
  | _ :: _, [], _, hl, _, _ => by simp at hl
  | _ :: _, _ :: _, [], _, hr, _ => by simp at hr

theorem vals_append {a : List Tm} {ls rs : List Preterm} {n : ℕ} (hl : ls.length = n) (hr : rs.length = n)
    (len : a.length = n + n) (agreeL : ∀ k < n, a[0 + k]? = ls[k]?.map (enc Γ))
    (agreeR : ∀ k < n, a[n + k]? = rs[k]?.map (enc Γ)) : a = (ls ++ rs).map (enc Γ) := by
  apply vals_eq (by simp [len, hl, hr])
  intro k lt
  simp only [List.length_append, hl, hr] at lt
  by_cases small : k < n
  · rw [List.getElem?_append_left (by omega)]
    simpa using agreeL k small
  · have := agreeR (k - n) (by omega)
    rw [show n + (k - n) = k by omega] at this
    rw [this, List.getElem?_append_right (by omega), hl]

theorem sound_cong {fr : Frame} {c : ℕ} {d : TermDecl} (hs : E.sig c = some d) {a ps : List Tm}
    {cl : Tm} (hi : (cvCongRule c d).instance fr a = some (ps, cl)) (good : ∀ j ∈ ps, Good E Γ H j) :
    Good E Γ H cl := by
  obtain ⟨len, hk, hc⟩ := (instance_iff fr _ a ps cl).mp hi
  set n := d.arguments.length with hn
  have kindsEq : (cvCongRule c d).kinds = (fits 0 d.arguments).map Premise.kind ++
      (fits n d.arguments).map Premise.kind ++
      (d.arguments.zipIdx.map fun x => Premise.judg (cvP (pnum x.1.sort) (pv x.2) (pv (n + x.2)))).map
        Premise.kind := by
    simp [cvCongRule, Rule.kinds, List.map_append, hn]
  obtain ⟨fitL, agreeL⟩ := read_fits (off := 0) hk
    (fun k m => by rw [kindsEq]; exact List.mem_append_left _ (List.mem_append_left _ m)) good
  obtain ⟨fitR, agreeR⟩ := read_fits (off := n) hk
    (fun k m => by rw [kindsEq]; exact List.mem_append_left _ (List.mem_append_right _ m)) good
  set ls := readArgs a 0 n with hls
  set rs := readArgs a n n with hrs
  have hl : ls.length = n := length_readArgs _ _ _
  have hr : rs.length = n := length_readArgs _ _ _
  have ha : a = (ls ++ rs).map (enc Γ) := vals_append hl hr (by rw [len]; rfl) agreeL agreeR
  have conv : ∀ (k : ℕ) (b : Binder) (l r : Preterm), d.arguments[k]? = some b → ls[k]? = some l → rs[k]? = some r →
      Converts E.sig E.defs Γ l r b.sort := by
    intro k b l r hb hl' hr'
    have mk : Kind.consume (cvP (pnum b.sort) (pv k) (pv (n + k))) ∈ (cvCongRule c d).kinds := by
      rw [kindsEq]
      refine List.mem_append_right _ ?_
      simp only [List.map_map, List.mem_map, Function.comp_def]
      exact ⟨(b, k), List.mem_zipIdx_iff_getElem?.mpr hb, rfl⟩
    obtain ⟨j, mj, ij⟩ := instKinds_consume _ _ hk _ mk
    have kl : k < n := by rw [← hl]; exact (List.getElem?_eq_some_iff.mp hl').1
    have g1 : (ls ++ rs)[k]? = some l := by rw [List.getElem?_append_left (by omega)]; exact hl'
    have g2 : (ls ++ rs)[n + k]? = some r := by
      rw [List.getElem?_append_right (by omega), hl, show n + k - n = k by omega]; exact hr'
    rw [ha] at ij
    simp only [cv_inst, instAll, inst_pnum, inst_pv_map, g1, g2, Option.map_some,
      Option.some.injEq] at ij
    subst ij
    obtain ⟨s, e, f, hsx, he, hf, hcv⟩ := good_cv (good _ mj)
    cases num_inj hsx
    cases enc_inj he
    cases enc_inj hf
    exact hcv
  have args : ConvertsArgs E.sig E.defs Γ ls rs d.arguments :=
    convertsArgs_of_get hl hr fun k b l r hb hl' hr' =>
      ⟨forall₂_get fitL hl' hb, forall₂_get fitR hr' hb, conv k b l r hb hl' hr'⟩
  rw [ha] at hc
  have sl := inst_spine (Γ := Γ) c (ls ++ rs) 0 n (by simp [hl, hr])
  have sr := inst_spine (Γ := Γ) c (ls ++ rs) n n (by simp [hl, hr])
  rw [show ((ls ++ rs).drop 0).take n = ls by simp [← hl]] at sl
  rw [show ((ls ++ rs).drop n).take n = rs by
    rw [List.drop_left' hl, List.take_of_length_le (le_of_eq hr)]] at sr
  simp only [cvCongRule, ← hn, cv_inst, instAll, inst_pnum, sl, sr, Option.map_some,
    Option.some.injEq] at hc
  subst hc
  exact Or.inr (Or.inr (Or.inl ⟨d.resultSort, _, _, rfl, .congruence hs args⟩))

/-! ## Unfolding -/

theorem fresh_mem {n m j k : ℕ} (hj : j < m) (hk : k < n + j) :
    Premise.absent (pv (n + j)) (pv k) ∈ fresh n m := by
  simp only [fresh, List.mem_flatMap, List.mem_range, List.mem_map]
  exact ⟨j, hj, k, hk, rfl⟩

theorem dummy_mem {n : ℕ} {ds : List ℕ} {j s : ℕ} (h : ds[j]? = some s) :
    Kind.consume (bvP s (pv (n + j))) ∈ (dummyFits n ds).map Premise.kind := by
  simp only [dummyFits, List.map_map, List.mem_map, Function.comp_def]
  exact ⟨(s, n + j), List.mem_zipIdx_iff_le_and_getElem?_sub.mpr ⟨by omega, by simpa using h⟩, rfl⟩

/-- **Fresh dummies**, from their pointwise conditions. -/
theorem freshDummies_of :
    ∀ {args : List Preterm} {ds images : List ℕ}, images.length = ds.length →
      (∀ (j s i : ℕ), ds[j]? = some s → images[j]? = some i → Γ[i]? = some (.bound s)) →
      (∀ e ∈ args, ∃ support, Preterm.Supports Γ e support) →
      (∀ (j i : ℕ) (e : Preterm), images[j]? = some i → e ∈ args ++ (images.take j).map Preterm.var →
        ¬ Preterm.HasVar Γ i e) →
      Definition.FreshDummies Γ args ds images
  | args, [], [], _, _, _, _ => .nil args
  | args, s :: ds, i :: images, hlen, bound, sup, fr => by
      have hb : Γ[i]? = some (.bound s) := bound 0 s i rfl rfl
      refine .cons hb (fun e me => ⟨sup e me, fr 0 i e rfl (by simpa using me)⟩) ?_
      refine freshDummies_of (by simpa using hlen) (fun j s' i' h1 h2 => bound (j + 1) s' i' (by simpa using h1)
        (by simpa using h2)) (fun e me => ?_) (fun j i' e h me => fr (j + 1) i' e (by simpa using h) ?_)
      · rcases List.mem_append.mp me with me | me
        · exact sup e me
        · simp only [List.mem_singleton] at me; subst me; exact ⟨_, .bound hb⟩
      · simp only [List.take_succ_cons, List.map_cons, List.mem_append, List.mem_cons] at me ⊢
        tauto
  | _, [], _ :: _, hlen, _, _, _ => by simp at hlen
  | _, _ :: _, [], hlen, _, _, _ => by simp at hlen

/-- The images of the dummies read back. -/
def readImages (a : List Tm) (n m : ℕ) : List ℕ :=
  (List.range m).map fun j => match a[n + j]? with
    | some (.node (.fv i) .nil) => i
    | _ => 0

theorem sound_unfold {fr : Frame} {c : ℕ} {d : TermDecl} {b : Definition.Body} (hs : E.sig c = some d)
    (hd : E.defs c = some b) {a ps : List Tm} {cl : Tm}
    (hi : (unfoldRule c d b).instance fr a = some (ps, cl)) (good : ∀ j ∈ ps, Good E Γ H j) :
    Good E Γ H cl := by
  obtain ⟨len, hk, hc⟩ := (instance_iff fr _ a ps cl).mp hi
  set n := d.arguments.length with hn
  set m := b.dummies.length with hm
  have kindsEq : (unfoldRule c d b).kinds = (fits 0 d.arguments).map Premise.kind ++
      (dummyFits n b.dummies).map Premise.kind ++ [Kind.consume (tyP (pnum d.resultSort) (patOf b.expression))] ++
      (fresh n m).map Premise.kind := by
    simp [unfoldRule, Rule.kinds, List.map_append, hn, hm, Premise.kind]
  obtain ⟨fit, agree⟩ := read_fits (off := 0) hk
    (fun k mk => by rw [kindsEq]; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ mk)))
    good
  set args := readArgs a 0 n with hargs
  have hal : args.length = n := length_readArgs _ _ _
  -- the dummies are bound variables of their sorts
  have dum : ∀ (j s : ℕ), b.dummies[j]? = some s → ∃ i, a[n + j]? = some (fvar i) ∧ Γ[i]? = some (.bound s) := by
    intro j s hj
    obtain ⟨jj, mj, ij⟩ := instKinds_consume _ _ hk _ (by
      rw [kindsEq]; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (dummy_mem hj))))
    simp only [bvP, inst_pjd, instAll, inst_pnum, inst_pv, substOf] at ij
    cases ha : a[n + j]? with
    | none => rw [ha] at ij; simp at ij
    | some v =>
        rw [ha] at ij
        simp only [Option.map_some, Option.some.injEq] at ij
        subst ij
        obtain ⟨i, rfl, hb⟩ := good_bv (good _ mj)
        exact ⟨i, rfl, hb⟩
  set images := readImages a n m with himages
  have himl : images.length = m := by simp [himages, readImages]
  have img : ∀ (j : ℕ), j < m → ∃ s i, b.dummies[j]? = some s ∧ images[j]? = some i ∧
      a[n + j]? = some (fvar i) ∧ Γ[i]? = some (.bound s) := by
    intro j lt
    obtain ⟨s, hs'⟩ : ∃ s, b.dummies[j]? = some s := ⟨_, List.getElem?_eq_getElem lt⟩
    obtain ⟨i, ha, hb⟩ := dum j s hs'
    refine ⟨s, i, hs', ?_, ha, hb⟩
    simp [himages, readImages, List.getElem?_range lt, ha, fvar, flds]
  set vals := args ++ images.map Preterm.var with hvals
  have ha : a = vals.map (enc Γ) := by
    apply vals_eq (by simp [hvals, len, unfoldRule, hal, himl, hn, hm])
    intro k lt
    simp only [hvals, List.length_append, List.length_map, hal, himl] at lt
    by_cases small : k < n
    · rw [List.getElem?_append_left (by omega)]
      simpa using agree k small
    · obtain ⟨s, i, -, hi', ha', hb⟩ := img (k - n) (by omega)
      rw [show n + (k - n) = k by omega] at ha'
      rw [ha', List.getElem?_append_right (by omega), hal, List.getElem?_map, hi']
      simp [enc, encVar, hb]
  -- the unfolded body has the result sort
  obtain ⟨jt, mjt, ijt⟩ := instKinds_consume _ _ hk (tyP (pnum d.resultSort) (patOf b.expression))
    (by rw [kindsEq]; simp)
  rw [ha] at ijt
  simp only [tyP, inst_pjd, instAll, inst_pnum, inst_patOf] at ijt
  cases hres : Preterm.substitute (Substitution.ofList vals) b.expression with
  | none => rw [hres] at ijt; simp at ijt
  | some result =>
      rw [hres] at ijt
      simp only [Option.map_some, Option.some.injEq] at ijt
      subst ijt
      obtain ⟨e, he, ht⟩ := good_ty (good _ mjt)
      have he' := enc_inj he
      subst he'
      -- the dummies are fresh
      have freshD : Definition.FreshDummies Γ args b.dummies images := by
        refine freshDummies_of (by rw [himl]) (fun j s i h1 h2 => ?_) (fun e me => ?_) (fun j i e h me => ?_)
        · have lt : j < m := by rw [hm]; exact (List.getElem?_eq_some_iff.mp h1).1
          obtain ⟨s', i', h1', h2', -, hb⟩ := img j lt
          rw [h1'] at h1; rw [h2'] at h2
          cases h1; cases h2; exact hb
        · obtain ⟨k, hk'⟩ := List.mem_iff_getElem?.mp me
          have klt : k < n := by rw [← hal]; exact (List.getElem?_eq_some_iff.mp hk').1
          have fk := forall₂_get fit hk' (List.getElem?_eq_getElem (by rw [← hn]; exact klt))
          exact fk.support_exists
        · have jlt : j < m := by rw [← himl]; exact (List.getElem?_eq_some_iff.mp h).1
          obtain ⟨s, i', -, hi', ha', hb⟩ := img j jlt
          rw [hi'] at h; cases h
          have mv : e ∈ vals.take (n + j) := by
            rw [hvals, List.take_append, List.take_of_length_le (by omega), hal,
              show n + j - n = j by omega]
            simpa [List.map_take] using me
          obtain ⟨k, hk'⟩ := List.mem_iff_getElem?.mp mv
          have klt : k < n + j := by
            have := (List.getElem?_eq_some_iff.mp hk').1
            simp at this; omega
          rw [List.getElem?_take_of_lt klt] at hk'
          have mk := List.mem_append_right ((fits 0 d.arguments).map Premise.kind ++
            (dummyFits n b.dummies).map Premise.kind ++ [Kind.consume (tyP (pnum d.resultSort) (patOf b.expression))])
            (List.mem_map_of_mem (f := Premise.kind) (fresh_mem jlt klt))
          rw [← kindsEq] at mk
          obtain ⟨xv, bv, hx, hbv, hok⟩ := (holds_absent fr _ _ _).mp (instKinds_holds fr _ hk _ mk)
          rw [inst_pv, substOf, ha'] at hx
          rw [inst_pv, substOf, ha, List.getElem?_map, hk'] at hbv
          simp only [Option.some.injEq, Option.map_some] at hx hbv
          subst hx hbv
          rw [show fvar i = enc Γ (.var i) by simp [enc, encVar, hb]] at hok
          exact (absentOk_enc Γ hb e).mp hok
      have unf : Definition.Unfolds E.sig E.defs Γ c args images result :=
        .intro hs hd fit freshD (Preterm.substitute_sound hres)
      rw [ha] at hc
      have sp := inst_spine (Γ := Γ) c vals 0 n (by simp [hvals, hal])
      rw [show (vals.drop 0).take n = args by
        rw [List.drop_zero, hvals, List.take_append, List.take_of_length_le (le_of_eq hal), hal,
          Nat.sub_self, List.take_zero, List.append_nil]] at sp
      simp only [unfoldRule, ← hn, cv_inst, instAll, inst_pnum, sp, inst_patOf, hres, Option.map_some,
        Option.some.injEq] at hc
      subst hc
      exact Or.inr (Or.inr (Or.inl ⟨d.resultSort, _, result, rfl, .unfold hs unf ht⟩))

/-! ## Soundness -/

/-- **Soundness of the presentation**: every judgment derivable from the context's hypotheses and
the claim's hypotheses means what it says in Mettapedia's MM0 kernel. -/
theorem derivable_good (fr : Frame) {j : (presOf (rules E) fr).J}
    (h : Derivable (presOf (rules E) fr) (hypsOf Γ H) j) :
    Good E Γ H j := by
  induction h with
  | hyp m => exact good_hyps m
  | @rule r a ps c hi _ ih =>
      have good : ∀ p ∈ ps, Good E Γ H p := fun p m => ih p m rfl
      cases r with
      | con k =>
          simp only [presOf, rules] at hi
          cases hs : E.sig k with
          | none => rw [hs] at hi; cases hi
          | some d => rw [hs] at hi; exact sound_con hs hi good
      | thm t =>
          simp only [presOf, rules] at hi
          cases ht : E.thms t with
          | none => rw [ht] at hi; cases hi
          | some d => rw [ht] at hi; exact sound_thm ht hi good
      | cvRefl s => exact sound_cvRefl hi good
      | cvSymm => exact sound_cvSymm hi good
      | cvTrans => exact sound_cvTrans hi good
      | cvCong k =>
          simp only [presOf, rules] at hi
          cases hs : E.sig k with
          | none => rw [hs] at hi; cases hi
          | some d => rw [hs] at hi; exact sound_cong hs hi good
      | unfold k =>
          simp only [presOf, rules] at hi
          cases hs : E.sig k with
          | none => rw [hs] at hi; cases hi
          | some d =>
              cases hd : E.defs k with
              | none => rw [hs, hd] at hi; cases hi
              | some b => rw [hs, hd] at hi; exact sound_unfold hs hd hi good
      | conv => exact sound_conv hi good

/-- **What the presentation proves, MM0 derives.** -/
theorem derivable_pf_derives (fr : Frame) {e : Preterm}
    (h : Derivable (presOf (rules E) fr) (hypsOf Γ H) (pfJ (enc Γ e))) :
    Derives E.sig E.defs E.thms Γ H e := by
  obtain ⟨e', he, hd⟩ := good_pf (derivable_good fr h)
  rw [← enc_inj he] at hd
  exact hd

end Mettapedia.Logic.TierZero.Adequacy.MM0
