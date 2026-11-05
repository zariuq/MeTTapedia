import Mettapedia.Machines.TierDeoptimization
import Mettapedia.Machines.AdmissionRewriting.Semantics

/-!
# Local declines and type monotonicity

A compiled tier that refuses a whole call graph when one site, or one declaration, is
outside what it compiles makes cost depend on code that never runs.  Measured on the
committed opt binary (PeTTa lane, `loop` 10,000 with a lambda, answer 10000 throughout):
31.0M instructions plain; 329.6M with an unrelated, never-called `(: quoteit (-> Atom
Atom))`; 341.4M with `(: + (-> Number Number Number))`; and a never-taken `(#+ $x 1)` or a
two-armed `if` in a callee drops the whole graph 44-59x.

**The model.**  A run is the stream of steps it executes (`TierDeoptimization`).  Each
step belongs to a call site with a callee head; declarations give some heads a type.
`SiteAdmission` decides each site from its own code and its callee's declaration only,
and charges the declaration's checks there.  `tierOf` turns any admission map into a
tiered machine in which declined sites run as host goals on the general engine.

This file proves:
* `local_observes`, `local_observes_decline`: whatever the admission map, the tiered run
  observes exactly the general run, hence exactly what declining every site observes;
* `localCost_le_wholeCost`, `localCost_lt_wholeCost`: per-site admission never costs more
  than refusing the whole graph, and costs strictly less as soon as the graph is refused
  for a site or a declaration the run never reaches (the never-taken `#+`, the uncalled
  `quoteit`) while one executed step is cheaper fast;
* `type_monotone`: adding a declaration, under local admission that only adds checks to
  the declared head's sites, costs at most the old cost plus those checks;
* `type_neutral_unexecuted`: a declaration of a head the run never executes costs
  nothing at all;
* `contagious_not_monotone`: under whole-graph admission, a declaration the tier refuses
  globally raises the cost of a run that never calls its head;
* `eval_fn_irrelevant`: in the admission fragment, a declaration of a head the program
  never mentions does not change its trace: such a declaration is answer-neutral;
* `eval_guard_neutral`: a guard declaration that agrees with the old function on integer
  arguments does not change the trace of a program whose calls of that head all take
  integer atoms: redeclaring `+` over numbers is answer-neutral on numeric programs.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.AdmissionRewriting.LocalDeclines

open TierDeoptimization

variable {ι σf σg H Decl : Type}

/-- A fast engine correct on every step it may be asked to run, and the general engine. -/
structure Engines (ι σf σg : Type) where
  gen : ι → σg → σg
  fast : ι → σf → σf
  enc : σf → σg
  dec : σg → Option σf
  sim : ∀ i s, enc (fast i s) = gen i (enc s)
  dec_enc : ∀ g s, dec g = some s → enc s = g

/-- The tiered machine admitting the steps `adm` accepts; the others are host goals. -/
def tierOf (E : Engines ι σf σg) (adm : ι → Bool) : Tiered ι σf σg where
  gen := E.gen
  fast i := if adm i then some (E.fast i) else none
  enc := E.enc
  dec := E.dec
  sim i f h s := by
    by_cases ha : adm i
    · simp only [ha, if_true, Option.some.injEq] at h; subst h; exact E.sim i s
    · simp [ha] at h
  dec_enc := E.dec_enc

theorem supported_tierOf (E : Engines ι σf σg) (adm : ι → Bool) (i : ι) :
    supported (tierOf E adm) i = adm i := by
  by_cases ha : adm i <;> simp [supported, tierOf, ha]

/-- Declining sites locally is invisible: the run observes the general engine. -/
theorem local_observes (E : Engines ι σf σg) (adm : ι → Bool) (is : List ι) (s : σf) :
    runTiered (tierOf E adm) is s = runGen (tierOf E adm) is (E.enc s) :=
  runTiered_eq _ is s

/-- The general run does not depend on what the tier admits. -/
theorem runGen_tierOf (E : Engines ι σf σg) (adm adm' : ι → Bool) :
    ∀ (is : List ι) (g : σg), runGen (tierOf E adm) is g = runGen (tierOf E adm') is g
  | [], _ => rfl
  | i :: is, g => by
    simp only [runGen]
    exact runGen_tierOf E adm adm' is _

/-- Per-site admission observes exactly what declining every site observes. -/
theorem local_observes_decline (E : Engines ι σf σg) (adm : ι → Bool) (is : List ι) (s : σf) :
    runTiered (tierOf E adm) is s = runTiered (tierOf E fun _ => false) is s := by
  rw [local_observes, local_observes, runGen_tierOf E adm (fun _ => false)]

/-- Per-site admission: a site is decided by its own code and its callee's declaration. -/
structure SiteAdmission (ι H Decl : Type) where
  /-- The callee head of a site. -/
  head : ι → H
  /-- Whether the tier compiles a site, given its callee's declaration. -/
  admit : Option Decl → ι → Bool
  /-- The cost of a declaration's own checks at a compiled site. -/
  check : Option Decl → ι → ℕ

/-- Declarations: each head's declared type, if any. -/
abbrev Decls (H Decl : Type) := H → Option Decl

variable (A : SiteAdmission ι H Decl)

/-- The admission map of a declaration environment. -/
def SiteAdmission.adm (Γd : Decls H Decl) (i : ι) : Bool := A.admit (Γd (A.head i)) i

/-- The fast cost of a site with its declaration's checks. -/
def SiteAdmission.cost (cf : ι → ℕ) (Γd : Decls H Decl) (i : ι) : ℕ :=
  cf i + A.check (Γd (A.head i)) i

/-- The cost of a run under per-site admission. -/
def localCost (E : Engines ι σf σg) (cf cg : ι → ℕ) (Γd : Decls H Decl) (is : List ι) : ℕ :=
  costTiered (tierOf E (A.adm Γd)) (A.cost cf Γd) cg is

/-- Whole-graph admission: every static site of the graph, and the declarations as a
whole (`declOK`), must be accepted, or every step runs generally. -/
def wholeCost (declOK : Decls H Decl → Bool) (sites : List ι) (cf cg : ι → ℕ)
    (Γd : Decls H Decl) (is : List ι) : ℕ :=
  if declOK Γd && sites.all (A.adm Γd) then (is.map (A.cost cf Γd)).sum else (is.map cg).sum

theorem localCost_eq (E : Engines ι σf σg) (cf cg : ι → ℕ) (Γd : Decls H Decl) (is : List ι) :
    localCost A E cf cg Γd is =
      (is.map fun i => if A.adm Γd i then A.cost cf Γd i else cg i).sum := by
  simp only [localCost, costTiered, supported_tierOf]

theorem localCost_le_general (E : Engines ι σf σg) (cf cg : ι → ℕ) (Γd : Decls H Decl)
    (hle : ∀ i, A.adm Γd i = true → A.cost cf Γd i ≤ cg i) (is : List ι) :
    localCost A E cf cg Γd is ≤ (is.map cg).sum := by
  rw [localCost_eq]
  induction is with
  | nil => simp
  | cons i is ih =>
    simp only [List.map_cons, List.sum_cons]
    have : (if A.adm Γd i then A.cost cf Γd i else cg i) ≤ cg i := by
      by_cases ha : A.adm Γd i
      · simp only [ha, if_true]; exact hle i ha
      · simp [ha]
    omega

/-- Per-site admission never costs more than refusing the whole graph, provided every
executed step is a site of the graph. -/
theorem localCost_le_wholeCost (E : Engines ι σf σg) (declOK : Decls H Decl → Bool)
    (sites : List ι) (cf cg : ι → ℕ) (Γd : Decls H Decl)
    (hle : ∀ i, A.adm Γd i = true → A.cost cf Γd i ≤ cg i) (is : List ι)
    (hsub : ∀ i ∈ is, i ∈ sites) :
    localCost A E cf cg Γd is ≤ wholeCost A declOK sites cf cg Γd is := by
  unfold wholeCost
  split
  · next h =>
    simp only [Bool.and_eq_true, List.all_eq_true] at h
    rw [localCost_eq]
    apply le_of_eq
    congr 1
    apply List.map_congr_left
    intro i hi
    simp [h.2 i (hsub i hi)]
  · exact localCost_le_general A E cf cg Γd hle is

/-- When the whole graph is refused although every executed step is admitted, and one
executed step is strictly cheaper fast, per-site admission is strictly cheaper. -/
theorem localCost_lt_wholeCost (E : Engines ι σf σg) (declOK : Decls H Decl → Bool)
    (sites : List ι) (cf cg : ι → ℕ) (Γd : Decls H Decl)
    (hle : ∀ i, A.adm Γd i = true → A.cost cf Γd i ≤ cg i) (is : List ι)
    (hrefused : (declOK Γd && sites.all (A.adm Γd)) = false)
    (hrun : ∀ i ∈ is, A.adm Γd i = true)
    (hcheap : ∃ j ∈ is, A.cost cf Γd j < cg j) :
    localCost A E cf cg Γd is < wholeCost A declOK sites cf cg Γd is := by
  simp only [wholeCost, hrefused, Bool.false_eq_true, if_false]
  rw [localCost_eq]
  obtain ⟨j, hj, hlt⟩ := hcheap
  induction is with
  | nil => simp at hj
  | cons i is ih =>
    simp only [List.map_cons, List.sum_cons]
    have hi : (if A.adm Γd i then A.cost cf Γd i else cg i) = A.cost cf Γd i := by
      simp [hrun i (by simp)]
    have hrest : (is.map fun i => if A.adm Γd i then A.cost cf Γd i else cg i).sum ≤
        (is.map cg).sum := by
      have := localCost_le_general A E cf cg Γd hle is
      rwa [localCost_eq] at this
    rcases List.mem_cons.mp hj with rfl | hj'
    · rw [hi]; omega
    · have := ih (fun i hi => hrun i (by simp [hi])) hj'
      have hle_i : A.cost cf Γd i ≤ cg i := hle i (hrun i (by simp))
      rw [hi]; omega

/-- A new declaration removes no fast path: every site admitted before stays admitted. -/
theorem fast_path_kept [DecidableEq H] (Γd : Decls H Decl) (f : H) (d : Decl)
    (hnone : Γd f = none)
    (hext : ∀ i, A.head i = f → A.admit none i = true → A.admit (some d) i = true)
    (i : ι) (h : A.adm Γd i = true) : A.adm (Function.update Γd f (some d)) i = true := by
  by_cases hf : A.head i = f
  · have h0 : A.admit none i = true := by
      simpa [SiteAdmission.adm, hf, hnone] using h
    simpa [SiteAdmission.adm, hf] using hext i hf h0
  · have hΓ : Function.update Γd f (some d) (A.head i) = Γd (A.head i) := by simp [hf]
    unfold SiteAdmission.adm; rw [hΓ]; exact h

/-- Type monotonicity: a new declaration of `f`, under per-site admission that keeps
every admitted `f` site admitted, costs at most the old cost plus its checks at the
executed `f` sites. -/
theorem type_monotone [DecidableEq H] (E : Engines ι σf σg) (cf cg : ι → ℕ)
    (hfg : ∀ i, cf i ≤ cg i) (Γd : Decls H Decl) (f : H) (d : Decl) (hnone : Γd f = none)
    (hcheck : ∀ i, A.check none i = 0)
    (hext : ∀ i, A.head i = f → A.admit none i = true → A.admit (some d) i = true)
    (is : List ι) :
    localCost A E cf cg (Function.update Γd f (some d)) is ≤
      localCost A E cf cg Γd is + ((is.filter (fun i => A.head i = f)).map (A.check (some d))).sum := by
  rw [localCost_eq, localCost_eq]
  induction is with
  | nil => simp
  | cons i is ih =>
    simp only [List.map_cons, List.sum_cons, List.filter_cons]
    by_cases hf : A.head i = f
    · have hΓ : Function.update Γd f (some d) (A.head i) = some d := by simp [hf]
      have hΓ0 : Γd (A.head i) = none := by rw [hf]; exact hnone
      simp only [hf, decide_true, if_true, List.map_cons, List.sum_cons]
      simp only [SiteAdmission.adm, SiteAdmission.cost, hΓ, hΓ0, hcheck] at ih ⊢
      by_cases ha : A.admit none i = true
      · simp only [hext i hf ha, ha, if_true]; omega
      · simp only [Bool.not_eq_true] at ha
        simp only [ha, Bool.false_eq_true, if_false]
        by_cases hb : A.admit (some d) i = true
        · simp only [hb, if_true]; have := hfg i; omega
        · simp only [Bool.not_eq_true] at hb; simp only [hb, Bool.false_eq_true, if_false]; omega
    · have hΓ : Function.update Γd f (some d) (A.head i) = Γd (A.head i) := by simp [hf]
      have hhead : (if A.adm (Function.update Γd f (some d)) i then
            A.cost cf (Function.update Γd f (some d)) i else cg i) =
          (if A.adm Γd i then A.cost cf Γd i else cg i) := by
        unfold SiteAdmission.adm SiteAdmission.cost; rw [hΓ]
      simp only [hf, decide_false, Bool.false_eq_true, if_false]
      rw [hhead]
      omega

/-- A declaration of a head the run never executes costs nothing. -/
theorem type_neutral_unexecuted [DecidableEq H] (E : Engines ι σf σg) (cf cg : ι → ℕ)
    (Γd : Decls H Decl) (f : H) (od : Option Decl) (is : List ι)
    (hnot : ∀ i ∈ is, A.head i ≠ f) :
    localCost A E cf cg (Function.update Γd f od) is = localCost A E cf cg Γd is := by
  rw [localCost_eq, localCost_eq]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hΓ : Function.update Γd f od (A.head i) = Γd (A.head i) := by simp [hnot i hi]
  unfold SiteAdmission.adm SiteAdmission.cost; rw [hΓ]

/-- Under whole-graph admission, a declaration the tier refuses as a whole raises the
cost of a run that never calls its head: whole-graph admission is not monotone. -/
theorem contagious_not_monotone [DecidableEq H] (declOK : Decls H Decl → Bool) (sites : List ι)
    (cf cg : ι → ℕ) (Γd : Decls H Decl) (f : H) (d : Decl) (is : List ι)
    (hbefore : (declOK Γd && sites.all (A.adm Γd)) = true)
    (hafter : declOK (Function.update Γd f (some d)) = false)
    (hnot : ∀ i ∈ is, A.head i ≠ f)
    (hle : ∀ i ∈ is, A.cost cf Γd i ≤ cg i)
    (hcheap : ∃ j ∈ is, A.cost cf Γd j < cg j) :
    wholeCost A declOK sites cf cg Γd is +
        ((is.filter (fun i => A.head i = f)).map (A.check (some d))).sum <
      wholeCost A declOK sites cf cg (Function.update Γd f (some d)) is := by
  have hfilter : is.filter (fun i => A.head i = f) = [] := by
    simp only [List.filter_eq_nil_iff, decide_eq_true_eq]
    exact fun i hi => hnot i hi
  simp only [wholeCost, hbefore, if_true, hafter, Bool.false_and, Bool.false_eq_true, if_false,
    hfilter, List.map_nil, List.sum_nil, add_zero]
  obtain ⟨j, hj, hlt⟩ := hcheap
  induction is with
  | nil => simp at hj
  | cons i is ih =>
    simp only [List.map_cons, List.sum_cons]
    have hrest : (is.map (A.cost cf Γd)).sum ≤ (is.map cg).sum := by
      apply List.sum_le_sum
      intro k hk
      exact hle k (by simp [hk])
    have hle_i := hle i (by simp)
    rcases List.mem_cons.mp hj with rfl | hj'
    · omega
    · have hf' : is.filter (fun i => A.head i = f) = [] := by
        simp only [List.filter_eq_nil_iff, decide_eq_true_eq]
        exact fun k hk => hnot k (by simp [hk])
      have := ih (fun k hk => hnot k (by simp [hk])) (fun k hk => hle k (by simp [hk])) hf' hj'
      omega

/-! ## Answer-neutral declarations in the admission fragment -/

open AdmissionRewriting

mutual
/-- Whether a head occurs in a term, held positions included. -/
def mentions (f : Name) : Tm → Bool
  | .var _ => false
  | .lit _ => false
  | .quote t => mentions f t
  | .tup xs => mentionsList f xs
  | .empty => false
  | .if3 c t e => mentions f c || mentions f t || mentions f e
  | .if2 c t => mentions f c || mentions f t
  | .let_ e b => mentions f e || mentions f b
  | .letStar es b => mentionsList f es || mentions f b
  | .case_ e alts => mentions f e || mentionsAlts f alts
  | .sup xs => mentionsList f xs
  | .once b => mentions f b
  | .call g args => decide (g = f) || mentionsList f args
  | .iterC _ ops g => decide (g = f) || mentionsList f ops
  | .iterB _ ops b => mentionsList f ops || mentions f b
/-- The list version. -/
def mentionsList (f : Name) : List Tm → Bool
  | [] => false
  | x :: xs => mentions f x || mentionsList f xs
/-- The branch version. -/
def mentionsAlts (f : Name) : List (Pat × Tm) → Bool
  | [] => false
  | (_, b) :: rest => mentions f b || mentionsAlts f rest
end

/-- Two dialects that differ at most in the function of one head. -/
structure AgreeExcept (D D' : Dialect) (f : Name) : Prop where
  fn : ∀ g, g ≠ f → D'.fn g = D.fn g
  caseEmpty : D'.caseEmpty = D.caseEmpty
  if2 : D'.if2 = D.if2
  elseOnNonBool : D'.elseOnNonBool = D.elseOnNonBool
  nonBool : D'.nonBool = D.nonBool
  arity : D'.arity = D.arity
  meter : D'.meter = D.meter
  varRead : D'.varRead = D.varRead

section Neutral

variable {D D' : Dialect} {f : Name}

mutual
/-- A declaration of a head the program never mentions does not change its trace. -/
theorem eval_fn_irrelevant (h : AgreeExcept D D' f) :
    ∀ (t : Tm) (ρ : List Val), mentions f t = false → eval D' t ρ = eval D t ρ
  | .var _, _, _ => by simp only [eval, h.varRead]
  | .lit _, _, _ => rfl
  | .quote _, _, _ => rfl
  | .tup xs, ρ, hm => by
    simp only [mentions] at hm
    simp only [eval, h.meter, evalArgs_irrelevant h xs ρ hm]
  | .empty, _, _ => by simp only [eval, h.meter]
  | .if3 c t e, ρ, hm => by
    simp only [mentions, Bool.or_eq_false_iff] at hm
    simp only [eval, h.meter, h.nonBool, h.elseOnNonBool, eval_fn_irrelevant h c ρ hm.1.1,
      eval_fn_irrelevant h t ρ hm.1.2, eval_fn_irrelevant h e ρ hm.2]
  | .if2 c t, ρ, hm => by
    simp only [mentions, Bool.or_eq_false_iff] at hm
    simp only [eval, h.meter, h.nonBool, h.elseOnNonBool, h.if2, h.arity,
      eval_fn_irrelevant h c ρ hm.1,
      eval_fn_irrelevant h t ρ hm.2]
  | .let_ e b, ρ, hm => by
    simp only [mentions, Bool.or_eq_false_iff] at hm
    simp only [eval, h.meter, eval_fn_irrelevant h e ρ hm.1]
    congr 1
    exact bindT_congr _ fun v => by rw [eval_fn_irrelevant h b (v :: ρ) hm.2]
  | .letStar es b, ρ, hm => by
    simp only [mentions, Bool.or_eq_false_iff] at hm
    simp only [eval, h.meter]
    congr 1
    exact evalLS_irrelevant h es (fun ρ' => eval D' b ρ') (fun ρ' => eval D b ρ')
      (fun ρ' => eval_fn_irrelevant h b ρ' hm.2) ρ hm.1
  | .case_ e alts, ρ, hm => by
    simp only [mentions, Bool.or_eq_false_iff] at hm
    simp only [eval, h.meter, eval_fn_irrelevant h e ρ hm.1, onEmpty_irrelevant h alts ρ hm.2]
    congr 2
    exact bindT_congr _ fun v => select_irrelevant h alts v ρ hm.2
  | .sup xs, ρ, hm => by
    simp only [mentions] at hm
    simp only [eval, h.meter, evalSup_irrelevant h xs ρ hm]
  | .once b, ρ, hm => by
    simp only [mentions] at hm
    simp only [eval, h.meter, eval_fn_irrelevant h b ρ hm]
  | .call g args, ρ, hm => by
    simp only [mentions, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hm
    simp only [eval, h.meter, evalArgs_irrelevant h args ρ hm.2, h.fn g hm.1]
  | .iterC k ops g, ρ, hm => by
    simp only [mentions, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hm
    simp only [eval, h.meter, evalArgs_irrelevant h ops ρ hm.2, h.fn g hm.1]
  | .iterB k ops b, ρ, hm => by
    simp only [mentions, Bool.or_eq_false_iff] at hm
    simp only [eval, h.meter, evalArgs_irrelevant h ops ρ hm.1]
    congr 1
    exact bindT_congr _ fun v =>
      iterate_congr k (fun vs _ => eval_fn_irrelevant h b (vs.reverse ++ ρ) hm.2) v
/-- The argument version. -/
theorem evalArgs_irrelevant (h : AgreeExcept D D' f) :
    ∀ (xs : List Tm) (ρ : List Val), mentionsList f xs = false →
      evalArgs D' xs ρ = evalArgs D xs ρ
  | [], _, _ => rfl
  | x :: xs, ρ, hm => by
    simp only [mentionsList, Bool.or_eq_false_iff] at hm
    simp only [evalArgs, eval_fn_irrelevant h x ρ hm.1, evalArgs_irrelevant h xs ρ hm.2]
/-- The alternative version. -/
theorem evalSup_irrelevant (h : AgreeExcept D D' f) :
    ∀ (xs : List Tm) (ρ : List Val), mentionsList f xs = false →
      evalSup D' xs ρ = evalSup D xs ρ
  | [], _, _ => rfl
  | x :: xs, ρ, hm => by
    simp only [mentionsList, Bool.or_eq_false_iff] at hm
    simp only [evalSup, eval_fn_irrelevant h x ρ hm.1, evalSup_irrelevant h xs ρ hm.2]
/-- The `let*` version. -/
theorem evalLS_irrelevant (h : AgreeExcept D D' f) :
    ∀ (es : List Tm) (k k' : List Val → Trace), (∀ ρ, k ρ = k' ρ) →
      ∀ (ρ : List Val), mentionsList f es = false → evalLS D' es k ρ = evalLS D es k' ρ
  | [], _, _, hk, ρ, _ => hk ρ
  | e :: es, k, k', hk, ρ, hm => by
    simp only [mentionsList, Bool.or_eq_false_iff] at hm
    simp only [evalLS, eval_fn_irrelevant h e ρ hm.1]
    exact bindT_congr _ fun v => evalLS_irrelevant h es k k' hk (v :: ρ) hm.2
/-- The branch version. -/
theorem select_irrelevant (h : AgreeExcept D D' f) :
    ∀ (alts : List (Pat × Tm)) (v : Val) (ρ : List Val), mentionsAlts f alts = false →
      select D' alts v ρ = select D alts v ρ
  | [], _, _, _ => rfl
  | (.bind, b) :: rest, v, ρ, hm => by
    simp only [mentionsAlts, Bool.or_eq_false_iff] at hm
    simp only [select, eval_fn_irrelevant h b (v :: ρ) hm.1]
  | (.lit l, b) :: rest, v, ρ, hm => by
    simp only [mentionsAlts, Bool.or_eq_false_iff] at hm
    simp only [select, eval_fn_irrelevant h b ρ hm.1, select_irrelevant h rest v ρ hm.2]
/-- The empty-scrutinee version. -/
theorem onEmpty_irrelevant (h : AgreeExcept D D' f) :
    ∀ (alts : List (Pat × Tm)) (ρ : List Val), mentionsAlts f alts = false →
      onEmpty D' alts ρ = onEmpty D alts ρ
  | [], _, _ => rfl
  | (p, b) :: rest, ρ, hm => by
    simp only [mentionsAlts, Bool.or_eq_false_iff] at hm
    simp only [onEmpty, h.caseEmpty, eval_fn_irrelevant h b ρ hm.1,
      eval_fn_irrelevant h b (.sym .emp :: ρ) hm.1, onEmpty_irrelevant h rest ρ hm.2]
end

end Neutral

/-! ## Guard declarations on integer calls -/

mutual
/-- Every call of `f` takes integer atoms (under the facts at its position); `f` is not
passed as a callable, and does not occur in held syntax. -/
def intCalls (f : Name) : Facts → Tm → Bool
  | _, .var _ => true
  | _, .lit _ => true
  | _, .quote t => !mentions f t
  | Γ, .tup xs => intCallsList f Γ xs
  | _, .empty => true
  | Γ, .if3 c t e => intCalls f Γ c && intCalls f Γ t && intCalls f Γ e
  | Γ, .if2 c t => intCalls f Γ c && intCalls f Γ t
  | Γ, .let_ e b => intCalls f Γ e && intCalls f (push Γ) b
  | Γ, .letStar es b => intCallsLS f Γ es && intCalls f (pushN es.length Γ) b
  | Γ, .case_ e alts => intCalls f Γ e && intCallsAlts f Γ alts
  | Γ, .sup xs => intCallsList f Γ xs
  | Γ, .once b => intCalls f Γ b
  | Γ, .call g args => (!decide (g = f) || args.all (IntAtom Γ)) && intCallsList f Γ args
  | Γ, .iterC _ ops g => !decide (g = f) && intCallsList f Γ ops
  | Γ, .iterB k ops b => intCallsList f Γ ops && intCalls f (pushN k.binders Γ) b
/-- The list version. -/
def intCallsList (f : Name) (Γ : Facts) : List Tm → Bool
  | [] => true
  | x :: xs => intCalls f Γ x && intCallsList f Γ xs
/-- The `let*` version: each source one binder deeper. -/
def intCallsLS (f : Name) : Facts → List Tm → Bool
  | _, [] => true
  | Γ, e :: es => intCalls f Γ e && intCallsLS f (push Γ) es
/-- The branch version. -/
def intCallsAlts (f : Name) (Γ : Facts) : List (Pat × Tm) → Bool
  | [] => true
  | (p, b) :: rest => intCalls f (p.scope Γ) b && intCallsAlts f Γ rest
end

/-- A dialect whose `f` is guarded: it agrees with the old one on integer arguments. -/
structure GuardedAt (D D' : Dialect) (f : Name) : Prop where
  agree : AgreeExcept D D' f
  ints : ∀ ns : List ℤ, D'.fn f (ns.map .int) = D.fn f (ns.map .int)
  intRead : ∀ n : ℤ, D.varRead (.int n) = ret (.int n)

theorem evalArgs_intAtoms (D : Dialect) (hvr : ∀ n : ℤ, D.varRead (.int n) = ret (.int n))
    {Γ : Facts} {ρ : List Val} (hρ : Sat Γ ρ) :
    ∀ (args : List Tm), args.all (IntAtom Γ) = true →
      ∃ ns : List ℤ, evalArgs D args ρ = ret (.tup (ns.map .int))
  | [], _ => ⟨[], rfl⟩
  | a :: args, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨n, hn⟩ := eval_intAtom hρ D hvr h.1
    obtain ⟨ns, hns⟩ := evalArgs_intAtoms D hvr hρ args h.2
    exact ⟨n :: ns, by simp [evalArgs, hn, hns, consTup]⟩

section Guard

variable {D D' : Dialect} {f : Name}

mutual
/-- A guard declaration that agrees on integers does not change the trace of a program
whose calls of the guarded head all take integer atoms. -/
theorem eval_guard_neutral (h : GuardedAt D D' f) :
    ∀ (Γ : Facts) (t : Tm) (ρ : List Val), Sat Γ ρ → intCalls f Γ t = true →
      eval D' t ρ = eval D t ρ
  | _, .var _, _, _, _ => by simp only [eval, h.agree.varRead]
  | _, .lit _, _, _, _ => rfl
  | _, .quote _, _, _, _ => rfl
  | Γ, .tup xs, ρ, hρ, hi => by
    simp only [intCalls] at hi
    simp only [eval, h.agree.meter, evalArgs_guard h Γ xs ρ hρ hi]
  | _, .empty, _, _, _ => by simp only [eval, h.agree.meter]
  | Γ, .if3 c t e, ρ, hρ, hi => by
    simp only [intCalls, Bool.and_eq_true] at hi
    simp only [eval, h.agree.meter, h.agree.nonBool, h.agree.elseOnNonBool,
      eval_guard_neutral h Γ c ρ hρ hi.1.1,
      eval_guard_neutral h Γ t ρ hρ hi.1.2, eval_guard_neutral h Γ e ρ hρ hi.2]
  | Γ, .if2 c t, ρ, hρ, hi => by
    simp only [intCalls, Bool.and_eq_true] at hi
    simp only [eval, h.agree.meter, h.agree.nonBool, h.agree.elseOnNonBool, h.agree.if2,
      h.agree.arity,
      eval_guard_neutral h Γ c ρ hρ hi.1, eval_guard_neutral h Γ t ρ hρ hi.2]
  | Γ, .let_ e b, ρ, hρ, hi => by
    simp only [intCalls, Bool.and_eq_true] at hi
    simp only [eval, h.agree.meter, eval_guard_neutral h Γ e ρ hρ hi.1]
    congr 1
    exact bindT_congr _ fun v => by
      rw [eval_guard_neutral h (push Γ) b (v :: ρ) (hρ.push v) hi.2]
  | Γ, .letStar es b, ρ, hρ, hi => by
    simp only [intCalls, Bool.and_eq_true] at hi
    simp only [eval, h.agree.meter]
    congr 1
    exact evalLS_guard h es Γ (fun ρ' => eval D' b ρ') (fun ρ' => eval D b ρ')
      (fun ρ' hρ' => eval_guard_neutral h _ b ρ' hρ' hi.2) ρ hρ hi.1
  | Γ, .case_ e alts, ρ, hρ, hi => by
    simp only [intCalls, Bool.and_eq_true] at hi
    simp only [eval, h.agree.meter, eval_guard_neutral h Γ e ρ hρ hi.1,
      onEmpty_guard h Γ alts ρ hρ hi.2]
    congr 2
    exact bindT_congr _ fun v => select_guard h Γ alts v ρ hρ hi.2
  | Γ, .sup xs, ρ, hρ, hi => by
    simp only [intCalls] at hi
    simp only [eval, h.agree.meter, evalSup_guard h Γ xs ρ hρ hi]
  | Γ, .once b, ρ, hρ, hi => by
    simp only [intCalls] at hi
    simp only [eval, h.agree.meter, eval_guard_neutral h Γ b ρ hρ hi]
  | Γ, .call g args, ρ, hρ, hi => by
    simp only [intCalls, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not] at hi
    simp only [eval, h.agree.meter, evalArgs_guard h Γ args ρ hρ hi.2]
    by_cases hg : g = f
    · subst hg
      have hall : args.all (IntAtom Γ) = true := by
        rcases hi.1 with h1 | h1
        · exact absurd rfl h1
        · exact h1
      obtain ⟨ns, hns⟩ := evalArgs_intAtoms D h.intRead hρ args hall
      rw [hns]
      simp [applyTup, h.ints ns]
    · rw [h.agree.fn g hg]
  | Γ, .iterC k ops g, ρ, hρ, hi => by
    simp only [intCalls, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hi
    simp only [eval, h.agree.meter, evalArgs_guard h Γ ops ρ hρ hi.2, h.agree.fn g hi.1]
  | Γ, .iterB k ops b, ρ, hρ, hi => by
    simp only [intCalls, Bool.and_eq_true] at hi
    simp only [eval, h.agree.meter, evalArgs_guard h Γ ops ρ hρ hi.1]
    congr 1
    refine bindT_congr _ fun v => iterate_congr k (fun vs hl => ?_) v
    exact eval_guard_neutral h _ b _ (by simpa [hl] using hρ.pushN vs) hi.2
/-- The argument version. -/
theorem evalArgs_guard (h : GuardedAt D D' f) :
    ∀ (Γ : Facts) (xs : List Tm) (ρ : List Val), Sat Γ ρ → intCallsList f Γ xs = true →
      evalArgs D' xs ρ = evalArgs D xs ρ
  | _, [], _, _, _ => rfl
  | Γ, x :: xs, ρ, hρ, hi => by
    simp only [intCallsList, Bool.and_eq_true] at hi
    simp only [evalArgs, eval_guard_neutral h Γ x ρ hρ hi.1, evalArgs_guard h Γ xs ρ hρ hi.2]
/-- The alternative version. -/
theorem evalSup_guard (h : GuardedAt D D' f) :
    ∀ (Γ : Facts) (xs : List Tm) (ρ : List Val), Sat Γ ρ → intCallsList f Γ xs = true →
      evalSup D' xs ρ = evalSup D xs ρ
  | _, [], _, _, _ => rfl
  | Γ, x :: xs, ρ, hρ, hi => by
    simp only [intCallsList, Bool.and_eq_true] at hi
    simp only [evalSup, eval_guard_neutral h Γ x ρ hρ hi.1, evalSup_guard h Γ xs ρ hρ hi.2]
/-- The `let*` version. -/
theorem evalLS_guard (h : GuardedAt D D' f) :
    ∀ (es : List Tm) (Γ : Facts) (k k' : List Val → Trace),
      (∀ ρ, Sat (pushN es.length Γ) ρ → k ρ = k' ρ) →
      ∀ (ρ : List Val), Sat Γ ρ → intCallsLS f Γ es = true → evalLS D' es k ρ = evalLS D es k' ρ
  | [], _, _, _, hk, ρ, hρ, _ => hk ρ hρ
  | e :: es, Γ, k, k', hk, ρ, hρ, hi => by
    simp only [intCallsLS, Bool.and_eq_true] at hi
    simp only [evalLS, eval_guard_neutral h Γ e ρ hρ hi.1]
    exact bindT_congr _ fun v =>
      evalLS_guard h es (push Γ) k k' (by simpa [pushN_succ] using hk) (v :: ρ) (hρ.push v) hi.2
/-- The branch version. -/
theorem select_guard (h : GuardedAt D D' f) :
    ∀ (Γ : Facts) (alts : List (Pat × Tm)) (v : Val) (ρ : List Val), Sat Γ ρ →
      intCallsAlts f Γ alts = true → select D' alts v ρ = select D alts v ρ
  | _, [], _, _, _, _ => rfl
  | Γ, (.bind, b) :: rest, v, ρ, hρ, hi => by
    simp only [intCallsAlts, Bool.and_eq_true] at hi
    simp only [select, eval_guard_neutral h _ b (v :: ρ) (hρ.push v) hi.1]
  | Γ, (.lit l, b) :: rest, v, ρ, hρ, hi => by
    simp only [intCallsAlts, Bool.and_eq_true] at hi
    simp only [select, eval_guard_neutral h _ b ρ hρ hi.1, select_guard h Γ rest v ρ hρ hi.2]
/-- The empty-scrutinee version. -/
theorem onEmpty_guard (h : GuardedAt D D' f) :
    ∀ (Γ : Facts) (alts : List (Pat × Tm)) (ρ : List Val), Sat Γ ρ →
      intCallsAlts f Γ alts = true → onEmpty D' alts ρ = onEmpty D alts ρ
  | _, [], _, _, _ => rfl
  | Γ, (.bind, b) :: rest, ρ, hρ, hi => by
    simp only [intCallsAlts, Bool.and_eq_true] at hi
    have hb := eval_guard_neutral h _ b (.sym .emp :: ρ) (hρ.push _) hi.1
    have hr := onEmpty_guard h Γ rest ρ hρ hi.2
    simp only [onEmpty, h.agree.caseEmpty]
    cases D.caseEmpty with
    | none => rfl
    | literal => exact hr
    | matching => exact hb
  | Γ, (.lit l, b) :: rest, ρ, hρ, hi => by
    simp only [intCallsAlts, Bool.and_eq_true] at hi
    have hb := eval_guard_neutral h _ b ρ hρ hi.1
    have hr := onEmpty_guard h Γ rest ρ hρ hi.2
    simp only [onEmpty, h.agree.caseEmpty]
    cases D.caseEmpty with
    | none => rfl
    | literal => simp only [hb, hr]
    | matching => simp only [hb, hr]
end

end Guard

/-! ## Controls: the cliff families in miniature

Three loop iterations, each a step of the loop and one of its callee, at fast cost 1 and
general cost 30.  The static graph also holds a never-taken site of an unknown head
(`#+`), which the tier does not compile; the program may declare an uncalled `quoteit`,
which the tier refuses as a whole. -/

namespace Controls

/-- Sites of the miniature program. -/
inductive Site
  | loop
  | callee
  | dead
  deriving DecidableEq

/-- Heads of the miniature program. -/
inductive Head
  | loop
  | g
  | hashPlus
  | quoteit
  deriving DecidableEq

/-- The callee of each site. -/
def headOf : Site → Head
  | .loop => .loop
  | .callee => .g
  | .dead => .hashPlus

/-- The tier compiles every site but the unknown head's. -/
def adm : SiteAdmission Site Head Unit where
  head := headOf
  admit := fun _ s => s != .dead
  check := fun _ _ => 0

/-- Engines with nothing to observe but cost. -/
def engines : Engines Site Unit Unit where
  gen := fun _ _ => ()
  fast := fun _ _ => ()
  enc := id
  dec := some
  sim := fun _ _ => rfl
  dec_enc := fun _ _ h => (Option.some.inj h).symm

/-- Fast and general costs. -/
def cf : Site → ℕ := fun _ => 1
/-- Fast and general costs. -/
def cg : Site → ℕ := fun _ => 30

/-- Three iterations; the dead site never runs. -/
def run : List Site := [.loop, .callee, .loop, .callee, .loop, .callee]

/-- No declarations. -/
def none₀ : Decls Head Unit := fun _ => none

/-- The tier refuses a program declaring `quoteit` (an `Atom`-holding declaration). -/
def declOK (Γd : Decls Head Unit) : Bool := (Γd .quoteit).isNone

/-- The never-taken `#+`: refusing the graph costs 180, declining the site costs 6. -/
theorem never_taken :
    localCost adm engines cf cg none₀ run = 6 ∧
      wholeCost adm declOK [.loop, .callee, .dead] cf cg none₀ run = 180 := by decide

/-- The uncalled `quoteit` declaration: refusing the graph jumps from 6 to 180; local
admission keeps 6. -/
theorem uncalled_declaration :
    wholeCost adm declOK [.loop, .callee] cf cg none₀ run = 6 ∧
      wholeCost adm declOK [.loop, .callee] cf cg (Function.update none₀ .quoteit (some ())) run =
        180 ∧
      localCost adm engines cf cg (Function.update none₀ .quoteit (some ())) run = 6 := by
  decide

end Controls

end Mettapedia.Machines.AdmissionRewriting.LocalDeclines
