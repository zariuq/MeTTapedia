import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.EvaluationModes.Designs

/-!
# Laws of the core: fuel, determinism, weaker checks, instantiation

* `exec_succ`, `exec_mono`: a run that finishes with some fuel finishes with the same answers with
  more; `exec_det`: two finishing runs of one goal give the same answers. So "the answers of a goal"
  is well defined, and `Finishes` names them.
* `exec_weaker`: making some definitions' result checks accept more (drop a check) changes no run
  that refused nothing: the same fuel gives the same answers. This is the core half of the
  weakening law; which elaborations stay inside its hypothesis is decided in `Laws`.
* `inst_nil`, `inst_closed`: instantiation leaves a template without variables unchanged.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.EvaluationModes

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Core

namespace CoreLaws

/-! ## More fuel -/

theorem continueEach_mono {k k' : Atom → Option (List Ans)}
    (hk : ∀ v here, k v = some here → k' v = some here) :
    ∀ (first L : List Ans), continueEach k first = some L → continueEach k' first = some L
  | [], _, h => h
  | (.val v, tr) :: rest, L, h => by
      unfold continueEach at h ⊢
      cases hv : k v with
      | none => rw [hv] at h; exact absurd h (by simp)
      | some here =>
          cases hr : continueEach k rest with
          | none => rw [hv, hr] at h; exact absurd h (by simp)
          | some later =>
              rw [hv, hr] at h
              rw [hk v here hv, continueEach_mono hk rest later hr]
              exact h
  | (.refused d kd, tr) :: rest, L, h => by
      unfold continueEach at h ⊢
      cases hr : continueEach k rest with
      | none => rw [hr] at h; exact absurd h (by simp)
      | some later =>
          rw [hr] at h
          rw [continueEach_mono hk rest later hr]
          exact h

theorem runClauses_mono {ev ev' : Env → Comp → Option (List Ans)}
    (hev : ∀ ρ c here, ev ρ c = some here → ev' ρ c = some here) (args : List Atom) :
    ∀ (clauses : List (List Atom × Comp)) (L : List Ans),
      runClauses ev args clauses = some L → runClauses ev' args clauses = some L
  | [], _, h => h
  | (pats, body) :: rest, L, h => by
      unfold runClauses at h ⊢
      cases hm : matchAtom.matchList pats args [] with
      | none =>
          cases hr : runClauses ev args rest with
          | none => rw [hm, hr] at h; exact absurd h (by simp)
          | some later =>
              rw [hm, hr] at h
              rw [runClauses_mono hev args rest later hr]
              exact h
      | some ρ =>
          cases hr : runClauses ev args rest with
          | none => rw [hm, hr] at h; exact absurd h (by simp)
          | some later =>
              rw [hm, hr] at h
              rw [runClauses_mono hev args rest later hr]
              simp only at h ⊢
              cases he : ev ρ body with
              | none => rw [he] at h; exact absurd h (by simp)
              | some here =>
                  rw [he] at h
                  rw [hev ρ body here he]
                  exact h

/-- One more unit of fuel changes no finished run. -/
theorem exec_succ (P : Prog) (n : Nat) :
    ∀ (g : Goal) (L : List Ans), exec P n g = some L → exec P (n + 1) g = some L := by
  induction n with
  | zero => intro g L h; simp [exec] at h
  | succ n ih =>
      intro g L h
      match g with
      | .comp ρ (.ret t) => exact h
      | .comp ρ (.plus a b) => exact h
      | .comp ρ (.run t) => exact ih _ _ h
      | .comp ρ (.call f args) => exact ih _ _ h
      | .comp ρ (.bind c x k) =>
          rw [exec_bind] at h ⊢
          cases hc : exec P n (.comp ρ c) with
          | none => rw [hc] at h; exact absurd h (by simp)
          | some first =>
              rw [hc] at h
              rw [ih _ _ hc]
              exact continueEach_mono (fun v here hv => ih _ _ hv) first L h
      | .enter f args =>
          unfold exec at h ⊢
          cases hf : P.find f args.length with
          | none => rw [hf] at h; exact h
          | some d =>
              rw [hf] at h
              simp only at h ⊢
              cases hr : firstRefusal d.argChecks args with
              | some p => rw [hr] at h; exact h
              | none =>
                  rw [hr] at h
                  simp only at h ⊢
                  by_cases hm : anyClauseMatches args d.clauses = true
                  · rw [if_pos hm] at h ⊢
                    cases hc : runClauses (fun ρ c => exec P n (.comp ρ c)) args d.clauses with
                    | none => rw [hc] at h; exact absurd h (by simp)
                    | some R0 =>
                        rw [hc] at h
                        rw [runClauses_mono (fun ρ c here hv => ih _ _ hv) args d.clauses R0 hc]
                        exact h
                  · rw [if_neg hm] at h ⊢
                    exact h

/-- More fuel changes no finished run. -/
theorem exec_mono (P : Prog) {n m : Nat} (le : n ≤ m) (g : Goal) (L : List Ans)
    (h : exec P n g = some L) : exec P m g = some L := by
  induction le with
  | refl => exact h
  | step _ ih => exact exec_succ P _ g L ih

/-- Two finished runs of one goal give the same answers. -/
theorem exec_det (P : Prog) {n m : Nat} (g : Goal) {L L' : List Ans}
    (h : exec P n g = some L) (h' : exec P m g = some L') : L = L' := by
  rcases Nat.le_total n m with le | le
  · have := exec_mono P le g L h
    rw [this] at h'
    exact Option.some.inj h'
  · have := exec_mono P le g L' h'
    rw [this] at h
    exact (Option.some.inj h).symm

/-- A goal finishes with these answers. -/
def Finishes (P : Prog) (g : Goal) (L : List Ans) : Prop := ∃ n, exec P n g = some L

theorem Finishes.det {P : Prog} {g : Goal} {L L' : List Ans}
    (h : Finishes P g L) (h' : Finishes P g L') : L = L' := by
  obtain ⟨n, hn⟩ := h
  obtain ⟨m, hm⟩ := h'
  exact exec_det P g hn hm

/-! ## Weaker result checks -/

/-- `d'` is `d` with a result check that accepts at least as much: none, or the same. -/
structure DefWeaker (d d' : Def) : Prop where
  head : d'.head = d.head
  arity : d'.arity = d.arity
  argChecks : d'.argChecks = d.argChecks
  clauses : d'.clauses = d.clauses
  result : d'.resultCheck = none ∨ d'.resultCheck = d.resultCheck

theorem DefWeaker.refl (d : Def) : DefWeaker d d := ⟨rfl, rfl, rfl, rfl, .inr rfl⟩

/-- Same reading of code; definitions in correspondence, each weaker. -/
structure ProgWeaker (Q Q' : Prog) : Prop where
  code : Q'.code = Q.code
  defs : List.Forall₂ DefWeaker Q.defs Q'.defs

theorem find_weaker {ds ds' : List Def} (h : List.Forall₂ DefWeaker ds ds') (f : String) (n : Nat) :
    (ds.find? fun d => d.head == f && d.arity == n) = none ∧
        (ds'.find? fun d => d.head == f && d.arity == n) = none ∨
      ∃ d d', (ds.find? fun d => d.head == f && d.arity == n) = some d ∧
        (ds'.find? fun d => d.head == f && d.arity == n) = some d' ∧ DefWeaker d d' := by
  induction h with
  | nil => exact .inl ⟨rfl, rfl⟩
  | @cons d d' ds ds' hd _ ih =>
      by_cases hp : (d.head == f && d.arity == n) = true
      · have hp' : (d'.head == f && d'.arity == n) = true := by rw [hd.head, hd.arity]; exact hp
        exact .inr ⟨d, d', by simp [List.find?, hp], by simp [List.find?, hp'], hd⟩
      · have hp' : ¬ (d'.head == f && d'.arity == n) = true := by rw [hd.head, hd.arity]; exact hp
        simp only [List.find?, hp, hp']
        exact ih

theorem allVal_cons (a : Ans) (L : List Ans) : allVal (a :: L) = (a.1.isVal && allVal L) := rfl

theorem allVal_append (L L' : List Ans) : allVal (L ++ L') = (allVal L && allVal L') := by
  simp [allVal, List.all_append]

theorem continueEach_weaker {k k' : Atom → Option (List Ans)}
    (hk : ∀ v here, k v = some here → allVal here = true → k' v = some here) :
    ∀ (first L : List Ans), continueEach k first = some L → allVal L = true →
      allVal first = true ∧ continueEach k' first = some L
  | [], _, h, _ => ⟨rfl, h⟩
  | (.val v, tr) :: rest, L, h, hL => by
      unfold continueEach at h ⊢
      cases hv : k v with
      | none => rw [hv] at h; exact absurd h (by simp)
      | some here =>
          cases hr : continueEach k rest with
          | none => rw [hv, hr] at h; exact absurd h (by simp)
          | some later =>
              rw [hv, hr] at h
              have hL' := hL
              rw [← Option.some.inj h, allVal_append] at hL'
              have hhere : allVal here = true := by
                have h1 := (Bool.and_eq_true _ _).mp hL' |>.1
                simpa [allVal] using h1
              have hlater : allVal later = true := (Bool.and_eq_true _ _).mp hL' |>.2
              obtain ⟨hrest, hrest'⟩ := continueEach_weaker hk rest later hr hlater
              refine ⟨?_, ?_⟩
              · rw [allVal_cons]; simp [Out.isVal, hrest]
              · rw [hk v here hv hhere, hrest']
                exact h
  | (.refused d kd, tr) :: rest, L, h, hL => by
      unfold continueEach at h
      cases hr : continueEach k rest with
      | none => rw [hr] at h; exact absurd h (by simp)
      | some later =>
          rw [hr] at h
          rw [← Option.some.inj h] at hL
          simp [allVal, Out.isVal] at hL

theorem runClauses_weaker {ev ev' : Env → Comp → Option (List Ans)}
    (hev : ∀ ρ c here, ev ρ c = some here → allVal here = true → ev' ρ c = some here)
    (args : List Atom) :
    ∀ (clauses : List (List Atom × Comp)) (L : List Ans),
      runClauses ev args clauses = some L → allVal L = true →
        runClauses ev' args clauses = some L
  | [], _, h, _ => h
  | (pats, body) :: rest, L, h, hL => by
      unfold runClauses at h ⊢
      cases hm : matchAtom.matchList pats args [] with
      | none =>
          cases hr : runClauses ev args rest with
          | none => rw [hm, hr] at h; exact absurd h (by simp)
          | some later =>
              rw [hm, hr] at h
              rw [← Option.some.inj h] at hL
              rw [runClauses_weaker hev args rest later hr hL]
              exact h
      | some ρ =>
          cases hr : runClauses ev args rest with
          | none => rw [hm, hr] at h; exact absurd h (by simp)
          | some later =>
              rw [hm, hr] at h
              simp only at h
              cases he : ev ρ body with
              | none => rw [he] at h; exact absurd h (by simp)
              | some here =>
                  rw [he] at h
                  have hL' := hL
                  rw [← Option.some.inj h] at hL'
                  rw [allVal_append] at hL'
                  have hhere := ((Bool.and_eq_true _ _).mp hL').1
                  have hlater := ((Bool.and_eq_true _ _).mp hL').2
                  rw [runClauses_weaker hev args rest later hr hlater]
                  simp only
                  rw [hev ρ body here he hhere]
                  exact h

theorem checkResult_val_of_isVal {c c' : Option Kind} (hc : c' = none ∨ c' = c) (o : Out)
    (h : (checkResult c o).isVal = true) : checkResult c' o = checkResult c o := by
  rcases hc with hc | hc
  · subst hc
    cases o with
    | val d =>
        cases c with
        | none => rfl
        | some k =>
            by_cases ha : k.accepts d = true
            · simp [checkResult, ha]
            · simp [checkResult, ha, Out.isVal] at h
    | refused d k => cases c <;> rfl
  · rw [hc]

/-- **Weaker result checks change no run that refused nothing.** -/
theorem exec_weaker {Q Q' : Prog} (hw : ProgWeaker Q Q') (n : Nat) :
    ∀ (g : Goal) (L : List Ans), exec Q n g = some L → allVal L = true → exec Q' n g = some L := by
  induction n with
  | zero => intro g L h; simp [exec] at h
  | succ n ih =>
      intro g L h hL
      match g with
      | .comp ρ (.ret t) => exact h
      | .comp ρ (.plus a b) => exact h
      | .comp ρ (.run t) =>
          change exec Q' n (.comp [] (Q'.code (inst ρ t))) = some L
          rw [hw.code]
          exact ih _ _ h hL
      | .comp ρ (.call f args) => exact ih _ _ h hL
      | .comp ρ (.bind c x k) =>
          rw [exec_bind] at h ⊢
          cases hc : exec Q n (.comp ρ c) with
          | none => rw [hc] at h; exact absurd h (by simp)
          | some first =>
              rw [hc] at h
              obtain ⟨hfirst, hcont⟩ :=
                continueEach_weaker (fun v here hv hh => ih _ _ hv hh) first L h hL
              rw [ih _ _ hc hfirst]
              exact hcont
      | .enter f args =>
          unfold exec at h ⊢
          rcases find_weaker hw.defs f args.length with ⟨h1, h2⟩ | ⟨d, d', h1, h2, hd⟩
          · change (match Q.find f args.length with | _ => _) = some L at h
            change (match Q'.find f args.length with | _ => _) = some L
            unfold Prog.find at h ⊢
            rw [h1] at h
            rw [h2]
            exact h
          · unfold Prog.find at h ⊢
            rw [h1] at h
            rw [h2]
            simp only at h ⊢
            rw [hd.argChecks, hd.clauses]
            cases hr : firstRefusal d.argChecks args with
            | some p =>
                rw [hr] at h
                rw [← Option.some.inj h] at hL
                simp [allVal, Out.isVal] at hL
            | none =>
                rw [hr] at h
                simp only at h ⊢
                by_cases hm : anyClauseMatches args d.clauses = true
                · rw [if_pos hm] at h ⊢
                  cases hc : runClauses (fun ρ c => exec Q n (.comp ρ c)) args d.clauses with
                  | none => rw [hc] at h; exact absurd h (by simp)
                  | some R0 =>
                      rw [hc] at h
                      simp only [Option.map_some] at h
                      have hL' := hL
                      rw [← Option.some.inj h] at hL'
                      have hR0 : allVal R0 = true := by
                        simp only [allVal, List.all_map, List.all_eq_true, Function.comp_def] at hL' ⊢
                        intro a ha
                        have := hL' a ha
                        cases ho : a.1 with
                        | val _ => rfl
                        | refused e k =>
                            rw [ho] at this
                            cases hrc : d.resultCheck <;> simp [checkResult, hrc, Out.isVal] at this
                      rw [runClauses_weaker (fun ρ c here hv hh => ih _ _ hv hh) args d.clauses R0
                        hc hR0]
                      simp only [Option.map_some]
                      rw [← h]
                      congr 1
                      apply List.map_congr_left
                      intro a ha
                      have hva : (checkResult d.resultCheck a.1).isVal = true := by
                        rw [← Option.some.inj h] at hL
                        simp only [allVal, List.all_map, List.all_eq_true,
                          Function.comp_def] at hL
                        exact hL a ha
                      rw [checkResult_val_of_isVal hd.result a.1 hva]
                · rw [if_neg hm] at h ⊢
                  exact h

/-! ## Instantiation -/

theorem instList_of {ρ : Env} (items : List Atom) (ih : ∀ t ∈ items, inst ρ t = t) :
    inst.instList ρ items = items := by
  induction items with
  | nil => rfl
  | cons t rest ihl =>
      simp only [inst.instList]
      rw [ih t List.mem_cons_self, ihl fun u m => ih u (List.mem_cons_of_mem _ m)]

/-- The empty environment instantiates nothing. -/
theorem inst_nil : (t : Atom) → inst [] t = t
  | .var _ => rfl
  | .symbol _ => rfl
  | .grounded _ => rfl
  | .expression items => by
      simp only [inst]
      rw [instList_of items fun t _ => inst_nil t]
termination_by t => sizeOf t
decreasing_by
  have := List.sizeOf_lt_of_mem ‹t ∈ items›
  simp only [Atom.expression.sizeOf_spec]
  omega

theorem patVarsList_nil {items : List Atom} (h : patVars.patVarsList items = []) :
    ∀ t ∈ items, patVars t = [] := by
  induction items with
  | nil => intro t m; cases m
  | cons a rest ih =>
      simp only [patVars.patVarsList, List.append_eq_nil_iff] at h
      intro t m
      rcases List.mem_cons.mp m with rfl | m
      · exact h.1
      · exact ih h.2 t m

/-- A template without variables is its own instance. -/
theorem inst_closed (ρ : Env) : (t : Atom) → patVars t = [] → inst ρ t = t
  | .var _, h => by simp [patVars] at h
  | .symbol _, _ => rfl
  | .grounded _, _ => rfl
  | .expression items, h => by
      simp only [inst]
      have hitems := patVarsList_nil (by simpa [patVars] using h)
      rw [instList_of items fun t m => inst_closed ρ t (hitems t m)]
termination_by t => sizeOf t
decreasing_by
  have := List.sizeOf_lt_of_mem ‹t ∈ items›
  simp only [Atom.expression.sizeOf_spec]
  omega

end CoreLaws

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.EvaluationModes
