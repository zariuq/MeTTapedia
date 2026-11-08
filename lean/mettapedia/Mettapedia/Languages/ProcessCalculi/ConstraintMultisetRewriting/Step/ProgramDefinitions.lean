import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramEffects

/-!
# Changing definitions: the versions each computation and each conclusion used

A definition is a row `defn k u c`: name, version, closed code. `call k` reads the current definition
and leaves a citation `cite k u`; `redefine k u c` takes the current definition and installs version
`u`. Redefinition is an ordinary effect.

## What each computation records
* **At the source** (`new_citation_reads_definition`, `citations_persist`): every new citation is made
  by a call that read the definition with that version, and no rule removes a citation.
* **On the step** (`knowledge_retained`, `call_records_version`): the call firing's read equation stays
  in every later knowledge, so every later solution gives the firing's version variable the version
  the call read.

## A conclusion does not transport to another version without a recheck
* `redefinition_run`: `let x = call f in let _ = redefine f v₂ b in let y = call f in …` under
  `defn f v₁ a`: the same call concluded `a` under `v₁` and `b` under `v₂`, and both citations stay.
* **Control** (`unconditional_transport_unsound`): under `v₁` every halted run of `call f` concludes `a`;
  under `v₂` every halted run concludes `b`. Transporting the conclusion without its version is
  unsound. Its citation's recheck (`Recheck`) fails against the redefined rows.

## What stays valid
`what_stays_valid`: a conclusion together with its citations is reproduced in every configuration
that still holds the rows it started from, the cited definitions among them (`path_frame`); its
citations are never removed; and the knowledge it recorded is never retracted.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Program

open ProgramRows ProgramTranslation

/-! ## Head tags -/

/-- The tag of a row. -/
def headTag : Sx → Option ℕ
  | .cell (.sym k) _ => some k
  | _ => none

/-- The tag of a pattern with a rigid head. -/
def patHead : Pat → Option ℕ
  | .cell (.sym k) _ => some k
  | _ => none

theorem headTag_inst : ∀ (p : Pat), rigidHead p = true → ∀ θ : ℕ → Sx, headTag (p.inst θ) = patHead p
  | .cell (.sym _) _, _, _ => rfl
  | .var _, h, _ => by simp [rigidHead] at h
  | .sym _, h, _ => by simp [rigidHead] at h
  | .cell (.var _) _, h, _ => by simp [rigidHead] at h
  | .cell (.cell _ _) _, h, _ => by simp [rigidHead] at h

/-- No rule takes or reads a citation. -/
theorem schema_never_takes_citations (i : RuleName) :
    ∀ p ∈ (schema i).take ++ (schema i).read, patHead p ≠ some 35 := by
  cases i <;> decide

/-- Only calls make citations. -/
theorem schema_citations_from_calls (i : RuleName) :
    ∀ q ∈ (schema i).make, patHead q = some 35 → i = .call := by
  cases i <;> decide

/-! ## What each computation records, at the source -/

theorem mem_push {l : List Sx} {F : Multiset Sx} {s : Sx} : s ∈ push l F ↔ s ∈ l ∨ s ∈ F := by
  rw [push_eq, Multiset.mem_add, Multiset.mem_coe]

/-- **No rule removes a citation.** -/
theorem citations_persist {W W' : Multiset Sx} (step : Step W W') {s : Sx} (inW : s ∈ W)
    (citation : headTag s = some 35) : s ∈ W' := by
  obtain ⟨i, θ, F, rfl, rfl⟩ := (step_iff_rewrites W W').mp step
  obtain ⟨takeRigid, readRigid, -⟩ := schema_rigid i
  rcases mem_push.mp inW with taken | rest
  · exfalso
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp taken
    exact schema_never_takes_citations i p (List.mem_append_left _ hp)
      ((headTag_inst p (takeRigid p hp) θ).symm.trans citation)
  · exact mem_push.mpr (.inr rest)

/-- **Every new citation is made by a call that read the definition with that version.** -/
theorem new_citation_reads_definition {W W' : Multiset Sx} (step : Step W W') {s : Sx} (inW' : s ∈ W')
    (citation : headTag s = some 35) (fresh : s ∉ W) : ∃ k u c, s = cite k u ∧ defn k u c ∈ W := by
  obtain ⟨i, θ, F, rfl, rfl⟩ := (step_iff_rewrites W W').mp step
  obtain ⟨-, -, makeRigid⟩ := schema_rigid i
  rcases mem_push.mp inW' with made | rest
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp made
    have isCall := schema_citations_from_calls i q hq ((headTag_inst q (makeRigid q hq) θ).symm.trans citation)
    subst isCall
    simp only [schema, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · change some 29 = some 35 at citation
      simp at citation
    · exact ⟨θ 0, θ 3, θ 4, rfl, mem_push.mpr (.inr (mem_push.mpr (.inl (List.mem_singleton_self _))))⟩
  · exact absurd (mem_push.mpr (.inr rest)) fresh

/-! ## What each computation records, on the step -/

/-- **Knowledge is never retracted along a translated run**: it only grows by appended equations. -/
theorem knowledge_retained {p q : Config × ℕ} (run : Relation.ReflTransGen (Translated schema) p q) :
    ∃ added, q.1.equations = p.1.equations ++ added := by
  induction run with
  | refl => exact ⟨[], (List.append_nil _).symm⟩
  | tail _ step ih =>
      obtain ⟨added, eq⟩ := ih
      cases step with
      | @fire C n i taken read valid =>
          refine ⟨added ++ GuardFreeProcessOrders.added Occ.label ((schema i).firing n taken read).rule
            ((schema i).firing n taken read).selection, ?_⟩
          change (Selection.problem _ Occ.label _ C) = _
          rw [GuardFreeProcessOrders.problem_eq, eq, List.append_assoc]

/-- **A call firing records the version it read**, in every later knowledge: if the call at scope `n`
reads an occurrence that represents `defn k u c`, then along every later translated run every
solution gives the call's version variable `(n, 3)` the version `u`. -/
theorem call_records_version {C : Config} {n : ℕ} {taken : List Occ} {o : Occ} {k u c : Sx}
    (reads : ∀ σ, A.Models σ C.equations → σ.applyTerm o.label = embed (defn k u c))
    {q : Config × ℕ}
    (run : Relation.ReflTransGen (Translated schema)
      (((schema .call).firing n taken [o]).result Occ.label C, n + 1) q)
    (σ : Mettapedia.Logic.LP.Subst rows) (solved : A.Models σ q.1.equations) : σ (n, 3) = embed u := by
  obtain ⟨added, eq⟩ := knowledge_retained run
  rw [eq] at solved
  have result : A.Models σ (((schema .call).firing n taken [o]).result Occ.label C).equations :=
    fun e member => solved e (List.mem_append_left _ member)
  have problem : (((schema .call).firing n taken [o]).result Occ.label C).equations =
      C.equations ++ Selection.equations (T := Tm) Occ.label ((schema .call).take.map (Pat.at n)) taken ++
        Selection.equations (T := Tm) Occ.label ((schema .call).read.map (Pat.at n)) [o] ++ [] := rfl
  rw [problem] at result
  simp only [SubstitutionAction.models_append, SubstitutionAction.models_nil, and_true] at result
  obtain ⟨⟨old, -⟩, readModels⟩ := result
  have readEq := readModels _ (List.mem_singleton_self (Pat.at n (p3 34 (.var 0) (.var 3) (.var 4)), o.label))
  change σ.applyTerm _ = σ.applyTerm o.label at readEq
  rw [reads σ old] at readEq
  have := agree_of_apply (θ := args [k, default, default, u, c]) (p3 34 (.var 0) (.var 3) (.var 4))
    readEq 3 (by decide)
  exact this

/-! ## A conclusion does not transport to another version -/

def kf : Sx := .sym 105
def kv₁ : Sx := .sym 106
def kv₂ : Sx := .sym 107

/-- `let x = call f in let _ = redefine f v₂ b in let y = call f in λ. var 0`, under `defn f v₁ a`. -/
def redefinitionProgram : List Sx :=
  [ev (let_ (call kf) (let_ (redefine kf kv₂ (atom kb)) (let_ (call kf) (lam (var zero))))) nil nil,
    defn kf kv₁ (atom ka)]

/-- Its end: the second call concluded `b`, the first `a`; both citations stay; only `v₂` is
installed. -/
def redefinitionEnd : List Sx :=
  [ret (clo (var zero) (cons (atom kb) (cons (atom kv₂) (cons (atom ka) nil)))) nil,
    cite kf kv₁, cite kf kv₂, defn kf kv₂ (atom kb)]

theorem redefinitionProgram_closed : SuccessorClosed (reach 22 [redefinitionProgram]) = true := by decide

theorem redefinition_halted :
    (halted (reach 22 [redefinitionProgram])).all (fun H => H.isPerm redefinitionEnd) = true ∧
      halted (reach 22 [redefinitionProgram]) ≠ [] := by decide

/-- **One computation, two versions**: every halted run ends with the call concluding `a` under `v₁`
and `b` under `v₂`, both citations retained, and one does halt. -/
theorem redefinition_run :
    (∀ W, Relation.ReflTransGen Step (redefinitionProgram : Multiset Sx) W → (∀ W', ¬ Step W W') →
        W = (redefinitionEnd : Multiset Sx)) ∧
      Relation.ReflTransGen Step (redefinitionProgram : Multiset Sx) (redefinitionEnd : Multiset Sx) := by
  obtain ⟨all, nonempty⟩ := redefinition_halted
  obtain ⟨reached, every⟩ := halted_runs redefinitionProgram_closed
  refine ⟨fun W path stuck => ?_, ?_⟩
  · obtain ⟨H, mem, rfl⟩ := every W path stuck
    exact Multiset.coe_eq_coe.mpr (List.isPerm_iff.mp (List.all_eq_true.mp all H mem))
  · obtain ⟨H, rest, eq⟩ := List.exists_cons_of_ne_nil nonempty
    have mem : H ∈ halted (reach 22 [redefinitionProgram]) := by rw [eq]; exact List.mem_cons_self
    have := (reached H mem).1
    rwa [Multiset.coe_eq_coe.mpr (List.isPerm_iff.mp (List.all_eq_true.mp all H mem))] at this

/-- `call f` under one definition. -/
def callUnder (u d : Sx) : List Sx := [ev (call kf) nil nil, defn kf u (atom d)]
def callEnd (u d : Sx) : List Sx := [ret (atom d) nil, cite kf u, defn kf u (atom d)]

theorem callUnder₁_closed : SuccessorClosed (reach 3 [callUnder kv₁ ka]) = true := by decide
theorem callUnder₂_closed : SuccessorClosed (reach 3 [callUnder kv₂ kb]) = true := by decide

theorem callUnder_halted :
    halted (reach 3 [callUnder kv₁ ka]) = [callEnd kv₁ ka] ∧
      halted (reach 3 [callUnder kv₂ kb]) = [callEnd kv₂ kb] := by decide

/-- **The recheck of a conclusion's citations**: every cited version is installed. -/
def Recheck (conclusion rows : List Sx) : Bool :=
  conclusion.all fun s =>
    match s with
    | .cell (.sym 35) (.cell k u) => rows.any fun r =>
        match r with
        | .cell (.sym 34) (.cell k' (.cell u' _)) => k' == k && u' == u
        | _ => false
    | _ => true

/-- **Control: unconditional transport is unsound.** Under `v₁`, every halted run of `call f`
concludes `a` (and one does); under `v₂`, every halted run concludes `b`, so the conclusion `a` does not
hold there. The citation of the `v₁` conclusion passes its recheck against `v₁` and fails it against
`v₂`. -/
theorem unconditional_transport_unsound :
    Relation.ReflTransGen Step (callUnder kv₁ ka : Multiset Sx) (callEnd kv₁ ka : Multiset Sx) ∧
      (∀ W, Relation.ReflTransGen Step (callUnder kv₂ kb : Multiset Sx) W → (∀ W', ¬ Step W W') →
        W = (callEnd kv₂ kb : Multiset Sx)) ∧
      ret (atom ka) nil ∉ callEnd kv₂ kb ∧
      Recheck [cite kf kv₁] (callUnder kv₁ ka) = true ∧ Recheck [cite kf kv₁] (callUnder kv₂ kb) = false := by
  obtain ⟨halted₁, halted₂⟩ := callUnder_halted
  obtain ⟨reached₁, -⟩ := halted_runs callUnder₁_closed
  obtain ⟨-, every₂⟩ := halted_runs callUnder₂_closed
  refine ⟨(reached₁ _ (by rw [halted₁]; exact List.mem_singleton_self _)).1, fun W path stuck => ?_,
    by decide, by decide, by decide⟩
  obtain ⟨H, mem, rfl⟩ := every₂ W path stuck
  rw [halted₂, List.mem_singleton] at mem
  rw [mem]

/-! ## What stays valid -/

/-- **Steps are local**: a step stays a step beside any further rows. -/
theorem step_frame {W W' : Multiset Sx} (step : Step W W') (X : Multiset Sx) : Step (W + X) (W' + X) := by
  obtain ⟨i, θ, F, rfl, rfl⟩ := (step_iff_rewrites W W').mp step
  refine (step_iff_rewrites _ _).mpr ⟨i, θ, F + X, ?_, ?_⟩ <;>
    simp only [push_eq, add_assoc]

theorem path_frame {W W' : Multiset Sx} (path : Relation.ReflTransGen Step W W') (X : Multiset Sx) :
    Relation.ReflTransGen Step (W + X) (W' + X) := by
  induction path with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (step_frame step X)

/-- **What stays valid under redefinition.** A conclusion reached from some rows, the cited
definitions among them, is reached with its citations from every configuration that still holds
those rows; each of its citations persists along every later run; and on the step, the knowledge
recorded by a translated run is never retracted. -/
theorem what_stays_valid {W W' : Multiset Sx} (path : Relation.ReflTransGen Step W W') :
    (∀ X : Multiset Sx, Relation.ReflTransGen Step (W + X) (W' + X)) ∧
      (∀ V, Relation.ReflTransGen Step W' V → ∀ s ∈ W', headTag s = some 35 → s ∈ V) ∧
      ∀ {p q : Config × ℕ}, Relation.ReflTransGen (Translated schema) p q →
        ∃ added, q.1.equations = p.1.equations ++ added := by
  refine ⟨path_frame path, fun V later s inW' citation => ?_, knowledge_retained⟩
  induction later with
  | refl => exact inW'
  | tail _ step ih => exact citations_persist step ih citation

#print axioms headTag_inst
#print axioms schema_never_takes_citations
#print axioms schema_citations_from_calls
#print axioms citations_persist
#print axioms new_citation_reads_definition
#print axioms knowledge_retained
#print axioms call_records_version
#print axioms redefinition_run
#print axioms unconditional_transport_unsound
#print axioms step_frame
#print axioms path_frame
#print axioms what_stays_valid

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Program
