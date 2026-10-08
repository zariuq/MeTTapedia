import Mettapedia.GSLT.LanguageDef.TemplateScope.Corpus

/-!
# Template scope, naming part 1: lambda dropping, the inverse of lifting

`lifted cs L` (`TemplateScope.Evaluation`) turns a lambda into a program
equation whose leading parameters are the lambda's captured names; the call
spine `(Lf c₁ … cₖ)` passes the captured names back as references.  Dropping
goes the other way (Danvy and Schultz's parameter dropping): given an
equation and the arguments of a call spine, it peels the equation's leading
parameter binders, instantiating each by its argument, and gives back a
lambda.

## Main results

* `run_callSpine` — a call spine whose arguments are values evaluates to the
  dropped term, as a single result with the store unchanged.
* `run_dropped_call` — **dropping preserves observations**: calling the
  equation through its spine equals applying the dropped lambda, on the whole
  bag of results with final stores, for every argument, path and store.  No
  hygiene condition is needed: the evaluator performs exactly the
  substitutions that dropping performs.
* `run_lifted_call_of_dropped` — `run_lifted_call` is the special case of a
  lifted equation called on its captured names.
* `dropArgs_lifted` — drop of lift is the original lambda (equality, not only
  up to renaming: the lifted parameters are named by the captured names).
* `lifted_dropArgs` — lift of drop is the original equation, for equations
  of lifted shape (`LiftedShape`).
* `liftedShape_iff` — the equations of lifted shape are exactly the lifted
  equations of hygienic lambdas, so lifting and dropping are inverse
  bijections between the two sets.
* Examples on corpus row B4, and two negative examples: an equation that also
  uses a captured name as a store name does not come back from a round trip,
  and a spine argument that is not a value is evaluated once by the call but
  duplicated by dropping.
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope

open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline

universe u v

variable {S : Type u} {X : Type v}

/-! ## Call spines -/

/-- Read a call spine back: `(F a₁ … aₖ)` gives the equation `F` and its
arguments. -/
def unspine : Tm S X → Option (S × List (Tm S X))
  | .fn F => some (F, [])
  | .app f a => (unspine f).map fun p => (p.1, p.2 ++ [a])
  | _ => none

theorem unspine_foldl (h : Tm S X) : ∀ (args : List (Tm S X)),
    unspine (args.foldl .app h) = (unspine h).map fun p => (p.1, p.2 ++ args)
  | [] => by simp
  | a :: as => by
      rw [List.foldl_cons, unspine_foldl (.app h a) as]
      cases hh : unspine h <;> simp [unspine, hh]

theorem unspine_callSpine (F : S) (args : List (Tm S X)) :
    unspine (callSpine (.fn F) args) = some (F, args) := by
  simp [callSpine, unspine_foldl, unspine]

/-- A term that reads back as a spine is that spine. -/
theorem callSpine_of_unspine : ∀ {t : Tm S X} {F : S} {args : List (Tm S X)},
    unspine t = some (F, args) → t = callSpine (.fn F) args
  | .fn G, F, args, h => by
      simp only [unspine, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
  | .app f a, F, args, h => by
      cases hf : unspine f with
      | none => simp [unspine, hf] at h
      | some p =>
          obtain ⟨G, as⟩ := p
          simp only [unspine, hf, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rw [callSpine_of_unspine hf]
          simp [callSpine, List.foldl_append]
  | .sym _, _, _, h | .var _, _, _, h | .pvar _, _, _, h | .lam _ _ _, _, _, h
  | .quote _, _, _, h | .pquote _, _, _, h | .letP _ _ _, _, _, h | .alt _ _, _, _, h => by
      simp [unspine] at h

/-- Terms the evaluator returns as they are, in one step and with the store
unchanged: symbols, store names, parameters, lambdas and quotations. -/
def Tm.isVal : Tm S X → Bool
  | .sym _ | .var _ | .pvar _ | .lam _ _ _ | .quote _ | .ctx _ _ | .pquote _ => true
  | _ => false

/-! ## Dropping -/

variable [DecidableEq X]

/-- **Dropping.**  Peel the equation's leading parameter binders (which own no
store names) by the arguments of a call spine: each argument instantiates its
parameter, exactly as activation does. -/
def dropArgs : Tm S X → List (Tm S X) → Option (Tm S X)
  | E, [] => some E
  | .lam p [] b, a :: as => dropArgs (subst Sub.none (Sub.single p a) b) as
  | _, _ :: _ => none

/-- Drop a call: read the spine, look its equation up, and peel the
equation's parameters by the spine's arguments. -/
def dropCall (prog : S → Option (Tm S X)) (spine : Tm S X) : Option (Tm S X) :=
  (unspine spine).bind fun p => (prog p.1).bind fun E => dropArgs E p.2

theorem dropArgs_append : ∀ (E : Tm S X) (xs ys : List (Tm S X)),
    dropArgs E (xs ++ ys) = (dropArgs E xs).bind fun E' => dropArgs E' ys
  | E, [], ys => by simp [dropArgs]
  | E, a :: as, ys => by
      cases E with
      | lam p own b =>
          cases own with
          | nil =>
              simp only [List.cons_append, dropArgs]
              exact dropArgs_append _ as ys
          | cons o os => simp [dropArgs]
      | _ => simp [dropArgs]

theorem dropCall_callSpine (prog : S → Option (Tm S X)) (F : S) (args : List (Tm S X)) :
    dropCall prog (callSpine (.fn F) args) = (prog F).bind fun E => dropArgs E args := by
  simp [dropCall, unspine_callSpine]

/-- The lifted equation over no names is the lambda itself. -/
theorem lifted_nil (L : Tm S X) : lifted [] L = L := by
  simp only [lifted, List.foldr_nil, List.not_mem_nil, decide_false]
  have : (absP fun _ => false : Sub S X) = Sub.none := by
    funext n
    simp [absP, Sub.none]
  rw [this, subst_none_none]

/-! ## Dropping preserves observations -/

variable [DecidableEq S]

/-- A value evaluates to itself, with the store unchanged. -/
theorem run_val (d : Disc) (prog : S → Option (Tm S X)) (m : ℕ) (π : Path)
    (σ : GStore S X) {v : Tm S X} (hv : v.isVal = true) :
    run d prog (m + 1) π σ v = some [(v, σ)] := by
  cases v <;> first | rfl | simp [Tm.isVal] at hv

/-- **A call spine evaluates to the dropped term.**  If the spine's arguments
are values and dropping them into the equation gives a value, the spine
evaluates to that value, once, with the store unchanged. -/
theorem run_callSpine (prog : S → Option (Tm S X)) {F : S} {E : Tm S X}
    (hprog : prog F = some E) :
    ∀ (args : List (Tm S X)) {L : Tm S X}, (∀ a ∈ args, a.isVal = true) →
      dropArgs E args = some L → L.isVal = true →
      ∀ (n : ℕ) (π : Path) (σ : GStore S X), args.length + 2 ≤ n →
        run .static prog n π σ (callSpine (.fn F) args) = some [(L, σ)] := by
  intro args
  induction args using List.reverseRecOn with
  | nil =>
      intro L _ hdrop hL n π σ hn
      simp only [dropArgs, Option.some.injEq] at hdrop
      subst hdrop
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by simp at hn; omega⟩
      show step .static prog (run .static prog (m + 1)) π σ (.fn F) = _
      simp only [step, hprog]
      exact run_val .static prog m _ σ hL
  | append_singleton pre a ih =>
      intro L hargs hdrop hL n π σ hn
      rw [dropArgs_append] at hdrop
      cases hpre : dropArgs E pre with
      | none => rw [hpre] at hdrop; cases hdrop
      | some Lp =>
          rw [hpre] at hdrop
          simp only [Option.bind_some] at hdrop
          cases Lp with
          | lam p own b =>
              cases own with
              | nil =>
                  simp only [dropArgs, Option.some.injEq] at hdrop
                  simp only [List.length_append, List.length_singleton] at hn
                  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
                  have hspine : callSpine (.fn F) (pre ++ [a]) =
                      .app (callSpine (.fn F) pre) a := by
                    simp [callSpine, List.foldl_append]
                  rw [hspine]
                  show step .static prog (run .static prog (m + 1)) π σ _ = _
                  simp only [step]
                  rw [ih (fun x hx => hargs x (List.mem_append_left _ hx)) hpre rfl (m + 1)
                    (π ++ [0]) σ (by omega), bindOpt_some_singleton]
                  simp only
                  rw [run_val .static prog m _ σ (hargs a (by simp)), bindOpt_some_singleton]
                  simp only [activate, renameOwn_nil]
                  rw [hdrop]
                  exact run_val .static prog m _ σ hL
              | cons o os => simp [dropArgs] at hdrop
          | _ => simp [dropArgs] at hdrop

/-- **Dropping preserves observations.**  Calling an equation through a spine
of value arguments equals applying the lambda that dropping gives back, on the
whole observation: the bag of results with their final stores. -/
theorem run_dropped_call (prog : S → Option (Tm S X)) {F : S} {E : Tm S X}
    (hprog : prog F = some E) (args : List (Tm S X)) (hargs : ∀ a ∈ args, a.isVal = true)
    {z : Nm X} {own : List X} {body : Tm S X}
    (hdrop : dropArgs E args = some (.lam z own body)) (a : Tm S X) (n : ℕ)
    (hn : args.length + 3 ≤ n) (π : Path) (σ : GStore S X) :
    run .static prog n π σ (.app (callSpine (.fn F) args) a) =
      run .static prog n π σ (.app (.lam z own body) a) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  show step .static prog (run .static prog (m + 1)) π σ _ =
    step .static prog (run .static prog (m + 1)) π σ _
  simp only [step]
  rw [run_callSpine prog hprog args hargs hdrop rfl (m + 1) (π ++ [0]) σ (by omega), run_lam]

/-- Dropping preserves observations, stated with `dropCall` on the spine. -/
theorem run_dropCall (prog : S → Option (Tm S X)) {spine : Tm S X} {F : S}
    {args : List (Tm S X)} (hsp : unspine spine = some (F, args))
    (hargs : ∀ a ∈ args, a.isVal = true) {z : Nm X} {own : List X} {body : Tm S X}
    (hdrop : dropCall prog spine = some (.lam z own body)) (a : Tm S X) (n : ℕ)
    (hn : args.length + 3 ≤ n) (π : Path) (σ : GStore S X) :
    run .static prog n π σ (.app spine a) = run .static prog n π σ (.app (.lam z own body) a) := by
  rw [callSpine_of_unspine hsp] at hdrop ⊢
  rw [dropCall_callSpine] at hdrop
  cases hprog : prog F with
  | none => rw [hprog] at hdrop; cases hdrop
  | some E =>
      rw [hprog] at hdrop
      exact run_dropped_call prog hprog args hargs hdrop a n hn π σ

/-- Dropping preserves the answer bag of a query. -/
theorem answerBag_dropped_call (prog : S → Option (Tm S X)) {F : S} {E : Tm S X}
    (hprog : prog F = some E) (args : List (Tm S X)) (hargs : ∀ a ∈ args, a.isVal = true)
    {z : Nm X} {own : List X} {body : Tm S X}
    (hdrop : dropArgs E args = some (.lam z own body)) (a : Tm S X) (bag : List (Tm S X)) :
    AnswerBag .static prog (.app (callSpine (.fn F) args) a) bag ↔
      AnswerBag .static prog (.app (.lam z own body) a) bag :=
  AnswerBag.congr_of_run (args.length + 3)
    (fun n hn => run_dropped_call prog hprog args hargs hdrop a n hn [] Store.empty) bag

/-! ## Drop of lift -/

omit [DecidableEq S] in
/-- One step of dropping a lifted equation: the first captured name, passed
as a reference, instantiates the first lifted parameter. -/
theorem dropArgs_lifted_cons {c : Nm X} {cs : List (Nm X)} {L : Tm S X} (hc : c ∉ cs)
    (hcL : c ∉ paramNames L) (args : List (Tm S X)) :
    dropArgs (lifted (c :: cs) L) (.var c :: args) = dropArgs (lifted cs L) args := by
  simp only [lifted, List.foldr_cons, dropArgs]
  rw [subst_single_foldr_lam _ cs _ hc, subst_single_absP _ _ hcL]
  have habs : (absP fun n => decide (n ∈ c :: cs) && decide (n ≠ c) : Sub S X) =
      absP fun n => decide (n ∈ cs) := by
    apply absP_congr
    intro n
    by_cases hn : n = c
    · subst hn
      simp [hc]
    · simp [hn]
  rw [habs]

omit [DecidableEq S] in
/-- **Drop of lift is the original lambda.**  Exact equality: the lifted
parameters are named by the captured names themselves. -/
theorem dropArgs_lifted : ∀ (cs : List (Nm X)) (L : Tm S X), cs.Nodup →
    (∀ c ∈ cs, c ∉ paramNames L) → dropArgs (lifted cs L) (cs.map .var) = some L
  | [], L, _, _ => by simp [dropArgs, lifted_nil]
  | c :: cs, L, hnd, hhyg => by
      rw [List.map_cons, dropArgs_lifted_cons (List.nodup_cons.mp hnd).1
        (hhyg c List.mem_cons_self)]
      exact dropArgs_lifted cs L (List.nodup_cons.mp hnd).2
        (fun c' h => hhyg c' (List.mem_cons_of_mem _ h))

/-- **`run_lifted_call` is a case of dropping**: the lifted equation, called
on its captured names, drops back to the lambda. -/
theorem run_lifted_call_of_dropped (prog : S → Option (Tm S X)) (Lf : S) (cs : List (Nm X))
    (z : Nm X) (own : List X) (body a : Tm S X)
    (hprog : prog Lf = some (lifted cs (.lam z own body))) (hnd : cs.Nodup)
    (hhyg : ∀ c ∈ cs, c ∉ paramNames (.lam z own body : Tm S X))
    (n : ℕ) (hn : cs.length + 3 ≤ n) (π : Path) (σ : GStore S X) :
    run .static prog n π σ (.app (callSpine (.fn Lf) (cs.map .var)) a) =
      run .static prog n π σ (.app (.lam z own body) a) :=
  run_dropped_call prog hprog (cs.map .var) (by simp [Tm.isVal])
    (dropArgs_lifted cs _ hnd hhyg) a n (by simpa using hn) π σ

/-! ## Lift of drop -/

/-- `paramClear c owned t`: no lambda of `t` binds the parameter `c`, and no
occurrence of the parameter `c` lies under a lambda that owns the store name
`c` (`owned` records whether the context already does).  Substitutions do not
enter sealed quotations, so neither does this test. -/
def paramClear (c : Nm X) : Bool → Tm S X → Bool
  | owned, .pvar x => !(owned && decide (x = c))
  | owned, .lam x own b => decide (x ≠ c) && paramClear c (owned || ownKey own c) b
  | owned, .app f a => paramClear c owned f && paramClear c owned a
  | owned, .pquote t => paramClear c owned t
  | owned, .letP p w b => paramClear c owned p && paramClear c owned w && paramClear c owned b
  | owned, .alt t₁ t₂ => paramClear c owned t₁ && paramClear c owned t₂
  | _, _ => true

/-- **Equations of lifted shape** over the captured names `cs`: the names lead
as parameter binders that own nothing, and the body below them mentions each
captured name only as that parameter — never as a free store name, never
rebound, and never under a lambda that owns the same store name. -/
def LiftedShape (cs : List (Nm X)) (E : Tm S X) : Prop :=
  ∃ B, E = cs.foldr (fun c acc => .lam c [] acc) B ∧
    ∀ c ∈ cs, c ∉ freeNames B ∧ paramClear c false B = true

/-- Instantiate the parameters `cs`, one after the other, by the store names of
the same names: what dropping a lifted-shape equation on its captured names
does to the body. -/
def instSeq : List (Nm X) → Tm S X → Tm S X
  | [], B => B
  | c :: cs, B => instSeq cs (subst Sub.none (Sub.single c (.var c)) B)

omit [DecidableEq S] in
theorem dropArgs_foldr_lam : ∀ (cs : List (Nm X)) (B : Tm S X), cs.Nodup →
    dropArgs (cs.foldr (fun c acc => .lam c [] acc) B) (cs.map .var) = some (instSeq cs B)
  | [], B, _ => rfl
  | c :: cs, B, hnd => by
      simp only [List.foldr_cons, List.map_cons, dropArgs]
      rw [subst_single_foldr_lam _ cs _ (List.nodup_cons.mp hnd).1]
      exact dropArgs_foldr_lam cs _ (List.nodup_cons.mp hnd).2

omit [DecidableEq S] in
/-- Abstracting `c` undoes instantiating the parameter `c` by the store name
`c`, where no occurrence of the parameter sits under an owner of `c`. -/
theorem subst_absP_single_var {c : Nm X} : ∀ (B : Tm S X) (P : Nm X → Bool) (owned : Bool),
    paramClear c owned B = true → (owned = false → P c = true) →
    subst (absP P) Sub.none (subst Sub.none (Sub.single c (.var c)) B) =
      subst (absP P) Sub.none B
  | .sym _, _, _, _, _ => rfl
  | .fn _, _, _, _, _ => rfl
  | .var _, _, _, _, _ => rfl
  | .pvar x, P, owned, h, hP => by
      by_cases hx : x = c
      · subst hx
        simp only [paramClear, decide_true, Bool.and_true, Bool.not_eq_true'] at h
        have hPc := hP h
        simp [subst, Sub.single, Sub.none, absP, hPc]
      · simp [subst, Sub.single, Sub.none, hx]
  | .lam x own b, P, owned, h, hP => by
      simp only [paramClear, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨hxc, hb⟩ := h
      simp only [subst, none_hideOwn, none_hideParam, single_hideParam_ne hxc, absP_hideOwn]
      congr 1
      apply subst_absP_single_var b _ _ hb
      intro ho
      simp only [Bool.or_eq_false_iff] at ho
      simp [hP ho.1, ho.2]
  | .app f a, P, owned, h, hP => by
      simp only [paramClear, Bool.and_eq_true] at h
      simp only [subst, subst_absP_single_var f P owned h.1 hP,
        subst_absP_single_var a P owned h.2 hP]
  | .quote _, _, _, _, _ => rfl
  | .ctx _ _, _, _, _, _ => rfl
  | .pquote t, P, owned, h, hP => by
      simp only [paramClear] at h
      simp only [subst, subst_absP_single_var t P owned h hP]
  | .letP p w b, P, owned, h, hP => by
      simp only [paramClear, Bool.and_eq_true] at h
      simp only [subst, subst_absP_single_var p P owned h.1.1 hP,
        subst_absP_single_var w P owned h.1.2 hP, subst_absP_single_var b P owned h.2 hP]
  | .alt t₁ t₂, P, owned, h, hP => by
      simp only [paramClear, Bool.and_eq_true] at h
      simp only [subst, subst_absP_single_var t₁ P owned h.1 hP,
        subst_absP_single_var t₂ P owned h.2 hP]

omit [DecidableEq S] in
/-- Instantiating parameters by store names leaves the parameter test of
every other name as it was. -/
theorem paramClear_subst_var {c : Nm X} : ∀ (B : Tm S X) (φ : Sub S X) (owned : Bool),
    (∀ p, φ p = Option.none ∨ ∃ m, φ p = some (.var m)) → φ c = Option.none →
    paramClear c owned (subst Sub.none φ B) = paramClear c owned B
  | .sym _, _, _, _, _ => rfl
  | .fn _, _, _, _, _ => rfl
  | .var _, _, _, _, _ => rfl
  | .pvar x, φ, owned, hφ, hc => by
      rcases hφ x with hx | ⟨m, hx⟩
      · simp [subst, hx]
      · have hxc : x ≠ c := by
          rintro rfl
          rw [hc] at hx
          cases hx
        simp [subst, hx, paramClear, hxc]
  | .lam x own b, φ, owned, hφ, hc => by
      simp only [subst, none_hideOwn, paramClear]
      rw [paramClear_subst_var b (φ.hideParam x) _ ?_ ?_]
      · intro p
        unfold Sub.hideParam
        split
        · exact Or.inl rfl
        · exact hφ p
      · unfold Sub.hideParam
        split
        · rfl
        · exact hc
  | .app f a, φ, owned, hφ, hc => by
      simp only [subst, paramClear, paramClear_subst_var f φ owned hφ hc,
        paramClear_subst_var a φ owned hφ hc]
  | .quote _, _, _, _, _ => rfl
  | .ctx _ _, _, _, _, _ => rfl
  | .pquote t, φ, owned, hφ, hc => by
      simp only [subst, paramClear, paramClear_subst_var t φ owned hφ hc]
  | .letP p w b, φ, owned, hφ, hc => by
      simp only [subst, paramClear, paramClear_subst_var p φ owned hφ hc,
        paramClear_subst_var w φ owned hφ hc, paramClear_subst_var b φ owned hφ hc]
  | .alt t₁ t₂, φ, owned, hφ, hc => by
      simp only [subst, paramClear, paramClear_subst_var t₁ φ owned hφ hc,
        paramClear_subst_var t₂ φ owned hφ hc]

omit [DecidableEq S] in
theorem single_var_shape {c c' : Nm X} (hne : c' ≠ c) :
    (∀ p, (Sub.single c (.var c) : Sub S X) p = Option.none ∨
      ∃ m, (Sub.single c (.var c) : Sub S X) p = some (.var m)) ∧
    (Sub.single c (.var c) : Sub S X) c' = Option.none := by
  refine ⟨fun p => ?_, by simp [Sub.single, hne]⟩
  by_cases hp : p = c
  · exact Or.inr ⟨c, by simp [Sub.single, hp]⟩
  · exact Or.inl (by simp [Sub.single, hp])

omit [DecidableEq S] in
/-- Abstracting the captured names undoes their instantiation by dropping. -/
theorem subst_absP_instSeq (P : Nm X → Bool) : ∀ (cs : List (Nm X)) (B : Tm S X),
    cs.Nodup → (∀ c ∈ cs, P c = true ∧ paramClear c false B = true) →
    subst (absP P) Sub.none (instSeq cs B) = subst (absP P) Sub.none B
  | [], _, _, _ => rfl
  | c :: cs, B, hnd, h => by
      simp only [instSeq]
      have hc := h c List.mem_cons_self
      rw [subst_absP_instSeq P cs _ (List.nodup_cons.mp hnd).2 ?_]
      · exact subst_absP_single_var B P false hc.2 (fun _ => hc.1)
      · intro c' hc'
        have hne : c' ≠ c := fun e => (List.nodup_cons.mp hnd).1 (e ▸ hc')
        obtain ⟨hφ, hφc⟩ := single_var_shape (S := S) hne
        refine ⟨(h c' (List.mem_cons_of_mem _ hc')).1, ?_⟩
        rw [paramClear_subst_var B _ false hφ hφc]
        exact (h c' (List.mem_cons_of_mem _ hc')).2

omit [DecidableEq S] in
/-- Abstraction changes nothing in a term none of whose free store names it
selects. -/
theorem subst_absP_eq_self : ∀ (B : Tm S X) (P : Nm X → Bool),
    (∀ n ∈ freeNames B, P n = false) → subst (absP P) Sub.none B = B
  | .sym _, _, _ => rfl
  | .fn _, _, _ => rfl
  | .var n, P, h => by
      have hn := h n (by simp [freeNames])
      simp [subst, absP, hn]
  | .pvar _, _, _ => rfl
  | .lam x own b, P, h => by
      simp only [subst, absP_hideOwn, none_hideParam]
      congr 1
      apply subst_absP_eq_self b
      intro n hn
      by_cases ho : ownKey own n
      · simp [ho]
      · have := h n (by simp [freeNames, hn, ho])
        simp [this]
  | .app f a, P, h => by
      simp only [freeNames, List.mem_append] at h
      simp only [subst, subst_absP_eq_self f P (fun n hn => h n (Or.inl hn)),
        subst_absP_eq_self a P (fun n hn => h n (Or.inr hn))]
  | .quote _, _, _ => rfl
  | .ctx _ _, _, _ => rfl
  | .pquote c, P, h => by
      simp only [freeNames] at h
      simp only [subst, subst_absP_eq_self c P h]
  | .letP p w b, P, h => by
      simp only [freeNames, List.mem_append] at h
      simp only [subst, subst_absP_eq_self p P (fun n hn => h n (Or.inl (Or.inl hn))),
        subst_absP_eq_self w P (fun n hn => h n (Or.inl (Or.inr hn))),
        subst_absP_eq_self b P (fun n hn => h n (Or.inr hn))]
  | .alt t₁ t₂, P, h => by
      simp only [freeNames, List.mem_append] at h
      simp only [subst, subst_absP_eq_self t₁ P (fun n hn => h n (Or.inl hn)),
        subst_absP_eq_self t₂ P (fun n hn => h n (Or.inr hn))]

omit [DecidableEq S] in
/-- **Lift of drop is the original equation**, for equations of lifted shape:
drop the equation on its captured names, lift the lambda over the same names,
and the equation comes back. -/
theorem lifted_dropArgs {cs : List (Nm X)} (hnd : cs.Nodup) {E : Tm S X}
    (hE : LiftedShape cs E) :
    ∃ L, dropArgs E (cs.map .var) = some L ∧ lifted cs L = E := by
  obtain ⟨B, rfl, hB⟩ := hE
  refine ⟨instSeq cs B, dropArgs_foldr_lam cs B hnd, ?_⟩
  unfold lifted
  congr 1
  rw [subst_absP_instSeq _ cs B hnd (fun c hc => ⟨by simp [hc], (hB c hc).2⟩)]
  apply subst_absP_eq_self
  intro n hn
  simp only [decide_eq_false_iff_not]
  intro hncs
  exact (hB n hncs).1 hn

/-! ## The bijection -/

omit [DecidableEq S] in
/-- Instantiating parameters by store names introduces no parameter name. -/
theorem paramNames_subst_var : ∀ (B : Tm S X) (φ : Sub S X),
    (∀ p, φ p = Option.none ∨ ∃ m, φ p = some (.var m)) →
    ∀ q ∈ paramNames (subst Sub.none φ B), q ∈ paramNames B
  | .sym _, _, _, _, h | .fn _, _, _, _, h | .var _, _, _, _, h | .quote _, _, _, _, h
  | .ctx _ _, _, _, _, h => by
      simp [subst, paramNames, Sub.none] at h
  | .pvar x, φ, hφ, q, h => by
      rcases hφ x with hx | ⟨m, hx⟩
      · simpa [subst, hx] using h
      · simp [subst, hx, paramNames] at h
  | .lam x own b, φ, hφ, q, h => by
      simp only [subst, none_hideOwn, paramNames, List.mem_cons] at h ⊢
      rcases h with h | h
      · exact Or.inl h
      · refine Or.inr (paramNames_subst_var b (φ.hideParam x) ?_ q h)
        intro p
        unfold Sub.hideParam
        split
        · exact Or.inl rfl
        · exact hφ p
  | .app f a, φ, hφ, q, h => by
      simp only [subst, paramNames, List.mem_append] at h ⊢
      rcases h with h | h
      · exact Or.inl (paramNames_subst_var f φ hφ q h)
      · exact Or.inr (paramNames_subst_var a φ hφ q h)
  | .pquote t, φ, hφ, q, h => by
      simp only [subst, paramNames] at h ⊢
      exact paramNames_subst_var t φ hφ q h
  | .letP p w b, φ, hφ, q, h => by
      simp only [subst, paramNames, List.mem_append] at h ⊢
      rcases h with (h | h) | h
      · exact Or.inl (Or.inl (paramNames_subst_var p φ hφ q h))
      · exact Or.inl (Or.inr (paramNames_subst_var w φ hφ q h))
      · exact Or.inr (paramNames_subst_var b φ hφ q h)
  | .alt t₁ t₂, φ, hφ, q, h => by
      simp only [subst, paramNames, List.mem_append] at h ⊢
      rcases h with h | h
      · exact Or.inl (paramNames_subst_var t₁ φ hφ q h)
      · exact Or.inr (paramNames_subst_var t₂ φ hφ q h)

omit [DecidableEq S] in
/-- Where no lambda rebinds the parameter `c`, instantiating it by the store
name `c` removes it from the parameter names. -/
theorem not_mem_paramNames_single_var {c : Nm X} : ∀ (B : Tm S X) (owned : Bool),
    paramClear c owned B = true →
    c ∉ paramNames (subst Sub.none (Sub.single c (.var c)) B)
  | .sym _, _, _ | .fn _, _, _ | .var _, _, _ | .quote _, _, _ | .ctx _ _, _, _ => by
      simp [subst, paramNames, Sub.none]
  | .pvar x, _, _ => by
      by_cases hx : x = c
      · subst hx
        simp [subst, Sub.single, paramNames]
      · simp [subst, Sub.single, hx, paramNames, Ne.symm hx]
  | .lam x own b, owned, h => by
      simp only [paramClear, Bool.and_eq_true, decide_eq_true_eq] at h
      simp only [subst, none_hideOwn, single_hideParam_ne h.1, paramNames, List.mem_cons,
        not_or]
      exact ⟨Ne.symm h.1, not_mem_paramNames_single_var b _ h.2⟩
  | .app f a, owned, h => by
      simp only [paramClear, Bool.and_eq_true] at h
      simp only [subst, paramNames, List.mem_append, not_or]
      exact ⟨not_mem_paramNames_single_var f owned h.1,
        not_mem_paramNames_single_var a owned h.2⟩
  | .pquote t, owned, h => by
      simp only [paramClear] at h
      simp only [subst, paramNames]
      exact not_mem_paramNames_single_var t owned h
  | .letP p w b, owned, h => by
      simp only [paramClear, Bool.and_eq_true] at h
      simp only [subst, paramNames, List.mem_append, not_or]
      exact ⟨⟨not_mem_paramNames_single_var p owned h.1.1,
        not_mem_paramNames_single_var w owned h.1.2⟩,
        not_mem_paramNames_single_var b owned h.2⟩
  | .alt t₁ t₂, owned, h => by
      simp only [paramClear, Bool.and_eq_true] at h
      simp only [subst, paramNames, List.mem_append, not_or]
      exact ⟨not_mem_paramNames_single_var t₁ owned h.1,
        not_mem_paramNames_single_var t₂ owned h.2⟩

omit [DecidableEq S] in
/-- Later instantiations introduce no parameter names. -/
theorem instSeq_paramNames_sub : ∀ (cs : List (Nm X)) (B : Tm S X),
    ∀ q ∈ paramNames (instSeq cs B), q ∈ paramNames B
  | [], _, _, h => h
  | c :: cs, B, q, h => by
      simp only [instSeq] at h
      refine paramNames_subst_var B _ ?_ q (instSeq_paramNames_sub cs _ q h)
      intro p
      by_cases hp : p = c
      · exact Or.inr ⟨c, by simp [Sub.single, hp]⟩
      · exact Or.inl (by simp [Sub.single, hp])

omit [DecidableEq S] in
/-- The lambda dropped from a lifted-shape equation is hygienic for its
captured names. -/
theorem instSeq_hygienic : ∀ (cs : List (Nm X)) (B : Tm S X), cs.Nodup →
    (∀ c ∈ cs, paramClear c false B = true) → ∀ c ∈ cs, c ∉ paramNames (instSeq cs B)
  | [], _, _, _, c, hc => by cases hc
  | c :: cs, B, hnd, h, c', hc' => by
      simp only [instSeq]
      have hcs : ∀ d ∈ cs,
          paramClear d false (subst Sub.none (Sub.single c (.var c)) B) = true := by
        intro d hd
        have hne : d ≠ c := fun e => (List.nodup_cons.mp hnd).1 (e ▸ hd)
        obtain ⟨hφ, hφd⟩ := single_var_shape (S := S) hne
        rw [paramClear_subst_var B _ false hφ hφd]
        exact h d (List.mem_cons_of_mem _ hd)
      by_cases hcc : c' = c
      · subst hcc
        intro hm
        exact not_mem_paramNames_single_var B false (h _ List.mem_cons_self)
          (instSeq_paramNames_sub cs _ _ hm)
      · have hc'' : c' ∈ cs := by
          rcases List.mem_cons.mp hc' with e | e
          · exact absurd e hcc
          · exact e
        exact instSeq_hygienic cs _ (List.nodup_cons.mp hnd).2 hcs c' hc''

omit [DecidableEq S] in
/-- Abstraction creates a parameter occurrence only where no lambda owns the
name, and creates no binder. -/
theorem paramClear_subst_absP {c : Nm X} : ∀ (L : Tm S X) (P : Nm X → Bool) (owned : Bool),
    c ∉ paramNames L → (owned = true → P c = false) →
    paramClear c owned (subst (absP P) Sub.none L) = true
  | .sym _, _, _, _, _ | .fn _, _, _, _, _ | .quote _, _, _, _, _ | .ctx _ _, _, _, _, _ => rfl
  | .var n, P, owned, _, hP => by
      by_cases hp : P n
      · by_cases hn : n = c
        · subst hn
          cases owned
          · simp [subst, absP, hp, paramClear]
          · exact absurd (hP rfl) (by simp [hp])
        · simp [subst, absP, hp, paramClear, hn]
      · simp [subst, absP, hp, paramClear]
  | .pvar x, P, owned, hL, _ => by
      have hx : x ≠ c := by
        intro e
        apply hL
        simp [paramNames, e]
      simp [subst, Sub.none, paramClear, hx]
  | .lam x own b, P, owned, hL, hP => by
      simp only [paramNames, List.mem_cons, not_or] at hL
      simp only [subst, absP_hideOwn, none_hideParam, paramClear, Bool.and_eq_true,
        decide_eq_true_eq]
      refine ⟨Ne.symm hL.1, paramClear_subst_absP b _ _ hL.2 ?_⟩
      intro ho
      by_cases hk : ownKey own c
      · simp [hk]
      · simp only [hk, Bool.or_false] at ho
        simp [hP ho]
  | .app f a, P, owned, hL, hP => by
      simp only [paramNames, List.mem_append, not_or] at hL
      simp only [subst, paramClear, Bool.and_eq_true]
      exact ⟨paramClear_subst_absP f P owned hL.1 hP, paramClear_subst_absP a P owned hL.2 hP⟩
  | .pquote t, P, owned, hL, hP => by
      simp only [paramNames] at hL
      simp only [subst, paramClear]
      exact paramClear_subst_absP t P owned hL hP
  | .letP p w b, P, owned, hL, hP => by
      simp only [paramNames, List.mem_append, not_or] at hL
      simp only [subst, paramClear, Bool.and_eq_true]
      exact ⟨⟨paramClear_subst_absP p P owned hL.1.1 hP,
        paramClear_subst_absP w P owned hL.1.2 hP⟩, paramClear_subst_absP b P owned hL.2 hP⟩
  | .alt t₁ t₂, P, owned, hL, hP => by
      simp only [paramNames, List.mem_append, not_or] at hL
      simp only [subst, paramClear, Bool.and_eq_true]
      exact ⟨paramClear_subst_absP t₁ P owned hL.1 hP, paramClear_subst_absP t₂ P owned hL.2 hP⟩

omit [DecidableEq S] in
/-- **Lifting and dropping are inverse bijections.**  The equations of lifted
shape over `cs` are exactly the lifted equations of the lambdas that are
hygienic for `cs`; dropping on the captured names inverts lifting on both
sides (`dropArgs_lifted`, `lifted_dropArgs`). -/
theorem liftedShape_iff {cs : List (Nm X)} (hnd : cs.Nodup) (E : Tm S X) :
    LiftedShape cs E ↔ ∃ L, (∀ c ∈ cs, c ∉ paramNames L) ∧ lifted cs L = E := by
  constructor
  · intro hE
    obtain ⟨L, hdrop, hlift⟩ := lifted_dropArgs hnd hE
    obtain ⟨B, rfl, hB⟩ := hE
    rw [dropArgs_foldr_lam cs B hnd, Option.some.injEq] at hdrop
    subst hdrop
    exact ⟨instSeq cs B, instSeq_hygienic cs B hnd (fun c hc => (hB c hc).2), hlift⟩
  · rintro ⟨L, hL, rfl⟩
    refine ⟨subst (absP fun n => decide (n ∈ cs)) Sub.none L, rfl, fun c hc => ⟨?_, ?_⟩⟩
    · rw [freeNames_subst_absP]
      simp [hc]
    · exact paramClear_subst_absP L _ false (hL c hc) (by simp)

end Mettapedia.GSLT.LanguageDef.TemplateScope

/-! ## Examples on the corpus -/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope.Corpus

open Mettapedia.GSLT.LanguageDef.TemplateScope

/-- The call spine of row B4's lifted equation: `(Lf $y)`. -/
def spineB4 : T := callSpine (.fn .Lf) [sv .y]

/-- **Positive.**  Dropping B4's lifted equation `(= (Lf $y $z) …)` on its
call spine gives back `L` as elaborated in B4; lifting that lambda again gives
back the equation, and the spine and the dropped lambda answer alike. -/
theorem drop_B4 :
    dropCall progLf spineB4 = some L_B4 ∧
    progLf .Lf = some (lifted [.src .y] L_B4) ∧
    answers .static progLf 40 (.app spineB4 (k .n1)) =
      answers .static progLf 40 (.app L_B4 (k .n1)) ∧
    answers .static progLf 40 (.app L_B4 (k .n1)) = some [ap (k .g) (k .n1)] := by
  decide

/-- An equation that uses its captured name both as the parameter and as a
store name: `(= (E $y) (lam z (Pair y $y)))`, with `y` the parameter. -/
def notLifted : T := .lam (.src .y) [] (lm .z (pair (pv .y) (sv .y)))

/-- **Negative: not of lifted shape.**  Dropping on `$y` merges the parameter
with the store name, and lifting the result abstracts both: the round trip
does not return the equation. -/
theorem notLifted_round_trip :
    dropArgs notLifted [sv .y] = some (lm .z (pair (sv .y) (sv .y))) ∧
    lifted [.src .y] (lm .z (pair (sv .y) (sv .y))) ≠ notLifted ∧
    ¬ LiftedShape [Nm.src Sp.y] notLifted := by
  refine ⟨by decide, by decide, ?_⟩
  rintro ⟨B, hE, hB⟩
  simp only [List.foldr_cons, List.foldr_nil, notLifted, Tm.lam.injEq] at hE
  obtain ⟨-, -, rfl⟩ := hE
  exact (hB (.src .y) List.mem_cons_self).1 (by decide)

/-- An equation whose parameter is used twice: `(= (Dup $c $z) (Pair $c $c))`. -/
def progDup : Sy → Option T := fun s =>
  if s = .Lf then some (.lam (.src .r) [] (lm .z (pair (pv .r) (pv .r)))) else none

/-- **Negative: dropping needs value arguments.**  The call evaluates the
choice `(superpose (1 2))` once and shares it; dropping substitutes the
unevaluated choice twice, and the bag grows from two answers to four. -/
theorem drop_needs_values :
    answers .static progDup 40 (.app (callSpine (.fn .Lf) [.alt (k .n1) (k .n2)]) (k .n3)) =
      some [pair (k .n1) (k .n1), pair (k .n2) (k .n2)] ∧
    dropCall progDup (callSpine (.fn .Lf) [.alt (k .n1) (k .n2)]) =
      some (lm .z (pair (.alt (k .n1) (k .n2)) (.alt (k .n1) (k .n2)))) ∧
    answers .static progDup 40
        (.app (lm .z (pair (.alt (k .n1) (k .n2)) (.alt (k .n1) (k .n2)))) (k .n3)) =
      some [pair (k .n1) (k .n1), pair (k .n1) (k .n2), pair (k .n2) (k .n1),
        pair (k .n2) (k .n2)] := by
  decide

end Mettapedia.GSLT.LanguageDef.TemplateScope.Corpus
