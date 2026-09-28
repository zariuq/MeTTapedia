import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.CallAbstraction
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ScrutineeFirstDefinition

/-!
# The kernel's check of a recursive right-hand side gives the recursive hypotheses

A definition by structural recursion is admitted by checking each right-hand
side with the defined constant `f` declared and not computing: its recursive
calls are `f x̄ v`, on the prefix variables and a recursive field `v`. The
semantic theorem (`DeclaresRecursion`) takes the right-hand side with each
call replaced by its recursive hypothesis: a variable of the type the call
has, generalized over the arguments after the scrutinee.

The hypothesis substitution `hypSub` is a call substitution, and the hypothesis
context and the pattern context are its contexts. So the kernel's check of the
right-hand side with `f` is the kernel's check of the abstracted right-hand
side in the hypothesis context, without `f` (`CheckingAlgorithm.reflect`), and
that check is sound for the rule package without `f` given the facts about the
weak-head forms of its types (`CheckingAlgorithm.sound`): it gives the premise
`DeclaresRecursion.bodyTyped`.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open TelescopeAbstraction (closeType applyClosed)

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L]

/-! ## The type a declared telescope type assigns after its arguments -/

theorem peel_snoc {n : Nat} {a : Tm Head n} :
    ∀ {as : List (Tm Head n)} {T D : Tm Head n} {B : Tm Head (n + 1)}, Peels T as →
      peel T as = .pi D B → Peels T (as ++ [a]) ∧ peel T (as ++ [a]) = inst0 a B := by
  intro as
  induction as with
  | nil =>
      intro T D B _ e
      simp only [peel] at e
      subst e
      exact ⟨trivial, rfl⟩
  | cons b as ih =>
      intro T D B p e
      cases T <;> simp only [Peels] at p
      case pi D₀ B₀ => exact ih p e

/-- A closed telescope type, instantiated at the arguments of a substitution
of its telescope, is the substituted body. -/
theorem peel_closeType {m : Nat} :
    ∀ {j : Nat} (Θ : Ctx Head j) (X : Tm Head j) (σ : Sub Head j m),
      Peels (liftClosed (closeType Θ X)) (telescopeArgs Θ σ) ∧
        peel (liftClosed (closeType Θ X)) (telescopeArgs Θ σ) = Presentation.subst σ X
  | _, .nil, X, σ => ⟨trivial, (subst_closed σ X).symm⟩
  | _, .snoc Θ D, X, σ => by
      obtain ⟨p, e⟩ := peel_closeType Θ (.pi D X) (tailSub σ)
      obtain ⟨p', e'⟩ := peel_snoc (a := σ 0) p e
      refine ⟨p', ?_⟩
      show peel (liftClosed (closeType Θ (.pi D X))) (telescopeArgs Θ (tailSub σ) ++ [σ 0]) = _
      rw [e', inst0_subst_liftSub, consSub_eta]

/-- The arguments of a substitution by variables are variables. -/
theorem telescopeArgs_vars {m : Nat} :
    ∀ {j : Nat} (Θ : Ctx Head j) (σ : Sub Head j m), (∀ i, ∃ x, σ i = .var x) →
      ∃ xs : List (Fin m), telescopeArgs Θ σ = xs.map .var
  | _, .nil, _, _ => ⟨[], rfl⟩
  | _, .snoc Θ _, σ, vars => by
      obtain ⟨xs, e⟩ := telescopeArgs_vars Θ (tailSub σ) (fun i => vars i.succ)
      obtain ⟨x, hx⟩ := vars 0
      refine ⟨xs ++ [x], ?_⟩
      show telescopeArgs Θ (tailSub σ) ++ [σ 0] = _
      rw [List.map_append, List.map_singleton, ← e, hx]

/-! ## Recursive calls are calls -/

section Calls

variable (f : DeclName) (e : (i : Nat) → Tm Head i) (s a d : Nat)

theorem callSub_vars {l : Nat} (hl : l < a) : ∀ i, ∃ x, callSub (Head := Head) s a d l i = .var x := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · refine ⟨⟨d + (a - 1 - l), by omega⟩, ?_⟩
    show (if h : l < a then _ else _) = _
    rw [dif_pos hl]
  · exact ⟨_, rfl⟩

/-- A recursive call on a field is a call of `f` on `s + 1` variables, and its
type is the type the declared type assigns after them. -/
theorem recCall_call {l : Nat} (hl : l < a) (C : Tm Head (s + 1 + d)) :
    ∃ xs : List (Fin (s + a + d)), xs.length = s + 1 ∧
      recCall f e s a d l = appSpine (.const f) (xs.map .var) ∧
      Peels (liftClosed (closeType (ofEntries e (s + 1 + d)) C)) (xs.map .var) ∧
      recCallType e s a d l C = peel (liftClosed (closeType (ofEntries e (s + 1 + d)) C)) (xs.map .var) := by
  obtain ⟨xs, hxs⟩ := telescopeArgs_vars (ofEntries e (s + 1)) (callSub s a d l) (callSub_vars s a d hl)
  have hlen : xs.length = s + 1 := by
    have := telescopeArgs_length (ofEntries e (s + 1)) (callSub (Head := Head) s a d l)
    rw [hxs, List.length_map] at this
    exact this
  obtain ⟨p, ep⟩ := peel_closeType (ofEntries e (s + 1)) (piRange e (s + 1) d C) (callSub s a d l)
  rw [← closeType_ofEntries_add, hxs] at p ep
  refine ⟨xs, hlen, ?_, p, ep.symm⟩
  rw [recCall, applyClosed_eq_appSpine, hxs]

/-- A recursive call on a field is a call of `f` on `s + 1` variables. -/
theorem recCall_isCall {l : Nat} (hl : l < a) :
    ∃ xs : List (Fin (s + a + d)), xs.length = s + 1 ∧
      recCall f e s a d l = appSpine (.const f) (xs.map .var) := by
  obtain ⟨xs, hxs⟩ := telescopeArgs_vars (ofEntries e (s + 1)) (callSub s a d l) (callSub_vars s a d hl)
  have hlen : xs.length = s + 1 := by
    have := telescopeArgs_length (ofEntries e (s + 1)) (callSub (Head := Head) s a d l)
    rw [hxs, List.length_map] at this
    exact this
  exact ⟨xs, hlen, by rw [recCall, applyClosed_eq_appSpine, hxs]⟩

/-- Recursive calls on distinct fields are distinct. -/
theorem recCall_injective {l l' : Nat} (hl : l < a) (hl' : l' < a)
    (same : recCall (Head := Head) f e s a d l = recCall f e s a d l') : l = l' := by
  rw [recCall, recCall, applyClosed_eq_appSpine, applyClosed_eq_appSpine] at same
  have args := (appSpine_const_injective same).2
  have last := congrArg List.getLast? args
  simp only [telescopeArgs_ofEntries_succ, List.getLast?_append, List.getLast?_singleton,
    Option.some_or] at last
  have v := Option.some.inj last
  simp only [callSub, consSub, Fin.cases_zero, dif_pos hl, dif_pos hl', Tm.var.injEq,
    Fin.mk.injEq] at v
  omega

end Calls

/-- The recursive positions of a constructor's fields are distinct. -/
theorem recPositions_nodup : ∀ (fields : List (Field Head)), (recPositions fields).Nodup
  | [] => List.nodup_nil
  | .recursive :: fields => by
      simp only [recPositions]
      refine List.nodup_cons.mpr ⟨by simp, ?_⟩
      exact (recPositions_nodup fields).map (fun _ _ h => Nat.succ.inj h)
  | .closed _ :: fields => by
      simp only [recPositions]
      exact (recPositions_nodup fields).map (fun _ _ h => Nat.succ.inj h)

/-! ## Lookups of an extended context under an extended substitution -/

theorem subst_lookup_extendEntries {n : Nat} (Γ : Ctx Head n) (entry : (j : Nat) → Tm Head (n + j))
    (values : Nat → Tm Head n) :
    ∀ (r : Nat) (i : Fin (n + r)),
      Presentation.subst (extendSub ids values r) (Ctx.lookup (extendEntries Γ entry r) i) =
        if h : i.val < r then
          (fun q => Presentation.subst (extendSub ids values q) (entry q)) (r - 1 - i.val)
        else Ctx.lookup Γ ⟨i.val - r, by have := i.isLt; omega⟩
  | 0, i => by
      rw [dif_neg (Nat.not_lt_zero _)]
      show Presentation.subst ids (Ctx.lookup Γ i) = _
      rw [subst_ids]
      exact congrArg _ (Fin.ext rfl)
  | r + 1, ⟨0, h⟩ => by
      rw [dif_pos (Nat.succ_pos r)]
      show Presentation.subst (consSub (values r) (extendSub ids values r))
        (Presentation.rename wk (entry r)) = _
      rw [subst_consSub_rename_wk]
      rfl
  | r + 1, ⟨i + 1, h⟩ => by
      show Presentation.subst (consSub (values r) (extendSub ids values r))
        (Presentation.rename wk (Ctx.lookup (extendEntries Γ entry r) ⟨i, by omega⟩)) = _
      rw [subst_consSub_rename_wk, subst_lookup_extendEntries Γ entry values r ⟨i, by omega⟩]
      by_cases hi : i < r
      · rw [dif_pos hi, dif_pos (by omega : i + 1 < r + 1)]
        exact congrArg (fun q => Presentation.subst (extendSub ids values q) (entry q))
          (show r - 1 - i = r + 1 - 1 - (i + 1) by omega)
      · rw [dif_neg hi, dif_neg (by omega : ¬ i + 1 < r + 1)]
        exact congrArg _ (Fin.ext (show i - r = i + 1 - (r + 1) by omega))


/-! ## Contexts without the constant -/

/-- No entry of the context mentions `f`. -/
def CtxConstFree (f : DeclName) : {n : Nat} → Ctx Head n → Prop
  | _, .nil => True
  | _, .snoc Γ A => CtxConstFree f Γ ∧ ConstFree f A

section Free

variable {f : DeclName}

theorem CtxConstFree.lookup : ∀ {n : Nat} {Γ : Ctx Head n}, CtxConstFree f Γ →
    ∀ i, ConstFree f (Ctx.lookup Γ i)
  | _, .nil, _, i => Fin.elim0 i
  | _, .snoc Γ A, h, i => by
      have h' : CtxConstFree f Γ ∧ ConstFree f A := h
      obtain ⟨hΓ, hA⟩ := h'
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hA.rename wk
      · exact (CtxConstFree.lookup hΓ j).rename wk

theorem CtxConstFree.extend {n : Nat} {Γ : Ctx Head n} (hΓ : CtxConstFree f Γ)
    {entry : (j : Nat) → Tm Head (n + j)} :
    ∀ (r : Nat), (∀ j, j < r → ConstFree f (entry j)) → CtxConstFree f (extendEntries Γ entry r)
  | 0, _ => hΓ
  | r + 1, free => by
      show CtxConstFree f (extendEntries Γ entry r) ∧ ConstFree f (entry r)
      exact ⟨CtxConstFree.extend hΓ r (fun j hj => free j (by omega)), free r (by omega)⟩

theorem CtxConstFree.of_entries {e : (i : Nat) → Tm Head i} (free : ∀ i, ConstFree f (e i)) :
    ∀ n, CtxConstFree f (Normalization.ofEntries e n)
  | 0 => trivial
  | n + 1 => by
      show CtxConstFree f (Normalization.ofEntries e n) ∧ ConstFree f (e n)
      exact ⟨CtxConstFree.of_entries free n, free n⟩

theorem constFree_const {n : Nat} {c : DeclName} : ConstFree f (.const c : Tm Head n) ↔ c ≠ f :=
  Iff.rfl

theorem fieldVars_vars (s : Nat) :
    ∀ (a : Nat) (t : Tm Head (s + a)), t ∈ fieldVars s a → ∃ x, t = .var x
  | 0, _, h => absurd h (by simp [fieldVars])
  | a + 1, t, h => by
      simp only [fieldVars, List.mem_append, List.mem_map, List.mem_singleton] at h
      rcases h with ⟨t', ht', rfl⟩ | rfl
      · obtain ⟨x, rfl⟩ := fieldVars_vars s a t' ht'
        exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩

theorem ConstFree.appSpine {n : Nat} {g : Tm Head n} (hg : ConstFree f g) :
    ∀ {as : List (Tm Head n)}, (∀ a ∈ as, ConstFree f a) → ConstFree f (appSpine g as) := by
  intro as
  induction as using List.reverseRecOn with
  | nil => intro _; exact hg
  | append_singleton init a ih =>
      intro h
      rw [appSpine_concat]
      exact ⟨ih (fun b hb => h b (List.mem_append_left _ hb)), h a (by simp)⟩

theorem ConstFree.liftSubN {n m : Nat} {σ : Sub Head n m} (hσ : ∀ i, ConstFree f (σ i)) :
    ∀ (j : Nat) (i : Fin (n + j)), ConstFree f (liftSubN σ j i)
  | 0, i => hσ i
  | j + 1, i => by
      refine Fin.cases ?_ (fun i' => ?_) i
      · trivial
      · exact (ConstFree.liftSubN hσ j i').rename wk

theorem ConstFree.piRange {e : (i : Nat) → Tm Head i} (free : ∀ i, ConstFree f (e i)) (j : Nat) :
    ∀ (d : Nat) {C : Tm Head (j + d)}, ConstFree f C → ConstFree f (piRange e j d C)
  | 0, _, hC => hC
  | d + 1, _, hC => ConstFree.piRange free j d ⟨free _, hC⟩

theorem patSub_constFree {s a : Nat} {k : DeclName} (hk : k ≠ f) :
    ∀ i, ConstFree f (patSub (Head := Head) s a k i) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · refine ConstFree.appSpine (constFree_const.mpr hk) ?_
    intro t ht
    obtain ⟨x, rfl⟩ := fieldVars_vars s a t ht
    trivial
  · trivial

/-- The hypothesis context mentions `f` nowhere when the telescope, the fields,
the constructor and the result type do not. -/
theorem CtxConstFree.of_hypCtx {T k : DeclName} {e : (i : Nat) → Tm Head i} {s d : Nat}
    {fields : List (Field Head)} {C : Tm Head (s + 1 + d)} (freeE : ∀ i, ConstFree f (e i))
    (freeFields : ∀ l, ConstFree f ((fields.getD l .recursive).type T)) (hk : k ≠ f)
    (freeC : ConstFree f C) : CtxConstFree f (hypCtx T k e s d fields C) := by
  have patSubFree := patSub_constFree (Head := Head) (s := s) (a := fields.length) hk
  refine CtxConstFree.extend (CtxConstFree.extend (CtxConstFree.extend
    (CtxConstFree.of_entries freeE s) _ (fun l _ => (freeFields l).liftClosed)) _
    (fun j _ => (freeE _).subst (ConstFree.liftSubN patSubFree j))) _ (fun j hj => ?_)
  refine ConstFree.rename ?_ _
  refine (ConstFree.piRange freeE (s + 1) d freeC).subst fun i => ?_
  refine Fin.cases ?_ (fun i' => ?_) i
  · have hl : (recPositions fields).getD j 0 < fields.length := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
      exact (recPositions_spec fields j hj).1
    show ConstFree f (if h : _ < fields.length then _ else _)
    rw [dif_pos hl]
    trivial
  · trivial

end Free


/-! ## The hypothesis substitution is a call substitution -/

section Hypotheses

variable (f : DeclName) {T k : DeclName} (e : (i : Nat) → Tm Head i) (s d : Nat)
  (fields : List (Field Head)) (C : Tm Head (s + 1 + d))

/-- At a hypothesis, the hypothesis substitution is the recursive call on its
field. -/
theorem hypSub_at_hyp (i : Fin (s + fields.length + d + (recPositions fields).length))
    (hi : i.val < (recPositions fields).length) :
    ∃ l, l < fields.length ∧ hypSub f e s d fields i = recCall f e s fields.length d l ∧
      l = (recPositions fields).getD ((recPositions fields).length - 1 - i.val) 0 :=
  ⟨_, recPosition_lt fields ⟨i.val, hi⟩, hypSub_hyp f e s d fields ⟨i.val, hi⟩, rfl⟩

/-- Past the hypotheses, the hypothesis substitution is the pattern variable. -/
theorem hypSub_at_pattern (i : Fin (s + fields.length + d + (recPositions fields).length))
    (hi : ¬ i.val < (recPositions fields).length) :
    hypSub f e s d fields i = .var ⟨i.val - (recPositions fields).length, by omega⟩ := by
  have e' : i = wkN (recPositions fields).length
      ⟨i.val - (recPositions fields).length, by omega⟩ := Fin.ext (by simp [wkN]; omega)
  conv_lhs => rw [e']
  exact hypSub_pattern f e s d fields _

theorem hypSub_callSub : CallSub f (s + 1) (hypSub (Head := Head) f e s d fields) where
  pos := Nat.succ_pos s
  shape := by
    intro i
    by_cases hi : i.val < (recPositions fields).length
    · obtain ⟨l, hl, h, _⟩ := hypSub_at_hyp f e s d fields i hi
      obtain ⟨xs, hlen, hcall⟩ := recCall_isCall f e s fields.length d hl
      exact .inr ⟨xs, hlen, h.trans hcall⟩
    · exact .inl ⟨_, hypSub_at_pattern f e s d fields i hi⟩
  injective := by
    intro i i' h
    by_cases hi : i.val < (recPositions fields).length <;>
      by_cases hi' : i'.val < (recPositions fields).length
    · obtain ⟨l, hl, h₁, rfl⟩ := hypSub_at_hyp f e s d fields i hi
      obtain ⟨l', hl', h₂, rfl⟩ := hypSub_at_hyp f e s d fields i' hi'
      have same := recCall_injective f e s fields.length d hl hl' (h₁.symm.trans (h.trans h₂))
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some] at same
      have := (recPositions_nodup fields).getElem_inj_iff.mp same
      exact Fin.ext (by omega)
    · exfalso
      obtain ⟨l, hl, h₁, _⟩ := hypSub_at_hyp f e s d fields i hi
      obtain ⟨xs, _, hcall⟩ := recCall_isCall f e s fields.length d hl
      rw [h₁, hcall, hypSub_at_pattern f e s d fields i' hi'] at h
      exact appSpine_const_ne_var h
    · exfalso
      obtain ⟨l, hl, h₁, _⟩ := hypSub_at_hyp f e s d fields i' hi'
      obtain ⟨xs, _, hcall⟩ := recCall_isCall f e s fields.length d hl
      rw [h₁, hcall, hypSub_at_pattern f e s d fields i hi] at h
      exact appSpine_const_ne_var h.symm
    · rw [hypSub_at_pattern f e s d fields i hi, hypSub_at_pattern f e s d fields i' hi'] at h
      have := congrArg Fin.val (Tm.var.inj h)
      exact Fin.ext (by simp at this; omega)

/-- The hypothesis context and the pattern context are the contexts of the
hypothesis substitution, for `f` declared at its telescope type. -/
theorem hypSub_callContexts {R : Rules Head} (freeCtx : CtxConstFree f (hypCtx T k e s d fields C)) :
    CallContexts R f (s + 1) (closeType (ofEntries e (s + 1 + d)) C) (hypSub f e s d fields)
      (hypCtx T k e s d fields C) (patternCtx T k e s d fields) where
  sub := hypSub_callSub f e s d fields
  var := by
    intro i j h
    have lookup := subst_lookup_extendEntries (patternCtx T k e s d fields)
      (fun j => Presentation.rename (wkN j)
        (recCallType e s fields.length d ((recPositions fields).getD j 0) C))
      (fun j => recCall f e s fields.length d ((recPositions fields).getD j 0))
      (recPositions fields).length i
    by_cases hi : i.val < (recPositions fields).length
    · exfalso
      obtain ⟨l, hl, h₁, _⟩ := hypSub_at_hyp f e s d fields i hi
      obtain ⟨xs, _, hcall, _, _⟩ := recCall_call f e s fields.length d hl C
      rw [h₁, hcall] at h
      exact appSpine_const_ne_var h
    · rw [dif_neg hi] at lookup
      rw [hypSub_at_pattern f e s d fields i hi] at h
      cases h
      exact Reduces.of_eq lookup
  call := by
    intro i xs h
    by_cases hi : i.val < (recPositions fields).length
    · obtain ⟨l, hl, h₁, hl₁⟩ := hypSub_at_hyp f e s d fields i hi
      obtain ⟨ys, _, hcall, peels, htype⟩ := recCall_call f e s fields.length d hl C
      rw [h₁, hcall] at h
      have hxy : ys.map Tm.var = xs.map Tm.var := (appSpine_const_injective h).2
      rw [← hxy]
      refine ⟨peels, ?_⟩
      have lookup := subst_lookup_extendEntries (patternCtx T k e s d fields)
        (fun j => Presentation.rename (wkN j)
          (recCallType e s fields.length d ((recPositions fields).getD j 0) C))
        (fun j => recCall f e s fields.length d ((recPositions fields).getD j 0))
        (recPositions fields).length i
      rw [dif_pos hi] at lookup
      refine lookup.trans ?_
      show Presentation.subst (extendSub ids _ _) (Presentation.rename (wkN _) _) = _
      rw [subst_extendSub_wkN, subst_ids, ← hl₁, htype]
    · exfalso
      rw [hypSub_at_pattern f e s d fields i hi] at h
      exact appSpine_const_ne_var h.symm
  free := freeCtx.lookup

end Hypotheses

/-! ## The bridge to the recursion's semantic theorem -/

section Bridge

variable {S₀ : Setting Head L} (facts : FormFacts S₀.R S₀.roles)
  (roots : RootPreserving S₀.R) (heads : HeadPreserving S₀.R) (algebra : CumulativeAlgebra S₀.R)
  (typesFormed : DeclaredTypesFormed S₀.R)
include facts roots heads algebra typesFormed

/-- The kernel's check of a right-hand side at the constructor `k`, with `f`
declared at its telescope type and not computing, is the premise of the
recursion's semantic theorem: the right-hand side with its calls abstracted to
the recursive hypotheses is typed in the hypothesis context, in the rule package
without `f`, whenever that package has the facts about the weak-head forms of
its types. -/
theorem bodyTyped_of_check {f T k : DeclName} {e : (i : Nat) → Tm Head i} {s d : Nat}
    {fields : List (Field Head)} {C : Tm Head (s + 1 + d)} {R : Rules Head}
    (dc : DeclaresCall R S₀.R f) (inert : CallsInert R f) (reflects : RootReflects R f (s + 1))
    (declared : R.constantType f = some (closeType (ofEntries e (s + 1 + d)) C))
    (freeE : ∀ i, ConstFree f (e i))
    (freeFields : ∀ l, ConstFree f ((fields.getD l .recursive).type T)) (hk : k ≠ f)
    (freeC : ConstFree f C) (formed : CtxFormed S₀.R (hypCtx T k e s d fields C))
    (typeFormed : IsType S₀.R (hypCtx T k e s d fields C)
      (Presentation.rename (wkN (recPositions fields).length)
        (Presentation.subst (patternSub s fields.length d k) C)))
    {body : Tm Head (s + fields.length + d + (recPositions fields).length)}
    (bodyFree : ConstFree f body)
    (check : CheckingAlgorithm R .check (patternCtx T k e s d fields)
      (Presentation.subst (hypSub f e s d fields) body)
      (Presentation.subst (patternSub s fields.length d k) C)) :
    Typed S₀.R (hypCtx T k e s d fields C) body
      (Presentation.rename (wkN (recPositions fields).length)
        (Presentation.subst (patternSub s fields.length d k) C)) := by
  have ctx := hypSub_callContexts (R := R) f e s d fields C
    (CtxConstFree.of_hypCtx freeE freeFields hk freeC)
  have typeFree : ConstFree f (Presentation.rename (wkN (recPositions fields).length)
      (Presentation.subst (patternSub s fields.length d k) C)) :=
    (freeC.subst (ConstFree.liftSubN (patSub_constFree hk) d)).rename _
  have reflected := CheckingAlgorithm.reflect dc inert reflects declared check ctx bodyFree
    typeFree rfl (by
      show Presentation.subst (extendSub ids _ _) (Presentation.rename (wkN _) _) = _
      rw [subst_extendSub_wkN, subst_ids])
  exact CheckingAlgorithm.sound facts roots heads algebra typesFormed reflected formed
    typeFormed

end Bridge

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
