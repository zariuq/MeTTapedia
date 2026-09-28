import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ScrutineeFirstEquations
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.CallAbstraction

/-!
# The authored right-hand sides of a definition admitted through its scrutinee-first form

The kernel admits `f`, recursive on its argument at `s` with calls that change
the arguments before it, by rewriting each authored equation: every call
`f ā v b̄` becomes `f' v ā b̄`, the scrutinee-first form applied to the moved
arguments (`reorderCalls`, the kernel's `sj_scrutinee_first_calls`). The
admitted definition `f x̄ y z̄ = f' y x̄ z̄` makes each such call a δ-redex whose
reduct is the rewritten call. So the rewritten right-hand side is a reduct of
the authored one, typed-equal to it wherever both are typed, given the facts
about the weak-head forms of types; and the declared function satisfies each
authored equation with its authored right-hand side, an arbitrary term the
rewriting is applied to.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open TelescopeAbstraction (closeType applyClosed applyClosed_subst)

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L]

/-! ## Moving an argument to the front -/

/-- The list with its element at `s` moved to the front, the others in order. -/
def moveToFront {α : Type} (s : Nat) (l : List α) : List α :=
  match l.drop s with
  | [] => l
  | x :: rest => x :: (l.take s ++ rest)

theorem moveToFront_append {α : Type} (s : Nat) (l₁ l₂ : List α) (hs : s < l₁.length) :
    moveToFront s (l₁ ++ l₂) = moveToFront s l₁ ++ l₂ := by
  unfold moveToFront
  rw [List.drop_append_of_le_length (Nat.le_of_lt hs)]
  rw [List.drop_eq_getElem_cons hs]
  simp only [List.cons_append, List.take_append_of_le_length (Nat.le_of_lt hs), List.append_assoc]

theorem moveToFront_map {α β : Type} (g : α → β) (s : Nat) (l : List α) :
    moveToFront s (l.map g) = (moveToFront s l).map g := by
  unfold moveToFront
  rw [← List.map_drop]
  cases l.drop s with
  | nil => rfl
  | cons x rest => simp [List.map_take]

theorem moveToFront_length {α : Type} (s : Nat) (l : List α) :
    (moveToFront s l).length = l.length := by
  unfold moveToFront
  cases h : l.drop s with
  | nil => rfl
  | cons x rest =>
      have := congrArg List.length h
      simp only [List.length_drop, List.length_cons] at this
      simp only [List.length_cons, List.length_append, List.length_take]
      omega

/-! ## Reordering the calls of `f` -/

section Reorder

variable (f f' : DeclName) (N s : Nat)

/-- The calls of `f` on at least `N` arguments rewritten as calls of `f'` with
the argument at `s` moved to the front; `stack` holds the rewritten arguments
the term is applied to. -/
def reorderAux : {n : Nat} → Tm Head n → List (Tm Head n) → Tm Head n
  | _, .app g a, stack => reorderAux g (reorderAux a [] :: stack)
  | _, .const c, stack =>
      if c = f ∧ N ≤ stack.length then appSpine (.const f') (moveToFront s stack)
      else appSpine (.const c) stack
  | _, .var i, stack => appSpine (.var i) stack
  | _, .head h, stack => appSpine (.head h) stack
  | _, .pi A B, stack => appSpine (.pi (reorderAux A []) (reorderAux B [])) stack
  | _, .sigma A B, stack => appSpine (.sigma (reorderAux A []) (reorderAux B [])) stack
  | _, .id A a b, stack =>
      appSpine (.id (reorderAux A []) (reorderAux a []) (reorderAux b [])) stack
  | _, .lam b, stack => appSpine (.lam (reorderAux b [])) stack
  | _, .pair a b, stack => appSpine (.pair (reorderAux a []) (reorderAux b [])) stack
  | _, .fst p, stack => appSpine (.fst (reorderAux p [])) stack
  | _, .snd p, stack => appSpine (.snd (reorderAux p [])) stack
  | _, .refl a, stack => appSpine (.refl (reorderAux a [])) stack

/-- Every call of `f` on at least `N` arguments rewritten as the call of `f'`
on the same arguments with the one at `s` first. -/
def reorderCalls {n : Nat} (t : Tm Head n) : Tm Head n := reorderAux f f' N s t []

/-- The δ-step of `f`: a full application steps to `f'` on the arguments with
the one at `s` moved to the front. -/
def MovesToFront (R : Rules Head) : Prop :=
  ∀ {n : Nat} (args : List (Tm Head n)), args.length = N →
    R.computation.step (appSpine (.const f) args) (appSpine (.const f') (moveToFront s args))

end Reorder

section Reduction

variable {R : Rules Head}

theorem Reduces.appSpine_both {n : Nat} {g g' : Tm Head n} (hg : Reduces R g g')
    {h : Tm Head n → Tm Head n} :
    ∀ {args : List (Tm Head n)}, (∀ a ∈ args, Reduces R a (h a)) →
      Reduces R (appSpine g args) (appSpine g' (args.map h))
  | [], _ => hg
  | a :: as, ha => by
      simp only [appSpine_cons, List.map_cons]
      have e₁ : Reduces R (.app g a) (.app g' a) :=
        Reduces.congr (f := fun x => Tm.app x a) (fun st => .congAppFun st) hg
      have e₂ : Reduces R (.app g' a) (.app g' (h a)) :=
        Reduces.congr (f := Tm.app g') (fun st => .congAppArg st) (ha a (List.mem_cons_self ..))
      exact Reduces.appSpine_both (e₁.trans e₂) (fun b hb => ha b (List.mem_cons_of_mem _ hb))

theorem Reduces.appSpine_step {n : Nat} {g g' : Tm Head n}
    (step : StepCore R.computation R.headEq g g') (args : List (Tm Head n)) :
    Reduces R (appSpine g args) (appSpine g' args) := by
  have := Reduces.appSpine_both (R := R) (Relation.ReflTransGen.single step) (h := id)
    (args := args) (fun _ _ => .refl)
  simpa using this

variable {f f' : DeclName} {N s : Nat} (moves : MovesToFront f f' N s R) (hs : s < N)
include moves hs

/-- The rewritten term is a reduct: each rewritten call is the δ-reduct of the
call, after its arguments are rewritten. -/
theorem reorder_reduces : ∀ {n : Nat} (t : Tm Head n),
    Reduces R t (reorderCalls f f' N s t) ∧
      ∀ (args : List (Tm Head n)), (∀ a ∈ args, Reduces R a (reorderCalls f f' N s a)) →
        Reduces R (appSpine t args) (reorderAux f f' N s t (args.map (reorderCalls f f' N s)))
  | n, .app g a => by
      obtain ⟨_, ihg⟩ := reorder_reduces g
      obtain ⟨iha, _⟩ := reorder_reduces a
      have part : ∀ (args : List (Tm Head n)), (∀ b ∈ args, Reduces R b (reorderCalls f f' N s b)) →
          Reduces R (appSpine (.app g a) args)
            (reorderAux f f' N s (.app g a) (args.map (reorderCalls f f' N s))) := by
        intro args hargs
        have := ihg (a :: args) (by
          intro b hb
          rcases List.mem_cons.mp hb with rfl | hb
          · exact iha
          · exact hargs b hb)
        simpa [reorderAux, reorderCalls] using this
      exact ⟨by simpa [reorderCalls] using part [] (fun b hb => nomatch hb), part⟩
  | n, .const c => by
      have part : ∀ (args : List (Tm Head n)), (∀ b ∈ args, Reduces R b (reorderCalls f f' N s b)) →
          Reduces R (appSpine (.const c) args)
            (reorderAux f f' N s (.const c) (args.map (reorderCalls f f' N s))) := by
        intro args hargs
        have congr := Reduces.appSpine_both (R := R) (g := .const c) .refl hargs
        simp only [reorderAux, List.length_map]
        split
        · rename_i h
          obtain ⟨hc, hlen⟩ := h
          rw [hc] at congr ⊢
          refine congr.trans ?_
          rw [← List.take_append_drop N (args.map (reorderCalls f f' N s)), appSpine_append,
            moveToFront_append s _ _ (by rw [List.length_take, List.length_map]; omega),
            appSpine_append]
          exact Reduces.appSpine_step
            (.root (moves _ (by rw [List.length_take, List.length_map]; omega))) _
        · exact congr
      refine ⟨?_, part⟩
      have := part [] (fun b hb => nomatch hb)
      simpa [reorderCalls] using this
  | n, .var i => by
      have part : ∀ (args : List (Tm Head n)), (∀ b ∈ args, Reduces R b (reorderCalls f f' N s b)) →
          Reduces R (appSpine (.var i) args)
            (reorderAux f f' N s (.var i) (args.map (reorderCalls f f' N s))) :=
        fun args hargs => Reduces.appSpine_both .refl hargs
      exact ⟨.refl, part⟩
  | n, .head h => by
      have part : ∀ (args : List (Tm Head n)), (∀ b ∈ args, Reduces R b (reorderCalls f f' N s b)) →
          Reduces R (appSpine (.head h) args)
            (reorderAux f f' N s (.head h) (args.map (reorderCalls f f' N s))) :=
        fun args hargs => Reduces.appSpine_both .refl hargs
      exact ⟨.refl, part⟩
  | _, .pi A B => by
      obtain ⟨ihA, _⟩ := reorder_reduces A
      obtain ⟨ihB, _⟩ := reorder_reduces B
      have head : Reduces R (.pi A B) (.pi (reorderCalls f f' N s A) (reorderCalls f f' N s B)) :=
        (Reduces.congr (f := fun X => Tm.pi X B) (fun st => .congPiDom st) ihA).trans
          (Reduces.congr (f := Tm.pi _) (fun st => .congPiCod st) ihB)
      exact ⟨head, fun args hargs => Reduces.appSpine_both head hargs⟩
  | _, .sigma A B => by
      obtain ⟨ihA, _⟩ := reorder_reduces A
      obtain ⟨ihB, _⟩ := reorder_reduces B
      have head : Reduces R (.sigma A B)
          (.sigma (reorderCalls f f' N s A) (reorderCalls f f' N s B)) :=
        (Reduces.congr (f := fun X => Tm.sigma X B) (fun st => .congSigmaDom st) ihA).trans
          (Reduces.congr (f := Tm.sigma _) (fun st => .congSigmaCod st) ihB)
      exact ⟨head, fun args hargs => Reduces.appSpine_both head hargs⟩
  | _, .id A a b => by
      obtain ⟨ihA, _⟩ := reorder_reduces A
      obtain ⟨iha, _⟩ := reorder_reduces a
      obtain ⟨ihb, _⟩ := reorder_reduces b
      have head : Reduces R (.id A a b)
          (.id (reorderCalls f f' N s A) (reorderCalls f f' N s a) (reorderCalls f f' N s b)) :=
        ((Reduces.congr (f := fun X => Tm.id X a b) (fun st => .congIdTy st) ihA).trans
          (Reduces.congr (f := fun X => Tm.id _ X b) (fun st => .congIdLeft st) iha)).trans
          (Reduces.congr (f := fun X => Tm.id _ _ X) (fun st => .congIdRight st) ihb)
      exact ⟨head, fun args hargs => Reduces.appSpine_both head hargs⟩
  | _, .lam b => by
      obtain ⟨ihb, _⟩ := reorder_reduces b
      have head : Reduces R (.lam b) (.lam (reorderCalls f f' N s b)) :=
        Reduces.congr (f := Tm.lam) (fun st => .congLam st) ihb
      exact ⟨head, fun args hargs => Reduces.appSpine_both head hargs⟩
  | _, .pair a b => by
      obtain ⟨iha, _⟩ := reorder_reduces a
      obtain ⟨ihb, _⟩ := reorder_reduces b
      have head : Reduces R (.pair a b) (.pair (reorderCalls f f' N s a) (reorderCalls f f' N s b)) :=
        (Reduces.congr (f := fun X => Tm.pair X b) (fun st => .congPairFst st) iha).trans
          (Reduces.congr (f := Tm.pair _) (fun st => .congPairSnd st) ihb)
      exact ⟨head, fun args hargs => Reduces.appSpine_both head hargs⟩
  | _, .fst p => by
      obtain ⟨ihp, _⟩ := reorder_reduces p
      have head : Reduces R (.fst p) (.fst (reorderCalls f f' N s p)) :=
        Reduces.congr (f := Tm.fst) (fun st => .congFst st) ihp
      exact ⟨head, fun args hargs => Reduces.appSpine_both head hargs⟩
  | _, .snd p => by
      obtain ⟨ihp, _⟩ := reorder_reduces p
      have head : Reduces R (.snd p) (.snd (reorderCalls f f' N s p)) :=
        Reduces.congr (f := Tm.snd) (fun st => .congSnd st) ihp
      exact ⟨head, fun args hargs => Reduces.appSpine_both head hargs⟩
  | _, .refl a => by
      obtain ⟨iha, _⟩ := reorder_reduces a
      have head : Reduces R (.refl a) (.refl (reorderCalls f f' N s a)) :=
        Reduces.congr (f := Tm.refl) (fun st => .congRefl st) iha
      exact ⟨head, fun args hargs => Reduces.appSpine_both head hargs⟩

end Reduction


/-! ## The admitted definition moves the argument to the front -/

theorem moveToFront_getElem {α : Type} (s : Nat) (l : List α) (hs : s < l.length) (p : Nat)
    (hp : p < (moveToFront s l).length) :
    (moveToFront s l)[p] =
      if h₀ : p = 0 then l[s] else if h₁ : p ≤ s then l[p - 1]'(by omega)
        else l[p]'(by rw [moveToFront_length] at hp; exact hp) := by
  have e : l.drop s = l[s] :: l.drop (s + 1) := List.drop_eq_getElem_cons hs
  have form : moveToFront s l = l[s] :: (l.take s ++ l.drop (s + 1)) := by
    unfold moveToFront
    rw [e]
  have hlen : (moveToFront s l).length = l.length := moveToFront_length s l
  simp only [form]
  rcases Nat.eq_zero_or_pos p with rfl | hpos
  · rw [dif_pos rfl]
    rfl
  · obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    rw [dif_neg (by omega), List.getElem_cons_succ]
    by_cases hq : q < s
    · rw [dif_pos (by omega), List.getElem_append_left (by rw [List.length_take]; omega), List.getElem_take]
      rfl
    · rw [dif_neg (by omega), List.getElem_append_right (by rw [List.length_take]; omega), List.getElem_drop]
      congr 1
      simp only [List.length_take]
      omega

section Definition

variable {S : Setting Head L} {F : Nat → Tm Head 0} {f f' : DeclName} {s d : Nat}
  {C : Tm Head (s + 1 + d)} {R₁ : Rules Head}

/-- The substitution of a telescope whose arguments are the list `args`. -/
def listSub {m : Nat} (N : Nat) (args : List (Tm Head m)) : Sub Head N m :=
  fun i => args.getD (N - 1 - i.val) defaultTm

theorem telescopeArgs_listSub (e : (i : Nat) → Tm Head i) {m : Nat} (N : Nat)
    (args : List (Tm Head m)) (hlen : args.length = N) :
    telescopeArgs (ofEntries e N) (listSub N args) = args := by
  rw [telescopeArgs_ofEntries_ofFn]
  apply List.ext_getElem
  · rw [List.length_ofFn, hlen]
  · intro p h₁ h₂
    simp only [List.getElem_ofFn, listSub]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    congr 1
    rw [List.length_ofFn] at h₁
    omega

/-- The scrutinee-first arguments of the telescope substitution whose authored
arguments are `args`: `args` with the one at `s` moved to the front. -/
theorem telescopeArgs_moveBack (e' : (i : Nat) → Tm Head i) {m : Nat} (s d : Nat)
    (args : List (Tm Head m)) (hlen : args.length = s + 1 + d) :
    telescopeArgs (ofEntries e' (0 + 1 + (s + d)))
        (fun j => listSub (s + 1 + d) args (teleMoveBack s d j)) = moveToFront s args := by
  rw [telescopeArgs_ofEntries_ofFn]
  apply List.ext_getElem
  · simp only [List.length_ofFn, moveToFront_length, hlen]
    omega
  · intro p h₁ h₂
    have hp : p < s + 1 + d := by rw [moveToFront_length, hlen] at h₂; exact h₂
    have key : ∀ q (hq : q < args.length), args.getD q defaultTm = args[q] := fun q hq => by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq, Option.getD_some]
    rw [List.getElem_ofFn, moveToFront_getElem s args (by omega) p h₂]
    unfold listSub
    rw [teleMoveBack_val]
    dsimp only
    split_ifs <;> first
      | (exfalso; omega)
      | (rw [key _ (by omega)]; congr 1; omega)

/-- The admitted definition `f x̄ y z̄ = f' y x̄ z̄` steps every full application
of `f` to `f'` on the arguments with the one at `s` moved to the front. -/
theorem DeclaresDefinition.movesToFront {e : (i : Nat) → Tm Head i}
    (defn : DeclaresDefinition S R₁ f (ofEntries e (s + 1 + d)) C (definitionBody F f' s d)) :
    MovesToFront f f' (s + 1 + d) s S.R := by
  intro m args hlen
  have step := defn.rule (listSub (s + 1 + d) args)
  rw [applyClosed_eq_appSpine, telescopeArgs_listSub _ _ _ hlen, subst_definitionBody,
    applyClosed_eq_appSpine, telescopeArgs_moveBack _ s d args hlen] at step
  exact step

end Definition

/-! ## The rewritten right-hand side is typed-equal to the authored one -/

section Equality

variable {S : Setting Head L} (facts : FormFacts S.R S.roles)
  (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
include facts roots heads

/-- In a model whose computation moves the argument to the front, a typed term
is typed-equal to its rewriting, which has the same type. -/
theorem Equal.reorderCalls {f f' : DeclName} {N s : Nat} (moves : MovesToFront f f' N s S.R)
    (hs : s < N) {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {t T : Tm Head n}
    (typing : Typed S.R Γ t T) :
    Typed S.R Γ (reorderCalls f f' N s t) T ∧ Equal S.R Γ t (reorderCalls f f' N s t) T :=
  Reduces.preserve facts roots heads formed (reorder_reduces moves hs t).1 typing

end Equality


/-! ## The authored equations with their authored right-hand sides -/

section Authored

variable {S : Setting Head L} (facts : FormFacts S.R S.roles)
  (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  {e e' : (i : Nat) → Tm Head i} {F : Nat → Tm Head 0} {f f' : DeclName} {s d : Nat}
  {C : Tm Head (s + 1 + d)} {R₁ : Rules Head}
  (defn : DeclaresDefinition S R₁ f (ofEntries e (s + 1 + d)) C (definitionBody F f' s d))
  {T : DeclName} {ctors : List (DeclName × List (Field Head))}
  {body' : (k : DeclName) → (fields : List (Field Head)) →
    Tm Head (0 + fields.length + (s + d) + (recPositions fields).length)}
  {R₀ : Rules Head}
  (first : DeclaresRecursion S R₀ f' T ctors e' 0 (s + d) (Presentation.rename (teleMove s d) C)
    body')
  {R₀' R₁' R₂' : Rules Head} {u : Head} {rec : DeclName} {v : Head}
  (ind : DeclaresInductive S R₀' R₁' R₂' T u ctors rec v)
include facts roots heads defn first ind

/-- The declared function satisfies each authored equation with its authored
right-hand side `rhs`, a term typed at the equation's type in the authored
pattern context: at a constructor form, `f` applied to the arguments is equal
to `rhs` under the match. The scrutinee-first form's right-hand side, with its
recursive calls, is the kernel's rewriting of `rhs` moved to that form's
pattern context. -/
theorem ScrutineeFirst.authored_equation {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ)
    {k : DeclName} {fields : List (Field Head)} (mem : (k, fields) ∈ ctors)
    {rhs : Tm Head (s + fields.length + d)}
    (patFormed : CtxFormed S.R (patternCtx T k e s d fields))
    (rhsTyped : Typed S.R (patternCtx T k e s d fields) rhs
      (Presentation.subst (patternSub s fields.length d k) C))
    (pipeline : Presentation.subst
        (hypSub f' e' 0 (s + d) fields) (body' k fields) =
      Presentation.rename (blockMove s fields.length d) (reorderCalls f f' (s + 1 + d) s rhs))
    {τ : Sub Head (s + 1 + d) n}
    (typedτ : SubstMor S.R (ofEntries e (s + 1 + d)) Γ τ)
    {as : List (Tm Head n)} (has : as.length = fields.length)
    (typedFields : ∀ l, l < fields.length →
      Typed S.R Γ (as.getD l defaultTm) (liftClosed ((fields.getD l .recursive).type T)))
    (scrut : scrutOf s d τ = appSpine (.const k) as) :
    Equal S.R Γ (applyClosed (ofEntries e (s + 1 + d)) τ (.const f))
      (Presentation.subst (matchSub s fields.length as d τ) rhs) (Presentation.subst τ C) := by
  have hτ : replaceScrut s (appSpine (.const k) as) d τ = τ := by
    rw [← scrut, replaceScrut_self]
  -- the δ-step of `f` and the ι-step of `f'`
  have typing : Typed S.R Γ (applyClosed (ofEntries e (s + 1 + d))
      (replaceScrut s (appSpine (.const k) as) d τ) (.const f)) (Presentation.subst τ C) := by
    rw [hτ]
    exact Typed.telescope_apply typedτ defn.typing
  have equation := ScrutineeFirst.equation facts defn first ind formed mem τ as has typing
  rw [hτ, pipeline, subst_rename] at equation
  have moved : (fun i => matchSub 0 fields.length as (s + d) (fun j => τ (teleMoveBack s d j))
      (blockMove s fields.length d i)) = matchSub s fields.length as d τ :=
    funext fun i => matchSub_blockMove s fields.length d as τ i
  rw [moved] at equation
  -- the rewritten right-hand side is equal to the authored one, under the match
  have match_ := SubstMor.pattern (R := S.R) e fields typedFields has d
    typedτ scrut
  have second := ((Equal.reorderCalls facts roots heads (DeclaresDefinition.movesToFront defn)
    (by omega) patFormed rhsTyped).2).substitute match_
  have typeEq : Presentation.subst (matchSub s fields.length as d τ)
      (Presentation.subst (patternSub s fields.length d k) C) = Presentation.subst τ C := by
    rw [subst_comp]
    conv_rhs => rw [← hτ]
    congr 1
    funext i
    exact subst_matchSub_patternSub k as has d τ i
  rw [typeEq] at second
  exact equation.trans second.symm

end Authored


/-! ## Execution: demand and sharing -/

/-- The δ-step's reduct holds every argument exactly once: none is dropped or
duplicated. -/
theorem moveToFront_perm {α : Type} (s : Nat) (l : List α) : (moveToFront s l).Perm l := by
  unfold moveToFront
  cases h : l.drop s with
  | nil => exact .refl _
  | cons x rest =>
      have e : l = l.take s ++ x :: rest := by rw [← h, List.take_append_drop]
      conv_rhs => rw [e]
      exact List.perm_middle.symm

theorem scrutOf_apply {m s : Nat} :
    ∀ (d : Nat) (σ : Sub Head (s + 1 + d) m), scrutOf s d σ = σ ⟨d, by omega⟩
  | 0, _ => rfl
  | d + 1, σ => by
      show scrutOf s d (tailSub σ) = _
      rw [scrutOf_apply d (tailSub σ)]
      rfl

/-- The scrutinee of the moved arguments is the authored scrutinee. -/
theorem scrutOf_moveBack {m : Nat} (s d : Nat) (σ : Sub Head (s + 1 + d) m) :
    scrutOf 0 (s + d) (fun j => σ (teleMoveBack s d j)) = scrutOf s d σ := by
  rw [scrutOf_apply, scrutOf_apply]
  congr 1
  apply Fin.ext
  rw [teleMoveBack_val]
  dsimp only
  split_ifs <;> first | (exfalso; omega) | rfl

section Execution

variable {S : Setting Head L} {e' : (i : Nat) → Tm Head i} {f' : DeclName} {s d : Nat}
  {C : Tm Head (s + 1 + d)} {T : DeclName} {ctors : List (DeclName × List (Field Head))}
  {body' : (k : DeclName) → (fields : List (Field Head)) →
    Tm Head (0 + fields.length + (s + d) + (recPositions fields).length)}
  {R₀ : Rules Head}

/-- After the δ-step of the authored function, which inspects no argument, the
scrutinee-first call is stuck when the authored scrutinee is neutral: the
computation demands the authored scrutinee and no other argument. -/
theorem ScrutineeFirst.stuck
    (first : DeclaresRecursion S R₀ f' T ctors e' 0 (s + d) (Presentation.rename (teleMove s d) C)
      body')
    {m : Nat} {σ : Sub Head (s + 1 + d) m} (neutral : Neutral S.roles (scrutOf s d σ)) :
    Neutral S.roles (applyClosed (ofEntries e' (0 + 1 + (s + d))) (fun j => σ (teleMoveBack s d j))
      (.const f')) := by
  apply first.neutral
  rw [scrutOf_moveBack]
  exact neutral

end Execution

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
