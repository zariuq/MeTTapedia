import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramNeedStep

/-!
# Call by need on the step: adequacy

- `nstep_fires`: each machine step from a configuration whose locations are listed is one firing of
  its schema on the rows.
- `fires_nstep`: each firing of a schema on the rows of a configuration is one machine step.
- `need_rows_iff`, `need_on_step`: row rewriting, and runs of translated firings of the ordinary
  step, reach exactly the rows of the machine's runs.
- `need_eval_on_step`: with Launchbury's semantics (`need_adequacy`): a by-need evaluation is a run
  of the step representing its final rows, and every such run is a by-need evaluation, with the
  final heap read on the listed locations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramNeed

open ProgramRows ProgramTranslation ProgramCompiled
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramNested (EPat NEquation)

variable {prog : Program}

/-! ## Listed locations -/

/-- The locations an expression binds or demands. -/
def locsX : NEx → List ℕ
  | .val _ => []
  | .loc ℓ => [ℓ]
  | .pair a b => locsX a ++ locsX b
  | .call a => locsX a
  | .bind ℓ a b => ℓ :: (locsX a ++ locsX b)

def locsF : Frame → List ℕ
  | .left b => locsX b
  | .right _ => []
  | .arg => []
  | .update ℓ => [ℓ]

theorem locs_instE (θ : ℕ → Sx) : ∀ p : EPat, locsX (instE θ p) = []
  | .val _ => rfl
  | .pair a b => by simp [instE, locsX, locs_instE θ a, locs_instE θ b]
  | .call a => by simp [instE, locsX, locs_instE θ a]

/-- **Every location the configuration names is listed.** -/
structure Inside (L : List ℕ) (c : Conf) : Prop where
  control : ∀ e, c.1 = .ev e → ∀ ℓ ∈ locsX e, ℓ ∈ L
  stack : ∀ f ∈ c.2.1, ∀ ℓ ∈ locsF f, ℓ ∈ L
  heap : ∀ ℓ e, c.2.2 ℓ = .thunk e → ∀ ℓ' ∈ locsX e, ℓ' ∈ L

theorem inside_step {L : List ℕ} {c c' : Conf} (step : NStep prog c c') (inside : Inside L c) : Inside L c' := by
  obtain ⟨control, stack, heap⟩ := inside
  cases step with
  | val t K H =>
      exact ⟨(fun e same => by cases same),stack, heap⟩
  | pair a b K H =>
      refine ⟨fun e same ℓ member => ?_, fun f member ℓ inF => ?_, heap⟩
      · cases same
        exact control _ rfl ℓ (by simp [locsX, member])
      · rcases List.mem_cons.mp member with rfl | member
        · exact control _ rfl ℓ (by simp [locsX, locsF] at inF ⊢; exact .inr inF)
        · exact stack f member ℓ inF
  | call a K H =>
      refine ⟨fun e same ℓ member => ?_, fun f member ℓ inF => ?_, heap⟩
      · cases same
        exact control _ rfl ℓ member
      · rcases List.mem_cons.mp member with rfl | member
        · simp [locsF] at inF
        · exact stack f member ℓ inF
  | bind ℓ a b K H fresh =>
      refine ⟨fun e same ℓ' member => ?_, stack, fun ℓ' e stored ℓ'' member => ?_⟩
      · cases same
        exact control _ rfl ℓ' (by simp [locsX, member])
      · by_cases at_ℓ : ℓ' = ℓ
        · subst at_ℓ
          change H.set ℓ' (.thunk a) ℓ' = _ at stored
          rw [Heap.set_same] at stored
          cases stored
          exact control _ rfl ℓ'' (by simp [locsX, member])
        · change H.set ℓ (.thunk a) ℓ' = _ at stored
          rw [Heap.set_other _ _ at_ℓ] at stored
          exact heap ℓ' e stored ℓ'' member
  | read ℓ K H v stored =>
      exact ⟨(fun e same => by cases same),stack, heap⟩
  | force ℓ K H e stored =>
      refine ⟨fun e' same ℓ' member => ?_, fun f member ℓ' inF => ?_, fun ℓ' e' stored' ℓ'' member => ?_⟩
      · cases same
        exact heap ℓ e stored ℓ' member
      · rcases List.mem_cons.mp member with rfl | member
        · simp only [locsF, List.mem_singleton] at inF
          subst inF
          exact control _ rfl ℓ' (by simp [locsX])
        · exact stack f member ℓ' inF
      · by_cases at_ℓ : ℓ' = ℓ
        · subst at_ℓ
          change H.set ℓ' .busy ℓ' = _ at stored'
          rw [Heap.set_same] at stored'
          cases stored'
        · change H.set ℓ .busy ℓ' = _ at stored'
          rw [Heap.set_other _ _ at_ℓ] at stored'
          exact heap ℓ' e' stored' ℓ'' member
  | left v b K H =>
      refine ⟨fun e same ℓ member => ?_, fun f member ℓ inF => ?_, heap⟩
      · cases same
        exact stack _ List.mem_cons_self ℓ member
      · rcases List.mem_cons.mp member with rfl | member
        · simp [locsF] at inF
        · exact stack f (List.mem_cons_of_mem _ member) ℓ inF
  | right v w K H =>
      exact ⟨(fun e same => by cases same),fun f member => stack f (List.mem_cons_of_mem _ member), heap⟩
  | arg w K H =>
      exact ⟨(fun e same => by cases same),fun f member => stack f (List.mem_cons_of_mem _ member), heap⟩
  | update ℓ v K H =>
      refine ⟨(fun e same => by cases same),fun f member => stack f (List.mem_cons_of_mem _ member),
        fun ℓ' e stored ℓ'' member => ?_⟩
      by_cases at_ℓ : ℓ' = ℓ
      · subst at_ℓ
        change H.set ℓ' (.value v) ℓ' = _ at stored
        rw [Heap.set_same] at stored
        cases stored
      · change H.set ℓ (.value v) ℓ' = _ at stored
        rw [Heap.set_other _ _ at_ℓ] at stored
        exact heap ℓ' e stored ℓ'' member
  | apply w K H j θ matched =>
      refine ⟨fun e same ℓ member => ?_, stack, heap⟩
      cases same
      rw [locs_instE] at member
      exact absurd member List.not_mem_nil

/-! ## Each machine step is one firing -/

/-- An assignment from a list of values. -/
def asg (l : List Sx) : ℕ → Sx := fun x => l.getD x (.sym 0)

theorem instE_congr {θ θ' : ℕ → Sx} : ∀ (p : EPat), (∀ x ∈ p.vars, θ x = θ' x) → instE θ p = instE θ' p
  | .val p, agree => by
      show NEx.val (p.inst θ) = NEx.val (p.inst θ')
      rw [Pat.inst_congr p agree]
  | .pair a b, agree => by
      show NEx.pair (instE θ a) (instE θ b) = NEx.pair (instE θ' a) (instE θ' b)
      rw [instE_congr a fun x hx => agree x (List.mem_append_left _ hx),
        instE_congr b fun x hx => agree x (List.mem_append_right _ hx)]
  | .call a, agree => by
      show NEx.call (instE θ a) = NEx.call (instE θ' a)
      rw [instE_congr a agree]

theorem fires_one {r : Schema} {take : Pat} {make : Pat} (shapeT : r.take = [take]) (shapeR : r.read = [])
    (shapeM : r.make = [make]) (θ : ℕ → Sx) {x y : Sx} {F : Multiset Sx} (hx : take.inst θ = x) (hy : make.inst θ = y) :
    r.Fires (x ::ₘ F) (y ::ₘ F) :=
  ⟨θ, F, by rw [shapeT, shapeR, ← hx]; rfl, by rw [shapeM, shapeR, ← hy]; rfl⟩

theorem fires_two {r : Schema} {take₁ take₂ make₁ make₂ : Pat} (shapeT : r.take = [take₁, take₂])
    (shapeR : r.read = []) (shapeM : r.make = [make₁, make₂]) (θ : ℕ → Sx) {x₁ x₂ y₁ y₂ : Sx} {F : Multiset Sx}
    (hx₁ : take₁.inst θ = x₁) (hx₂ : take₂.inst θ = x₂) (hy₁ : make₁.inst θ = y₁) (hy₂ : make₂.inst θ = y₂) :
    r.Fires (x₁ ::ₘ x₂ ::ₘ F) (y₁ ::ₘ y₂ ::ₘ F) :=
  ⟨θ, F, by rw [shapeT, shapeR, ← hx₁, ← hx₂]; rfl, by rw [shapeM, shapeR, ← hy₁, ← hy₂]; rfl⟩

theorem fires_read {r : Schema} {take read make : Pat} (shapeT : r.take = [take]) (shapeR : r.read = [read])
    (shapeM : r.make = [make]) (θ : ℕ → Sx) {x z y : Sx} {F : Multiset Sx} (hx : take.inst θ = x)
    (hz : read.inst θ = z) (hy : make.inst θ = y) : r.Fires (x ::ₘ z ::ₘ F) (y ::ₘ z ::ₘ F) :=
  ⟨θ, F, by rw [shapeT, shapeR, ← hx, ← hz]; rfl, by rw [shapeM, shapeR, ← hy, ← hz]; rfl⟩

/-- **Each machine step is one firing of its schema.** -/
theorem nstep_fires {L : List ℕ} (nodup : L.Nodup) (restricted : RangeRestricted prog) {c c' : Conf}
    (step : NStep prog c c') (inside : Inside L c) (wf : Wf c) :
    Rewrites (nschema prog) (rowsOf L c) (rowsOf L c') := by
  cases step with
  | val t K H => exact ⟨.inl .val, fires_one rfl rfl rfl (asg [t, encK K]) rfl rfl⟩
  | pair a b K H => exact ⟨.inl .pair, fires_one rfl rfl rfl (asg [encX a, encX b, encK K]) rfl rfl⟩
  | call a K H => exact ⟨.inl .call, fires_one rfl rfl rfl (asg [encX a, encK K]) rfl rfl⟩
  | bind ℓ a b K H fresh =>
      have inL : ℓ ∈ L := inside.control _ rfl ℓ (by simp [locsX])
      obtain ⟨before, after⟩ := cells_split nodup inL H (.thunk a)
      refine ⟨.inl .bind, ?_⟩
      unfold rowsOf
      dsimp only
      rw [before, after, fresh]
      exact fires_two rfl rfl rfl (asg [nat ℓ, encX a, encX b, encK K]) rfl rfl rfl rfl
  | read ℓ K H v stored =>
      have inL : ℓ ∈ L := inside.control _ rfl ℓ (by simp [locsX])
      obtain ⟨before, -⟩ := cells_split nodup inL H .empty
      refine ⟨.inl .read, ?_⟩
      unfold rowsOf
      dsimp only
      rw [before, stored]
      exact fires_read rfl rfl rfl (asg [nat ℓ, encK K, v]) rfl rfl rfl
  | force ℓ K H e stored =>
      have inL : ℓ ∈ L := inside.control _ rfl ℓ (by simp [locsX])
      obtain ⟨before, after⟩ := cells_split nodup inL H .busy
      refine ⟨.inl .force, ?_⟩
      unfold rowsOf
      dsimp only
      rw [before, after, stored]
      exact fires_two rfl rfl rfl (asg [nat ℓ, encK K, encX e]) rfl rfl rfl rfl
  | left v b K H => exact ⟨.inl .left, fires_one rfl rfl rfl (asg [v, encX b, encK K]) rfl rfl⟩
  | right v w K H => exact ⟨.inl .right, fires_one rfl rfl rfl (asg [w, v, encK K]) rfl rfl⟩
  | arg w K H => exact ⟨.inl .arg, fires_one rfl rfl rfl (asg [w, encK K]) rfl rfl⟩
  | update ℓ v K H =>
      have inL : ℓ ∈ L := inside.stack _ List.mem_cons_self ℓ (by simp [locsF])
      have busy : H ℓ = .busy := wf.2 ℓ List.mem_cons_self
      obtain ⟨before, after⟩ := cells_split nodup inL H (.value v)
      refine ⟨.inl .update, ?_⟩
      unfold rowsOf
      dsimp only
      rw [before, after, busy]
      exact fires_two rfl rfl rfl (asg [v, nat ℓ, encK K]) rfl rfl rfl rfl
  | apply w K H j θ matched =>
      let θ' : ℕ → Sx := fun x => if x = stackVar (prog.get j) then encK K else θ x
      have agreeL : ∀ x ∈ (prog.get j).lhs.vars, θ' x = θ x := fun x hx => by
        simp only [θ', if_neg (Nat.ne_of_lt (lt_stackVar _ x hx))]
      have agreeR : ∀ x ∈ (prog.get j).rhs.vars, θ' x = θ x := fun x hx => agreeL x (restricted j x hx)
      refine ⟨.inr j, fires_one rfl rfl rfl θ' ?_ ?_⟩
      · show tup 240 [tup 222 [(prog.get j).lhs.inst θ'], θ' (stackVar (prog.get j))] = thr (.ap w) K
        rw [Pat.inst_congr _ agreeL, matched]
        simp only [θ', if_pos rfl]
        rfl
      · show tup 240 [tup 220 [(encEP (prog.get j).rhs).inst θ'], θ' (stackVar (prog.get j))] =
          thr (.ev (instE θ (prog.get j).rhs)) K
        rw [encEP_inst, instE_congr _ agreeR]
        simp only [θ', if_pos rfl]
        rfl

/-! ## Each firing is one machine step -/

theorem decode_ev {c : Control} {x : Sx} (h : encC c = tup 220 [x]) : ∃ e, c = .ev e ∧ encX e = x := by
  cases c with
  | ev e => exact ⟨e, rfl, by simpa [encC, tup_inj] using h⟩
  | ret _ => simp [encC, tup_inj] at h
  | ap _ => simp [encC, tup_inj] at h

theorem decode_ret {c : Control} {x : Sx} (h : encC c = tup 221 [x]) : c = .ret x := by
  cases c with
  | ret _ => simpa [encC, tup_inj] using h
  | ev _ => simp [encC, tup_inj] at h
  | ap _ => simp [encC, tup_inj] at h

theorem decode_ap {c : Control} {x : Sx} (h : encC c = tup 222 [x]) : c = .ap x := by
  cases c with
  | ap _ => simpa [encC, tup_inj] using h
  | ev _ => simp [encC, tup_inj] at h
  | ret _ => simp [encC, tup_inj] at h

theorem decode_val {e : NEx} {x : Sx} (h : encX e = tup 200 [x]) : e = .val x := by
  cases e with
  | val _ => simpa [encX, tup_inj] using h
  | loc _ => simp [encX, tup_inj] at h
  | pair _ _ => simp [encX, tup_inj] at h
  | call _ => simp [encX, tup_inj] at h
  | bind _ _ _ => simp [encX, tup_inj] at h

theorem decode_loc {e : NEx} {x : Sx} (h : encX e = tup 201 [x]) : ∃ ℓ, e = .loc ℓ ∧ nat ℓ = x := by
  cases e with
  | loc ℓ => exact ⟨ℓ, rfl, by simpa [encX, tup_inj] using h⟩
  | val _ => simp [encX, tup_inj] at h
  | pair _ _ => simp [encX, tup_inj] at h
  | call _ => simp [encX, tup_inj] at h
  | bind _ _ _ => simp [encX, tup_inj] at h

theorem decode_pair {e : NEx} {x y : Sx} (h : encX e = tup 202 [x, y]) :
    ∃ a b, e = .pair a b ∧ encX a = x ∧ encX b = y := by
  cases e with
  | pair a b =>
      simp only [encX, tup_inj, List.cons.injEq, and_true, true_and] at h
      exact ⟨a, b, rfl, h.1, h.2⟩
  | val _ => simp [encX, tup_inj] at h
  | loc _ => simp [encX, tup_inj] at h
  | call _ => simp [encX, tup_inj] at h
  | bind _ _ _ => simp [encX, tup_inj] at h

theorem decode_call {e : NEx} {x : Sx} (h : encX e = tup 203 [x]) : ∃ a, e = .call a ∧ encX a = x := by
  cases e with
  | call a => exact ⟨a, rfl, by simpa [encX, tup_inj] using h⟩
  | val _ => simp [encX, tup_inj] at h
  | loc _ => simp [encX, tup_inj] at h
  | pair _ _ => simp [encX, tup_inj] at h
  | bind _ _ _ => simp [encX, tup_inj] at h

theorem decode_bind {e : NEx} {x y z : Sx} (h : encX e = tup 204 [x, y, z]) :
    ∃ ℓ a b, e = .bind ℓ a b ∧ nat ℓ = x ∧ encX a = y ∧ encX b = z := by
  cases e with
  | bind ℓ a b =>
      simp only [encX, tup_inj, List.cons.injEq, and_true, true_and] at h
      exact ⟨ℓ, a, b, rfl, h.1, h.2.1, h.2.2⟩
  | val _ => simp [encX, tup_inj] at h
  | loc _ => simp [encX, tup_inj] at h
  | pair _ _ => simp [encX, tup_inj] at h
  | call _ => simp [encX, tup_inj] at h

theorem decode_cons {K : List Frame} {x y : Sx} (h : encK K = tup 90 [x, y]) :
    ∃ f K', K = f :: K' ∧ encF f = x ∧ encK K' = y := by
  cases K with
  | nil => simp [encK, codeOf, knil, tup_inj] at h
  | cons f K' =>
      simp only [encK, List.map_cons, codeOf, kons, tup_inj, List.cons.injEq, and_true, true_and] at h
      exact ⟨f, K', rfl, h.1, h.2⟩

theorem decode_left {f : Frame} {x : Sx} (h : encF f = tup 210 [x]) : ∃ b, f = .left b ∧ encX b = x := by
  cases f with
  | left b => exact ⟨b, rfl, by simpa [encF, tup_inj] using h⟩
  | right _ => simp [encF, tup_inj] at h
  | arg => simp [encF, tup_inj] at h
  | update _ => simp [encF, tup_inj] at h

theorem decode_right {f : Frame} {x : Sx} (h : encF f = tup 211 [x]) : f = .right x := by
  cases f with
  | right _ => simpa [encF, tup_inj] using h
  | left _ => simp [encF, tup_inj] at h
  | arg => simp [encF, tup_inj] at h
  | update _ => simp [encF, tup_inj] at h

theorem decode_arg {f : Frame} (h : encF f = tup 212 []) : f = .arg := by
  cases f with
  | arg => rfl
  | left _ => simp [encF, tup_inj] at h
  | right _ => simp [encF, tup_inj] at h
  | update _ => simp [encF, tup_inj] at h

theorem decode_update {f : Frame} {x : Sx} (h : encF f = tup 213 [x]) : ∃ ℓ, f = .update ℓ ∧ nat ℓ = x := by
  cases f with
  | update ℓ => exact ⟨ℓ, rfl, by simpa [encF, tup_inj] using h⟩
  | left _ => simp [encF, tup_inj] at h
  | right _ => simp [encF, tup_inj] at h
  | arg => simp [encF, tup_inj] at h

/-- The thread take of a firing is the thread row. -/
theorem thread_take {L : List ℕ} {c : Control} {K : List Frame} {H : Heap} {a b : Sx} {G : Multiset Sx}
    (same : thr c K ::ₘ cells L H = tup 240 [a, b] ::ₘ G) : encC c = a ∧ encK K = b ∧ G = cells L H := by
  rcases Multiset.cons_eq_cons.mp same with ⟨heads, tails⟩ | ⟨_, rest, inCells, _⟩
  · simp only [thr, tup_inj, List.cons.injEq, and_true, true_and] at heads
    exact ⟨heads.1, heads.2, tails.symm⟩
  · have member : tup 240 [a, b] ∈ cells L H := by rw [inCells]; exact Multiset.mem_cons_self _ _
    obtain ⟨ℓ, -, eq⟩ := cell_mem member
    simp [cellRow, tup_inj] at eq

theorem fires_shape {r : Schema} {W W' : Multiset Sx} (fires : r.Fires W W') :
    ∃ (θ : ℕ → Sx) (F : Multiset Sx), W = push (r.take.map (Pat.inst θ)) (push (r.read.map (Pat.inst θ)) F) ∧
      W' = push (r.make.map (Pat.inst θ)) (push (r.read.map (Pat.inst θ)) F) := fires

set_option linter.unusedSimpArgs false in
/-- **Each firing of a schema on the rows of a configuration is one machine step.** -/
theorem fires_nstep {L : List ℕ} (nodup : L.Nodup) {c : Conf} {i : NRule prog} {W' : Multiset Sx}
    (fires : (nschema prog i).Fires (rowsOf L c) W') : ∃ c', NStep prog c c' ∧ W' = rowsOf L c' := by
  obtain ⟨ctl, K, H⟩ := c
  obtain ⟨θ, F, before, after⟩ := fires_shape fires
  rcases i with r | j
  · cases r with
    | val =>
        simp only [nschema, adminSchema, thrP, evP, retP, apP, consP, cellP, pvar, ptup_inst, List.map_cons,
          List.map_nil, Pat.inst, push, List.foldr_cons, List.foldr_nil, rowsOf] at before after
        obtain ⟨hc, hK, rfl⟩ := thread_take before
        obtain ⟨e, rfl, he⟩ := decode_ev hc
        have := decode_val he
        subst this
        refine ⟨_, .val _ K H, ?_⟩
        rw [after, ← hK]
        rfl
    | pair =>
        simp only [nschema, adminSchema, thrP, evP, retP, apP, consP, cellP, pvar, ptup_inst, List.map_cons,
          List.map_nil, Pat.inst, push, List.foldr_cons, List.foldr_nil, rowsOf] at before after
        obtain ⟨hc, hK, rfl⟩ := thread_take before
        obtain ⟨e, rfl, he⟩ := decode_ev hc
        obtain ⟨a, b, rfl, ha, hb⟩ := decode_pair he
        refine ⟨_, .pair a b K H, ?_⟩
        rw [after, ← ha, ← hb, ← hK]
        rfl
    | call =>
        simp only [nschema, adminSchema, thrP, evP, retP, apP, consP, cellP, pvar, ptup_inst, List.map_cons,
          List.map_nil, Pat.inst, push, List.foldr_cons, List.foldr_nil, rowsOf] at before after
        obtain ⟨hc, hK, rfl⟩ := thread_take before
        obtain ⟨e, rfl, he⟩ := decode_ev hc
        obtain ⟨a, rfl, ha⟩ := decode_call he
        refine ⟨_, .call a K H, ?_⟩
        rw [after, ← ha, ← hK]
        rfl
    | bind =>
        simp only [nschema, adminSchema, thrP, evP, retP, apP, consP, cellP, pvar, ptup_inst, List.map_cons,
          List.map_nil, Pat.inst, push, List.foldr_cons, List.foldr_nil, rowsOf] at before after
        obtain ⟨hc, hK, rest⟩ := thread_take before
        obtain ⟨e, rfl, he⟩ := decode_ev hc
        obtain ⟨ℓ, a, b, rfl, hℓ, ha, hb⟩ := decode_bind he
        have cellEq : cells L H = cellRow ℓ .empty ::ₘ F := by
          rw [← rest, ← hℓ]
          rfl
        obtain ⟨inL, fresh, rfl⟩ := cell_split nodup cellEq
        refine ⟨_, .bind ℓ a b K H fresh.symm, ?_⟩
        rw [after]
        show _ = thr (.ev b) K ::ₘ cells L (H.set ℓ (.thunk a))
        rw [(cells_split nodup inL H (.thunk a)).2, ← hℓ, ← ha, ← hb, ← hK]
        rfl
    | read =>
        simp only [nschema, adminSchema, thrP, evP, retP, apP, consP, cellP, pvar, ptup_inst, List.map_cons,
          List.map_nil, Pat.inst, push, List.foldr_cons, List.foldr_nil, rowsOf] at before after
        obtain ⟨hc, hK, rest⟩ := thread_take before
        obtain ⟨e, rfl, he⟩ := decode_ev hc
        obtain ⟨ℓ, rfl, hℓ⟩ := decode_loc he
        have cellEq : cells L H = cellRow ℓ (.value (θ 2)) ::ₘ F := by
          rw [← rest, ← hℓ]
          rfl
        obtain ⟨-, stored, -⟩ := cell_split nodup cellEq
        refine ⟨_, .read ℓ K H (θ 2) stored.symm, ?_⟩
        rw [after]
        show _ = thr (.ret (θ 2)) K ::ₘ cells L H
        rw [cellEq, ← hℓ, ← hK]
        rfl
    | force =>
        simp only [nschema, adminSchema, thrP, evP, retP, apP, consP, cellP, pvar, ptup_inst, List.map_cons,
          List.map_nil, Pat.inst, push, List.foldr_cons, List.foldr_nil, rowsOf] at before after
        obtain ⟨hc, hK, rest⟩ := thread_take before
        obtain ⟨e, rfl, he⟩ := decode_ev hc
        obtain ⟨ℓ, rfl, hℓ⟩ := decode_loc he
        obtain ⟨t, ht, stored⟩ : ∃ t, encX t = θ 2 ∧ H ℓ = .thunk t := by
          have member : tup 241 [θ 0, tup 231 [θ 2]] ∈ cells L H := by
            rw [← rest]
            exact Multiset.mem_cons_self _ _
          obtain ⟨ℓ', -, eq⟩ := cell_mem member
          simp only [cellRow, tup_inj, List.cons.injEq, and_true, true_and] at eq
          rw [← hℓ] at eq
          have same := nat_inj eq.1
          subst same
          cases stored : H ℓ with
          | thunk t =>
              rw [stored] at eq
              simp only [encCell, tup_inj, List.cons.injEq, and_true, true_and] at eq
              exact ⟨t, eq.symm, rfl⟩
          | empty =>
              rw [stored] at eq
              simp [encCell, tup_inj] at eq
          | busy =>
              rw [stored] at eq
              simp [encCell, tup_inj] at eq
          | value _ =>
              rw [stored] at eq
              simp [encCell, tup_inj] at eq
        have cellEq : cells L H = cellRow ℓ (.thunk t) ::ₘ F := by
          rw [← rest, ← hℓ, ← ht]
          rfl
        obtain ⟨inL, -, rfl⟩ := cell_split nodup cellEq
        refine ⟨_, .force ℓ K H t stored, ?_⟩
        rw [after]
        show _ = thr (.ev t) (.update ℓ :: K) ::ₘ cells L (H.set ℓ .busy)
        rw [(cells_split nodup inL H .busy).2, ← hℓ, ← ht, ← hK]
        rfl
    | left =>
        simp only [nschema, adminSchema, thrP, evP, retP, apP, consP, cellP, pvar, ptup_inst, List.map_cons,
          List.map_nil, Pat.inst, push, List.foldr_cons, List.foldr_nil, rowsOf] at before after
        obtain ⟨hc, hK, rfl⟩ := thread_take before
        have := decode_ret hc
        subst this
        obtain ⟨f, K', rfl, hf, hK'⟩ := decode_cons hK
        obtain ⟨b, rfl, hb⟩ := decode_left hf
        refine ⟨_, .left (θ 0) b K' H, ?_⟩
        rw [after, ← hb, ← hK']
        rfl
    | right =>
        simp only [nschema, adminSchema, thrP, evP, retP, apP, consP, cellP, pvar, ptup_inst, List.map_cons,
          List.map_nil, Pat.inst, push, List.foldr_cons, List.foldr_nil, rowsOf] at before after
        obtain ⟨hc, hK, rfl⟩ := thread_take before
        have := decode_ret hc
        subst this
        obtain ⟨f, K', rfl, hf, hK'⟩ := decode_cons hK
        have := decode_right hf
        subst this
        refine ⟨_, .right (θ 1) (θ 0) K' H, ?_⟩
        rw [after, ← hK']
        rfl
    | arg =>
        simp only [nschema, adminSchema, thrP, evP, retP, apP, consP, cellP, pvar, ptup_inst, List.map_cons,
          List.map_nil, Pat.inst, push, List.foldr_cons, List.foldr_nil, rowsOf] at before after
        obtain ⟨hc, hK, rfl⟩ := thread_take before
        have := decode_ret hc
        subst this
        obtain ⟨f, K', rfl, hf, hK'⟩ := decode_cons hK
        have := decode_arg hf
        subst this
        refine ⟨_, .arg (θ 0) K' H, ?_⟩
        rw [after, ← hK']
        rfl
    | update =>
        simp only [nschema, adminSchema, thrP, evP, retP, apP, consP, cellP, pvar, ptup_inst, List.map_cons,
          List.map_nil, Pat.inst, push, List.foldr_cons, List.foldr_nil, rowsOf] at before after
        obtain ⟨hc, hK, rest⟩ := thread_take before
        have := decode_ret hc
        subst this
        obtain ⟨f, K', rfl, hf, hK'⟩ := decode_cons hK
        obtain ⟨ℓ, rfl, hℓ⟩ := decode_update hf
        have cellEq : cells L H = cellRow ℓ .busy ::ₘ F := by
          rw [← rest, ← hℓ]
          rfl
        obtain ⟨inL, -, rfl⟩ := cell_split nodup cellEq
        refine ⟨_, .update ℓ (θ 0) K' H, ?_⟩
        rw [after]
        show _ = thr (.ret (θ 0)) K' ::ₘ cells L (H.set ℓ (.value (θ 0)))
        rw [(cells_split nodup inL H (.value (θ 0))).2, ← hℓ, ← hK']
        rfl
  · simp only [nschema, applySchema, thrP, evP, apP, pvar, ptup_inst, List.map_cons, List.map_nil, Pat.inst,
      push, List.foldr_cons, List.foldr_nil, rowsOf] at before after
    obtain ⟨hc, hK, rfl⟩ := thread_take before
    have := decode_ap hc
    subst this
    refine ⟨_, .apply _ K H j θ rfl, ?_⟩
    rw [after, encEP_inst, ← hK]
    rfl

/-! ## Runs -/

/-- The rows of a configuration, as a list. -/
def rowsList (L : List ℕ) (c : Conf) : List Sx := thr c.1 c.2.1 :: L.map fun ℓ => cellRow ℓ (c.2.2 ℓ)

theorem rowsList_coe (L : List ℕ) (c : Conf) : (rowsList L c : Multiset Sx) = rowsOf L c := by
  rw [rowsList, ← Multiset.cons_coe]
  rfl

/-- **Row rewriting reaches exactly the rows of the machine's runs.** -/
theorem need_rows_iff {L : List ℕ} (nodup : L.Nodup) (restricted : RangeRestricted prog) {c : Conf}
    (inside : Inside L c) (wf : Wf c) (W : Multiset Sx) :
    Relation.ReflTransGen (Rewrites (nschema prog)) (rowsOf L c) W ↔
      ∃ c', Relation.ReflTransGen (NStep prog) c c' ∧ W = rowsOf L c' := by
  constructor
  · intro path
    induction path with
    | refl => exact ⟨c, .refl, rfl⟩
    | tail _ step ih =>
        obtain ⟨c', run, rfl⟩ := ih
        obtain ⟨i, fires⟩ := step
        obtain ⟨c'', next, rfl⟩ := fires_nstep nodup fires
        exact ⟨c'', run.tail next, rfl⟩
  · rintro ⟨c', run, rfl⟩
    have keep : ∀ {d : Conf}, Relation.ReflTransGen (NStep prog) c d → Inside L d ∧ Wf d := by
      intro d run
      induction run with
      | refl => exact ⟨inside, wf⟩
      | tail _ step ih => exact ⟨inside_step step ih.1, wf_step step ih.2⟩
    induction run with
    | refl => exact .refl
    | tail before step ih =>
        exact ih.tail (nstep_fires nodup restricted step (keep before).1 (keep before).2)

/-- **Call by need on the ordinary step.** Runs of translated firings of the by-need schemas reach
configurations representing exactly the rows of the machine's runs. -/
theorem need_on_step {L : List ℕ} (nodup : L.Nodup) (restricted : RangeRestricted prog) {c : Conf}
    (inside : Inside L c) (wf : Wf c) (W : Multiset Sx) :
    (∃ q : Config × ℕ, Relation.ReflTransGen (Translated (nschema prog)) (initial (rowsList L c), 1) q ∧
        Represents q.1 W q.2) ↔
      ∃ c', Relation.ReflTransGen (NStep prog) c c' ∧ W = rowsOf L c' := by
  rw [← execution_iff (nschema_wellFormed restricted), rowsList_coe]
  exact need_rows_iff nodup restricted inside wf W

theorem cells_agree {L : List ℕ} {H H' : Heap} (same : cells L H = cells L H') : ∀ ℓ ∈ L, H ℓ = H' ℓ := by
  intro ℓ inL
  have member : cellRow ℓ (H ℓ) ∈ cells L H' := by
    rw [← same]
    exact Multiset.mem_coe.mpr (List.mem_map.mpr ⟨ℓ, inL, rfl⟩)
  obtain ⟨ℓ', -, eq⟩ := cell_mem member
  simp only [cellRow, tup_inj, List.cons.injEq, and_true, true_and] at eq
  have sameLoc := nat_inj eq.1
  subst sameLoc
  exact encCell_inj eq.2

/-- **By-need evaluation on the ordinary step, both ways**: a by-need evaluation is a run of the
step representing its final rows, and every run of the step representing the final rows of a
value is a by-need evaluation, whose final heap agrees on the listed locations. -/
theorem need_eval_on_step {L : List ℕ} (nodup : L.Nodup) (restricted : RangeRestricted prog) {e : NEx}
    {H : Heap} (inside : Inside L (.ev e, [], H)) {v : Sx} {H' : Heap} :
    (NEval prog H e H' v → ∃ q : Config × ℕ,
      Relation.ReflTransGen (Translated (nschema prog)) (initial (rowsList L (.ev e, [], H)), 1) q ∧
        Represents q.1 (rowsOf L (.ret v, [], H')) q.2) ∧
    ((∃ q : Config × ℕ,
      Relation.ReflTransGen (Translated (nschema prog)) (initial (rowsList L (.ev e, [], H)), 1) q ∧
        Represents q.1 (rowsOf L (.ret v, [], H')) q.2) →
      ∃ H'', NEval prog H e H'' v ∧ ∀ ℓ ∈ L, H'' ℓ = H' ℓ) := by
  have onStep := need_on_step nodup restricted inside (wf_initial e H)
  constructor
  · intro eval
    exact (onStep _).mpr ⟨_, eval_runs eval [], rfl⟩
  · intro reached
    obtain ⟨⟨ctl, K, H''⟩, run, same⟩ := (onStep _).mp reached
    obtain ⟨rfl, rfl, cellsSame⟩ := thread_split same
    exact ⟨H'', runs_eval run, cells_agree cellsSame⟩

#print axioms nstep_fires
#print axioms fires_nstep
#print axioms need_rows_iff
#print axioms need_on_step
#print axioms inside_step
#print axioms cells_agree
#print axioms need_eval_on_step

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramNeed
