import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramNested

/-!
# Controls for nested calls

Each control is a machine run, carried to the ordinary step by `nested_execution` and to the
reference semantics in evaluation contexts by `kruns_unload`.

* **A nested call is evaluated** (`nested_evaluated`, `nested_evaluated_on_step`,
  `nested_evaluated_reference`): with `(= (g a) b)` and `(= (f $x) (out $x))`, the expression
  `(f (g a))` (both calls evaluated) reaches the value `(out b)`: the inner call is answered first,
  and its answer is the outer call's argument. Each answered call cites version `1`.
* **Two nested calls multiply their answers** (`answers_multiply`, `answers_distinct`,
  `answers_multiply_on_step`): with `(= (c) x)` and `(= (c) y)`, the expression `((c) (c))` reaches
  each of the four values `(x x)`, `(x y)`, `(y x)`, `(y y)`, one per pair of equation choices, and
  the four are distinct.
* **A nested call that matches nothing stays** (`unmatched_inner_reached`, `unmatched_inner_stuck`,
  `unmatched_inner_stays_on_step`): in `(f (g c))`, the inner call `(g c)` matches no equation. The
  run reaches the call `(g c)` under the frames of `(f [])`, and there it has no machine step, and
  the configuration representing it on the step admits no translated firing. The call is not an
  error and is not dropped: it stays, waiting, in its context.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramNested.Controls

open Mettapedia.Logic.LP
open ProgramRows ProgramTranslation ProgramEquationsOpen ProgramEquations
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramNested

/-! ## Ground data -/

def sf : Sx := .sym 150
def sg : Sx := .sym 151
def sa : Sx := .sym 152
def sb : Sx := .sym 153
def sc : Sx := .sym 154
def sout : Sx := .sym 155
def scc : Sx := .sym 156
def sx : Sx := .sym 157
def sy : Sx := .sym 158

/-- Held ground data. -/
def gv (s : Sx) : Ex := .val (embed s)

/-- The call `(h e)`: the pair of the head and the argument, evaluated, then called. -/
def callOf (h : Sx) (e : Ex) : Ex := .call (.pair (gv h) e)

theorem frames_fixed (θ : Subst rows) (K : List Frame) (ground : ∀ f ∈ K, f.subst θ = f) :
    K.map (Frame.subst θ) = K := by
  induction K with
  | nil => rfl
  | cons f K ih =>
      rw [List.map_cons, ground f List.mem_cons_self, ih fun g h => ground g (List.mem_cons_of_mem _ h)]

theorem right_fixed (θ : Subst rows) (s : Sx) : (Frame.right (embed s)).subst θ = .right (embed s) := by
  rw [Frame.subst, apply_embed]

theorem arg_fixed (θ : Subst rows) : Frame.arg.subst θ = Frame.arg := rfl

theorem rows_fixed (θ : Subst rows) (F : Multiset SRow) (ground : ∀ s ∈ F, s.subst θ = s) :
    F.map (SRow.subst θ) = F :=
  (Multiset.map_congr rfl ground).trans (Multiset.map_id' F)

theorem Ex.subst_id : ∀ e : Ex, e.subst (Subst.id rows) = e
  | .val t => by rw [Ex.subst, Subst.applyTerm_id]
  | .pair a b => by rw [Ex.subst, Ex.subst_id a, Ex.subst_id b]
  | .call a => by rw [Ex.subst, Ex.subst_id a]

theorem Frame.subst_id : ∀ f : Frame, f.subst (Subst.id rows) = f
  | .left b => by rw [Frame.subst, Ex.subst_id]
  | .right v => by rw [Frame.subst, Subst.applyTerm_id]
  | .arg => rfl

theorem SRow.subst_id : ∀ s : SRow, s.subst (Subst.id rows) = s
  | .ev e K => by rw [SRow.subst, Ex.subst_id, frames_fixed _ K fun f _ => Frame.subst_id f]
  | .ret v K => by rw [SRow.subst, Subst.applyTerm_id, frames_fixed _ K fun f _ => Frame.subst_id f]
  | .ap w K => by rw [SRow.subst, Subst.applyTerm_id, frames_fixed _ K fun f _ => Frame.subst_id f]
  | .version _ => rfl
  | .citation _ => rfl
  | .redef _ => rfl
  | .finished => rfl
  | .data k t => by rw [SRow.subst, Subst.applyTerm_id]

/-! ## Bounds -/

theorem bnode {n : ℕ} {a b : Tm} (ha : Bounded n a) (hb : Bounded n b) : Bounded n (node a b) :=
  fun v hv => (mem_freeVars_node.mp hv).elim (ha v) (hb v)

theorem btag {n k : ℕ} {t : Tm} (h : Bounded n t) : Bounded n (tagged k t) := fun v hv =>
  h v (by rwa [freeVars_tagged] at hv)

theorem bconst (n k : ℕ) : Bounded n (.const k) := fun v hv => by simp [Term.freeVars] at hv

/-- An expression whose data are ground. -/
def GroundEx : Ex → Prop
  | .val t => ∃ s, t = embed s
  | .pair a b => GroundEx a ∧ GroundEx b
  | .call a => GroundEx a

theorem GroundEx.bounded (n : ℕ) : ∀ {e : Ex}, GroundEx e → Bounded n (encE e)
  | .val _, ⟨s, rfl⟩ => btag (embed_bounded n s)
  | .pair _ _, ⟨ga, gb⟩ => btag (bnode (GroundEx.bounded n ga) (GroundEx.bounded n gb))
  | .call _, ga => btag (GroundEx.bounded n ga)

theorem start_good (e : Ex) (u : ℕ) : ∀ s ∈ [SRow.ev e [], .version u], s.Good := by
  intro s h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl <;> trivial

theorem start_bounded {e : Ex} (ground : GroundEx e) (u : ℕ) :
    ∀ s ∈ [SRow.ev e [], .version u], Bounded 1 s.enc := by
  intro s h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl
  · exact btag (bnode (ground.bounded 1) (bconst 1 143))
  · exact btag (bconst 1 u)

/-! ## A nested call is evaluated -/

/-- `(= (g a) b)`. -/
def eqG : NEquation := ⟨.cell (.sym 151) (.sym 152), .val (.sym 153)⟩
/-- `(= (f $x) (out $x))`. -/
def eqF : NEquation := ⟨.cell (.sym 150) (.var 0), .val (.cell (.sym 155) (.var 0))⟩

def defsFG : Defs := fun _ => [eqG, eqF]

/-- `(f (g z))`, both calls evaluated. -/
def nestedExpr (z : Sx) : Ex := callOf sf (callOf sg (gv z))

theorem nestedExpr_ground (z : Sx) : GroundEx (nestedExpr z) :=
  ⟨⟨sf, rfl⟩, ⟨⟨sg, rfl⟩, ⟨z, rfl⟩⟩⟩

/-- The frames of `(f [])`. -/
def outerFrames : List Frame := [.right (embed sf), .arg]

/-- **From `(f (g z))`, eleven administrative steps reach the inner call `(g z)` in the frames of
`(f [])`.** -/
theorem inner_run (defs : Defs) (z : Sx) (F : Multiset SRow) (n : ℕ) :
    Relation.ReflTransGen (KStep defs) (.ev (nestedExpr z) [] ::ₘ F, n)
      (.ap (embed (.cell sg z)) outerFrames ::ₘ F, n + 11) := by
  have s1 := KStep.call (defs := defs) (.pair (gv sf) (callOf sg (gv z))) [] F n
  have s2 := KStep.pair (defs := defs) (gv sf) (callOf sg (gv z)) [.arg] F (n + 1)
  have s3 := KStep.val (defs := defs) (embed sf) [.left (callOf sg (gv z)), .arg] F (n + 2)
  have s4 := KStep.left (defs := defs) (embed sf) (callOf sg (gv z)) [.arg] F (n + 3)
  have s5 := KStep.call (defs := defs) (.pair (gv sg) (gv z)) outerFrames F (n + 4)
  have s6 := KStep.pair (defs := defs) (gv sg) (gv z) (.arg :: outerFrames) F (n + 5)
  have s7 := KStep.val (defs := defs) (embed sg) (.left (gv z) :: .arg :: outerFrames) F (n + 6)
  have s8 := KStep.left (defs := defs) (embed sg) (gv z) (.arg :: outerFrames) F (n + 7)
  have s9 := KStep.val (defs := defs) (embed z) (.right (embed sg) :: .arg :: outerFrames) F (n + 8)
  have s10 := KStep.right (defs := defs) (embed sg) (embed z) (.arg :: outerFrames) F (n + 9)
  have s11 := KStep.arg (defs := defs) (node (embed sg) (embed z)) outerFrames F (n + 10)
  exact ((((((((((Relation.ReflTransGen.single s1).tail s2).tail s3).tail s4).tail s5).tail s6).tail
    s7).tail s8).tail s9).tail s10).tail s11

theorem mgu_ground (n : ℕ) (p : Pat) (s : Sx) (same : p.at n = embed s) :
    IsMGU [(p.at n, embed s)] (Subst.id rows) :=
  isMGU_id_of_eq fun e member => by
    rw [List.mem_singleton] at member
    rw [member]
    exact same

/-- **A nested call is evaluated**: `(f (g a))` reaches the value `(out b)`, citing version `1`
for each of its two answered calls. -/
theorem nested_evaluated :
    Relation.ReflTransGen (KStep defsFG) (.ev (nestedExpr sa) [] ::ₘ .version 1 ::ₘ 0, 1)
      (.ret (node (embed sout) (embed sb)) [] ::ₘ .citation 1 ::ₘ .version 1 ::ₘ .citation 1 ::ₘ 0, 18) := by
  have first := inner_run defsFG sa (.version 1 ::ₘ 0) 1
  -- the inner call `(g a)` is answered `b`
  have s12 := KStep.apply (defs := defsFG) 1 ⟨0, by decide⟩ (embed (.cell sg sa)) outerFrames 0 12
    (Subst.id rows) (mgu_ground 12 eqG.lhs (.cell sg sa) rfl)
  rw [frames_fixed _ _ (by
      intro f h
      simp only [outerFrames, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl
      · exact right_fixed _ sf
      · rfl),
    Multiset.map_zero] at s12
  have rhs12 : (((defsFG 1).get ⟨0, by decide⟩).rhs.at 12).subst (Subst.id rows) = gv sb := rfl
  rw [rhs12] at s12
  have s13 := KStep.val (defs := defsFG) (embed sb) outerFrames (.citation 1 ::ₘ .version 1 ::ₘ 0) 13
  have s14 := KStep.right (defs := defsFG) (embed sf) (embed sb) [.arg]
    (.citation 1 ::ₘ .version 1 ::ₘ 0) 14
  have s15 := KStep.arg (defs := defsFG) (node (embed sf) (embed sb)) []
    (.citation 1 ::ₘ .version 1 ::ₘ 0) 15
  -- the outer call `(f b)` is answered `(out b)`
  have mgu16 : IsMGU [(eqF.lhs.at 16, node (embed sf) (embed sb))] (matcher 16 [embed sb]) := by
    have := matcher_isMGU (n := 16) (vals := [embed sb]) (fun t h => by
      rw [List.mem_singleton] at h
      rw [h]
      exact embed_bounded 16 sb) (p := eqF.lhs) (by decide) (by decide)
    exact this
  have s16 := KStep.apply (defs := defsFG) 1 ⟨1, by decide⟩ (node (embed sf) (embed sb)) []
    (.citation 1 ::ₘ 0) 16 (matcher 16 [embed sb]) mgu16
  have rhs16 : (((defsFG 1).get ⟨1, by decide⟩).rhs.at 16).subst (matcher 16 [embed sb]) =
      .val (node (embed sout) (embed sb)) := by
    show Ex.val ((matcher 16 [embed sb]).applyTerm ((Pat.cell (.sym 155) (.var 0)).at 16)) = _
    rw [matcher_at _ (by decide)]
    rfl
  rw [rhs16, List.map_nil, rows_fixed _ _ (by
    intro s h
    simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at h
    rw [h]
    rfl)] at s16
  have s17 := KStep.val (defs := defsFG) (node (embed sout) (embed sb)) []
    (.citation 1 ::ₘ .version 1 ::ₘ .citation 1 ::ₘ 0) 17
  have reorder : SRow.ap (node (embed sf) (embed sb)) [] ::ₘ .citation 1 ::ₘ .version 1 ::ₘ 0 =
      .ap (node (embed sf) (embed sb)) [] ::ₘ .version 1 ::ₘ .citation 1 ::ₘ 0 := by
    rw [Multiset.cons_swap (SRow.citation 1)]
  rw [reorder] at s15
  exact (((((first.tail s12).tail s13).tail s14).tail s15).tail s16).tail s17

/-- **On the step**: a run of translated firings from the initial rows reaches a configuration
representing the value `(out b)`. -/
theorem nested_evaluated_on_step :
    ∃ D, Relation.ReflTransGen (Translated (kschema defsFG))
      (openInitial ([SRow.ev (nestedExpr sa) [], .version 1].map SRow.enc), 1) (D, 18) ∧
      ORepresents D ((.ret (node (embed sout) (embed sb)) [] ::ₘ .citation 1 ::ₘ .version 1 ::ₘ
        .citation 1 ::ₘ 0 : Multiset SRow).map SRow.enc) 18 :=
  (nested_execution defsFG _ (start_good _ 1) (start_bounded (nestedExpr_ground sa) 1) _ 18).1
    nested_evaluated

/-- **In evaluation contexts**: the reference semantics reaches the value `(out b)` from the thread
`(f (g a))`. -/
theorem nested_evaluated_reference :
    ∃ m, m ≤ 18 ∧ Relation.ReflTransGen (CStep defsFG)
      (thread (encE (nestedExpr sa)) ::ₘ unloadAll (.version 1 ::ₘ 0), 1)
      (thread (encE (.val (node (embed sout) (embed sb)))) ::ₘ unloadAll (.citation 1 ::ₘ .version 1 ::ₘ
        .citation 1 ::ₘ 0), m) :=
  halted_is_value nested_evaluated

/-! ## Two nested calls multiply their answers -/

/-- `(= (c) x)` and `(= (c) y)`. -/
def eqX : NEquation := ⟨.sym 156, .val (.sym 157)⟩
def eqY : NEquation := ⟨.sym 156, .val (.sym 158)⟩

def defsC : Defs := fun _ => [eqX, eqY]

/-- The answer of the `j`-th equation. -/
def pick (j : Fin 2) : Sx := if j = 0 then sx else sy

theorem rhs_pick (n : ℕ) (j : Fin 2) :
    (((defsC 1).get ⟨j, j.2⟩).rhs.at n).subst (Subst.id rows) = gv (pick j) := by
  fin_cases j <;> rfl

/-- The nullary call `(c)`. -/
def cCall : Ex := .call (gv scc)

/-- `((c) (c))`: a pair of two calls. -/
def twoCalls : Ex := .pair cCall cCall

theorem twoCalls_ground : GroundEx twoCalls := ⟨⟨scc, rfl⟩, ⟨scc, rfl⟩⟩

/-- A call `(c)` under frames `K` is answered by the `j`-th equation, in five steps. -/
theorem c_run (j : Fin 2) (K : List Frame) (F : Multiset SRow) (n : ℕ) :
    Relation.ReflTransGen (KStep defsC) (.ev cCall K ::ₘ .version 1 ::ₘ F, n)
      (.ret (embed (pick j)) K ::ₘ .citation 1 ::ₘ .version 1 ::ₘ F, n + 5) := by
  have s1 := KStep.call (defs := defsC) (gv scc) K (.version 1 ::ₘ F) n
  have s2 := KStep.val (defs := defsC) (embed scc) (.arg :: K) (.version 1 ::ₘ F) (n + 1)
  have s3 := KStep.arg (defs := defsC) (embed scc) K (.version 1 ::ₘ F) (n + 2)
  have s4 := KStep.apply (defs := defsC) 1 ⟨j, j.2⟩ (embed scc) K F (n + 3) (Subst.id rows)
    (mgu_ground (n + 3) _ scc (by fin_cases j <;> rfl))
  rw [rhs_pick, frames_fixed _ K fun f _ => Frame.subst_id f, rows_fixed _ F fun s _ => SRow.subst_id s]
    at s4
  have s5 := KStep.val (defs := defsC) (embed (pick j)) K (.citation 1 ::ₘ .version 1 ::ₘ F) (n + 4)
  exact ((((Relation.ReflTransGen.single s1).tail s2).tail s3).tail s4).tail s5

/-- **Two nested calls multiply their answers**: for each pair of equation choices, `((c) (c))`
reaches the value `(xᵢ xⱼ)` of that pair. -/
theorem answers_multiply (j₁ j₂ : Fin 2) :
    Relation.ReflTransGen (KStep defsC) (.ev twoCalls [] ::ₘ .version 1 ::ₘ 0, 1)
      (.ret (node (embed (pick j₁)) (embed (pick j₂))) [] ::ₘ .citation 1 ::ₘ .citation 1 ::ₘ .version 1 ::ₘ 0,
        14) := by
  have s1 := KStep.pair (defs := defsC) cCall cCall [] (.version 1 ::ₘ 0) 1
  have firstCall := c_run j₁ [.left cCall] 0 2
  have s7 := KStep.left (defs := defsC) (embed (pick j₁)) cCall [] (.citation 1 ::ₘ .version 1 ::ₘ 0) 7
  have reorder : SRow.ev cCall [.right (embed (pick j₁))] ::ₘ .citation 1 ::ₘ .version 1 ::ₘ 0 =
      .ev cCall [.right (embed (pick j₁))] ::ₘ .version 1 ::ₘ .citation 1 ::ₘ 0 := by
    rw [Multiset.cons_swap (SRow.citation 1)]
  rw [reorder] at s7
  have secondCall := c_run j₂ [.right (embed (pick j₁))] (.citation 1 ::ₘ 0) 8
  have s13 := KStep.right (defs := defsC) (embed (pick j₁)) (embed (pick j₂)) []
    (.citation 1 ::ₘ .version 1 ::ₘ .citation 1 ::ₘ 0) 13
  have final : SRow.ret (node (embed (pick j₁)) (embed (pick j₂))) [] ::ₘ .citation 1 ::ₘ .version 1 ::ₘ
      .citation 1 ::ₘ 0 =
      .ret (node (embed (pick j₁)) (embed (pick j₂))) [] ::ₘ .citation 1 ::ₘ .citation 1 ::ₘ .version 1 ::ₘ 0 := by
    rw [Multiset.cons_swap (SRow.version 1) (SRow.citation 1)]
  rw [final] at s13
  exact ((((Relation.ReflTransGen.single s1).trans firstCall).tail s7).trans secondCall).tail s13

/-- **The four answers are distinct**: each pair of choices gives its own value. -/
theorem answers_distinct {j₁ j₂ k₁ k₂ : Fin 2}
    (same : node (embed (pick j₁)) (embed (pick j₂)) = node (embed (pick k₁)) (embed (pick k₂))) :
    j₁ = k₁ ∧ j₂ = k₂ := by
  rw [node_inj] at same
  have one := embed_injective same.1
  have two := embed_injective same.2
  revert one two
  fin_cases j₁ <;> fin_cases j₂ <;> fin_cases k₁ <;> fin_cases k₂ <;> decide

theorem answers_multiply_on_step (j₁ j₂ : Fin 2) :
    ∃ D, Relation.ReflTransGen (Translated (kschema defsC))
      (openInitial ([SRow.ev twoCalls [], .version 1].map SRow.enc), 1) (D, 14) ∧
      ORepresents D ((.ret (node (embed (pick j₁)) (embed (pick j₂))) [] ::ₘ .citation 1 ::ₘ .citation 1 ::ₘ
        .version 1 ::ₘ 0 : Multiset SRow).map SRow.enc) 14 :=
  (nested_execution defsC _ (start_good _ 1) (start_bounded twoCalls_ground 1) _ 14).1
    (answers_multiply j₁ j₂)

/-! ## A nested call that matches nothing stays -/

/-- The stuck configuration: the inner call `(g c)` in the frames of `(f [])`. -/
def stuckRows : Multiset SRow := .ap (embed (.cell sg sc)) outerFrames ::ₘ .version 1 ::ₘ 0

theorem unmatched_inner_reached :
    Relation.ReflTransGen (KStep defsFG) (.ev (nestedExpr sc) [] ::ₘ .version 1 ::ₘ 0, 1) (stuckRows, 12) :=
  inner_run defsFG sc _ 1

/-- `(g c)` unifies with neither left-hand side. -/
theorem no_equation_unifies (n : ℕ) : ∀ e ∈ defsFG 1, ∀ δ : Subst rows,
    ¬ Unifies δ [(e.lhs.at n, embed (.cell sg sc))] := by
  intro e member δ unifies
  have same := unifies _ List.mem_cons_self
  simp only [defsFG, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · change δ.applyTerm (node (.const 151) (.const 152)) = δ.applyTerm (node (.const 151) (.const 154)) at same
    rw [apply_node, apply_node, node_inj] at same
    exact absurd same.2 (by simp)
  · change δ.applyTerm (node (.const 150) (.var (n, 0))) = δ.applyTerm (node (.const 151) (.const 154)) at same
    rw [apply_node, apply_node, node_inj] at same
    exact absurd same.1 (by simp)

/-- **There it has no machine step.** -/
theorem unmatched_inner_stuck (n : ℕ) (s' : Multiset SRow × ℕ) : ¬ KStep defsFG (stuckRows, n) s' := by
  intro step
  have mem : ∀ {r : SRow} {F : Multiset SRow}, r ::ₘ F = stuckRows →
      r = .ap (embed (.cell sg sc)) outerFrames ∨ r = .version 1 := fun h => by
    have : _ ∈ stuckRows := h ▸ Multiset.mem_cons_self _ _
    simpa [stuckRows] using this
  generalize hs : (stuckRows, n) = start at step
  cases step with
  | val t K F m => obtain h | h := mem (Prod.mk.inj hs).1.symm <;> cases h
  | pair a b K F m => obtain h | h := mem (Prod.mk.inj hs).1.symm <;> cases h
  | call a K F m => obtain h | h := mem (Prod.mk.inj hs).1.symm <;> cases h
  | left v b K F m => obtain h | h := mem (Prod.mk.inj hs).1.symm <;> cases h
  | right v w K F m => obtain h | h := mem (Prod.mk.inj hs).1.symm <;> cases h
  | arg w K F m => obtain h | h := mem (Prod.mk.inj hs).1.symm <;> cases h
  | redefine u u' F m => obtain h | h := mem (Prod.mk.inj hs).1.symm <;> cases h
  | apply u j w K F m θ mgu =>
      obtain ⟨rows, rfl⟩ := Prod.mk.inj hs
      obtain h | h := mem rows.symm
      · cases h
        have uIn : SRow.version u ∈ stuckRows := by
          rw [rows]
          exact Multiset.mem_cons_of_mem (Multiset.mem_cons_self _ _)
        have hu : u = 1 := by simpa [stuckRows] using uIn
        subst hu
        exact no_equation_unifies n _ (List.get_mem _ j) θ mgu.unifies
      · cases h

theorem stuck_good : ∀ s ∈ stuckRows, s.Good := by
  intro s h
  simp only [stuckRows, Multiset.mem_cons, Multiset.notMem_zero, or_false] at h
  rcases h with rfl | rfl <;> trivial

/-- **On the step the call stays**: a run of translated firings reaches a configuration
representing the waiting call, and that configuration admits no translated firing. -/
theorem unmatched_inner_stays_on_step :
    ∃ D, Relation.ReflTransGen (Translated (kschema defsFG))
      (openInitial ([SRow.ev (nestedExpr sc) [], .version 1].map SRow.enc), 1) (D, 12) ∧
      ORepresents D (stuckRows.map SRow.enc) 12 ∧ ∀ q, ¬ Translated (kschema defsFG) (D, 12) q := by
  obtain ⟨D, run, rep⟩ := (nested_execution defsFG _ (start_good _ 1)
    (start_bounded (nestedExpr_ground sc) 1) _ 12).1 unmatched_inner_reached
  refine ⟨D, run, rep, fun q firing => ?_⟩
  obtain ⟨Ws', step, -⟩ := nested_complete rep stuck_good firing
  exact unmatched_inner_stuck 12 _ step

#print axioms inner_run
#print axioms nested_evaluated
#print axioms nested_evaluated_on_step
#print axioms nested_evaluated_reference
#print axioms c_run
#print axioms answers_multiply
#print axioms answers_distinct
#print axioms answers_multiply_on_step
#print axioms unmatched_inner_reached
#print axioms no_equation_unifies
#print axioms unmatched_inner_stuck
#print axioms unmatched_inner_stays_on_step

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramNested.Controls
