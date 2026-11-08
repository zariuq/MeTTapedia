import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramNeedShare
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramCompiledInterpreter

/-!
# Call by need on the step: the thread row and one shared row per heap cell

The by-need machine as row rewriting (R82's `Schema`s): the configuration is one thread row and one
row per heap cell of a fixed list of locations (`rowsOf`). There is one schema per machine rule, and
one per equation:

- a bind takes the empty cell row and makes the thunk row;
- a demand of a thunk takes its row and makes the busy row, pushing the update marker;
- returning to the marker takes the busy row and makes the value row;
- **a demand of a value reads the value row**: the schema reads it and does not take it, so the row
  stays, shared by every later demand.

- `nstep_fires`, `fires_nstep`: each machine step is one firing of its schema on the rows, and each
  firing of a schema on the rows of a configuration is one machine step.
- `need_rows_iff`: source row rewriting from the rows of a configuration reaches exactly the rows of
  its machine runs.
- `need_on_step`: **the ordinary step's translated firings reach configurations representing exactly
  the rows of the machine's runs**, by R82's `execution_iff`.

Hypotheses: the locations are distinct and include every location the expression binds or demands
(`Inside`); the program's equations are range restricted.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramNeed

open ProgramRows ProgramTranslation ProgramCompiled
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramNested (EPat NEquation)

variable {prog : Program}

/-! ## Encodings -/

def encX : NEx → Sx
  | .val t => tup 200 [t]
  | .loc ℓ => tup 201 [nat ℓ]
  | .pair a b => tup 202 [encX a, encX b]
  | .call a => tup 203 [encX a]
  | .bind ℓ a b => tup 204 [nat ℓ, encX a, encX b]

def encF : Frame → Sx
  | .left b => tup 210 [encX b]
  | .right v => tup 211 [v]
  | .arg => tup 212 []
  | .update ℓ => tup 213 [nat ℓ]

def encK (K : List Frame) : Sx := codeOf (K.map encF)

def encC : Control → Sx
  | .ev e => tup 220 [encX e]
  | .ret v => tup 221 [v]
  | .ap w => tup 222 [w]

def encCell : Cell → Sx
  | .empty => tup 230 []
  | .thunk e => tup 231 [encX e]
  | .busy => tup 232 []
  | .value v => tup 233 [v]

/-- The thread row. -/
def thr (c : Control) (K : List Frame) : Sx := tup 240 [encC c, encK K]

/-- The row of one heap cell. -/
def cellRow (ℓ : ℕ) (c : Cell) : Sx := tup 241 [nat ℓ, encCell c]

/-- The cell rows of the locations `L`. -/
def cells (L : List ℕ) (H : Heap) : Multiset Sx := (L.map fun ℓ => cellRow ℓ (H ℓ) : List Sx)

/-- **The rows of a configuration**: its thread, and the cells of `L`. -/
def rowsOf (L : List ℕ) (c : Conf) : Multiset Sx := thr c.1 c.2.1 ::ₘ cells L c.2.2

/-! ## Injectivity -/

theorem nat_inj : ∀ {a b : ℕ}, nat a = nat b → a = b
  | 0, 0, _ => rfl
  | 0, _ + 1, h => by simp [nat, tup_inj] at h
  | _ + 1, 0, h => by simp [nat, tup_inj] at h
  | a + 1, b + 1, h => by
      simp only [nat, tup_inj, List.cons.injEq, and_true, true_and] at h
      rw [nat_inj h]

theorem encX_inj : ∀ {a b : NEx}, encX a = encX b → a = b
  | .val _, .val _, h => by simp only [encX, tup_inj, List.cons.injEq, and_true, true_and] at h; rw [h]
  | .loc _, .loc _, h => by
      simp only [encX, tup_inj, List.cons.injEq, and_true, true_and] at h; rw [nat_inj h]
  | .pair _ _, .pair _ _, h => by
      simp only [encX, tup_inj, List.cons.injEq, and_true, true_and] at h
      rw [encX_inj h.1, encX_inj h.2]
  | .call _, .call _, h => by
      simp only [encX, tup_inj, List.cons.injEq, and_true, true_and] at h; rw [encX_inj h]
  | .bind _ _ _, .bind _ _ _, h => by
      simp only [encX, tup_inj, List.cons.injEq, and_true, true_and] at h
      rw [nat_inj h.1, encX_inj h.2.1, encX_inj h.2.2]
  | .val _, .loc _, h | .val _, .pair _ _, h | .val _, .call _, h | .val _, .bind _ _ _, h
  | .loc _, .val _, h | .loc _, .pair _ _, h | .loc _, .call _, h | .loc _, .bind _ _ _, h
  | .pair _ _, .val _, h | .pair _ _, .loc _, h | .pair _ _, .call _, h | .pair _ _, .bind _ _ _, h
  | .call _, .val _, h | .call _, .loc _, h | .call _, .pair _ _, h | .call _, .bind _ _ _, h
  | .bind _ _ _, .val _, h | .bind _ _ _, .loc _, h | .bind _ _ _, .pair _ _, h | .bind _ _ _, .call _, h => by
      simp [encX, tup_inj] at h

theorem encF_inj : ∀ {f g : Frame}, encF f = encF g → f = g
  | .left _, .left _, h => by
      simp only [encF, tup_inj, List.cons.injEq, and_true, true_and] at h; rw [encX_inj h]
  | .right _, .right _, h => by simp only [encF, tup_inj, List.cons.injEq, and_true, true_and] at h; rw [h]
  | .arg, .arg, _ => rfl
  | .update _, .update _, h => by
      simp only [encF, tup_inj, List.cons.injEq, and_true, true_and] at h; rw [nat_inj h]
  | .left _, .right _, h | .left _, .arg, h | .left _, .update _, h
  | .right _, .left _, h | .right _, .arg, h | .right _, .update _, h
  | .arg, .left _, h | .arg, .right _, h | .arg, .update _, h
  | .update _, .left _, h | .update _, .right _, h | .update _, .arg, h => by
      simp [encF, tup_inj] at h

theorem encK_inj : ∀ {K K' : List Frame}, encK K = encK K' → K = K'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [encK, codeOf, knil, kons, tup_inj] at h
  | _ :: _, [], h => by simp [encK, codeOf, knil, kons, tup_inj] at h
  | f :: K, g :: K', h => by
      simp only [encK, List.map_cons, codeOf, kons_inj] at h
      rw [encF_inj h.1, encK_inj (K := K) (K' := K') h.2]

theorem encC_inj : ∀ {c d : Control}, encC c = encC d → c = d
  | .ev _, .ev _, h => by
      simp only [encC, tup_inj, List.cons.injEq, and_true, true_and] at h; rw [encX_inj h]
  | .ret _, .ret _, h => by simp only [encC, tup_inj, List.cons.injEq, and_true, true_and] at h; rw [h]
  | .ap _, .ap _, h => by simp only [encC, tup_inj, List.cons.injEq, and_true, true_and] at h; rw [h]
  | .ev _, .ret _, h | .ev _, .ap _, h | .ret _, .ev _, h | .ret _, .ap _, h | .ap _, .ev _, h
  | .ap _, .ret _, h => by simp [encC, tup_inj] at h

theorem encCell_inj : ∀ {c d : Cell}, encCell c = encCell d → c = d
  | .empty, .empty, _ => rfl
  | .thunk _, .thunk _, h => by
      simp only [encCell, tup_inj, List.cons.injEq, and_true, true_and] at h; rw [encX_inj h]
  | .busy, .busy, _ => rfl
  | .value _, .value _, h => by simp only [encCell, tup_inj, List.cons.injEq, and_true, true_and] at h; rw [h]
  | .empty, .thunk _, h | .empty, .busy, h | .empty, .value _, h
  | .thunk _, .empty, h | .thunk _, .busy, h | .thunk _, .value _, h
  | .busy, .empty, h | .busy, .thunk _, h | .busy, .value _, h
  | .value _, .empty, h | .value _, .thunk _, h | .value _, .busy, h => by
      simp [encCell, tup_inj] at h

theorem thr_inj {c d : Control} {K K' : List Frame} (same : thr c K = thr d K') : c = d ∧ K = K' := by
  simp only [thr, tup_inj, List.cons.injEq, and_true, true_and] at same
  exact ⟨encC_inj same.1, encK_inj same.2⟩

/-! ## Cells -/

theorem cell_mem {L : List ℕ} {H : Heap} {x : Sx} (member : x ∈ cells L H) : ∃ ℓ ∈ L, x = cellRow ℓ (H ℓ) := by
  obtain ⟨ℓ, mem, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp member)
  exact ⟨ℓ, mem, rfl⟩

theorem thr_not_cell {c : Control} {K : List Frame} {ℓ : ℕ} {x : Cell} : thr c K ≠ cellRow ℓ x := by
  intro same
  simp [thr, cellRow, tup_inj] at same

/-- The thread row is the thread row: a row of thread shape among the rows is the thread. -/
theorem thread_split {L : List ℕ} {c : Control} {K : List Frame} {H : Heap} {d : Control} {K' : List Frame}
    {G : Multiset Sx} (same : thr c K ::ₘ cells L H = thr d K' ::ₘ G) : c = d ∧ K = K' ∧ G = cells L H := by
  rcases Multiset.cons_eq_cons.mp same with ⟨heads, tails⟩ | ⟨_, rest, inCells, _⟩
  · obtain ⟨rfl, rfl⟩ := thr_inj heads
    exact ⟨rfl, rfl, tails.symm⟩
  · have member : thr d K' ∈ cells L H := by rw [inCells]; exact Multiset.mem_cons_self _ _
    obtain ⟨ℓ, -, eq⟩ := cell_mem member
    exact (thr_not_cell eq).elim

/-- **Splitting off one cell.** -/
theorem cells_split {L : List ℕ} (nodup : L.Nodup) {ℓ : ℕ} (inL : ℓ ∈ L) (H : Heap) (c : Cell) :
    cells L H = cellRow ℓ (H ℓ) ::ₘ cells (L.erase ℓ) H ∧
      cells L (H.set ℓ c) = cellRow ℓ c ::ₘ cells (L.erase ℓ) H := by
  have perm := List.perm_cons_erase inL
  have outside : ∀ ℓ' ∈ L.erase ℓ, ℓ' ≠ ℓ := fun ℓ' member same => by
    subst same
    exact (List.Nodup.not_mem_erase nodup) member
  constructor
  · unfold cells
    rw [Multiset.coe_eq_coe.mpr (perm.map _)]
    rfl
  · unfold cells
    rw [Multiset.coe_eq_coe.mpr (perm.map _), List.map_cons, Heap.set_same]
    rw [← Multiset.cons_coe]
    congr 2
    exact List.map_congr_left fun ℓ' member => by rw [Heap.set_other _ _ (outside ℓ' member)]

/-- A cell row among the cells is the cell of its location. -/
theorem cell_split {L : List ℕ} (nodup : L.Nodup) {H : Heap} {ℓ : ℕ} {x : Cell} {F : Multiset Sx}
    (same : cells L H = cellRow ℓ x ::ₘ F) : ℓ ∈ L ∧ x = H ℓ ∧ F = cells (L.erase ℓ) H := by
  have member : cellRow ℓ x ∈ cells L H := by rw [same]; exact Multiset.mem_cons_self _ _
  obtain ⟨ℓ', inL, eq⟩ := cell_mem member
  simp only [cellRow, tup_inj, List.cons.injEq, and_true, true_and] at eq
  have sameLoc := nat_inj eq.1
  subst sameLoc
  have sameCell := encCell_inj eq.2
  subst sameCell
  refine ⟨inL, rfl, ?_⟩
  rw [(cells_split nodup inL H (H ℓ)).1] at same
  exact (Multiset.cons_inj_right _).mp same.symm

/-! ## The schemas -/

/-- Pattern builders. -/
def thrP (c k : Pat) : Pat := ptup 240 [c, k]
def evP (e : Pat) : Pat := ptup 220 [e]
def retP (v : Pat) : Pat := ptup 221 [v]
def apP (w : Pat) : Pat := ptup 222 [w]
def consP (f k : Pat) : Pat := ptup 90 [f, k]
def cellP (ℓ c : Pat) : Pat := ptup 241 [ℓ, c]

/-- The encoding of a right-hand side, as a pattern. -/
def encEP : EPat → Pat
  | .val p => ptup 200 [p]
  | .pair a b => ptup 202 [encEP a, encEP b]
  | .call a => ptup 203 [encEP a]

theorem encEP_inst (θ : ℕ → Sx) : ∀ p : EPat, (encEP p).inst θ = encX (instE θ p)
  | .val _ => rfl
  | .pair a b => by
      show tup 202 [(encEP a).inst θ, (encEP b).inst θ] = _
      rw [encEP_inst θ a, encEP_inst θ b]
      rfl
  | .call a => by
      show tup 203 [(encEP a).inst θ] = _
      rw [encEP_inst θ a]
      rfl

theorem encEP_vars : ∀ p : EPat, (encEP p).vars = p.vars
  | .val p => by simp [encEP, ptup, pseq, Pat.vars, EPat.vars]
  | .pair a b => by simp [encEP, ptup, pseq, Pat.vars, EPat.vars, encEP_vars a, encEP_vars b]
  | .call a => by simp [encEP, ptup, pseq, Pat.vars, EPat.vars, encEP_vars a]

/-- The machine's administrative rules. -/
inductive Admin where
  | val | pair | call | bind | read | force | left | right | arg | update

/-- The stack's pattern variable for an equation: past every variable of its left-hand side. -/
def stackVar (e : NEquation) : ℕ := e.lhs.vars.sum + 1

theorem lt_stackVar (e : NEquation) : ∀ x ∈ e.lhs.vars, x < stackVar e := by
  intro x hx
  unfold stackVar
  generalize e.lhs.vars = l at hx
  induction l with
  | nil => exact absurd hx List.not_mem_nil
  | cons a l ih =>
      rcases List.mem_cons.mp hx with rfl | hx
      · simp only [List.sum_cons]; omega
      · have := ih hx
        simp only [List.sum_cons]; omega

/-- A pattern variable. -/
abbrev pvar (i : ℕ) : Pat := .var i

/-- **The administrative schemas of the by-need machine.** -/
def adminSchema : Admin → Schema
  | .val => ⟨[thrP (evP (ptup 200 [pvar 0])) (pvar 1)], [], [thrP (retP (pvar 0)) (pvar 1)]⟩
  | .pair => ⟨[thrP (evP (ptup 202 [pvar 0, pvar 1])) (pvar 2)], [], [thrP (evP (pvar 0)) (consP (ptup 210 [pvar 1]) (pvar 2))]⟩
  | .call => ⟨[thrP (evP (ptup 203 [pvar 0])) (pvar 1)], [], [thrP (evP (pvar 0)) (consP (ptup 212 []) (pvar 1))]⟩
  | .bind => ⟨[thrP (evP (ptup 204 [pvar 0, pvar 1, pvar 2])) (pvar 3), cellP (pvar 0) (ptup 230 [])], [],
      [thrP (evP (pvar 2)) (pvar 3), cellP (pvar 0) (ptup 231 [pvar 1])]⟩
  | .read => ⟨[thrP (evP (ptup 201 [pvar 0])) (pvar 1)], [cellP (pvar 0) (ptup 233 [pvar 2])], [thrP (retP (pvar 2)) (pvar 1)]⟩
  | .force => ⟨[thrP (evP (ptup 201 [pvar 0])) (pvar 1), cellP (pvar 0) (ptup 231 [pvar 2])], [],
      [thrP (evP (pvar 2)) (consP (ptup 213 [pvar 0]) (pvar 1)), cellP (pvar 0) (ptup 232 [])]⟩
  | .left => ⟨[thrP (retP (pvar 0)) (consP (ptup 210 [pvar 1]) (pvar 2))], [],
      [thrP (evP (pvar 1)) (consP (ptup 211 [pvar 0]) (pvar 2))]⟩
  | .right => ⟨[thrP (retP (pvar 0)) (consP (ptup 211 [pvar 1]) (pvar 2))], [], [thrP (retP (.cell (pvar 1) (pvar 0))) (pvar 2)]⟩
  | .arg => ⟨[thrP (retP (pvar 0)) (consP (ptup 212 []) (pvar 1))], [], [thrP (apP (pvar 0)) (pvar 1)]⟩
  | .update => ⟨[thrP (retP (pvar 0)) (consP (ptup 213 [pvar 1]) (pvar 2)), cellP (pvar 1) (ptup 232 [])], [],
      [thrP (retP (pvar 0)) (pvar 2), cellP (pvar 1) (ptup 233 [pvar 0])]⟩

/-- The schema of one equation: a call of an instance of its left-hand side continues with the
instance of its right-hand side. -/
def applySchema (e : NEquation) : Schema :=
  ⟨[thrP (apP e.lhs) (pvar (stackVar e))], [], [thrP (evP (encEP e.rhs)) (pvar (stackVar e))]⟩

/-- The rules: the administrative ones, and one per equation. -/
abbrev NRule (prog : Program) := Admin ⊕ Fin prog.length

/-- **The schemas of the by-need machine.** -/
def nschema (prog : Program) : NRule prog → Schema
  | .inl r => adminSchema r
  | .inr j => applySchema (prog.get j)

/-- The equations are range restricted: every variable of a right-hand side is one of its
left-hand side's. -/
def RangeRestricted (prog : Program) : Prop :=
  ∀ j : Fin prog.length, ∀ x ∈ (prog.get j).rhs.vars, x ∈ (prog.get j).lhs.vars

theorem admin_wellFormed : ∀ r, (adminSchema r).WellFormed := by
  intro r
  cases r <;> exact ⟨by decide, by decide⟩

theorem apply_wellFormed (e : NEquation) (restricted : ∀ x ∈ e.rhs.vars, x ∈ e.lhs.vars) :
    (applySchema e).WellFormed := by
  refine ⟨fun q member x hx => ?_, by simp [applySchema]⟩
  simp only [applySchema, List.mem_singleton] at member
  subst member
  refine ⟨thrP (apP e.lhs) (pvar (stackVar e)), by simp [applySchema], ?_⟩
  simp only [thrP, evP, apP, ptup, pseq, Pat.vars, List.nil_append, List.append_nil, List.mem_append,
    encEP_vars] at hx ⊢
  rcases hx with hx | hx
  · exact .inl (restricted x hx)
  · exact .inr hx

theorem nschema_wellFormed (restricted : RangeRestricted prog) : ∀ r, (nschema prog r).WellFormed
  | .inl r => admin_wellFormed r
  | .inr j => apply_wellFormed _ (restricted j)

#print axioms nat_inj
#print axioms encX_inj
#print axioms encK_inj
#print axioms thread_split
#print axioms cells_split
#print axioms cell_split
#print axioms encEP_inst
#print axioms nschema_wellFormed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramNeed
