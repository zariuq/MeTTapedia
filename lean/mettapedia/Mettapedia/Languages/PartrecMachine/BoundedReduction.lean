import Mettapedia.Languages.PartrecMachine.Rice

/-!
# Bounded reduction: the resource-bound route out of Rice's theorem

`rice` rules out a computable decision of any nontrivial set of programs that
depends only on what they compute.  This module exhibits the escape it leaves
open, stated about reduction in the authored language itself.

* `ReducesWithin n` is reduction in the authored language in at most `n` steps,
  and `HaltsWithin n program` says the program's pending evaluation on the empty
  input reaches a halted configuration within `n` steps.
* **Decidable.**  Reduction on the encoded image is simulated by a primitive
  recursive step function on a frame representation of continuations
  (`reducesWithin_halt_iff`), so `HaltsWithin n` is computably decidable
  (`haltsWithin_decidable`).
* **Nontrivial.**  `zero'` halts within two steps; the silent program never halts.
* **Not invariant under what programs compute.**  A decidable nontrivial set
  cannot be, by `rice` (`haltsWithin_not_invariant`): the step budget is
  information about how a program computes, not only what.
* **Exhaustive.**  Halting on the empty input is halting within some budget
  (`haltsOnEmpty_iff_exists_within`).

The frame representation is a change of data structure for continuations, not a
second description of the language.  Its only role is to make the simulated step
function primitive recursive, and `reduces_frameState_iff` ties it back to the
authored reduction relation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.PartrecMachine

open Mettapedia.OSLF.MeTTaIL.Syntax
open Turing.ToPartrec
open Mettapedia.Computability.ToPartrecCodeEncoding
open Primrec

/-! ## Reduction with a step budget -/

/-- Reduction in the authored language in at most `n` steps. -/
inductive ReducesWithin : ℕ → Pattern → Pattern → Prop
  | refl (budget : ℕ) (term : Pattern) : ReducesWithin budget term term
  | step {budget : ℕ} {term next target : Pattern} :
      Reduces term next → ReducesWithin budget next target → ReducesWithin (budget + 1) term target

theorem reducesWithin_of_rewritePath
    {source target : (Mettapedia.OSLF.Framework.TypeSynthesis.langGSLT partrecMachine).Term}
    (path : (Mettapedia.OSLF.Framework.TypeSynthesis.langGSLT partrecMachine).RewritePath source target) :
    ∀ budget, path.length ≤ budget → ReducesWithin budget source target := by
  induction path with
  | nil term => exact fun budget _ => .refl budget term
  | cons step rest ih =>
      intro budget short
      simp only [Mettapedia.GSLT.GSLT.RewritePath.length] at short
      obtain ⟨smaller, rfl⟩ : ∃ smaller, budget = smaller + 1 := ⟨budget - 1, by omega⟩
      exact .step ((reduces_iff_generatedStep _ _).mpr step) (ih smaller (by omega))

/-- **Bounded reduction is a rewrite path of bounded length** in the generated
theory. -/
theorem reducesWithin_iff_rewritePath (budget : ℕ) (source target : Pattern) :
    ReducesWithin budget source target ↔
      ∃ path : (Mettapedia.OSLF.Framework.TypeSynthesis.langGSLT partrecMachine).RewritePath
        source target, path.length ≤ budget := by
  constructor
  · intro within
    induction within with
    | refl budget term =>
        exact ⟨@Mettapedia.GSLT.GSLT.RewritePath.nil
          (Mettapedia.OSLF.Framework.TypeSynthesis.langGSLT partrecMachine) term, Nat.zero_le budget⟩
    | step reduces _ ih =>
        obtain ⟨path, short⟩ := ih
        exact ⟨.cons ((reduces_iff_generatedStep _ _).mp reduces) path, by
          simp only [Mettapedia.GSLT.GSLT.RewritePath.length]
          omega⟩
  · rintro ⟨path, short⟩
    exact reducesWithin_of_rewritePath path budget short

theorem reducesWithin_zero_iff {term target : Pattern} :
    ReducesWithin 0 term target ↔ term = target := by
  constructor
  · rintro ⟨⟩
    rfl
  · rintro rfl
    exact .refl 0 _

theorem reducesWithin_succ_iff {budget : ℕ} {term target : Pattern} :
    ReducesWithin (budget + 1) term target ↔
      term = target ∨ ∃ next, Reduces term next ∧ ReducesWithin budget next target := by
  constructor
  · rintro (_ | ⟨reduces, rest⟩)
    · exact .inl rfl
    · exact .inr ⟨_, reduces, rest⟩
  · rintro (rfl | ⟨next, reduces, rest⟩)
    · exact .refl _ _
    · exact .step reduces rest

theorem reflTransGen_of_reducesWithin {budget : ℕ} {term target : Pattern}
    (within : ReducesWithin budget term target) : Relation.ReflTransGen Reduces term target := by
  induction within with
  | refl => exact .refl
  | step reduces _ ih => exact .head reduces ih

theorem exists_reducesWithin_of_reflTransGen {term target : Pattern}
    (reduces : Relation.ReflTransGen Reduces term target) :
    ∃ budget, ReducesWithin budget term target := by
  induction reduces using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, .refl 0 _⟩
  | head first _ ih =>
      obtain ⟨budget, rest⟩ := ih
      exact ⟨budget + 1, .step first rest⟩

/-- A program halts on the empty input within `budget` reduction steps. -/
def HaltsWithin (budget : ℕ) (program : Code) : Prop :=
  ∃ output, ReducesWithin budget (normalTerm program .halt []) (encCfg (.halt output))

/-! ## Frames: continuations as lists -/

/-- One continuation frame: `cons₁ fs as`, `cons₂ ns`, `comp f`, or `fix f`. -/
abbrev Frame : Type := (Code × List ℕ) ⊕ (List ℕ ⊕ (Code ⊕ Code))

def contOf : List Frame → Cont
  | [] => .halt
  | .inl (fs, as) :: frames => .cons₁ fs as (contOf frames)
  | .inr (.inl ns) :: frames => .cons₂ ns (contOf frames)
  | .inr (.inr (.inl f)) :: frames => .comp f (contOf frames)
  | .inr (.inr (.inr f)) :: frames => .fix f (contOf frames)

def framesOf : Cont → List Frame
  | .halt => []
  | .cons₁ fs as k => .inl (fs, as) :: framesOf k
  | .cons₂ ns k => .inr (.inl ns) :: framesOf k
  | .comp f k => .inr (.inr (.inl f)) :: framesOf k
  | .fix f k => .inr (.inr (.inr f)) :: framesOf k

theorem contOf_framesOf (k : Cont) : contOf (framesOf k) = k := by
  induction k <;> simp [framesOf, contOf, *]

theorem framesOf_contOf (frames : List Frame) : framesOf (contOf frames) = frames := by
  induction frames with
  | nil => rfl
  | cons frame frames ih => rcases frame with ⟨_, _⟩ | _ | _ | _ <;> simp [contOf, framesOf, ih]

/-- A pending normal evaluation, a returning configuration, or a halted one. -/
abbrev FrameState : Type := (Code × List Frame × List ℕ) ⊕ ((List Frame × List ℕ) ⊕ List ℕ)

def encFrameState : FrameState → Pattern
  | .inl (c, frames, v) => normalTerm c (contOf frames) v
  | .inr (.inl (frames, v)) => encCfg (.ret (contOf frames) v)
  | .inr (.inr v) => encCfg (.halt v)

theorem encFrameState_injective : Function.Injective encFrameState := by
  intro first second same
  rcases first with ⟨c, frames, v⟩ | ⟨frames, v⟩ | v <;>
    rcases second with ⟨d, frames', w⟩ | ⟨frames', w⟩ | w <;>
    simp only [encFrameState] at same
  · simp only [normalTerm, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at same
    obtain ⟨hc, hk, hv⟩ := same
    rw [encCode_injective hc, encNats_injective hv,
      ← framesOf_contOf frames, encCont_injective hk, framesOf_contOf]
  · exact absurd same (normalTerm_ne_encCfg _ _ _ _)
  · exact absurd same (normalTerm_ne_encCfg _ _ _ _)
  · exact absurd same.symm (normalTerm_ne_encCfg _ _ _ _)
  · have := encCfg_injective same
    simp only [Cfg.ret.injEq] at this
    rw [← framesOf_contOf frames, this.1, framesOf_contOf, this.2]
  · cases encCfg_injective same
  · exact absurd same.symm (normalTerm_ne_encCfg _ _ _ _)
  · cases encCfg_injective same
  · rw [show v = w by simpa using encCfg_injective same]

/-! ## The simulated step -/

def normalStep (c : Code) (frames : List Frame) (v : List ℕ) : FrameState :=
  match c with
  | .zero' => .inr (.inl (frames, 0 :: v))
  | .succ => .inr (.inl (frames, [v.headI.succ]))
  | .tail => .inr (.inl (frames, v.tail))
  | .cons f fs => .inl (f, .inl (fs, v) :: frames, v)
  | .comp f g => .inl (g, .inr (.inr (.inl f)) :: frames, v)
  | .case f g =>
      if v.headI = 0 then .inl (f, frames, v.tail) else .inl (g, frames, (v.headI - 1) :: v.tail)
  | .fix f => .inl (f, .inr (.inr (.inr f)) :: frames, v)

def retStep : List Frame → List ℕ → FrameState
  | [], v => .inr (.inr v)
  | .inl (fs, as) :: frames, v => .inl (fs, .inr (.inl v) :: frames, as)
  | .inr (.inl ns) :: frames, v => .inr (.inl (frames, ns.headI :: v))
  | .inr (.inr (.inl f)) :: frames, v => .inl (f, frames, v)
  | .inr (.inr (.inr f)) :: frames, v =>
      if v.headI = 0 then .inr (.inl (frames, v.tail))
      else .inl (f, .inr (.inr (.inr f)) :: frames, v.tail)

/-- One step, with halted states fixed. -/
def frameStep : FrameState → FrameState
  | .inl (c, frames, v) => normalStep c frames v
  | .inr (.inl (frames, v)) => retStep frames v
  | .inr (.inr v) => .inr (.inr v)

def isHalted : FrameState → Bool
  | .inr (.inr _) => true
  | _ => false

theorem encFrameState_normalStep (c : Code) (frames : List Frame) (v : List ℕ) :
    encFrameState (normalStep c frames v) = normalReduct c (contOf frames) v := by
  cases c with
  | case f g =>
      rcases v with _ | ⟨_ | n, w⟩ <;> simp [normalStep, normalReduct, encFrameState]
  | _ => rfl

theorem encFrameState_retStep (frames : List Frame) (v : List ℕ) :
    encFrameState (retStep frames v) = retReduct (contOf frames) v := by
  rcases frames with _ | ⟨⟨_, _⟩ | _ | _ | f, frames⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · by_cases zero : v.headI = 0 <;> simp [retStep, retReduct, contOf, encFrameState, zero]

/-- **The simulated step is reduction.**  A state that has not halted reduces to
exactly the encoding of its simulated successor; a halted one does not reduce. -/
theorem reduces_frameState_iff (state : FrameState) (target : Pattern) :
    Reduces (encFrameState state) target ↔
      isHalted state = false ∧ target = encFrameState (frameStep state) := by
  rcases state with ⟨c, frames, v⟩ | ⟨frames, v⟩ | v
  · show Reduces (normalTerm c (contOf frames) v) target ↔ _
    rw [reduces_normal_iff, ← encFrameState_normalStep]
    exact ⟨fun same => ⟨rfl, same⟩, fun both => both.2⟩
  · show Reduces (encCfg (.ret (contOf frames) v)) target ↔ _
    rw [reduces_ret_iff, ← encFrameState_retStep]
    exact ⟨fun same => ⟨rfl, same⟩, fun both => both.2⟩
  · simp only [encFrameState, isHalted, Bool.true_eq_false, false_and, iff_false]
    exact halt_irreducible v target

theorem frameStep_halted {state : FrameState} (halted : isHalted state = true) :
    frameStep state = state := by
  rcases state with _ | _ | v <;> simp_all [isHalted, frameStep]

theorem reducesWithin_halt_iff (budget : ℕ) (state : FrameState) (output : List ℕ) :
    ReducesWithin budget (encFrameState state) (encCfg (.halt output)) ↔
      frameStep^[budget] state = .inr (.inr output) := by
  induction budget generalizing state with
  | zero =>
      rw [reducesWithin_zero_iff, Function.iterate_zero_apply]
      exact ⟨fun same => encFrameState_injective (same.trans rfl),
        fun same => by rw [same]; rfl⟩
  | succ budget ih =>
      rw [reducesWithin_succ_iff, Function.iterate_succ_apply]
      cases halted : isHalted state
      · constructor
        · rintro (same | ⟨next, reduces, rest⟩)
          · have := encFrameState_injective (show encFrameState state = encFrameState (.inr (.inr output)) from same)
            subst this
            simp [isHalted] at halted
          · obtain ⟨-, rfl⟩ := (reduces_frameState_iff state next).mp reduces
            exact (ih _).mp rest
        · intro reaches
          exact .inr ⟨_, (reduces_frameState_iff state _).mpr ⟨halted, rfl⟩, (ih _).mpr reaches⟩
      · rw [frameStep_halted halted]
        rcases state with _ | _ | v <;> simp only [isHalted, Bool.false_eq_true] at halted
        rw [Function.iterate_fixed (frameStep_halted (state := .inr (.inr v)) rfl)]
        constructor
        · rintro (same | ⟨next, reduces, -⟩)
          · have outputs := encCfg_injective (show encCfg (.halt v) = encCfg (.halt output) from same)
            simp only [Cfg.halt.injEq] at outputs
            rw [outputs]
          · exact absurd reduces (by simpa [encFrameState] using halt_irreducible v next)
        · intro same
          simp only [Sum.inr.injEq] at same
          exact .inl (by rw [same]; rfl)

theorem haltsWithin_iff (budget : ℕ) (program : Code) :
    HaltsWithin budget program ↔ isHalted (frameStep^[budget] (.inl (program, [], []))) = true := by
  have start : normalTerm program .halt [] = encFrameState (.inl (program, [], [])) := rfl
  simp only [HaltsWithin, start, reducesWithin_halt_iff]
  constructor
  · rintro ⟨output, reaches⟩
    rw [reaches]
    rfl
  · intro halted
    generalize frameStep^[budget] (.inl (program, [], [])) = final at halted
    rcases final with _ | _ | output <;> simp_all [isHalted]

/-! ## Primitive recursion -/

def ofPartrecCodeRec (d : Nat.Partrec.Code) : Code :=
  Nat.Partrec.Code.recOn d .zero' .succ .tail .zero' (fun _ _ f g => .cons f g)
    (fun _ _ f g => .comp f g) (fun _ _ f g => .case f g) (fun _ f => .fix f)

theorem ofPartrecCode_eq_rec (d : Nat.Partrec.Code) : ofPartrecCode d = ofPartrecCodeRec d := by
  induction d <;> simp [ofPartrecCode, ofPartrecCodeRec, *]

theorem ofPartrecCode_primrec : Primrec ofPartrecCode := by
  have recursion := Nat.Partrec.Code.primrec_recOn (α := Nat.Partrec.Code) (σ := Code)
    Primrec.id (Primrec.const .zero') (Primrec.const .succ) (Primrec.const .tail)
    (Primrec.const .zero')
    (pr := fun _ _ _ f g => .cons f g)
    (primrec₂_cons.comp (fst.comp (snd.comp (snd.comp snd))) (snd.comp (snd.comp (snd.comp snd))))
    (co := fun _ _ _ f g => .comp f g)
    (primrec₂_comp.comp (fst.comp (snd.comp (snd.comp snd))) (snd.comp (snd.comp (snd.comp snd))))
    (pc := fun _ _ _ f g => .case f g)
    (primrec₂_case.comp (fst.comp (snd.comp (snd.comp snd))) (snd.comp (snd.comp (snd.comp snd))))
    (rf := fun _ _ f => .fix f) (primrec_fix.comp (snd.comp snd))
  exact recursion.of_eq fun d => (ofPartrecCode_eq_rec d).symm

theorem normalStep_eq_recOn (c : Code) (frames : List Frame) (v : List ℕ) :
    normalStep c frames v =
      Nat.Partrec.Code.recOn (toPartrecCode c)
        (.inr (.inl (frames, 0 :: v))) (.inr (.inl (frames, [v.headI.succ])))
        (.inr (.inl (frames, v.tail))) (.inr (.inr []))
        (fun cf cg _ _ => .inl (ofPartrecCode cf, .inl (ofPartrecCode cg, v) :: frames, v))
        (fun cf cg _ _ => .inl (ofPartrecCode cg, .inr (.inr (.inl (ofPartrecCode cf))) :: frames, v))
        (fun cf cg _ _ => if v.headI = 0 then .inl (ofPartrecCode cf, frames, v.tail)
          else .inl (ofPartrecCode cg, frames, (v.headI - 1) :: v.tail))
        (fun cf _ => .inl (ofPartrecCode cf, .inr (.inr (.inr (ofPartrecCode cf))) :: frames, v)) := by
  cases c <;> simp [normalStep, toPartrecCode, ofPartrecCode_toPartrecCode]

theorem normalStep_primrec :
    Primrec fun state : Code × List Frame × List ℕ => normalStep state.1 state.2.1 state.2.2 := by
  -- projections from the recursor's argument `(state, cf, cg, _, _)` or `(state, cf, _)`
  have frames₅ : Primrec fun p : (Code × List Frame × List ℕ) × Nat.Partrec.Code × Nat.Partrec.Code ×
      FrameState × FrameState => p.1.2.1 := fst.comp (snd.comp fst)
  have values₅ : Primrec fun p : (Code × List Frame × List ℕ) × Nat.Partrec.Code × Nat.Partrec.Code ×
      FrameState × FrameState => p.1.2.2 := snd.comp (snd.comp fst)
  have cf₅ : Primrec fun p : (Code × List Frame × List ℕ) × Nat.Partrec.Code × Nat.Partrec.Code ×
      FrameState × FrameState => ofPartrecCode p.2.1 := ofPartrecCode_primrec.comp (fst.comp snd)
  have cg₅ : Primrec fun p : (Code × List Frame × List ℕ) × Nat.Partrec.Code × Nat.Partrec.Code ×
      FrameState × FrameState => ofPartrecCode p.2.2.1 :=
    ofPartrecCode_primrec.comp (fst.comp (snd.comp snd))
  have headZero : PrimrecPred fun p : (Code × List Frame × List ℕ) × Nat.Partrec.Code ×
      Nat.Partrec.Code × FrameState × FrameState => p.1.2.2.headI = 0 :=
    Primrec.eq.comp (list_headI.comp values₅) (const 0)
  have recursion := Nat.Partrec.Code.primrec_recOn
    (α := Code × List Frame × List ℕ) (σ := FrameState)
    (c := fun state => toPartrecCode state.1) (toPartrecCode_primrec.comp fst)
    (z := fun state => .inr (.inl (state.2.1, 0 :: state.2.2)))
    (sumInr.comp (sumInl.comp (pair (fst.comp snd) (list_cons.comp (const 0) (snd.comp snd)))))
    (s := fun state => .inr (.inl (state.2.1, [state.2.2.headI.succ])))
    (sumInr.comp (sumInl.comp (pair (fst.comp snd)
      (list_cons.comp (succ.comp (list_headI.comp (snd.comp snd))) (const [])))))
    (l := fun state => .inr (.inl (state.2.1, state.2.2.tail)))
    (sumInr.comp (sumInl.comp (pair (fst.comp snd) (list_tail.comp (snd.comp snd)))))
    (r := fun _ => .inr (.inr [])) (const _)
    (pr := fun state cf cg _ _ => .inl (ofPartrecCode cf, .inl (ofPartrecCode cg, state.2.2) :: state.2.1, state.2.2))
    (sumInl.comp (pair cf₅ (pair (list_cons.comp (sumInl.comp (pair cg₅ values₅)) frames₅) values₅)))
    (co := fun state cf cg _ _ => .inl (ofPartrecCode cg, .inr (.inr (.inl (ofPartrecCode cf))) :: state.2.1, state.2.2))
    (sumInl.comp (pair cg₅ (pair (list_cons.comp (sumInr.comp (sumInr.comp (sumInl.comp cf₅))) frames₅)
      values₅)))
    (pc := fun state cf cg _ _ => if state.2.2.headI = 0 then .inl (ofPartrecCode cf, state.2.1, state.2.2.tail)
      else .inl (ofPartrecCode cg, state.2.1, (state.2.2.headI - 1) :: state.2.2.tail))
    (Primrec.ite headZero (sumInl.comp (pair cf₅ (pair frames₅ (list_tail.comp values₅))))
      (sumInl.comp (pair cg₅ (pair frames₅ (list_cons.comp
        (nat_sub.comp (list_headI.comp values₅) (const 1)) (list_tail.comp values₅))))))
    (rf := fun state cf _ => .inl (ofPartrecCode cf, .inr (.inr (.inr (ofPartrecCode cf))) :: state.2.1, state.2.2))
    (sumInl.comp (pair (ofPartrecCode_primrec.comp (fst.comp snd)) (pair (list_cons.comp
      (sumInr.comp (sumInr.comp (sumInr.comp (ofPartrecCode_primrec.comp (fst.comp snd)))))
      (fst.comp (snd.comp fst))) (snd.comp (snd.comp fst)))))
  exact recursion.of_eq fun state => (normalStep_eq_recOn state.1 state.2.1 state.2.2).symm

/-- The return step on a nonempty frame stack, as a function of the whole state and
the stack's head and tail. -/
def retBranch (state : List Frame × List ℕ) (entry : Frame × List Frame) : FrameState :=
  Sum.casesOn entry.1 (fun pending => .inl (pending.1, .inr (.inl state.2) :: entry.2, pending.2))
    fun other => Sum.casesOn other (fun ns => .inr (.inl (entry.2, ns.headI :: state.2)))
      fun code => Sum.casesOn code (fun f => .inl (f, entry.2, state.2))
        fun f => if state.2.headI = 0 then .inr (.inl (entry.2, state.2.tail))
          else .inl (f, .inr (.inr (.inr f)) :: entry.2, state.2.tail)

abbrev BranchInput : Type := (List Frame × List ℕ) × Frame × List Frame

theorem retBranch_primrec : Primrec₂ retBranch := by
  have values : Primrec fun p : BranchInput => p.1.2 := snd.comp fst
  have rest : Primrec fun p : BranchInput => p.2.2 := snd.comp snd
  have fixBranch : Primrec₂ fun (p : BranchInput) (f : Code) =>
      (if p.1.2.headI = 0 then .inr (.inl (p.2.2, p.1.2.tail))
        else .inl (f, .inr (.inr (.inr f)) :: p.2.2, p.1.2.tail) : FrameState) :=
    (Primrec.ite (Primrec.eq.comp (list_headI.comp (values.comp fst)) (const 0))
      (sumInr.comp (sumInl.comp (pair (rest.comp fst) (list_tail.comp (values.comp fst)))))
      (sumInl.comp (pair snd (pair (list_cons.comp (sumInr.comp (sumInr.comp (sumInr.comp snd)))
        (rest.comp fst)) (list_tail.comp (values.comp fst)))))).to₂
  have compBranch : Primrec₂ fun (p : BranchInput) (f : Code) =>
      (.inl (f, p.2.2, p.1.2) : FrameState) :=
    (sumInl.comp (pair snd (pair (rest.comp fst) (values.comp fst)))).to₂
  have codeBranch : Primrec₂ fun (p : BranchInput) (code : Code ⊕ Code) =>
      (Sum.casesOn code (fun f => .inl (f, p.2.2, p.1.2))
        fun f => if p.1.2.headI = 0 then .inr (.inl (p.2.2, p.1.2.tail))
          else .inl (f, .inr (.inr (.inr f)) :: p.2.2, p.1.2.tail) : FrameState) :=
    (sumCasesOn snd (compBranch.comp (fst.comp fst) snd).to₂ (fixBranch.comp (fst.comp fst) snd).to₂).to₂
  have cons₂Branch : Primrec₂ fun (p : BranchInput) (ns : List ℕ) =>
      (.inr (.inl (p.2.2, ns.headI :: p.1.2)) : FrameState) :=
    (sumInr.comp (sumInl.comp (pair (rest.comp fst) (list_cons.comp (list_headI.comp snd)
      (values.comp fst))))).to₂
  have otherBranch : Primrec₂ fun (p : BranchInput) (other : List ℕ ⊕ (Code ⊕ Code)) =>
      (Sum.casesOn other (fun ns => .inr (.inl (p.2.2, ns.headI :: p.1.2)))
        fun code => Sum.casesOn code (fun f => .inl (f, p.2.2, p.1.2))
          fun f => if p.1.2.headI = 0 then .inr (.inl (p.2.2, p.1.2.tail))
            else .inl (f, .inr (.inr (.inr f)) :: p.2.2, p.1.2.tail) : FrameState) :=
    (sumCasesOn snd (cons₂Branch.comp (fst.comp fst) snd).to₂
      (codeBranch.comp (fst.comp fst) snd).to₂).to₂
  have cons₁Branch : Primrec₂ fun (p : BranchInput) (pending : Code × List ℕ) =>
      (.inl (pending.1, .inr (.inl p.1.2) :: p.2.2, pending.2) : FrameState) :=
    (sumInl.comp (pair (fst.comp snd) (pair (list_cons.comp (sumInr.comp (sumInl.comp
      (values.comp fst))) (rest.comp fst)) (snd.comp snd)))).to₂
  have whole : Primrec fun p : BranchInput => retBranch p.1 p.2 :=
    sumCasesOn (fst.comp snd) cons₁Branch otherBranch
  exact whole.to₂

theorem retStep_eq_casesOn (frames : List Frame) (v : List ℕ) :
    retStep frames v =
      List.casesOn frames (.inr (.inr v)) fun frame rest => retBranch (frames, v) (frame, rest) := by
  rcases frames with _ | ⟨⟨_, _⟩ | _ | _ | _, _⟩ <;> rfl

theorem retStep_primrec :
    Primrec fun state : List Frame × List ℕ => retStep state.1 state.2 := by
  have cased : Primrec fun state : List Frame × List ℕ =>
      (List.casesOn state.1 (.inr (.inr state.2)) fun frame rest => retBranch state (frame, rest) :
        FrameState) :=
    list_casesOn fst (sumInr.comp (sumInr.comp snd)) retBranch_primrec
  exact cased.of_eq fun state => (retStep_eq_casesOn state.1 state.2).symm

theorem frameStep_primrec : Primrec frameStep := by
  refine Primrec.of_eq (sumCasesOn Primrec.id (normalStep_primrec.comp snd).to₂
    (sumCasesOn snd (retStep_primrec.comp snd).to₂ (sumInr.comp (sumInr.comp snd)).to₂).to₂) ?_
  intro state
  rcases state with ⟨_, _, _⟩ | ⟨_, _⟩ | _ <;> rfl

theorem isHalted_primrec : Primrec isHalted := by
  refine Primrec.of_eq (sumCasesOn Primrec.id (const false).to₂
    (sumCasesOn snd (const false).to₂ (const true).to₂).to₂) ?_
  intro state
  rcases state with _ | _ | _ <;> rfl

/-! ## The escape -/

/-- **Bounded halting is decidable.** -/
theorem haltsWithin_decidable (budget : ℕ) : ComputablePred (HaltsWithin budget) := by
  refine ComputablePred.computable_iff.mpr
    ⟨fun program => isHalted (frameStep^[budget] (.inl (program, [], []))), ?_, ?_⟩
  · exact (isHalted_primrec.comp (nat_iterate (const budget)
      (sumInl.comp (pair Primrec.id (const ([], [])))) (frameStep_primrec.comp snd).to₂)).to_comp
  · funext program
    exact propext (haltsWithin_iff budget program)

theorem zero'_haltsWithin_two : HaltsWithin 2 .zero' :=
  (haltsWithin_iff 2 .zero').mpr rfl

theorem silent_never_halts (budget : ℕ) : ¬ HaltsWithin budget silent := by
  rintro ⟨output, within⟩
  have := haltsWith_iff.mp (reflTransGen_of_reducesWithin within)
  simp [silent_eval] at this

theorem haltsWithin_nontrivial (budget : ℕ) (large : 2 ≤ budget) :
    ({program | HaltsWithin budget program} : Set Code).Nonempty ∧
      ({program | HaltsWithin budget program} : Set Code)ᶜ.Nonempty := by
  refine ⟨⟨.zero', ?_⟩, ⟨silent, silent_never_halts budget⟩⟩
  obtain ⟨output, within⟩ := zero'_haltsWithin_two
  refine ⟨output, ?_⟩
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le large
  have halted : frameStep^[2] (.inl (.zero', [], [])) = .inr (.inr output) :=
    (reducesWithin_halt_iff 2 _ output).mp within
  refine (reducesWithin_halt_iff (2 + extra) (.inl (.zero', [], [])) output).mpr ?_
  rw [add_comm, Function.iterate_add_apply, halted,
    Function.iterate_fixed (frameStep_halted (state := .inr (.inr output)) rfl)]

/-- **The budget is not what a program computes.**  Bounded halting is decidable
and nontrivial, so by `rice` it cannot depend only on what a program computes. -/
theorem haltsWithin_not_invariant (budget : ℕ) (large : 2 ≤ budget) :
    ¬ Mettapedia.Computability.ObservationInvariant HaltsWith {program | HaltsWithin budget program} :=
  fun invariant => rice invariant (haltsWithin_nontrivial budget large) (haltsWithin_decidable budget)

/-- Halting on the empty input is halting within some budget. -/
theorem haltsOnEmpty_iff_exists_within (program : Code) :
    HaltsOnEmpty program ↔ ∃ budget, HaltsWithin budget program := by
  constructor
  · rintro ⟨output, reduces⟩
    obtain ⟨budget, within⟩ := exists_reducesWithin_of_reflTransGen reduces
    exact ⟨budget, output, within⟩
  · rintro ⟨budget, output, within⟩
    exact ⟨output, reflTransGen_of_reducesWithin within⟩

/-! ## Axiom audit -/

#print axioms reducesWithin_iff_rewritePath
#print axioms reduces_frameState_iff
#print axioms reducesWithin_halt_iff
#print axioms frameStep_primrec
#print axioms haltsWithin_decidable
#print axioms haltsWithin_nontrivial
#print axioms haltsWithin_not_invariant
#print axioms haltsOnEmpty_iff_exists_within

end Mettapedia.Languages.PartrecMachine
