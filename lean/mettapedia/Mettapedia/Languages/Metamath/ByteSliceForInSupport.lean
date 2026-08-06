module
public import Batteries.Data.ByteSlice
import all Batteries.Data.ByteSlice

/-!
# `ByteSlice.forIn` characterized as list folds

The Batteries `ByteSlice.forIn` implementation iterates with the
`size - 1 - i` index recursion; its inner `loop` is module-private, so
this file — a `module`-system file importing only Batteries, with
`import all` for the internals — proves the two general
characterizations (yield-only loops and if-exit loops) as public
theorems over a loop-free byte extraction.  Downstream legacy modules
instantiate them for the shipped mm-lean4 content loops (`toLabel`,
`eqArray`); nothing else ever needs the hidden loop.
-/

namespace Mettapedia.Languages.Metamath.ByteSliceForInSupport

/-- Loop-free byte extraction of a slice. -/
@[expose] public def sliceList (s : ByteSlice) : List UInt8 :=
  (s.byteArray.data.toList.drop s.start).take s.size

public theorem sliceList_def (s : ByteSlice) :
    sliceList s = (s.byteArray.data.toList.drop s.start).take s.size :=
  rfl

/-- A fold that may exit early: `P` decides exit, `d` the exit value,
`g` the continuing step. -/
public def foldWithExit {β : Type} (P : UInt8 → β → Bool)
    (d g : UInt8 → β → β) : List UInt8 → β → β
  | [], b => b
  | c :: rest, b =>
      if P c b then d c b else foldWithExit P d g rest (g c b)

theorem loop_yield {β : Type} (s : ByteSlice)
    (f' : UInt8 → β → Id (ForInStep β)) (g : UInt8 → β → β)
    (hf : ∀ c b, f' c b = pure (ForInStep.yield (g c b))) :
    ∀ (i : Nat) (h : i ≤ s.size) (b : β),
      ByteSlice.forIn.loop s f' i h b =
        ((s.byteArray.data.toList.drop
            (s.start + (s.size - i))).take i).foldl
          (fun b c => g c b) b
  | 0, _, b => by
      rw [List.take_zero]
      rfl
  | i + 1, h, b => by
      have hstop := s.stop_le_size_byteArray
      have hsize : s.size = s.stop - s.start := rfl
      have hlen : s.byteArray.data.toList.length = s.byteArray.size :=
        rfl
      have hbound : s.start + (s.size - 1 - i) <
          s.byteArray.data.toList.length := by
        omega
      have h1 : s.start + (s.size - (i + 1)) =
          s.start + (s.size - 1 - i) := by
        omega
      have h2 : s.start + (s.size - i) =
          (s.start + (s.size - 1 - i)) + 1 := by
        omega
      rw [h1, List.drop_eq_getElem_cons hbound, List.take_succ_cons,
        List.foldl_cons]
      show (match f' s[s.size - 1 - i] b with
        | ForInStep.done r => pure r
        | ForInStep.yield r =>
            ByteSlice.forIn.loop s f' i (Nat.le_of_succ_le h) r) = _
      rw [hf]
      show ByteSlice.forIn.loop s f' i (Nat.le_of_succ_le h)
          (g s[s.size - 1 - i] b) = _
      rw [loop_yield s f' g hf i (Nat.le_of_succ_le h), h2]
      rfl

/-- **Yield-only `forIn` is a left fold over the slice's bytes.** -/
public theorem byteSlice_forIn_yield {β : Type} (s : ByteSlice)
    (f' : UInt8 → β → Id (ForInStep β)) (g : UInt8 → β → β)
    (hf : ∀ c b, f' c b = pure (ForInStep.yield (g c b))) (init : β) :
    ByteSlice.forIn s init f' =
      (sliceList s).foldl (fun b c => g c b) init := by
  unfold ByteSlice.forIn
  rw [loop_yield s f' g hf s.size (Nat.le_refl _) init]
  rw [Nat.sub_self, Nat.add_zero]
  rfl

theorem loop_exit {β : Type} (s : ByteSlice)
    (f' : UInt8 → β → Id (ForInStep β)) (P : UInt8 → β → Bool)
    (d g : UInt8 → β → β)
    (hf : ∀ c b, f' c b =
      if P c b then pure (ForInStep.done (d c b))
      else pure (ForInStep.yield (g c b))) :
    ∀ (i : Nat) (h : i ≤ s.size) (b : β),
      ByteSlice.forIn.loop s f' i h b =
        foldWithExit P d g
          ((s.byteArray.data.toList.drop
              (s.start + (s.size - i))).take i) b
  | 0, _, b => by
      rw [List.take_zero]
      rfl
  | i + 1, h, b => by
      have hstop := s.stop_le_size_byteArray
      have hsize : s.size = s.stop - s.start := rfl
      have hlen : s.byteArray.data.toList.length = s.byteArray.size :=
        rfl
      have hbound : s.start + (s.size - 1 - i) <
          s.byteArray.data.toList.length := by
        omega
      have h1 : s.start + (s.size - (i + 1)) =
          s.start + (s.size - 1 - i) := by
        omega
      have h2 : s.start + (s.size - i) =
          (s.start + (s.size - 1 - i)) + 1 := by
        omega
      rw [h1, List.drop_eq_getElem_cons hbound, List.take_succ_cons]
      have hhead :
          s.byteArray.data.toList[s.start + (s.size - 1 - i)]'hbound =
            s[s.size - 1 - i] := rfl
      rw [hhead]
      show (match f' s[s.size - 1 - i] b with
        | ForInStep.done r => pure r
        | ForInStep.yield r =>
            ByteSlice.forIn.loop s f' i (Nat.le_of_succ_le h) r) = _
      rw [hf]
      simp only [foldWithExit]
      by_cases hP : P s[s.size - 1 - i] b = true
      · rw [if_pos hP, if_pos hP]
        rfl
      · rw [if_neg hP, if_neg hP]
        show ByteSlice.forIn.loop s f' i (Nat.le_of_succ_le h)
            (g s[s.size - 1 - i] b) = _
        rw [loop_exit s f' P d g hf i (Nat.le_of_succ_le h), h2]

/-- **If-exit `forIn` is the exit fold over the slice's bytes.** -/
public theorem byteSlice_forIn_exit {β : Type} (s : ByteSlice)
    (f' : UInt8 → β → Id (ForInStep β)) (P : UInt8 → β → Bool)
    (d g : UInt8 → β → β)
    (hf : ∀ c b, f' c b =
      if P c b then pure (ForInStep.done (d c b))
      else pure (ForInStep.yield (g c b))) (init : β) :
    ByteSlice.forIn s init f' =
      foldWithExit P d g (sliceList s) init := by
  unfold ByteSlice.forIn
  rw [loop_exit s f' P d g hf s.size (Nat.le_refl _) init]
  rw [Nat.sub_self, Nat.add_zero]
  rfl

end Mettapedia.Languages.Metamath.ByteSliceForInSupport
