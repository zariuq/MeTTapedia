import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ExactStaticTypes

/-!
# Typings kept under copying, and the run's answer typing

**Copies keep their typings** (`space_type_stamps_transfer`). A copy of a value
has its shape, its variables possibly renamed (`renameA`), and HE's typing reads
no variable name: a variable has no typing whatever its name, so the copy's
typings are the source's (`heInfo_rename`, `stamp_rename`).

**The store keeps them by address** (`ShapeTyping`'s `Heap`, `AddrMemo`,
`Sound`). Recording at the copy's address the typing kept at the source's,
where the source's entry is valid under its arena's current epoch, keeps the
store sound (`sound_transfer`), and so does a whole copy walk, node by node
(`transferAll`, `sound_transferAll`): every validated hit is then HE's typing of
the atom at its address.

**The run's answer** (rule 13). A run records for the value its last checked
build made the build's exact static typing (`ExactStaticTypes.build_exactAt`);
a lookup of that record validated under the arena's epoch, after any heap
operations, is HE's typing of the atom then at the address, and while the
arena's epoch is unchanged that atom is the build's value, whose `get-type`
answers, read by solutions, are the recorded typing alone (`answer_typing`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypingTransfer

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open ShapeTyping ExactStaticTypes

mutual
/-- A copy of an atom with its variables renamed. -/
def renameA (g : String → String) : Atom → Atom
  | .var x => .var (g x)
  | .symbol s => .symbol s
  | .grounded v => .grounded v
  | .expression xs => .expression (renameL g xs)
/-- A copy of a list of atoms. -/
def renameL (g : String → String) : List Atom → List Atom
  | [] => []
  | x :: xs => renameA g x :: renameL g xs
end

mutual
/-- **HE's typing reads no variable name.** -/
theorem heInfo_rename (Γ : Decls) (g : String → String) : ∀ t : Atom, heInfo Γ (renameA g t) = heInfo Γ t
  | .var x => rfl
  | .symbol s => rfl
  | .grounded v => rfl
  | .expression xs => by
      rw [renameA, heInfo_expression, heInfo_expression, heInfos_rename Γ g xs]
theorem heInfos_rename (Γ : Decls) (g : String → String) :
    ∀ xs : List Atom, (renameL g xs).map (heInfo Γ) = xs.map (heInfo Γ)
  | [] => rfl
  | x :: xs => by
      rw [renameL, List.map_cons, List.map_cons, heInfo_rename Γ g x, heInfos_rename Γ g xs]
end

/-- **A copy has its source's typings.** -/
theorem stamp_rename (Γ : Decls) (g : String → String) (t : Atom) : stamp Γ (renameA g t) = stamp Γ t := by
  simp only [stamp, heInfo_rename]

mutual
theorem renameA_id : ∀ t : Atom, renameA id t = t
  | .var _ => rfl
  | .symbol _ => rfl
  | .grounded _ => rfl
  | .expression xs => by rw [renameA, renameL_id xs]
theorem renameL_id : ∀ xs : List Atom, renameL id xs = xs
  | [] => rfl
  | x :: xs => by rw [renameL, renameA_id x, renameL_id xs]
end

variable {Addr J : Type} [DecidableEq Addr]

/-- **Recording a copy's typing from its source keeps the store sound**: the
source's entry validated under its arena's epoch is the source's typing, and the
copy has the same typing. -/
theorem sound_transfer {H : Heap Addr} {f : Atom → J} {m : AddrMemo Addr J} (hm : Sound H f m)
    {p q : Addr} {j : J} (hit : lookupAt H m p = some j) {t' : Atom} {b : ℕ}
    (hq : H.cell q = some (t', b)) (copy : ∀ t a, H.cell p = some (t, a) → f t' = f t) :
    Sound H f (Function.update m q (some (b, H.epoch b, j))) := by
  obtain ⟨t, a, hp, rfl⟩ := validated_hit hm hit
  rw [← copy t a hp]
  exact sound_record hm hq

/-- One step of a copy walk: the copy at `q` takes the typing validated at its
source `p`, if any. -/
def transferStep (H : Heap Addr) (m : AddrMemo Addr J) (pq : Addr × Addr) : AddrMemo Addr J :=
  match lookupAt H m pq.1, H.cell pq.2 with
  | some j, some (_, b) => Function.update m pq.2 (some (b, H.epoch b, j))
  | _, _ => m

/-- A copy walk over its pairs of source and copy, each copied node once. -/
def transferAll (H : Heap Addr) (m : AddrMemo Addr J) (pqs : List (Addr × Addr)) : AddrMemo Addr J :=
  pqs.foldl (transferStep H) m

/-- **A copy walk keeps the store sound** when each copy has its source's
typing. -/
theorem sound_transferAll {H : Heap Addr} {f : Atom → J} :
    ∀ (m : AddrMemo Addr J) (pqs : List (Addr × Addr)), Sound H f m →
      (∀ pq ∈ pqs, ∀ t a t' b, H.cell pq.1 = some (t, a) → H.cell pq.2 = some (t', b) → f t' = f t) →
      Sound H f (transferAll H m pqs)
  | m, [], hm, _ => hm
  | m, pq :: pqs, hm, copies => by
      have hstep : Sound H f (transferStep H m pq) := by
        unfold transferStep
        split
        · rename_i j b' _ hj hc
          exact sound_transfer hm hj hc fun t a hp => copies pq (by simp) t a _ _ hp hc
        · exact hm
      exact sound_transferAll _ pqs hstep fun pq' h => copies pq' (by simp [h])

/-- A copy walk over renamed copies of HE's typings keeps the store sound. -/
theorem stamp_transferAll {Γ : Decls} {H : Heap Addr} (m : AddrMemo Addr Stamp)
    (hm : Sound H (stamp Γ) m) (pqs : List (Addr × Addr))
    (copies : ∀ pq ∈ pqs, ∀ t a t' b, H.cell pq.1 = some (t, a) → H.cell pq.2 = some (t', b) →
      ∃ g, t' = renameA g t) :
    Sound H (stamp Γ) (transferAll H m pqs) :=
  sound_transferAll m pqs hm fun pq h t a t' b hp hq => by
    obtain ⟨g, rfl⟩ := copies pq h t a t' b hp hq
    exact stamp_rename Γ g t

/-- **The run's answer typing**: the exact typing of the value a checked build
made, recorded at its address; a later lookup validated under the arena's epoch
is HE's typing of the atom then at the address, and while the arena's epoch is
unchanged that atom is the build's value, typed exactly at the record. -/
theorem answer_typing {Γ : Decls} {H : Heap Addr} {m : AddrMemo Addr Stamp} (hm : Sound H (stamp Γ) m)
    {q : Addr} {t : Atom} {b : ℕ} (hq : H.cell q = some (t, b)) {S : Set (Ty Empty)}
    (hS : ExactAt S (stamp Γ t)) (ops : List (HeapOp Addr)) {j : Stamp}
    (hit : lookupAt (H.run ops) (Function.update m q (some (b, H.epoch b, ⟨metaName t, [Sem.ok S]⟩))) q =
      some j) :
    (∃ t' a, (H.run ops).cell q = some (t', a) ∧ j = stamp Γ t') ∧
      ((H.run ops).epoch b = H.epoch b → j = stamp Γ t ∧ (answers Γ t).map sols = [S]) := by
  have hrec : (⟨metaName t, [Sem.ok S]⟩ : Stamp) = stamp Γ t := by
    rw [stamp_eta Γ t, hS]
  rw [hrec] at hit
  have hsound := sound_run (sound_record hm hq) ops
  obtain ⟨t', a, hcell, hj⟩ := validated_hit hsound hit
  refine ⟨⟨t', a, hcell, hj⟩, fun he => ⟨?_, recorded_answers Γ t S hS⟩⟩
  have hkeep := Heap.run_keeps_cell H ops hq he
  rw [hcell] at hkeep
  cases hkeep
  exact hj

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypingTransfer
