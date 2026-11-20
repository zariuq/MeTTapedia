import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.Machine

/-!
# The store's invariants, as properties of the bag a state reads as

The theorems of `Machine` are at states that read as the rows of a machine store. What that hypothesis holds of
the bag is stated here by itself, since it is part of what is trusted beside the operations.

* `Invariants B`: **no row of the bag occurs twice; two cells of one kind and key hold one value; two instruction
  rows at one counter are one row.** So there is one cell per kind and key (in particular one control cell and
  one flag cell) and one instruction row per counter.
* `storeRows_invariants`: **the rows of every store have the invariants.**
* `invariants_kept`: **they are kept by every admitted firing of the evaluated program**, at a state that reads
  as the rows of a store: the result reads as a bag with the invariants. With `Machine.machine_of_runs`, they hold
  at every state of every run from such a state.
* `not_invariants_of_two_cells`: a bag with two cells of one kind and key that hold two values does not have
  them. At such a bag the value a firing makes depends on which cell it reads
  (`Neighbour.two_values_admitted`, on the instruction step of `KernelStep`).

What is not proved: that the invariants alone, for a bag that also holds rows that are not the store's, give the
theorems of `Machine`; they are proved for bags that are exactly the rows of a store.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.Machine

open Mettapedia.Logic.LP
open NamesOnTheStep (Expr)
open Presentation.Schematic (Tm SState X E)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines (ReadsBag)

variable {W : Type}

/-- **The store's invariants, on a bag of rows**: no row occurs twice; cells of one kind and key hold one value;
instruction rows at one counter are one row. -/
structure Invariants (B : Multiset Expr) : Prop where
  nodup : B.Nodup
  cells : ∀ {kind key value value' : Expr}, cellE kind key value ∈ B → cellE kind key value' ∈ B →
    value = value'
  instrs : ∀ {pc op dst src next op' dst' src' next' : Expr}, instrE pc op dst src next ∈ B →
    instrE pc op' dst' src' next' ∈ B → op = op' ∧ dst = dst' ∧ src = src' ∧ next = next'

/-- An instruction row of a store is the row of an instruction of its table. -/
theorem instr_of_mem_storeRows (words : Words W) (m : Store W) {pc op dst src next : Expr}
    (inside : instrE pc op dst src next ∈ storeRows words m) :
    ∃ p ∈ m.points, instrE pc op dst src next = instrRow p (m.code p) := by
  unfold storeRows at inside
  rcases Multiset.mem_add.mp inside with front | inCode
  · rcases Multiset.mem_add.mp front with front | inRegs
    · rcases Multiset.mem_add.mp front with isCtrl | isFlag
      · exact absurd (Multiset.mem_singleton.mp isCtrl).symm cellE_ne_instrE
      · exact absurd (Multiset.mem_singleton.mp isFlag).symm cellE_ne_instrE
    · obtain ⟨d, -, same⟩ := Multiset.mem_map.mp inRegs
      exact absurd same cellE_ne_instrE
  · obtain ⟨p, inP, same⟩ := Multiset.mem_map.mp inCode
    exact ⟨p, Finset.mem_val.mp inP, same.symm⟩

/-- **Cells of one kind and key of a store hold one value.** -/
theorem storeRows_cells (words : Words W) (m : Store W) {kind key value value' : Expr}
    (one : cellE kind key value ∈ storeRows words m) (two : cellE kind key value' ∈ storeRows words m) :
    value = value' := by
  rcases cell_of_mem_storeRows words m one with ⟨k1, -, v1⟩ | ⟨k1, -, v1⟩ | ⟨d, -, k1, key1, v1⟩ <;>
    rcases cell_of_mem_storeRows words m two with ⟨k2, -, v2⟩ | ⟨k2, -, v2⟩ | ⟨d', -, k2, key2, v2⟩
  · exact v1.trans v2.symm
  · exact absurd (Expr.sym.inj (k1.symm.trans k2)) (by decide)
  · exact absurd (Expr.sym.inj (k1.symm.trans k2)) (by decide)
  · exact absurd (Expr.sym.inj (k1.symm.trans k2)) (by decide)
  · exact v1.trans v2.symm
  · exact absurd (Expr.sym.inj (k1.symm.trans k2)) (by decide)
  · exact absurd (Expr.sym.inj (k1.symm.trans k2)) (by decide)
  · exact absurd (Expr.sym.inj (k1.symm.trans k2)) (by decide)
  · have same : d = d' := Expr.sym.inj (key1.symm.trans key2)
    subst same
    exact v1.trans v2.symm

/-- **Instruction rows of a store at one counter are one row.** -/
theorem storeRows_instrs (words : Words W) (m : Store W) {pc op dst src next op' dst' src' next' : Expr}
    (one : instrE pc op dst src next ∈ storeRows words m)
    (two : instrE pc op' dst' src' next' ∈ storeRows words m) :
    op = op' ∧ dst = dst' ∧ src = src' ∧ next = next' := by
  obtain ⟨p, -, same⟩ := instr_of_mem_storeRows words m one
  obtain ⟨p', -, same'⟩ := instr_of_mem_storeRows words m two
  obtain ⟨hp, ho, hd, hs, hn⟩ := instrE_inj same
  obtain ⟨hp', ho', hd', hs', hn'⟩ := instrE_inj same'
  have samePoint : p = p' := Expr.sym.inj (hp.symm.trans hp')
  subst samePoint
  exact ⟨ho.trans ho'.symm, hd.trans hd'.symm, hs.trans hs'.symm, hn.trans hn'.symm⟩

/-- **No row of a store occurs twice.** -/
theorem storeRows_nodup (words : Words W) (m : Store W) : (storeRows words m).Nodup := by
  have regsNodup : (m.regs.val.map fun key => regRow key (words.enc (m.reg key))).Nodup :=
    Multiset.Nodup.map (fun a b same => Expr.sym.inj (cellE_inj same).2.1) m.regs.nodup
  have codeNodup : (m.points.val.map fun p => instrRow p (m.code p)).Nodup :=
    Multiset.Nodup.map (fun a b same => Expr.sym.inj (instrE_inj same).1) m.points.nodup
  unfold storeRows
  refine Multiset.nodup_add.mpr ⟨Multiset.nodup_add.mpr ⟨Multiset.nodup_add.mpr
    ⟨Multiset.nodup_singleton _, Multiset.nodup_singleton _, ?_⟩, regsNodup, ?_⟩, codeNodup, ?_⟩
  · exact Multiset.disjoint_left.mpr fun inCtrl inFlag =>
      absurd (Expr.sym.inj (cellE_inj ((Multiset.mem_singleton.mp inCtrl).symm.trans
        (Multiset.mem_singleton.mp inFlag))).1) (by decide)
  · exact Multiset.disjoint_left.mpr fun inFront inRegs => by
      obtain ⟨key, -, same⟩ := Multiset.mem_map.mp inRegs
      rcases Multiset.mem_add.mp inFront with isCtrl | isFlag
      · exact absurd (Expr.sym.inj (cellE_inj (same.trans (Multiset.mem_singleton.mp isCtrl))).1) (by decide)
      · exact absurd (Expr.sym.inj (cellE_inj (same.trans (Multiset.mem_singleton.mp isFlag))).1) (by decide)
  · exact Multiset.disjoint_left.mpr fun inCells inCode => by
      obtain ⟨p, -, same⟩ := Multiset.mem_map.mp inCode
      rcases Multiset.mem_add.mp inCells with front | inRegs
      · rcases Multiset.mem_add.mp front with isCtrl | isFlag
        · exact absurd ((Multiset.mem_singleton.mp isCtrl).symm.trans same.symm) cellE_ne_instrE
        · exact absurd ((Multiset.mem_singleton.mp isFlag).symm.trans same.symm) cellE_ne_instrE
      · obtain ⟨key, -, same'⟩ := Multiset.mem_map.mp inRegs
        exact absurd (same'.trans same.symm) cellE_ne_instrE

/-- **The rows of every store have the invariants.** -/
theorem storeRows_invariants (words : Words W) (m : Store W) : Invariants (storeRows words m) :=
  ⟨storeRows_nodup words m, fun one two => storeRows_cells words m one two,
    fun one two => storeRows_instrs words m one two⟩

/-- **The invariants are kept by every admitted firing of the evaluated program**, at a state that reads as the
rows of a store: the result reads as a bag with the invariants. -/
theorem invariants_kept {O : Type} [DecidableEq O] (words : Words W) (ops : ℕ → W → W → Option (W × W))
    {s : SState O} {m : Store W} (reads : ReadsBag s (storeRows words m))
    (f : Firing O E (evaluated (interp words ops) program) s.frame)
    (admitted : (step X O E (evaluated (interp words ops) program)).Admits (s := s) f) :
    ∃ B, ReadsBag (f.result X s) B ∧ Invariants B := by
  obtain ⟨m', -, reads'⟩ := machine_backward words ops reads f admitted
  exact ⟨_, reads', storeRows_invariants words m'⟩

/-- **A bag with two cells of one kind and key that hold two values does not have the invariants.** -/
theorem not_invariants_of_two_cells {B : Multiset Expr} {kind key value value' : Expr}
    (one : cellE kind key value ∈ B) (two : cellE kind key value' ∈ B) (different : value ≠ value') :
    ¬ Invariants B := fun invariants => different (invariants.cells one two)

#print axioms storeRows_cells
#print axioms storeRows_instrs
#print axioms storeRows_nodup
#print axioms storeRows_invariants
#print axioms invariants_kept
#print axioms not_invariants_of_two_cells

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.Machine
