import Mettapedia.OSLF.Syntax.RhoPayloadPresentation
import Mettapedia.GSLT.Causality.ResourceInteraction

/-!
# The rho calculus as interaction on a bag of atoms

A process class is determined by the bag of its atom classes. Communication
consumes an output atom and an input atom on one channel and adds the atoms of
the instantiated continuation. A drop consumes a dropped quotation and adds the
atoms of its code. Each step of either profile is exactly one such firing on
the bags of atoms.

Both communicating atoms are linear. Two communications whose atoms fit
together in one bag commute. An output wanted by two inputs, present once, is a
conflict: after either communication the other is disabled.
-/

noncomputable section

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoPayloadPresentation

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPolynomial (Rule)
open Mettapedia.GSLT
open Mettapedia.GSLT.Causality.ResourceInteraction

attribute [local instance] Classical.propDecidable

variable {Γ : Ctx sig}

/-! ## Atoms and their realization -/

/-- Every atom of a process is an atom class: its bag of atoms is itself. -/
theorem atomsQ_of_mem_atoms : {s : Srt} → (t : Term sig Γ s) → {x : Cls Γ Srt.pr} →
    x ∈ atoms t → atomsQ x = {x}
  | Srt.pr, .var v, x, h => by
      change x ∈ ({cls (.var v : Term sig Γ Srt.pr)} : Multiset _) at h
      rw [Multiset.mem_singleton.mp h]
      rfl
  | Srt.pr, .op Op.nil _, x, h => by
      change x ∈ (0 : Multiset _) at h
      simp at h
  | Srt.pr, .op Op.par (.cons a (.cons b .nil)), x, h => by
      change x ∈ atoms a + atoms b at h
      rcases Multiset.mem_add.mp h with h | h
      · exact atomsQ_of_mem_atoms a h
      · exact atomsQ_of_mem_atoms b h
  | Srt.pr, .op Op.out args, x, h => by
      change x ∈ ({cls (.op Op.out args : Term sig Γ Srt.pr)} : Multiset _) at h
      rw [Multiset.mem_singleton.mp h]
      rfl
  | Srt.pr, .op Op.inp args, x, h => by
      change x ∈ ({cls (.op Op.inp args : Term sig Γ Srt.pr)} : Multiset _) at h
      rw [Multiset.mem_singleton.mp h]
      rfl
  | Srt.pr, .op Op.drp args, x, h => by
      change x ∈ ({cls (.op Op.drp args : Term sig Γ Srt.pr)} : Multiset _) at h
      rw [Multiset.mem_singleton.mp h]
      rfl
  | Srt.nm, .var _, x, h => by
      change x ∈ (0 : Multiset _) at h
      simp at h
  | Srt.nm, .op Op.quo _, x, h => by
      change x ∈ (0 : Multiset _) at h
      simp at h
  | Srt.nm, .op (Op.free _) _, x, h => by
      change x ∈ (0 : Multiset _) at h
      simp at h

/-- A bag of atom classes. -/
def AtomBag (M : Multiset (Cls Γ Srt.pr)) : Prop := ∀ x ∈ M, atomsQ x = {x}

theorem atomBag_atoms (t : Term sig Γ Srt.pr) : AtomBag (atoms t) :=
  fun _ h => atomsQ_of_mem_atoms t h

/-- A process in parallel form, one representative per listed class. -/
def realizeList : List (Cls Γ Srt.pr) → Term sig Γ Srt.pr
  | [] => nilT
  | x :: xs => parT (Quotient.out x) (realizeList xs)

theorem cls_out (x : Cls Γ Srt.pr) : cls (Quotient.out x) = x :=
  Quotient.out_eq x

theorem atoms_realizeList : (L : List (Cls Γ Srt.pr)) → (∀ x ∈ L, atomsQ x = {x}) →
    atoms (realizeList L) = (L : Multiset (Cls Γ Srt.pr))
  | [], _ => rfl
  | x :: xs, h => by
      change atoms (Quotient.out x) + atoms (realizeList xs) = _
      rw [atoms_realizeList xs (fun y hy => h y (List.mem_cons_of_mem x hy))]
      have hx : atoms (Quotient.out x) = {x} := by
        rw [← atomsQ_cls, cls_out]
        exact h x List.mem_cons_self
      rw [hx]
      simp

/-- A process whose atoms are a given bag of atom classes. -/
def realize (M : Multiset (Cls Γ Srt.pr)) : Term sig Γ Srt.pr := realizeList M.toList

theorem atoms_realize {M : Multiset (Cls Γ Srt.pr)} (h : AtomBag M) : atoms (realize M) = M := by
  unfold realize
  rw [atoms_realizeList _ (fun x hx => h x (Multiset.mem_toList.mp hx)), Multiset.coe_toList]

theorem atomBag_add {M N : Multiset (Cls Γ Srt.pr)} (hM : AtomBag M) (hN : AtomBag N) :
    AtomBag (M + N) := fun x hx => (Multiset.mem_add.mp hx).elim (hM x) (hN x)

theorem atomBag_of_le {M N : Multiset (Cls Γ Srt.pr)} (hN : AtomBag N) (h : M ≤ N) :
    AtomBag M := fun x hx => hN x (Multiset.mem_of_le h hx)

/-! ## Rho as a resource system -/

/-- The data of a communication: channel, payload and continuation. -/
abbrev CommInstance (Γ : Ctx sig) : Type :=
  Term sig Γ Srt.nm × Term sig Γ Srt.pr × Term sig (Srt.pr :: Γ) Srt.pr

/-- A communication consumes its output and its input. -/
def commConsume (i : CommInstance Γ) : Multiset (Cls Γ Srt.pr) :=
  cls (outT i.1 i.2.1) ::ₘ cls (inpT i.1 i.2.2) ::ₘ 0

/-- A communication adds the atoms of the instantiated continuation. -/
def commProduce (i : CommInstance Γ) : Multiset (Cls Γ Srt.pr) :=
  atoms (inst i.2.2 i.2.1)

/-- The strict profile as a resource system over atom classes. -/
def strictSystem (Γ : Ctx sig) : System (Cls Γ Srt.pr) where
  Site := Unit
  Instance := fun _ => CommInstance Γ
  consume := fun i => commConsume i
  read := fun _ => 0
  produce := fun i => commProduce i

/-- The firings of the book profile. -/
inductive Firing where
  | comm
  | drop

/-- A communication, or the code of a dropped quotation. -/
def bookInstance (Γ : Ctx sig) : Firing → Type
  | .comm => CommInstance Γ
  | .drop => Term sig Γ Srt.pr

/-- A drop consumes the dropped quotation. -/
def bookConsume : {site : Firing} → bookInstance Γ site → Multiset (Cls Γ Srt.pr)
  | .comm, i => commConsume i
  | .drop, code => cls (drpT (quoT code)) ::ₘ 0

/-- A drop adds the atoms of its code. -/
def bookProduce : {site : Firing} → bookInstance Γ site → Multiset (Cls Γ Srt.pr)
  | .comm, i => commProduce i
  | .drop, code => atoms code

/-- The book profile as a resource system over atom classes. -/
def bookSystem (Γ : Ctx sig) : System (Cls Γ Srt.pr) where
  Site := Firing
  Instance := bookInstance Γ
  consume := fun i => bookConsume i
  read := fun _ => 0
  produce := fun i => bookProduce i

/-! ## Each step is one firing on the bags of atoms -/

private theorem pair_le {x y : Cls Γ Srt.pr} (others : Multiset (Cls Γ Srt.pr)) :
    x ::ₘ y ::ₘ 0 ≤ x ::ₘ y ::ₘ others :=
  Multiset.cons_le_cons x (Multiset.cons_le_cons y (Multiset.zero_le _))

private theorem pair_sub {x y : Cls Γ Srt.pr} (others : Multiset (Cls Γ Srt.pr)) :
    (x ::ₘ y ::ₘ others) - (x ::ₘ y ::ₘ 0) = others := by
  have split : x ::ₘ y ::ₘ others = (x ::ₘ y ::ₘ 0) + others := by
    rw [Multiset.cons_add, Multiset.cons_add, zero_add]
  rw [split, add_tsub_cancel_left]

private theorem one_sub {x : Cls Γ Srt.pr} (others : Multiset (Cls Γ Srt.pr)) :
    (x ::ₘ others) - (x ::ₘ 0) = others := by
  have split : x ::ₘ others = (x ::ₘ 0) + others := by
    rw [Multiset.cons_add, zero_add]
  rw [split, add_tsub_cancel_left]

/-- A drop shape is a firing of its code. -/
private theorem firing_of_dropShape {a b : Term sig Γ Srt.pr} (code : Term sig Γ Srt.pr)
    (others : Multiset (Cls Γ Srt.pr)) (hs : atoms a = cls (drpT (quoT code)) ::ₘ others)
    (ht : atoms b = atoms code + others) :
    cls (drpT (quoT code)) ::ₘ 0 + 0 ≤ atoms a ∧
      atoms b = atoms a - (cls (drpT (quoT code)) ::ₘ 0) + atoms code := by
  refine ⟨?_, ?_⟩
  · rw [add_zero, hs]
    exact Multiset.cons_le_cons _ (Multiset.zero_le _)
  · rw [hs, ht, one_sub, add_comm]

/-- A communication shape is a firing of its instance. -/
private theorem firing_of_commShape {a b : Term sig Γ Srt.pr} (c : Term sig Γ Srt.nm)
    (q : Term sig Γ Srt.pr) (K : Term sig (Srt.pr :: Γ) Srt.pr) (others : Multiset (Cls Γ Srt.pr))
    (hs : atoms a = cls (outT c q) ::ₘ cls (inpT c K) ::ₘ others)
    (ht : atoms b = atoms (inst K q) + others) :
    commConsume (c, q, K) + 0 ≤ atoms a ∧
      atoms b = atoms a - commConsume (c, q, K) + commProduce (c, q, K) := by
  refine ⟨?_, ?_⟩
  · rw [add_zero, hs]
    exact pair_le others
  · rw [hs, ht]
    unfold commConsume commProduce
    rw [pair_sub, add_comm]

/-- A firing of a communication is a step of either profile. -/
private theorem steps_of_commFiring (rest : List (Rule sig metas)) {a b : Term sig Γ Srt.pr}
    (i : CommInstance Γ) (enabled : commConsume i + 0 ≤ atoms a)
    (hb : atoms b = atoms a - commConsume i + commProduce i) :
    Steps (comm :: parCong :: rest) a b := by
  obtain ⟨c, q, K⟩ := i
  rw [add_zero] at enabled
  have bag : AtomBag (atoms a - commConsume (c, q, K)) :=
    atomBag_of_le (atomBag_atoms a) tsub_le_self
  set R := realize (atoms a - commConsume (c, q, K))
  have hR : atoms R = atoms a - commConsume (c, q, K) := atoms_realize bag
  have hC : atoms (parT (outT c q) (inpT c K)) = commConsume (c, q, K) := by
    change cls (outT c q) ::ₘ 0 + cls (inpT c K) ::ₘ 0 = cls (outT c q) ::ₘ cls (inpT c K) ::ₘ 0
    rw [Multiset.cons_add, zero_add]
  have hsource : EqClosure equations a (parT (parT (outT c q) (inpT c K)) R) := by
    apply cls_eq_iff.mp
    apply cls_eq_of_atoms_eq
    change atoms a = atoms (parT (outT c q) (inpT c K)) + atoms R
    rw [hC, hR, add_tsub_cancel_of_le enabled]
  have htarget : EqClosure equations (parT (inst K q) R) b := by
    apply cls_eq_iff.mp
    apply cls_eq_of_atoms_eq
    change atoms (inst K q) + atoms R = atoms b
    rw [hR, hb, add_comm]
    rfl
  exact steps_of_equiv hsource htarget (steps_parCong rest R (steps_comm rest c q K))

/-- **A step of the strict profile is exactly one communication on the bags of
atoms.** -/
theorem strict_step_iff (a b : Term sig Γ Srt.pr) :
    Steps strictRules a b ↔ (strictSystem Γ).theory.Step (atoms a) (atoms b) := by
  constructor
  · intro step
    rcases steps_inversion (rest := []) (Or.inl rfl) step with
      ⟨c, q, K, others, hs, ht⟩ | ⟨impossible, _⟩
    · obtain ⟨enabled, fired⟩ := firing_of_commShape c q K others hs ht
      exact ⟨(), (c, q, K), enabled, fired⟩
    · exact absurd impossible (by simp)
  · rintro ⟨_, i, enabled, hb⟩
    exact steps_of_commFiring [] i enabled hb

/-- **A step of the book profile is exactly one communication or one drop on the
bags of atoms.** -/
theorem book_step_iff (a b : Term sig Γ Srt.pr) :
    Steps bookRules a b ↔ (bookSystem Γ).theory.Step (atoms a) (atoms b) := by
  constructor
  · intro step
    rcases steps_inversion (rest := [drop]) (Or.inr rfl) step with
      ⟨c, q, K, others, hs, ht⟩ | ⟨_, code, others, hs, ht⟩
    · obtain ⟨enabled, fired⟩ := firing_of_commShape c q K others hs ht
      exact ⟨Firing.comm, (c, q, K), enabled, fired⟩
    · obtain ⟨enabled, fired⟩ := firing_of_dropShape code others hs ht
      exact ⟨Firing.drop, code, enabled, fired⟩
  · rintro ⟨site, i, enabled, hb⟩
    cases site with
    | comm => exact steps_of_commFiring [drop] i enabled hb
    | drop =>
        change cls (drpT (quoT i)) ::ₘ 0 + 0 ≤ atoms a at enabled
        change atoms b = atoms a - (cls (drpT (quoT i)) ::ₘ 0) + atoms i at hb
        rw [add_zero] at enabled
        have bag : AtomBag (atoms a - (cls (drpT (quoT i)) ::ₘ 0)) :=
          atomBag_of_le (atomBag_atoms a) tsub_le_self
        set R := realize (atoms a - (cls (drpT (quoT i)) ::ₘ 0))
        have hR : atoms R = atoms a - (cls (drpT (quoT i)) ::ₘ 0) := atoms_realize bag
        have hsource : EqClosure equations a (parT (drpT (quoT i)) R) := by
          apply cls_eq_iff.mp
          apply cls_eq_of_atoms_eq
          change atoms a = cls (drpT (quoT i)) ::ₘ 0 + atoms R
          rw [hR, add_tsub_cancel_of_le enabled]
        have htarget : EqClosure equations (parT i R) b := by
          apply cls_eq_iff.mp
          apply cls_eq_of_atoms_eq
          change atoms i + atoms R = atoms b
          rw [hR, hb, add_comm]
        exact steps_of_equiv hsource htarget (steps_parCong [drop] R (steps_drop i))


/-! ## Commuting squares and conflicts of rho -/

private theorem atomBag_fire (M : Multiset (Cls Γ Srt.pr)) (hM : AtomBag M) (i : CommInstance Γ) :
    AtomBag ((strictSystem Γ).fire M (site := ()) i) :=
  atomBag_add (atomBag_of_le hM tsub_le_self) (atomBag_atoms _)

private theorem enables_of_concurrent_left {M : Multiset (Cls Γ Srt.pr)} {i j : CommInstance Γ}
    (h : (strictSystem Γ).Concurrent M (site₁ := ()) (site₂ := ()) i j) :
    (strictSystem Γ).Enables M (site := ()) i :=
  le_trans (add_le_add (Multiset.le_add_right _ _) le_rfl) h.1

/-- **Two communications whose atoms fit together commute**: each order is two
steps of the strict profile, and they meet. -/
theorem strict_square {a : Term sig Γ Srt.pr} (i j : CommInstance Γ)
    (concurrent : (strictSystem Γ).Concurrent (atoms a) (site₁ := ()) (site₂ := ()) i j) :
    ∃ b₁ b₂ d : Term sig Γ Srt.pr,
      Steps strictRules a b₁ ∧ Steps strictRules b₁ d ∧
        Steps strictRules a b₂ ∧ Steps strictRules b₂ d := by
  set S := strictSystem Γ
  set M := atoms a
  have bagM : AtomBag M := atomBag_atoms a
  have bag₁ := atomBag_fire M bagM i
  have bag₂ := atomBag_fire M bagM j
  have bagD := atomBag_fire (S.fire M (site := ()) i) bag₁ j
  refine ⟨realize (S.fire M (site := ()) i), realize (S.fire M (site := ()) j),
    realize (S.fire (S.fire M (site := ()) i) (site := ()) j), ?_, ?_, ?_, ?_⟩
  · refine (strict_step_iff _ _).mpr ⟨(), i, enables_of_concurrent_left concurrent, ?_⟩
    exact atoms_realize bag₁
  · refine (strict_step_iff _ _).mpr ⟨(), j, ?_, ?_⟩
    · rw [atoms_realize bag₁]
      exact S.enables_fire concurrent
    · rw [atoms_realize bagD, atoms_realize bag₁]
  · refine (strict_step_iff _ _).mpr
      ⟨(), j, enables_of_concurrent_left (S.concurrent_symm concurrent), ?_⟩
    exact atoms_realize bag₂
  · refine (strict_step_iff _ _).mpr ⟨(), i, ?_, ?_⟩
    · rw [atoms_realize bag₂]
      exact S.enables_fire (S.concurrent_symm concurrent)
    · rw [atoms_realize bagD, atoms_realize bag₂]
      exact S.fire_comm concurrent

/-- **An output wanted by two inputs is a conflict.** When its class occurs once
among the atoms, the two communications are not concurrent, and after either
the other is disabled. -/
theorem strict_conflict {a : Term sig Γ Srt.pr} (c : Term sig Γ Srt.nm) (q : Term sig Γ Srt.pr)
    (K₁ K₂ : Term sig (Srt.pr :: Γ) Srt.pr) (once : (atoms a).count (cls (outT c q)) ≤ 1)
    (notBack : cls (outT c q) ∉ atoms (inst K₁ q)) :
    ¬ (strictSystem Γ).Concurrent (atoms a) (site₁ := ()) (site₂ := ()) (c, q, K₁) (c, q, K₂) ∧
      ¬ (strictSystem Γ).Enables
          ((strictSystem Γ).fire (atoms a) (site := ()) (c, q, K₁)) (site := ()) (c, q, K₂) :=
  have inConsume : ∀ K : Term sig (Srt.pr :: Γ) Srt.pr,
      cls (outT c q) ∈ (strictSystem Γ).consume (site := ()) (c, q, K) := fun K => by
    change cls (outT c q) ∈ cls (outT c q) ::ₘ cls (inpT c K) ::ₘ 0
    exact Multiset.mem_cons_self _ _
  ⟨(strictSystem Γ).not_concurrent_of_shared_consumption (atoms a) (site₁ := ()) (site₂ := ())
      (c, q, K₁) (c, q, K₂) (cls (outT c q)) (inConsume K₁) (inConsume K₂) once,
    (strictSystem Γ).disabled_after (atoms a) (site₁ := ()) (site₂ := ())
      (c, q, K₁) (c, q, K₂) (cls (outT c q)) (inConsume K₁) (inConsume K₂) once notBack⟩

/-- An output and an input are never one class. -/
theorem cls_outT_ne_cls_inpT (c c' : Term sig Γ Srt.nm) (q : Term sig Γ Srt.pr)
    (K : Term sig (Srt.pr :: Γ) Srt.pr) : cls (outT c q) ≠ cls (inpT c' K) := by
  intro same
  have parts := outParts_invariant (cls_eq_iff.mp same)
  change ({(cls c, cls q)} : Multiset _) = 0 at parts
  exact Multiset.singleton_ne_zero _ parts

/-! ## Controls on closed processes -/

/-- The channel `@0`. -/
def zeroChannel : Term sig [] Srt.nm := quoT nilT

/-- `@0!(0)`. -/
def zeroOutput : Term sig [] Srt.pr := outT zeroChannel nilT

/-- `for(z <- @0){0}`. -/
def idleInput : Term sig [] Srt.pr := inpT zeroChannel nilT

/-- `for(z <- @0){@0!(0)}`, an input that resends. -/
def resendInput : Term sig [] Srt.pr := inpT zeroChannel (outT (quoT nilT) nilT)

/-- `@0!(0) | for(z <- @0){0} | for(z <- @0){@0!(0)}`: one output, two inputs. -/
def oneOutputTwoInputs : Term sig [] Srt.pr := parT (parT zeroOutput idleInput) resendInput

/-- **One output, two inputs: a run takes one of them.** The two communications
conflict, and after the idle input takes the output, the resending input cannot. -/
theorem one_output_two_inputs_conflict :
    ¬ (strictSystem []).Concurrent (atoms oneOutputTwoInputs) (site₁ := ()) (site₂ := ())
        (zeroChannel, nilT, nilT) (zeroChannel, nilT, outT (quoT nilT) nilT) ∧
      ¬ (strictSystem []).Enables
          ((strictSystem []).fire (atoms oneOutputTwoInputs) (site := ())
            (zeroChannel, nilT, nilT)) (site := ()) (zeroChannel, nilT, outT (quoT nilT) nilT) := by
  refine strict_conflict zeroChannel nilT nilT (outT (quoT nilT) nilT) ?_ ?_
  · change ((cls zeroOutput ::ₘ 0 + cls idleInput ::ₘ 0) + cls resendInput ::ₘ 0).count
        (cls (outT zeroChannel nilT)) ≤ 1
    have h₁ := cls_outT_ne_cls_inpT zeroChannel zeroChannel nilT nilT
    have h₂ := cls_outT_ne_cls_inpT zeroChannel zeroChannel nilT (outT (quoT nilT) nilT)
    simp only [Multiset.count_add, Multiset.count_cons, Multiset.count_zero]
    unfold zeroOutput idleInput resendInput
    simp [h₁, h₂]
  · change cls (outT zeroChannel nilT) ∉ (0 : Multiset _)
    simp

/-- `@0!(0) | @0!(0) | for(z <- @0){0} | for(z <- @0){0}`: two copies of one
communication. -/
def twoCopies : Term sig [] Srt.pr :=
  parT (parT zeroOutput zeroOutput) (parT idleInput idleInput)

/-- **Two copies of one communication commute.** The same instance fires on each
copy, in either order; independence of sites could not relate them. -/
theorem two_copies_commute :
    ∃ b₁ b₂ d : Term sig [] Srt.pr,
      Steps strictRules twoCopies b₁ ∧ Steps strictRules b₁ d ∧
        Steps strictRules twoCopies b₂ ∧ Steps strictRules b₂ d := by
  refine strict_square (zeroChannel, nilT, nilT) (zeroChannel, nilT, nilT) ⟨?_, ?_⟩ <;>
  · change (cls zeroOutput ::ₘ cls idleInput ::ₘ 0) + (cls zeroOutput ::ₘ cls idleInput ::ₘ 0) + 0 ≤
      (cls zeroOutput ::ₘ 0 + cls zeroOutput ::ₘ 0) + (cls idleInput ::ₘ 0 + cls idleInput ::ₘ 0)
    apply le_of_eq
    have pair : ∀ x y : Cls [] Srt.pr, x ::ₘ y ::ₘ (0 : Multiset _) = (x ::ₘ 0) + (y ::ₘ 0) := by
      intro x y
      rw [Multiset.cons_add, zero_add]
    rw [pair, add_zero]
    ac_rfl

#print axioms strict_step_iff
#print axioms book_step_iff
#print axioms strict_square
#print axioms strict_conflict
#print axioms one_output_two_inputs_conflict
#print axioms two_copies_commute

end Mettapedia.OSLF.Binding.RhoPayloadPresentation
