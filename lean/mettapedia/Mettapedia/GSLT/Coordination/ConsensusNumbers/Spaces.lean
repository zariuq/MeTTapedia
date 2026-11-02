import Mettapedia.GSLT.Coordination.ConsensusNumbers.Registers

/-!
# A space with MeTTa's separate operations

A space holds a bag of atoms. MeTTa's operations on it are each atomic on their own:

* `add a` adds one occurrence of `a` (`add-atom`);
* `remove a` removes one occurrence of `a` if there is one (`remove-atom` in Hyperon
  Experimental);
* `removeWhere p` removes every occurrence of every atom satisfying `p` (`remove-atom` in PeTTa,
  which retracts every atom unifying with its argument; `removeWhere (· = a)` clears all copies
  of `a`);
* `query p` answers the bag of atoms satisfying `p`, changing nothing (`match`, `get-atoms`; any
  answer computed from the matching atoms is computed by the asking process from this one).

Two versions differ only in what a removal answers:

* `separateSpace`: a removal reports whether it removed something.
  Example: in the space `{token}`, the first `remove token` answers `removed true`, the second
  `removed false`.
* `silentSpace`: a removal answers only `ack`, whether or not it removed anything. This is what
  the implementations do for atoms that are data: Hyperon Experimental's `remove-atom` answers the
  unit atom, PeTTa's answers `true` after `retractall`, which always succeeds, and CeTTa's answers
  the unit atom or PeTTa's success value.

## Results

* **Silent removal gives consensus number one** (`silentSpace_hasConsensusNumber_one`): every pair
  of operations hides its order from one of its two processes (`silentSpace_pairCannotOrder`).
  This holds with any number of spaces and registers used together
  (`silentSpaces_registers_not_solvable_two`). So the separate operations, as the three
  implementations provide them for data atoms, cannot give two processes consensus. (PeTTa's
  removal of an equation atom `(= ...)` does report whether a compiled clause went away; that path
  is a reporting removal.)
* **Reported removal gives consensus number two** (`separateSpace_hasConsensusNumber_two`):
  * every pair of operations hides its order from a bystander (`separateSpace_bystander`): two
    removals of the last copy of `a` leave the same bag in both orders, and only their own two
    processes learn who won;
  * two processes do reach consensus (`separateSpace_solvable_two`): each adds its proposal, then
    removes the single `token`; the one whose removal reports success decides its own proposal,
    the other reads the winner's proposal (a test-and-set race).
  * The bound holds with any number of spaces and registers used together
    (`separateSpaces_registers_not_solvable_three`).

## Controls

* `Controls.remove_remove_bystander_only`: two removals of the one `token` hide their order from a
  bystander, and from neither of the two removers: the reported removal is exactly what lifts the
  consensus number from one to two.
* `Controls.silent_remove_remove_hidden`: with silent removal the same pair is hidden from the
  first remover.
* `Controls.tas_race_solves`: the test-and-set race over natural-number atoms solves consensus for
  two processes.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Coordination.ConsensusNumbers

/-- MeTTa's separate operations on a space. -/
inductive SpaceOp (A : Type) where
  | add (a : A)
  | remove (a : A)
  | removeWhere (p : A → Bool)
  | query (p : A → Bool)

/-- What an operation on a space answers. -/
inductive SpaceReply (A : Type) where
  | ack
  | removed (ok : Bool)
  | matches (m : Multiset A)
  | fired (ok : Bool)

variable {A : Type} [DecidableEq A]

/-- The bag after an operation. -/
def spaceNext (M : Multiset A) : SpaceOp A → Multiset A
  | .add a => a ::ₘ M
  | .remove a => M.erase a
  | .removeWhere p => M.filter fun b => p b = false
  | .query _ => M

/-- Answers with reported removal. -/
def spaceReply (M : Multiset A) : SpaceOp A → SpaceReply A
  | .add _ => .ack
  | .remove a => .removed (decide (a ∈ M))
  | .removeWhere p => .removed (decide (M.filter (fun b => p b = true) ≠ 0))
  | .query p => .matches (M.filter fun b => p b = true)

/-- Answers with silent removal. -/
def silentReply (M : Multiset A) : SpaceOp A → SpaceReply A
  | .add _ => .ack
  | .remove _ => .ack
  | .removeWhere _ => .ack
  | .query p => .matches (M.filter fun b => p b = true)

variable (A) in
/-- A space with MeTTa's separate operations, removals reporting success. -/
abbrev separateSpace : DetObject where
  State := Multiset A
  Op := SpaceOp A
  Res := SpaceReply A
  apply M op := (spaceNext M op, spaceReply M op)

variable (A) in
/-- A space with MeTTa's separate operations, removals answering nothing. -/
abbrev silentSpace : DetObject where
  State := Multiset A
  Op := SpaceOp A
  Res := SpaceReply A
  apply M op := (spaceNext M op, silentReply M op)

/-! ## How the bag changes in the two orders -/

theorem count_erase' (c x : A) (M : Multiset A) :
    (M.erase x).count c = if c = x then M.count c - 1 else M.count c := by
  split_ifs with h
  · subst h; exact Multiset.count_erase_self _ _
  · exact Multiset.count_erase_of_ne h _

theorem add_remove_comm {M : Multiset A} {x y : A} (h : y ∈ M ∨ x ≠ y) :
    (x ::ₘ M).erase y = x ::ₘ M.erase y := by
  by_cases same : x = y
  · subst same
    rcases h with h | h
    · rw [Multiset.erase_cons_head, Multiset.cons_erase h]
    · exact absurd rfl h
  · exact Multiset.erase_cons_tail _ same

omit [DecidableEq A] in
theorem add_removeWhere_comm {M : Multiset A} {x : A} {p : A → Bool} (h : p x = false) :
    (x ::ₘ M).filter (fun b => p b = false) = x ::ₘ M.filter (fun b => p b = false) :=
  Multiset.filter_cons_of_pos _ h

omit [DecidableEq A] in
theorem add_removeWhere_hit {M : Multiset A} {x : A} {p : A → Bool} (h : p x = true) :
    (x ::ₘ M).filter (fun b => p b = false) = M.filter (fun b => p b = false) :=
  Multiset.filter_cons_of_neg _ (by simp [h])

theorem remove_removeWhere_comm (M : Multiset A) (x : A) (p : A → Bool) :
    (M.erase x).filter (fun b => p b = false) = (M.filter (fun b => p b = false)).erase x := by
  ext c
  simp only [Multiset.count_filter, count_erase']
  split_ifs <;> simp_all

theorem removeWhere_comm (M : Multiset A) (p q : A → Bool) :
    (M.filter (fun b => p b = false)).filter (fun b => q b = false) =
      (M.filter (fun b => q b = false)).filter (fun b => p b = false) := by
  ext c
  simp only [Multiset.count_filter]
  split_ifs <;> simp_all

omit [DecidableEq A] in
theorem removeWhere_miss {M : Multiset A} {p : A → Bool} (h : M.filter (fun b => p b = true) = 0) :
    M.filter (fun b => p b = false) = M := by
  refine Multiset.filter_eq_self.mpr fun a mem => ?_
  have := Multiset.filter_eq_nil.mp h a mem
  simpa using this

theorem remove_absent {M : Multiset A} {y : A} (h : y ∉ M) : M.erase y = M :=
  Multiset.erase_of_notMem h

/-! ## Reported removal: a bystander cannot order -/

section Separate

theorem sep_add_add (M : Multiset A) (x y : A) :
    BystanderCannotOrder (separateSpace A) M (.add x) (.add y) :=
  Or.inr (Multiset.cons_swap y x M)

theorem sep_add_remove (M : Multiset A) (x y : A) :
    BystanderCannotOrder (separateSpace A) M (.add x) (.remove y) := by
  by_cases h : y ∈ M ∨ x ≠ y
  · exact Or.inr (add_remove_comm h)
  · have absent : y ∉ M := fun mem => h (Or.inl mem)
    exact Or.inl (Or.inr (.noChange (remove_absent absent)))

theorem sep_add_removeWhere (M : Multiset A) (x : A) (p : A → Bool) :
    BystanderCannotOrder (separateSpace A) M (.add x) (.removeWhere p) := by
  by_cases miss : M.filter (fun b => p b = true) = 0
  · exact Or.inl (Or.inr (.noChange (removeWhere_miss miss)))
  · by_cases px : p x = true
    · refine Or.inl (Or.inl (.overwritten (Prod.ext (add_removeWhere_hit px) ?_)))
      have hit : (spaceNext M (.add x)).filter (fun b => p b = true) ≠ 0 := by
        simp only [spaceNext]
        rw [Multiset.filter_cons_of_pos (p := fun b => p b = true) M px]
        exact Multiset.cons_ne_zero
      show SpaceReply.removed (decide (_ ≠ 0)) = SpaceReply.removed (decide (_ ≠ 0))
      rw [decide_eq_true hit, decide_eq_true miss]
    · exact Or.inr (add_removeWhere_comm (by simpa using px))

theorem sep_remove_remove (M : Multiset A) (x y : A) :
    BystanderCannotOrder (separateSpace A) M (.remove x) (.remove y) :=
  Or.inr (Multiset.erase_comm M x y)

theorem sep_remove_removeWhere (M : Multiset A) (x : A) (p : A → Bool) :
    BystanderCannotOrder (separateSpace A) M (.remove x) (.removeWhere p) :=
  Or.inr (remove_removeWhere_comm M x p)

theorem sep_removeWhere_removeWhere (M : Multiset A) (p q : A → Bool) :
    BystanderCannotOrder (separateSpace A) M (.removeWhere p) (.removeWhere q) :=
  Or.inr (removeWhere_comm M p q)

/-- **A bystander cannot tell the order of any two separate operations.** -/
theorem separateSpace_bystander : ∀ M a b, BystanderCannotOrder (separateSpace A) M a b := by
  intro M a b
  cases a with
  | query p => exact Or.inl (Or.inl (.noChange rfl))
  | add x =>
      cases b with
      | query q => exact Or.inl (Or.inr (.noChange rfl))
      | add y => exact sep_add_add M x y
      | remove y => exact sep_add_remove M x y
      | removeWhere q => exact sep_add_removeWhere M x q
  | remove x =>
      cases b with
      | query q => exact Or.inl (Or.inr (.noChange rfl))
      | add y => exact (sep_add_remove M y x).symm
      | remove y => exact sep_remove_remove M x y
      | removeWhere q => exact sep_remove_removeWhere M x q
  | removeWhere p =>
      cases b with
      | query q => exact Or.inl (Or.inr (.noChange rfl))
      | add y => exact (sep_add_removeWhere M y p).symm
      | remove y => exact (sep_remove_removeWhere M y p).symm
      | removeWhere q => exact sep_removeWhere_removeWhere M p q

/-- **No three-process consensus from a space with separate operations.** -/
theorem separateSpace_not_solvable_three {n : ℕ} (three : 3 ≤ n) :
    ¬ Solvable (separateSpace A).toObject n Bool :=
  not_solvable_of_bystanderCannotOrder three separateSpace_bystander

end Separate

/-! ## Silent removal: a process of the pair cannot order -/

section Silent

theorem silent_add_remove (M : Multiset A) (x y : A) :
    PairCannotOrder (silentSpace A) M (.add x) (.remove y) := by
  by_cases h : y ∈ M ∨ x ≠ y
  · exact Or.inl (.commutes (add_remove_comm h) rfl)
  · have absent : y ∉ M := fun mem => h (Or.inl mem)
    exact Or.inr (.noChange (remove_absent absent))

theorem silent_add_removeWhere (M : Multiset A) (x : A) (p : A → Bool) :
    PairCannotOrder (silentSpace A) M (.add x) (.removeWhere p) := by
  by_cases miss : M.filter (fun b => p b = true) = 0
  · exact Or.inr (.noChange (removeWhere_miss miss))
  · by_cases px : p x = true
    · exact Or.inl (.overwritten (Prod.ext (add_removeWhere_hit px) rfl))
    · exact Or.inl (.commutes (add_removeWhere_comm (by simpa using px)) rfl)

/-- **One of the two processes cannot tell the order of any two operations, when removal is
silent.** -/
theorem silentSpace_pairCannotOrder : ∀ M a b, PairCannotOrder (silentSpace A) M a b := by
  intro M a b
  cases a with
  | query p => exact Or.inl (.noChange rfl)
  | add x =>
      cases b with
      | query q => exact Or.inr (.noChange rfl)
      | add y => exact Or.inl (.commutes (Multiset.cons_swap y x M) rfl)
      | remove y => exact silent_add_remove M x y
      | removeWhere q => exact silent_add_removeWhere M x q
  | remove x =>
      cases b with
      | query q => exact Or.inr (.noChange rfl)
      | add y => exact (silent_add_remove M y x).symm
      | remove y => exact Or.inl (.commutes (Multiset.erase_comm M x y) rfl)
      | removeWhere q => exact Or.inl (.commutes (remove_removeWhere_comm M x q) rfl)
  | removeWhere p =>
      cases b with
      | query q => exact Or.inr (.noChange rfl)
      | add y => exact (silent_add_removeWhere M y p).symm
      | remove y => exact Or.inl (.commutes (remove_removeWhere_comm M y p).symm rfl)
      | removeWhere q => exact Or.inl (.commutes (removeWhere_comm M p q) rfl)

/-- **A space whose removals answer nothing has consensus number one.** -/
theorem silentSpace_hasConsensusNumber_one : HasConsensusNumber (silentSpace A).toObject 1 :=
  hasConsensusNumber_one (T := silentSpace A) 0 silentSpace_pairCannotOrder

end Silent

/-! ## Many spaces and registers together -/

section Together

variable (K ι V : Type) [DecidableEq K] [DecidableEq ι]

variable (A) in
/-- Spaces named by `K`, with reported removal, beside the registers named by `ι`. -/
abbrev separateSpacesAndRegisters : DetObject :=
  DetObject.pi fun k : Option K => match k with
    | none => registers ι V
    | some _ => separateSpace A

variable (A) in
/-- Spaces named by `K`, with silent removal, beside the registers named by `ι`. -/
abbrev silentSpacesAndRegisters : DetObject :=
  DetObject.pi fun k : Option K => match k with
    | none => registers ι V
    | some _ => silentSpace A

/-- **No three-process consensus from any number of spaces with separate operations and
registers.** -/
theorem separateSpaces_registers_not_solvable_three {n : ℕ} (three : 3 ≤ n) :
    ¬ Solvable (separateSpacesAndRegisters A K ι V).toObject n Bool := by
  refine not_solvable_of_bystanderCannotOrder three (pi_bystanderCannotOrder ?_)
  rintro (_ | _) s a b
  · exact (registers_pairCannotOrder s a b).bystander
  · exact separateSpace_bystander s a b

/-- **No two-process consensus from any number of spaces with silent removal and registers.**
This is Hyperon Experimental's toolkit: `add-atom`, `remove-atom` answering the unit atom,
`match`, and state atoms (registers). -/
theorem silentSpaces_registers_not_solvable_two {n : ℕ} (two : 2 ≤ n) :
    ¬ Solvable (silentSpacesAndRegisters A K ι V).toObject n Bool := by
  refine not_solvable_of_pairCannotOrder two (pi_pairCannotOrder ?_)
  rintro (_ | _) s a b
  · exact registers_pairCannotOrder s a b
  · exact silentSpace_pairCannotOrder s a b

end Together

/-! ## Two processes reach consensus by a test-and-set race -/

section TestAndSet

variable {V : Type}

/-- A process of the race: about to post its proposal, about to remove the token, lost and about
to read, decided its own proposal, or decided the winner's. -/
inductive TasLocal (V : Type) where
  | start (v : V)
  | raced (v : V)
  | lost (v : V)
  | won (v : V)
  | adopted (v : V)

variable (token : A) (prop : Fin 2 → V → A)

open Classical in
/-- Is the atom a proposal of process `j`? -/
noncomputable def isPropOf (j : Fin 2) (a : A) : Bool := decide (∃ w, prop j w = a)

open Classical in
/-- The proposal of process `j` found in `m`, or `v` if there is none. -/
noncomputable def pickProp (j : Fin 2) (m : Multiset A) (v : V) : V :=
  if h : ∃ w, prop j w ∈ m then h.choose else v

/-- The test-and-set race over a space starting as `{token}`. -/
noncomputable abbrev tasProtocol : Protocol (separateSpace A).toObject 2 V where
  Local := TasLocal V
  start _ v := .start v
  init := {token}
  action i
    | .start v => .invoke (.add (prop i v))
    | .raced _ => .invoke (.remove token)
    | .lost _ => .invoke (.query (isPropOf prop i.rev))
    | .won v => .decide v
    | .adopted v => .decide v
  next i
    | .start v, _ => .raced v
    | .raced v, .removed true => .won v
    | .raced v, _ => .lost v
    | .lost v, .matches m => .adopted (pickProp prop i.rev m v)
    | .lost v, _ => .lost v
    | .won v, _ => .won v
    | .adopted v, _ => .adopted v

/-- Where a process is in the race. -/
inductive Phase where
  | start | raced | lost | won | adopted
  deriving DecidableEq

variable {token prop}

/-- The local state of process `i` at a phase. -/
def locOf (x : Fin 2 → V) (i : Fin 2) : Phase → TasLocal V
  | .start => .start (x i)
  | .raced => .raced (x i)
  | .lost => .lost (x i)
  | .won => .won (x i)
  | .adopted => .adopted (x i.rev)

variable (token prop) in
/-- The bag at given phases: the token until someone won, and each posted proposal. -/
def board (x : Fin 2 → V) (p q : Phase) : Multiset A :=
  (if p = .won ∨ q = .won then 0 else {token}) +
    ((if p = .start then 0 else {prop 0 (x 0)}) + (if q = .start then 0 else {prop 1 (x 1)}))

/-- The phases that occur together: at most one winner, and a loser only beside a winner. -/
def Allowed (p q : Phase) : Prop :=
  ¬ (p = .won ∧ q = .won) ∧ ((p = .lost ∨ p = .adopted) → q = .won) ∧
    ((q = .lost ∨ q = .adopted) → p = .won)

instance (p q : Phase) : Decidable (Allowed p q) := by unfold Allowed; infer_instance

variable (token prop) in
/-- The reachable configurations of the race. -/
def TasInv (x : Fin 2 → V) (C : (tasProtocol token prop).Config) : Prop :=
  ∃ p q, Allowed p q ∧ C.loc 0 = locOf x 0 p ∧ C.loc 1 = locOf x 1 q ∧
    C.obj = board token prop x p q

variable (prop_inj : ∀ i v j w, prop i v = prop j w → i = j ∧ v = w)
  (token_ne : ∀ i v, prop i v ≠ token)

omit [DecidableEq A] in
include token_ne in
theorem token_mem_board {x : Fin 2 → V} {p q : Phase} :
    token ∈ board token prop x p q ↔ ¬ (p = .won ∨ q = .won) := by
  unfold board
  constructor
  · intro mem won
    rw [if_pos won, zero_add] at mem
    rcases Multiset.mem_add.mp mem with m | m <;> split_ifs at m <;> simp at m
    · exact token_ne _ _ m.symm
    · exact token_ne _ _ m.symm
  · intro nowon
    rw [if_neg nowon]
    exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_singleton_self _))

omit [DecidableEq A] in
include prop_inj token_ne in
theorem pickProp_board {x : Fin 2 → V} {j : Fin 2} {p q : Phase}
    (posted : prop j (x j) ∈ board token prop x p q) (v : V) :
    pickProp prop j ((board token prop x p q).filter fun a => isPropOf prop j a = true) v = x j := by
  have mem : prop j (x j) ∈ (board token prop x p q).filter fun a => isPropOf prop j a = true :=
    Multiset.mem_filter.mpr ⟨posted, by simp [isPropOf]⟩
  have only : ∀ u, prop j u ∈ (board token prop x p q).filter (fun a => isPropOf prop j a = true) →
      u = x j := by
    intro u m
    have m := (Multiset.mem_filter.mp m).1
    unfold board at m
    rcases Multiset.mem_add.mp m with m | m
    · split_ifs at m <;> simp at m
      exact absurd m (token_ne _ _)
    rcases Multiset.mem_add.mp m with m | m <;> split_ifs at m <;> simp at m
    · obtain ⟨rfl, rfl⟩ := prop_inj _ _ _ _ m; rfl
    · obtain ⟨rfl, rfl⟩ := prop_inj _ _ _ _ m; rfl
  unfold pickProp
  rw [dif_pos ⟨_, mem⟩]
  exact only _ (Exists.choose_spec (p := fun w => prop j w ∈ _) ⟨_, mem⟩)

@[simp] theorem rev_zero : (0 : Fin 2).rev = 1 := rfl
@[simp] theorem rev_one : (1 : Fin 2).rev = 0 := rfl

section Steps

variable {C : (tasProtocol token prop).Config} {i : Fin 2} {v : V}

theorem tas_go_start (hc : C.loc i = .start v) :
    (tasProtocol token prop).go C i = ⟨prop i v ::ₘ C.obj, Function.update C.loc i (.raced v)⟩ := by
  rw [Protocol.go_of_invoke (op := (SpaceOp.add (prop i v) : SpaceOp A)) (by rw [hc]), hc]
  rfl

theorem tas_go_raced_win (hc : C.loc i = .raced v) (present : token ∈ C.obj) :
    (tasProtocol token prop).go C i = ⟨C.obj.erase token, Function.update C.loc i (.won v)⟩ := by
  rw [Protocol.go_of_invoke (op := (SpaceOp.remove token : SpaceOp A)) (by rw [hc]), hc]
  simp [spaceNext, spaceReply, present]

theorem tas_go_raced_lose (hc : C.loc i = .raced v) (absent : token ∉ C.obj) :
    (tasProtocol token prop).go C i = ⟨C.obj, Function.update C.loc i (.lost v)⟩ := by
  rw [Protocol.go_of_invoke (op := (SpaceOp.remove token : SpaceOp A)) (by rw [hc]), hc]
  simp [spaceNext, spaceReply, absent]

theorem tas_go_lost (hc : C.loc i = .lost v) :
    (tasProtocol token prop).go C i = ⟨C.obj, Function.update C.loc i
      (.adopted (pickProp prop i.rev (C.obj.filter fun a => isPropOf prop i.rev a = true) v))⟩ := by
  rw [Protocol.go_of_invoke (op := (SpaceOp.query (isPropOf prop i.rev) : SpaceOp A)) (by rw [hc]), hc]
  rfl

theorem tas_go_won (hc : C.loc i = .won v) : (tasProtocol token prop).go C i = C :=
  Protocol.go_of_decide (v := v) (by rw [hc])

theorem tas_go_adopted (hc : C.loc i = .adopted v) : (tasProtocol token prop).go C i = C :=
  Protocol.go_of_decide (v := v) (by rw [hc])

end Steps

include prop_inj token_ne in
/-- **The race keeps its invariant.** -/
theorem tas_inv_go {x : Fin 2 → V} {C : (tasProtocol token prop).Config}
    (inv : TasInv token prop x C) (i : Fin 2) : TasInv token prop x ((tasProtocol token prop).go C i) := by
  obtain ⟨p, q, allowed, h0, h1, hobj⟩ := inv
  obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  · cases p with
    | start =>
        rw [tas_go_start h0]
        refine ⟨.raced, q, ?_, by simp [locOf], by simp [h1], ?_⟩
        · revert allowed; cases q <;> decide
        · rw [hobj]; simp [board, ← Multiset.singleton_add]; abel
    | raced =>
        by_cases won : q = .won
        · subst won
          have absent : token ∉ C.obj := by rw [hobj, token_mem_board token_ne]; simp
          rw [tas_go_raced_lose h0 absent]
          exact ⟨.lost, .won, by decide, by simp [locOf], by simp [h1], by rw [hobj]; simp [board]⟩
        · have present : token ∈ C.obj := by rw [hobj, token_mem_board token_ne]; simp [won]
          rw [tas_go_raced_win h0 present]
          refine ⟨.won, q, ?_, by simp [locOf], by simp [h1], ?_⟩
          · revert allowed won; cases q <;> decide
          · rw [hobj]; simp [board, won]
            rw [Multiset.erase_cons_tail _ (token_ne 0 (x 0)), Multiset.erase_cons_head]
    | lost =>
        have won : q = .won := allowed.2.1 (Or.inl rfl)
        subst won
        rw [tas_go_lost h0]
        refine ⟨.adopted, .won, by decide, ?_, by simp [h1], by rw [hobj]; simp [board]⟩
        simp only [Function.update_self, locOf, rev_zero]
        rw [hobj, pickProp_board prop_inj token_ne (by simp [board])]
    | won => rw [tas_go_won h0]; exact ⟨_, _, allowed, h0, h1, hobj⟩
    | adopted => rw [tas_go_adopted h0]; exact ⟨_, _, allowed, h0, h1, hobj⟩
  · cases q with
    | start =>
        rw [tas_go_start h1]
        refine ⟨p, .raced, ?_, by simp [h0], by simp [locOf], ?_⟩
        · revert allowed; cases p <;> decide
        · rw [hobj]; simp [board, ← Multiset.singleton_add]; abel
    | raced =>
        by_cases won : p = .won
        · subst won
          have absent : token ∉ C.obj := by rw [hobj, token_mem_board token_ne]; simp
          rw [tas_go_raced_lose h1 absent]
          exact ⟨.won, .lost, by decide, by simp [h0], by simp [locOf], by rw [hobj]; simp [board]⟩
        · have present : token ∈ C.obj := by rw [hobj, token_mem_board token_ne]; simp [won]
          rw [tas_go_raced_win h1 present]
          refine ⟨p, .won, ?_, by simp [h0], by simp [locOf], ?_⟩
          · revert allowed won; cases p <;> decide
          · rw [hobj]; simp [board, won]
    | lost =>
        have won : p = .won := allowed.2.2 (Or.inl rfl)
        subst won
        rw [tas_go_lost h1]
        refine ⟨.won, .adopted, by decide, by simp [h0], ?_, by rw [hobj]; simp [board]⟩
        simp only [Function.update_self, locOf, rev_one]
        rw [hobj, pickProp_board prop_inj token_ne (by simp [board])]
    | won => rw [tas_go_won h1]; exact ⟨_, _, allowed, h0, h1, hobj⟩
    | adopted => rw [tas_go_adopted h1]; exact ⟨_, _, allowed, h0, h1, hobj⟩

include prop_inj token_ne in
theorem tas_inv_of_reach {x : Fin 2 → V} {C : (tasProtocol token prop).Config}
    (reach : (tasProtocol token prop).Reach x C) : TasInv token prop x C := by
  obtain ⟨σ, rfl⟩ := Protocol.reach_iff.mp reach
  clear reach
  suffices ∀ D, TasInv token prop x D → TasInv token prop x ((tasProtocol token prop).run D σ) from
    this _ ⟨.start, .start, by decide, rfl, rfl, by simp [board, Protocol.initial]⟩
  induction σ with
  | nil => exact fun D h => h
  | cons i σ ih => exact fun D h => ih _ (tas_inv_go prop_inj token_ne h i)

/-- A process decided its own input after winning, or the other's input after losing. -/
theorem tas_decided {x : Fin 2 → V} {i : Fin 2} {ph : Phase} {v : V}
    (h : (tasProtocol token prop).action i (locOf x i ph) = .decide v) :
    (ph = .won ∧ v = x i) ∨ (ph = .adopted ∧ v = x i.rev) := by
  cases ph <;> simp [locOf] at h ⊢ <;> exact h.symm

/-- Steps left before a process decides. -/
def tasRank : TasLocal V → ℕ
  | .start _ => 3
  | .raced _ => 2
  | .lost _ => 1
  | .won _ => 0
  | .adopted _ => 0

theorem tas_rank_go_le (C : (tasProtocol token prop).Config) (i j : Fin 2) :
    tasRank (((tasProtocol token prop).go C j).loc i) ≤ tasRank (C.loc i) := by
  by_cases same : i = j
  · subst same
    cases hc : C.loc i with
    | start v => rw [tas_go_start hc]; simp [tasRank]
    | raced v =>
        by_cases present : token ∈ C.obj
        · rw [tas_go_raced_win hc present]; simp [tasRank]
        · rw [tas_go_raced_lose hc present]; simp [tasRank]
    | lost v => rw [tas_go_lost hc]; simp [tasRank]
    | won v => rw [tas_go_won hc, hc]
    | adopted v => rw [tas_go_adopted hc, hc]
  · rw [Protocol.go_loc_of_ne same]

theorem tas_rank_go_lt (C : (tasProtocol token prop).Config) (i : Fin 2)
    (undecided : (tasProtocol token prop).decision C i = none) :
    tasRank (((tasProtocol token prop).go C i).loc i) < tasRank (C.loc i) := by
  cases hc : C.loc i with
  | start v => rw [tas_go_start hc]; simp [tasRank]
  | raced v =>
      by_cases present : token ∈ C.obj
      · rw [tas_go_raced_win hc present]; simp [tasRank]
      · rw [tas_go_raced_lose hc present]; simp [tasRank]
  | lost v => rw [tas_go_lost hc]; simp [tasRank]
  | won v =>
      have : (tasProtocol token prop).decision C i = some v := by
        unfold Protocol.decision; rw [hc]
      rw [this] at undecided; cases undecided
  | adopted v =>
      have : (tasProtocol token prop).decision C i = some v := by
        unfold Protocol.decision; rw [hc]
      rw [this] at undecided; cases undecided

include prop_inj token_ne in
/-- **Two processes reach consensus over a space whose removals report success.** -/
theorem tas_solves : (tasProtocol token prop).Solves := by
  refine ⟨?_, ?_, ?_⟩
  · intro x C reach i j v w hv hw
    obtain ⟨p, q, allowed, h0, h1, -⟩ := tas_inv_of_reach prop_inj token_ne reach
    have hv := Protocol.decision_eq_some_iff.mp hv
    have hw := Protocol.decision_eq_some_iff.mp hw
    obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    all_goals obtain rfl | rfl : j = 0 ∨ j = 1 := by fin_cases j <;> simp
    all_goals first
      | (rw [h0] at hv) | (rw [h1] at hv)
    all_goals first
      | (rw [h0] at hw) | (rw [h1] at hw)
    all_goals
      rcases tas_decided hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        rcases tas_decided hw with ⟨hq, rfl⟩ | ⟨hq, rfl⟩ <;> simp_all [Allowed]
  · intro x C reach i v hv
    have hv := Protocol.decision_eq_some_iff.mp hv
    obtain ⟨p, q, -, h0, h1, -⟩ := tas_inv_of_reach prop_inj token_ne reach
    obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    · rw [h0] at hv
      rcases tas_decided hv with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact ⟨0, rfl⟩
      · exact ⟨_, rfl⟩
    · rw [h1] at hv
      rcases tas_decided hv with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨_, rfl⟩
  · refine Protocol.waitFree_of_measure (fun i C => tasRank (C.loc i)) ?_ ?_
    · intro x C i j D _ step
      rw [Protocol.step_iff_go.mp step]
      exact tas_rank_go_le C i j
    · intro x C i D _ step undecided
      rw [Protocol.step_iff_go.mp step]
      exact tas_rank_go_lt C i undecided

include prop_inj token_ne in
theorem separateSpace_solvable_two : Solvable (separateSpace A).toObject 2 V :=
  ⟨_, tas_solves prop_inj token_ne⟩

end TestAndSet

/-- **A space whose removals report success has consensus number two**, when it has five
distinct atoms (any infinite atom type does). -/
theorem separateSpace_hasConsensusNumber_two [Infinite A] :
    HasConsensusNumber (separateSpace A).toObject 2 := by
  let e : Option (Fin 2 × Bool) → A := fun o => Infinite.natEmbedding A (Encodable.encode o)
  have inj : Function.Injective e :=
    (Infinite.natEmbedding A).injective.comp Encodable.encode_injective
  refine hasConsensusNumber_two (T := separateSpace A) 0 separateSpace_bystander ?_
  refine separateSpace_solvable_two (token := e none) (prop := fun i v => e (some (i, v)))
    (fun i v j w h => ?_) (fun i v h => ?_)
  · have := Option.some.inj (inj h)
    exact ⟨(Prod.ext_iff.mp this).1, (Prod.ext_iff.mp this).2⟩
  · exact absurd (inj h) (by simp)


namespace Controls

/-- **Positive and negative control**: two removals of the one `token` hide their order from a
bystander (both orders leave the empty bag) and from neither remover (the first answers
`removed true`, the second `removed false`). -/
theorem remove_remove_bystander_only (token : A) :
    BystanderCannotOrder (separateSpace A) {token} (.remove token) (.remove token) ∧
      ¬ PairCannotOrder (separateSpace A) {token} (.remove token) (.remove token) := by
  refine ⟨Or.inr rfl, ?_⟩
  have seen : ¬ OrderHidden (separateSpace A) {token} (.remove token) (.remove token) := by
    rintro (h | h | ⟨-, h⟩) <;> simp [spaceNext, spaceReply] at h
  exact fun h => h.elim seen seen

/-- **Positive control**: with silent removal the same two removals are hidden from the first
remover: both orders leave the empty bag and it hears `ack` either way. -/
theorem silent_remove_remove_hidden (token : A) :
    OrderHidden (silentSpace A) {token} (.remove token) (.remove token) :=
  .commutes rfl rfl

/-- **Positive control**: the test-and-set race decides for two processes with inputs `false` and
`true` over the atoms `0` (the token) and `1 + 2i + v` (the proposals). -/
theorem tas_race_solves :
    (tasProtocol (A := ℕ) 0 fun i (v : Bool) => 1 + 2 * i.val + v.toNat).Solves := by
  refine tas_solves (fun i v j w h => ?_) (fun i v h => by omega)
  have hv := v.toNat_le
  have hw := w.toNat_le
  have hij : i.val = j.val := by omega
  refine ⟨Fin.ext hij, ?_⟩
  cases v <;> cases w <;> simp_all

end Controls

end Mettapedia.GSLT.Coordination.ConsensusNumbers
