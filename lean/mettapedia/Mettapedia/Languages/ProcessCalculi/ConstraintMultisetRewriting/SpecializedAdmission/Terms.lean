import Mathlib.Data.List.Basic

/-!
# Terms of specialized admission

First-order terms with the kinds of the reference implementation's terms: an application of a
symbol to arguments, a structural code, a generative name, a frame variable, a local of a firing
(in a rule schema its parameters are its first locals), and the `j`-th name a firing mints.

* `inst σ φ` writes each local `k` as `σ k` and each fresh name `j` as `φ j`. A firing at a frame
  that has minted `b` names opens its fresh names at `fun j => name (b + j)`; a solution of its
  information assigns its locals.
* `atoms` lists the leaves of a term. `closed` says a term has no variable, local or fresh name:
  it is the same term at every solution. `minted b` says every name in it is below `b`.

The equality of terms is decided structurally (`beq_iff`), as hash-consing decides it in C.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SpecializedAdmission

/-- First-order terms. `app f args` applies the symbol `f`; a symbol has one arity in C, and every
test of an application here checks the number of arguments too. -/
inductive Tm where
  | app (f : Nat) (args : List Tm)
  | code (c : Int)
  | name (n : Nat)
  | var (i : Nat)
  | loc (i : Nat)
  | fresh (j : Nat)

namespace Tm

instance : Inhabited Tm := ⟨.code 0⟩

mutual
/-- Structural equality, as a Boolean. -/
def beq : Tm → Tm → Bool
  | .app f as, .app g bs => f == g && beqList as bs
  | .code a, .code b => a == b
  | .name a, .name b => a == b
  | .var a, .var b => a == b
  | .loc a, .loc b => a == b
  | .fresh a, .fresh b => a == b
  | _, _ => false
/-- Structural equality of lists of terms. -/
def beqList : List Tm → List Tm → Bool
  | [], [] => true
  | a :: as, b :: bs => beq a b && beqList as bs
  | _, _ => false
end

mutual
theorem beq_iff : ∀ a b : Tm, beq a b = true ↔ a = b
  | .app f as, b => by
      cases b with
      | app g bs =>
          have ih := beqList_iff as bs
          simp only [beq, Bool.and_eq_true, beq_iff_eq, ih, app.injEq]
      | _ => exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
  | .code c, b => by
      cases b with
      | code d => simp [beq]
      | _ => exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
  | .name n, b => by
      cases b with
      | name m => simp [beq]
      | _ => exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
  | .var i, b => by
      cases b with
      | var k => simp [beq]
      | _ => exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
  | .loc i, b => by
      cases b with
      | loc k => simp [beq]
      | _ => exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
  | .fresh j, b => by
      cases b with
      | fresh k => simp [beq]
      | _ => exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
theorem beqList_iff : ∀ as bs : List Tm, beqList as bs = true ↔ as = bs
  | [], [] => by simp [beqList]
  | [], _ :: _ => ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
  | _ :: _, [] => ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
  | a :: as, b :: bs => by
      have h1 := beq_iff a b
      have h2 := beqList_iff as bs
      simp only [beqList, Bool.and_eq_true, h1, h2, List.cons.injEq]
end

instance : DecidableEq Tm := fun a b => decidable_of_iff (beq a b = true) (beq_iff a b)

mutual
/-- Each local `k` written as `σ k`, each fresh name `j` as `φ j`. -/
def inst (σ φ : Nat → Tm) : Tm → Tm
  | .app f args => .app f (instList σ φ args)
  | .code c => .code c
  | .name n => .name n
  | .var i => .var i
  | .loc k => σ k
  | .fresh j => φ j
/-- `inst` on each term of a list. -/
def instList (σ φ : Nat → Tm) : List Tm → List Tm
  | [] => []
  | t :: ts => inst σ φ t :: instList σ φ ts
end

mutual
/-- The leaves of a term, in order. -/
def atoms : Tm → List Tm
  | .app _ args => atomsList args
  | .code c => [.code c]
  | .name n => [.name n]
  | .var i => [.var i]
  | .loc k => [.loc k]
  | .fresh j => [.fresh j]
/-- The leaves of a list of terms, in order. -/
def atomsList : List Tm → List Tm
  | [] => []
  | t :: ts => atoms t ++ atomsList ts
end

theorem instList_eq_map (σ φ : Nat → Tm) : ∀ ts : List Tm, instList σ φ ts = ts.map (inst σ φ)
  | [] => rfl
  | t :: ts => by simp only [instList, List.map_cons, instList_eq_map σ φ ts]

theorem atomsList_eq_flatMap : ∀ ts : List Tm, atomsList ts = ts.flatMap atoms
  | [] => rfl
  | t :: ts => by simp only [atomsList, List.flatMap_cons, atomsList_eq_flatMap ts]

mutual
theorem inst_congr {σ τ φ ψ : Nat → Tm} : ∀ t : Tm,
    (∀ k, loc k ∈ t.atoms → σ k = τ k) → (∀ j, fresh j ∈ t.atoms → φ j = ψ j) →
    t.inst σ φ = t.inst τ ψ
  | .app f args, h1, h2 => by
      simp only [atoms] at h1 h2
      have e := instList_congr args h1 h2
      simp only [inst, e]
  | .code _, _, _ => rfl
  | .name _, _, _ => rfl
  | .var _, _, _ => rfl
  | .loc k, h1, _ => h1 k (by simp only [atoms, List.mem_singleton])
  | .fresh j, _, h2 => h2 j (by simp only [atoms, List.mem_singleton])
theorem instList_congr {σ τ φ ψ : Nat → Tm} : ∀ ts : List Tm,
    (∀ k, loc k ∈ atomsList ts → σ k = τ k) → (∀ j, fresh j ∈ atomsList ts → φ j = ψ j) →
    instList σ φ ts = instList τ ψ ts
  | [], _, _ => rfl
  | t :: ts, h1, h2 => by
      simp only [atomsList, List.mem_append] at h1 h2
      have e1 := inst_congr t (fun k hk => h1 k (Or.inl hk)) (fun j hj => h2 j (Or.inl hj))
      have e2 := instList_congr ts (fun k hk => h1 k (Or.inr hk)) (fun j hj => h2 j (Or.inr hj))
      simp only [instList, e1, e2]
end

mutual
theorem inst_id : ∀ t : Tm, t.inst loc fresh = t
  | .app f args => by simp only [inst, instList_id args]
  | .code _ => rfl
  | .name _ => rfl
  | .var _ => rfl
  | .loc _ => rfl
  | .fresh _ => rfl
theorem instList_id : ∀ ts : List Tm, instList loc fresh ts = ts
  | [] => rfl
  | t :: ts => by simp only [instList, inst_id t, instList_id ts]
end

@[simp] theorem inst_app (σ φ : Nat → Tm) (f : Nat) (args : List Tm) :
    (app f args).inst σ φ = app f (args.map (inst σ φ)) := by
  simp only [inst, instList_eq_map]
@[simp] theorem inst_code (σ φ : Nat → Tm) (c : Int) : (code c).inst σ φ = code c := rfl
@[simp] theorem inst_name (σ φ : Nat → Tm) (n : Nat) : (name n).inst σ φ = name n := rfl
@[simp] theorem inst_var (σ φ : Nat → Tm) (i : Nat) : (var i).inst σ φ = var i := rfl
@[simp] theorem inst_loc (σ φ : Nat → Tm) (k : Nat) : (loc k).inst σ φ = σ k := rfl
@[simp] theorem inst_fresh (σ φ : Nat → Tm) (j : Nat) : (fresh j).inst σ φ = φ j := rfl

@[simp] theorem atoms_app (f : Nat) (args : List Tm) : (app f args).atoms = args.flatMap atoms := by
  simp only [atoms, atomsList_eq_flatMap]
@[simp] theorem atoms_code (c : Int) : (code c).atoms = [code c] := rfl
@[simp] theorem atoms_name (n : Nat) : (name n).atoms = [name n] := rfl
@[simp] theorem atoms_var (i : Nat) : (var i).atoms = [var i] := rfl
@[simp] theorem atoms_loc (k : Nat) : (loc k).atoms = [loc k] := rfl
@[simp] theorem atoms_fresh (j : Nat) : (fresh j).atoms = [fresh j] := rfl

/-- An atom that is a code or a name. -/
def rigidAtom : Tm → Bool
  | .code _ => true
  | .name _ => true
  | _ => false

/-- No variable, local or fresh name: the same term at every solution and at every frame that
has minted its names. -/
def closed (t : Tm) : Bool := t.atoms.all rigidAtom

/-- Every name in the term is below `b`. -/
def minted (b : Nat) (t : Tm) : Bool := t.atoms.all fun a => match a with
  | .name m => decide (m < b)
  | _ => true

theorem inst_closed {t : Tm} (h : t.closed = true) (σ φ : Nat → Tm) : t.inst σ φ = t := by
  have hall : ∀ a ∈ t.atoms, rigidAtom a = true := List.all_eq_true.mp h
  rw [inst_congr (τ := loc) (ψ := fresh) t
      (fun k hk => absurd (hall _ hk) (by simp [rigidAtom]))
      (fun j hj => absurd (hall _ hj) (by simp [rigidAtom])), inst_id]

theorem closed_app {f : Nat} {args : List Tm} :
    (app f args).closed = true ↔ ∀ a ∈ args, a.closed = true := by
  simp only [closed, atoms_app, List.all_eq_true, List.mem_flatMap]
  constructor
  · intro h a ha x hx
    exact h x ⟨a, ha, hx⟩
  · rintro h x ⟨a, ha, hx⟩
    exact h a ha x hx

/-! ### Controls -/

/-- Opening: the fresh name `1` of a firing at a frame with `10` names is the name `11`. -/
example : (app 3 [loc 0, fresh 1]).inst (fun _ => code 7) (fun j => name (10 + j)) =
    app 3 [code 7, name 11] := by decide
example : (app 3 [loc 0, fresh 1]).inst (fun _ => code 7) (fun j => name (10 + j)) ≠
    app 3 [code 7, name 12] := by decide
/-- A symbol applied to different numbers of arguments gives different terms. -/
example : app 1 [code 0] ≠ app 1 [code 0, code 0] := by decide
example : (app 2 [name 3, code 1]).closed = true := by decide
example : (app 2 [name 3, loc 0]).closed = false := by decide
example : (app 2 [name 3]).minted 4 = true := by decide
example : (app 2 [name 3]).minted 3 = false := by decide

#print axioms beq_iff
#print axioms inst_congr
#print axioms inst_closed

end Tm

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SpecializedAdmission
