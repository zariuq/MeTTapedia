import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.CertifiedSpines

/-!
# In PeTTa a typed fold costs at least the best untyped fold

A fold over lists, `(= (f Nil) base)` and `(= (f (Cons $x $xs)) (step $x (f $xs)))`,
reads each cell: it tells `Nil` from a cell, tests that a cell is a `Cons` with
two fields, tests the element's class and steps. A declaration
`(: f (-> (List τ) R))` could only make it cheaper by letting it drop the cell
test. This module states when PeTTa's types allow that and proves that,
measured as PeTTa runs it, the typed fold never costs less than the best fold
of its untyped twin: the same equations without the declarations, which have
the same answers on every argument the typed call accepts.

**Dropping the cell test is sound exactly on spines.** The pass without it
(`foldTrusted`) answers on every value; the equations (`foldEq`) answer exactly
on spines of `Cons` cells ending in `Nil`, and there the two agree
(`trusted_agrees_iff`). So a certificate licenses the pass exactly when every
value it certifies is a spine (`Licensed`).

**PeTTa's typing licenses it only at a closed sort.** Under `ListClosed` every
ground value typed once at `(List τ)` is a spine (`licensed_of_closed`, from
`CertifiedSpines.spine_of_count`). Any other symbol whose row is a constructor
declaration with range `(List τ)` at some instance, applied to ground arguments
typed once at its fields, is a ground value typed once at `(List τ)` and no
spine, on which the pass without the test answers and the equations answer
nothing (`not_licensed_of_open`, `trusted_wrong_of_open`). A typed producer of
lists is such a symbol: PeTTa types an unevaluated application by its head's
row, so `(: build (-> Number (List Number) (List Number)))` opens the sort
(`typed_producer_opens`, `Controls.held_build_certified`), and a typed fold
over a typed producer's lists keeps its cell test (the measured `list_T`).

**Evidence** (`TypedEvidence`): a run knows its argument's typing at `(List τ)`
by a check that inspects the value (the guard, `eval_petta_value_typed_once`),
by `Nil`, or by a cell it built from an element typed once at `τ` and a tail it
knows. A typed producer's declared range is none of these by itself: PeTTa
enforces it by the producer's result guard, a check, or the producer's version
proves it by construction, so what the consumer reads is evidence of one of the
three kinds, established inside the producer. Under the licence, each piece of
typed evidence is evidence of the spine at the same cost (`TypedEvidence.toShape`),
which a run without declarations can hold (`ShapeEvidence`): the check walks the
same value, the builds are the same builds.

**The bound** (`typed_fold_ge_untyped`, T8 for PeTTa): a typed run that pays
`guards` for its checks, holds typed evidence of cost `k` and drops the cell
test only where the declarations license it costs at least a sound run of the
untyped twin: the same evidence read as shape evidence with the same pass, or the
tested pass with none. A check made only to drop the test never pays, since a
check of the typing reads each cell's head and arity (`walk_never_pays`; every
value typable at the closed sort is a spine, `CertifiedSpines.spine_of_typable`,
so changing any one cell's head or arity makes it untypable). And a tested pass
that answers has found a spine (`tested_pass_certifies`), so an untyped run that
keeps that fact holds, for every later fold of the value, the certificate a
typed check would have given.

**The element test stays.** PeTTa's library declares `(: + (-> Number Number
Number))`, so `(+ 1 2)` held as data is typed once at `Number` and is no number
(`Controls.number_not_closed`): `Number` is never closed, and a fold's machine
integer test remains with or without declarations.

**What would give types a representation guarantee** (`termRows`,
`sealed_closed`, `sealed_licensed`): a sort is sealed when its type is offered as
the type of a term only by its constructors, and a function's row is read as a
contract on its call's answers, never as the type of an unevaluated application
of it. Under that reading the list sort of `list_T` is closed though `build` is
typed (`Controls.sealed_listT`), every ground value typed once at `(List Number)`
is a spine, and the held `(build 1 Nil)` is not typed there
(`Controls.sealed_rejects_held_build`).

**Measured** (opt binary, pinned placement key, instructions per element at
2000/4000/8000): `(sum (build n Nil))` 655.8 untyped and 655.8 to 656.0 typed;
`(toint (add (fromint n) (fromint n)))` 1688.8 untyped and 1688.5 typed. The
typed programs tie, each with a constant cost for its declarations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypedFoldBound

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open TypedCalls.Controls (listOf consRow cons_constructor)
open CertifiedSpines

/-! ## The fold, with and without the cell test -/

section Passes

variable {β : Type} (base : β) (stepF : Atom → β → β)

/-- **The equations of a fold**: `Nil` answers the base, a `Cons` cell the step
over its tail's answer; any other value matches no equation and answers nothing. -/
def foldEq : Atom → Option β
  | .symbol s => if s = "Nil" then some base else none
  | .expression [.symbol c, x, r] => if c = "Cons" then (foldEq r).map (stepF x) else none
  | _ => none

/-- **The pass without the cell test**: a value with at least three elements is
read as a cell, its second element the element and its third the tail; anything
else ends the spine. It answers on every value. -/
def foldTrusted : Atom → β
  | .expression (_ :: x :: r :: _) => stepF x (foldTrusted r)
  | _ => base

variable {base stepF}

theorem foldEq_spine {P : Atom → Prop} : ∀ {v : Atom}, ConsSpine P v →
    foldEq base stepF v = some (foldTrusted base stepF v)
  | _, .nil => by simp [foldEq, foldTrusted]
  | _, .cons x r _ hr => by
      simp only [foldEq, if_true, foldTrusted]
      rw [foldEq_spine hr]
      rfl

theorem spine_of_foldEq : ∀ {v : Atom} {b : β}, foldEq base stepF v = some b →
    ConsSpine (fun _ => True) v
  | .symbol s, b, h => by
      simp only [foldEq] at h
      split_ifs at h with hs
      subst hs
      exact .nil
  | .expression [.symbol c, x, r], b, h => by
      simp only [foldEq] at h
      split_ifs at h with hc
      subst hc
      obtain ⟨b', hb', -⟩ := Option.map_eq_some_iff.mp h
      exact .cons x r trivial (spine_of_foldEq hb')
  | .var _, b, h => by simp [foldEq] at h
  | .grounded _, b, h => by simp [foldEq] at h
  | .expression [], b, h => by simp [foldEq] at h
  | .expression [_], b, h => by simp [foldEq] at h
  | .expression [_, _], b, h => by simp [foldEq] at h
  | .expression (_ :: _ :: _ :: _ :: _), b, h => by simp [foldEq] at h
  | .expression [.var _, _, _], b, h => by simp [foldEq] at h
  | .expression [.grounded _, _, _], b, h => by simp [foldEq] at h
  | .expression [.expression _, _, _], b, h => by simp [foldEq] at h

/-- **The equations answer exactly on spines.** -/
theorem foldEq_isSome_iff (v : Atom) :
    (foldEq base stepF v).isSome ↔ ConsSpine (fun _ => True) v := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp h
    exact spine_of_foldEq hb
  · intro h
    rw [foldEq_spine h]
    rfl

/-- **The pass without the cell test answers as the equations exactly on
spines**: a certificate licenses it exactly when what it certifies is a spine. -/
theorem trusted_agrees_iff (v : Atom) :
    foldEq base stepF v = some (foldTrusted base stepF v) ↔ ConsSpine (fun _ => True) v :=
  ⟨fun h => spine_of_foldEq h, fun h => foldEq_spine h⟩

/-- **A tested pass that answers has found a spine**: a run that keeps the fact
holds the certificate for every later fold of the value. -/
theorem tested_pass_certifies {v : Atom} {b : β} (h : foldEq base stepF v = some b) :
    ConsSpine (fun _ => True) v ∧ b = foldTrusted base stepF v := by
  have hs := spine_of_foldEq h
  refine ⟨hs, ?_⟩
  rw [foldEq_spine hs] at h
  exact (Option.some.inj h).symm

end Passes

theorem spine_true {P : Atom → Prop} : ∀ {v : Atom}, ConsSpine P v → ConsSpine (fun _ => True) v
  | _, .nil => .nil
  | _, .cons x r _ hr => .cons x r trivial (spine_true hr)

/-! ## When typing licenses the pass without the cell test -/

section Licence

variable {Γ : Decls} {τ : Ty Empty}

/-- **The declarations license the pass without the cell test at `(List τ)`**:
every ground value typed once there is a spine. -/
def Licensed (Γ : Decls) (τ : Ty Empty) : Prop :=
  ∀ v : Atom, Ground v → count (info Γ v) (listOf τ) = 1 → ConsSpine (fun _ => True) v

/-- **A closed sort licenses it.** -/
theorem licensed_of_closed (hΓ : ListClosed Γ) : Licensed Γ τ := fun v hg one =>
  spine_true (spine_of_count hΓ τ v hg one)

/-- **An open sort certifies a value that is no spine**: a symbol other than `Nil`
and `Cons` whose one row is a constructor declaration with range `(List τ)` at an
instance, applied to ground arguments typed once at its checked fields, is
ground, typed once at `(List τ)`, and no spine. -/
theorem open_nonspine (hF : Functional Γ) {g : String} (hCons : g ≠ "Cons")
    {As : List (Ty String)} {R : Ty String} (row : Γ g = [arrow As R]) (hC : Constructor As R)
    (σ : String → Ty Empty) (hR : R.bind σ = listOf τ) (ws : List Atom) (len : ws.length = As.length)
    (fields : ∀ p ∈ List.zip As ws, ¬ FreeField R p.1 → count (info Γ p.2) (p.1.bind σ) = 1)
    (hg : GroundAll ws) :
    count (info Γ (.expression (.symbol g :: ws))) (listOf τ) = 1 ∧
      Ground (.expression (.symbol g :: ws)) ∧ ¬ ConsSpine (fun _ => True) (.expression (.symbol g :: ws)) := by
  refine ⟨hR ▸ ctor_construction hF row hC ws len σ fields, ⟨trivial, hg⟩, fun h => ?_⟩
  rcases h.head with same | ⟨x, r, same⟩
  · cases same
  · simp only [Atom.expression.injEq, List.cons.injEq, Atom.symbol.injEq] at same
    exact hCons same.1

/-- **An open sort does not license the pass.** -/
theorem not_licensed_of_open (hF : Functional Γ) {g : String} (hCons : g ≠ "Cons")
    {As : List (Ty String)} {R : Ty String} (row : Γ g = [arrow As R]) (hC : Constructor As R)
    (σ : String → Ty Empty) (hR : R.bind σ = listOf τ) (ws : List Atom) (len : ws.length = As.length)
    (fields : ∀ p ∈ List.zip As ws, ¬ FreeField R p.1 → count (info Γ p.2) (p.1.bind σ) = 1)
    (hg : GroundAll ws) : ¬ Licensed Γ τ := fun lic => by
  obtain ⟨one, ground, nonspine⟩ := open_nonspine hF hCons row hC σ hR ws len fields hg
  exact nonspine (lic _ ground one)

/-- **There the pass without the cell test answers where the equations answer
nothing.** -/
theorem trusted_wrong_of_open {β : Type} (base : β) (stepF : Atom → β → β) (hF : Functional Γ)
    {g : String} (hCons : g ≠ "Cons")
    {As : List (Ty String)} {R : Ty String} (row : Γ g = [arrow As R]) (hC : Constructor As R)
    (σ : String → Ty Empty) (hR : R.bind σ = listOf τ) (ws : List Atom) (len : ws.length = As.length)
    (fields : ∀ p ∈ List.zip As ws, ¬ FreeField R p.1 → count (info Γ p.2) (p.1.bind σ) = 1)
    (hg : GroundAll ws) :
    foldEq base stepF (.expression (.symbol g :: ws)) = none ∧
      foldEq base stepF (.expression (.symbol g :: ws)) ≠
        some (foldTrusted base stepF (.expression (.symbol g :: ws))) := by
  obtain ⟨-, -, nonspine⟩ := open_nonspine hF hCons row hC σ hR ws len fields hg
  have none' : foldEq base stepF (.expression (.symbol g :: ws)) = none := by
    cases h : foldEq base stepF (.expression (.symbol g :: ws)) with
    | none => rfl
    | some b => exact absurd (spine_of_foldEq h) nonspine
  exact ⟨none', by rw [none']; simp⟩

/-- **A typed producer of lists opens the sort**: PeTTa types an unevaluated
application by its head's row, so a row of another symbol whose range is a list
type breaks the closure. -/
theorem typed_producer_opens {g : String} (hNil : g ≠ "Nil") (hCons : g ≠ "Cons")
    {As : List (Ty String)} {T : Ty String} (row : arrow As (listOf T) ∈ Γ g) : ¬ ListClosed Γ :=
  fun hΓ => by
    have := hΓ.other g hNil hCons _ row
    simp [offered, AwayFromList, listOf] at this

end Licence

/-! ## Evidence -/

section Evidence

variable {Γ : Decls} {τ : Ty Empty} {walk : Atom → ℕ} {build : ℕ}

variable (Γ τ walk build) in
/-- **How a typed run comes to know its argument's typing at `(List τ)`**, with
what it costs at run time: a check that inspects the value (the guard), `Nil`,
or a cell built from an element typed once at `τ` and a tail it knows, at
`build` per cell. -/
inductive TypedEvidence : Atom → ℕ → Prop
  | walk (v : Atom) : count (info Γ v) (listOf τ) = 1 → TypedEvidence v (walk v)
  | nil : TypedEvidence (.symbol "Nil") 0
  | cons (x r : Atom) (k : ℕ) : count (info Γ x) τ = 1 → TypedEvidence r k →
      TypedEvidence (.expression [.symbol "Cons", x, r]) (k + build)

variable (walk build) in
/-- **How an untyped run comes to know its argument is a spine**, at the same
costs: a check, `Nil`, or a cell built over a tail it knows. -/
inductive ShapeEvidence : Atom → ℕ → Prop
  | walk (v : Atom) : ConsSpine (fun _ => True) v → ShapeEvidence v (walk v)
  | nil : ShapeEvidence (.symbol "Nil") 0
  | cons (x r : Atom) (k : ℕ) : ShapeEvidence r k → ShapeEvidence (.expression [.symbol "Cons", x, r]) (k + build)

/-- Shape evidence is a spine. -/
theorem ShapeEvidence.spine : ∀ {v : Atom} {k : ℕ}, ShapeEvidence walk build v k → ConsSpine (fun _ => True) v
  | _, _, .walk _ h => h
  | _, _, .nil => .nil
  | _, _, .cons x r _ h => .cons x r trivial h.spine

/-- **Typed evidence is true** under functional declarations with the usual `Nil`
and `Cons` rows. -/
theorem TypedEvidence.typed (hF : Functional Γ) (hNil : Γ "Nil" = [listOf (.var "a")])
    (hCons : Γ "Cons" = [consRow]) :
    ∀ {v : Atom} {k : ℕ}, TypedEvidence Γ τ walk build v k → count (info Γ v) (listOf τ) = 1
  | _, _, .walk _ h => h
  | _, _, .nil => CertifiedSpines.Controls.count_nil_of hF hNil τ
  | _, _, .cons x r _ hx hr => by
      have tail := hr.typed hF hNil hCons
      have := ctor_construction hF hCons cons_constructor [x, r] rfl (fun _ => τ) (by
        intro p hp _
        simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
          or_false] at hp
        rcases hp with rfl | rfl
        · simpa using hx
        · simpa [listOf] using tail)
      simpa [listOf] using this

/-- **Under the licence, typed evidence is shape evidence at the same cost.** -/
theorem TypedEvidence.toShape (lic : Licensed Γ τ) {v : Atom} {k : ℕ} (hg : Ground v)
    (ev : TypedEvidence Γ τ walk build v k) : ShapeEvidence walk build v k := by
  induction ev with
  | walk v h => exact .walk v (lic v hg h)
  | nil => exact .nil
  | cons x r k _ _ ih => exact .cons x r k (ih (ground_cons_parts hg).2)

/-- **The untyped run is sound**: on shape evidence, the pass without the cell test
answers as the equations. -/
theorem shape_run_sound {β : Type} (base : β) (stepF : Atom → β → β) {v : Atom} {k : ℕ}
    (ev : ShapeEvidence walk build v k) : foldEq base stepF v = some (foldTrusted base stepF v) :=
  foldEq_spine ev.spine

/-- **The typed run is sound where the declarations license it**: on a ground value
typed once at `(List τ)`, the pass without the cell test answers as the equations. -/
theorem licensed_run_sound {β : Type} (base : β) (stepF : Atom → β → β) (lic : Licensed Γ τ)
    {v : Atom} (hg : Ground v) (one : count (info Γ v) (listOf τ) = 1) :
    foldEq base stepF v = some (foldTrusted base stepF v) :=
  foldEq_spine (lic v hg one)

end Evidence

/-! ## The bound -/

/-- The costs of a fold pass per cell: reading the cell's head to tell `Nil` from a
cell (every pass pays it: it is how a pass finds the end), the rest of the cell
test (a `Cons` with two fields), the element's class test, and the step. -/
structure PassCosts where
  head : ℕ
  cellTest : ℕ
  elemTest : ℕ
  step : ℕ

/-- The pass with the cell test over `n` cells and the end. -/
def testedPass (c : PassCosts) (n : ℕ) : ℕ := n * (c.head + c.cellTest + c.elemTest + c.step) + c.head

/-- The pass without it. -/
def trustedPass (c : PassCosts) (n : ℕ) : ℕ := n * (c.head + c.elemTest + c.step) + c.head

/-- The pass a run makes. -/
def pass (c : PassCosts) (n : ℕ) (trusted : Bool) : ℕ := if trusted then trustedPass c n else testedPass c n

theorem trustedPass_le (c : PassCosts) (n : ℕ) : trustedPass c n ≤ testedPass c n := by
  unfold trustedPass testedPass
  have : n * (c.head + c.elemTest + c.step) ≤ n * (c.head + c.cellTest + c.elemTest + c.step) :=
    Nat.mul_le_mul_left n (by omega)
  omega

/-- **T8 for PeTTa: a typed fold costs at least the best untyped fold.** A typed
run of a fold at `(List τ)` on a ground argument of `n` cells pays `guards` for
the checks it does not discharge, holds typed evidence of cost `k`, and drops the
cell test only where the declarations license it. The untyped twin then has a
sound run, dropping the test only on shape evidence, that costs no more: the same
evidence as shape evidence with the same pass, or the tested pass with none. -/
theorem typed_fold_ge_untyped {Γ : Decls} {τ : Ty Empty} {walk : Atom → ℕ} {build : ℕ}
    (c : PassCosts) (n guards k : ℕ) {v : Atom} (hg : Ground v)
    (ev : TypedEvidence Γ τ walk build v k) (trusted : Bool) (sound : trusted = true → Licensed Γ τ) :
    ∃ (k' : ℕ) (trusted' : Bool), (trusted' = true → ShapeEvidence walk build v k') ∧
      k' + pass c n trusted' ≤ guards + k + pass c n trusted := by
  cases trusted with
  | true => exact ⟨k, true, (fun _ => ev.toShape (sound rfl) hg), by omega⟩
  | false => exact ⟨0, false, (fun h => by cases h), by simp [pass]⟩

/-- **A check made to drop the cell test never pays**: a check of the typing reads
each cell's head and arity, at least the cell test per cell, so checking and then
running without the test costs at least the tested pass. -/
theorem walk_never_pays (c : PassCosts) (n w : ℕ) (reads : n * c.cellTest ≤ w) :
    testedPass c n ≤ w + trustedPass c n := by
  unfold testedPass trustedPass
  have : n * (c.head + c.cellTest + c.elemTest + c.step) =
      n * (c.head + c.elemTest + c.step) + n * c.cellTest := by ring
  omega

/-- **Every value typable at the closed sort is a spine**, so changing one cell's
head to another symbol, or its arity, anywhere along a typed value makes it
untypable: a check reads every cell. -/
theorem typable_nonspine {Γ : Decls} (hΓ : ListClosed Γ) (τ : Ty Empty) {v : Atom} (hg : Ground v)
    (hns : ¬ ConsSpine (fun x => Typable Γ x τ) v) : ¬ Typable Γ v (listOf τ) :=
  fun ht => hns (spine_of_typable hΓ τ v hg ht)

/-! ## The Peano sort -/

section Peano

variable {β : Type} (base : β) (stepF : β → β)

/-- **The equations of a fold over naturals**: `Z` answers the base, `(S n)` the step
over `n`'s answer; any other value answers nothing. -/
def natEq : Atom → Option β
  | .symbol s => if s = "Z" then some base else none
  | .expression [.symbol c, n] => if c = "S" then (natEq n).map stepF else none
  | _ => none

/-- **The pass without the cell test**: a value with at least two elements is read as
a successor of its second element; anything else ends the spine. -/
def natTrusted : Atom → β
  | .expression (_ :: n :: _) => stepF (natTrusted n)
  | _ => base

variable {base stepF}

theorem natEq_spine : ∀ {v : Atom}, NatSpine v → natEq base stepF v = some (natTrusted base stepF v)
  | _, .zero => by simp [natEq, natTrusted]
  | _, .succ n hn => by
      simp only [natEq, if_true, natTrusted]
      rw [natEq_spine hn]
      rfl

theorem spine_of_natEq : ∀ {v : Atom} {b : β}, natEq base stepF v = some b → NatSpine v
  | .symbol s, b, h => by
      simp only [natEq] at h
      split_ifs at h with hs
      subst hs
      exact .zero
  | .expression [.symbol c, n], b, h => by
      simp only [natEq] at h
      split_ifs at h with hc
      subst hc
      obtain ⟨b', hb', -⟩ := Option.map_eq_some_iff.mp h
      exact .succ n (spine_of_natEq hb')
  | .var _, b, h => by simp [natEq] at h
  | .grounded _, b, h => by simp [natEq] at h
  | .expression [], b, h => by simp [natEq] at h
  | .expression [_], b, h => by simp [natEq] at h
  | .expression (_ :: _ :: _ :: _), b, h => by simp [natEq] at h
  | .expression [.var _, _], b, h => by simp [natEq] at h
  | .expression [.grounded _, _], b, h => by simp [natEq] at h
  | .expression [.expression _, _], b, h => by simp [natEq] at h

/-- **Over naturals too, the pass without the cell test answers as the equations
exactly on spines.** -/
theorem natTrusted_agrees_iff (v : Atom) :
    natEq base stepF v = some (natTrusted base stepF v) ↔ NatSpine v :=
  ⟨fun h => spine_of_natEq h, fun h => natEq_spine h⟩

end Peano

section PeanoLicence

variable {Γ : Decls}

/-- **The declarations license the pass without the cell test at `Nat`.** -/
def NatLicensed (Γ : Decls) : Prop :=
  ∀ v : Atom, Ground v → count (info Γ v) (.sym "Nat") = 1 → NatSpine v

theorem natLicensed_of_closed (hΓ : NatClosed Γ) : NatLicensed Γ := fun v hg one =>
  nat_spine_of_typable hΓ v hg ((typable_iff_count Γ v _).mpr (by omega))

/-- **An open Peano sort certifies a value that is no spine.** -/
theorem nat_open_nonspine (hF : Functional Γ) {g : String} (hS : g ≠ "S")
    {As : List (Ty String)} {R : Ty String} (row : Γ g = [arrow As R]) (hC : Constructor As R)
    (σ : String → Ty Empty) (hR : R.bind σ = .sym "Nat") (ws : List Atom) (len : ws.length = As.length)
    (fields : ∀ p ∈ List.zip As ws, ¬ FreeField R p.1 → count (info Γ p.2) (p.1.bind σ) = 1)
    (hg : GroundAll ws) :
    count (info Γ (.expression (.symbol g :: ws))) (.sym "Nat") = 1 ∧
      Ground (.expression (.symbol g :: ws)) ∧ ¬ NatSpine (.expression (.symbol g :: ws)) := by
  refine ⟨hR ▸ ctor_construction hF row hC ws len σ fields, ⟨trivial, hg⟩, fun h => ?_⟩
  rcases h.head with same | ⟨n, same⟩
  · cases same
  · simp only [Atom.expression.injEq, List.cons.injEq, Atom.symbol.injEq] at same
    exact hS same.1

theorem not_natLicensed_of_open (hF : Functional Γ) {g : String} (hS : g ≠ "S")
    {As : List (Ty String)} {R : Ty String} (row : Γ g = [arrow As R]) (hC : Constructor As R)
    (σ : String → Ty Empty) (hR : R.bind σ = .sym "Nat") (ws : List Atom) (len : ws.length = As.length)
    (fields : ∀ p ∈ List.zip As ws, ¬ FreeField R p.1 → count (info Γ p.2) (p.1.bind σ) = 1)
    (hg : GroundAll ws) : ¬ NatLicensed Γ := fun lic => by
  obtain ⟨one, ground, nonspine⟩ := nat_open_nonspine hF hS row hC σ hR ws len fields hg
  exact nonspine (lic _ ground one)

/-- **A typed producer of naturals opens the Peano sort.** -/
theorem typed_producer_opens_nat {g : String} (hZ : g ≠ "Z") (hS : g ≠ "S")
    {As : List (Ty String)} (row : arrow As (.sym "Nat") ∈ Γ g) : ¬ NatClosed Γ :=
  fun hΓ => by
    have := hΓ.other g hZ hS _ row
    simp [offered, AwayFromNat] at this

variable {walk : Atom → ℕ} {build : ℕ}

variable (Γ walk build) in
/-- How a typed run knows its argument's typing at `Nat`: a check, `Z`, or a
successor it built over a value it knows. -/
inductive NatTypedEvidence : Atom → ℕ → Prop
  | walk (v : Atom) : count (info Γ v) (.sym "Nat") = 1 → NatTypedEvidence v (walk v)
  | zero : NatTypedEvidence (.symbol "Z") 0
  | succ (n : Atom) (k : ℕ) : NatTypedEvidence n k → NatTypedEvidence (.expression [.symbol "S", n]) (k + build)

variable (walk build) in
/-- How an untyped run knows its argument is a Peano spine, at the same costs. -/
inductive NatShapeEvidence : Atom → ℕ → Prop
  | walk (v : Atom) : NatSpine v → NatShapeEvidence v (walk v)
  | zero : NatShapeEvidence (.symbol "Z") 0
  | succ (n : Atom) (k : ℕ) : NatShapeEvidence n k → NatShapeEvidence (.expression [.symbol "S", n]) (k + build)

theorem NatShapeEvidence.spine : ∀ {v : Atom} {k : ℕ}, NatShapeEvidence walk build v k → NatSpine v
  | _, _, .walk _ h => h
  | _, _, .zero => .zero
  | _, _, .succ n _ h => .succ n h.spine

/-- **Under the licence, typed evidence at `Nat` is shape evidence at the same cost.** -/
theorem NatTypedEvidence.toShape (lic : NatLicensed Γ) {v : Atom} {k : ℕ} (hg : Ground v)
    (ev : NatTypedEvidence Γ walk build v k) : NatShapeEvidence walk build v k := by
  induction ev with
  | walk v h => exact .walk v (lic v hg h)
  | zero => exact .zero
  | succ n k _ ih => exact .succ n k (ih hg.2.1)

/-- **T8 for PeTTa over naturals**: a typed fold at `Nat` costs at least a sound run
of its untyped twin. -/
theorem typed_nat_fold_ge_untyped (c : PassCosts) (n guards k : ℕ) {v : Atom} (hg : Ground v)
    (ev : NatTypedEvidence Γ walk build v k) (trusted : Bool) (sound : trusted = true → NatLicensed Γ) :
    ∃ (k' : ℕ) (trusted' : Bool), (trusted' = true → NatShapeEvidence walk build v k') ∧
      k' + pass c n trusted' ≤ guards + k + pass c n trusted := by
  cases trusted with
  | true => exact ⟨k, true, (fun _ => ev.toShape (sound rfl) hg), by omega⟩
  | false => exact ⟨0, false, (fun h => by cases h), by simp [pass]⟩

end PeanoLicence

/-! ## What would give types a representation guarantee -/

section Sealed

variable (Γ : Decls) (funs : String → Prop) [DecidablePred funs]

/-- **Term typing under sealed sorts**: a function's row (a head with equations)
is read as a contract on its call's answers, not as the type of an unevaluated
application of it, so the term relation keeps the rows of the other symbols
only. -/
def termRows : Decls := fun s => if funs s then [] else Γ s

variable {Γ funs}

/-- **Under sealing, the list sort is closed** as soon as the constructors keep
their rows and no other symbol that is not a function offers a list type. -/
theorem sealed_closed (hNil : Γ "Nil" = [listOf (.var "a")]) (hCons : Γ "Cons" = [consRow])
    (fNil : ¬ funs "Nil") (fCons : ¬ funs "Cons")
    (others : ∀ s, ¬ funs s → s ≠ "Nil" → s ≠ "Cons" → ∀ ρ ∈ Γ s, AwayFromList (offered ρ)) :
    ListClosed (termRows Γ funs) where
  nil := by simp [termRows, fNil, hNil]
  cons := by simp [termRows, fCons, hCons]
  other := fun s h1 h2 ρ hρ => by
    by_cases hs : funs s
    · simp [termRows, hs] at hρ
    · simp only [termRows, hs, if_false] at hρ
      exact others s hs h1 h2 ρ hρ

/-- **A sealed sort carries its representation**: every ground value typed once at
`(List τ)` under the term relation is a spine. -/
theorem sealed_licensed (hNil : Γ "Nil" = [listOf (.var "a")]) (hCons : Γ "Cons" = [consRow])
    (fNil : ¬ funs "Nil") (fCons : ¬ funs "Cons")
    (others : ∀ s, ¬ funs s → s ≠ "Nil" → s ≠ "Cons" → ∀ ρ ∈ Γ s, AwayFromList (offered ρ))
    (τ : Ty Empty) : Licensed (termRows Γ funs) τ :=
  licensed_of_closed (sealed_closed hNil hCons fNil fCons others)

end Sealed

/-! ## Controls -/

namespace Controls

open TypedCalls.Controls (sym num app)
open CertifiedSpines.Controls (listNum count_int closed_constructor count_nil_of)

/-- `build`'s row, `(-> Number (List Number) (List Number))`. -/
abbrev buildRow : Ty String := arrow [.sym "Number", listOf (.sym "Number")] (listOf (.sym "Number"))

/-- `sum`'s row, `(-> (List Number) Number)`. -/
abbrev sumRow : Ty String := arrow [listOf (.sym "Number")] (.sym "Number")

/-- The library rows the probes read: `+` and `-` on numbers, `==` to a truth value. -/
abbrev numRow : Ty String := arrow [.sym "Number", .sym "Number"] (.sym "Number")
abbrev eqRow : Ty String := arrow [.sym "Number", .sym "Number"] (.sym "Bool")

/-- The declarations of `list_T`: the list constructors, `build`, `sum`, and the
library rows of `+`, `-` and `==`. -/
def listTDecls : Decls := fun s =>
  if s = "Nil" then [listOf (.var "a")] else if s = "Cons" then [consRow]
  else if s = "build" then [buildRow] else if s = "sum" then [sumRow]
  else if s = "+" then [numRow] else if s = "-" then [numRow] else if s = "==" then [eqRow]
  else []

/-- The declarations of `list_Tsum`: the same without `build`'s. -/
def listTsumDecls : Decls := fun s => if s = "build" then [] else listTDecls s

theorem listTDecls_functional : Functional listTDecls := by
  intro s
  unfold listTDecls
  split_ifs <;> simp

/-- `(build 1 Nil)`, held as data. -/
def heldBuild : Atom := app "build" [num 1, sym "Nil"]

/-- **A typed producer's held application is certified**: under `list_T`'s
declarations `(build 1 Nil)` is ground, typed once at `(List Number)` and no
spine, the signature is open, and the sort is not licensed. -/
theorem held_build_certified :
    count (info listTDecls heldBuild) listNum = 1 ∧ Ground heldBuild ∧
      ¬ ConsSpine (fun _ => True) heldBuild ∧ ¬ ListClosed listTDecls ∧
      ¬ Licensed listTDecls (.sym "Number") := by
  have hC : Constructor [.sym "Number", listOf (.sym "Number")] (listOf (.sym "Number")) :=
    closed_constructor _ _ (by simp [Named, listOf]) (by simp [listOf])
  have fields : ∀ p ∈ List.zip [.sym "Number", listOf (.sym "Number")] [num 1, sym "Nil"],
      ¬ FreeField (listOf (.sym "Number")) p.1 →
        count (info listTDecls p.2) (p.1.bind fun _ => .sym "Number") = 1 := by
    intro p hp _
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
      or_false] at hp
    rcases hp with rfl | rfl
    · exact count_int _ 1
    · simpa [listOf] using count_nil_of listTDecls_functional (by simp [listTDecls]) (.sym "Number")
  obtain ⟨one, ground, nonspine⟩ := open_nonspine (τ := .sym "Number") listTDecls_functional
    (g := "build") (by decide) (by simp [listTDecls]) hC (fun _ => .sym "Number")
    (by simp [listOf]) [num 1, sym "Nil"] rfl fields (by simp [GroundAll, Ground])
  refine ⟨one, ground, nonspine, ?_, ?_⟩
  · exact typed_producer_opens (g := "build") (As := [.sym "Number", listOf (.sym "Number")])
      (T := .sym "Number") (by decide) (by decide) (by simp [listTDecls, buildRow])
  · exact not_licensed_of_open listTDecls_functional (g := "build") (by decide)
      (by simp [listTDecls]) hC (fun _ => .sym "Number") (by simp [listOf]) [num 1, sym "Nil"] rfl
      fields (by simp [GroundAll, Ground])

/-- On it the pass without the cell test answers `1 + 0` where the equations of
`sum` answer nothing. -/
theorem held_build_trusted_wrong :
    foldEq (0 : ℤ) (fun x b => match x with | .grounded (.int z) => z + b | _ => b) heldBuild = none ∧
      foldTrusted (0 : ℤ) (fun x b => match x with | .grounded (.int z) => z + b | _ => b) heldBuild = 1 := by
  refine ⟨?_, rfl⟩
  simp [heldBuild, foldEq, app, sym]

/-- **`list_Tsum`'s signature is closed**: only `sum` is typed, and its row and the
library's offer numbers and truth values. -/
theorem listTsum_closed : ListClosed listTsumDecls where
  nil := by simp [listTsumDecls, listTDecls]
  cons := by simp [listTsumDecls, listTDecls]
  other := fun s h1 h2 ρ hρ => by
    unfold listTsumDecls listTDecls at hρ
    split_ifs at hρ <;> simp_all [offered, AwayFromList, sumRow, numRow, eqRow]

theorem listTsum_licensed : Licensed listTsumDecls (.sym "Number") := licensed_of_closed listTsum_closed

/-- **`Number` is never closed in PeTTa**: under the library row of `+`, `(+ 1 2)`
held as data is typed once at `Number` and is no number, so a fold keeps its
element test whatever is declared. -/
theorem number_not_closed :
    count (info listTDecls (app "+" [num 1, num 2])) (.sym "Number") = 1 ∧
      ∀ g, app "+" [num 1, num 2] ≠ .grounded g := by
  refine ⟨?_, fun g h => by cases h⟩
  have hC : Constructor [.sym "Number", .sym "Number"] (.sym "Number") :=
    closed_constructor _ _ (by simp [Named]) (by simp)
  have := ctor_construction listTDecls_functional (C := "+") (by simp [listTDecls]) hC
    [num 1, num 2] rfl (fun _ => .sym "Number") (by
      intro p hp _
      simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
        or_false] at hp
      rcases hp with rfl | rfl
      · exact count_int _ 1
      · exact count_int _ 2)
  simpa using this

/-- The functions of `list_T`: `build` and `sum`. -/
def listTFuns (s : String) : Prop := s = "build" ∨ s = "sum"

instance : DecidablePred listTFuns := fun s => by unfold listTFuns; infer_instance

/-- **Sealed, `list_T`'s sort is closed** though `build` is typed. -/
theorem sealed_listT : ListClosed (termRows listTDecls listTFuns) :=
  sealed_closed (by simp [listTDecls]) (by simp [listTDecls]) (by simp [listTFuns])
    (by simp [listTFuns]) fun s hs h1 h2 ρ hρ => by
      simp only [listTFuns, not_or] at hs
      unfold listTDecls at hρ
      split_ifs at hρ <;> simp_all [offered, AwayFromList, numRow, eqRow]

/-- **Sealed, the held `(build 1 Nil)` is not typed at `(List Number)`**: it is no
spine, and the sealed sort is licensed. -/
theorem sealed_rejects_held_build :
    count (info (termRows listTDecls listTFuns) heldBuild) listNum ≠ 1 := fun one =>
  held_build_certified.2.2.1
    (licensed_of_closed sealed_listT heldBuild held_build_certified.2.1 one)

/-- The declarations of `peano_T`: `Z`, `S`, the typed `fromint`, `add` and `toint`,
and the library rows. -/
def peanoTDecls : Decls := fun s =>
  if s = "Z" then [.sym "Nat"] else if s = "S" then [arrow [.sym "Nat"] (.sym "Nat")]
  else if s = "fromint" then [arrow [.sym "Number"] (.sym "Nat")]
  else if s = "add" then [arrow [.sym "Nat", .sym "Nat"] (.sym "Nat")]
  else if s = "toint" then [arrow [.sym "Nat"] (.sym "Number")]
  else if s = "+" then [numRow] else if s = "-" then [numRow] else if s = "==" then [eqRow]
  else []

/-- The declarations of `peano_Tctor`: the constructors and the library only. -/
def peanoTctorDecls : Decls := fun s =>
  if s = "fromint" ∨ s = "add" ∨ s = "toint" then [] else peanoTDecls s

theorem peanoTDecls_functional : Functional peanoTDecls := by
  intro s
  unfold peanoTDecls
  split_ifs <;> simp

/-- **`peano_T`'s typed `add` opens the sort**: `(add Z Z)` held as data is typed once
at `Nat` and is no Peano spine, so the typed `toint` keeps its cell test. -/
theorem held_add_certified :
    count (info peanoTDecls (app "add" [sym "Z", sym "Z"])) (.sym "Nat") = 1 ∧
      ¬ NatSpine (app "add" [sym "Z", sym "Z"]) ∧ ¬ NatClosed peanoTDecls ∧ ¬ NatLicensed peanoTDecls := by
  have hC : Constructor [.sym "Nat", .sym "Nat"] (.sym "Nat") :=
    closed_constructor _ _ (by simp [Named]) (by simp)
  have z : count (info peanoTDecls (sym "Z")) (.sym "Nat") = 1 := by
    rw [count_symbol_closed peanoTDecls "Z" (.sym "Nat") (by simp [peanoTDecls, Ty.lift])]
    simp
  have fields : ∀ p ∈ List.zip [.sym "Nat", .sym "Nat"] [sym "Z", sym "Z"],
      ¬ FreeField (.sym "Nat") p.1 → count (info peanoTDecls p.2) (p.1.bind fun _ => .sym "Nat") = 1 := by
    intro p hp _
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
      or_false] at hp
    rcases hp with rfl | rfl <;> simpa using z
  obtain ⟨one, -, nonspine⟩ := nat_open_nonspine peanoTDecls_functional (g := "add") (by decide)
    (by simp [peanoTDecls]) hC (fun _ => .sym "Nat") rfl [sym "Z", sym "Z"] rfl fields
    (by simp [GroundAll, Ground])
  refine ⟨one, nonspine, ?_, ?_⟩
  · exact typed_producer_opens_nat (g := "add") (As := [.sym "Nat", .sym "Nat"]) (by decide) (by decide)
      (by simp [peanoTDecls])
  · exact not_natLicensed_of_open peanoTDecls_functional (g := "add") (by decide)
      (by simp [peanoTDecls]) hC (fun _ => .sym "Nat") rfl [sym "Z", sym "Z"] rfl fields
      (by simp [GroundAll, Ground])

/-- **`peano_Tctor`'s signature is closed**: only the constructors are declared. -/
theorem peanoTctor_closed : NatClosed peanoTctorDecls where
  zero := by simp [peanoTctorDecls, peanoTDecls]
  succ := by simp [peanoTctorDecls, peanoTDecls]
  other := fun s h1 h2 ρ hρ => by
    unfold peanoTctorDecls peanoTDecls at hρ
    split_ifs at hρ <;> simp_all [offered, AwayFromNat, numRow, eqRow]

theorem peanoTctor_licensed : NatLicensed peanoTctorDecls := natLicensed_of_closed peanoTctor_closed

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypedFoldBound
