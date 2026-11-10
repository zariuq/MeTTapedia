import Mathlib.Data.ZMod.Basic
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Independence

/-!
# Conserved charges of the candidate step

A **conserved charge** (`ConservedCharge`) is a potential on states, valued in a commutative
monoid, with a flux each firing takes and a flux it makes, such that every admitted firing balances:
the potential after it plus what it took is the potential before it plus what it made. The balance
is a field: a charge is data an instance supplies, or one of the charges derived below. Nothing here
derives a charge from a symmetry (for that direction see `ChargeNoether`).

* **Telescoping** (`run_balance`): along every run, the potential at the end plus everything taken
  is the potential at the start plus everything made. Totals along runs are functors out of the
  free category of runs (`Run.total_append`), being site accounts (`Run.ofAdd_total`).
* **Invariance** (`Invariant`): states of one class carry one potential. Invariance is a property
  of a charge relative to a transport; it is separate from the balance.
* **The fold filter** (`balanced_of_fold`, `not_fold_of_unbalanced`, `not_same_of_potential_ne`):
  a run that folds back to its start up to isomorphism takes exactly what it makes, in a
  cancellative monoid. A mismatch is therefore a sound rejection of a fold. A match is never a
  reason to fold (`ChargeFirstOrder`).
* **Incremental potentials** (`potential_result`, `potential_last`): in a group the potential of a
  result is the potential before it plus what the firing made minus what it took, so a search can
  carry the potential along without reading the state.
* **Trace invariance, two forms.** Net flux is a property of traces whenever the charge is
  invariant (`traceEquiv_net`). Each total separately is one when its flux is invariant under
  transport, alikeness and residuals (`traceEquiv_total`). Neither makes an arbitrary account a
  charge: equal accounts on equivalent runs say nothing about runs that are not equivalent.
* **Images** (`map`, `Invariant.map`, `not_same_of_map_ne`): a homomorphism carries a charge to a
  charge and keeps invariance, so a mismatch of images is still a sound rejection. In particular a
  charge in `ℤ` read in `ZMod (2 ^ 64)`, wrapping machine arithmetic, is a charge, and its filter is
  sound (`intCharge_wrap`); wrapping only loses rejections, never soundness. Finitely many charges
  form one charge in the product (`pi`), whose filter is the conjunction of theirs.
* **Occurrence weights** (`weightCharge`): for every step and every weight on occurrence
  identities, the total weight of the present occurrences is a conserved charge, whose fluxes are the
  weights of the taken and the made occurrences. It is invariant under every transport whose
  renamings keep the weight (`weightCharge_invariant`). With the weight `o ↦ {v o}` in multisets it is
  the multiset of the values `v` of the present occurrences (`weightCharge_singleton_potential`): label
  counts, and Murata's place invariants when the weight is a place vector.
* **Balanced firings** (`potential_last_of_balanced`): when every firing of a run takes what it
  makes, the potential is constant along it. For occurrence weights this is a place invariant.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled fire)

universe uO uT uH uOcc uS uF uA uB uK

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {State : Type uS} {Firing : State → Type uF}

/-! ## Totals along runs -/

namespace Step.Run

variable {P : Step X O State Firing} {A : Type uA} [AddCommMonoid A]

/-- **The total of a flux along a run.** -/
def total (flux : (t : State) → Firing t → A) : {s : State} → P.Run s → A
  | _, .nil _ => 0
  | _, .cons f _ rest => flux _ f + total flux rest

@[simp] theorem total_nil (flux : (t : State) → Firing t → A) (s : State) :
    total flux (.nil s : P.Run s) = 0 := rfl

@[simp] theorem total_cons (flux : (t : State) → Firing t → A) {s : State} (f : Firing s)
    (admitted : P.Admits f) (rest : P.Run (P.result f admitted)) :
    total flux (.cons f admitted rest) = flux s f + total flux rest := rfl

/-- A total is a site account, read additively. -/
theorem ofAdd_total (flux : (t : State) → Firing t → A) :
    ∀ {s : State} (r : P.Run s),
      Multiplicative.ofAdd (total flux r) = r.account fun t f => Multiplicative.ofAdd (flux t f)
  | _, .nil _ => rfl
  | _, .cons f _ rest => congrArg (fun m => Multiplicative.ofAdd (flux _ f) * m) (ofAdd_total flux rest)

/-- **Totals are functors out of the free category of runs.** -/
theorem total_append (flux : (t : State) → Firing t → A) :
    ∀ {s : State} (r : P.Run s) (later : P.Run r.last),
      total flux (r.append later) = total flux r + total flux later
  | _, .nil _, _ => (zero_add _).symm
  | _, .cons f _ rest, later => by
      show flux _ f + total flux (rest.append later) = flux _ f + total flux rest + total flux later
      rw [total_append flux rest later, add_assoc]
      rfl

/-- **A total is a property of traces** when its flux is invariant under transport, alikeness and
residuals. -/
theorem traceEquiv_total {T : Transport P} (flux : (t : State) → Firing t → A)
    (move : ∀ {s t : State} (i : T.Iso s t) (f : Firing s), flux t (T.move i f) = flux s f)
    (alike : ∀ {s : State} {f f' : Firing s}, T.Alike f f' → flux s f = flux s f')
    (residual : ∀ {s : State} (g : Firing s) (admitted : P.Admits g) (f : Firing s),
      flux _ (T.residual g admitted f) = flux s f)
    {s : State} {r r' : P.Run s} (equivalent : T.TraceEquiv s r r') :
    total flux r = total flux r' := by
  have accounts := Transport.TraceEquiv.account_eq_comm (T := T)
    (fun t f => Multiplicative.ofAdd (flux t f)) (fun i f => congrArg Multiplicative.ofAdd (move i f))
    (fun same => congrArg Multiplicative.ofAdd (alike same))
    (fun g admitted f => congrArg Multiplicative.ofAdd (residual g admitted f)) equivalent
  rw [← ofAdd_total, ← ofAdd_total] at accounts
  exact Multiplicative.ofAdd.injective accounts

end Step.Run

/-! ## Conserved charges -/

/-- **A conserved charge of a step**: a potential on states with a flux each firing takes and a flux
it makes, balancing at every admitted firing. -/
structure ConservedCharge (P : Step X O State Firing) (A : Type uA) [AddCommMonoid A] where
  potential : State → A
  taken : (s : State) → Firing s → A
  made : (s : State) → Firing s → A
  balance : ∀ {s : State} (f : Firing s) (admitted : P.Admits f),
    potential (P.result f admitted) + taken s f = potential s + made s f

namespace ConservedCharge

variable {P : Step X O State Firing} {A : Type uA} [AddCommMonoid A] (Q : ConservedCharge P A)

/-- Everything a run takes. -/
abbrev runTaken {s : State} (r : P.Run s) : A := r.total Q.taken

/-- Everything a run makes. -/
abbrev runMade {s : State} (r : P.Run s) : A := r.total Q.made

/-- **Telescoping**: the potential at the end of a run plus everything it took is the potential at
its start plus everything it made. -/
theorem run_balance : ∀ {s : State} (r : P.Run s),
    Q.potential r.last + Q.runTaken r = Q.potential s + Q.runMade r
  | s, .nil _ => by simp [Step.Run.last]
  | s, .cons f admitted rest => by
      have later := run_balance rest
      have step := Q.balance f admitted
      show Q.potential rest.last + (Q.taken s f + rest.total Q.taken) =
        Q.potential s + (Q.made s f + rest.total Q.made)
      calc Q.potential rest.last + (Q.taken s f + rest.total Q.taken)
          = Q.taken s f + (Q.potential rest.last + rest.total Q.taken) := add_left_comm _ _ _
        _ = Q.taken s f + (Q.potential (P.result f admitted) + rest.total Q.made) := by rw [later]
        _ = Q.potential (P.result f admitted) + Q.taken s f + rest.total Q.made := by
            rw [← add_assoc, add_comm (Q.taken s f)]
        _ = Q.potential s + Q.made s f + rest.total Q.made := by rw [step]
        _ = Q.potential s + (Q.made s f + rest.total Q.made) := add_assoc _ _ _

/-- **Constant along balanced firings**: when every firing of a run takes what it makes, the
potential at its end is the potential at its start. -/
theorem potential_last_of_balanced [IsRightCancelAdd A] :
    ∀ {s : State} (r : P.Run s), (∀ x ∈ r.word, Q.taken x.1 x.2 = Q.made x.1 x.2) →
      Q.potential r.last = Q.potential s
  | _, .nil _, _ => rfl
  | s, .cons f admitted rest, balanced => by
      have head : Q.taken s f = Q.made s f := balanced ⟨s, f⟩ (by simp [Step.Run.word])
      have later := potential_last_of_balanced rest fun x member =>
        balanced x (by simp [Step.Run.word, member])
      have step := Q.balance f admitted
      rw [head] at step
      exact later.trans (add_right_cancel step)

/-! ### Invariance and the fold filter -/

/-- **A charge invariant under a transport**: states of one class carry one potential. -/
def Invariant (T : Transport P) : Prop := ∀ {s t : State}, T.Same s t → Q.potential s = Q.potential t

variable {Q}

/-- **A fold takes exactly what it makes**: a run that ends in the class of its start, under a
transport the charge is invariant under. -/
theorem balanced_of_fold [IsLeftCancelAdd A] {T : Transport P} (invariant : Q.Invariant T)
    {s : State} (r : P.Run s) (fold : T.Same s r.last) : Q.runTaken r = Q.runMade r := by
  have balance := Q.run_balance r
  rw [← invariant fold] at balance
  exact add_left_cancel balance

/-- **The fold filter**: a run that does not take what it makes cannot fold back to its start. -/
theorem not_fold_of_unbalanced [IsLeftCancelAdd A] {T : Transport P} (invariant : Q.Invariant T)
    {s : State} (r : P.Run s) (unbalanced : Q.runTaken r ≠ Q.runMade r) : ¬ T.Same s r.last :=
  fun fold => unbalanced (balanced_of_fold invariant r fold)

/-- **Different potentials, different classes.** -/
theorem not_same_of_potential_ne {T : Transport P} (invariant : Q.Invariant T) {s t : State}
    (differ : Q.potential s ≠ Q.potential t) : ¬ T.Same s t :=
  fun same => differ (invariant same)

/-! ### Charges in groups -/

section Group

variable {G : Type uA} [AddCommGroup G] (Q : ConservedCharge P G)

/-- **The potential of a result, computed from the firing alone.** -/
theorem potential_result {s : State} (f : Firing s) (admitted : P.Admits f) :
    Q.potential (P.result f admitted) = Q.potential s + Q.made s f - Q.taken s f :=
  eq_sub_of_add_eq (Q.balance f admitted)

/-- **The potential at the end of a run, computed from its start and its totals.** -/
theorem potential_last {s : State} (r : P.Run s) :
    Q.potential r.last = Q.potential s + Q.runMade r - Q.runTaken r :=
  eq_sub_of_add_eq (Q.run_balance r)

variable {Q}

/-- **Net flux is a property of traces** for an invariant charge. -/
theorem traceEquiv_net {T : Transport P} (invariant : Q.Invariant T) {s : State} {r r' : P.Run s}
    (equivalent : T.TraceEquiv s r r') : Q.runMade r - Q.runTaken r = Q.runMade r' - Q.runTaken r' := by
  have ends := invariant (Transport.TraceEquiv.same_last equivalent)
  rw [Q.potential_last r, Q.potential_last r', add_sub_assoc, add_sub_assoc] at ends
  exact add_left_cancel ends

end Group

/-! ### Images and products -/

variable (Q)

/-- **The image of a charge under a homomorphism.** -/
def map {B : Type uB} [AddCommMonoid B] (φ : A →+ B) : ConservedCharge P B where
  potential s := φ (Q.potential s)
  taken s f := φ (Q.taken s f)
  made s f := φ (Q.made s f)
  balance f admitted := by rw [← map_add, ← map_add, Q.balance f admitted]

variable {Q}

theorem Invariant.map {B : Type uB} [AddCommMonoid B] {T : Transport P} (invariant : Q.Invariant T)
    (φ : A →+ B) : (Q.map φ).Invariant T :=
  fun same => congrArg φ (invariant same)

/-- **Mismatched images are a sound rejection.** -/
theorem not_same_of_map_ne {B : Type uB} [AddCommMonoid B] {T : Transport P}
    (invariant : Q.Invariant T) (φ : A →+ B) {s t : State}
    (differ : φ (Q.potential s) ≠ φ (Q.potential t)) : ¬ T.Same s t :=
  not_same_of_potential_ne (invariant.map φ) differ

/-- **Wrapping machine arithmetic keeps a charge**: an integer charge read modulo `2 ^ 64` is a
charge, invariant whenever the integer charge is, so its mismatch is a sound rejection. -/
theorem intCharge_wrap {Q : ConservedCharge P ℤ} {T : Transport P} (invariant : Q.Invariant T)
    {s t : State} (differ : ((Q.potential s : ℤ) : ZMod (2 ^ 64)) ≠ ((Q.potential t : ℤ) : ZMod (2 ^ 64))) :
    ¬ T.Same s t :=
  not_same_of_map_ne invariant (Int.castAddHom (ZMod (2 ^ 64)))
    (by simpa only [Int.coe_castAddHom] using differ)

/-- **A family of charges is a charge in the product.** -/
def pi {ι : Type uK} {B : ι → Type uB} [∀ i, AddCommMonoid (B i)] (Q : ∀ i, ConservedCharge P (B i)) :
    ConservedCharge P (∀ i, B i) where
  potential s i := (Q i).potential s
  taken s f i := (Q i).taken s f
  made s f i := (Q i).made s f
  balance f admitted := funext fun i => (Q i).balance f admitted

theorem Invariant.pi {ι : Type uK} {B : ι → Type uB} [∀ i, AddCommMonoid (B i)]
    {Q : ∀ i, ConservedCharge P (B i)} {T : Transport P} (invariant : ∀ i, (Q i).Invariant T) :
    (ConservedCharge.pi Q).Invariant T :=
  fun same => funext fun i => invariant i same

end ConservedCharge

/-! ## Occurrence weights -/

section Weights

variable {A : Type uA} [AddCommMonoid A]

/-- **Occurrence weights are conserved charges of every step**: the total weight of the present
occurrences, with the weights of the taken and of the made occurrences as fluxes. -/
def weightCharge (P : Step X O State Firing) (w : O → A) : ConservedCharge P A where
  potential s := ∑ o ∈ P.present s, w o
  taken _ f := ∑ o ∈ (P.selection f).taken.toFinset, w o
  made _ f := ∑ o ∈ (P.selection f).made.toFinset, w o
  balance {s} f admitted := by
    have enabled := (P.prepares admitted).2.1
    have inside : (P.selection f).taken.toFinset ⊆ P.present s := enabled.taken_subset
    have fresh : Disjoint (P.selection f).made.toFinset (P.present s) := enabled.fresh
    have apart : Disjoint (P.present s \ (P.selection f).taken.toFinset) (P.selection f).made.toFinset :=
      fresh.symm.mono_left Finset.sdiff_subset
    show ∑ o ∈ P.present (P.result f admitted), w o + ∑ o ∈ (P.selection f).taken.toFinset, w o =
      ∑ o ∈ P.present s, w o + ∑ o ∈ (P.selection f).made.toFinset, w o
    rw [P.present_result f admitted]
    show ∑ o ∈ (P.present s \ (P.selection f).taken.toFinset) ∪ (P.selection f).made.toFinset, w o +
        ∑ o ∈ (P.selection f).taken.toFinset, w o =
      ∑ o ∈ P.present s, w o + ∑ o ∈ (P.selection f).made.toFinset, w o
    rw [Finset.sum_union apart, add_right_comm, Finset.sum_sdiff inside]

/-- **Occurrence weights are invariant** under every transport whose renamings keep the weight of
the present occurrences. -/
theorem weightCharge_invariant {P : Step X O State Firing} (T : Transport P) (w : O → A)
    (keeps : ∀ {s t : State} (i : T.Iso s t), ∀ o ∈ P.present s, w ((T.toStateIso i).rename o) = w o) :
    (weightCharge P w).Invariant T := by
  rintro s t ⟨i⟩
  show ∑ o ∈ P.present s, w o = ∑ o ∈ P.present t, w o
  rw [← (T.toStateIso i).present, Finset.sum_map]
  exact (Finset.sum_congr rfl fun o member => keeps i o member).symm

omit [DecidableEq O] in
/-- A sum of singletons is the multiset of the values. -/
theorem sum_singleton_eq_map {V : Type uB} (s : Finset O) (v : O → V) :
    ∑ o ∈ s, ({v o} : Multiset V) = s.val.map v := by
  have collected := Multiset.sum_map_singleton (s.val.map v)
  rw [Multiset.map_map] at collected
  exact collected

/-- **Value counts**: with the weight `o ↦ {v o}`, the potential is the multiset of the values of
the present occurrences. -/
theorem weightCharge_singleton_potential {V : Type uB} (P : Step X O State Firing) (v : O → V)
    (s : State) : (weightCharge P fun o => ({v o} : Multiset V)).potential s = (P.present s).val.map v :=
  sum_singleton_eq_map _ v

end Weights

#print axioms Step.Run.ofAdd_total
#print axioms Step.Run.total_append
#print axioms Step.Run.traceEquiv_total
#print axioms ConservedCharge.run_balance
#print axioms ConservedCharge.potential_last_of_balanced
#print axioms ConservedCharge.balanced_of_fold
#print axioms ConservedCharge.not_fold_of_unbalanced
#print axioms ConservedCharge.not_same_of_potential_ne
#print axioms ConservedCharge.potential_result
#print axioms ConservedCharge.potential_last
#print axioms ConservedCharge.traceEquiv_net
#print axioms ConservedCharge.Invariant.map
#print axioms ConservedCharge.not_same_of_map_ne
#print axioms ConservedCharge.intCharge_wrap
#print axioms ConservedCharge.Invariant.pi
#print axioms weightCharge
#print axioms weightCharge_invariant
#print axioms weightCharge_singleton_potential

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
