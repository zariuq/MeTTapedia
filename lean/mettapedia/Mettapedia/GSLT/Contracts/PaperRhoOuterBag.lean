import Mettapedia.GSLT.Contracts.PaperRhoAdequacy

/-!
# The outer bag of the paper-facing rho calculus

Only the unguarded parallel layer is a bag. Its labels still retain the
congruence of prefixes, name equality and scoped substitution. Thus the
bag accounts exactly for exchange and multiplicity without pretending
that communication may descend into suspended code.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.PaperRho.OuterBag

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.OSLF.MeTTaIL.PatternCode (sortPatterns_eq_of_perm)
open Adequacy (canonicalForm parallelMembers)

def outer (process : Process) : Multiset Pattern :=
  ((parallelMembers process).map canonicalForm : Multiset Pattern)

@[simp] theorem outer_zero : outer .zero = 0 := rfl

@[simp] theorem outer_par (first second : Process) :
    outer (.par first second) = outer first + outer second := by
  simp only [outer, parallelMembers, List.map_append, Multiset.coe_add]

@[simp] theorem outer_send (channel : Name) (payload : Process) :
    outer (.send channel payload) = {canonicalForm (.send channel payload)} := rfl

@[simp] theorem outer_receive (channel : Name) (body : Process) :
    outer (.receive channel body) = {canonicalForm (.receive channel body)} := rfl

@[simp] theorem outer_card (process : Process) :
    (outer process).card = (parallelMembers process).length := by
  simp only [outer, Multiset.coe_card, List.length_map]

theorem outer_exact (first second : Process) :
    outer first = outer second ↔ Congruence first second := by
  constructor
  · intro same
    apply (Adequacy.canonicalize_encodeProcess_eq_iff first second).mp
    change canonicalForm first = canonicalForm second
    have permutation := Multiset.coe_eq_coe.mp same
    rw [Adequacy.canonicalForm_eq_collapse first, Adequacy.canonicalForm_eq_collapse second,
      sortPatterns_eq_of_perm permutation]
  · intro equal
    have same := (Adequacy.canonicalize_encodeProcess_eq_iff first second).mpr equal
    change canonicalForm first = canonicalForm second at same
    have a := Adequacy.parallelContents_canonicalForm first
    have b := Adequacy.parallelContents_canonicalForm second
    rw [same] at a
    exact Multiset.coe_eq_coe.mpr (a.symm.trans b)

def needed (offered waiting : Name) (payload body : Process) : Multiset Pattern :=
  {canonicalForm (.send offered payload)} + {canonicalForm (.receive waiting body)}

/-- One paper step replaces two selected outer occurrences; the other
occurrences survive with all their multiplicities. Whether the two can
communicate is decided by the paper's actual name and scope judgments. -/
theorem reduction_iff_outer (before after : Process) :
    Reduction before after ↔
      ∃ (offered waiting : Name) (payload body frame : Process),
        ScopedName 0 offered ∧ ScopedName 0 waiting ∧ ScopedProcess 0 payload ∧ ScopedProcess 1 body ∧
        NameEquivalence offered waiting ∧
        outer before = needed offered waiting payload body + outer frame ∧
        outer after = outer (.par (substitute payload 0 body) frame) := by
  constructor
  · intro fired
    obtain ⟨offered, waiting, payload, body, frame, ho, hw, hp, hb, channel, start, finish⟩ :=
      Adequacy.redex_of_reduction fired
    exact ⟨offered, waiting, payload, body, frame, ho, hw, hp, hb, channel,
      by simpa only [needed, outer_par, outer_send, outer_receive] using (outer_exact _ _).mpr start,
      (outer_exact _ _).mpr finish⟩
  · rintro ⟨offered, waiting, payload, body, frame, ho, hw, hp, hb, channel, start, finish⟩
    have beforeEq :
        Congruence before (.par (.par (.send offered payload) (.receive waiting body)) frame) :=
      (outer_exact _ _).mp (by simpa only [needed, outer_par, outer_send, outer_receive] using start)
    have afterEq := (outer_exact _ _).mp finish
    exact .equiv beforeEq (.par frame (.comm ho hw hp hb channel (substitute_fits payload 0 body)))
      afterEq.symm

theorem two_active_occurrences {before after : Process} (step : Reduction before after) :
    2 ≤ (outer before).card := by
  obtain ⟨offered, waiting, payload, body, frame, _, _, _, _, _, required, _⟩ :=
    (reduction_iff_outer before after).mp step
  rw [required]
  simp [needed]

theorem suspended_body_cannot_fire (channel : Name) (body after : Process) :
    ¬Reduction (.receive channel body) after := by
  intro admitted
  have sizes := two_active_occurrences admitted
  simp at sizes

def forwarder (channel : Name) : Process := .receive channel (.drop (.bound 0))

/-- The forwarder simply releases the matched closed payload. There
is no general body-substitution problem left in this specialization. -/
theorem forward_closed (offered waiting : Name) (payload frame : Process)
    (ho : ScopedName 0 offered) (hw : ScopedName 0 waiting) (closed : ScopedProcess 0 payload)
    (agrees : NameEquivalence offered waiting) :
    Reduction (.par (.par (.send offered payload) (forwarder waiting)) frame) (.par payload frame) :=
  .par frame (.comm ho hw closed (.drop (.bound (by decide))) agrees (.drop_hit (.refl _)))

end Mettapedia.GSLT.Contracts.PaperRho.OuterBag
