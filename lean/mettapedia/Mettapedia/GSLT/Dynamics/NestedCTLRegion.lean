import Mettapedia.Logic.BDD.NestedCTL
import Mettapedia.Logic.CTLContextualInformation
import Mettapedia.Logic.BDD.Canonical
import Mettapedia.GSLT.Dynamics.RegionPortfolio

/-!
# Nested symbolic CTL as an observation-qualified region

The reference is nested path semantics and the worker is total BDD compilation.
The canonical key theorem connects diagram identity to all fixed-model CTL
continuations. The transition model, labels and valid-state domain remain
parameters of the certificate. Solver counts and MeTTa driver counts are not
identified by this value-observer adapter.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.ObservationQualified.NestedCTLRegion

open Mettapedia.Logic CTLFormula BDDCore StatePredicates StateTransducer

variable {Label : Type} {n : Nat} {domain : Diagram n}

def questions (n : Nat) : RegionObservations.Family (Set (State n)) where
  Question := Set (State n) → Bool
  Answer _ := Bool
  read question states := question states

def boundary (program : Certified n domain) (atoms : Label → Diagram n) :
    Boundary (Formula Label) (Set (State n)) (Set (State n)) where
  source := meaning (denote domain) (Relation domain program.rules) (fun label => denote (atoms label))
  summarize := id
  future := questions n
  sufficient _ _ same question := congrArg question same

def region (program : Certified n domain) (atoms : Label → Diagram n) :
    CertifiedRegion (boundary program atoms) Nat where
  regime := 0
  Artifact := Diagram n
  attempt formula := .committed (NestedCTL.compile program atoms formula)
  decode := denote
  restores _ _ impossible := by cases impossible
  exact formula _ committed := by
    cases committed
    exact NestedCTL.compile_exact program atoms formula

/-- Compilation identifies exactly those formulas indistinguishable by all
the admitted nested contexts in this fixed model. -/
theorem canonical_key_exact (program : Certified n domain) (atoms : Label → Diagram n) :
    (CTLContextualInformation.observers (denote domain) (Relation domain program.rules)
      (fun label => denote (atoms label))).Exact (NestedCTL.compile program atoms) := by
  intro first second
  rw [Canonical.diagram_eq_iff_denote, NestedCTL.compile_exact, NestedCTL.compile_exact]
  exact CTLContextualInformation.meaning_exact _ _ _ first second

theorem key_sufficient (program : Certified n domain) (atoms : Label → Diagram n) :
    (CTLContextualInformation.observers (denote domain) (Relation domain program.rules)
      (fun label => denote (atoms label))).Sufficient (NestedCTL.compile program atoms) :=
  fun first second => (canonical_key_exact program atoms first second).mp

/-- Compilation clears invalid codes, so equality on the valid domain is
already equality of the canonical key. Without that clipping invariant the
same conclusion would be false for arbitrary diagrams. -/
theorem valid_domain_key_exact (program : Certified n domain) (atoms : Label → Diagram n)
    (first second : Formula Label) :
    NestedCTL.compile program atoms first = NestedCTL.compile program atoms second ↔
      ∀ state ∈ denote domain,
        (NestedCTL.compile program atoms first).val.eval state =
          (NestedCTL.compile program atoms second).val.eval state := by
  constructor
  · intro same state _
    rw [same]
  · intro agree
    apply (Canonical.equivalent_iff_equal _ _).mp
    apply (equivalent_iff _ _).mpr
    intro state
    by_cases valid : state ∈ denote domain
    · exact agree state valid
    · have firstOutside : state ∉ denote (NestedCTL.compile program atoms first) :=
        fun member => valid (NestedCTL.compile_within program atoms first member)
      have secondOutside : state ∉ denote (NestedCTL.compile program atoms second) :=
        fun member => valid (NestedCTL.compile_within program atoms second member)
      simp only [denote, BDD.satSet, Set.mem_ofPred_eq, Bool.not_eq_true] at firstOutside secondOutside
      rw [firstOutside, secondOutside]

end Mettapedia.GSLT.Dynamics.ObservationQualified.NestedCTLRegion
