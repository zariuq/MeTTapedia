import Mathlib.Order.Closure
import Mettapedia.Cybernetics.ObservedVariety

/-!
# Relational closure with derivation receipts

A connection network is a set of directed connections.  A relational closure
adds the connections licensed by one selected closure discipline.  Its three
laws are proved before the construction is exposed as Mathlib's
`ClosureOperator`.

The informative object is not only the closed network.  `ConnectionReceipt`
retains whether each resulting connection was authored or generated.  At the
presentation level, two networks become internally indistinguishable exactly
when they have the same closure, while different closures remain externally
distinguishable.

Symmetric closure is the worked source-faithful instance.  It exhibits both a
generated inverse connection and two distinct presentations whose difference
is suppressed after closure.

Reference:

- F. Heylighen, *Relational Closure: a mathematical concept for
  distinction-making and complexity analysis* (1990).
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics

universe uNode

namespace RelationalClosure

/-- A directed connection network. -/
abbrev Network (Node : Type uNode) := Set (Node × Node)

/-- The closure laws, kept separate from any particular implementation. -/
structure Laws {Node : Type uNode}
    (close : Network Node → Network Node) : Prop where
  extensive : ∀ network, network ⊆ close network
  monotone : Monotone close
  idempotent : ∀ network, close (close network) = close network

/-- A selected relational closure discipline. -/
structure System (Node : Type uNode) where
  close : Network Node → Network Node
  laws : Laws close

namespace System

variable {Node : Type uNode}

/-- The proved relational closure is a standard Mathlib closure operator. -/
def toClosureOperator (system : System Node) :
    ClosureOperator (Network Node) where
  toFun := system.close
  monotone' := system.laws.monotone
  le_closure' := system.laws.extensive
  idempotent' := system.laws.idempotent

/-- A connection was either authored or added by the selected closure. -/
inductive ConnectionOrigin (system : System Node)
    (seed : Network Node) (connection : Node × Node) : Type uNode where
  | authored (member : connection ∈ seed)
  | generated (closedMember : connection ∈ system.close seed)
      (notAuthored : connection ∉ seed)

/-- A proof-relevant receipt for one connection in a closed network. -/
structure ConnectionReceipt (system : System Node)
    (seed : Network Node) : Type uNode where
  connection : Node × Node
  origin : ConnectionOrigin system seed connection

/-- Every closed connection has an authored-or-generated receipt. -/
noncomputable def receiptOfClosed (system : System Node)
    (seed : Network Node) {connection : Node × Node}
    (closedMember : connection ∈ system.close seed) :
    ConnectionReceipt system seed := by
  classical
  refine ⟨connection, ?_⟩
  by_cases authored : connection ∈ seed
  · exact .authored authored
  · exact .generated closedMember authored

/-- Presentations whose closures agree differ only by distinctions suppressed
by the selected closure discipline. -/
def SameClosedPresentation (system : System Node)
    (first second : Network Node) : Prop :=
  system.close first = system.close second

/-- The closed-network observer promotes differences between distinct closure
classes to external distinctions. -/
def observer (system : System Node) :
    Observer (Network Node) (Network Node) where
  observe := system.close

theorem sameClosedPresentation_iff_not_distinguished
    (system : System Node) (first second : Network Node) :
    system.SameClosedPresentation first second ↔
      ¬ system.observer.Distinguishes first second := by
  simp [SameClosedPresentation, observer, Observer.Distinguishes]

/-- A seed and its closure are internally indistinguishable after closure. -/
theorem seed_sameClosedPresentation_close
    (system : System Node) (seed : Network Node) :
    system.SameClosedPresentation seed (system.close seed) := by
  exact system.laws.idempotent seed |>.symm

end System

/-! ## Symmetric closure -/

/-- Reverse every directed connection. -/
def reverse {Node : Type uNode} (network : Network Node) : Network Node :=
  {connection | (connection.2, connection.1) ∈ network}

/-- Add the inverse of every authored connection. -/
def symmetricClose {Node : Type uNode}
    (network : Network Node) : Network Node :=
  network ∪ reverse network

theorem symmetricClose_laws {Node : Type uNode} :
    Laws (@symmetricClose Node) where
  extensive network connection member := Or.inl member
  monotone := by
    intro first second subset connection member
    rcases member with authored | reversed
    · exact Or.inl (subset authored)
    · exact Or.inr (subset reversed)
  idempotent := by
    intro network
    ext connection
    rcases connection with ⟨source, target⟩
    simp only [symmetricClose, reverse, Set.mem_union, Set.mem_setOf_eq]
    aesop

/-- Symmetric closure as a proved relational closure system. -/
def symmetric (Node : Type uNode) : System Node where
  close := symmetricClose
  laws := symmetricClose_laws

/-! ## Separating canaries -/

namespace SymmetricCanary

abbrev Node := Bool

def seed : Network Node := {(false, true)}

theorem inverse_mem_close :
    (true, false) ∈ (symmetric Node).close seed := by
  simp [symmetric, symmetricClose, reverse, seed]

theorem inverse_not_mem_seed : (true, false) ∉ seed := by
  simp [seed]

/-- The inverse is genuinely generated rather than silently reclassified as
authored. -/
def inverseReceipt : (symmetric Node).ConnectionReceipt seed where
  connection := (true, false)
  origin := .generated inverse_mem_close inverse_not_mem_seed

theorem seed_ne_close : seed ≠ (symmetric Node).close seed := by
  intro equal
  have authoredInverse : (true, false) ∈ seed := by
    rw [equal]
    exact inverse_mem_close
  exact inverse_not_mem_seed authoredInverse

/-- A real internal presentation distinction is suppressed by closure. -/
theorem distinct_presentations_same_closure :
    seed ≠ (symmetric Node).close seed ∧
      (symmetric Node).SameClosedPresentation
        seed ((symmetric Node).close seed) :=
  ⟨seed_ne_close,
    (symmetric Node).seed_sameClosedPresentation_close seed⟩

/-- Closure still promotes an external distinction between the empty network
and a network containing a real connection. -/
theorem empty_seed_distinguished :
    (symmetric Node).observer.Distinguishes ∅ seed := by
  intro equal
  change (symmetric Node).close ∅ = (symmetric Node).close seed at equal
  have member : (false, true) ∈ (symmetric Node).close seed := by
    exact (symmetric Node).laws.extensive seed (by simp [seed])
  have notMember : (false, true) ∉ (symmetric Node).close ∅ := by
    simp [symmetric, symmetricClose, reverse]
  apply notMember
  rw [equal]
  exact member

end SymmetricCanary

end RelationalClosure

end Mettapedia.Cybernetics

#print axioms Mettapedia.Cybernetics.RelationalClosure.symmetricClose_laws
#print axioms Mettapedia.Cybernetics.RelationalClosure.SymmetricCanary.distinct_presentations_same_closure
#print axioms Mettapedia.Cybernetics.RelationalClosure.SymmetricCanary.empty_seed_distinguished
