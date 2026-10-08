import Mettapedia.GSLT.Logic.ProgrammableSpaceEvidenceInference
import Mettapedia.GSLT.Logic.ProgrammableSpaceEvidenceReadings

/-!
# Shared-query reachability and dependent evidence consumers

The authored source has edges `n → n+1`, `n+1 → n+2` and `n → n+2`.
Two actual rule occurrences answer the same selected query, one directly and
one through the intermediate vertex. They share the input occurrence that
selected the query. Another query has a different destination and a different
dependent result type.

Destination-indexed outputs use only the fact quotient. Route observations and
certificates that a specified edge was used need the retained derivation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ProgrammableSpaceEvidence.Controls

attribute [local instance] Finite.membership

open Mettapedia.TypeTheory.DependentFamilyObserverFactorization
open Mettapedia.TypeTheory.DependentFamilySectionDescent

inductive Atom where
  | selected (start finish : Nat)
  | edge (start finish : Nat)
  | reaches (start finish : Nat)
  deriving DecidableEq

def Atom.destination : Atom → Nat
  | .selected _ finish | .edge _ finish | .reaches _ finish => finish

inductive Origin where
  | nearQuery | farQuery | firstEdge | secondEdge | directEdge
  deriving DecidableEq

def source (n : Nat) : Source Atom Origin where
  input
    | .nearQuery => .selected n (n+1)
    | .farQuery => .selected n (n+2)
    | .firstEdge => .edge n (n+1)
    | .secondEdge => .edge (n+1) (n+2)
    | .directEdge => .edge n (n+2)
  rules := [
    ⟨[.selected n (n+1), .edge n (n+1)], .reaches n (n+1)⟩,
    ⟨[.selected n (n+2), .edge n (n+2)], .reaches n (n+2)⟩,
    ⟨[.selected n (n+2), .edge n (n+1), .edge (n+1) (n+2)], .reaches n (n+2)⟩]

def nearProof (n : Nat) : Derivation (source n) (.reaches n (n+1)) :=
  .rule ⟨0, by change 0 < 3; decide⟩
    (Fin.cases (Derivation.input (source := source n) Origin.nearQuery)
      (Fin.cases (Derivation.input (source := source n) Origin.firstEdge) (fun i => Fin.elim0 i)))

def directProof (n : Nat) : Derivation (source n) (.reaches n (n+2)) :=
  .rule ⟨1, by change 1 < 3; decide⟩
    (Fin.cases (Derivation.input (source := source n) Origin.farQuery)
      (Fin.cases (Derivation.input (source := source n) Origin.directEdge) (fun i => Fin.elim0 i)))

def indirectProof (n : Nat) : Derivation (source n) (.reaches n (n+2)) :=
  .rule ⟨2, by change 2 < 3; decide⟩
    (Fin.cases (Derivation.input (source := source n) Origin.farQuery)
      (Fin.cases (Derivation.input (source := source n) Origin.firstEdge)
        (Fin.cases (Derivation.input (source := source n) Origin.secondEdge) (fun i => Fin.elim0 i))))

def near (n : Nat) : Receipt (source n) := ⟨_, nearProof n⟩
def direct (n : Nat) : Receipt (source n) := ⟨_, directProof n⟩
def indirect (n : Nat) : Receipt (source n) := ⟨_, indirectProof n⟩

@[simp] theorem direct_origins (n : Nat) :
    (direct n).origins = [.farQuery, .directEdge] := rfl

@[simp] theorem indirect_origins (n : Nat) :
    (indirect n).origins = [.farQuery, .firstEdge, .secondEdge] := rfl

theorem same_fact (n : Nat) : (direct n).fact = (indirect n).fact := rfl

theorem different_derivations (n : Nat) : direct n ≠ indirect n := by
  intro same
  have different := congrArg (fun receipt : Receipt (source n) => receipt.root.map Fin.val) same
  change some 1 = some 2 at different
  cases different

theorem same_fact_class (n : Nat) :
    observeFact (source n) (direct n) = observeFact (source n) (indirect n) :=
  Quotient.sound (same_fact n)

theorem share_query_origin (n : Nat) :
    ¬ Receipt.OriginSeparated (direct n) (indirect n) :=
  Receipt.not_originSeparated_of_shared _ _ .farQuery
    (by simp only [direct_origins, List.mem_cons, true_or])
    (by simp only [indirect_origins, List.mem_cons, true_or])

def answers (n : Nat) : List (Receipt (source n)) := [direct n, indirect n]

def answerSupport (n : Nat) : Finset Atom := batchSupport (answers n)

def answerOrigins (n : Nat) : Finset Origin :=
  batchOriginSupport (answers n)

def queryOrigins (n : Nat) : Finset Origin :=
  (answerOrigins n).filter fun origin => origin = .nearQuery ∨ origin = .farQuery

theorem three_counts (n : Nat) :
    (answers n).length = 2 ∧ (answerSupport n).card = 1 ∧
      (answerOrigins n).card = 4 ∧ (queryOrigins n).card = 1 := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · simp [answerSupport, batchSupport, answers, direct, indirect, Receipt.fact,
      Finite.support, Finite.unique]
  · change (Finite.support [Origin.farQuery, Origin.directEdge, Origin.farQuery,
      Origin.firstEdge, Origin.secondEdge]).card = 4
    decide
  · change ((Finite.support [Origin.farQuery, Origin.directEdge, Origin.farQuery,
      Origin.firstEdge, Origin.secondEdge]).filter
        fun origin => origin = .nearQuery ∨ origin = .farQuery).card = 1
    decide

def inputOrigins : List Origin :=
  [.nearQuery, .farQuery, .firstEdge, .secondEdge, .directEdge]

/-- The two proof paths are produced by the actual typed premise-bag operator. -/
theorem actual_production_count :
    (producedReceipts (source 0) (inputBag (source 0) inputOrigins) (.reaches 0 2)).card = 2 := by
  rw [produced_count]
  decide +kernel

theorem actual_production_receipts :
    producedReceipts (source 0) (inputBag (source 0) inputOrigins) (.reaches 0 2) =
      (answers 0 : Multiset (Receipt (source 0))) := by
  rfl

theorem repeating_one_path_is_not_both_paths (n : Nat) :
    [direct n, direct n] ≠ answers n := by
  intro same
  have last := List.cons.inj (List.cons.inj same).2
  exact different_derivations n last.1

abbrev Payload {n : Nat} (receipt : Receipt (source n)) : Type :=
  Fin (receipt.fact.destination + 1)

def payloadFamily (n : Nat) : FamilyFactorization Receipt.fact (@Payload n) where
  targetFamily atom := Fin (atom.destination + 1)
  identify _ := Equiv.refl _

def destination {n : Nat} (receipt : Receipt (source n)) : Payload receipt :=
  ⟨receipt.fact.destination, Nat.lt_succ_self _⟩

theorem destination_compatible (n : Nat) : Compatible (payloadFamily n) destination := by
  intro first second same
  exact congrArg (fun atom : Atom =>
    (⟨atom, ⟨atom.destination, Nat.lt_succ_self _⟩⟩ : Sigma fun atom => Fin (atom.destination+1))) same

def factDestination (n : Nat) : ∀ value, factFamily (payloadFamily n) value :=
  descend (payloadFamily n) destination (destination_compatible n)

theorem factDestination_agrees (n : Nat) (receipt : Receipt (source n)) :
    factDestination n (observeFact (source n) receipt) = destination receipt := rfl

theorem payload_is_not_constant (n : Nat) : ¬ Nonempty (Payload (near n) ≃ Payload (direct n)) := by
  rintro ⟨equivalence⟩
  have sizes := Finite.fin_size_of_equiv equivalence
  exact Nat.ne_of_lt (Nat.lt_succ_self (n+1+1)) sizes

def usedIntermediate {n : Nat} (receipt : Receipt (source n)) : Bool :=
  match receipt.root with
  | none => false
  | some index => index.val == 2

def routeFamily (n : Nat) : FamilyFactorization Receipt.fact
    (fun _ : Receipt (source n) => Bool) := FamilyFactorization.constant Receipt.fact Bool

theorem route_not_compatible (n : Nat) : ¬ Compatible (routeFamily n) usedIntermediate := by
  intro compatible
  have same := compatible (direct n) (indirect n) (same_fact n)
  have values := eq_of_heq (Sigma.mk.inj_iff.mp same).2
  exact Bool.false_ne_true values

theorem route_not_from_facts (n : Nat) :
    ¬ ∃ consumer : ∀ value, factFamily (routeFamily n) value,
      pullback (routeFamily n) consumer = usedIntermediate :=
  fun existsConsumer => route_not_compatible n
    ((compatible_iff_descends (routeFamily n) usedIntermediate).mpr existsConsumer)

/-- A dependent consumer requiring evidence that the direct edge was used. -/
def DirectEdgeCertificate {n : Nat} (receipt : Receipt (source n)) : Type :=
  PLift (Origin.directEdge ∈ receipt.origins)

def directEdgeCertificate (n : Nat) : DirectEdgeCertificate (direct n) :=
  ⟨by simp [direct_origins]⟩

theorem no_indirectEdgeCertificate (n : Nat) : ¬ Nonempty (DirectEdgeCertificate (indirect n)) := by
  rintro ⟨certificate⟩
  have member := certificate.down
  simp only [indirect_origins, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with impossible | impossible | impossible <;> cases impossible

/-- Even the family cannot be reconstructed from the conclusion alone. -/
theorem directEdgeFamily_not_descending (n : Nat) :
    ¬ Nonempty (FamilyFactorization Receipt.fact (@DirectEdgeCertificate n)) := by
  rintro ⟨factorization⟩
  let change := equalityEquiv (congrArg factorization.targetFamily (same_fact n))
  let transfer := (factorization.identify (direct n)).trans
    (change.trans (factorization.identify (indirect n)).symm)
  exact no_indirectEdgeCertificate n ⟨transfer (directEdgeCertificate n)⟩

end Mettapedia.GSLT.ProgrammableSpaceEvidence.Controls
