import Mettapedia.GSLT.Logic.ContextHML
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Lattice

/-!
# Assembly Theory and Namespace Copy Number

This file formalizes the clearest constructive kernel from Meredith's
"Computation, Causality, and Consciousness" (2026), Part III, §23.

## Main Definitions

* `AssemblyPath` — a context-labeled construction path
* `AssemblyWitness` — a context-labeled construction path from an elementary term
* `assemblyIndex` — minimum interactive path length from the elementary set
* `Namespace` — a finite region of channels equipped with channel contents
* `Namespace.copyNumber` — number of channels whose contents are bisimilar to a term

## Design Note

The paper's strongest fully formalizable Part III claims are the ones that depend
only on the open synchronization tree and on bisimilarity. This file therefore
proves the minimum-causal-depth and copy-counting kernel, while leaving the later
density/phase-transition claims for explicit future work.

## References

- Meredith, "Computation, Causality, and Consciousness" (2026), §23
- Cronin & Walker, "Assembly Theory"
-/

namespace Mettapedia.GSLT

variable (S : GSLT)
variable [HasMinimalContexts S]

/-- A designated set of elementary terms from which assembly paths may start. -/
abbrev ElementaryTerms := Set S.Term

/-- A context-labeled path used for assembly depth. This is the local Part III path
    kernel and does not depend on the broader synchronization-tree file. -/
inductive AssemblyPath : S.Term → S.Term → Type _ where
  | nil (t : S.Term) : AssemblyPath t t
  | cons {t u v : S.Term} (K : MinimalContext S)
      (h : S.Step (K.plug t) u) (rest : AssemblyPath u v) :
      AssemblyPath t v

/-- Length of an assembly path. -/
def AssemblyPath.length : {t u : S.Term} → AssemblyPath (S := S) t u → Nat
  | _, _, .nil _ => 0
  | _, _, .cons _ _ rest => 1 + rest.length

/-- A witness that `M` can be assembled from an elementary source by a context-labeled path. -/
structure AssemblyWitness (E : ElementaryTerms S) (M : S.Term) where
  /-- The chosen elementary source term -/
  source : S.Term
  /-- The source belongs to the designated elementary set -/
  source_mem : source ∈ E
  /-- A context-labeled path from the source to `M` -/
  path : AssemblyPath (S := S) source M

/-- `M` is assemblable from `E` if there exists at least one assembly witness. -/
def Assemblable (E : ElementaryTerms S) (M : S.Term) : Prop :=
  Nonempty (AssemblyWitness (S := S) E M)

/-- The set of all interactive path lengths witnessing assembly from `E` to `M`. -/
def assemblyDepths (E : ElementaryTerms S) (M : S.Term) : Set Nat :=
  { n | ∃ w : AssemblyWitness (S := S) E M, w.path.length (S := S) = n }

/-- Definition 23.1/Proposition 23.1 kernel:
    the assembly index is the minimum interactive path length from the elementary set. -/
noncomputable def assemblyIndex {E : ElementaryTerms S} {M : S.Term}
    (_hA : Assemblable (S := S) E M) : Nat :=
  sInf (assemblyDepths (S := S) E M)

theorem assemblyDepths_nonempty {E : ElementaryTerms S} {M : S.Term}
    (hA : Assemblable (S := S) E M) :
    (assemblyDepths (S := S) E M).Nonempty := by
  rcases hA with ⟨w⟩
  exact ⟨w.path.length (S := S), ⟨w, rfl⟩⟩

theorem assemblyIndex_mem {E : ElementaryTerms S} {M : S.Term}
    (hA : Assemblable (S := S) E M) :
    assemblyIndex (S := S) hA ∈ assemblyDepths (S := S) E M :=
  Nat.sInf_mem (assemblyDepths_nonempty (S := S) hA)

/-- The minimum assembly depth is attained by some concrete interactive path. -/
theorem assemblyIndex_attained {E : ElementaryTerms S} {M : S.Term}
    (hA : Assemblable (S := S) E M) :
    ∃ w : AssemblyWitness (S := S) E M,
      w.path.length (S := S) = assemblyIndex (S := S) hA := by
  exact assemblyIndex_mem (S := S) hA

/-- Every concrete assembly witness bounds the assembly index from above. -/
theorem assemblyIndex_le_of_witness {E : ElementaryTerms S} {M : S.Term}
    (hA : Assemblable (S := S) E M) (w : AssemblyWitness (S := S) E M) :
    assemblyIndex (S := S) hA ≤ w.path.length (S := S) := by
  exact Nat.sInf_le ⟨w, rfl⟩

/-- If one witness is length-minimal among all assembly witnesses, then its path length
    is exactly the assembly index. -/
theorem assemblyIndex_eq_of_minimal {E : ElementaryTerms S} {M : S.Term}
    (hA : Assemblable (S := S) E M) (w : AssemblyWitness (S := S) E M)
    (hmin : ∀ w' : AssemblyWitness (S := S) E M,
      w.path.length (S := S) ≤ w'.path.length (S := S)) :
    assemblyIndex (S := S) hA = w.path.length (S := S) := by
  apply le_antisymm
  · exact assemblyIndex_le_of_witness (S := S) hA w
  · rcases assemblyIndex_attained (S := S) hA with ⟨wmin, hwmin⟩
    rw [← hwmin]
    exact hmin wmin

/-- An elementary term assembles to itself via the empty interactive path. -/
def elementaryWitness {E : ElementaryTerms S} {M : S.Term} (hM : M ∈ E) :
    AssemblyWitness (S := S) E M where
  source := M
  source_mem := hM
  path := .nil M

/-- Every elementary term is assemblable from the elementary set. -/
theorem elementary_assemblable {E : ElementaryTerms S} {M : S.Term}
    (hM : M ∈ E) :
    Assemblable (S := S) E M :=
  ⟨elementaryWitness (S := S) hM⟩

/-- Elementary terms have assembly index `0`. -/
theorem assemblyIndex_eq_zero_of_mem {E : ElementaryTerms S} {M : S.Term}
    (hM : M ∈ E) :
    assemblyIndex (S := S) (elementary_assemblable (S := S) hM) = 0 := by
  let w := elementaryWitness (S := S) hM
  have hle := assemblyIndex_le_of_witness (S := S) (elementary_assemblable (S := S) hM) w
  exact le_antisymm hle (Nat.zero_le _)

/-- A finite namespace of channels equipped with their hosted contents. -/
structure Namespace (Channel : Type*) where
  /-- The channels belonging to the namespace -/
  channels : Finset Channel
  /-- The content hosted at each channel -/
  contents : Channel → S.Term

namespace Namespace

variable {S} {Channel : Type*}

/-- Definition 23.4 kernel: the copy number of `P` in a namespace is the number of
    channels whose contents are bisimilar to `P`. -/
noncomputable def copyNumber (N : Namespace S Channel) (P : S.Term) : Nat := by
  classical
  exact (N.channels.filter fun c => S.Bisimilar (N.contents c) P).card

@[simp] theorem copyNumber_empty (contents : Channel → S.Term) (P : S.Term) :
    copyNumber (S := S) ({ channels := ∅, contents := contents } : Namespace S Channel) P = 0 := by
  classical
  simp [copyNumber]

/-- Copy number never exceeds the size of the namespace. -/
theorem copyNumber_le_card (N : Namespace S Channel) (P : S.Term) :
    N.copyNumber (S := S) P ≤ N.channels.card := by
  classical
  unfold copyNumber
  exact Finset.card_filter_le _ _

/-- Copy number is invariant under replacing the target term by a bisimilar one. -/
theorem copyNumber_eq_of_bisimilar (N : Namespace S Channel) {P Q : S.Term}
    (hPQ : S.Bisimilar P Q) :
    N.copyNumber (S := S) P = N.copyNumber (S := S) Q := by
  classical
  unfold copyNumber
  congr
  ext c
  have hiff : S.Bisimilar (N.contents c) P ↔ S.Bisimilar (N.contents c) Q := by
    constructor
    · intro h
      exact S.bisimilar_trans h hPQ
    · intro h
      exact S.bisimilar_trans h (S.bisimilar_symm hPQ)
  simp [hiff]

/-- If every channel in the namespace hosts a bisimilar copy of `P`, then the copy number
    is the full namespace size. -/
theorem copyNumber_eq_card_of_forall (N : Namespace S Channel) (P : S.Term)
    (hfull : ∀ c ∈ N.channels, S.Bisimilar (N.contents c) P) :
    N.copyNumber (S := S) P = N.channels.card := by
  classical
  unfold copyNumber
  rw [Finset.card_filter_eq_iff]
  intro c hc
  exact hfull c hc

end Namespace

/-! ## Summary

This file establishes:

1. **assemblyIndex**: minimum interactive causal depth from elementary terms
2. **assemblyIndex_attained**: the minimum is realized by a concrete path
3. **assemblyIndex_eq_zero_of_mem**: elementary terms have depth zero
4. **Namespace.copyNumber**: finite-region copy counting by bisimilarity
5. **copyNumber_eq_of_bisimilar**: copy number respects the identity criterion of bisimulation

**Paper Coverage**: Definition 23.1; Proposition 23.1; Definitions 23.2–23.4
(generic namespace kernel).

**No sorry statements** — every statement here is proved from the current
interactive-path and bisimilarity infrastructure.
-/

end Mettapedia.GSLT
