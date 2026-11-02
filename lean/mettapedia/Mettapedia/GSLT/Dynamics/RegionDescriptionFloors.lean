import Mettapedia.GSLT.Dynamics.RegionInformationCoding
import Mettapedia.InformationTheory.FiniteDescriptionFloors

/-!
# Description floors for observable region classes

Descriptions recover semantic classes, not necessarily concrete source
states. This charges exactly the distinctions the declared observers can
detect. The worst-case floor reuses the existing string-counting and
Kolmogorov developments. The difficult class may depend on the decoder.

Conditional codes may share words across retained contexts. A code that must
also reconstruct the context pays for the disjoint union instead. Context
storage, decoder construction, query cost, lifetime and revision validation
are not removed by calling the payload sufficient.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.RegionDescriptionFloors

open RegionObservations RegionInformationCoding
open Mettapedia.InformationTheory.FiniteInterfaceCoding
open Mettapedia.InformationTheory.FiniteDescriptionFloors
open Mettapedia.InformationTheory.RelationStoreFloors
open KolmogorovComplexity

universe u v w

theorem some_source_needs_description_floor {State : Type u} [Nonempty State]
    (family : Family.{u, v, w} State) [Finite family.Classes]
    (decoder : List Bool → Option family.Classes) :
    ∃ state, ¬DescribedBelow decoder (Nat.log 2 (Nat.card family.Classes)) (family.classOf state) := by
  let : Nonempty family.Classes := Nonempty.map family.classOf inferInstance
  obtain ⟨cls, hard⟩ := exists_value_needs_floor_log decoder
  induction cls using Quotient.inductionOn with
  | h state => exact ⟨state, hard⟩

/-- The encoding and decoding interface remains explicit. This is a worst
case over source observations, not a bound on every individual program. -/
theorem some_source_needs_program_floor {State : Type u} [Nonempty State]
    (family : Family.{u, v, w} State) [Finite family.Classes]
    (algorithm : Algorithm) (encode : family.Classes → BinString) (decode : BinString → Option family.Classes)
    (roundtrip : ∀ cls, decode (encode cls) = some cls)
    (reachable : ∀ cls, ∃ program, encode cls ∈ algorithm program) :
    ∃ state, Nat.log 2 (Nat.card family.Classes) ≤ C[algorithm](encode (family.classOf state)) := by
  let : Nonempty family.Classes := Nonempty.map family.classOf inferInstance
  obtain ⟨cls, hard⟩ := exists_program_length_floor algorithm encode decode roundtrip reachable
  induction cls using Quotient.inductionOn with
  | h state => exact ⟨state, hard⟩

theorem some_source_has_kolmogorov_floor {State : Type u} [Nonempty State]
    (family : Family.{u, v, w} State) [Finite family.Classes]
    (encode : family.Classes → BinString) (decode : BinString → Option family.Classes)
    (roundtrip : ∀ cls, decode (encode cls) = some cls) :
    ∃ state, Nat.log 2 (Nat.card family.Classes) ≤ K(encode (family.classOf state)) := by
  let : Nonempty family.Classes := Nonempty.map family.classOf inferInstance
  obtain ⟨cls, hard⟩ := exists_kolmogorov_floor encode decode roundtrip
  induction cls using Quotient.inductionOn with
  | h state => exact ⟨state, hard⟩

theorem conditional_budget {Context : Type u} [Fintype Context] {State : Context → Type v}
    (family : (context : Context) → Family.{v, w, w} (State context))
    [∀ context, Finite (family context).Classes] (bits : Nat) :
    Nonempty (FibreCode Context (fun context => (family context).Classes) bits) ↔
      (Finset.univ.sup (fun context => requiredBits (family context))) ≤ bits :=
  minimum_fibre_width bits

theorem context_recovery_budget {Context : Type u} [Fintype Context] {State : Context → Type v}
    (family : (context : Context) → Family.{v, w, w} (State context))
    [∀ context, Finite (family context).Classes] (bits : Nat) :
    Nonempty (Code (Sigma fun context => (family context).Classes) bits) ↔
      (∑ context, Nat.card (family context).Classes) ≤ 2 ^ bits :=
  unframed_code_iff bits

end Mettapedia.GSLT.Dynamics.RegionDescriptionFloors
