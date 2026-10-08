import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualRealizedGraphs

/-!
# Unfolding and finality of the constructed indexed matching limit

The actual coherent finite-tree limit has inverse unfolding and rolling
maps. Coiteration satisfies the coalgebra equation, and every morphism
into this limit agrees with the constructed coiteration at every depth.
This is finality for the stated small indexed polynomial, not for an
unrestricted powerclass of all material values.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphRealizers.IndexedLimit

universe u v w
variable {Index : Type u} {Shape : Index → Type u}
variable {Position : (index : Index) → Shape index → Type u}
variable {next : (index : Index) → (shape : Shape index) → Position index shape → Index}

namespace Realizer

theorem ext {index : Index} {first second : Realizer Shape Position next index}
    (same : ∀ depth, first.approx depth = second.approx depth) : first = second := by
  cases first
  cases second
  congr
  funext depth
  exact same depth

theorem out_roll {index : Index}
    (layer : Layer Shape Position next (Realizer Shape Position next) index) :
    (roll layer).out = layer := by
  apply Sigma.ext rfl
  apply heq_of_eq
  funext position
  apply ext
  intro depth
  rfl

theorem roll_out {index : Index} (proof : Realizer Shape Position next index) :
    roll proof.out = proof := by
  apply ext
  intro depth
  cases depth with
  | zero => exact proof.coherent 0
  | succ depth =>
    exact GraphBisimulationRealizers.FixedIndexLimit.reconstruct
      (fun depth shape => (position : Position index shape) →
        Approx Shape Position next depth (next index shape position))
      (fun depth shape value position => truncate Shape Position next depth _ (value position))
      proof.values proof.values_coherent depth

def unfolding (index : Index) :
    Realizer Shape Position next index ≃
      Layer Shape Position next (Realizer Shape Position next) index where
  toFun := out
  invFun := roll
  left_inv := roll_out
  right_inv := out_roll

theorem out_corec {witness : Index → Type v}
    (step : ∀ index, witness index → Layer Shape Position next witness index)
    {index : Index} (proof : witness index) :
    (corec Shape Position next step proof).out =
      map Shape Position next (fun _ value => corec Shape Position next step value)
        (step index proof) := by
  apply Sigma.ext rfl
  apply heq_of_eq
  funext position
  apply ext
  intro depth
  rfl

end Realizer

/-- A coalgebra morphism into the constructed matching limit is determined
by the supplied coalgebra, not by a selected infinite branch. -/
theorem corec_unique {witness : Index → Type v}
    (step : ∀ index, witness index → Layer Shape Position next witness index)
    (morphism : ∀ index, witness index → Realizer Shape Position next index)
    (commutes : ∀ index value, (morphism index value).out =
      map Shape Position next morphism (step index value)) :
    ∀ index value, morphism index value = corec Shape Position next step value := by
  have approximations : ∀ depth index value,
      (morphism index value).approx depth = iterate Shape Position next step depth index value := by
    intro depth
    induction depth with
    | zero =>
        intro index value
        change (_ : PUnit) = _
        exact Subsingleton.elim _ _
    | succ depth induction =>
        intro index value
        have unfolded := congrArg Realizer.roll (commutes index value)
        rw [Realizer.roll_out] at unfolded
        rw [unfolded]
        change map Shape Position next (fun _ value => value.approx depth)
          (map Shape Position next morphism (step index value)) = _
        rw [map_composition]
        exact map_congr Shape Position next (fun index value => induction index value) _
  intro index value
  exact Realizer.ext (fun depth => approximations depth index value)

namespace Controls

abbrev BitShape (_ : PUnit) := Bool
abbrev BitPosition (_ : PUnit) (_ : Bool) := PUnit
def bitNext (_ : PUnit) (_ : Bool) (_ : PUnit) : PUnit := PUnit.unit
abbrev BitLimit := Realizer BitShape BitPosition bitNext PUnit.unit

def bitStep (bits : Nat → Bool) (_ : PUnit) (stage : Nat) :
    Layer BitShape BitPosition bitNext (fun _ => Nat) PUnit.unit :=
  ⟨bits stage, fun _ => stage+1⟩

def stream (bits : Nat → Bool) (stage : Nat) : BitLimit :=
  corec BitShape BitPosition bitNext (bitStep bits) (index := PUnit.unit) stage

def head (value : BitLimit) : Bool := value.out.1
def tail (value : BitLimit) : BitLimit := value.out.2 PUnit.unit

theorem stream_head (bits : Nat → Bool) (stage : Nat) :
    head (stream bits stage) = bits stage := rfl

theorem stream_tail (bits : Nat → Bool) (stage : Nat) :
    tail (stream bits stage) = stream bits (stage+1) := by
  unfold tail stream
  rw [Realizer.out_corec]
  rfl

theorem stream_unique (bits : Nat → Bool)
    (candidate : Nat → BitLimit)
    (commutes : ∀ stage, (candidate stage).out =
      ⟨bits stage, fun _ => candidate (stage+1)⟩) :
    ∀ stage, candidate stage = stream bits stage :=
  fun stage => corec_unique (bitStep bits) (fun _ => candidate)
    (fun _ value => commutes value) PUnit.unit stage

def pulse (bound : Nat) (stage : Nat) : Bool := decide (stage = bound+1)

/-- No finite window of head readings determines the infinite recipient. -/
theorem bounded_heads_agree (bound stage : Nat) (visible : stage ≤ bound) :
    head (stream (pulse bound) stage) = head (stream (fun _ => false) stage) := by
  simp only [stream_head, pulse, decide_eq_false_iff_not]
  omega

theorem later_heads_differ (bound : Nat) :
    head (stream (pulse bound) (bound+1)) ≠ head (stream (fun _ => false) (bound+1)) := by
  simp [stream_head, pulse]

theorem current_head_does_not_determine_tail :
    head (stream (pulse 0) 0) = head (stream (fun _ => false) 0) ∧
      tail (stream (pulse 0) 0) ≠ tail (stream (fun _ => false) 0) := by
  refine ⟨bounded_heads_agree 0 0 (Nat.le_refl 0), ?_⟩
  rw [stream_tail, stream_tail]
  intro same
  exact later_heads_differ 0 (congrArg head same)

end Controls

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphRealizers.IndexedLimit
