import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMatchingFinality

/-!
# Explicit context restriction of full matching evidence

One-step restriction composes the actual future arrows and retains the
complete continuation evidence. Its unfolding equation uses the constructed
indexed matching finality equations.
These operations concern proof-relevant graph strategies, not native Id.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphRealizers

open CategoryTheory ContextualGraphDiagrams
universe u
variable {D : Type u} [Category.{u} D] {left right : Diagram D}

namespace Realizer

def restrictedLayer {origin point : D} {first : left.nodes.obj origin}
    {second : right.nodes.obj origin} (arrival : origin ⟶ point)
    (proof : Realizer left right origin first second) :
    Layer left right (fun index => Realizer left right index.1 index.2.1 index.2.2)
      point (left.nodes.map arrival first) (right.nodes.map arrival second) :=
  ⟨fun future =>
    ⟨fun child => (futureForth arrival proof future child).1,
      fun child => (futureBack arrival proof future child).1⟩,
    fun ⟨future, position⟩ => match position with
      | .inl child => (futureForth arrival proof future child).2
      | .inr child => (futureBack arrival proof future child).2⟩

def restrictDirect {origin point : D} {first : left.nodes.obj origin}
    {second : right.nodes.obj origin} (arrival : origin ⟶ point)
    (proof : Realizer left right origin first second) :
    Realizer left right point (left.nodes.map arrival first) (right.nodes.map arrival second) :=
  IndexedLimit.Realizer.roll (restrictedLayer arrival proof)

theorem out_restrictDirect {origin point : D} {first : left.nodes.obj origin}
    {second : right.nodes.obj origin} (arrival : origin ⟶ point)
    (proof : Realizer left right origin first second) :
    IndexedLimit.Realizer.out (restrictDirect arrival proof) = restrictedLayer arrival proof :=
  IndexedLimit.Realizer.out_roll _

end Realizer

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphRealizers
