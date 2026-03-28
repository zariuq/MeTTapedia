import Mettapedia.GSLT.Core.GSLT

/-!
# Minimal Context Interface

This file isolates the context machinery behind Meredith's Definition 5.1.

For an abstract `GSLT`, we cannot derive syntactic one-hole contexts or prove
Milner-Sewell-Leifer minimality generically.  Instead, we separate:

* raw context *shapes* `GSLTContext`,
* a `HasMinimalContexts` interface providing the admissible minimal contexts,
* the subtype `MinimalContext` of context shapes certified minimal by that
  interface.

This is stricter and more faithful than treating all endofunctions
`Term → Term` as legitimate modal labels.
-/

namespace Mettapedia.GSLT

/-- A raw context shape for a GSLT: a surrounding term with one distinguished
hole abstracted as a plug operation.

This does **not** by itself assert Milner-Leifer minimality.  That certification
is carried separately by `HasMinimalContexts`.
-/
structure GSLTContext (S : GSLT) where
  /-- Apply the context to a term: `K[P]`. -/
  plug : S.Term → S.Term

namespace GSLTContext

variable {S : GSLT}

/-- The empty context `[−]`. -/
def id : GSLTContext S where
  plug := _root_.id

/-- Composition of context shapes: `K₁[K₂[−]]`. -/
def comp (K₁ K₂ : GSLTContext S) : GSLTContext S where
  plug := K₁.plug ∘ K₂.plug

@[simp] theorem id_plug (t : S.Term) : (id (S := S)).plug t = t := rfl
@[simp] theorem comp_plug (K₁ K₂ : GSLTContext S) (t : S.Term) :
    (comp K₁ K₂).plug t = K₁.plug (K₂.plug t) := rfl

end GSLTContext

/-- Abstract interface for the minimal reactive contexts used in Meredith's
Milner-Sewell-Leifer layer.

An instance packages which context shapes count as:

* one-hole contexts,
* reactive contexts,
* minimal contexts.

The interface remains intentionally abstract at the generic `GSLT` level; the
concrete proof obligations belong to instances such as rho-calculus or other
operational theories.
-/
class HasMinimalContexts (S : GSLT) where
  /-- Well-formed one-hole context shapes. -/
  IsOneHole : GSLTContext S → Prop
  /-- Context shapes that can participate in the reactive LTS. -/
  IsReactive : GSLTContext S → Prop
  /-- Minimal reactive contexts. -/
  IsMinimal : GSLTContext S → Prop
  /-- The empty context is a legitimate one-hole context. -/
  id_oneHole : IsOneHole (GSLTContext.id (S := S))
  /-- The empty context is reactive. -/
  id_reactive : IsReactive (GSLTContext.id (S := S))
  /-- The empty context is minimal. -/
  id_minimal : IsMinimal (GSLTContext.id (S := S))
  /-- Every minimal context is reactive. -/
  minimal_reactive : ∀ {K : GSLTContext S}, IsMinimal K → IsReactive K
  /-- Every minimal context is a well-formed one-hole context. -/
  minimal_oneHole : ∀ {K : GSLTContext S}, IsMinimal K → IsOneHole K

/-- The subtype of context shapes certified minimal by the chosen MSL interface. -/
abbrev MinimalContext (S : GSLT) [HasMinimalContexts S] :=
  { K : GSLTContext S // HasMinimalContexts.IsMinimal K }

namespace MinimalContext

variable {S : GSLT} [HasMinimalContexts S]

instance : CoeOut (MinimalContext S) (GSLTContext S) := ⟨Subtype.val⟩

/-- Plug a term into a minimal context. -/
def plug (K : MinimalContext S) (t : S.Term) : S.Term :=
  K.1.plug t

/-- The empty minimal context. -/
def id : MinimalContext S :=
  ⟨GSLTContext.id (S := S), HasMinimalContexts.id_minimal (S := S)⟩

theorem reactive (K : MinimalContext S) : HasMinimalContexts.IsReactive K.1 :=
  HasMinimalContexts.minimal_reactive K.2

theorem oneHole (K : MinimalContext S) : HasMinimalContexts.IsOneHole K.1 :=
  HasMinimalContexts.minimal_oneHole K.2

@[simp] theorem id_plug (t : S.Term) : (id (S := S)).plug t = t := rfl

end MinimalContext

end Mettapedia.GSLT
