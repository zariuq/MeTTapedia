import Mettapedia.Logic.HOL.Embedding.SimpleSliceOfDependent

/-!
# Weak types, predicate guards, and the boundary of simple type theory

Controlled mathematical language often treats a noun or notion as a weak
type.  Semantically, its first-order/HOL reading is a predicate on an ambient
carrier; its type-theoretic reading is the corresponding subtype.  The
translations below prove that existential and guarded-universal statements,
including dependent notions, retain exactly the same truth conditions.

That observation does not make all dependent structure dispensable.
`supportCannotRecoverDistinctEvidence` proves that proposition-valued support
cannot recover which of two evidence objects was supplied, and the existing
simple-slice theorem exhibits a well-formed dependent type outside the image
of Church simple types.  Thus predicates are a sufficient elaboration target
for truth-valued weak notions, while witness-indexed data and transport remain
genuine reasons to use dependent types.

This module specifies the semantic elaboration boundary only.  It does not
define a controlled-language parser or identify proof evidence with truth.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.Embedding.WeakTypeComprehension

open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.Embedding.SimpleSliceOfDependent

universe uCarrier uFibre uEvidence uBase uConst

/-! ## Truth-preserving weak-type reification -/

/-- A weak type is a predicate over an ambient carrier. -/
abbrev Notion (Carrier : Type uCarrier) := Carrier -> Prop

/-- Reify a predicate-valued notion as the subtype of its witnesses. -/
abbrev Realization {Carrier : Type uCarrier} (notion : Notion Carrier) :=
  { value : Carrier // notion value }

/-- Existence in the predicate reading is exactly inhabitation of the
reified weak type. -/
theorem exists_iff_nonempty_realization
    {Carrier : Type uCarrier} (notion : Notion Carrier) :
    (exists value, notion value) <-> Nonempty (Realization notion) := by
  constructor
  · rintro ⟨value, membership⟩
    exact ⟨⟨value, membership⟩⟩
  · rintro ⟨⟨value, membership⟩⟩
    exact ⟨value, membership⟩

/-- A guarded universal in the predicate reading is exactly a universal over
the reified weak type. -/
theorem guardedForall_iff_forall_realization
    {Carrier : Type uCarrier} (notion : Notion Carrier)
    (property : Carrier -> Prop) :
    (forall value, notion value -> property value) <->
      (forall value : Realization notion, property value.1) := by
  constructor
  · intro guarded value
    exact guarded value.1 value.2
  · intro overRealization value membership
    exact overRealization ⟨value, membership⟩

/-- A notion whose ambient carrier depends on a first witness. -/
abbrev DependentNotion {Carrier : Type uCarrier}
    (Fibre : Carrier -> Type uFibre) :=
  forall value, Fibre value -> Prop

/-- Reification of a dependent notion retains both the base witness and the
fibre witness. -/
abbrev DependentRealization
    {Carrier : Type uCarrier} {Fibre : Carrier -> Type uFibre}
    (base : Notion Carrier) (fibre : DependentNotion Fibre) :=
  Sigma fun value : Realization base =>
    { dependentValue : Fibre value.1 // fibre value.1 dependentValue }

/-- Nested guarded existence is exactly inhabitation of the dependent
reification. -/
theorem dependentExists_iff_nonempty_realization
    {Carrier : Type uCarrier} {Fibre : Carrier -> Type uFibre}
    (base : Notion Carrier) (fibre : DependentNotion Fibre) :
    (exists value, base value /\
      exists dependentValue, fibre value dependentValue) <->
      Nonempty (DependentRealization base fibre) := by
  constructor
  · rintro ⟨value, baseMembership, dependentValue, fibreMembership⟩
    exact ⟨⟨⟨value, baseMembership⟩,
      ⟨dependentValue, fibreMembership⟩⟩⟩
  · rintro ⟨⟨⟨value, baseMembership⟩,
      ⟨dependentValue, fibreMembership⟩⟩⟩
    exact ⟨value, baseMembership, dependentValue, fibreMembership⟩

/-- A dependent guarded universal is likewise preserved by reification. -/
theorem dependentGuardedForall_iff_forall_realization
    {Carrier : Type uCarrier} {Fibre : Carrier -> Type uFibre}
    (base : Notion Carrier) (fibre : DependentNotion Fibre)
    (property : forall value, Fibre value -> Prop) :
    (forall value, base value -> forall dependentValue,
      fibre value dependentValue -> property value dependentValue) <->
      (forall witness : DependentRealization base fibre,
        property witness.1.1 witness.2.1) := by
  constructor
  · intro guarded witness
    exact guarded witness.1.1 witness.1.2 witness.2.1 witness.2.2
  · intro overRealization value baseMembership dependentValue fibreMembership
    exact overRealization
      ⟨⟨value, baseMembership⟩, ⟨dependentValue, fibreMembership⟩⟩

/-! ## Why truth-valued weak types do not replace dependent evidence -/

/-- Truncating evidence to proposition-valued inhabitation has no retraction
when the evidence type contains two distinguishable values. -/
theorem supportCannotRecoverDistinctEvidence
    {Evidence : Type uEvidence} (first second : Evidence)
    (distinct : first ≠ second) :
    Not (exists recover : Nonempty Evidence -> Evidence,
      forall evidence, recover ⟨evidence⟩ = evidence) := by
  rintro ⟨recover, recovers⟩
  have supportEqual :
      (⟨first⟩ : Nonempty Evidence) = ⟨second⟩ :=
    Subsingleton.elim _ _
  have evidenceEqual : first = second := by
    calc
      first = recover ⟨first⟩ := (recovers first).symm
      _ = recover ⟨second⟩ := congrArg recover supportEqual
      _ = second := recovers second
  exact distinct evidenceEqual

/-- Minimal negative control: Boolean evidence cannot be reconstructed from
the proposition that some Boolean evidence exists. -/
theorem boolEvidence_not_recoverable :
    Not (exists recover : Nonempty Bool -> Bool,
      forall evidence, recover ⟨evidence⟩ = evidence) :=
  supportCannotRecoverDistinctEvidence false true (by decide)

/-! ## The STT/DTT decision boundary -/

/-- Truth-valued notions translate exactly, while a genuinely varying
dependent type remains outside the simple-type image.  This is the precise
reason to use STT by default and DTT where a consumer needs indexed data. -/
theorem weak_notions_and_genuine_dependency_boundary
    {Carrier : Type uCarrier} (notion : Notion Carrier)
    {Base : Type uBase} {Const : Ty Base -> Type uConst} (base : Base) :
    ((exists value, notion value) <-> Nonempty (Realization notion)) /\
      HasType ([] : List (Expr Base Const)) (dependentType base) Expr.univ /\
      Not (exists simple : Ty Base,
        tyToExpr (Const := Const) simple = dependentType base) := by
  exact ⟨exists_iff_nonempty_realization notion,
    dependentType_formed [] base,
    dependentType_not_image base⟩

/-! ## Axiom audit -/

#print axioms exists_iff_nonempty_realization
#print axioms guardedForall_iff_forall_realization
#print axioms dependentExists_iff_nonempty_realization
#print axioms dependentGuardedForall_iff_forall_realization
#print axioms supportCannotRecoverDistinctEvidence
#print axioms boolEvidence_not_recoverable
#print axioms weak_notions_and_genuine_dependency_boundary

end Mettapedia.Logic.HOL.Embedding.WeakTypeComprehension
