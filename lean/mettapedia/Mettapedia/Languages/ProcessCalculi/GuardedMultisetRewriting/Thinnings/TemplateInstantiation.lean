import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.Operations
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.Patterns

/-!
# One shared template traversal with a qualified variable resolver

Structural and contextual instantiation use the same constructor traversal.
The resolver may extend the canonical store, but its value must be stable
under extension of the original store. Plain substitution and contextual
grafting discharge this primitive contract independently.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings

open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources

variable {Head V : Type} [DecidableEq Head]

abbrev VariableResolver (Head V : Type) := V → Store Head → Store Head × Option Ref

def ResolverCorrect (base : Store Head) (resolve : VariableResolver Head V) (values : Subst V (Term Head)) : Prop :=
  ∀ store, base <+: store → Canonical store → ∀ variableName,
    store <+: (resolve variableName store).1 ∧ Canonical (resolve variableName store).1 ∧
      (∀ result, (resolve variableName store).2 = some result → CanonRef (resolve variableName store).1 result) ∧
      (resolve variableName store).2.map (unfold (resolve variableName store).1) = values variableName

mutual
def instantiateByR (resolve : VariableResolver Head V) : TreePat Head V → Store Head → Store Head × Option Ref
  | .mvar variableName, store => resolve variableName store
  | .idx index, store =>
      let result := encodeR store (.idx index)
      (result.1, some result.2)
  | .node head fields, store =>
      match instantiateFieldsByR resolve fields store with
      | (larger, none) => (larger, none)
      | (larger, some children) =>
          let result := mkNode larger head children
          (result.1, some result.2)

def instantiateFieldsByR (resolve : VariableResolver Head V) :
    TreePatFields Head V → Store Head → Store Head × Option (List (Nat × Ref))
  | .nil, store => (store, some [])
  | .cons depth pattern rest, store =>
      match instantiateByR resolve pattern store with
      | (larger, none) => (larger, none)
      | (larger, some result) =>
          match instantiateFieldsByR resolve rest larger with
          | (finalStore, none) => (finalStore, none)
          | (finalStore, some children) => (finalStore, some ((depth, result) :: children))
end

mutual
theorem instantiateByR_spec (base : Store Head) (resolve : VariableResolver Head V)
    (values : Subst V (Term Head)) (correct : ResolverCorrect base resolve values)
    (pattern : TreePat Head V) (store : Store Head) (grows : base <+: store) (canonical : Canonical store) :
    store <+: (instantiateByR resolve pattern store).1 ∧ Canonical (instantiateByR resolve pattern store).1 ∧
      (∀ result, (instantiateByR resolve pattern store).2 = some result →
        CanonRef (instantiateByR resolve pattern store).1 result) ∧
      (instantiateByR resolve pattern store).2.map (unfold (instantiateByR resolve pattern store).1) =
        pattern.inst values := by
  cases pattern with
  | mvar variableName => exact correct store grows canonical variableName
  | idx index =>
    obtain ⟨more, nextCanonical, valid, _⟩ := encodeR_spec store canonical (.idx index)
    refine ⟨more, nextCanonical, ?_, ?_⟩
    · intro result assigned
      have same : (encodeR store (.idx index)).2 = result := Option.some.inj assigned
      simpa only [instantiateByR, same] using valid
    · simpa [instantiateByR, TreePat.inst] using congrArg some (encodeR_unfold canonical (.idx index))
  | node head fields =>
    obtain ⟨more, nextCanonical, children, semantic⟩ :=
      instantiateFieldsByR_spec base resolve values correct fields store grows canonical
    simp only [instantiateByR]
    generalize instantiateFieldsByR resolve fields store = result at more nextCanonical children semantic ⊢
    obtain ⟨nextStore, result⟩ := result
    dsimp only at more nextCanonical children semantic ⊢
    cases result with
    | none =>
      refine ⟨more, nextCanonical, ?_, ?_⟩
      · intro output impossible; cases impossible
      · simp [TreePat.inst, ← semantic]
    | some refs =>
      obtain ⟨last, finalCanonical, valid, _⟩ := mkNode_spec nextCanonical head (children refs rfl)
      refine ⟨more.trans last, finalCanonical, ?_, ?_⟩
      · intro output assigned
        cases assigned
        exact valid
      · simp [TreePat.inst, ← semantic, mkNode_unfold nextCanonical head (children refs rfl)]

theorem instantiateFieldsByR_spec (base : Store Head) (resolve : VariableResolver Head V)
    (values : Subst V (Term Head)) (correct : ResolverCorrect base resolve values)
    (fields : TreePatFields Head V) (store : Store Head) (grows : base <+: store) (canonical : Canonical store) :
    store <+: (instantiateFieldsByR resolve fields store).1 ∧ Canonical (instantiateFieldsByR resolve fields store).1 ∧
      (∀ results, (instantiateFieldsByR resolve fields store).2 = some results →
        ∀ child ∈ results, CanonRef (instantiateFieldsByR resolve fields store).1 child.2) ∧
      (instantiateFieldsByR resolve fields store).2.map (fieldsOfRefs (instantiateFieldsByR resolve fields store).1) =
        fields.inst values := by
  cases fields with
  | nil =>
    refine ⟨List.prefix_refl _, canonical, ?_, rfl⟩
    intro results assigned
    cases assigned
    simp
  | cons depth pattern rest =>
    obtain ⟨more, nextCanonical, headValid, headTree⟩ :=
      instantiateByR_spec base resolve values correct pattern store grows canonical
    simp only [instantiateFieldsByR]
    generalize instantiateByR resolve pattern store = first at more nextCanonical headValid headTree ⊢
    obtain ⟨nextStore, first⟩ := first
    dsimp only at more nextCanonical headValid headTree ⊢
    cases first with
    | none =>
      refine ⟨more, nextCanonical, ?_, ?_⟩
      · intro results impossible; cases impossible
      · simp [TreePatFields.inst, ← headTree]
    | some result =>
      dsimp only
      obtain ⟨last, finalCanonical, tailValid, tailTree⟩ :=
        instantiateFieldsByR_spec base resolve values correct rest nextStore (grows.trans more) nextCanonical
      generalize instantiateFieldsByR resolve rest nextStore = tail at last finalCanonical tailValid tailTree ⊢
      obtain ⟨finalStore, tail⟩ := tail
      dsimp only at last finalCanonical tailValid tailTree ⊢
      cases tail with
      | none =>
        refine ⟨more.trans last, finalCanonical, ?_, ?_⟩
        · intro results impossible; cases impossible
        · simp [TreePatFields.inst, ← headTree, ← tailTree]
      | some children =>
        refine ⟨more.trans last, finalCanonical, ?_, ?_⟩
        · intro results assigned
          cases assigned
          intro child member
          rcases List.mem_cons.mp member with rfl | member
          · exact (headValid result rfl).prefix last
          · exact tailValid children rfl child member
        · simp only [Option.map_some, TreePatFields.inst, ← headTree, ← tailTree, fieldsOfRefs,
            unfold_prefix nextCanonical.topo last (headValid result rfl).valid]
end

end Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings
