import Mettapedia.Languages.MeTTa.PeTTa.LambdaStaging

/-!
# Sufficient staging depth does not choose different generated code

The depth bound controls finite structural preparation, not evaluator fuel.
Successful preparations agree across bounds and with the total interface.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.LambdaStaging

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open LambdaLifting (Table)
open SpaceSemantics (Program)

theorem ArgumentsRel.mono {first second : Table → Atom → Result → Prop}
    (forward : ∀ table expression result, first table expression result → second table expression result)
    {held : Nat → Bool} {table : Table} {index : Nat} {input : List Atom} {result : Arguments}
    (source : ArgumentsRel first held table index input result) :
    ArgumentsRel second held table index input result := by
  induction source with
  | nil => exact .nil
  | held demand _ ih => exact .held demand ih
  | translated demand edge _ ih => exact .translated demand (forward _ _ _ edge) ih

theorem RowsRel.mono {first second : Table → Atom → Result → Prop}
    (forward : ∀ table expression result, first table expression result → second table expression result)
    {table : Table} {input : List Atom} {result : Arguments} (source : RowsRel first table input result) :
    RowsRel second table input result := by
  induction source with
  | nil => exact .nil
  | raw parts _ ih => exact .raw parts ih
  | pair parts edge _ ih => exact .pair parts (forward _ _ _ edge) ih

theorem Layer.mono {registry : Program} {foreign : Finset String}
    {first second : Table → Atom → Result → Prop}
    (forward : ∀ table expression result, first table expression result → second table expression result)
    {table : Table} {shape : Shape} {result : Result}
    (source : Layer registry foreign first table shape result) :
    Layer registry foreign second table shape result := by
  cases source with
  | value => exact .value
  | quoted => exact .quoted
  | lambda reservation body => exact .lambda reservation (forward _ _ _ body)
  | alternatives entries => exact .alternatives (entries.mono forward)
  | first edge => exact .first (forward _ _ _ edge)
  | binding value continuation => exact .binding (forward _ _ _ value) (forward _ _ _ continuation)
  | bindings rows continuation => exact .bindings (rows.mono forward) (forward _ _ _ continuation)
  | selection key rows => exact .selection (forward _ _ _ key) (rows.mono forward)
  | nullary head emitted => exact .nullary (forward _ _ _ head) emitted
  | application head arguments emitted => exact .application (forward _ _ _ head) (arguments.mono forward) emitted

theorem StageAt.next (registry : Program) (foreign : Finset String) :
    ∀ depth table expression result, StageAt registry foreign depth table expression result →
      StageAt registry foreign (depth + 1) table expression result := by
  intro depth
  induction depth with
  | zero => intro table expression result impossible; exact False.elim impossible
  | succ depth ih =>
      intro table expression result source
      exact Layer.mono ih source

theorem StageAt.mono (registry : Program) (foreign : Finset String)
    {depth upper : Nat} {table : Table} {expression : Atom} {result : Result}
    (source : StageAt registry foreign depth table expression result) (bound : depth ≤ upper) :
    StageAt registry foreign upper table expression result := by
  exact Nat.le_induction source (fun next _ previous => StageAt.next registry foreign next _ _ _ previous)
    upper bound

theorem Staged.functional {registry : Program} {foreign : Finset String}
    {table : Table} {expression : Atom} {first second : Result}
    (left : Staged registry foreign table expression first)
    (right : Staged registry foreign table expression second) : first = second := by
  obtain ⟨leftDepth,leftSource⟩ := left
  obtain ⟨rightDepth,rightSource⟩ := right
  have leftComputed := (prepare_iff registry foreign (max leftDepth rightDepth) table expression first).mpr
    (StageAt.mono registry foreign leftSource (Nat.le_max_left _ _))
  have rightComputed := (prepare_iff registry foreign (max leftDepth rightDepth) table expression second).mpr
    (StageAt.mono registry foreign rightSource (Nat.le_max_right _ _))
  exact Option.some.inj (leftComputed.symm.trans rightComputed)

theorem stage_eq_of_prepared {registry : Program} {foreign : Finset String}
    {depth : Nat} {table : Table} {expression : Atom} {result : Result}
    (computed : prepare registry foreign depth table expression = some result) :
    stage registry foreign table expression = result :=
  Staged.functional (stage_source registry foreign table expression)
    ⟨depth,(prepare_iff registry foreign depth table expression result).mp computed⟩

theorem stage_extension (registry : Program) (foreign : Finset String)
    (table : Table) (expression : Atom) : Extension table (stage registry foreign table expression).table :=
  prepare_extension registry foreign _ table expression _ (stage_computed registry foreign table expression)

end Mettapedia.Languages.MeTTa.PeTTa.LambdaStaging
