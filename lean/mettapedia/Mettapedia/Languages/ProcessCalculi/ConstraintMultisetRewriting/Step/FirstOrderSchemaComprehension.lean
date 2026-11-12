import Mettapedia.TypeTheory.ContextualSchemaTelescopes
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramTranslation

/-!
# First-order schema opening through independent typed holes

The existing row-pattern schema supplies a finite set of local variable
names. Each local receives one independent hole of the row type. Reading
the resulting CwF arguments gives exactly the existing pattern instances;
the scope-tagged first-order substitution is checked against `Pat.at`.

A fallback totalizes values outside the schema's declared support. The
schema's behavior is independent of it. No additional observer or
noninterference claim is made for names outside that support.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrderSchemaComprehension

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualSchemaTelescopes
open ProgramRows

abbrev model := familiesCwf.{0}

/-- First-order local variables are the constant-type case of relative comprehension. -/
abbrev holes : (base : Type) → List Nat → Extension model base
  | base, [] => Extension.nil (C := model) base
  | base, _ :: rest => Extension.cons (C := model) (fun _ => Sx) (holes (Σ _ : base, Sx) rest)

def payload : (names : List Nat) → {base : Type} → (holes base names).target → List (Nat × Sx)
  | [], _, _ => []
  | name :: rest, base, world =>
      (name, ((holes (Σ _ : base, Sx) rest).weaken world).2) :: payload rest world

def supplied : (names : List Nat) → {base source : Type} →
    (baseMap : source → base) → (source → Nat → Sx) → (holes base names).Arguments baseMap
  | [], _, _, _, _ => PUnit.unit
  | name :: rest, _, _, _, values =>
      ⟨(fun point => values point name), supplied rest _ values⟩

theorem payload_assemble : (names : List Nat) → {base source : Type} →
    (baseMap : source → base) → (values : source → Nat → Sx) → (point : source) →
      payload names ((holes base names).assemble baseMap (supplied names baseMap values) point) =
        names.map (fun name => (name, values point name))
  | [], _, _, _, _, _ => rfl
  | name :: rest, base, source, baseMap, values, point => by
      let extended : source → (Σ _ : base, Sx) := fun point => ⟨baseMap point, values point name⟩
      change
        (name, ((holes (Σ _ : base, Sx) rest).weaken
          ((holes (Σ _ : base, Sx) rest).assemble extended
            (supplied rest extended values) point)).2) ::
          payload rest ((holes (Σ _ : base, Sx) rest).assemble extended
            (supplied rest extended values) point) = _
      have old := congrFun ((holes (Σ _ : base, Sx) rest).weaken_assemble
        extended (supplied rest extended values)) point
      change (holes (Σ _ : base, Sx) rest).weaken
        ((holes (Σ _ : base, Sx) rest).assemble extended
          (supplied rest extended values) point) = extended point at old
      rw [old, payload_assemble rest extended values point]
      rfl

def decode {base : Type} (names : List Nat) (fallback : Nat → Sx)
    (world : (holes base names).target) : Nat → Sx :=
  fun name => ((payload names world).lookup name).getD (fallback name)

theorem lookup_supplied (names : List Nat) (values : Nat → Sx) (name : Nat)
    (member : name ∈ names) :
    (names.map (fun key => (key, values key))).lookup name = some (values name) := by
  induction names with
  | nil => cases member
  | cons first rest ih =>
      by_cases same : first = name
      · subst first
        simp
      · have later : name ∈ rest := (List.mem_cons.mp member).resolve_left (Ne.symm same)
        simpa only [List.map_cons, List.lookup_cons,
          beq_eq_false_iff_ne.mpr (Ne.symm same)] using ih later

theorem decode_supplied {base source : Type} (names : List Nat) (fallback : Nat → Sx)
    (baseMap : source → base) (values : source → Nat → Sx) (point : source)
    (name : Nat) (member : name ∈ names) :
    decode names fallback ((holes base names).assemble baseMap (supplied names baseMap values) point)
      name = values point name := by
  unfold decode
  rw [payload_assemble, lookup_supplied names (values point) name member]
  rfl

def patterns (schema : ProgramTranslation.Schema) : List Pat :=
  schema.take ++ schema.read ++ schema.make

def names (schema : ProgramTranslation.Schema) : List Nat :=
  ((patterns schema).flatMap Pat.vars).eraseDups

theorem covered {schema : ProgramTranslation.Schema} {pattern : Pat}
    (present : pattern ∈ patterns schema) {name : Nat} (used : name ∈ pattern.vars) :
    name ∈ names schema := by
  apply List.mem_eraseDups.mpr
  exact List.mem_flatMap.mpr ⟨pattern, present, used⟩

abbrev Arguments (schema : ProgramTranslation.Schema) :=
  (holes Unit (names schema)).Arguments (fun point : Unit => point)

def assignment (schema : ProgramTranslation.Schema) (fallback : Nat → Sx)
    (arguments : Arguments schema) : Nat → Sx :=
  decode (names schema) fallback ((holes Unit (names schema)).assemble (fun point : Unit => point)
    arguments ())

def argumentsOf (schema : ProgramTranslation.Schema) (values : Nat → Sx) : Arguments schema :=
  supplied (names schema) (fun point : Unit => point) (fun _ => values)

theorem instance_eq {schema : ProgramTranslation.Schema} (fallback values : Nat → Sx)
    {pattern : Pat} (present : pattern ∈ patterns schema) :
    pattern.inst (assignment schema fallback (argumentsOf schema values)) = pattern.inst values := by
  apply Pat.inst_congr
  intro name member
  exact decode_supplied (names schema) fallback (fun point : Unit => point)
    (fun _ => values) () name (covered present member)

theorem instances_eq {schema : ProgramTranslation.Schema} (fallback values : Nat → Sx)
    (part : List Pat) (included : ∀ pattern ∈ part, pattern ∈ patterns schema) :
    part.map (Pat.inst (assignment schema fallback (argumentsOf schema values))) =
      part.map (Pat.inst values) := by
  apply List.map_congr_left
  intro pattern member
  exact instance_eq fallback values (included pattern member)

/-- Application stated by the finite typed arguments, including the actual
resource remainder. There is no total assignment among its witnesses. -/
def Fires (fallback : Nat → Sx) (schema : ProgramTranslation.Schema)
    (before after : Multiset Sx) : Prop :=
  ∃ arguments : Arguments schema, ∃ rest : Multiset Sx,
    before = ProgramTranslation.push
      (schema.take.map (Pat.inst (assignment schema fallback arguments)))
      (ProgramTranslation.push
        (schema.read.map (Pat.inst (assignment schema fallback arguments))) rest) ∧
    after = ProgramTranslation.push
      (schema.make.map (Pat.inst (assignment schema fallback arguments)))
      (ProgramTranslation.push
        (schema.read.map (Pat.inst (assignment schema fallback arguments))) rest)

theorem fires_iff (fallback : Nat → Sx) (schema : ProgramTranslation.Schema)
    (before after : Multiset Sx) : Fires fallback schema before after ↔ schema.Fires before after := by
  constructor
  · rintro ⟨arguments, rest, source, target⟩
    exact ⟨assignment schema fallback arguments, rest, source, target⟩
  · rintro ⟨values, rest, source, target⟩
    have takes := instances_eq (schema := schema) fallback values schema.take
      (fun pattern member => by simp [patterns, member])
    have reads := instances_eq (schema := schema) fallback values schema.read
      (fun pattern member => by simp [patterns, member])
    have makes := instances_eq (schema := schema) fallback values schema.make
      (fun pattern member => by simp [patterns, member])
    exact ⟨argumentsOf schema values, rest,
      by simpa only [takes, reads] using source,
      by simpa only [makes, reads] using target⟩

theorem fires_fallback_independent (first second : Nat → Sx)
    (schema : ProgramTranslation.Schema) (before after : Multiset Sx) :
    Fires first schema before after ↔ Fires second schema before after :=
  (fires_iff first schema before after).trans (fires_iff second schema before after).symm

/-- Instantiate precisely the schema's supported names in the selected fresh
scope, leaving every other substitution entry as supplied by the caller. -/
def instantiateScope (schema : ProgramTranslation.Schema) (scope : Nat)
    (previous : Mettapedia.Logic.LP.Subst rows) (fallback : Nat → Sx)
    (arguments : Arguments schema) : Mettapedia.Logic.LP.Subst rows :=
  fun key => if key.1 = scope ∧ key.2 ∈ names schema
    then embed (assignment schema fallback arguments key.2) else previous key

theorem scoped_instance {schema : ProgramTranslation.Schema} (scope : Nat)
    (previous : Mettapedia.Logic.LP.Subst rows) (fallback : Nat → Sx)
    (arguments : Arguments schema) {pattern : Pat} (present : pattern ∈ patterns schema) :
    (instantiateScope schema scope previous fallback arguments).applyTerm (pattern.at scope) =
      embed (pattern.inst (assignment schema fallback arguments)) := by
  apply apply_at
  intro name used
  simp [instantiateScope, covered present used]

theorem scoped_preserves_older (schema : ProgramTranslation.Schema) (scope : Nat)
    (previous : Mettapedia.Logic.LP.Subst rows) (fallback : Nat → Sx)
    (arguments : Arguments schema) (term : Tm) (older : Bounded scope term) :
    (instantiateScope schema scope previous fallback arguments).applyTerm term = previous.applyTerm term := by
  apply apply_bounded older
  intro key below
  simp [instantiateScope, Nat.ne_of_lt below]

/-- Recovery of the existing admitted firing and its interpreted result.
The old profile's coverage and single-read hypotheses remain explicit. -/
theorem firing_sound {state : ProgramTranslation.Config} {before after : Multiset Sx}
    {scope : Nat} {schema : ProgramTranslation.Schema} (fallback : Nat → Sx)
    (formed : schema.WellFormed) (rep : ProgramTranslation.Represents state before scope)
    (fires : Fires fallback schema before after) :
    ∃ taken read : List ProgramTranslation.Occ,
      (schema.firing scope taken read).Valid ProgramTranslation.A ProgramTranslation.Occ.label state ∧
      ProgramTranslation.Represents
        ((schema.firing scope taken read).result ProgramTranslation.Occ.label state) after (scope + 1) :=
  ProgramTranslation.sound formed rep ((fires_iff fallback schema before after).mp fires)

theorem firing_complete {state : ProgramTranslation.Config} {before : Multiset Sx}
    {scope : Nat} {schema : ProgramTranslation.Schema} (fallback : Nat → Sx)
    (formed : schema.WellFormed) (rep : ProgramTranslation.Represents state before scope)
    {taken read : List ProgramTranslation.Occ}
    (admitted : (schema.firing scope taken read).Valid
      ProgramTranslation.A ProgramTranslation.Occ.label state) :
    ∃ after, Fires fallback schema before after ∧
      ProgramTranslation.Represents
        ((schema.firing scope taken read).result ProgramTranslation.Occ.label state) after (scope + 1) := by
  obtain ⟨after, fires, result⟩ := ProgramTranslation.complete formed rep admitted
  exact ⟨after, (fires_iff fallback schema before after).mpr fires, result⟩

def Rewrites {Index : Type*} (schemas : Index → ProgramTranslation.Schema)
    (fallback : Nat → Sx) (before after : Multiset Sx) : Prop :=
  ∃ index, Fires fallback (schemas index) before after

theorem rewrites_eq {Index : Type*} (schemas : Index → ProgramTranslation.Schema)
    (fallback : Nat → Sx) : Rewrites schemas fallback = ProgramTranslation.Rewrites schemas := by
  funext before after
  apply propext
  simp only [Rewrites, ProgramTranslation.Rewrites, fires_iff]

/-- Finite executions through the original first-order compiler, with the
same initial configuration, translated firings and final row multiset. -/
theorem execution_iff {Index : Type*} (schemas : Index → ProgramTranslation.Schema)
    (fallback : Nat → Sx) (formed : ∀ index, (schemas index).WellFormed)
    (initial : List Sx) (final : Multiset Sx) :
    Relation.ReflTransGen (Rewrites schemas fallback) (initial : Multiset Sx) final ↔
      ∃ target : ProgramTranslation.Config × Nat,
        Relation.ReflTransGen (ProgramTranslation.Translated schemas)
          (ProgramTranslation.initial initial, 1) target ∧
        ProgramTranslation.Represents target.1 final target.2 := by
  rw [rewrites_eq]
  exact ProgramTranslation.execution_iff formed initial final

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrderSchemaComprehension
