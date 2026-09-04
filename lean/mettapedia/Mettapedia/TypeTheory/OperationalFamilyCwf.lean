import Mettapedia.GSLT.Core.ContextualLadderTerminal
import Mettapedia.TypeTheory.OperationalIntensionalExtensionalModes

/-!
# The CwF of operationally indexed families

An operational context is a carrier with an authored one-step relation.  A
dependent type over it assigns a fibre to every state and a transport map to
every primitive step.  No identity or composition law is imposed: those laws
are absent from `DynSys` itself.

This module equips operational systems with a category-with-families
structure.  Comprehension retains both the base step and the equation saying
that its chosen transport reaches the target value.  The construction is the
dependent operational counterpart of `RouteFamilyCwf`; keeping the two
separate makes the extra reflexivity law at the intensional pole visible.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.OperationalFamilyCwf

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.OperationalIntensionalExtensionalModes

universe u

/-! ## Operational substitutions -/

/-- Identity substitution of operational contexts. -/
def dynIdentity (context : DynSys.{u}) : DynHom context context where
  toFun point := point
  map_step step := step

/-- Composition of operational substitutions in execution order. -/
def dynCompose {first middle last : DynSys.{u}}
    (earlier : DynHom first middle) (later : DynHom middle last) :
    DynHom first last where
  toFun point := later.toFun (earlier.toFun point)
  map_step step := later.map_step (earlier.map_step step)

/-! ## Operational dependent types and terms -/

/-- A dependent family over an operational system.  Transport is specified
only for authored primitive steps, with no unearned reflexivity or
composition equations. -/
structure DynFamily (context : DynSys.{u}) : Type (u + 1) where
  fibre : context.carrier -> Type u
  transport : {source target : context.carrier} ->
    context.Step source target -> fibre source -> fibre target

namespace DynFamily

/-- Equality of operational families is determined by fibre and transport. -/
theorem ext {context : DynSys.{u}} {left right : DynFamily context}
    (sameFibre : left.fibre = right.fibre)
    (sameTransport :
      HEq (@DynFamily.transport _ left) (@DynFamily.transport _ right)) :
    left = right := by
  cases left
  cases right
  cases sameFibre
  cases sameTransport
  rfl

/-- Pull an operational family back along a step-preserving substitution. -/
def reindex {source target : DynSys.{u}} (family : DynFamily target)
    (substitution : DynHom source target) : DynFamily source where
  fibre point := family.fibre (substitution.toFun point)
  transport step := family.transport (substitution.map_step step)

@[simp]
theorem reindex_fibre {source target : DynSys.{u}}
    (family : DynFamily target) (substitution : DynHom source target)
    (point : source.carrier) :
    (family.reindex substitution).fibre point =
      family.fibre (substitution.toFun point) :=
  rfl

@[simp]
theorem reindex_transport {source target : DynSys.{u}}
    (family : DynFamily target) (substitution : DynHom source target)
    {first last : source.carrier} (step : source.Step first last)
    (value : family.fibre (substitution.toFun first)) :
    (family.reindex substitution).transport step value =
      family.transport (substitution.map_step step) value :=
  rfl

@[simp]
theorem reindex_identity {context : DynSys.{u}}
    (family : DynFamily context) :
    family.reindex (dynIdentity context) = family :=
  rfl

@[simp]
theorem reindex_composite {first middle last : DynSys.{u}}
    (family : DynFamily last) (earlier : DynHom first middle)
    (later : DynHom middle last) :
    family.reindex (dynCompose earlier later) =
      (family.reindex later).reindex earlier :=
  rfl

/-- A state-insensitive operational family. -/
def constant (context : DynSys.{u}) (valueType : Type u) :
    DynFamily context where
  fibre _ := valueType
  transport _ value := value

@[simp]
theorem constant_reindex {source target : DynSys.{u}}
    (substitution : DynHom source target) (valueType : Type u) :
    (constant target valueType).reindex substitution =
      constant source valueType :=
  rfl

end DynFamily

/-- A term of an operational family is a section natural along every
primitive step. -/
structure DynSection {context : DynSys.{u}}
    (family : DynFamily context) : Type u where
  value : forall point : context.carrier, family.fibre point
  natural : forall {source target : context.carrier}
    (step : context.Step source target),
    family.transport step (value source) = value target

namespace DynSection

/-- Operational sections are determined by their pointwise values. -/
@[ext]
theorem ext {context : DynSys.{u}} {family : DynFamily context}
    {left right : DynSection family}
    (sameValue : left.value = right.value) : left = right := by
  cases left
  cases right
  cases sameValue
  rfl

/-- Reindex a section along an operational substitution. -/
def reindex {source target : DynSys.{u}} {family : DynFamily target}
    (term : DynSection family) (substitution : DynHom source target) :
    DynSection (family.reindex substitution) where
  value point := term.value (substitution.toFun point)
  natural step := term.natural (substitution.map_step step)

@[simp]
theorem reindex_value {source target : DynSys.{u}}
    {family : DynFamily target} (term : DynSection family)
    (substitution : DynHom source target) (point : source.carrier) :
    (term.reindex substitution).value point =
      term.value (substitution.toFun point) :=
  rfl

end DynSection

/-! ## Comprehension -/

/-- Extend an operational context by a dependent family.  A total-state step
retains a base step and the equation witnessing dependent transport. -/
def extend (context : DynSys.{u}) (family : DynFamily context) :
    DynSys.{u} where
  carrier := Sigma family.fibre
  Step source target :=
    Exists fun step : context.Step source.1 target.1 =>
      family.transport step source.2 = target.2

/-- The first projection from operational comprehension. -/
def weaken {context : DynSys.{u}} (family : DynFamily context) :
    DynHom (extend context family) context where
  toFun point := point.1
  map_step step := by
    rcases step with ⟨baseStep, _⟩
    exact baseStep

/-- The final variable in an operational comprehension. -/
def lastVariable {context : DynSys.{u}} (family : DynFamily context) :
    DynSection (family.reindex (weaken family)) where
  value point := point.2
  natural step := by
    rcases step with ⟨_, transported⟩
    exact transported

/-- Pair a substitution and dependent term into a comprehension. -/
def pair {source target : DynSys.{u}}
    (substitution : DynHom source target) (family : DynFamily target)
    (term : DynSection (family.reindex substitution)) :
    DynHom source (extend target family) where
  toFun point := ⟨substitution.toFun point, term.value point⟩
  map_step step :=
    Exists.intro (substitution.map_step step) (term.natural step)

@[simp]
theorem weaken_pair {source target : DynSys.{u}}
    (substitution : DynHom source target) (family : DynFamily target)
    (term : DynSection (family.reindex substitution)) :
    dynCompose (pair substitution family term) (weaken family) =
      substitution := by
  apply DynHom.ext
  intro point
  rfl

/-! ## The operational-family CwF -/

/-- Operational systems, transported families, and step-natural sections
form a category with families. -/
def dynCwf : Cwf.{u + 1, u, u + 1, u} where
  Ctx := DynSys.{u}
  Sub := DynHom
  idS := dynIdentity
  compS later earlier := dynCompose earlier later
  id_comp substitution := by
    apply DynHom.ext
    intro point
    rfl
  comp_id substitution := by
    apply DynHom.ext
    intro point
    rfl
  comp_assoc later middle earlier := by
    apply DynHom.ext
    intro point
    rfl
  Ty := DynFamily
  tySub family substitution := family.reindex substitution
  tySub_id family := DynFamily.reindex_identity family
  tySub_comp family later earlier :=
    DynFamily.reindex_composite family earlier later
  Tm _ family := DynSection family
  tmSub term substitution := term.reindex substitution
  tmSub_id term := by
    apply DynSection.ext
    rfl
  tmSub_comp term later earlier := by
    apply DynSection.ext
    rfl
  ext := extend
  wk family := weaken family
  vz family := lastVariable family
  pair substitution family term := pair substitution family term
  wk_pair substitution family term := weaken_pair substitution family term
  vz_pair substitution family term := by
    apply DynSection.ext
    rfl
  pair_eta family substitution := by
    apply DynHom.ext
    intro point
    apply Sigma.ext rfl
    exact HEq.rfl

/-! ## Terminal operational context -/

/-- The one-state total dynamics is terminal: every authored step has a
unique image. -/
def empty : DynSys.{u} where
  carrier := PUnit
  Step _ _ := True

/-- Every operational context has its unique map to the terminal dynamics. -/
def toEmpty (context : DynSys.{u}) : DynHom context empty where
  toFun _ := PUnit.unit
  map_step _ := trivial

/-- The operational-family CwF with its chosen terminal context. -/
def dynCwfWithTerminal : CwfWithTerminal.{u + 1, u, u + 1, u} where
  toCwf := dynCwf.{u}
  empty := empty.{u}
  toEmpty := toEmpty
  toEmpty_unique := by
    intro context substitution
    apply DynHom.ext
    intro point
    cases substitution.toFun point
    rfl

/-! ## Controls -/

/-- Constant operational families are inhabited by every constant value. -/
def constantSection (context : DynSys.{u}) (valueType : Type u)
    (value : valueType) : DynSection (DynFamily.constant context valueType) where
  value _ := value
  natural _ := rfl

/-- An empty fibre at one state prevents a global operational section. -/
def isolatedPair : DynSys.{0} where
  carrier := Bool
  Step _ _ := False

def emptyAtFalse : DynFamily isolatedPair where
  fibre
    | false => PEmpty
    | true => PUnit
  transport step := step.elim

theorem emptyAtFalse_has_no_section :
    IsEmpty (DynSection emptyAtFalse) := by
  constructor
  intro term
  exact PEmpty.elim (term.value false)

#print axioms dynCwf
#print axioms dynCwfWithTerminal
#print axioms constantSection
#print axioms emptyAtFalse_has_no_section

end Mettapedia.TypeTheory.OperationalFamilyCwf
