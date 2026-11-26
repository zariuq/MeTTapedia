import Lean

/-!
# Quotient primitives in the Type-carrier interpretation

The set-class interpretation covers successor-universe instances of the
kernel quotient primitives. Prop carriers and unconstrained Sort parameters
need a different proof-irrelevant representation and are refused here.
The profile is checked before a term reader drops universe instantiations.

A reading of syntax alone, Lean back to Lean, interprets nothing: it reads
every instance and records, with `outside`, the instances a set reading of the
same data must refuse.
-/

namespace Mettapedia.Languages.Lean.Declarations.QuotientProfile

open _root_.Lean Meta

def kind? (name : Name) : MetaM (Option String) := do
  match (← getConstInfo name) with
  | .quotInfo value =>
      return match value.kind with
      | .type => some "type"
      | .ctor => some "constructor"
      | .lift => some "lift"
      | .ind => none
  | _ => return none

def usesTypeProfile (name : Name) : MetaM Bool := do
  return name == ``Quot.liftOn || (← kind? name).isSome

def refusal? (name : Name) (levels : List Level) : MetaM (Option String) := do
  unless ← usesTypeProfile name do return none
  let expected := (← getConstInfo name).levelParams.length
  if levels.length != expected then
    return some s!"quotient universe interface changed for {name}"
  for level in levels do
    match level.normalize with
    | .succ _ => pure ()
    | _ => return some s!"{name}: only Type-carrier/result quotient instances are interpreted; level {level} is not a successor"
  return none

/-- `Quot.sound` at levels outside the profile: its carrier is not in `Type`. -/
def soundRefusal? (levels : List Level) : MetaM (Option String) := do
  for level in levels do
    unless level.normalize matches .succ _ do
      return some s!"Quot.sound at level {level}, which is not a successor"
  return none

/-- What the profile refuses in an expression, each reason once: the instances of the quotient
primitives, and of `Quot.sound`, at levels a set reading does not interpret. -/
def outside (e : Expr) : MetaM (Array String) := do
  let found ← IO.mkRef (#[] : Array String)
  forEachExpr e fun s => do
    let .const c us := s | return
    let reason? ← if c == ``Quot.sound then soundRefusal? us else refusal? c us
    if let some reason := reason? then
      found.modify fun rs => if rs.contains reason then rs else rs.push reason
  found.get

/-- Specialize an actual declaration's universe parameters to Type levels.
The original declaration identity is retained; this is a restricted profile,
not a claim about all Sort-polymorphic instances. -/
def typeInstance (declaration : Name) : MetaM (Expr × List Level) := do
  let info ← getConstInfo declaration
  let levels := info.levelParams.map (fun parameter => Level.succ (.param parameter))
  return (info.type.instantiateLevelParams info.levelParams levels, levels)

/-- The kernel reduction rule at the admitted universe profile. -/
theorem lift_beta {α : Type u} {β : Type v} (relation : α → α → Prop)
    (function : α → β) (respect : ∀ a b, relation a b → function a = function b) (a : α) :
    Quot.lift function respect (Quot.mk relation a) = function a := rfl

end Mettapedia.Languages.Lean.Declarations.QuotientProfile
