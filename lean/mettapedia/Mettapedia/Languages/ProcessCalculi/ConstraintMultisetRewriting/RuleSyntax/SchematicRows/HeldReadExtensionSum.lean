import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Core

/-!
# An explicit identity branch for internal read-protocol steps

Old extensions and firings embed without changing their information,
freshness, admission or result. The additional branch is a real capability,
not a new default. A protected protocol must reserve it for its internal
phase; no equivalence of unrestricted old and extended programs is claimed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadExtensionSum

open Interface (Frames)

universe uO uT uH uE uOcc
variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  (X : Frames Tm Hom) (E : Extensions.{uO, uH, uE} Hom)

def withIdentity : Extensions.{uO, uH, uE} Hom where
  Ext a := E.Ext a ⊕ PUnit.{1}
  target {a} extension := match extension with
    | .inl original => E.target original
    | .inr _ => a
  weaken {a} extension := match extension with
    | .inl original => E.weaken original
    | .inr _ => X.id a

variable {O : Type uOcc} {P : RuleSyntax.Program Tm} {a : Obj}

def lift (firing : RuleSyntax.Firing O E P a) :
    RuleSyntax.Firing O (withIdentity X E) P a :=
  ⟨firing.rule, firing.member, .inl firing.ext, firing.opening, firing.selection, firing.seen⟩

theorem lift_information (source : RuleSyntax.State Tm O)
    (firing : RuleSyntax.Firing O E P source.frame) :
    (lift X E firing).information X source = firing.information X source := rfl

theorem lift_fresh_iff (source : RuleSyntax.State Tm O)
    (firing : RuleSyntax.Firing O E P source.frame) :
    (lift X E firing).Fresh X source ↔ firing.Fresh X source := Iff.rfl

theorem lift_shapes_iff (source : RuleSyntax.State Tm O)
    (firing : RuleSyntax.Firing O E P source.frame) :
    (lift X E firing).Shapes X source ↔ firing.Shapes X source := Iff.rfl

variable [DecidableEq O]

theorem lift_admission_iff (source : RuleSyntax.State Tm O)
    (firing : RuleSyntax.Firing O E P source.frame) :
    (lift X E firing).Admits X source ↔ firing.Admits X source := Iff.rfl

theorem lift_result (source : RuleSyntax.State Tm O)
    (firing : RuleSyntax.Firing O E P source.frame) :
    (lift X E firing).result X source = firing.result X source := rfl

omit [DecidableEq O] in
theorem internal_target (frame : Obj) :
    (withIdentity X E).target (a := frame) (.inr PUnit.unit) = frame := rfl

omit [DecidableEq O] in
theorem internal_weakening (frame : Obj) :
    (withIdentity X E).weaken (a := frame) (.inr PUnit.unit) = X.id frame := rfl

omit [DecidableEq O] in
theorem branches_distinct (frame : Obj) (extension : E.Ext frame) :
    (Sum.inl extension : (withIdentity X E).Ext frame) ≠ .inr PUnit.unit := by
  intro impossible
  cases impossible

/-- The added branch really adds a capability even if the original family
offers none. It is not an identity-only implementation pretending to be a sum. -/
def emptyExtensions : Extensions.{uO, uH, 0} Hom where
  Ext _ := Empty
  target extension := nomatch extension
  weaken extension := nomatch extension

omit [DecidableEq O] in
theorem identity_adds_capability (frame : Obj) :
    Nonempty ((withIdentity X (emptyExtensions (Hom := Hom))).Ext frame) ∧
      ¬ Nonempty ((emptyExtensions (Hom := Hom)).Ext frame) := by
  refine ⟨⟨.inr PUnit.unit⟩, ?_⟩
  rintro ⟨impossible⟩
  cases impossible

#print axioms lift_information
#print axioms lift_fresh_iff
#print axioms lift_admission_iff
#print axioms lift_result
#print axioms branches_distinct
#print axioms identity_adds_capability

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadExtensionSum
