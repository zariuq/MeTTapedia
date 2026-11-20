import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.Rule
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Bags

/-!
# Independently opened rows at each selected position

The selected occurrence is physical; its row-local opening belongs to the
pattern position. Two reads of one schematic occurrence may consequently use
different fresh instances. Shared rows have no local opening.

Joint freshness is the existing `JointFirings.Bag.Fresh` over a scope probe. Its
members expose the user rule and all selected schema terms consistently. The
scope bag is not an executed batch, and its universal indexing program is not
the user's program or an admission predicate.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows

open Interface (Frames)

universe uO uT uH uE uOcc
variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}

namespace Row

def interfaceSize {a : Obj} : Row Tm a → Nat × Nat
  | .shared _ => (0, 0)
  | .schematic closure => (closure.schema.params.length, closure.args.length)

def WellFormed {a : Obj} (row : Row Tm a) : Prop := row.interfaceSize.1 = row.interfaceSize.2

end Row

inductive RowUse (Tm : Obj → Type uT) (Hom : Obj → Obj → Type uH) (target : Obj) {a : Obj} :
    Row Tm a → Type (max uO uT uH) where
  | shared (term : Tm a) : RowUse Tm Hom target (.shared term)
  | schematic (row : Closure Tm a) (opening : Hom row.schema.locals target) :
      RowUse Tm Hom target (.schematic row)

namespace RowUse

variable {a target : Obj}

def value (X : Frames Tm Hom) (weaken : Hom a target) {row : Row Tm a} : RowUse Tm Hom target row → Tm target
  | .shared term => X.act weaken term
  | .schematic closure opening => X.act opening closure.schema.value

def information (X : Frames Tm Hom) (weaken : Hom a target) {row : Row Tm a} :
    RowUse Tm Hom target row → EquationStore (Tm target)
  | .shared _ => []
  | .schematic closure opening =>
      X.applyStore opening closure.schema.knowledge ++
        (closure.schema.params.map (X.act opening)).zip (closure.args.map (X.act weaken))

def scopeRule {a : Obj} (row : Closure Tm a) : RuleSyntax.Rule Tm :=
  ⟨row.schema.locals, ⟨[], [], row.schema.knowledge, [], row.schema.value :: row.schema.params⟩, []⟩

def scopeMember (E : Extensions.{uO, uH, uE} Hom) (ext : E.Ext a) {row : Row Tm a} :
    RowUse Tm Hom (E.target ext) row →
      Option (JointFirings.Member (Tm a) E (Set.univ : RuleSyntax.Program Tm) ext)
  | .shared _ => none
  | .schematic closure opening =>
      some ⟨scopeRule closure, Set.mem_univ _, opening, ⟨[], [], []⟩, []⟩

theorem value_shared (X : Frames Tm Hom) (weaken : Hom a target) (term : Tm a)
    (use : RowUse Tm Hom target (.shared term)) : value X weaken use = X.act weaken term := by
  cases use
  rfl

theorem information_shared (X : Frames Tm Hom) (weaken : Hom a target) (term : Tm a)
    (use : RowUse Tm Hom target (.shared term)) : information X weaken use = [] := by
  cases use
  rfl

theorem scopeMember_shared (E : Extensions.{uO, uH, uE} Hom) (ext : E.Ext a) (term : Tm a)
    (use : RowUse Tm Hom (E.target ext) (.shared term)) : scopeMember E ext use = none := by
  cases use
  rfl

end RowUse

abbrev PackedUse (Tm : Obj → Type uT) (Hom : Obj → Obj → Type uH) (source target : Obj) :=
  (row : Row Tm source) × RowUse Tm Hom target row

structure Firing (O : Type uOcc) (E : Extensions.{uO, uH, uE} Hom) (P : Set (Rule Tm)) (s : State Tm O) where
  rule : Rule Tm
  member : rule ∈ P
  ext : E.Ext s.frame
  opening : Hom rule.basic.locals (E.target ext)
  selection : Selection O
  taken : (i : Fin selection.taken.length) → RowUse Tm Hom (E.target ext) (s.label (selection.taken.get i))
  read : (i : Fin selection.read.length) → RowUse Tm Hom (E.target ext) (s.label (selection.read.get i))
  seen : List (Finset O)

namespace Firing

variable {O : Type uOcc} {E : Extensions.{uO, uH, uE} Hom} {P : Set (Rule Tm)} {s : State Tm O}
  (f : Firing O E P s)

def takenUses : List (PackedUse Tm Hom s.frame (E.target f.ext)) :=
  List.ofFn (fun i => ⟨s.label (f.selection.taken.get i), f.taken i⟩)

def readUses : List (PackedUse Tm Hom s.frame (E.target f.ext)) :=
  List.ofFn (fun i => ⟨s.label (f.selection.read.get i), f.read i⟩)

def uses : List (PackedUse Tm Hom s.frame (E.target f.ext)) := f.takenUses ++ f.readUses

def scopeMember : JointFirings.Member (Tm s.frame) E (Set.univ : RuleSyntax.Program Tm) f.ext :=
  ⟨f.rule.scope, Set.mem_univ _, f.opening, ⟨[], [], []⟩, []⟩

def scopeBag : JointFirings.Bag (Tm s.frame) E (Set.univ : RuleSyntax.Program Tm) s.frame :=
  ⟨f.ext, f.scopeMember :: f.uses.filterMap (fun selected => RowUse.scopeMember E f.ext selected.2)⟩

def Fresh (X : Frames Tm Hom) : Prop := f.scopeBag.Fresh X s.scope

def takenValues (X : Frames Tm Hom) : List (Tm (E.target f.ext)) :=
  f.takenUses.map (fun selected => RowUse.value X (E.weaken f.ext) selected.2)

def readValues (X : Frames Tm Hom) : List (Tm (E.target f.ext)) :=
  f.readUses.map (fun selected => RowUse.value X (E.weaken f.ext) selected.2)

def information (X : Frames Tm Hom) : EquationStore (Tm (E.target f.ext)) :=
  X.applyStore (E.weaken f.ext) s.knowledge ++
    f.uses.flatMap (fun selected => RowUse.information X (E.weaken f.ext) selected.2) ++
    (f.rule.basic.body.take.map (X.act f.opening)).zip (f.takenValues X) ++
    (f.rule.basic.body.read.map (X.act f.opening)).zip (f.readValues X) ++
    X.applyStore f.opening f.rule.basic.body.tell

theorem takenValues_length (X : Frames Tm Hom) : (f.takenValues X).length = f.selection.taken.length := by
  simp [takenValues, takenUses]

theorem readValues_length (X : Frames Tm Hom) : (f.readValues X).length = f.selection.read.length := by
  simp [readValues, readUses]

end Firing

#print axioms RowUse.value_shared
#print axioms RowUse.scopeMember_shared
#print axioms Firing.takenValues_length
#print axioms Firing.readValues_length

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows
