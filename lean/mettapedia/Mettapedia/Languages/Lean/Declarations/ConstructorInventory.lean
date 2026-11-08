import Mettapedia.Languages.Lean.Declarations.BlockProfile

/-!
# Constructor erasure through single-family and tagged-block inventories

The original single-family profile remains the first route. Nested/mutual
constructors use the block inventory when admitted. Other profiles retain
the source compiler's erasure information without claiming model admission.
-/

namespace Mettapedia.Languages.Lean.Declarations.ConstructorInventory

open _root_.Lean _root_.Lean.Meta

def constructorFields (constructor : Name) : MetaM (List Bool) := do
  let some (.ctorInfo info) := (← getEnv).find? constructor | keptConstructorFields constructor
  if info.induct.isAnonymous then return ← keptConstructorFields constructor
  match ← read info.induct with
  | .ok reading =>
      match (Profile.inventoryKept reading).bind (·.lookup constructor.toString) with
      | some fields => return fields
      | none => keptConstructorFields constructor
  | .error _ =>
      match ← readBlock info.induct with
      | .ok block =>
          match (BlockProfile.inventoryKept block).bind (·.lookup constructor.toString) with
          | some fields => return fields
          | none => keptConstructorFields constructor
      | .error _ => keptConstructorFields constructor

end Mettapedia.Languages.Lean.Declarations.ConstructorInventory
