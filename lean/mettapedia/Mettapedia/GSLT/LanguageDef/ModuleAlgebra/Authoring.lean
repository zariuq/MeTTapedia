import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.Presentation
import Mettapedia.GSLT.LanguageDef.ModuleFormat.DependencyAdmission

/-!
# Origin-sensitive composition in the existing coGSLT interface

Finite declaration fragments are generators of nested authored documents.
Elaboration flattens bundles, unions their fragments, and checks the whole.
Unlike ordered module-envelope catalogs, repeated shared declarations are
identified. A conflicting declaration rejects the whole assembly.

This structured authoring boundary does not parse the upstream `.module` surface.
-/

namespace Mettapedia.GSLT.LanguageDef.ModuleAlgebra

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef.Extension
open Mettapedia.GSLT.LanguageDef.ExtensionComposition

variable {Origin Label Body : Type}
  [DecidableEq Origin] [DecidableEq Label] [DecidableEq Body]

def unionFragments (fragments : List (Fragment (Origin := Origin)
    (Label := Label) (Body := Body))) :
    Fragment (Origin := Origin) (Label := Label) (Body := Body) :=
  fragments.foldr (· ∪ ·) ∅

theorem unionFragments_append (first second : List (Fragment (Origin := Origin)
    (Label := Label) (Body := Body))) :
    unionFragments (first ++ second) = unionFragments first ∪ unionFragments second := by
  let : Std.Associative (fun a b : Fragment (Origin := Origin)
      (Label := Label) (Body := Body) => a ∪ b) := ⟨Finset.union_assoc⟩
  simp only [unionFragments, List.foldr_append]
  simpa only [Finset.empty_union] using
    (List.foldr_assoc (l := first) (op := (· ∪ ·))
      (a₁ := ∅) (a₂ := second.foldr (· ∪ ·) ∅))

abbrev Document (Origin Label Body : Type) := DeclarationDocument (Finset (Entry Origin Label Body))

def elaborate (document : Document Origin Label Body) :
    Option (Presentation Origin Label Body) := check (unionFragments document.values)

/-- Quote a whole admitted fragment as one structured declaration. -/
def quote (p : Presentation Origin Label Body) : Document Origin Label Body := .declaration p.val

@[simp] theorem elaborate_quote (p : Presentation Origin Label Body) :
    elaborate (quote p) = some p := by
  simp [elaborate, quote, DeclarationDocument.values, unionFragments]

/-- The algebra reuses the library's authored GSLT and exact-elaboration laws. -/
def presentationSystem : GSLT.CompositionalElaboration (Presentation Origin Label Body) where
  authoring := ExactDeclarationCodec.documentCompositional (Finset (Entry Origin Label Body))
  elaboration := {
    elaborate := elaborate
    quote := quote
    elaborate_quote := elaborate_quote
    equation := by
      intro first second equivalent
      change first.values = second.values at equivalent
      unfold elaborate
      rw [equivalent]
    rewrite := by
      intro first second impossible
      exact False.elim impossible }
  emptyPayload := empty
  merge := join
  elaborate_empty := by
    simp [elaborate, ExactDeclarationCodec.documentCompositional,
      DeclarationDocument.values, DeclarationDocument.valuesList, unionFragments, check, empty]
  elaborate_append := by
    intro first second
    change Document Origin Label Body at first second
    change elaborate (.bundle [first, second]) = _
    simp only [elaborate, DeclarationDocument.values, DeclarationDocument.valuesList,
      List.append_nil]
    rw [unionFragments_append, check_union]

/-- Associativity includes both rejection paths, derived from the source laws. -/
theorem join_assoc (first second third : Presentation Origin Label Body) :
    (join first second).bind (fun merged => join merged third) =
      (join second third).bind (fun merged => join first merged) :=
  presentationSystem.toPartialMonoid.op_assoc first second third

def presentationLayer (Base : Type) : CompositionalLayer Base where
  Fiber := fun _ => Presentation Origin Label Body
  system := fun _ => presentationSystem

def presentationCoGSLT (Base : Type) : CoGSLTLayer Base :=
  (presentationLayer (Origin := Origin) (Label := Label) (Body := Body) Base).toCoGSLTLayer

/-- Checked envelope dependencies and presentation composition attach to the
same snapshot/core interface through the established product construction. -/
def checkedModulePresentationLayer (limits : ModuleFormat.Limits) :
    CompositionalLayer (ModuleFormat.Snapshot limits) :=
  (ModuleFormat.checkedCatalogCompositionalLayer limits).product
    (presentationLayer (Origin := Origin) (Label := Label) (Body := Body) _)

end Mettapedia.GSLT.LanguageDef.ModuleAlgebra
