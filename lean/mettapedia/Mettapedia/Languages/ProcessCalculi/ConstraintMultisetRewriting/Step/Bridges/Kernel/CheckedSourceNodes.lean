import Mettapedia.Languages.HOLLight.ExportReplay

/-!
# Compositional source checks and context-qualified canonical images

Each node retains the existing named type-check equation. Canonical images
retain equality to the existing binder conversion. A memo key never grants
authority: the stored source and typed binder list must agree before reuse.
The HOL inference and declaration checkers are unchanged.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.CheckedSourceNodes

open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight

def constant (symbol : Const) (type : Ty) : CheckedSourceTerm :=
  ⟨.const symbol type, type, by simp only [SourceTerm.inferType]⟩

def variableNode (name : Name) (type : Ty) : CheckedSourceTerm :=
  ⟨.var name type, type, by simp only [SourceTerm.inferType]⟩

def retarget? (checked : CheckedSourceTerm) (source : SourceTerm) : Option CheckedSourceTerm :=
  if same : SourceTerm.same checked.source source = true then
    some ⟨source, checked.ty, by
      rw [← (SourceTerm.same_eq_true_iff _ _).mp same]
      exact checked.checked⟩
  else none

def application? (function argument : CheckedSourceTerm) : Option CheckedSourceTerm :=
  match found : function.ty.destFunction? with
  | none => none
  | some (domain, codomain) =>
      if same : Ty.same domain argument.ty = true then
        some ⟨.app function.source argument.source, codomain, by
          simp [SourceTerm.inferType, function.checked, argument.checked, found, same]⟩
      else none

def abstraction (name : Name) (domain : Ty) (body : CheckedSourceTerm) : CheckedSourceTerm :=
  ⟨.abs name domain body.source, .function domain body.ty, by
    simp [SourceTerm.inferType, body.checked]⟩

theorem application_success (function argument : CheckedSourceTerm) :
    (application? function argument).isSome ↔
      (.app function.source argument.source : SourceTerm).inferType.isSome := by
  unfold application?
  split
  · rename_i found
    simp [SourceTerm.inferType, function.checked, argument.checked, found]
  · rename_i domain codomain found
    split <;> rename_i same
    all_goals simp [SourceTerm.inferType, function.checked, argument.checked, found, same]

structure Image (source : SourceTerm) (binders : List SourceVar) where
  term : DBTerm
  exact : term = source.toDB binders

def canonical (checked : CheckedSourceTerm) (image : Image checked.source []) : CanonicalTerm :=
  ⟨image.term, checked.ty, by
    rw [image.exact]
    exact (DBTerm.inferType_toDB [] checked.source).trans checked.checked⟩

theorem canonical_agrees (checked : CheckedSourceTerm) (image : Image checked.source []) :
    canonical checked image = checked.canonical := by
  apply CanonicalTerm.ext_term
  exact image.exact

def Image.constant (symbol : Const) (type : Ty) (binders : List SourceVar) :
    Image (.const symbol type) binders :=
  ⟨.const symbol type, by simp only [SourceTerm.toDB]⟩

def Image.variable (name : Name) (type : Ty) (binders : List SourceVar) :
    Image (.var name type) binders :=
  ⟨match boundIndex ⟨name,type⟩ binders with
    | some index => .bound index
    | none => .free ⟨name,type⟩,
   by cases found : boundIndex ⟨name,type⟩ binders <;> simp [SourceTerm.toDB, found]⟩

def Image.application {function argument : SourceTerm} {binders : List SourceVar}
    (left : Image function binders) (right : Image argument binders) :
    Image (.app function argument) binders :=
  ⟨.app left.term right.term, by simp only [SourceTerm.toDB, left.exact, right.exact]⟩

def Image.abstraction (name : Name) (domain : Ty) {body : SourceTerm} {binders : List SourceVar}
    (inside : Image body (⟨name,domain⟩ :: binders)) :
    Image (.abs name domain body) binders :=
  ⟨.abs domain inside.term, by simp only [SourceTerm.toDB, inside.exact]⟩

def bindersSame : List SourceVar → List SourceVar → Bool
  | [], [] => true
  | first :: rest, other :: later => sourceVarSame first other && bindersSame rest later
  | _, _ => false

theorem bindersSame_iff (first second : List SourceVar) :
    bindersSame first second = true ↔ first = second := by
  induction first generalizing second with
  | nil => cases second <;> simp [bindersSame]
  | cons head rest ih =>
      cases second <;> simp [bindersSame, sourceVarSame_eq_true_iff, ih]

structure Entry where
  source : SourceTerm
  binders : List SourceVar
  image : Image source binders

def Entry.use? (entry : Entry) (source : SourceTerm) (binders : List SourceVar) :
    Option (Image source binders) :=
  if sameSource : SourceTerm.same entry.source source = true then
    if sameBinders : bindersSame entry.binders binders = true then
      some ⟨entry.image.term, by
        rw [entry.image.exact, (SourceTerm.same_eq_true_iff _ _).mp sameSource,
          (bindersSame_iff _ _).mp sameBinders]⟩
    else none
  else none

theorem Entry.use_same (entry : Entry) : entry.use? entry.source entry.binders = some entry.image := by
  simp only [Entry.use?, SourceTerm.same_eq_true_iff, bindersSame_iff, ↓reduceDIte]

namespace Controls

def x : SourceVar := ⟨Name.global "x", Ty.bool⟩
def stored : Entry := ⟨.var x.name x.ty, [x], Image.variable x.name x.ty [x]⟩

theorem same_context_hits : (stored.use? (.var x.name x.ty) [x]).isSome = true := by
  rw [show stored.use? (.var x.name x.ty) [x] = some stored.image from stored.use_same]
  rfl

theorem changed_context_misses : (stored.use? (.var x.name x.ty) []).isNone = true := by
  decide +kernel

theorem changed_source_misses :
    (stored.use? (.var (Name.global "y") Ty.bool) [x]).isNone = true := by
  decide +kernel

end Controls

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.CheckedSourceNodes
