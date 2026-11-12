import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Frames

/-!
# Reindexing frames and retaining copy identities

An object index is distinct from the underlying term context. Reindexing
retains the native actions. Copy indices permit distinct occurrences of the
same original context; a source copy supplies its own index for lifting any
native future, so no global inhabitant or fresh-index axiom is needed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Frames

universe uO uT uH uN uK

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}

def reindex (X : Frames Tm Hom) {Index : Type uN} (forget : Index → Obj) :
    Frames (fun index => Tm (forget index)) (fun first last => Hom (forget first) (forget last)) where
  E := X.E
  equivalence index := X.equivalence (forget index)
  act := X.act
  id index := X.id (forget index)
  comp := X.comp
  act_id := X.act_id
  act_comp := X.act_comp
  preserves := X.preserves

def copies (X : Frames Tm Hom) (Key : Type uK) :
    Frames (fun index : Key × Obj => Tm index.2) (fun first last => Hom first.2 last.2) :=
  X.reindex Prod.snd

theorem copies_solvable_iff (X : Frames Tm Hom) {Key : Type uK} (source : Key × Obj)
    (knowledge : EquationStore (Tm source.2)) :
    (X.copies Key).Solvable (a := source) knowledge ↔ X.Solvable knowledge := by
  constructor
  · rintro ⟨target, mapping, solved⟩
    exact ⟨target.2, mapping, solved⟩
  · rintro ⟨target, mapping, solved⟩
    exact ⟨(source.1, target), mapping, solved⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Frames
