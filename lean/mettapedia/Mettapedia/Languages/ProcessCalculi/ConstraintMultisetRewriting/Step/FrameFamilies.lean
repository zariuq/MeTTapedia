import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Frames

/-!
# Finite families of declaration frames

The empty family is a frame even when the original object type is empty.
Terms retain their original frame and validity witness. A morphism chooses one
target frame and native morphism for each represented source frame. Repeated
references to the same frame share that choice. No common original target,
inhabitant of an empty term fibre, or new term constructor is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Frames

universe uO uT uH

namespace Families

variable {Obj : Type uO} (Tm : Obj → Type uT) (Hom : Obj → Obj → Type uH)

abbrev Term (family : List Obj) := {term : (a : Obj) × Tm a // term.1 ∈ family}

abbrev Map (source target : List Obj) :=
  (a : Obj) → a ∈ source → (b : {b : Obj // b ∈ target}) × Hom a b.val

variable {Tm Hom}

inductive Related (X : Frames Tm Hom) : ((a : Obj) × Tm a) → ((a : Obj) × Tm a) → Prop
  | sameFrame {a : Obj} {left right : Tm a} (same : X.E left right) :
      Related X ⟨a, left⟩ ⟨a, right⟩

variable (X : Frames Tm Hom)

def act {source target : List Obj} (mapping : Map Hom source target)
    (term : Term Tm source) : Term Tm target :=
  let image := mapping term.val.1 term.property
  ⟨⟨image.fst.val, X.act image.snd term.val.2⟩, image.fst.property⟩

def identity (family : List Obj) : Map Hom family family :=
  fun a member => ⟨⟨a, member⟩, X.id a⟩

def compose {source middle target : List Obj}
    (later : Map Hom middle target) (earlier : Map Hom source middle) : Map Hom source target :=
  fun a member =>
    let first := earlier a member
    let second := later first.fst.val first.fst.property
    ⟨second.fst, X.comp second.snd first.snd⟩

def inclusion {source target : List Obj} (included : ∀ a ∈ source, a ∈ target) :
    Map Hom source target := fun a member => ⟨⟨a, included a member⟩, X.id a⟩

def left (one two : List Obj) : Map Hom one (one ++ two) :=
  inclusion X fun _ member => List.mem_append_left _ member

def right (one two : List Obj) : Map Hom two (one ++ two) :=
  inclusion X fun _ member => List.mem_append_right _ member

theorem act_inclusion {source target : List Obj} (included : ∀ a ∈ source, a ∈ target)
    (term : Term Tm source) : (act X (inclusion X included) term).val = term.val := by
  rcases term with ⟨⟨a, term⟩, member⟩
  simp [act, inclusion, X.act_id]

theorem empty_term_fibre : ¬Nonempty (Term Tm ([] : List Obj)) := by
  rintro ⟨term⟩
  have impossible := term.property
  cases impossible

theorem related_frame_eq {one two : (a : Obj) × Tm a} (same : Related X one two) :
    one.1 = two.1 := by
  cases same
  rfl

theorem related_same_frame_iff {a : Obj} {one two : Tm a} :
    Related X ⟨a, one⟩ ⟨a, two⟩ ↔ X.E one two := by
  constructor
  · intro same
    cases same with
    | sameFrame same => exact same
  · exact Related.sameFrame

theorem related_refl (term : (a : Obj) × Tm a) : Related X term term := by
  rcases term with ⟨a, term⟩
  exact .sameFrame ((X.equivalence a).refl term)

theorem related_symm {left right : (a : Obj) × Tm a} (same : Related X left right) :
    Related X right left := by
  cases same with
  | sameFrame same => exact .sameFrame ((X.equivalence _).symm same)

theorem related_trans {left middle right : (a : Obj) × Tm a}
    (first : Related X left middle) (second : Related X middle right) : Related X left right := by
  cases first with
  | sameFrame first =>
      cases second with
      | sameFrame second => exact .sameFrame ((X.equivalence _).trans first second)

theorem act_identity {family : List Obj} (term : Term Tm family) :
    act X (identity X family) term = term := by
  rcases term with ⟨⟨a, term⟩, member⟩
  apply Subtype.ext
  change (⟨a, X.act (X.id a) term⟩ : (b : Obj) × Tm b) = ⟨a, term⟩
  rw [X.act_id]

theorem act_compose {source middle target : List Obj}
    (later : Map Hom middle target) (earlier : Map Hom source middle) (term : Term Tm source) :
    act X (compose X later earlier) term = act X later (act X earlier term) := by
  rcases term with ⟨⟨a, term⟩, member⟩
  rcases first : earlier a member with ⟨⟨b, inMiddle⟩, firstMap⟩
  rcases second : later b inMiddle with ⟨⟨c, inTarget⟩, secondMap⟩
  apply Subtype.ext
  simp [act, compose, X.act_comp]

theorem preserves {source target : List Obj} (mapping : Map Hom source target)
    {left right : Term Tm source} (same : Related X left.val right.val) :
    Related X (act X mapping left).val (act X mapping right).val := by
  rcases left with ⟨⟨a, left⟩, inLeft⟩
  rcases right with ⟨⟨b, right⟩, inRight⟩
  cases same with
  | sameFrame same =>
      exact .sameFrame (X.preserves (mapping a inLeft).snd same)

end Families

def families {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
    (X : Frames Tm Hom) : Frames (Families.Term Tm) (Families.Map Hom) where
  E left right := Families.Related X left.val right.val
  equivalence _ := ⟨fun term => Families.related_refl X term.val,
    fun same => Families.related_symm X same,
    fun first second => Families.related_trans X first second⟩
  act := Families.act X
  id := Families.identity X
  comp := Families.compose X
  act_id := Families.act_identity X
  act_comp := Families.act_compose X
  preserves := Families.preserves X

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Frames
