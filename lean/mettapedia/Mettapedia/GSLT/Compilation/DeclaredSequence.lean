import Mettapedia.OSLF.MeTTaIL.Syntax

/-!
# A list view on declared sequence constructors

The view reads a spine of two explicitly chosen constructors, retaining the
element patterns as authored. Nothing rewrites terms outside that view.
The declaration is about constructor rows in an actual signature. A result
sort with additional constructors is not implicitly quotiented by this view.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Compilation.DeclaredSequence

open Mettapedia.OSLF.MeTTaIL.Syntax (LanguageDef Pattern)

/-- Choose two constructors in the supplied signature. The declaration
does not change their names, payloads or the signature's remaining rows. -/
structure View (language : LanguageDef) where
  sort : String
  elementSort : String
  nil : String
  cons : String
  nilDeclared : ∃ rule ∈ language.terms,
    rule.label = nil ∧ rule.category = sort ∧ rule.params = []
  consDeclared : ∃ rule ∈ language.terms, ∃ head tail : String,
    rule.label = cons ∧ rule.category = sort ∧
      rule.params = [.simple head (.base elementSort), .simple tail (.base sort)]

namespace View

variable {language : LanguageDef} (view : View language)

/-- The authored sequence spine. Element patterns are not normalized. -/
def put : List Pattern → Pattern
  | [] => .apply view.nil []
  | head :: tail => .apply view.cons [head, put tail]

/-- A partial view, not an evaluator equation for constructors named
`cons`. Improper tails and other constructors are outside its domain. -/
def get? : Pattern → Option (List Pattern)
  | .apply label [] => if label = view.nil then some [] else none
  | .apply label [head, tail] =>
      if label = view.cons then (get? tail).map (head :: ·) else none
  | _ => none
termination_by value => sizeOf value

/-- The sequence-specific shape of an authored value, independent of the
partial decoder. Element typing can be checked by the source judgment. -/
inductive Spine : Pattern → Prop
  | nil : Spine (.apply view.nil [])
  | cons (head : Pattern) {tail : Pattern} :
      Spine tail → Spine (.apply view.cons [head, tail])

@[simp] theorem get_put (items : List Pattern) : view.get? (view.put items) = some items := by
  induction items with
  | nil => simp [put, get?]
  | cons head tail ih => simp [put, get?, ih]

theorem put_has_spine (items : List Pattern) : view.Spine (view.put items) := by
  induction items with
  | nil => exact .nil
  | cons head tail ih => exact .cons head ih

theorem put_get : ∀ {value : Pattern} {items : List Pattern},
    view.get? value = some items → view.put items = value
  | .apply label [], items, read => by
      by_cases name : label = view.nil
      · subst label
        have same : [] = items := by simpa [get?] using read
        subst items
        rfl
      · simp [get?, name] at read
  | .apply label [head, tail], items, read => by
      by_cases name : label = view.cons
      · subst label
        cases result : view.get? tail with
        | none => simp [get?, result] at read
        | some rest =>
            have same : head :: rest = items := by simpa [get?, result] using read
            subst items
            have tailExact := put_get result
            simp only [put, tailExact]
      · simp [get?, name] at read
  | .apply _ [_], _, read => by simp [get?] at read
  | .apply _ (_ :: _ :: _ :: _), _, read => by simp [get?] at read
  | .bvar _, _, read => by simp [get?] at read
  | .fvar _, _, read => by simp [get?] at read
  | .lambda _ _, _, read => by simp [get?] at read
  | .multiLambda _ _ _, _, read => by simp [get?] at read
  | .subst _ _, _, read => by simp [get?] at read
  | .collection _ _ _, _, read => by simp [get?] at read
termination_by value => sizeOf value

theorem accepts_iff_spine (value : Pattern) :
    (∃ items, view.get? value = some items) ↔ view.Spine value := by
  constructor
  · rintro ⟨items, read⟩
    rw [← view.put_get read]
    exact view.put_has_spine items
  · intro proper
    induction proper with
    | nil => exact ⟨[], view.get_put []⟩
    | cons head tail ih =>
        obtain ⟨items, read⟩ := ih
        exact ⟨head :: items, by simp [get?, read]⟩

/-- A successful view cannot identify any two distinct authored spines. -/
theorem view_injective_on_spine :
    Set.InjOn view.get? {term | view.Spine term} := by
  intro left leftSpine right _ equal
  obtain ⟨items, read⟩ := (view.accepts_iff_spine left).mpr leftSpine
  exact (view.put_get read).symm.trans (view.put_get (equal ▸ read))

theorem put_injective : Function.Injective view.put := by
  intro a b same
  have observations := congrArg view.get? same
  simpa only [get_put, Option.some.injEq] using observations

namespace Controls

/-- The old untyped flattening equation, isolated at the actual collision
shape. It is not the declared sequence view. -/
def indiscriminateCons : Pattern → Pattern
  | .apply "cons" [.apply head [], .apply next rest] => .apply head (.apply next [] :: rest)
  | original => original

def consTerm : Pattern := .apply "cons" [.apply "h" [], .apply "t1" [.apply "t2" []]]
def flatTerm : Pattern := .apply "h" [.apply "t1" [], .apply "t2" []]

theorem flatten_collides :
    consTerm ≠ flatTerm ∧ indiscriminateCons consTerm = indiscriminateCons flatTerm :=
  ⟨by decide, rfl⟩

theorem flatten_not_injective : ¬ Function.Injective indiscriminateCons :=
  fun injective => flatten_collides.1 (injective flatten_collides.2)

theorem unlisted_head_refused (label : String) (different : label ≠ view.nil) :
    view.get? (.apply label []) = none := by
  simp [get?, different]

end Controls

#print axioms get_put
#print axioms put_has_spine
#print axioms put_get
#print axioms accepts_iff_spine
#print axioms view_injective_on_spine
#print axioms put_injective
#print axioms Controls.flatten_collides
#print axioms Controls.flatten_not_injective
#print axioms Controls.unlisted_head_refused

end View

end Mettapedia.GSLT.Compilation.DeclaredSequence
