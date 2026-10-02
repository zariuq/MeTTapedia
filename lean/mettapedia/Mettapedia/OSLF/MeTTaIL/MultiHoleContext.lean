import Mettapedia.OSLF.MeTTaIL.DerivedContexts
import Mathlib.Data.List.Nodup
import Mathlib.Logic.Function.Basic

/-!
# Patterns with several holes

A one-hole context is a pattern with one distinguished position.  A pattern
with holes named by an index type has any number of them.  Filling replaces
every hole by a pattern, textually: a hole beneath a binder captures, which is
what a context is for.

Plugging contexts into the holes of a context is the bind of a monad whose
unit is a hole.  Its laws are proved here on the syntax itself.  A pattern is
a context with no hole, a one-hole context is a context whose only index
names one hole, and filling agrees with the existing plugging in both cases.

A context is linear when every index names exactly one hole.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.DerivedContexts

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- A pattern with holes named by `ι`. -/
inductive MultiHoleContext (ι : Type) where
  | hole (index : ι)
  | bvar (index : Nat)
  | fvar (name : String)
  | apply (constructor : String) (arguments : List (MultiHoleContext ι))
  | lambda (binderName : Option String) (body : MultiHoleContext ι)
  | multiLambda (arity : Nat) (binderNames : List String) (body : MultiHoleContext ι)
  | subst (body replacement : MultiHoleContext ι)
  | collection (collectionType : CollType) (elements : List (MultiHoleContext ι))
      (rest : Option String)

namespace MultiHoleContext

variable {ι κ μ : Type}

mutual
/-- Replace every hole by the pattern assigned to its index. -/
def fill (filling : ι → Pattern) : MultiHoleContext ι → Pattern
  | .hole index => filling index
  | .bvar index => .bvar index
  | .fvar name => .fvar name
  | .apply constructor arguments => .apply constructor (fillList filling arguments)
  | .lambda binderName body => .lambda binderName (fill filling body)
  | .multiLambda arity binderNames body => .multiLambda arity binderNames (fill filling body)
  | .subst body replacement => .subst (fill filling body) (fill filling replacement)
  | .collection collectionType elements rest =>
      .collection collectionType (fillList filling elements) rest

/-- Filling, along a list of contexts. -/
def fillList (filling : ι → Pattern) : List (MultiHoleContext ι) → List Pattern
  | [] => []
  | context :: contexts => fill filling context :: fillList filling contexts
end

mutual
/-- Replace every hole by the context assigned to its index. -/
def bind (assignment : ι → MultiHoleContext κ) : MultiHoleContext ι → MultiHoleContext κ
  | .hole index => assignment index
  | .bvar index => .bvar index
  | .fvar name => .fvar name
  | .apply constructor arguments => .apply constructor (bindList assignment arguments)
  | .lambda binderName body => .lambda binderName (bind assignment body)
  | .multiLambda arity binderNames body => .multiLambda arity binderNames (bind assignment body)
  | .subst body replacement => .subst (bind assignment body) (bind assignment replacement)
  | .collection collectionType elements rest =>
      .collection collectionType (bindList assignment elements) rest

/-- Plugging, along a list of contexts. -/
def bindList (assignment : ι → MultiHoleContext κ) :
    List (MultiHoleContext ι) → List (MultiHoleContext κ)
  | [] => []
  | context :: contexts => bind assignment context :: bindList assignment contexts
end

mutual
/-- The indices of the holes of a context, in order of occurrence. -/
def holes : MultiHoleContext ι → List ι
  | .hole index => [index]
  | .bvar _ => []
  | .fvar _ => []
  | .apply _ arguments => holesList arguments
  | .lambda _ body => holes body
  | .multiLambda _ _ body => holes body
  | .subst body replacement => holes body ++ holes replacement
  | .collection _ elements _ => holesList elements

/-- The holes of a list of contexts. -/
def holesList : List (MultiHoleContext ι) → List ι
  | [] => []
  | context :: contexts => holes context ++ holesList contexts
end

mutual
/-- A pattern as a context with no hole. -/
def ofPattern : Pattern → MultiHoleContext ι
  | .bvar index => .bvar index
  | .fvar name => .fvar name
  | .apply constructor arguments => .apply constructor (ofPatternList arguments)
  | .lambda binderName body => .lambda binderName (ofPattern body)
  | .multiLambda arity binderNames body => .multiLambda arity binderNames (ofPattern body)
  | .subst body replacement => .subst (ofPattern body) (ofPattern replacement)
  | .collection collectionType elements rest =>
      .collection collectionType (ofPatternList elements) rest

/-- Patterns as contexts with no hole, along a list. -/
def ofPatternList : List Pattern → List (MultiHoleContext ι)
  | [] => []
  | pattern :: patterns => ofPattern pattern :: ofPatternList patterns
end

/-- Rename the holes of a context. -/
def relabel (rename : ι → κ) (context : MultiHoleContext ι) : MultiHoleContext κ :=
  bind (fun index => .hole (rename index)) context

/-- Plug a family of contexts into the holes of a context.  The holes of the
result are the holes of the plugged contexts, kept apart by the hole they were
plugged into. -/
def plug {arity : ι → Type} (context : MultiHoleContext ι)
    (inner : (index : ι) → MultiHoleContext (arity index)) :
    MultiHoleContext (Σ index, arity index) :=
  bind (fun index => relabel (Sigma.mk index) (inner index)) context

/-! ## Lists -/

@[simp] theorem fillList_eq_map (filling : ι → Pattern) :
    ∀ contexts : List (MultiHoleContext ι), fillList filling contexts = contexts.map (fill filling)
  | [] => rfl
  | context :: contexts => by
      simp only [fillList, List.map_cons, fillList_eq_map filling contexts]

@[simp] theorem bindList_eq_map (assignment : ι → MultiHoleContext κ) :
    ∀ contexts : List (MultiHoleContext ι),
      bindList assignment contexts = contexts.map (bind assignment)
  | [] => rfl
  | context :: contexts => by
      simp only [bindList, List.map_cons, bindList_eq_map assignment contexts]

@[simp] theorem holesList_eq_flatMap :
    ∀ contexts : List (MultiHoleContext ι), holesList contexts = contexts.flatMap holes
  | [] => rfl
  | context :: contexts => by
      simp only [holesList, List.flatMap_cons, holesList_eq_flatMap contexts]

@[simp] theorem ofPatternList_eq_map :
    ∀ patterns : List Pattern,
      (ofPatternList patterns : List (MultiHoleContext ι)) = patterns.map ofPattern
  | [] => rfl
  | pattern :: patterns => by
      simp only [ofPatternList, List.map_cons, ofPatternList_eq_map patterns]

/-! ## The monad laws -/

mutual
/-- **Filling a plugged context** fills the outer context with the filled
inner ones. -/
theorem fill_bind (filling : κ → Pattern) (assignment : ι → MultiHoleContext κ) :
    ∀ context : MultiHoleContext ι,
      fill filling (bind assignment context) =
        fill (fun index => fill filling (assignment index)) context
  | .hole _ => rfl
  | .bvar _ => rfl
  | .fvar _ => rfl
  | .apply _ arguments => by
      simp only [bind, fill, fillList_bindList filling assignment arguments]
  | .lambda _ body => by simp only [bind, fill, fill_bind filling assignment body]
  | .multiLambda _ _ body => by simp only [bind, fill, fill_bind filling assignment body]
  | .subst body replacement => by
      simp only [bind, fill, fill_bind filling assignment body,
        fill_bind filling assignment replacement]
  | .collection _ elements _ => by
      simp only [bind, fill, fillList_bindList filling assignment elements]

theorem fillList_bindList (filling : κ → Pattern) (assignment : ι → MultiHoleContext κ) :
    ∀ contexts : List (MultiHoleContext ι),
      fillList filling (bindList assignment contexts) =
        fillList (fun index => fill filling (assignment index)) contexts
  | [] => rfl
  | context :: contexts => by
      simp only [bindList, fillList, fill_bind filling assignment context,
        fillList_bindList filling assignment contexts]
end

mutual
/-- Plugging is associative. -/
theorem bind_bind (second : κ → MultiHoleContext μ) (first : ι → MultiHoleContext κ) :
    ∀ context : MultiHoleContext ι,
      bind second (bind first context) = bind (fun index => bind second (first index)) context
  | .hole _ => rfl
  | .bvar _ => rfl
  | .fvar _ => rfl
  | .apply _ arguments => by simp only [bind, bindList_bindList second first arguments]
  | .lambda _ body => by simp only [bind, bind_bind second first body]
  | .multiLambda _ _ body => by simp only [bind, bind_bind second first body]
  | .subst body replacement => by
      simp only [bind, bind_bind second first body, bind_bind second first replacement]
  | .collection _ elements _ => by simp only [bind, bindList_bindList second first elements]

theorem bindList_bindList (second : κ → MultiHoleContext μ) (first : ι → MultiHoleContext κ) :
    ∀ contexts : List (MultiHoleContext ι),
      bindList second (bindList first contexts) =
        bindList (fun index => bind second (first index)) contexts
  | [] => rfl
  | context :: contexts => by
      simp only [bindList, bind_bind second first context,
        bindList_bindList second first contexts]
end

mutual
/-- Plugging a hole into every hole changes nothing. -/
theorem bind_hole : ∀ context : MultiHoleContext ι, bind .hole context = context
  | .hole _ => rfl
  | .bvar _ => rfl
  | .fvar _ => rfl
  | .apply _ arguments => by simp only [bind, bindList_hole arguments]
  | .lambda _ body => by simp only [bind, bind_hole body]
  | .multiLambda _ _ body => by simp only [bind, bind_hole body]
  | .subst body replacement => by simp only [bind, bind_hole body, bind_hole replacement]
  | .collection _ elements _ => by simp only [bind, bindList_hole elements]

theorem bindList_hole : ∀ contexts : List (MultiHoleContext ι), bindList .hole contexts = contexts
  | [] => rfl
  | context :: contexts => by simp only [bindList, bind_hole context, bindList_hole contexts]
end

mutual
/-- The holes of a plugged context are the holes of the plugged contexts, in
the order of the holes they fill. -/
theorem holes_bind (assignment : ι → MultiHoleContext κ) :
    ∀ context : MultiHoleContext ι,
      holes (bind assignment context) =
        (holes context).flatMap fun index => holes (assignment index)
  | .hole _ => by simp [bind, holes]
  | .bvar _ => rfl
  | .fvar _ => rfl
  | .apply _ arguments => by simp only [bind, holes, holesList_bindList assignment arguments]
  | .lambda _ body => by simp only [bind, holes, holes_bind assignment body]
  | .multiLambda _ _ body => by simp only [bind, holes, holes_bind assignment body]
  | .subst body replacement => by
      simp only [bind, holes, holes_bind assignment body, holes_bind assignment replacement,
        List.flatMap_append]
  | .collection _ elements _ => by
      simp only [bind, holes, holesList_bindList assignment elements]

theorem holesList_bindList (assignment : ι → MultiHoleContext κ) :
    ∀ contexts : List (MultiHoleContext ι),
      holesList (bindList assignment contexts) =
        (holesList contexts).flatMap fun index => holes (assignment index)
  | [] => rfl
  | context :: contexts => by
      simp only [bindList, holesList, holes_bind assignment context,
        holesList_bindList assignment contexts, List.flatMap_append]
end

mutual
/-- Filling reads the filling only at the holes of the context. -/
theorem fill_congr {first second : ι → Pattern} :
    ∀ context : MultiHoleContext ι,
      (∀ index ∈ holes context, first index = second index) →
        fill first context = fill second context
  | .hole index, agree => agree index (by simp [holes])
  | .bvar _, _ => rfl
  | .fvar _, _ => rfl
  | .apply _ arguments, agree => by
      simp only [fill, fillList_congr arguments agree]
  | .lambda _ body, agree => by simp only [fill, fill_congr body agree]
  | .multiLambda _ _ body, agree => by simp only [fill, fill_congr body agree]
  | .subst body replacement, agree => by
      simp only [fill,
        fill_congr body (fun index membership =>
          agree index (by simp only [holes, List.mem_append]; exact .inl membership)),
        fill_congr replacement (fun index membership =>
          agree index (by simp only [holes, List.mem_append]; exact .inr membership))]
  | .collection _ elements _, agree => by
      simp only [fill, fillList_congr elements agree]

theorem fillList_congr {first second : ι → Pattern} :
    ∀ contexts : List (MultiHoleContext ι),
      (∀ index ∈ holesList contexts, first index = second index) →
        fillList first contexts = fillList second contexts
  | [], _ => rfl
  | context :: contexts, agree => by
      simp only [fillList,
        fill_congr context (fun index membership =>
          agree index (by simp only [holesList, List.mem_append]; exact .inl membership)),
        fillList_congr contexts (fun index membership =>
          agree index (by simp only [holesList, List.mem_append]; exact .inr membership))]
end

/-! ## Patterns are the contexts with no hole -/

mutual
/-- A pattern has no hole to fill. -/
theorem fill_ofPattern (filling : ι → Pattern) :
    ∀ pattern : Pattern, fill filling (ofPattern pattern) = pattern
  | .bvar _ => rfl
  | .fvar _ => rfl
  | .apply _ arguments => by simp only [ofPattern, fill, fillList_ofPatternList filling arguments]
  | .lambda _ body => by simp only [ofPattern, fill, fill_ofPattern filling body]
  | .multiLambda _ _ body => by simp only [ofPattern, fill, fill_ofPattern filling body]
  | .subst body replacement => by
      simp only [ofPattern, fill, fill_ofPattern filling body, fill_ofPattern filling replacement]
  | .collection _ elements _ => by
      simp only [ofPattern, fill, fillList_ofPatternList filling elements]

theorem fillList_ofPatternList (filling : ι → Pattern) :
    ∀ patterns : List Pattern, fillList filling (ofPatternList patterns) = patterns
  | [] => rfl
  | pattern :: patterns => by
      simp only [ofPatternList, fillList, fill_ofPattern filling pattern,
        fillList_ofPatternList filling patterns]
end

mutual
theorem holes_ofPattern : ∀ pattern : Pattern, holes (ofPattern pattern : MultiHoleContext ι) = []
  | .bvar _ => rfl
  | .fvar _ => rfl
  | .apply _ arguments => by simp only [ofPattern, holes, holesList_ofPatternList arguments]
  | .lambda _ body => by simp only [ofPattern, holes, holes_ofPattern body]
  | .multiLambda _ _ body => by simp only [ofPattern, holes, holes_ofPattern body]
  | .subst body replacement => by
      simp only [ofPattern, holes, holes_ofPattern body, holes_ofPattern replacement,
        List.append_nil]
  | .collection _ elements _ => by simp only [ofPattern, holes, holesList_ofPatternList elements]

theorem holesList_ofPatternList :
    ∀ patterns : List Pattern, holesList (ofPatternList patterns : List (MultiHoleContext ι)) = []
  | [] => rfl
  | pattern :: patterns => by
      simp only [ofPatternList, holesList, holes_ofPattern pattern,
        holesList_ofPatternList patterns, List.append_nil]
end

mutual
/-- A context with no hole is the pattern it fills to. -/
theorem ofPattern_fill (filling : ι → Pattern) :
    ∀ context : MultiHoleContext ι, holes context = [] →
      (ofPattern (fill filling context) : MultiHoleContext ι) = context
  | .hole _, empty => by simp [holes] at empty
  | .bvar _, _ => rfl
  | .fvar _, _ => rfl
  | .apply _ arguments, empty => by
      simp only [fill, ofPattern, ofPatternList_fillList filling arguments empty]
  | .lambda _ body, empty => by simp only [fill, ofPattern, ofPattern_fill filling body empty]
  | .multiLambda _ _ body, empty => by
      simp only [fill, ofPattern, ofPattern_fill filling body empty]
  | .subst body replacement, empty => by
      simp only [holes, List.append_eq_nil_iff] at empty
      simp only [fill, ofPattern, ofPattern_fill filling body empty.1,
        ofPattern_fill filling replacement empty.2]
  | .collection _ elements _, empty => by
      simp only [fill, ofPattern, ofPatternList_fillList filling elements empty]

theorem ofPatternList_fillList (filling : ι → Pattern) :
    ∀ contexts : List (MultiHoleContext ι), holesList contexts = [] →
      (ofPatternList (fillList filling contexts) : List (MultiHoleContext ι)) = contexts
  | [], _ => rfl
  | context :: contexts, empty => by
      simp only [holesList, List.append_eq_nil_iff] at empty
      simp only [fillList, ofPatternList, ofPattern_fill filling context empty.1,
        ofPatternList_fillList filling contexts empty.2]
end

/-! ## Renaming and plugging families -/

theorem fill_relabel (filling : κ → Pattern) (rename : ι → κ) (context : MultiHoleContext ι) :
    fill filling (relabel rename context) = fill (fun index => filling (rename index)) context :=
  fill_bind filling _ context

theorem holes_relabel (rename : ι → κ) (context : MultiHoleContext ι) :
    holes (relabel rename context) = (holes context).map rename := by
  rw [relabel, holes_bind, List.map_eq_flatMap]
  rfl

theorem relabel_relabel (second : κ → μ) (first : ι → κ) (context : MultiHoleContext ι) :
    relabel second (relabel first context) = relabel (fun index => second (first index)) context :=
  bind_bind _ _ context

theorem relabel_id (context : MultiHoleContext ι) : relabel id context = context :=
  bind_hole context

/-- **Filling a plugged family.**  Each inner context is filled with the part
of the filling that belongs to its own holes. -/
theorem fill_plug {arity : ι → Type} (filling : (Σ index, arity index) → Pattern)
    (context : MultiHoleContext ι) (inner : (index : ι) → MultiHoleContext (arity index)) :
    fill filling (plug context inner) =
      fill (fun index => fill (fun position => filling ⟨index, position⟩) (inner index))
        context := by
  rw [plug, fill_bind]
  congr 1
  funext index
  exact fill_relabel filling (Sigma.mk index) (inner index)

theorem holes_plug {arity : ι → Type} (context : MultiHoleContext ι)
    (inner : (index : ι) → MultiHoleContext (arity index)) :
    holes (plug context inner) =
      (holes context).flatMap fun index => (holes (inner index)).map (Sigma.mk index) := by
  rw [plug, holes_bind]
  congr 1
  funext index
  exact holes_relabel (Sigma.mk index) (inner index)

/-! ## One-hole contexts -/

/-- A one-hole context as a context whose single index names its hole. -/
def ofOneHole : OneHoleContext → MultiHoleContext Unit
  | .hole => .hole ()
  | .apply constructor before inner after =>
      .apply constructor (before.map ofPattern ++ ofOneHole inner :: after.map ofPattern)
  | .lambda binderName inner => .lambda binderName (ofOneHole inner)
  | .multiLambda arity binderNames inner => .multiLambda arity binderNames (ofOneHole inner)
  | .substBody inner replacement => .subst (ofOneHole inner) (ofPattern replacement)
  | .substReplacement body inner => .subst (ofPattern body) (ofOneHole inner)
  | .collection collectionType before inner after rest =>
      .collection collectionType
        (before.map ofPattern ++ ofOneHole inner :: after.map ofPattern) rest

private theorem map_fill_ofPattern (filling : ι → Pattern) (patterns : List Pattern) :
    (patterns.map ofPattern).map (fill filling) = patterns := by
  rw [← ofPatternList_eq_map, ← fillList_eq_map]
  exact fillList_ofPatternList filling patterns

private theorem flatMap_holes_ofPattern (patterns : List Pattern) :
    (patterns.map (ofPattern : Pattern → MultiHoleContext ι)).flatMap holes = [] := by
  rw [← ofPatternList_eq_map, ← holesList_eq_flatMap]
  exact holesList_ofPatternList patterns

/-- **Filling agrees with plugging** a one-hole context. -/
theorem fill_ofOneHole (filling : Unit → Pattern) :
    ∀ context : OneHoleContext,
      fill filling (ofOneHole context) = context.fill (filling ())
  | .hole => rfl
  | .apply _ before inner after => by
      simp only [ofOneHole, fill, fillList_eq_map, List.map_append, List.map_cons,
        map_fill_ofPattern, fill_ofOneHole filling inner, OneHoleContext.fill]
  | .lambda _ inner => by
      simp only [ofOneHole, fill, fill_ofOneHole filling inner, OneHoleContext.fill]
  | .multiLambda _ _ inner => by
      simp only [ofOneHole, fill, fill_ofOneHole filling inner, OneHoleContext.fill]
  | .substBody inner replacement => by
      simp only [ofOneHole, fill, fill_ofOneHole filling inner, fill_ofPattern,
        OneHoleContext.fill]
  | .substReplacement body inner => by
      simp only [ofOneHole, fill, fill_ofOneHole filling inner, fill_ofPattern,
        OneHoleContext.fill]
  | .collection _ before inner after _ => by
      simp only [ofOneHole, fill, fillList_eq_map, List.map_append, List.map_cons,
        map_fill_ofPattern, fill_ofOneHole filling inner, OneHoleContext.fill]

/-- A one-hole context has one hole. -/
theorem holes_ofOneHole : ∀ context : OneHoleContext, holes (ofOneHole context) = [()]
  | .hole => rfl
  | .apply _ before inner after => by
      simp only [ofOneHole, holes, holesList_eq_flatMap, List.flatMap_append, List.flatMap_cons,
        flatMap_holes_ofPattern, holes_ofOneHole inner, List.nil_append, List.append_nil]
  | .lambda _ inner => by simp only [ofOneHole, holes, holes_ofOneHole inner]
  | .multiLambda _ _ inner => by simp only [ofOneHole, holes, holes_ofOneHole inner]
  | .substBody inner replacement => by
      simp only [ofOneHole, holes, holes_ofOneHole inner, holes_ofPattern, List.append_nil]
  | .substReplacement body inner => by
      simp only [ofOneHole, holes, holes_ofOneHole inner, holes_ofPattern, List.nil_append]
  | .collection _ before inner after _ => by
      simp only [ofOneHole, holes, holesList_eq_flatMap, List.flatMap_append, List.flatMap_cons,
        flatMap_holes_ofPattern, holes_ofOneHole inner, List.nil_append, List.append_nil]

/-! ## The one-hole context at a hole -/

/-- Changing the filling at an index that names no hole changes nothing. -/
theorem fill_update_of_not_mem [DecidableEq ι] (filling : ι → Pattern) {index : ι}
    (pattern : Pattern) {context : MultiHoleContext ι} (absent : index ∉ holes context) :
    fill (Function.update filling index pattern) context = fill filling context :=
  fill_congr context fun other membership =>
    Function.update_of_ne (fun same : other = index => absent (same ▸ membership)) pattern
      filling

theorem fillList_update_of_not_mem [DecidableEq ι] (filling : ι → Pattern) {index : ι}
    (pattern : Pattern) {contexts : List (MultiHoleContext ι)}
    (absent : index ∉ holesList contexts) :
    fillList (Function.update filling index pattern) contexts = fillList filling contexts :=
  fillList_congr contexts fun other membership =>
    Function.update_of_ne (fun same : other = index => absent (same ▸ membership)) pattern
      filling

mutual
/-- **The derivative at a hole.**  When an index names exactly one hole, the
context with every other hole filled is a one-hole context: as a function of
what is put at that index, filling is plugging into it. -/
theorem exists_oneHole [DecidableEq ι] (index : ι) (filling : ι → Pattern) :
    ∀ context : MultiHoleContext ι, (holes context).count index = 1 →
      ∃ focus : OneHoleContext, ∀ pattern,
        fill (Function.update filling index pattern) context = focus.fill pattern
  | .hole other, once => by
      have same : other = index := by
        by_contra distinct
        simp [holes, distinct] at once
      subst same
      exact ⟨.hole, fun pattern => by simp [fill]⟩
  | .bvar _, once => by simp [holes] at once
  | .fvar _, once => by simp [holes] at once
  | .apply constructor arguments, once => by
      obtain ⟨before, focus, after, filled⟩ := exists_oneHoleList index filling arguments once
      exact ⟨.apply constructor before focus after, fun pattern => by
        simp only [fill, filled pattern, OneHoleContext.fill]⟩
  | .lambda binderName body, once => by
      obtain ⟨focus, filled⟩ := exists_oneHole index filling body once
      exact ⟨.lambda binderName focus, fun pattern => by
        simp only [fill, filled pattern, OneHoleContext.fill]⟩
  | .multiLambda arity binderNames body, once => by
      obtain ⟨focus, filled⟩ := exists_oneHole index filling body once
      exact ⟨.multiLambda arity binderNames focus, fun pattern => by
        simp only [fill, filled pattern, OneHoleContext.fill]⟩
  | .subst body replacement, once => by
      simp only [holes, List.count_append] at once
      by_cases inBody : (holes body).count index = 1
      · have absent : index ∉ holes replacement := List.count_eq_zero.mp (by omega)
        obtain ⟨focus, filled⟩ := exists_oneHole index filling body inBody
        exact ⟨.substBody focus (fill filling replacement), fun pattern => by
          simp only [fill, filled pattern, fill_update_of_not_mem filling pattern absent,
            OneHoleContext.fill]⟩
      · have inReplacement : (holes replacement).count index = 1 := by omega
        have absent : index ∉ holes body := List.count_eq_zero.mp (by omega)
        obtain ⟨focus, filled⟩ := exists_oneHole index filling replacement inReplacement
        exact ⟨.substReplacement (fill filling body) focus, fun pattern => by
          simp only [fill, filled pattern, fill_update_of_not_mem filling pattern absent,
            OneHoleContext.fill]⟩
  | .collection collectionType elements rest, once => by
      obtain ⟨before, focus, after, filled⟩ := exists_oneHoleList index filling elements once
      exact ⟨.collection collectionType before focus after rest, fun pattern => by
        simp only [fill, filled pattern, OneHoleContext.fill]⟩

theorem exists_oneHoleList [DecidableEq ι] (index : ι) (filling : ι → Pattern) :
    ∀ contexts : List (MultiHoleContext ι), (holesList contexts).count index = 1 →
      ∃ (before : List Pattern) (focus : OneHoleContext) (after : List Pattern), ∀ pattern,
        fillList (Function.update filling index pattern) contexts =
          before ++ focus.fill pattern :: after
  | [], once => by simp [holesList] at once
  | context :: contexts, once => by
      simp only [holesList, List.count_append] at once
      by_cases inHead : (holes context).count index = 1
      · have absent : index ∉ holesList contexts := List.count_eq_zero.mp (by omega)
        obtain ⟨focus, filled⟩ := exists_oneHole index filling context inHead
        exact ⟨[], focus, fillList filling contexts, fun pattern => by
          simp only [fillList, filled pattern, fillList_update_of_not_mem filling pattern absent,
            List.nil_append]⟩
      · have inTail : (holesList contexts).count index = 1 := by omega
        have absent : index ∉ holes context := List.count_eq_zero.mp (by omega)
        obtain ⟨before, focus, after, filled⟩ := exists_oneHoleList index filling contexts inTail
        exact ⟨fill filling context :: before, focus, after, fun pattern => by
          simp only [fillList, filled pattern, fill_update_of_not_mem filling pattern absent,
            List.cons_append]⟩
end

/-! ## Linear contexts -/

/-- Every index names exactly one hole. -/
def Linear (context : MultiHoleContext ι) : Prop :=
  (holes context).Nodup ∧ ∀ index, index ∈ holes context

/-- In a linear context every index names exactly one hole. -/
theorem Linear.count_eq_one [DecidableEq ι] {context : MultiHoleContext ι}
    (linear : Linear context) (index : ι) : (holes context).count index = 1 :=
  List.count_eq_one_of_mem linear.1 (linear.2 index)

/-- **A linear context is a one-hole context at each of its holes**, once the
other holes are filled. -/
theorem Linear.exists_oneHole [DecidableEq ι] {context : MultiHoleContext ι}
    (linear : Linear context) (index : ι) (filling : ι → Pattern) :
    ∃ focus : OneHoleContext, ∀ pattern,
      fill (Function.update filling index pattern) context = focus.fill pattern :=
  MultiHoleContext.exists_oneHole index filling context (linear.count_eq_one index)

/-- A hole is linear in its one index. -/
theorem linear_hole : Linear (.hole () : MultiHoleContext Unit) :=
  ⟨by simp [holes], fun _ => by simp [holes]⟩

/-- A one-hole context is linear. -/
theorem linear_ofOneHole (context : OneHoleContext) : Linear (ofOneHole context) := by
  rw [Linear, holes_ofOneHole]
  exact ⟨by simp, fun _ => by simp⟩

/-- A pattern is a linear context with no index. -/
theorem linear_ofPattern (pattern : Pattern) :
    Linear (ofPattern pattern : MultiHoleContext Empty) := by
  rw [Linear, holes_ofPattern]
  exact ⟨List.nodup_nil, fun index => index.elim⟩

/-- A context that uses one hole twice is not linear: a context places what it
is given, it does not copy it. -/
theorem not_linear_of_duplicate (label : String) :
    ¬ Linear (.apply label [.hole (), .hole ()] : MultiHoleContext Unit) := by
  intro linear
  have nodup := linear.1
  simp [holes, holesList] at nodup

/-- Renaming the holes along a bijection keeps a context linear. -/
theorem Linear.relabel {context : MultiHoleContext ι} (linear : Linear context)
    {rename : ι → κ} (bijective : Function.Bijective rename) :
    Linear (relabel rename context) := by
  rw [Linear, holes_relabel]
  refine ⟨linear.1.map bijective.1, fun index => ?_⟩
  obtain ⟨source, rfl⟩ := bijective.2 index
  exact List.mem_map_of_mem (linear.2 source)

/-- **Plugging linear contexts into a linear context gives a linear
context.** -/
theorem Linear.plug {arity : ι → Type} {context : MultiHoleContext ι} (linear : Linear context)
    {inner : (index : ι) → MultiHoleContext (arity index)}
    (innerLinear : ∀ index, Linear (inner index)) :
    Linear (plug context inner) := by
  rw [Linear, holes_plug]
  refine ⟨?_, ?_⟩
  · rw [List.nodup_flatMap]
    refine ⟨fun index _ => (innerLinear index).1.map
      (fun first second same => by cases same; rfl), ?_⟩
    refine linear.1.imp ?_
    intro first second distinct position inFirst inSecond
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp inFirst
    obtain ⟨_, _, same⟩ := List.mem_map.mp inSecond
    exact distinct (congrArg Sigma.fst same).symm
  · rintro ⟨index, position⟩
    exact List.mem_flatMap.mpr ⟨index, linear.2 index,
      List.mem_map_of_mem ((innerLinear index).2 position)⟩

end MultiHoleContext

end Mettapedia.OSLF.MeTTaIL.DerivedContexts
