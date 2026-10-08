import Mettapedia.CategoryTheory.RelativeClosedSyntaxRegularity
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits

/-!
# Independent interpretation of relative closed expressions

An assignment supplies a base functor and meanings of individual fresh
objects and arrows. The structural evaluator uses the target's actual
products, function objects and equalizers. Arrow annotations are checked
against their independently evaluated endpoints. Equalizer lifts check the
complete candidate commutativity equation before constructing their value.

Declaration realization is local: it reads individual arrow headers and
individual authored equations. It contains no generated-judgment soundness,
whole-tree interpretation or free-extension universal property.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory

universe u v a w z

variable {C : Type u} [Category.{v} C] {symbols : Symbols.{a}}
variable {D : Type w} [Category.{z} D]

structure ArrowValue (D : Type w) [Category.{z} D] : Type (max w z) where
  source : D
  target : D
  arrow : source ⟶ target

namespace ArrowValue

def readAt (value : Option (ArrowValue D)) (source target : D) : Option (source ⟶ target) := by
  classical
  exact match value with
    | none => none
    | some supplied =>
      if sourceSame : supplied.source = source then
        if targetSame : supplied.target = target then
          some (eqToHom sourceSame.symm ≫ supplied.arrow ≫ eqToHom targetSame)
        else none
      else none

@[simp] theorem readAt_supplied {source target : D} (arrow : source ⟶ target) :
    readAt (some ⟨source, target, arrow⟩) source target = some arrow := by
  simp [readAt]

theorem readAt_endpoints {value : ArrowValue D} {source target : D}
    {arrow : source ⟶ target} (read : readAt (some value) source target = some arrow) :
    value.source = source ∧ value.target = target := by
  classical
  by_cases sourceSame : value.source = source
  · by_cases targetSame : value.target = target
    · exact ⟨sourceSame, targetSame⟩
    · simp [readAt, sourceSame, targetSame] at read
  · simp [readAt, sourceSame] at read

theorem readAt_value {value : ArrowValue D} {source target : D}
    {arrow : source ⟶ target} (read : readAt (some value) source target = some arrow) :
    value = ⟨source, target, arrow⟩ := by
  classical
  obtain ⟨sourceSame, targetSame⟩ := readAt_endpoints read
  cases value with
  | mk before after supplied =>
    dsimp at sourceSame targetSame
    subst before
    subst after
    have same := (readAt_supplied supplied).symm.trans read
    have actual := Option.some.inj same
    cases actual
    rfl

theorem arrow_injective {source target : D} {before after : source ⟶ target}
    (same : (⟨source, target, before⟩ : ArrowValue D) = ⟨source, target, after⟩) : before = after := by
  have checked := congrArg (fun value : ArrowValue D => readAt (some value) source target) same
  simpa only [readAt_supplied, Option.some.injEq] using checked

theorem readAt_eq_some {value : Option (ArrowValue D)} {source target : D}
    {arrow : source ⟶ target} (read : readAt value source target = some arrow) :
    value = some ⟨source, target, arrow⟩ := by
  cases value with
  | none => cases read
  | some value => exact congrArg some (readAt_value read)

end ArrowValue

structure Assignment (C : Type u) [Category.{v} C] (symbols : Symbols.{a})
    (D : Type w) [Category.{z} D] where
  base : C ⥤ D
  object : symbols.ObjectName → D
  arrow : symbols.ArrowName → ArrowValue D

variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]

def exchange (left right : D) : left ⊗ right ⟶ right ⊗ left :=
  CartesianMonoidalCategory.lift (CartesianMonoidalCategory.snd left right)
    (CartesianMonoidalCategory.fst left right)

def evaluation (argument result : D) : (argument ⟶[D] result) ⊗ argument ⟶ result :=
  exchange (argument ⟶[D] result) argument ≫ (ihom.ev argument).app result

def abstraction {context argument result : D} (body : context ⊗ argument ⟶ result) :
    context ⟶ (argument ⟶[D] result) :=
  MonoidalClosed.curry (exchange argument context ≫ body)

namespace Assignment

variable (assignment : Assignment C symbols D)

attribute [local instance] Classical.propDecidable

private def bindResult {α : Type u} {β : Type v} (value : Option α)
    (continuation : α → Option β) : Option β :=
  match value with
  | none => none
  | some actual => continuation actual

mutual

def evaluateObjectLift (assignment : Assignment C symbols D) :
    ObjectCode C symbols → ULift.{z} (Option D)
  | .base object => ⟨some (assignment.base.obj object)⟩
  | .name origin => ⟨some (assignment.object origin)⟩
  | .terminal => ⟨some (𝟙_ D)⟩
  | .product left right =>
      ⟨bindResult (assignment.evaluateObjectLift left).down (fun left =>
        bindResult (assignment.evaluateObjectLift right).down (fun right =>
          some (left ⊗ right)))⟩
  | .exponential argument result =>
      ⟨bindResult (assignment.evaluateObjectLift argument).down (fun argument =>
        bindResult (assignment.evaluateObjectLift result).down (fun result =>
          some (argument ⟶[D] result)))⟩
  | .equalizer source target before after =>
      ⟨bindResult (assignment.evaluateObjectLift source).down (fun source =>
        bindResult (assignment.evaluateObjectLift target).down (fun target =>
          bindResult (ArrowValue.readAt (assignment.evaluateArrow before) source target) (fun before =>
            bindResult (ArrowValue.readAt (assignment.evaluateArrow after) source target) (fun after =>
              some (equalizer before after)))))⟩

def evaluateArrow (assignment : Assignment C symbols D) : ArrowCode C symbols →
    Option (ArrowValue D)
  | .base arrow =>
      some ⟨assignment.base.obj _, assignment.base.obj _, assignment.base.map arrow⟩
  | .name origin => some (assignment.arrow origin)
  | .identity object =>
      bindResult (assignment.evaluateObjectLift object).down (fun object =>
        some ⟨object, object, 𝟙 object⟩)
  | .compose before after =>
      bindResult (assignment.evaluateArrow before) (fun before =>
        bindResult (assignment.evaluateArrow after) (fun after =>
          bindResult (ArrowValue.readAt (some after) before.target after.target) (fun actual =>
            some ⟨before.source, after.target, before.arrow ≫ actual⟩)))
  | .terminal source =>
      bindResult (assignment.evaluateObjectLift source).down (fun source =>
        some ⟨source, 𝟙_ D, CartesianMonoidalCategory.toUnit source⟩)
  | .first left right =>
      bindResult (assignment.evaluateObjectLift left).down (fun left =>
        bindResult (assignment.evaluateObjectLift right).down (fun right =>
          some ⟨left ⊗ right, left, CartesianMonoidalCategory.fst left right⟩))
  | .second left right =>
      bindResult (assignment.evaluateObjectLift left).down (fun left =>
        bindResult (assignment.evaluateObjectLift right).down (fun right =>
          some ⟨left ⊗ right, right, CartesianMonoidalCategory.snd left right⟩))
  | .pair before after =>
      bindResult (assignment.evaluateArrow before) (fun before =>
        bindResult (assignment.evaluateArrow after) (fun after =>
          bindResult (ArrowValue.readAt (some after) before.source after.target) (fun actual =>
            some ⟨before.source, before.target ⊗ after.target,
              CartesianMonoidalCategory.lift before.arrow actual⟩)))
  | .evaluation argument result =>
      bindResult (assignment.evaluateObjectLift argument).down (fun argument =>
        bindResult (assignment.evaluateObjectLift result).down (fun result =>
          some ⟨(argument ⟶[D] result) ⊗ argument, result, evaluation argument result⟩))
  | .curry context argument result body =>
      bindResult (assignment.evaluateObjectLift context).down (fun context =>
        bindResult (assignment.evaluateObjectLift argument).down (fun argument =>
          bindResult (assignment.evaluateObjectLift result).down (fun result =>
            bindResult (ArrowValue.readAt (assignment.evaluateArrow body) (context ⊗ argument) result)
              (fun body => some ⟨context, argument ⟶[D] result, abstraction body⟩))))
  | .equalizerArrow source target before after =>
      bindResult (assignment.evaluateObjectLift source).down (fun source =>
        bindResult (assignment.evaluateObjectLift target).down (fun target =>
          bindResult (ArrowValue.readAt (assignment.evaluateArrow before) source target) (fun before =>
            bindResult (ArrowValue.readAt (assignment.evaluateArrow after) source target) (fun after =>
              some ⟨equalizer before after, source, equalizer.ι before after⟩))))
  | .equalizerLift source target before after context candidate =>
      bindResult (assignment.evaluateObjectLift source).down (fun source =>
        bindResult (assignment.evaluateObjectLift target).down (fun target =>
          bindResult (assignment.evaluateObjectLift context).down (fun context =>
            bindResult (ArrowValue.readAt (assignment.evaluateArrow before) source target)
              (fun before =>
                bindResult (ArrowValue.readAt (assignment.evaluateArrow after) source target)
                  (fun after =>
                    bindResult (ArrowValue.readAt (assignment.evaluateArrow candidate) context source)
                      (fun candidate =>
                        if commutes : candidate ≫ before = candidate ≫ after then
                          some ⟨context, equalizer before after, equalizer.lift candidate commutes⟩
                        else none))))))

end

def evaluateObject (code : ObjectCode C symbols) : Option D :=
  (assignment.evaluateObjectLift code).down

@[simp] theorem evaluate_base_object (object : C) :
    assignment.evaluateObject (.base object) = some (assignment.base.obj object) := rfl

@[simp] theorem evaluate_object_name (origin : symbols.ObjectName) :
    assignment.evaluateObject (.name origin) = some (assignment.object origin) := rfl

@[simp] theorem evaluate_terminal_object :
    assignment.evaluateObject .terminal = some (𝟙_ D) := rfl

@[simp] theorem evaluate_base_arrow {source target : C} (arrow : source ⟶ target) :
    assignment.evaluateArrow (.base arrow) =
      some ⟨assignment.base.obj source, assignment.base.obj target, assignment.base.map arrow⟩ := rfl

@[simp] theorem evaluate_arrow_name (origin : symbols.ArrowName) :
    assignment.evaluateArrow (.name origin) = some (assignment.arrow origin) := rfl

theorem evaluate_product {left right : ObjectCode C symbols} {before after : D}
    (leftRead : assignment.evaluateObject left = some before)
    (rightRead : assignment.evaluateObject right = some after) :
    assignment.evaluateObject (.product left right) = some (before ⊗ after) := by
  change bindResult (assignment.evaluateObject left) (fun first =>
    bindResult (assignment.evaluateObject right) (fun second => some (first ⊗ second))) = _
  rw [leftRead, rightRead]
  rfl

theorem evaluate_exponential {argument result : ObjectCode C symbols} {before after : D}
    (argumentRead : assignment.evaluateObject argument = some before)
    (resultRead : assignment.evaluateObject result = some after) :
    assignment.evaluateObject (.exponential argument result) = some (before ⟶[D] after) := by
  change bindResult (assignment.evaluateObject argument) (fun first =>
    bindResult (assignment.evaluateObject result) (fun second => some (first ⟶[D] second))) = _
  rw [argumentRead, resultRead]
  rfl

theorem evaluate_equalizer {source target : ObjectCode C symbols}
    {before after : ArrowCode C symbols} {first second : D}
    (f g : first ⟶ second)
    (sourceRead : assignment.evaluateObject source = some first)
    (targetRead : assignment.evaluateObject target = some second)
    (beforeRead : assignment.evaluateArrow before = some ⟨first, second, f⟩)
    (afterRead : assignment.evaluateArrow after = some ⟨first, second, g⟩) :
    assignment.evaluateObject (.equalizer source target before after) = some (equalizer f g) := by
  change bindResult (assignment.evaluateObject source) (fun first =>
    bindResult (assignment.evaluateObject target) (fun second =>
      bindResult (ArrowValue.readAt (assignment.evaluateArrow before) first second) (fun f =>
        bindResult (ArrowValue.readAt (assignment.evaluateArrow after) first second) (fun g =>
          some (equalizer f g))))) = _
  rw [sourceRead, targetRead]
  simp only [bindResult, beforeRead, afterRead, ArrowValue.readAt_supplied]

theorem evaluate_identity {code : ObjectCode C symbols} {object : D}
    (objectRead : assignment.evaluateObject code = some object) :
    assignment.evaluateArrow (.identity code) = some ⟨object, object, 𝟙 object⟩ := by
  change bindResult (assignment.evaluateObject code) (fun object =>
    some (⟨object, object, 𝟙 object⟩ : ArrowValue D)) = _
  rw [objectRead]
  rfl

theorem evaluate_compose {before after : ArrowCode C symbols} {source middle target : D}
    (f : source ⟶ middle) (g : middle ⟶ target)
    (beforeRead : assignment.evaluateArrow before = some ⟨source, middle, f⟩)
    (afterRead : assignment.evaluateArrow after = some ⟨middle, target, g⟩) :
    assignment.evaluateArrow (.compose before after) = some ⟨source, target, f ≫ g⟩ := by
  change bindResult (assignment.evaluateArrow before) (fun f =>
    bindResult (assignment.evaluateArrow after) (fun g =>
      bindResult (ArrowValue.readAt (some g) f.target g.target) (fun actual =>
        some (⟨f.source, g.target, f.arrow ≫ actual⟩ : ArrowValue D)))) = _
  rw [beforeRead, afterRead]
  simp only [bindResult, ArrowValue.readAt_supplied]

theorem evaluate_terminal_arrow {code : ObjectCode C symbols} {source : D}
    (sourceRead : assignment.evaluateObject code = some source) :
    assignment.evaluateArrow (.terminal code) =
      some ⟨source, 𝟙_ D, CartesianMonoidalCategory.toUnit source⟩ := by
  change bindResult (assignment.evaluateObject code) (fun source =>
    some (⟨source, 𝟙_ D, CartesianMonoidalCategory.toUnit source⟩ : ArrowValue D)) = _
  rw [sourceRead]
  rfl

theorem evaluate_first {left right : ObjectCode C symbols} {before after : D}
    (leftRead : assignment.evaluateObject left = some before)
    (rightRead : assignment.evaluateObject right = some after) :
    assignment.evaluateArrow (.first left right) =
      some ⟨before ⊗ after, before, CartesianMonoidalCategory.fst before after⟩ := by
  change bindResult (assignment.evaluateObject left) (fun first =>
    bindResult (assignment.evaluateObject right) (fun second =>
      some (⟨first ⊗ second, first, CartesianMonoidalCategory.fst first second⟩ : ArrowValue D))) = _
  rw [leftRead, rightRead]
  rfl

theorem evaluate_second {left right : ObjectCode C symbols} {before after : D}
    (leftRead : assignment.evaluateObject left = some before)
    (rightRead : assignment.evaluateObject right = some after) :
    assignment.evaluateArrow (.second left right) =
      some ⟨before ⊗ after, after, CartesianMonoidalCategory.snd before after⟩ := by
  change bindResult (assignment.evaluateObject left) (fun first =>
    bindResult (assignment.evaluateObject right) (fun second =>
      some (⟨first ⊗ second, second, CartesianMonoidalCategory.snd first second⟩ : ArrowValue D))) = _
  rw [leftRead, rightRead]
  rfl

theorem evaluate_pair {before after : ArrowCode C symbols} {source left right : D}
    (f : source ⟶ left) (g : source ⟶ right)
    (beforeRead : assignment.evaluateArrow before = some ⟨source, left, f⟩)
    (afterRead : assignment.evaluateArrow after = some ⟨source, right, g⟩) :
    assignment.evaluateArrow (.pair before after) =
      some ⟨source, left ⊗ right, CartesianMonoidalCategory.lift f g⟩ := by
  change bindResult (assignment.evaluateArrow before) (fun f =>
    bindResult (assignment.evaluateArrow after) (fun g =>
      bindResult (ArrowValue.readAt (some g) f.source g.target) (fun actual =>
        some (⟨f.source, f.target ⊗ g.target,
          CartesianMonoidalCategory.lift f.arrow actual⟩ : ArrowValue D)))) = _
  rw [beforeRead, afterRead]
  simp only [bindResult, ArrowValue.readAt_supplied]

theorem evaluate_evaluation {argument result : ObjectCode C symbols} {before after : D}
    (argumentRead : assignment.evaluateObject argument = some before)
    (resultRead : assignment.evaluateObject result = some after) :
    assignment.evaluateArrow (.evaluation argument result) =
      some ⟨(before ⟶[D] after) ⊗ before, after, evaluation before after⟩ := by
  change bindResult (assignment.evaluateObject argument) (fun first =>
    bindResult (assignment.evaluateObject result) (fun second =>
      some (⟨(first ⟶[D] second) ⊗ first, second, evaluation first second⟩ : ArrowValue D))) = _
  rw [argumentRead, resultRead]
  rfl

theorem evaluate_abstraction {context argument result : ObjectCode C symbols}
    {body : ArrowCode C symbols} {Γ A B : D} (f : Γ ⊗ A ⟶ B)
    (contextRead : assignment.evaluateObject context = some Γ)
    (argumentRead : assignment.evaluateObject argument = some A)
    (resultRead : assignment.evaluateObject result = some B)
    (bodyRead : assignment.evaluateArrow body = some ⟨Γ ⊗ A, B, f⟩) :
    assignment.evaluateArrow (.curry context argument result body) =
      some ⟨Γ, A ⟶[D] B, abstraction f⟩ := by
  change bindResult (assignment.evaluateObject context) (fun Γ =>
    bindResult (assignment.evaluateObject argument) (fun A =>
      bindResult (assignment.evaluateObject result) (fun B =>
        bindResult (ArrowValue.readAt (assignment.evaluateArrow body) (Γ ⊗ A) B)
          (fun f => some (⟨Γ, A ⟶[D] B, abstraction f⟩ : ArrowValue D))))) = _
  rw [contextRead, argumentRead, resultRead]
  simp only [bindResult, bodyRead, ArrowValue.readAt_supplied]

theorem evaluate_equalizer_arrow {source target : ObjectCode C symbols}
    {before after : ArrowCode C symbols} {first second : D}
    (f g : first ⟶ second)
    (sourceRead : assignment.evaluateObject source = some first)
    (targetRead : assignment.evaluateObject target = some second)
    (beforeRead : assignment.evaluateArrow before = some ⟨first, second, f⟩)
    (afterRead : assignment.evaluateArrow after = some ⟨first, second, g⟩) :
    assignment.evaluateArrow (.equalizerArrow source target before after) =
      some ⟨equalizer f g, first, equalizer.ι f g⟩ := by
  change bindResult (assignment.evaluateObject source) (fun first =>
    bindResult (assignment.evaluateObject target) (fun second =>
      bindResult (ArrowValue.readAt (assignment.evaluateArrow before) first second) (fun f =>
        bindResult (ArrowValue.readAt (assignment.evaluateArrow after) first second) (fun g =>
          some (⟨equalizer f g, first, equalizer.ι f g⟩ : ArrowValue D))))) = _
  rw [sourceRead, targetRead]
  simp only [bindResult, beforeRead, afterRead, ArrowValue.readAt_supplied]

theorem evaluate_equalizer_lift {source target context : ObjectCode C symbols}
    {before after candidate : ArrowCode C symbols} {first second Γ : D}
    (f g : first ⟶ second) (h : Γ ⟶ first) (commutes : h ≫ f = h ≫ g)
    (sourceRead : assignment.evaluateObject source = some first)
    (targetRead : assignment.evaluateObject target = some second)
    (contextRead : assignment.evaluateObject context = some Γ)
    (beforeRead : assignment.evaluateArrow before = some ⟨first, second, f⟩)
    (afterRead : assignment.evaluateArrow after = some ⟨first, second, g⟩)
    (candidateRead : assignment.evaluateArrow candidate = some ⟨Γ, first, h⟩) :
    assignment.evaluateArrow (.equalizerLift source target before after context candidate) =
      some ⟨Γ, equalizer f g, equalizer.lift h commutes⟩ := by
  change bindResult (assignment.evaluateObject source) (fun first =>
    bindResult (assignment.evaluateObject target) (fun second =>
      bindResult (assignment.evaluateObject context) (fun Γ =>
        bindResult (ArrowValue.readAt (assignment.evaluateArrow before) first second) (fun f =>
          bindResult (ArrowValue.readAt (assignment.evaluateArrow after) first second) (fun g =>
            bindResult (ArrowValue.readAt (assignment.evaluateArrow candidate) Γ first) (fun h =>
              if same : h ≫ f = h ≫ g then
                some (⟨Γ, equalizer f g, equalizer.lift h same⟩ : ArrowValue D) else none)))))) = _
  rw [sourceRead, targetRead, contextRead]
  simp only [bindResult, beforeRead, afterRead, candidateRead,
    ArrowValue.readAt_supplied, dif_pos commutes]

theorem evaluate_equalizer_shape {source target : ObjectCode C symbols}
    {before after : ArrowCode C symbols} {object : D}
    (read : assignment.evaluateObject (.equalizer source target before after) = some object) :
    ∃ first second : D, ∃ f g : first ⟶ second,
      object = equalizer f g ∧
      assignment.evaluateArrow (.equalizerArrow source target before after) =
        some ⟨equalizer f g, first, equalizer.ι f g⟩ := by
  change bindResult (assignment.evaluateObject source) (fun first =>
    bindResult (assignment.evaluateObject target) (fun second =>
      bindResult (ArrowValue.readAt (assignment.evaluateArrow before) first second) (fun f =>
        bindResult (ArrowValue.readAt (assignment.evaluateArrow after) first second) (fun g =>
          some (equalizer f g))))) = some object at read
  cases sourceRead : assignment.evaluateObject source with
  | none => simp only [sourceRead, bindResult] at read; cases read
  | some first =>
    cases targetRead : assignment.evaluateObject target with
    | none => simp only [sourceRead, targetRead, bindResult] at read; cases read
    | some second =>
      cases beforeRead : ArrowValue.readAt (assignment.evaluateArrow before) first second with
      | none => simp only [sourceRead, targetRead, bindResult, beforeRead] at read; cases read
      | some f =>
        cases afterRead : ArrowValue.readAt (assignment.evaluateArrow after) first second with
        | none =>
          simp only [sourceRead, targetRead, bindResult, beforeRead, afterRead] at read
          cases read
        | some g =>
          simp only [sourceRead, targetRead, bindResult, beforeRead, afterRead] at read
          refine ⟨first, second, f, g, (Option.some.inj read).symm, ?_⟩
          change bindResult (assignment.evaluateObject source) (fun first =>
            bindResult (assignment.evaluateObject target) (fun second =>
              bindResult (ArrowValue.readAt (assignment.evaluateArrow before) first second) (fun f =>
                bindResult (ArrowValue.readAt (assignment.evaluateArrow after) first second) (fun g =>
                  some (⟨equalizer f g, first, equalizer.ι f g⟩ : ArrowValue D))))) = _
          rw [sourceRead, targetRead]
          simp only [bindResult, beforeRead, afterRead]

end Assignment

structure Realization (signature : Signature (C := C) (symbols := symbols))
    (assignment : Assignment C symbols D) : Prop where
  source (origin : symbols.ArrowName) :
    assignment.evaluateObject (signature.source origin) = some (assignment.arrow origin).source
  target (origin : symbols.ArrowName) :
    assignment.evaluateObject (signature.target origin) = some (assignment.arrow origin).target
  equation (origin : symbols.EquationName) : ∃ value : ArrowValue D,
    assignment.evaluateObject (signature.equationSource origin) = some value.source ∧
    assignment.evaluateObject (signature.equationTarget origin) = some value.target ∧
    assignment.evaluateArrow (signature.left origin) = some value ∧
    assignment.evaluateArrow (signature.right origin) = some value

def Interprets (assignment : Assignment C symbols D) : Judgment C symbols → Prop
  | .object code => ∃ value, assignment.evaluateObject code = some value
  | .arrow source target code => ∃ value : ArrowValue D,
      assignment.evaluateObject source = some value.source ∧
      assignment.evaluateObject target = some value.target ∧
      assignment.evaluateArrow code = some value
  | .equation source target before after => ∃ value : ArrowValue D,
      assignment.evaluateObject source = some value.source ∧
      assignment.evaluateObject target = some value.target ∧
      assignment.evaluateArrow before = some value ∧
      assignment.evaluateArrow after = some value

namespace Interprets

theorem arrowAt {assignment : Assignment C symbols D} {source target : ObjectCode C symbols}
    {code : ArrowCode C symbols} {first second : D}
    (interpreted : Interprets assignment (.arrow source target code))
    (sourceRead : assignment.evaluateObject source = some first)
    (targetRead : assignment.evaluateObject target = some second) :
    ∃ arrow : first ⟶ second, assignment.evaluateArrow code = some ⟨first, second, arrow⟩ := by
  obtain ⟨value, sourceValue, targetValue, read⟩ := interpreted
  have sourceSame := Option.some.inj (sourceValue.symm.trans sourceRead)
  have targetSame := Option.some.inj (targetValue.symm.trans targetRead)
  cases value with
  | mk before after arrow =>
    dsimp at sourceSame targetSame
    subst before
    subst after
    exact ⟨arrow, read⟩

theorem equationAt {assignment : Assignment C symbols D} {source target : ObjectCode C symbols}
    {before after : ArrowCode C symbols} {first second : D}
    (interpreted : Interprets assignment (.equation source target before after))
    (sourceRead : assignment.evaluateObject source = some first)
    (targetRead : assignment.evaluateObject target = some second) :
    ∃ arrow : first ⟶ second,
      assignment.evaluateArrow before = some ⟨first, second, arrow⟩ ∧
      assignment.evaluateArrow after = some ⟨first, second, arrow⟩ := by
  obtain ⟨value, sourceValue, targetValue, beforeRead, afterRead⟩ := interpreted
  have sourceSame := Option.some.inj (sourceValue.symm.trans sourceRead)
  have targetSame := Option.some.inj (targetValue.symm.trans targetRead)
  cases value with
  | mk source target arrow =>
    dsimp at sourceSame targetSame
    subst source
    subst target
    exact ⟨arrow, beforeRead, afterRead⟩

theorem equal_arrows {assignment : Assignment C symbols D} {source target : ObjectCode C symbols}
    {before after : ArrowCode C symbols} {first second : D} (f g : first ⟶ second)
    (interpreted : Interprets assignment (.equation source target before after))
    (beforeRead : assignment.evaluateArrow before = some ⟨first, second, f⟩)
    (afterRead : assignment.evaluateArrow after = some ⟨first, second, g⟩) : f = g := by
  obtain ⟨value, _sourceValue, _targetValue, left, right⟩ := interpreted
  have same := (beforeRead.symm.trans left).trans (right.symm.trans afterRead)
  exact ArrowValue.arrow_injective (Option.some.inj same)

end Interprets

end Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation
