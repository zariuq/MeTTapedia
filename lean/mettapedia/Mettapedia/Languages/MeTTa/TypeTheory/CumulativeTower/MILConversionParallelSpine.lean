import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.MILConversionParallel

/-!
# Rigid application spines in completed parallel development

Partial eliminator applications and fully applied constructors have no root
contraction. Parallel development therefore retains their names and recovers
the development of each actual argument. These inversion lemmas distinguish
that structural fact from unrestricted inversion of arbitrary applications.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace MILConversionParallel

open Presentation IntrinsicMILHypothesis

variable {n : Nat}

/-- Arguments are stored outermost first, so removing a cons removes the
outer application directly. -/
def spine (name : DeclName) : List (Tower.Tm n) → Tower.Tm n
  | [] => .const name
  | argument :: rest => .app (spine name rest) argument

def spineHead : Tower.Tm n → Option DeclName
  | .const name => some name
  | .app function _ => spineHead function
  | _ => none

def spineDepth : Tower.Tm n → Nat
  | .app function _ => spineDepth function + 1
  | _ => 0

theorem spine_injective (name : DeclName) : Function.Injective (spine (n := n) name) := by
  intro first
  induction first with
  | nil =>
      intro second equality
      cases second with
      | nil => rfl
      | cons _ _ => cases equality
  | cons argument rest ih =>
      intro second equality
      cases second with
      | nil => cases equality
      | cons argument' rest' =>
          obtain ⟨tail, head⟩ := Tm.app.inj equality
          exact congrArg₂ List.cons head (ih tail)

@[simp] theorem spineHead_spine (name : DeclName) (arguments : List (Tower.Tm n)) :
    spineHead (spine name arguments) = some name := by
  induction arguments with
  | nil => rfl
  | cons _ _ ih => exact ih

@[simp] theorem spineDepth_spine (name : DeclName) (arguments : List (Tower.Tm n)) :
    spineDepth (spine name arguments) = arguments.length := by
  induction arguments with
  | nil => rfl
  | cons _ _ ih => exact congrArg (fun count => count + 1) ih

private theorem spine_inversion_aux {source target : Tower.Tm n} (parallel : Par source target) :
    ∀ name arguments, source = spine name arguments →
      (name ≠ eliminateName ∨ arguments.length < 8) →
      ∃ arguments', target = spine name arguments' ∧ List.Forall₂ Par arguments arguments' := by
  induction parallel with
  | const original =>
      intro name arguments equality _
      cases arguments with
      | nil => cases equality; exact ⟨[], rfl, .nil⟩
      | cons argument rest => cases equality
  | @app n function function' argument argument' functionStep argumentStep ihFunction _ =>
      intro name arguments equality rigid
      cases arguments with
      | nil => cases equality
      | cons first rest =>
          cases equality
          have smaller : name ≠ eliminateName ∨ rest.length < 8 := by
            rcases rigid with different | short
            · exact .inl different
            · exact .inr (by simpa only [List.length_cons] using Nat.lt_of_succ_lt short)
          obtain ⟨rest', shape, arguments⟩ := ihFunction name rest rfl smaller
          exact ⟨argument' :: rest', by simp only [spine, shape], .cons argumentStep arguments⟩
  | primitive =>
      intro name arguments equality rigid
      have names : eliminateName = name := by
        simpa only [eliminateApp, spineHead, spineHead_spine, Option.some.injEq] using
          congrArg spineHead equality
      have counts : 8 = arguments.length := by
        simpa only [eliminateApp, spineDepth, spineDepth_spine] using congrArg spineDepth equality
      rcases rigid with different | short
      · exact False.elim (different names.symm)
      · omega
  | chain =>
      intro name arguments equality rigid
      have names : eliminateName = name := by
        simpa only [eliminateApp, spineHead, spineHead_spine, Option.some.injEq] using
          congrArg spineHead equality
      have counts : 8 = arguments.length := by
        simpa only [eliminateApp, spineDepth, spineDepth_spine] using congrArg spineDepth equality
      rcases rigid with different | short
      · exact False.elim (different names.symm)
      · omega
  | _ =>
      intro name arguments equality _
      have impossible := congrArg spineHead equality
      simp only [spineHead, spineHead_spine] at impossible
      cases impossible

theorem spine_inversion (name : DeclName) (arguments : List (Tower.Tm n))
    (rigid : name ≠ eliminateName ∨ arguments.length < 8)
    {target : Tower.Tm n} (parallel : Par (spine name arguments) target) :
    ∃ arguments', target = spine name arguments' ∧ List.Forall₂ Par arguments arguments' :=
  spine_inversion_aux parallel name arguments rfl rigid

def eliminatePrefix (sorts primitives motive primitiveCase chainCase source target : Tower.Tm n) :
    Tower.Tm n := spine eliminateName [target, source, chainCase, primitiveCase, motive, primitives, sorts]

theorem par_eliminatePrefix
    {sorts primitives motive primitiveCase chainCase source target
      sorts' primitives' motive' primitiveCase' chainCase' source' target' : Tower.Tm n}
    (s : Par sorts sorts') (p : Par primitives primitives') (motiveStep : Par motive motive')
    (pc : Par primitiveCase primitiveCase') (cc : Par chainCase chainCase')
    (x : Par source source') (y : Par target target') :
    Par (eliminatePrefix sorts primitives motive primitiveCase chainCase source target)
      (eliminatePrefix sorts' primitives' motive' primitiveCase' chainCase' source' target') :=
  .app (.app (.app (.app (.app (.app (.app (.const _) s) p) motiveStep) pc) cc) x) y

theorem par_primitiveApp
    {sorts primitives source target symbol sorts' primitives' source' target' symbol' : Tower.Tm n}
    (s : Par sorts sorts') (p : Par primitives primitives') (x : Par source source')
    (y : Par target target') (z : Par symbol symbol') :
    Par (primitiveApp sorts primitives source target symbol)
      (primitiveApp sorts' primitives' source' target' symbol') :=
  .app (.app (.app (.app (.app (.const _) s) p) x) y) z

theorem par_chainApp
    {sorts primitives source middle target earlier later
      sorts' primitives' source' middle' target' earlier' later' : Tower.Tm n}
    (s : Par sorts sorts') (p : Par primitives primitives') (x : Par source source')
    (m : Par middle middle') (y : Par target target')
    (first : Par earlier earlier') (second : Par later later') :
    Par (chainApp sorts primitives source middle target earlier later)
      (chainApp sorts' primitives' source' middle' target' earlier' later') :=
  .app (.app (.app (.app (.app (.app (.app (.const _) s) p) x) m) y) first) second

theorem eliminatePrefix_inversion
    {sorts primitives motive primitiveCase chainCase source target result : Tower.Tm n}
    (parallel : Par (eliminatePrefix sorts primitives motive primitiveCase chainCase source target) result) :
    ∃ sorts' primitives' motive' primitiveCase' chainCase' source' target',
      result = eliminatePrefix sorts' primitives' motive' primitiveCase' chainCase' source' target' ∧
      Par sorts sorts' ∧ Par primitives primitives' ∧ Par motive motive' ∧
      Par primitiveCase primitiveCase' ∧ Par chainCase chainCase' ∧
      Par source source' ∧ Par target target' := by
  obtain ⟨arguments, shape, argumentSteps⟩ := spine_inversion eliminateName
    [target, source, chainCase, primitiveCase, motive, primitives, sorts]
    (.inr (by simp only [List.length_cons, List.length_nil]; decide)) parallel
  cases argumentSteps with | cons targetStep rest =>
    cases rest with | cons sourceStep rest =>
      cases rest with | cons chainStep rest =>
        cases rest with | cons primitiveStep rest =>
          cases rest with | cons motiveStep rest =>
            cases rest with | cons primitivesStep rest =>
              cases rest with | cons sortsStep rest =>
                cases rest
                exact ⟨_, _, _, _, _, _, _, shape, sortsStep, primitivesStep, motiveStep,
                  primitiveStep, chainStep, sourceStep, targetStep⟩

theorem primitiveApp_inversion
    {sorts primitives source target symbol result : Tower.Tm n}
    (parallel : Par (primitiveApp sorts primitives source target symbol) result) :
    ∃ sorts' primitives' source' target' symbol',
      result = primitiveApp sorts' primitives' source' target' symbol' ∧
      Par sorts sorts' ∧ Par primitives primitives' ∧ Par source source' ∧
      Par target target' ∧ Par symbol symbol' := by
  obtain ⟨arguments, shape, argumentSteps⟩ :=
    spine_inversion primitiveName [symbol, target, source, primitives, sorts]
      (.inl (by decide)) parallel
  cases argumentSteps with | cons symbolStep rest =>
    cases rest with | cons targetStep rest =>
      cases rest with | cons sourceStep rest =>
        cases rest with | cons primitivesStep rest =>
          cases rest with | cons sortsStep rest =>
            cases rest
            exact ⟨_, _, _, _, _, shape, sortsStep, primitivesStep, sourceStep, targetStep, symbolStep⟩

theorem chainApp_inversion
    {sorts primitives source middle target earlier later result : Tower.Tm n}
    (parallel : Par (chainApp sorts primitives source middle target earlier later) result) :
    ∃ sorts' primitives' source' middle' target' earlier' later',
      result = chainApp sorts' primitives' source' middle' target' earlier' later' ∧
      Par sorts sorts' ∧ Par primitives primitives' ∧ Par source source' ∧
      Par middle middle' ∧ Par target target' ∧ Par earlier earlier' ∧ Par later later' := by
  obtain ⟨arguments, shape, argumentSteps⟩ :=
    spine_inversion chainName [later, earlier, target, middle, source, primitives, sorts]
      (.inl (by decide)) parallel
  cases argumentSteps with | cons laterStep rest =>
    cases rest with | cons earlierStep rest =>
      cases rest with | cons targetStep rest =>
        cases rest with | cons middleStep rest =>
          cases rest with | cons sourceStep rest =>
            cases rest with | cons primitivesStep rest =>
              cases rest with | cons sortsStep rest =>
                cases rest
                exact ⟨_, _, _, _, _, _, _, shape, sortsStep, primitivesStep, sourceStep,
                  middleStep, targetStep, earlierStep, laterStep⟩

theorem lam_inversion {body : Tower.Tm (n + 1)} {target : Tower.Tm n}
    (parallel : Par (.lam body) target) :
    ∃ body', target = .lam body' ∧ Par body body' := by
  cases parallel with | lam inner => exact ⟨_, rfl, inner⟩

theorem pair_inversion {first second target : Tower.Tm n}
    (parallel : Par (.pair first second) target) :
    ∃ first' second', target = .pair first' second' ∧ Par first first' ∧ Par second second' := by
  cases parallel with | pair firstStep secondStep => exact ⟨_, _, rfl, firstStep, secondStep⟩

#print axioms spine_injective
#print axioms spineHead_spine
#print axioms spineDepth_spine
#print axioms spine_inversion
#print axioms par_eliminatePrefix
#print axioms par_primitiveApp
#print axioms par_chainApp
#print axioms eliminatePrefix_inversion
#print axioms primitiveApp_inversion
#print axioms chainApp_inversion
#print axioms lam_inversion
#print axioms pair_inversion

end MILConversionParallel
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
