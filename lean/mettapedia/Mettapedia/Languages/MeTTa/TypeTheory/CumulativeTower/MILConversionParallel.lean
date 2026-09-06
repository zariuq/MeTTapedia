import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.MILConversionCompletion

/-!
# Parallel development with retained native metadata coherence

The auxiliary parallel relation develops selected arguments while retaining
authored conversion evidence for duplicated metadata. Its contractions are
sound for authored conversion; they are not claimed to be single runtime
steps. Primitive and chain branches retain their actual, distinct reducts.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace MILConversionParallel

open Presentation IntrinsicMILHypothesis MILConversionCompletion

inductive Par : {n : Nat} → Tower.Tm n → Tower.Tm n → Prop where
  | var {n : Nat} (index : Fin n) : Par (.var index) (.var index)
  | const {n : Nat} (name : DeclName) : Par (.const name : Tower.Tm n) (.const name)
  | head {n : Nat} (value : Tower.Head) : Par (.head value : Tower.Tm n) (.head value)
  | headRel {n : Nat} {left right : Tower.Head} :
      Tower.HeadEq left right → Par (.head left : Tower.Tm n) (.head right)
  | pi {n : Nat} {domain domain' : Tower.Tm n} {codomain codomain' : Tower.Tm (n + 1)} :
      Par domain domain' → Par codomain codomain' →
        Par (.pi domain codomain) (.pi domain' codomain')
  | sigma {n : Nat} {domain domain' : Tower.Tm n} {codomain codomain' : Tower.Tm (n + 1)} :
      Par domain domain' → Par codomain codomain' →
        Par (.sigma domain codomain) (.sigma domain' codomain')
  | id {n : Nat} {type type' left left' right right' : Tower.Tm n} :
      Par type type' → Par left left' → Par right right' →
        Par (.id type left right) (.id type' left' right')
  | lam {n : Nat} {body body' : Tower.Tm (n + 1)} : Par body body' → Par (.lam body) (.lam body')
  | app {n : Nat} {function function' argument argument' : Tower.Tm n} :
      Par function function' → Par argument argument' →
        Par (.app function argument) (.app function' argument')
  | pair {n : Nat} {first first' second second' : Tower.Tm n} :
      Par first first' → Par second second' → Par (.pair first second) (.pair first' second')
  | fst {n : Nat} {pair pair' : Tower.Tm n} : Par pair pair' → Par (.fst pair) (.fst pair')
  | snd {n : Nat} {pair pair' : Tower.Tm n} : Par pair pair' → Par (.snd pair) (.snd pair')
  | refl {n : Nat} {term term' : Tower.Tm n} : Par term term' → Par (.refl term) (.refl term')
  | betaPi {n : Nat} {body body' : Tower.Tm (n + 1)} {argument argument' : Tower.Tm n} :
      Par body body' → Par argument argument' →
        Par (.app (.lam body) argument) (inst0 argument' body')
  | betaSigmaFst {n : Nat} {first first' second second' : Tower.Tm n} :
      Par first first' → Par second second' → Par (.fst (.pair first second)) first'
  | betaSigmaSnd {n : Nat} {first first' second second' : Tower.Tm n} :
      Par first first' → Par second second' → Par (.snd (.pair first second)) second'
  | primitive {n : Nat} {sorts primitives motive primitiveCase chainCase source target symbol
      sorts' primitives' motive' primitiveCase' chainCase' source' target' symbol'
      innerSorts innerPrimitives innerSource innerTarget : Tower.Tm n} :
      AuthoredConv innerSorts sorts → AuthoredConv innerPrimitives primitives →
      AuthoredConv innerSource source → AuthoredConv innerTarget target →
      Par sorts sorts' → Par primitives primitives' → Par motive motive' →
      Par primitiveCase primitiveCase' → Par chainCase chainCase' →
      Par source source' → Par target target' → Par symbol symbol' →
      Par
        (eliminateApp sorts primitives motive primitiveCase chainCase source target
          (primitiveApp innerSorts innerPrimitives innerSource innerTarget symbol))
        (.app (.app (.app primitiveCase' source') target') symbol')
  | chain {n : Nat} {sorts primitives motive primitiveCase chainCase source middle target earlier later
      sorts' primitives' motive' primitiveCase' chainCase' source' middle' target' earlier' later'
      innerSorts innerPrimitives innerSource innerTarget : Tower.Tm n} :
      AuthoredConv innerSorts sorts → AuthoredConv innerPrimitives primitives →
      AuthoredConv innerSource source → AuthoredConv innerTarget target →
      Par sorts sorts' → Par primitives primitives' → Par motive motive' →
      Par primitiveCase primitiveCase' → Par chainCase chainCase' →
      Par source source' → Par middle middle' → Par target target' →
      Par earlier earlier' → Par later later' →
      Par
        (eliminateApp sorts primitives motive primitiveCase chainCase source target
          (chainApp innerSorts innerPrimitives innerSource middle innerTarget earlier later))
        (.app
          (.app (.app (.app (.app (.app (.app chainCase' source') middle') target') earlier') later')
            (eliminateApp sorts' primitives' motive' primitiveCase' chainCase' source' middle' earlier'))
          (eliminateApp sorts' primitives' motive' primitiveCase' chainCase' middle' target' later'))

theorem par_refl {n : Nat} (term : Tower.Tm n) : Par term term := by
  induction term with
  | var index => exact .var index
  | const name => exact .const name
  | head value => exact .head value
  | pi _ _ first second => exact .pi first second
  | sigma _ _ first second => exact .sigma first second
  | id _ _ _ first second third => exact .id first second third
  | lam _ inner => exact .lam inner
  | app _ _ first second => exact .app first second
  | pair _ _ first second => exact .pair first second
  | fst _ inner => exact .fst inner
  | snd _ inner => exact .snd inner
  | refl _ inner => exact .refl inner

theorem eliminateApp_congr {n : Nat}
    {sorts primitives motive primitiveCase chainCase source target hypothesis
      sorts' primitives' motive' primitiveCase' chainCase' source' target' hypothesis' : Tower.Tm n}
    (first : AuthoredConv sorts sorts') (second : AuthoredConv primitives primitives')
    (third : AuthoredConv motive motive') (fourth : AuthoredConv primitiveCase primitiveCase')
    (fifth : AuthoredConv chainCase chainCase') (sixth : AuthoredConv source source')
    (seventh : AuthoredConv target target') (eighth : AuthoredConv hypothesis hypothesis') :
    AuthoredConv (eliminateApp sorts primitives motive primitiveCase chainCase source target hypothesis)
      (eliminateApp sorts' primitives' motive' primitiveCase' chainCase' source' target' hypothesis') :=
  Conv.congApp (Conv.congApp (Conv.congApp (Conv.congApp (Conv.congApp
    (Conv.congApp (Conv.congApp (Conv.congApp (.refl _) first) second) third) fourth) fifth)
      sixth) seventh) eighth

/-- Auxiliary parallel development preserves the original conversion theory.
In particular, its coherence guards can be transported without a confluence
assumption or a recursive call to a conversion checker. -/
theorem Par.sound {n : Nat} {left right : Tower.Tm n} (parallel : Par left right) :
    AuthoredConv left right := by
  induction parallel with
  | var _ => exact .refl _
  | const _ => exact .refl _
  | head _ => exact .refl _
  | headRel equality => exact .rel _ _ (.head equality)
  | pi _ _ first second => exact Conv.congPi first second
  | sigma _ _ first second => exact Conv.congSigma first second
  | id _ _ _ first second third => exact Conv.congId first second third
  | lam _ inner => exact Conv.congLam inner
  | app _ _ first second => exact Conv.congApp first second
  | pair _ _ first second => exact Conv.congPair first second
  | fst _ inner => exact Conv.mapCompatible Tm.fst (fun step => .congFst step) inner
  | snd _ inner => exact Conv.mapCompatible Tm.snd (fun step => .congSnd step) inner
  | refl _ inner => exact Conv.mapCompatible Tm.refl (fun step => .congRefl step) inner
  | betaPi _ _ body argument =>
      exact .trans _ _ _ (Conv.congApp (Conv.congLam body) argument)
        (.rel _ _ (.betaPi _ _))
  | betaSigmaFst _ _ first second =>
      exact .trans _ _ _ (Conv.mapCompatible Tm.fst (fun step => .congFst step)
        (Conv.congPair first second)) (.rel _ _ (.betaSigmaFst _ _))
  | betaSigmaSnd _ _ first second =>
      exact .trans _ _ _ (Conv.mapCompatible Tm.snd (fun step => .congSnd step)
        (Conv.congPair first second)) (.rel _ _ (.betaSigmaSnd _ _))
  | primitive cs cp cx cy _ _ _ _ _ _ _ _ _ _ _ pc _ x y symbol =>
      exact .trans _ _ _ (Root.sound (.primitive cs cp cx cy))
        (Conv.congApp (Conv.congApp (Conv.congApp pc x) y) symbol)
  | chain cs cp cx cy _ _ _ _ _ _ _ _ _ _ s p motive pc cc x middle y earlier later =>
      exact .trans _ _ _ (Root.sound (.chain cs cp cx cy))
        (Conv.congApp
          (Conv.congApp (Conv.congApp (Conv.congApp (Conv.congApp
            (Conv.congApp (Conv.congApp cc x) middle) y) earlier) later)
              (eliminateApp_congr s p motive pc cc x middle earlier))
          (eliminateApp_congr s p motive pc cc middle y later))

#print axioms par_refl
#print axioms Par.sound

end MILConversionParallel
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
