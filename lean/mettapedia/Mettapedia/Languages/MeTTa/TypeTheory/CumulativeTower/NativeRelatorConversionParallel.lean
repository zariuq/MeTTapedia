import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.NativeRelatorConversionCompletion

/-!
# Parallel development with retained native metadata coherence

The auxiliary parallel relation develops selected arguments while retaining
authored conversion evidence for duplicated metadata. Its contractions are
sound for authored conversion; they are not claimed to be single runtime
steps. All five native branches retain their actual, distinct reducts.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace NativeRelatorConversionParallel

open Presentation NativeIndexedFamilies NativeRelatorConversionCompletion

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
  | listNil {n : Nat} {a p z s innerA a' p' z' s' : Tower.Tm n} :
      AuthoredConv innerA a →
      Par a a' → Par p p' → Par z z' → Par s s' →
      Par (Intrinsic.eliminateApp a p z s (Intrinsic.nilApp innerA)) (z')
  | listCons {n : Nat} {a p z s innerA h t a' p' z' s' h' t' : Tower.Tm n} :
      AuthoredConv innerA a →
      Par a a' → Par p p' → Par z z' → Par s s' → Par h h' → Par t t' →
      Par (Intrinsic.eliminateApp a p z s (Intrinsic.consApp innerA h t)) (.app (.app (.app s' h') t') (Intrinsic.eliminateApp a' p' z' s' t'))
  | identity {n : Nat} {a x p d y witness a' x' p' d' y' witness' : Tower.Tm n} :
      AuthoredConv y x → AuthoredConv witness x →
      Par a a' → Par x x' → Par p p' → Par d d' → Par y y' → Par witness witness' →
      Par (Intrinsic.identityEliminateApp a x p d y (.refl witness)) (d')
  | relNil {n : Nat} {a b r p z s xs ys innerA innerB innerR a' b' r' p' z' s' xs' ys' : Tower.Tm n} :
      AuthoredConv innerA a → AuthoredConv innerB b → AuthoredConv innerR r → AuthoredConv xs (Intrinsic.nilApp a) → AuthoredConv ys (Intrinsic.nilApp b) →
      Par a a' → Par b b' → Par r r' → Par p p' → Par z z' → Par s s' → Par xs xs' → Par ys ys' →
      Par (IntrinsicRelator.eliminateApp a b r p z s xs ys (IntrinsicRelator.nilRelApp innerA innerB innerR)) (z')
  | relCons {n : Nat} {a b r p z s xs ys innerA innerB innerR h k t u he te a' b' r' p' z' s' xs' ys' h' k' t' u' he' te' : Tower.Tm n} :
      AuthoredConv innerA a → AuthoredConv innerB b → AuthoredConv innerR r → AuthoredConv xs (Intrinsic.consApp a h t) → AuthoredConv ys (Intrinsic.consApp b k u) →
      Par a a' → Par b b' → Par r r' → Par p p' → Par z z' → Par s s' → Par xs xs' → Par ys ys' → Par h h' → Par k k' → Par t t' → Par u u' → Par he he' → Par te te' →
      Par (IntrinsicRelator.eliminateApp a b r p z s xs ys (IntrinsicRelator.consRelApp innerA innerB innerR h k t u he te)) (.app (.app (.app (.app (.app (.app (.app s' h') k') t') u') he') te') (IntrinsicRelator.eliminateApp a' b' r' p' z' s' t' u' te'))

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
  | listNil ca _ _ _ _ _ _ hz _ =>
      exact .trans _ _ _ (Root.sound (.listNil ca))
        hz
  | listCons ca _ _ _ _ _ _ ha hp hz hs hh ht =>
      exact .trans _ _ _ (Root.sound (.listCons ca))
        (Conv.congApp (Conv.congApp (Conv.congApp hs hh) ht) (listElim_congr ha hp hz hs ht))
  | identity cy cw _ _ _ _ _ _ _ _ _ hd _ _ =>
      exact .trans _ _ _ (Root.sound (.identity cy cw))
        hd
  | relNil ca cb cr cx cy _ _ _ _ _ _ _ _ _ _ _ _ hz _ _ _ =>
      exact .trans _ _ _ (Root.sound (.relNil ca cb cr cx cy))
        hz
  | relCons ca cb cr cx cy _ _ _ _ _ _ _ _ _ _ _ _ _ _ ha hb hr hp hz hs _ _ hh hk ht hu hhe hte =>
      exact .trans _ _ _ (Root.sound (.relCons ca cb cr cx cy))
        (Conv.congApp (Conv.congApp (Conv.congApp (Conv.congApp (Conv.congApp (Conv.congApp (Conv.congApp hs hh) hk) ht) hu) hhe) hte) (relElim_congr ha hb hr hp hz hs ht hu hte))

#print axioms par_refl
#print axioms Par.sound

end NativeRelatorConversionParallel
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
