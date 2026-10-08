import Mettapedia.TypeTheory.ContextualTypeOperations
import Mathlib.Order.Heyting.Hom

/-!
# Local predicate and ordinary proposition capabilities

A predicate doctrine has ordered predicates in each context, a Heyting
substitution action, and the two display quantifiers with their local
adjunction and base-change laws. Predicates need not be every subobject of
the context category. In particular, existential truth supplies logical
evidence and does not select a data section.

The ordinary proposition type represents these predicates by its complete
term fibre. Its quotation and readout are inverse and natural. These are
local model capabilities; no raw syntax, derivation soundness, whole
interpreter compatibility or classifying theorem is a field.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualPredicateCapabilities

open Mettapedia.GSLT.Core.ContextualLadder

universe c s t m p

structure PredicateDoctrine (C : Cwf.{c, s, t, m}) where
  Predicate : C.Ctx → Type p
  [algebra : ∀ context, HeytingAlgebra (Predicate context)]
  reindex : {source target : C.Ctx} → C.Sub source target →
    HeytingHom (Predicate target) (Predicate source)
  reindex_id : ∀ {context : C.Ctx} (predicate : Predicate context),
    reindex (C.idS context) predicate = predicate
  reindex_comp : ∀ {source middle target : C.Ctx} (earlier : C.Sub source middle)
    (later : C.Sub middle target) (predicate : Predicate target),
    reindex (C.compS later earlier) predicate = reindex earlier (reindex later predicate)
  all : {context : C.Ctx} → (type : C.Ty context) →
    Predicate (C.ext context type) → Predicate context
  some : {context : C.Ctx} → (type : C.Ty context) →
    Predicate (C.ext context type) → Predicate context
  all_adjunction : ∀ {context : C.Ctx} (type : C.Ty context)
    (body : Predicate (C.ext context type)) (premise : Predicate context),
    reindex (C.wk type) premise ≤ body ↔ premise ≤ all type body
  some_adjunction : ∀ {context : C.Ctx} (type : C.Ty context)
    (body : Predicate (C.ext context type)) (consequent : Predicate context),
    some type body ≤ consequent ↔ body ≤ reindex (C.wk type) consequent
  all_reindex : ∀ {source target : C.Ctx} (substitution : C.Sub source target)
    (type : C.Ty target) (body : Predicate (C.ext target type)),
    reindex substitution (all type body) =
      all (C.tySub type substitution)
        (reindex (TypeOver.extensionSubstitution substitution type) body)
  some_reindex : ∀ {source target : C.Ctx} (substitution : C.Sub source target)
    (type : C.Ty target) (body : Predicate (C.ext target type)),
    reindex substitution (some type body) =
      some (C.tySub type substitution)
        (reindex (TypeOver.extensionSubstitution substitution type) body)

attribute [instance] PredicateDoctrine.algebra

variable {C : Cwf.{c, s, t, m}}

structure PropositionOperations (doctrine : PredicateDoctrine.{c, s, t, m, p} C) where
  omega : (context : C.Ctx) → C.Ty context
  quote : {context : C.Ctx} → doctrine.Predicate context → C.Tm context (omega context)
  holds : {context : C.Ctx} → C.Tm context (omega context) → doctrine.Predicate context
  holds_quote : ∀ {context : C.Ctx} (predicate : doctrine.Predicate context),
    holds (quote predicate) = predicate
  quote_holds : ∀ {context : C.Ctx} (term : C.Tm context (omega context)),
    quote (holds term) = term
  omega_substitution : ∀ {source target : C.Ctx} (substitution : C.Sub source target),
    C.tySub (omega target) substitution = omega source
  quote_substitution : ∀ {source target : C.Ctx} (substitution : C.Sub source target)
    (predicate : doctrine.Predicate target),
    HEq (C.tmSub (quote predicate) substitution) (quote (doctrine.reindex substitution predicate))
  holds_substitution : ∀ {source target : C.Ctx} (substitution : C.Sub source target)
    (term : C.Tm target (omega target)) (transported : C.Tm source (omega source)),
    HEq (C.tmSub term substitution) transported →
      holds transported = doctrine.reindex substitution (holds term)

structure AssumptionOperations (doctrine : PredicateDoctrine.{c, s, t, m, p} C) where
  assumed : (context : C.Ctx) → doctrine.Predicate context → C.Ctx
  inclusion : ∀ {context : C.Ctx} (predicate : doctrine.Predicate context),
    C.Sub (assumed context predicate) context
  select : ∀ {source target : C.Ctx} (predicate : doctrine.Predicate target)
    (substitution : C.Sub source target),
    doctrine.reindex substitution predicate = ⊤ → C.Sub source (assumed target predicate)
  select_beta : ∀ {source target : C.Ctx} (predicate : doctrine.Predicate target)
    (substitution : C.Sub source target) (guard : doctrine.reindex substitution predicate = ⊤),
    C.compS (inclusion predicate) (select predicate substitution guard) = substitution
  inclusion_monic : ∀ {source target : C.Ctx} (predicate : doctrine.Predicate target)
    (first second : C.Sub source (assumed target predicate)),
    C.compS (inclusion predicate) first = C.compS (inclusion predicate) second → first = second
  consequence : ∀ {context : C.Ctx} (assumption consequent : doctrine.Predicate context),
    doctrine.reindex (inclusion assumption) consequent = ⊤ ↔ assumption ≤ consequent

structure RefinementOperations (doctrine : PredicateDoctrine.{c, s, t, m, p} C) where
  refined : {context : C.Ctx} → (type : C.Ty context) →
    doctrine.Predicate (C.ext context type) → C.Ty context
  intro : ∀ {context : C.Ctx} (type : C.Ty context)
    (predicate : doctrine.Predicate (C.ext context type)) (term : C.Tm context type),
    doctrine.reindex (ContextualProductComparison.selfExtend C term) predicate = ⊤ →
      C.Tm context (refined type predicate)
  forget : ∀ {context : C.Ctx} (type : C.Ty context)
    (predicate : doctrine.Predicate (C.ext context type)),
    C.Tm context (refined type predicate) → C.Tm context type
  forget_guard : ∀ {context : C.Ctx} (type : C.Ty context)
    (predicate : doctrine.Predicate (C.ext context type))
    (term : C.Tm context (refined type predicate)),
    doctrine.reindex (ContextualProductComparison.selfExtend C (forget type predicate term)) predicate = ⊤
  beta : ∀ {context : C.Ctx} (type : C.Ty context)
    (predicate : doctrine.Predicate (C.ext context type)) (term : C.Tm context type)
    (guard : doctrine.reindex (ContextualProductComparison.selfExtend C term) predicate = ⊤),
    forget type predicate (intro type predicate term guard) = term
  eta : ∀ {context : C.Ctx} (type : C.Ty context)
    (predicate : doctrine.Predicate (C.ext context type))
    (term : C.Tm context (refined type predicate)),
    intro type predicate (forget type predicate term) (forget_guard type predicate term) = term
  formation_substitution : ∀ {source target : C.Ctx} (substitution : C.Sub source target)
    (type : C.Ty target) (predicate : doctrine.Predicate (C.ext target type)),
    C.tySub (refined type predicate) substitution = refined (C.tySub type substitution)
      (doctrine.reindex (TypeOver.extensionSubstitution substitution type) predicate)
  intro_substitution : ∀ {source target : C.Ctx} (substitution : C.Sub source target)
    (type : C.Ty target) (predicate : doctrine.Predicate (C.ext target type))
    (term : C.Tm target type)
    (guard : doctrine.reindex (ContextualProductComparison.selfExtend C term) predicate = ⊤)
    (transportedGuard : doctrine.reindex
      (ContextualProductComparison.selfExtend C (C.tmSub term substitution))
      (doctrine.reindex (TypeOver.extensionSubstitution substitution type) predicate) = ⊤),
    HEq (C.tmSub (intro type predicate term guard) substitution)
      (intro (C.tySub type substitution)
        (doctrine.reindex (TypeOver.extensionSubstitution substitution type) predicate)
          (C.tmSub term substitution) transportedGuard)
  forget_substitution : ∀ {source target : C.Ctx} (substitution : C.Sub source target)
    (type : C.Ty target) (predicate : doctrine.Predicate (C.ext target type))
    (term : C.Tm target (refined type predicate))
    (transported : C.Tm source (refined (C.tySub type substitution)
      (doctrine.reindex (TypeOver.extensionSubstitution substitution type) predicate))),
    HEq (C.tmSub term substitution) transported →
      HEq (C.tmSub (forget type predicate term) substitution)
        (forget (C.tySub type substitution)
          (doctrine.reindex (TypeOver.extensionSubstitution substitution type) predicate) transported)

end Mettapedia.TypeTheory.ContextualPredicateCapabilities
