import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalSubstitution

/-!
# Preservation of ordered declaration dependencies

Renaming leaves primitive dependencies unchanged. Substitution preserves a
rank bound when each supplied argument respects that bound. These are syntax
theorems; formation of declaration headers remains a separate judgment.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External

universe u

variable {S : Symbols.{u}}
variable (typeRank : S.TypeSymbol → Nat) (termRank : S.TermSymbol → Nat) (bound : Nat)

mutual

theorem TypeExpr.before_rename_iff : ∀ {n m : Nat} (mapping : Renaming n m) (value : TypeExpr S n),
    (value.rename mapping).before typeRank termRank bound ↔ value.before typeRank termRank bound
  | _, _, mapping, .family symbol arguments => by
      simp only [TypeExpr.rename, TypeExpr.before,
        TermExpr.before_rename_iff mapping]
  | _, _, mapping, .pi domain body => by
      simp only [TypeExpr.rename,
        TypeExpr.before,
        TypeExpr.before_rename_iff mapping domain,
        TypeExpr.before_rename_iff (liftRenaming mapping) body]
  | _, _, mapping, .sigma domain body => by
      simp only [TypeExpr.rename,
        TypeExpr.before,
        TypeExpr.before_rename_iff mapping domain,
        TypeExpr.before_rename_iff (liftRenaming mapping) body]

theorem TermExpr.before_rename_iff : ∀ {n m : Nat} (mapping : Renaming n m) (value : TermExpr S n),
    (value.rename mapping).before typeRank termRank bound ↔ value.before typeRank termRank bound
  | _, _, mapping, .var index => by
      rfl
  | _, _, mapping, .primitive symbol arguments => by
      simp only [TermExpr.rename, TermExpr.before,
        TermExpr.before_rename_iff mapping]
  | _, _, mapping, .lam domain codomain body => by
      simp only [TermExpr.rename,
        TermExpr.before,
        TypeExpr.before_rename_iff mapping domain,
        TypeExpr.before_rename_iff (liftRenaming mapping) codomain,
        TermExpr.before_rename_iff (liftRenaming mapping) body]
  | _, _, mapping, .app domain body function argument => by
      simp only [TermExpr.rename,
        TermExpr.before,
        TypeExpr.before_rename_iff mapping domain,
        TypeExpr.before_rename_iff (liftRenaming mapping) body,
        TermExpr.before_rename_iff mapping function,
        TermExpr.before_rename_iff mapping argument]
  | _, _, mapping, .pair domain body first second => by
      simp only [TermExpr.rename,
        TermExpr.before,
        TypeExpr.before_rename_iff mapping domain,
        TypeExpr.before_rename_iff (liftRenaming mapping) body,
        TermExpr.before_rename_iff mapping first,
        TermExpr.before_rename_iff mapping second]
  | _, _, mapping, .fst domain body pair => by
      simp only [TermExpr.rename,
        TermExpr.before,
        TypeExpr.before_rename_iff mapping domain,
        TypeExpr.before_rename_iff (liftRenaming mapping) body,
        TermExpr.before_rename_iff mapping pair]
  | _, _, mapping, .snd domain body pair => by
      simp only [TermExpr.rename,
        TermExpr.before,
        TypeExpr.before_rename_iff mapping domain,
        TypeExpr.before_rename_iff (liftRenaming mapping) body,
        TermExpr.before_rename_iff mapping pair]
  | _, _, mapping, .sigmaElim domain body motive branch pair => by
      simp only [TermExpr.rename,
        TermExpr.before,
        TypeExpr.before_rename_iff mapping domain,
        TypeExpr.before_rename_iff (liftRenaming mapping) body,
        TypeExpr.before_rename_iff (liftRenaming mapping) motive,
        TermExpr.before_rename_iff (liftRenaming (liftRenaming mapping)) branch,
        TermExpr.before_rename_iff mapping pair]

end

theorem ContextExpr.lookup_before : ∀ {n : Nat} (context : ContextExpr S n)
    (_ordered : context.before typeRank termRank bound) (position : Fin n),
    (context.lookup position).before typeRank termRank bound
  | _, .nil, _, position => Fin.elim0 position
  | _, .snoc context type, ordered, position => by
      cases position using Fin.cases with
      | zero =>
          exact (TypeExpr.before_rename_iff typeRank termRank bound Fin.succ type).mpr ordered.2
      | succ previous =>
          exact (TypeExpr.before_rename_iff typeRank termRank bound Fin.succ (context.lookup previous)).mpr
            (ContextExpr.lookup_before context ordered.1 previous)

theorem liftSubstitution_before {n m : Nat} (substitution : Substitution S n m)
    (bounded : ∀ index, (substitution index).before typeRank termRank bound) :
    ∀ index, (liftSubstitution substitution index).before typeRank termRank bound := by
  intro index
  cases index using Fin.cases with
  | zero => trivial
  | succ index =>
      exact (TermExpr.before_rename_iff typeRank termRank bound Fin.succ (substitution index)).mpr
        (bounded index)

mutual

theorem TypeExpr.before_substitute : ∀ {n m : Nat} (substitution : Substitution S n m)
    (_bounded : ∀ index, (substitution index).before typeRank termRank bound)
    (value : TypeExpr S n), value.before typeRank termRank bound →
      (value.substitute substitution).before typeRank termRank bound
  | _, _, substitution, bounded, .family symbol arguments, ordered => by
      refine ⟨ordered.1, fun position => ?_⟩
      exact TermExpr.before_substitute substitution bounded
        (arguments position) (ordered.2 position)
  | _, _, substitution, bounded, .pi domain body, ordered => by
      exact ⟨TypeExpr.before_substitute substitution bounded domain ordered.1,
        TypeExpr.before_substitute (liftSubstitution substitution) (liftSubstitution_before typeRank termRank bound _ bounded) body ordered.2⟩
  | _, _, substitution, bounded, .sigma domain body, ordered => by
      exact ⟨TypeExpr.before_substitute substitution bounded domain ordered.1,
        TypeExpr.before_substitute (liftSubstitution substitution) (liftSubstitution_before typeRank termRank bound _ bounded) body ordered.2⟩

theorem TermExpr.before_substitute : ∀ {n m : Nat} (substitution : Substitution S n m)
    (_bounded : ∀ index, (substitution index).before typeRank termRank bound)
    (value : TermExpr S n), value.before typeRank termRank bound →
      (value.substitute substitution).before typeRank termRank bound
  | _, _, substitution, bounded, .var index, ordered => by
      exact bounded index
  | _, _, substitution, bounded, .primitive symbol arguments, ordered => by
      refine ⟨ordered.1, fun position => ?_⟩
      exact TermExpr.before_substitute substitution bounded
        (arguments position) (ordered.2 position)
  | _, _, substitution, bounded, .lam domain codomain body, ordered => by
      exact ⟨TypeExpr.before_substitute substitution bounded domain ordered.1,
        TypeExpr.before_substitute (liftSubstitution substitution) (liftSubstitution_before typeRank termRank bound _ bounded) codomain ordered.2.1,
        TermExpr.before_substitute (liftSubstitution substitution) (liftSubstitution_before typeRank termRank bound _ bounded) body ordered.2.2⟩
  | _, _, substitution, bounded, .app domain body function argument, ordered => by
      exact ⟨TypeExpr.before_substitute substitution bounded domain ordered.1,
        TypeExpr.before_substitute (liftSubstitution substitution) (liftSubstitution_before typeRank termRank bound _ bounded) body ordered.2.1,
        TermExpr.before_substitute substitution bounded function ordered.2.2.1,
        TermExpr.before_substitute substitution bounded argument ordered.2.2.2⟩
  | _, _, substitution, bounded, .pair domain body first second, ordered => by
      exact ⟨TypeExpr.before_substitute substitution bounded domain ordered.1,
        TypeExpr.before_substitute (liftSubstitution substitution) (liftSubstitution_before typeRank termRank bound _ bounded) body ordered.2.1,
        TermExpr.before_substitute substitution bounded first ordered.2.2.1,
        TermExpr.before_substitute substitution bounded second ordered.2.2.2⟩
  | _, _, substitution, bounded, .fst domain body pair, ordered => by
      exact ⟨TypeExpr.before_substitute substitution bounded domain ordered.1,
        TypeExpr.before_substitute (liftSubstitution substitution) (liftSubstitution_before typeRank termRank bound _ bounded) body ordered.2.1,
        TermExpr.before_substitute substitution bounded pair ordered.2.2⟩
  | _, _, substitution, bounded, .snd domain body pair, ordered => by
      exact ⟨TypeExpr.before_substitute substitution bounded domain ordered.1,
        TypeExpr.before_substitute (liftSubstitution substitution) (liftSubstitution_before typeRank termRank bound _ bounded) body ordered.2.1,
        TermExpr.before_substitute substitution bounded pair ordered.2.2⟩
  | _, _, substitution, bounded, .sigmaElim domain body motive branch pair, ordered => by
      exact ⟨TypeExpr.before_substitute substitution bounded domain ordered.1,
        TypeExpr.before_substitute (liftSubstitution substitution) (liftSubstitution_before typeRank termRank bound _ bounded) body ordered.2.1,
        TypeExpr.before_substitute (liftSubstitution substitution) (liftSubstitution_before typeRank termRank bound _ bounded) motive ordered.2.2.1,
        TermExpr.before_substitute (liftSubstitution (liftSubstitution substitution)) (liftSubstitution_before typeRank termRank bound _ (liftSubstitution_before typeRank termRank bound _ bounded)) branch ordered.2.2.2.1,
        TermExpr.before_substitute substitution bounded pair ordered.2.2.2.2⟩

end

end Mettapedia.TypeTheory.Calculi.NativeDependent.External
