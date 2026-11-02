import Mettapedia.Languages.OpenTheory.VariableSchemaSubstitution

/-!
# Constructing native simultaneous maps from typed schema parameters

A typed HOL substitution supplies every parameter image. The native table
retains each image once, with its post-type-substitution key. Distinctness is
checked at those keys; source type injectivity is not required.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.OpenTheory.ReverseTranslation.VariableSchema
open Mettapedia.Logic

namespace Instantiation

def key (types : TypeSubst) {Γ : HOL.Ctx AtomicTy} (names : Naming Γ)
    {type : HOL.Ty AtomicTy} (index : HOL.Var Γ type) : SourceVar :=
  ⟨names index, reverseTy (HOL.Ty.substitute types.baseInstance type)⟩

theorem key_action (types : TypeSubst) {Γ : HOL.Ctx AtomicTy} (names : Naming Γ)
    {type : HOL.Ty AtomicTy} (index : HOL.Var Γ type) :
    key types names index = types.applyVar (Naming.sourceVar names index) := by
  simp only [key, TypeSubst.applyVar, Naming.sourceVar, reverseTy_substitute]

def KeysDistinct (types : TypeSubst) {Γ : HOL.Ctx AtomicTy} (names : Naming Γ) : Prop :=
  ∀ {first second : HOL.Ty AtomicTy} (a : HOL.Var Γ first) (b : HOL.Var Γ second),
    key types names a = key types names b → deBruijnIndex a = deBruijnIndex b

theorem KeysDistinct.empty (types : TypeSubst) : KeysDistinct types Naming.empty := by
  intro _ _ impossible
  cases impossible

theorem KeysDistinct.cons (types : TypeSubst) {Γ : HOL.Ctx AtomicTy} {domain : HOL.Ty AtomicTy}
    (name : Name) (names : Naming Γ) (distinct : KeysDistinct types names)
    (fresh : name ∉ Naming.toList names) : KeysDistinct types (Naming.cons (σ := domain) name names) := by
  intro first second a b same
  cases a with
  | vz =>
    cases b with
    | vz => rfl
    | vs b =>
      have sameName : name = names b := congrArg Var.name same
      exact False.elim (fresh (sameName.symm ▸ Naming.mem_toList names b))
  | vs a =>
    cases b with
    | vz =>
      have sameName : names a = name := congrArg Var.name same
      exact False.elim (fresh (sameName ▸ Naming.mem_toList names a))
    | vs b =>
      exact congrArg Nat.succ (distinct a b same)

theorem KeysDistinct.tail (types : TypeSubst) {Γ : HOL.Ctx AtomicTy} {domain : HOL.Ty AtomicTy}
    (names : Naming (domain :: Γ)) (distinct : KeysDistinct types names) :
    KeysDistinct types (fun index => names (.vs index)) := by
  intro first second a b same
  exact Nat.add_right_cancel (distinct (.vs a) (.vs b) same)

abbrev Images (types : TypeSubst) (Γ : HOL.Ctx AtomicTy) :=
  ∀ {type : HOL.Ty AtomicTy}, HOL.Var Γ type →
    {code : CheckedSourceTerm // code.ty = reverseTy (HOL.Ty.substitute types.baseInstance type)}

def entries (types : TypeSubst) {Γ : HOL.Ctx AtomicTy}
    (sourceNames : Naming Γ) (images : Images types Γ) : List (SourceVar × CheckedSourceTerm) :=
  List.rec (motive := fun context : HOL.Ctx AtomicTy =>
      Naming context → Images types context → List (SourceVar × CheckedSourceTerm))
    (fun _ _ => [])
    (fun _ _ rest names replacements =>
      (key types names HOL.Var.vz, (replacements HOL.Var.vz).val) ::
        rest (fun index => names (.vs index)) (fun index => replacements (.vs index)))
    Γ sourceNames images

theorem entries_typed (types : TypeSubst) :
    ∀ {Γ : HOL.Ctx AtomicTy} (sourceNames : Naming Γ) (images : Images types Γ)
      (entry : SourceVar × CheckedSourceTerm),
      entry ∈ entries types sourceNames images → entry.2.ty = entry.1.ty
  | [], _, _, _, impossible => nomatch impossible
  | _ :: _, sourceNames, images, entry, member => by
    rcases List.mem_cons.mp member with same | member
    · subst entry
      exact (images HOL.Var.vz).property
    · exact entries_typed types (fun index => sourceNames (.vs index))
        (fun index => images (.vs index)) entry member

def mapping (types : TypeSubst) {Γ : HOL.Ctx AtomicTy}
    (sourceNames : Naming Γ) (images : Images types Γ) : TypeCorrectTermSubstitution where
  raw := ⟨types, entries types sourceNames images⟩
  typeCorrect := entries_typed types sourceNames images

theorem lookup_image (types : TypeSubst) :
    ∀ {Γ : HOL.Ctx AtomicTy} (sourceNames : Naming Γ) (images : Images types Γ),
      KeysDistinct types sourceNames → ∀ {type : HOL.Ty AtomicTy} (index : HOL.Var Γ type),
        (mapping types sourceNames images).raw.lookup (key types sourceNames index) =
          some (images index).val
  | _ :: _, sourceNames, images, distinct, _, .vz => by
    simp [mapping, entries, TermSubst.lookup, TermSubst.keySame]
  | _ :: _, sourceNames, images, distinct, _, .vs index => by
    have different : key types sourceNames HOL.Var.vz ≠ key types sourceNames (.vs index) := by
      intro same
      have impossible := distinct HOL.Var.vz (.vs index) same
      simp [deBruijnIndex] at impossible
    have headMiss : TermSubst.keySame (key types sourceNames HOL.Var.vz)
        (key types sourceNames (.vs index)) = false := by
      apply Bool.eq_false_iff.mpr
      intro same
      exact different ((sourceVarSame_eq_true_iff _ _).mp same)
    change (List.find? (fun entry => TermSubst.keySame entry.1 (key types sourceNames (.vs index)))
      ((key types sourceNames HOL.Var.vz, (images HOL.Var.vz).val) ::
        entries types (fun item => sourceNames (.vs item)) (fun item => images (.vs item)))).map Prod.snd = _
    simp only [List.find?_cons, headMiss]
    exact lookup_image types (fun item => sourceNames (.vs item)) (fun item => images (.vs item))
      (distinct.tail types sourceNames) index

theorem compatible (types : TypeSubst) {Γ Δ : HOL.Ctx AtomicTy}
    (sourceNames : Naming Γ) (targetNames : Naming Δ)
    (images : Images types Γ) (distinct : KeysDistinct types sourceNames)
    (theta : HOL.Subst Symbol (Γ.map (HOL.Ty.substitute types.baseInstance)) Δ)
    (exactImages : ∀ {type : HOL.Ty AtomicTy} (index : HOL.Var Γ type),
      (images index).val.canonical = reverseCanonical targetNames (theta (index.mapTypes types.baseInstance)))
    {type : HOL.Ty AtomicTy} (index : HOL.Var Γ type) :
    reverseTerm targetNames (theta (index.mapTypes types.baseInstance)) =
      (mapping types sourceNames images).raw.applyDB (Naming.env sourceNames index) := by
  change _ = (mapping types sourceNames images).raw.applyDB (.free (Naming.sourceVar sourceNames index))
  rw [TermSubst.applyDB_free_of_lookup_some (mapping types sourceNames images).raw _ (images index).val
    (by simpa only [mapping, key_action] using lookup_image types sourceNames images distinct index)]
  exact (congrArg CanonicalTerm.term (exactImages index)).symm

theorem canonical (types : TypeSubst) {Γ Δ : HOL.Ctx AtomicTy} {type : HOL.Ty AtomicTy}
    (term : ParameterTerm Γ type) (sourceNames : Naming Γ) (targetNames : Naming Δ)
    (images : Images types Γ) (distinct : KeysDistinct types sourceNames)
    (theta : HOL.Subst Symbol (Γ.map (HOL.Ty.substitute types.baseInstance)) Δ)
    (exactImages : ∀ {type : HOL.Ty AtomicTy} (index : HOL.Var Γ type),
      (images index).val.canonical = reverseCanonical targetNames (theta (index.mapTypes types.baseInstance))) :
    (mapping types sourceNames images).apply (reverseCanonical sourceNames (embed term)) =
      reverseCanonical targetNames (HOL.subst theta (mapped (mapping types sourceNames images).raw term)) :=
  canonical_action (mapping types sourceNames images) term sourceNames targetNames theta
    (fun index => compatible types sourceNames targetNames images distinct theta exactImages index)

#print axioms entries_typed
#print axioms lookup_image
#print axioms compatible
#print axioms canonical

end Instantiation
end Mettapedia.Languages.OpenTheory.ReverseTranslation.VariableSchema
