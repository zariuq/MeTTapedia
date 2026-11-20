import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Families.Laws
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.InductiveConsequences

/-!
# Declared inductive families

A family `D` with `p` parameters is declared by the telescope of its parameter types, the
types of its indices over the parameters, its universe, and its constructors. A constructor
is a telescope of fields ending in its target indices: a value field has a type over the
parameters; a recursive field is `D` at indices over the parameters and the earlier
fields; the target is a list of indices over the parameters and all the fields. This is
the schema of inductive families with telescopes, restricted to value fields whose types do
not mention earlier fields and to index types over the parameters only.

The declared types are

* `D : Π params. Π indices. U`, by `FamilyDecl.familyType`;
* `k : Π params. Π fields. D params target`, by `FamilyDecl.ctorType`.

At given parameters `ps` in a context the declaration is read as a family
(`FamilyDecl.view`): its type at the indices `is` is the spine `D ps is`; the canonical forms
of a constructor `k` are the spines `k ps' fs` whose stored parameters `ps'` are convertible,
one by one, to `ps` at the parameter types; value fields carry the packs of their types
instantiated at `ps`; recursive fields and the target compute their indices from the
fields. Another spine `D ps₂ is'` is the same family when `ps₂` is convertible to `ps` and
every value-field type and index type at `ps₂` is reducibly equal to the one at `ps`.

Constructor forms of the reading are rigid when the constructors are declared as
constructors under distinct names (`FamilyDecl.view_rigid`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization
namespace Families

open TelescopeAbstraction (closeType)
open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L]

/-! ## The schema -/

/-- The fields of a constructor of a family with `p` parameters, after `j` earlier fields,
ending in the target indices. A value field has a type over the parameters; a recursive
field has indices over the parameters and the `j` earlier fields; the target has indices
over the parameters and all the fields. -/
inductive CtorTele (Head : Type) (p : Nat) : Nat → Type where
  | target {j : Nat} (indices : List (Tm Head (p + j))) : CtorTele Head p j
  | value {j : Nat} (type : Tm Head p) (rest : CtorTele Head p (j + 1)) : CtorTele Head p j
  | recursive {j : Nat} (indices : List (Tm Head (p + j))) (rest : CtorTele Head p (j + 1)) :
      CtorTele Head p j

/-- A declared inductive family. -/
structure FamilyDecl (Head : Type) where
  name : DeclName
  params : Nat
  paramEntry : (j : Nat) → Tm Head j
  indexTypes : List (Tm Head params)
  sort : Head
  ctors : List (DeclName × CtorTele Head params 0)

/-! ## The declared types -/

section Types

variable {p : Nat}

/-- The parameters as variables over the parameters and `j` fields, in telescope order. -/
def paramVars (p j : Nat) : List (Tm Head (p + j)) :=
  List.ofFn fun i : Fin p => .var ⟨p + j - 1 - i.val, by omega⟩

/-- A term over the parameters, seen over the parameters and `j` fields. -/
def overFields (j : Nat) (t : Tm Head p) : Tm Head (p + j) :=
  Presentation.rename (fun i => Fin.addNat i j) t

/-- The type `Π fields. D params target` of a constructor, over the parameters. -/
def CtorTele.body (D : DeclName) : {j : Nat} → CtorTele Head p j → Tm Head (p + j)
  | j, .target idx => appSpine (.const D) (paramVars p j ++ idx)
  | j, .value T rest => .pi (overFields j T) (rest.body D)
  | j, .recursive idx rest => .pi (appSpine (.const D) (paramVars p j ++ idx)) (rest.body D)

/-- The arrows `Π indices. U` over the parameters. -/
def indexArrows (u : Head) : List (Tm Head p) → (j : Nat) → Tm Head (p + j)
  | [], _ => .head u
  | T :: Ts, j => .pi (overFields j T) (indexArrows u Ts (j + 1))

/-- The telescope of the parameters. -/
def FamilyDecl.paramTele (decl : FamilyDecl Head) : Ctx Head decl.params :=
  ofEntries decl.paramEntry decl.params

/-- The declared type `Π params. Π indices. U` of the family. -/
def FamilyDecl.familyType (decl : FamilyDecl Head) : Tm Head 0 :=
  closeType decl.paramTele (indexArrows decl.sort decl.indexTypes 0)

/-- The declared type `Π params. Π fields. D params target` of a constructor. -/
def FamilyDecl.ctorType (decl : FamilyDecl Head) (tele : CtorTele Head decl.params 0) :
    Tm Head 0 :=
  closeType decl.paramTele (tele.body decl.name)

end Types

/-! ## Reading a declaration at its parameters -/

section Reading

variable {n p : Nat}

/-- A term over `N` variables instantiated at the arguments, in telescope order. -/
def inst {N : Nat} (args : List (Tm Head n)) (t : Tm Head N) : Tm Head n :=
  Presentation.subst (argsSub N args) t

/-- The value-field types of a constructor. -/
def CtorTele.valueTypes : {j : Nat} → CtorTele Head p j → List (Tm Head p)
  | _, .target _ => []
  | _, .value T rest => T :: rest.valueTypes
  | _, .recursive _ rest => rest.valueTypes

/-- The fields of a constructor at the parameters `ps`, with the packs `typePack` gives to
the instantiated value-field types. -/
def CtorTele.fieldsAt (typePack : Tm Head n → Pack Head n) (ps : List (Tm Head n)) :
    {j : Nat} → CtorTele Head p j → List (FieldAt Head n)
  | _, .target _ => []
  | _, .value T rest => .value (typePack (inst ps T)) :: rest.fieldsAt typePack ps
  | j, .recursive idx rest =>
      .recursive (fun all => idx.map (inst (ps ++ all.take j))) :: rest.fieldsAt typePack ps

/-- The target indices of a constructor at the parameters `ps` and the given fields. -/
def CtorTele.targetAt (ps : List (Tm Head n)) :
    {j : Nat} → CtorTele Head p j → List (Tm Head n) → List (Tm Head n)
  | j, .target idx => fun all => idx.map (inst (ps ++ all.take j))
  | _, .value _ rest => rest.targetAt ps
  | _, .recursive _ rest => rest.targetAt ps

/-- A default term, for positions outside a list. -/
def junk : Tm Head n := .const .anonymous

/-- The type of the parameter at position `j`, at the earlier parameters of `ps`. -/
def FamilyDecl.paramTypeAt (decl : FamilyDecl Head) (ps : List (Tm Head n)) (j : Nat) :
    Tm Head n :=
  inst (ps.take j) (decl.paramEntry j)

/-- Parameters `ps'` convertible, one by one, to the parameters `ps`, at the parameter types
instantiated at `ps`. -/
def FamilyDecl.ParamsConv (S : Setting Head L) (Γ : Ctx Head n) (decl : FamilyDecl Head)
    (ps ps' : List (Tm Head n)) : Prop :=
  ps'.length = decl.params ∧ ∀ j < decl.params,
    S.E.convTm Γ (ps'.getD j junk) (ps.getD j junk) (decl.paramTypeAt ps j)

/-- Every value-field type and index type at `ps₂` is reducibly equal to the one at `ps`. -/
def FamilyDecl.TypesAgree (decl : FamilyDecl Head) (typePack : Tm Head n → Pack Head n)
    (ps ps₂ : List (Tm Head n)) : Prop :=
  (∀ entry ∈ decl.ctors, ∀ T ∈ entry.2.valueTypes, (typePack (inst ps T)).eqTy (inst ps₂ T)) ∧
    ∀ T ∈ decl.indexTypes, (typePack (inst ps T)).eqTy (inst ps₂ T)

/-- A constructor of the declaration read at the parameters `ps`. -/
def FamilyDecl.ctorAt (S : Setting Head L) (Γ : Ctx Head n) (decl : FamilyDecl Head)
    (typePack : Tm Head n → Pack Head n) (ps : List (Tm Head n))
    (entry : DeclName × CtorTele Head decl.params 0) : CtorAt Head n where
  form nf fs := ∃ ps', nf = appSpine (.const entry.1) (ps' ++ fs) ∧ decl.ParamsConv S Γ ps ps'
  fields := entry.2.fieldsAt typePack ps
  target := entry.2.targetAt ps

/-- The declaration read at the parameters `ps` as a family. -/
def FamilyDecl.view (S : Setting Head L) (Γ : Ctx Head n) (decl : FamilyDecl Head)
    (typePack : Tm Head n → Pack Head n) (ps : List (Tm Head n)) : FamilyAt Head n where
  type is := appSpine (.const decl.name) (ps ++ is)
  ctors := decl.ctors.map (decl.ctorAt S Γ typePack ps)
  indexPacks := decl.indexTypes.map fun T => typePack (inst ps T)
  sameFormer X is := ∃ ps₂, X = appSpine (.const decl.name) (ps₂ ++ is) ∧
    is.length = decl.indexTypes.length ∧ decl.ParamsConv S Γ ps ps₂ ∧
    decl.TypesAgree typePack ps ps₂

end Reading

/-! ## Rigid constructor forms -/

section Rigid

variable {S : Setting Head L} {n : Nat} {Γ : Ctx Head n}

/-- The constructors of a declaration are declared as constructors, under distinct names. -/
structure FamilyDecl.CtorsDeclared (S : Setting Head L) (decl : FamilyDecl Head) : Prop where
  role : ∀ {entry}, entry ∈ decl.ctors → ∃ arity, S.roles entry.1 = .constructor arity
  distinct : (decl.ctors.map Prod.fst).Nodup

theorem FamilyDecl.view_rigid {decl : FamilyDecl Head} (declared : decl.CtorsDeclared S)
    {typePack : Tm Head n → Pack Head n} {ps : List (Tm Head n)} :
    FormsRigid S (decl.view S Γ typePack ps) where
  whnf := by
    intro c nf fs mem form
    obtain ⟨entry, entryMem, rfl⟩ := List.mem_map.mp mem
    obtain ⟨ps', rfl, _⟩ := form
    obtain ⟨arity, role⟩ := declared.role entryMem
    exact canonical_whnf S.shape (.inr ⟨_, _, _, role, rfl⟩)
  not_neutral := by
    intro c nf fs mem form nNf
    obtain ⟨entry, entryMem, rfl⟩ := List.mem_map.mp mem
    obtain ⟨ps', rfl, _⟩ := form
    obtain ⟨arity, role⟩ := declared.role entryMem
    exact nNf.not_canonical (.inr ⟨_, _, _, role, rfl⟩)
  unique := by
    intro c c' nf fs fs' mem mem' form form'
    obtain ⟨entry, entryMem, rfl⟩ := List.mem_map.mp mem
    obtain ⟨entry', entryMem', rfl⟩ := List.mem_map.mp mem'
    obtain ⟨ps', rfl, len, _⟩ := form
    obtain ⟨ps'', e, len', _⟩ := form'
    obtain ⟨sameName, sameArgs⟩ := appSpine_const_injective e
    obtain ⟨-, rfl⟩ := List.append_inj sameArgs (len.trans len'.symm)
    have : entry = entry' := by
      rcases entry with ⟨k, tele⟩
      rcases entry' with ⟨k', tele'⟩
      have hk : k = k' := sameName
      subst hk
      have := List.inj_on_of_nodup_map declared.distinct entryMem entryMem' rfl
      exact this
    subst this
    exact ⟨rfl, rfl⟩

end Rigid

end Families
end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
