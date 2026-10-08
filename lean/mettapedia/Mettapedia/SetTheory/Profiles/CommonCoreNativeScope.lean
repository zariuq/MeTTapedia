import Mettapedia.SetTheory.Profiles.CommonCoreLogicalCompilation

/-!
# Reconstruction of closed compiled logical terms

The parser resolves set and proposition names in their own lexical scopes,
checks the primitive grammar, and rejects binder capture. Its depth bound
counts logical constructors. The scope invariant tracks distinct names
introduced at earlier binder depths; it is constructed from the empty
scope and is preserved by each of the encoder's two binder forms.

This validates the symbolic `WireTerm` boundary. It neither verifies the C
reader nor supplies a varying higher-order model.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.Profiles.CommonCoreNativeScope

open Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialLogic (Formula)
open Mettapedia.GSLT.LanguageDef.CertificateGSLT (WireTerm)
open CommonCoreLogicalCompilation

/- Decimal indices are reconstructed from their actual ASCII bytes by
following the fuel-based `toDigitsCore` recursion. -/

private def decimalByteValue (bytes : List UInt8) (initial : Nat) : Nat :=
  bytes.foldl (fun previous byte => 10 * previous + (byte.toNat - 48)) initial

private theorem digit_bytes {digit : Nat} (small : digit < 10) (tail : List Char) :
    (Nat.digitChar digit :: tail).utf8Encode.data.toList =
      UInt8.ofNat (48+digit) :: tail.utf8Encode.data.toList := by
  have encoding : String.utf8EncodeChar (Nat.digitChar digit) = [UInt8.ofNat (48+digit)] := by
    match digit with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => rfl
    | rest+10 => omega
  rw [List.utf8Encode_cons, List.utf8Encode_singleton, encoding]
  simp

private theorem digit_step {digit : Nat} (small : digit < 10) (previous : Nat) :
    10 * previous + ((UInt8.ofNat (48+digit)).toNat - 48) = 10 * previous + digit := by
  rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  omega

private theorem core_decimalByteValue (fuel number : Nat) (tail : List Char) (enough : number < fuel) :
    decimalByteValue (Nat.toDigitsCore 10 fuel number tail).utf8Encode.data.toList 0 =
      decimalByteValue tail.utf8Encode.data.toList number := by
  induction fuel generalizing number tail with
  | zero => omega
  | succ fuel ih =>
      rw [Nat.toDigitsCore]
      have small : number % 10 < 10 := Nat.mod_lt _ (by decide)
      by_cases finished : number / 10 = 0
      · rw [if_pos finished, digit_bytes small]
        simp only [decimalByteValue, List.foldl_cons, Nat.mul_zero, Nat.zero_add]
        rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
        congr 1
        omega
      · rw [if_neg finished, ih (number / 10) (Nat.digitChar (number % 10) :: tail) (by omega)]
        rw [digit_bytes small]
        simp only [decimalByteValue, List.foldl_cons]
        rw [digit_step small]
        congr 1
        omega

private theorem repr_decimalByteValue (number : Nat) :
    decimalByteValue number.repr.toByteArray.data.toList 0 = number := by
  change decimalByteValue (Nat.toDigitsCore 10 (number+1) number []).utf8Encode.data.toList 0 = number
  rw [core_decimalByteValue _ _ _ (by omega)]
  rfl

private theorem repr_injective : Function.Injective Nat.repr := by
  intro first second same
  have reading := congrArg (fun encoded => decimalByteValue encoded.toByteArray.data.toList 0) same
  exact (repr_decimalByteValue first).symm.trans (reading.trans (repr_decimalByteValue second))

private theorem distinguish (first second : String) : "_core_s" ++ first ≠ "_core_p" ++ second := by
  intro same
  have bytes := congrArg (fun encoded => encoded.toByteArray.data.toList) same
  simp only [String.toByteArray_append, ByteArray.data_append, Array.toList_append] at bytes
  change ([95, 99, 111, 114, 101, 95, 115] : List UInt8) ++ first.toByteArray.data.toList =
    [95, 99, 111, 114, 101, 95, 112] ++ second.toByteArray.data.toList at bytes
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at bytes
  exact (by decide : (115 : UInt8) ≠ 112) bytes.2.2.2.2.2.2.1

def setName (depth : Nat) : String := "_core_s" ++ toString depth
def propName (depth : Nat) : String := "_core_p" ++ toString depth

theorem setName_injective : Function.Injective setName := by
  intro first second same
  exact repr_injective ((String.append_right_inj "_core_s").mp same)

theorem propName_injective : Function.Injective propName := by
  intro first second same
  exact repr_injective ((String.append_right_inj "_core_p").mp same)

theorem names_disjoint (first second : Nat) : setName first ≠ propName second :=
  distinguish (toString first) (toString second)

/-- A nearest-binder lookup retaining the actual typed variable index. -/
def lookup : {count : Nat} → (Fin count → String) → String → Option (Fin count)
  | 0, _, _ => none
  | count+1, environment, name =>
      if environment 0 = name then some 0
      else Fin.succ <$> lookup (fun index : Fin count => environment index.succ) name

theorem lookup_absent {count : Nat} (environment : Fin count → String) (name : String)
    (absent : ∀ index, environment index ≠ name) : lookup environment name = none := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [lookup, if_neg (absent 0), ih _ (fun index => absent index.succ)]
      rfl

theorem lookup_index {count : Nat} (environment : Fin count → String)
    (unique : Function.Injective environment) (index : Fin count) :
    lookup environment (environment index) = some index := by
  induction count with
  | zero => exact Fin.elim0 index
  | succ count ih =>
      refine Fin.cases ?_ (fun earlier => ?_) index
      · simp [lookup]
      · have different : environment 0 ≠ environment earlier.succ := by
          intro same
          exact Fin.succ_ne_zero earlier (unique same).symm
        have tailUnique : Function.Injective (fun old : Fin count => environment old.succ) := by
          intro first second same
          exact Fin.succ_injective _ (unique same)
        simp only [lookup, if_neg different, ih _ tailUnique earlier]
        rfl

def Fresh {sets props : Nat} (name : String) (environment : Fin sets → String)
    (propositions : Fin props → String) : Prop :=
  lookup environment name = none ∧ lookup propositions name = none

instance {sets props : Nat} (name : String) (environment : Fin sets → String)
    (propositions : Fin props → String) : Decidable (Fresh name environment propositions) :=
  inferInstanceAs (Decidable (_ ∧ _))

structure Scope {sets props : Nat} (environment : Fin sets → String)
    (propositions : Fin props → String) : Prop where
  set_unique : Function.Injective environment
  prop_unique : Function.Injective propositions
  set_earlier : ∀ index, ∃ depth, depth < sets+props ∧ environment index = setName depth
  prop_earlier : ∀ index, ∃ depth, depth < sets+props ∧ propositions index = propName depth

theorem Scope.set_fresh {sets props : Nat} {environment : Fin sets → String}
    {propositions : Fin props → String} (scope : Scope environment propositions) :
    Fresh (setName (sets+props)) environment propositions := by
  constructor
  · apply lookup_absent
    intro index same
    obtain ⟨depth, earlier, name⟩ := scope.set_earlier index
    have equal := setName_injective (name.symm.trans same)
    omega
  · apply lookup_absent
    intro index same
    obtain ⟨depth, _, name⟩ := scope.prop_earlier index
    exact names_disjoint (sets+props) depth (same.symm.trans name)

theorem Scope.prop_fresh {sets props : Nat} {environment : Fin sets → String}
    {propositions : Fin props → String} (scope : Scope environment propositions) :
    Fresh (propName (sets+props)) environment propositions := by
  constructor
  · apply lookup_absent
    intro index same
    obtain ⟨depth, _, name⟩ := scope.set_earlier index
    exact names_disjoint depth (sets+props) (name.symm.trans same)
  · apply lookup_absent
    intro index same
    obtain ⟨depth, earlier, name⟩ := scope.prop_earlier index
    have equal := propName_injective (name.symm.trans same)
    omega

theorem prepend_injective {count : Nat} (environment : Fin count → String)
    (unique : Function.Injective environment) (name : String)
    (fresh : ∀ index, name ≠ environment index) :
    Function.Injective (Fin.cases name environment) := by
  intro first
  refine Fin.cases ?_ (fun previous => ?_) first
  · intro second
    refine Fin.cases (fun _ => rfl) (fun previous contradicts => ?_) second
    exact (fresh previous contradicts).elim
  · intro second
    refine Fin.cases (fun contradicts => ?_) (fun other agrees => ?_) second
    · exact (fresh previous contradicts.symm).elim
    · exact congrArg Fin.succ (unique agrees)

theorem Scope.pushSet {sets props : Nat} {environment : Fin sets → String}
    {propositions : Fin props → String} (scope : Scope environment propositions) :
    Scope (Fin.cases (setName (sets+props)) environment) propositions where
  set_unique := prepend_injective environment scope.set_unique _ (by
    intro index same
    obtain ⟨depth, earlier, name⟩ := scope.set_earlier index
    have equal := setName_injective (same.trans name)
    omega)
  prop_unique := scope.prop_unique
  set_earlier index := Fin.cases
    ⟨sets+props, by omega, rfl⟩
    (fun previous => by
      obtain ⟨depth, earlier, name⟩ := scope.set_earlier previous
      exact ⟨depth, by omega, name⟩) index
  prop_earlier index := by
    obtain ⟨depth, earlier, name⟩ := scope.prop_earlier index
    exact ⟨depth, by omega, name⟩

theorem Scope.pushProp {sets props : Nat} {environment : Fin sets → String}
    {propositions : Fin props → String} (scope : Scope environment propositions) :
    Scope environment (Fin.cases (propName (sets+props)) propositions) where
  set_unique := scope.set_unique
  prop_unique := prepend_injective propositions scope.prop_unique _ (by
    intro index same
    obtain ⟨depth, earlier, name⟩ := scope.prop_earlier index
    have equal := propName_injective (same.trans name)
    omega)
  set_earlier index := by
    obtain ⟨depth, earlier, name⟩ := scope.set_earlier index
    exact ⟨depth, by omega, name⟩
  prop_earlier index := Fin.cases
    ⟨sets+props, by omega, rfl⟩
    (fun previous => by
      obtain ⟨depth, earlier, name⟩ := scope.prop_earlier previous
      exact ⟨depth, by omega, name⟩) index

theorem emptyScope : Scope (sets := 0) (props := 0) Fin.elim0 Fin.elim0 where
  set_unique first := Fin.elim0 first
  prop_unique first := Fin.elim0 first
  set_earlier index := Fin.elim0 index
  prop_earlier index := Fin.elim0 index

def depth : {sets props : Nat} → Logical sets props → Nat
  | _, _, .equal _ _ | _, _, .member _ _ | _, _, .proposition _ => 1
  | _, _, .imply first second => max (depth first) (depth second) + 1
  | _, _, .allSet body | _, _, .allProp body => depth body + 1

def decode : Nat → (sets props : Nat) → (Fin sets → String) → (Fin props → String) →
    WireTerm → Option (Logical sets props)
  | 0, _, _, _, _, _ => none
  | fuel+1, sets, props, environment, propositions, term =>
      match term with
      | .list [.symbol "eq", .symbol "set", .symbol first, .symbol second] => do
          return .equal (← lookup environment first) (← lookup environment second)
      | .list [.symbol "In", .symbol child, .symbol parent] => do
          return .member (← lookup environment child) (← lookup environment parent)
      | .symbol name => .proposition <$> lookup propositions name
      | .list [.symbol "imp", first, second] => do
          return .imply (← decode fuel sets props environment propositions first)
            (← decode fuel sets props environment propositions second)
      | .list [.symbol "all", .symbol "set", .list [.symbol "lam", .symbol name, body]] =>
          if Fresh name environment propositions then
            .allSet <$> decode fuel (sets+1) props (Fin.cases name environment) propositions body
          else none
      | .list [.symbol "all", .symbol "prop", .list [.symbol "lam", .symbol name, body]] =>
          if Fresh name environment propositions then
            .allProp <$> decode fuel sets (props+1) environment (Fin.cases name propositions) body
          else none
      | _ => none

theorem decode_encode {sets props : Nat} (body : Logical sets props)
    (fuel : Nat) (enough : depth body ≤ fuel) (environment : Fin sets → String)
    (propositions : Fin props → String) (scope : Scope environment propositions) :
    decode fuel sets props environment propositions (encode body environment propositions) = some body := by
  induction body generalizing fuel with
  | equal first second =>
      cases fuel with
      | zero => simp [depth] at enough
      | succ fuel => simp [encode, decode, lookup_index environment scope.set_unique]
  | member child parent =>
      cases fuel with
      | zero => simp [depth] at enough
      | succ fuel => simp [encode, decode, lookup_index environment scope.set_unique]
  | proposition index =>
      cases fuel with
      | zero => simp [depth] at enough
      | succ fuel => simp [encode, decode, lookup_index propositions scope.prop_unique]
  | imply first second firstIH secondIH =>
      cases fuel with
      | zero => simp [depth] at enough
      | succ fuel =>
          have firstBound : depth first ≤ fuel := by simp only [depth] at enough; omega
          have secondBound : depth second ≤ fuel := by simp only [depth] at enough; omega
          simp [encode, decode, firstIH fuel firstBound environment propositions scope,
            secondIH fuel secondBound environment propositions scope]
  | @allSet sets props body bodyIH =>
      cases fuel with
      | zero => simp [depth] at enough
      | succ fuel =>
          have bound : depth body ≤ fuel := Nat.le_of_succ_le_succ enough
          change (if Fresh (setName (sets+props)) environment propositions then
            Logical.allSet <$> decode fuel (sets+1) props
              (Fin.cases (setName (sets+props)) environment) propositions
              (encode body (Fin.cases (setName (sets+props)) environment) propositions)
            else none) = some (Logical.allSet body)
          rw [if_pos scope.set_fresh, bodyIH fuel bound _ _ scope.pushSet]
          rfl
  | @allProp sets props body bodyIH =>
      cases fuel with
      | zero => simp [depth] at enough
      | succ fuel =>
          have bound : depth body ≤ fuel := Nat.le_of_succ_le_succ enough
          change (if Fresh (propName (sets+props)) environment propositions then
            Logical.allProp <$> decode fuel sets (props+1) environment
              (Fin.cases (propName (sets+props)) propositions)
              (encode body environment (Fin.cases (propName (sets+props)) propositions))
            else none) = some (Logical.allProp body)
          rw [if_pos scope.prop_fresh, bodyIH fuel bound _ _ scope.pushProp]
          rfl

/-- Every closed logical term reconstructs with its exact two de Bruijn
namespaces, after all lexical names have been resolved independently. -/
theorem decode_closed (body : Logical 0 0) (fuel : Nat) (enough : depth body ≤ fuel) :
    decode fuel 0 0 Fin.elim0 Fin.elim0 (encode body Fin.elim0 Fin.elim0) = some body :=
  decode_encode body fuel enough Fin.elim0 Fin.elim0 emptyScope

theorem decode_encodeSentence (body : Formula 0) (fuel : Nat)
    (enough : depth (compile body 0) ≤ fuel) :
    decode fuel 0 0 Fin.elim0 Fin.elim0 (encodeSentence body) = some (compile body 0) :=
  decode_closed (compile body 0) fuel enough

theorem closed_encode_injective :
    Function.Injective (fun body : Logical 0 0 => encode body Fin.elim0 Fin.elim0) := by
  intro first second same
  let fuel := max (depth first) (depth second)
  have decoded := congrArg (decode fuel 0 0 Fin.elim0 Fin.elim0) same
  rw [decode_closed first fuel (Nat.le_max_left _ _),
    decode_closed second fuel (Nat.le_max_right _ _)] at decoded
  exact Option.some.inj decoded

/-- The decoded closed surface has the original material sentence's
ordinary meaning for every carrier and membership relation. -/
theorem decoded_sentence_meaning {S : Type*} (member : S → S → Prop)
    (body : Formula 0) (fuel : Nat) (enough : depth (compile body 0) ≤ fuel)
    (decoded : Logical 0 0)
    (accepted : decode fuel 0 0 Fin.elim0 Fin.elim0 (encodeSentence body) = some decoded) :
    evaluate member decoded Fin.elim0 Fin.elim0 ↔
      Mettapedia.SetTheory.CarveOuts.Sites.Tarski member body Fin.elim0 := by
  rw [decode_encodeSentence body fuel enough] at accepted
  cases Option.some.inj accepted
  exact evaluate_compile member body 0 Fin.elim0 Fin.elim0

theorem unknown_set_name_rejected (name : String) (fuel props : Nat)
    (propositions : Fin props → String) :
    decode fuel 0 props Fin.elim0 propositions
      (.list [.symbol "In", .symbol name, .symbol name]) = none := by
  cases fuel <;> rfl

theorem unknown_proposition_name_rejected (name : String) (fuel sets : Nat)
    (environment : Fin sets → String) :
    decode fuel sets 0 environment Fin.elim0 (.symbol name) = none := by
  cases fuel <;> rfl

/-- An arbitrary open naming environment may collide with the generated
binder; the closed reconstruction theorem does not assert otherwise. -/
theorem open_capture_has_same_encoding :
    encode (Logical.allSet (Logical.equal 0 1) : Logical 1 0)
      (fun _ => setName 1) Fin.elim0 =
    encode (Logical.allSet (Logical.equal 0 0) : Logical 1 0)
      (fun _ => setName 1) Fin.elim0 := rfl

theorem open_capture_terms_differ :
    (Logical.allSet (Logical.equal 0 1) : Logical 1 0) ≠
      Logical.allSet (Logical.equal 0 0) := by
  intro same
  have indices : (1 : Fin 2) = 0 := (Logical.equal.inj (Logical.allSet.inj same)).2
  exact (by decide : (1 : Fin 2) ≠ 0) indices

theorem open_capture_rejected (fuel : Nat) :
    decode fuel 1 0 (fun _ => setName 1) Fin.elim0
      (encode (Logical.allSet (Logical.equal 0 1) : Logical 1 0)
        (fun _ => setName 1) Fin.elim0) = none := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      simp [encode, decode, Fresh, lookup, setName]

end Mettapedia.SetTheory.Profiles.CommonCoreNativeScope
