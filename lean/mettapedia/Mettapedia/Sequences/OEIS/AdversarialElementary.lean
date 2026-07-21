import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mettapedia.Sequences.OEIS.Constructions
import Mettapedia.Sequences.OEIS.Elementary49
import Mettapedia.Sequences.OEIS.OrderedPredicate

/-!
# Candidate-independent elementary specifications from the weak-evidence cohort

This module records the source-locked mathematical specifications that reduce
to recurrences, finite products, closed forms, or elementary ordered
predicates.  It contains no candidate programs and makes no claim that a
candidate realizes any specification.
-/

namespace Mettapedia.Sequences.OEIS.AdversarialElementary

open scoped BigOperators
open Mettapedia.Sequences.OEIS.Constructions
open Mettapedia.Sequences.OEIS.Elementary49

namespace A103527
def source := sourceOf "A103527" "2eb698b423497f05072b55befdbdad6b3ca8d047e25e396ef16c024ff7bfc2b5" 0
def values : Nat → Nat := firstOrder 2 (fun previous => 2 ^ previous + previous)
def spec := totalNatSpec 0 values
def formalization := formalizationOf source spec
end A103527

namespace A034797
def source := sourceOf "A034797" "03f1f34fec1df2f5df5a1095579402df5d3d42ce9b924a99891829589a790f70" 0
def values : Nat → Nat := firstOrder 0 (fun previous => previous + 2 ^ previous)
def spec := totalNatSpec 0 values
def formalization := formalizationOf source spec
end A034797

namespace A174736
def source := sourceOf "A174736" "17e8abc45d49b00e4f0c8e9bd0f30ffbf3bad8b1b74d8215ba7b4281a64f14aa" 1
def values (position : Nat) : Nat := 2 ^ ((2 * 4 ^ position + 1) / 3)
def spec := totalNatSpec 1 values
def formalization := formalizationOf source spec
end A174736

namespace A243669
def source := sourceOf "A243669" "2d820596d92fba27e045b6208b9e3b4302c72211f1ebba9b87f04c332a76eca1" 1
def values : Nat → Int := secondOrder 1 5 (fun earlier later => 6 * later - 2 * earlier)
def spec := totalIntSpec 1 values
def formalization := formalizationOf source spec
end A243669

namespace A005018
def source := sourceOf "A005018" "bc563e6f1a9ea76fcfda3ff0301c740ed075eae5a67d18dba4d67a566ca44333" 1
def Qualifies (value : Nat) : Prop := 0 < value ∧ value ∣ 20
noncomputable def spec := OrderedPredicate.spec 1 Qualifies
noncomputable def formalization := formalizationOf source spec
end A005018

namespace A018351
def source := sourceOf "A018351" "0e4df084088218437696bbedae9de947464d68143ec4bf35b4c67b6251b2f79c" 1
def Qualifies (value : Nat) : Prop := 0 < value ∧ value ∣ 242
noncomputable def spec := OrderedPredicate.spec 1 Qualifies
noncomputable def formalization := formalizationOf source spec
end A018351

namespace A050923
def source := sourceOf "A050923" "f54f9244a1f16749ecc6772ff5283c8d1fa5197cf11f298d77541bba86ca82b3" 0
def values (position : Nat) : Nat := 2 ^ position.factorial
def spec := totalNatSpec 0 values
def formalization := formalizationOf source spec
end A050923

namespace A166999
def source := sourceOf "A166999" "656da9bb87f68e550417ad01a626695112d0de58c63bcd14242630ca2941c59f" 0
def values : Nat → Nat :=
  firstOrder 1 (fun previous => previous + previous ^ 2 + previous ^ 3)
def spec := totalNatSpec 0 values
def formalization := formalizationOf source spec
end A166999

namespace A185092
def source := sourceOf "A185092" "710f5dd689368c53a69545ff5914415d1f34d047a4668ab81ca77dd47cd2045c" 1
def Qualifies (value : Nat) : Prop := 0 < value ∧ value ∣ 12
noncomputable def spec := OrderedPredicate.spec 1 Qualifies
noncomputable def formalization := formalizationOf source spec
end A185092

namespace A323383
def source := sourceOf "A323383" "a36ee345593a5d1037a03812e3d83f1b0be98d17f0cdad8d9f81f004a03c780b" 1
def Qualifies (value : Nat) : Prop := 0 < value ∧ value < 24 ∧ value ∣ 24
noncomputable def spec := OrderedPredicate.spec 1 Qualifies
noncomputable def formalization := formalizationOf source spec
end A323383

namespace A005776
def source := sourceOf "A005776" "6088f438aa18b23a8044a1fc4987022765116e9a5470d48a24e8db65348b6eea" 1
def Qualifies (value : Nat) : Prop := 0 < value ∧ value < 30 ∧ Nat.Coprime value 30
noncomputable def spec := OrderedPredicate.spec 1 Qualifies
noncomputable def formalization := formalizationOf source spec
end A005776

namespace A168320
def source := sourceOf "A168320" "6df0beebe1b5d618c306b9e5887e995c6049b0ad141b4dbb008ee57af89849b9" 0
def values : Nat → Nat :=
  indexedFirstOrder 1 (fun position previous => previous ^ 2 + 2 ^ position)
def spec := totalNatSpec 0 values
def formalization := formalizationOf source spec
end A168320

namespace A300361
def source := sourceOf "A300361" "77b227cb9fde205e3601c284f7b5311d1321a381a05ee06676b1431160f7ab07" 0
def values (position : Nat) : Nat := 2 ^ (2 ^ position - position)
def spec := totalNatSpec 0 values
def formalization := formalizationOf source spec
end A300361

namespace A027875
def source := sourceOf "A027875" "a7d5482b15c07d3079f7c7ab1822c5089c8405f78812b63842487a9bceff98df" 0
def values (position : Nat) : Nat := initialProduct (fun index => 7 ^ index - 1) position
def spec := totalNatSpec 0 values
def formalization := formalizationOf source spec
end A027875

namespace A092596
def source := sourceOf "A092596" "fb61077c7509e84d65abcf1dcfcbca50799aa9602d02f0f740ce29c2874dfd9b" 1
def digitSum10 (value : Nat) : Nat := (Nat.digits 10 value).sum
def Qualifies (value : Nat) : Prop := 2 * digitSum10 value > value
noncomputable def spec := OrderedPredicate.spec 1 Qualifies
noncomputable def formalization := formalizationOf source spec
end A092596

namespace A285198
def source := sourceOf "A285198" "c1bd6802587a703189bb71eb7be10c48cc0c680c34cfb1bd9449fb3a204c094e" 0
def values (position : Nat) : Nat := Nat.choose 9 position
def spec := boundedNatSpec 0 10 values
def formalization := formalizationOf source spec
end A285198

namespace A002109
def source := sourceOf "A002109" "1475648eb9391292f37daf3f7cd3c85ff89c2c457265a218621a3a9e7b59e7ea" 0
def values (position : Nat) : Nat := initialProduct (fun index => index ^ index) position
def spec := totalNatSpec 0 values
def formalization := formalizationOf source spec
end A002109

namespace A096313
def source := sourceOf "A096313" "5b7a01402bca816d0cf1f68dccda562382898cbb2745bbf3aa20ca7b1b8495ba" 0
def values (position : Nat) : Nat :=
  (position + 1).factorial * initialProduct Nat.factorial (position - 1)
def spec := totalNatSpec 0 values
def formalization := formalizationOf source spec
end A096313

namespace A176369
def source := sourceOf "A176369" "015a394f99b893038bdfaba5b50f49f283aac89d4d9a2a015e3afd546ea54d92" 1
def values : Nat → Int := secondOrder 0 16 (fun earlier later => 258 * later - earlier)
def spec := totalIntSpec 1 values
def formalization := formalizationOf source spec
end A176369

namespace A214706
def source := sourceOf "A214706" "b0220da34943390caeeabd168d2b74bec18c816f40a0f370a26ef3f37fa60b49" 0
def values : Nat → Nat := secondOrder 1 5 (fun earlier later => later * earlier)
def spec := totalNatSpec 0 values
def formalization := formalizationOf source spec
end A214706

namespace A083667
def source := sourceOf "A083667" "740c7eece7afd8e157cd1a7b78b6dfe612771f7cdedc5547ef0e5de046cac8c5" 0
def values (position : Nat) : Nat := 2 ^ position * 3 ^ Nat.choose position 2
def spec := totalNatSpec 0 values
def formalization := formalizationOf source spec
end A083667

namespace A016809
def source := sourceOf "A016809" "ff4f2220a3a4441f3ac1c8ea48b707aa525f168a24c67e23d33f54e029c0e264" 0
def values (position : Nat) : Nat := (4 * position) ^ 9
def spec := totalNatSpec 0 values
def formalization := formalizationOf source spec
end A016809

namespace A076111
def source := sourceOf "A076111" "fb6b68afc936d2bc36f0c731ad163b1029034d5cdc84d5e9c6f7b8c98655c4f2" 0
def values (position : Nat) : Nat :=
  ∏ index ∈ Finset.range position, (1 + position * (index + 1))
def spec := totalNatSpec 0 values
def formalization := formalizationOf source spec
end A076111

namespace A097736
def source := sourceOf "A097736" "0c429be7e0a32e56264e39ae89d06cc33fc63adc6a3cf2a45f34de7236f5d339" 0
def values : Nat → Int := secondOrder 1 257 (fun earlier later => 258 * later - earlier)
def spec := totalIntSpec 0 values
def formalization := formalizationOf source spec
end A097736

/-- The 24 source-locked elementary specifications in this tranche. -/
noncomputable def registry : List (String × SequenceSpec) :=
  [("A103527", A103527.spec), ("A034797", A034797.spec),
   ("A174736", A174736.spec), ("A243669", A243669.spec),
   ("A005018", A005018.spec), ("A018351", A018351.spec),
   ("A050923", A050923.spec), ("A166999", A166999.spec),
   ("A185092", A185092.spec), ("A323383", A323383.spec),
   ("A005776", A005776.spec), ("A168320", A168320.spec),
   ("A300361", A300361.spec), ("A027875", A027875.spec),
   ("A092596", A092596.spec), ("A285198", A285198.spec),
   ("A002109", A002109.spec), ("A096313", A096313.spec),
   ("A176369", A176369.spec), ("A214706", A214706.spec),
   ("A083667", A083667.spec), ("A016809", A016809.spec),
   ("A076111", A076111.spec), ("A097736", A097736.spec)]

theorem registry_length : registry.length = 24 := by rfl

/-! Representative recurrence and boundary checks. -/

example : A103527.values 0 = 2 := rfl
example : A103527.values 1 = 6 := by norm_num [A103527.values, firstOrder]
example : A285198.values 10 = 0 := by simp [A285198.values]
example : ¬ A285198.spec.Domain (A285198.spec.index 10) := by
  simp [A285198.spec, boundedNatSpec, SequenceSpec.index]

#print axioms registry_length

end Mettapedia.Sequences.OEIS.AdversarialElementary
