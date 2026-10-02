import Mettapedia.GSLT.LanguageDef.NativeOpsSourceGuestLex
import Mettapedia.GSLT.LanguageDef.NativeOpsSourceGuestScan
import Mettapedia.GSLT.LanguageDef.NativeOpsText
import Mettapedia.GSLT.Parsing.SourceSExprAdmission

import Mettapedia.GSLT.Parsing.SourceSExprSafety

/-! Actual operational component admitted through the existing complete carrier parser. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
set_option Elab.async false

namespace Mettapedia.GSLT.LanguageDef.NativeOpsSourceGuestAdmission

open Mettapedia.GSLT.Parsing
open NativeOps NativeOpsSourceGuestSnapshot

theorem syntax_000_safe : SExprTokenRoundTrip.safe syntax_000 :=
  (SourceSExprSafety.safeBool_iff syntax_000).mp (by decide +kernel)

theorem syntax_001_safe : SExprTokenRoundTrip.safe syntax_001 :=
  (SourceSExprSafety.safeBool_iff syntax_001).mp (by decide +kernel)

theorem syntax_002_safe : SExprTokenRoundTrip.safe syntax_002 :=
  (SourceSExprSafety.safeBool_iff syntax_002).mp (by decide +kernel)

theorem syntax_003_safe : SExprTokenRoundTrip.safe syntax_003 :=
  (SourceSExprSafety.safeBool_iff syntax_003).mp (by decide +kernel)

theorem syntax_004_safe : SExprTokenRoundTrip.safe syntax_004 :=
  (SourceSExprSafety.safeBool_iff syntax_004).mp (by decide +kernel)

theorem syntax_005_safe : SExprTokenRoundTrip.safe syntax_005 :=
  (SourceSExprSafety.safeBool_iff syntax_005).mp (by decide +kernel)

theorem syntax_006_safe : SExprTokenRoundTrip.safe syntax_006 :=
  (SourceSExprSafety.safeBool_iff syntax_006).mp (by decide +kernel)

theorem syntax_007_safe : SExprTokenRoundTrip.safe syntax_007 :=
  (SourceSExprSafety.safeBool_iff syntax_007).mp (by decide +kernel)

theorem syntax_008_safe : SExprTokenRoundTrip.safe syntax_008 :=
  (SourceSExprSafety.safeBool_iff syntax_008).mp (by decide +kernel)

theorem syntax_009_safe : SExprTokenRoundTrip.safe syntax_009 :=
  (SourceSExprSafety.safeBool_iff syntax_009).mp (by decide +kernel)

theorem syntax_010_safe : SExprTokenRoundTrip.safe syntax_010 :=
  (SourceSExprSafety.safeBool_iff syntax_010).mp (by decide +kernel)

theorem syntax_011_safe : SExprTokenRoundTrip.safe syntax_011 :=
  (SourceSExprSafety.safeBool_iff syntax_011).mp (by decide +kernel)

theorem syntax_012_safe : SExprTokenRoundTrip.safe syntax_012 :=
  (SourceSExprSafety.safeBool_iff syntax_012).mp (by decide +kernel)

theorem syntax_013_safe : SExprTokenRoundTrip.safe syntax_013 :=
  (SourceSExprSafety.safeBool_iff syntax_013).mp (by decide +kernel)

theorem syntax_014_safe : SExprTokenRoundTrip.safe syntax_014 :=
  (SourceSExprSafety.safeBool_iff syntax_014).mp (by decide +kernel)

theorem syntax_015_safe : SExprTokenRoundTrip.safe syntax_015 :=
  (SourceSExprSafety.safeBool_iff syntax_015).mp (by decide +kernel)

theorem syntax_016_safe : SExprTokenRoundTrip.safe syntax_016 :=
  (SourceSExprSafety.safeBool_iff syntax_016).mp (by decide +kernel)

theorem syntax_017_safe : SExprTokenRoundTrip.safe syntax_017 :=
  (SourceSExprSafety.safeBool_iff syntax_017).mp (by decide +kernel)

theorem syntax_018_safe : SExprTokenRoundTrip.safe syntax_018 :=
  (SourceSExprSafety.safeBool_iff syntax_018).mp (by decide +kernel)

theorem syntax_019_safe : SExprTokenRoundTrip.safe syntax_019 :=
  (SourceSExprSafety.safeBool_iff syntax_019).mp (by decide +kernel)

theorem syntax_020_safe : SExprTokenRoundTrip.safe syntax_020 :=
  (SourceSExprSafety.safeBool_iff syntax_020).mp (by decide +kernel)

theorem syntax_021_safe : SExprTokenRoundTrip.safe syntax_021 :=
  (SourceSExprSafety.safeBool_iff syntax_021).mp (by decide +kernel)

theorem syntax_022_safe : SExprTokenRoundTrip.safe syntax_022 :=
  (SourceSExprSafety.safeBool_iff syntax_022).mp (by decide +kernel)

theorem syntax_023_safe : SExprTokenRoundTrip.safe syntax_023 :=
  (SourceSExprSafety.safeBool_iff syntax_023).mp (by decide +kernel)

theorem syntax_024_safe : SExprTokenRoundTrip.safe syntax_024 :=
  (SourceSExprSafety.safeBool_iff syntax_024).mp (by decide +kernel)

theorem syntax_025_safe : SExprTokenRoundTrip.safe syntax_025 :=
  (SourceSExprSafety.safeBool_iff syntax_025).mp (by decide +kernel)

theorem syntax_026_safe : SExprTokenRoundTrip.safe syntax_026 :=
  (SourceSExprSafety.safeBool_iff syntax_026).mp (by decide +kernel)

theorem syntax_027_safe : SExprTokenRoundTrip.safe syntax_027 :=
  (SourceSExprSafety.safeBool_iff syntax_027).mp (by decide +kernel)

theorem syntax_028_safe : SExprTokenRoundTrip.safe syntax_028 :=
  (SourceSExprSafety.safeBool_iff syntax_028).mp (by decide +kernel)

theorem syntax_029_safe : SExprTokenRoundTrip.safe syntax_029 :=
  (SourceSExprSafety.safeBool_iff syntax_029).mp (by decide +kernel)

theorem syntax_030_safe : SExprTokenRoundTrip.safe syntax_030 :=
  (SourceSExprSafety.safeBool_iff syntax_030).mp (by decide +kernel)

theorem syntax_031_safe : SExprTokenRoundTrip.safe syntax_031 :=
  (SourceSExprSafety.safeBool_iff syntax_031).mp (by decide +kernel)

theorem syntax_032_safe : SExprTokenRoundTrip.safe syntax_032 :=
  (SourceSExprSafety.safeBool_iff syntax_032).mp (by decide +kernel)

theorem syntax_033_safe : SExprTokenRoundTrip.safe syntax_033 :=
  (SourceSExprSafety.safeBool_iff syntax_033).mp (by decide +kernel)

theorem syntax_034_safe : SExprTokenRoundTrip.safe syntax_034 :=
  (SourceSExprSafety.safeBool_iff syntax_034).mp (by decide +kernel)

theorem syntax_035_safe : SExprTokenRoundTrip.safe syntax_035 :=
  (SourceSExprSafety.safeBool_iff syntax_035).mp (by decide +kernel)

theorem syntax_036_safe : SExprTokenRoundTrip.safe syntax_036 :=
  (SourceSExprSafety.safeBool_iff syntax_036).mp (by decide +kernel)

theorem syntax_037_safe : SExprTokenRoundTrip.safe syntax_037 :=
  (SourceSExprSafety.safeBool_iff syntax_037).mp (by decide +kernel)

theorem syntax_038_safe : SExprTokenRoundTrip.safe syntax_038 :=
  (SourceSExprSafety.safeBool_iff syntax_038).mp (by decide +kernel)

theorem syntax_039_safe : SExprTokenRoundTrip.safe syntax_039 :=
  (SourceSExprSafety.safeBool_iff syntax_039).mp (by decide +kernel)

theorem syntax_040_safe : SExprTokenRoundTrip.safe syntax_040 :=
  (SourceSExprSafety.safeBool_iff syntax_040).mp (by decide +kernel)

theorem syntax_041_safe : SExprTokenRoundTrip.safe syntax_041 :=
  (SourceSExprSafety.safeBool_iff syntax_041).mp (by decide +kernel)

theorem syntax_042_safe : SExprTokenRoundTrip.safe syntax_042 :=
  (SourceSExprSafety.safeBool_iff syntax_042).mp (by decide +kernel)

theorem syntax_043_safe : SExprTokenRoundTrip.safe syntax_043 :=
  (SourceSExprSafety.safeBool_iff syntax_043).mp (by decide +kernel)

theorem syntax_044_safe : SExprTokenRoundTrip.safe syntax_044 :=
  (SourceSExprSafety.safeBool_iff syntax_044).mp (by decide +kernel)

theorem syntax_045_safe : SExprTokenRoundTrip.safe syntax_045 :=
  (SourceSExprSafety.safeBool_iff syntax_045).mp (by decide +kernel)

theorem syntax_046_safe : SExprTokenRoundTrip.safe syntax_046 :=
  (SourceSExprSafety.safeBool_iff syntax_046).mp (by decide +kernel)

theorem syntax_047_safe : SExprTokenRoundTrip.safe syntax_047 :=
  (SourceSExprSafety.safeBool_iff syntax_047).mp (by decide +kernel)

theorem syntax_048_safe : SExprTokenRoundTrip.safe syntax_048 :=
  (SourceSExprSafety.safeBool_iff syntax_048).mp (by decide +kernel)

theorem syntax_049_safe : SExprTokenRoundTrip.safe syntax_049 :=
  (SourceSExprSafety.safeBool_iff syntax_049).mp (by decide +kernel)

theorem syntax_050_safe : SExprTokenRoundTrip.safe syntax_050 :=
  (SourceSExprSafety.safeBool_iff syntax_050).mp (by decide +kernel)

theorem syntax_051_safe : SExprTokenRoundTrip.safe syntax_051 :=
  (SourceSExprSafety.safeBool_iff syntax_051).mp (by decide +kernel)

theorem syntax_052_safe : SExprTokenRoundTrip.safe syntax_052 :=
  (SourceSExprSafety.safeBool_iff syntax_052).mp (by decide +kernel)

theorem syntax_053_safe : SExprTokenRoundTrip.safe syntax_053 :=
  (SourceSExprSafety.safeBool_iff syntax_053).mp (by decide +kernel)

theorem syntax_054_safe : SExprTokenRoundTrip.safe syntax_054 :=
  (SourceSExprSafety.safeBool_iff syntax_054).mp (by decide +kernel)

theorem syntax_055_safe : SExprTokenRoundTrip.safe syntax_055 :=
  (SourceSExprSafety.safeBool_iff syntax_055).mp (by decide +kernel)

theorem syntax_056_safe : SExprTokenRoundTrip.safe syntax_056 :=
  (SourceSExprSafety.safeBool_iff syntax_056).mp (by decide +kernel)

theorem syntax_057_safe : SExprTokenRoundTrip.safe syntax_057 :=
  (SourceSExprSafety.safeBool_iff syntax_057).mp (by decide +kernel)

theorem syntax_058_safe : SExprTokenRoundTrip.safe syntax_058 :=
  (SourceSExprSafety.safeBool_iff syntax_058).mp (by decide +kernel)

theorem syntax_059_safe : SExprTokenRoundTrip.safe syntax_059 :=
  (SourceSExprSafety.safeBool_iff syntax_059).mp (by decide +kernel)

theorem syntax_060_safe : SExprTokenRoundTrip.safe syntax_060 :=
  (SourceSExprSafety.safeBool_iff syntax_060).mp (by decide +kernel)

theorem syntax_061_safe : SExprTokenRoundTrip.safe syntax_061 :=
  (SourceSExprSafety.safeBool_iff syntax_061).mp (by decide +kernel)

theorem syntax_062_safe : SExprTokenRoundTrip.safe syntax_062 :=
  (SourceSExprSafety.safeBool_iff syntax_062).mp (by decide +kernel)

theorem syntax_063_safe : SExprTokenRoundTrip.safe syntax_063 :=
  (SourceSExprSafety.safeBool_iff syntax_063).mp (by decide +kernel)

theorem syntax_064_safe : SExprTokenRoundTrip.safe syntax_064 :=
  (SourceSExprSafety.safeBool_iff syntax_064).mp (by decide +kernel)

theorem syntax_065_safe : SExprTokenRoundTrip.safe syntax_065 :=
  (SourceSExprSafety.safeBool_iff syntax_065).mp (by decide +kernel)

theorem syntax_066_safe : SExprTokenRoundTrip.safe syntax_066 :=
  (SourceSExprSafety.safeBool_iff syntax_066).mp (by decide +kernel)

theorem syntax_067_safe : SExprTokenRoundTrip.safe syntax_067 :=
  (SourceSExprSafety.safeBool_iff syntax_067).mp (by decide +kernel)

theorem syntax_068_safe : SExprTokenRoundTrip.safe syntax_068 :=
  (SourceSExprSafety.safeBool_iff syntax_068).mp (by decide +kernel)

theorem syntax_069_safe : SExprTokenRoundTrip.safe syntax_069 :=
  (SourceSExprSafety.safeBool_iff syntax_069).mp (by decide +kernel)

theorem syntax_070_safe : SExprTokenRoundTrip.safe syntax_070 :=
  (SourceSExprSafety.safeBool_iff syntax_070).mp (by decide +kernel)

theorem syntax_071_safe : SExprTokenRoundTrip.safe syntax_071 :=
  (SourceSExprSafety.safeBool_iff syntax_071).mp (by decide +kernel)

theorem syntax_072_safe : SExprTokenRoundTrip.safe syntax_072 :=
  (SourceSExprSafety.safeBool_iff syntax_072).mp (by decide +kernel)

theorem syntax_073_safe : SExprTokenRoundTrip.safe syntax_073 :=
  (SourceSExprSafety.safeBool_iff syntax_073).mp (by decide +kernel)

theorem tail_074_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_074 := trivial

theorem tail_073_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_073 :=
  ⟨syntax_073_safe, tail_074_safe⟩

theorem tail_072_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_072 :=
  ⟨syntax_072_safe, tail_073_safe⟩

theorem tail_071_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_071 :=
  ⟨syntax_071_safe, tail_072_safe⟩

theorem tail_070_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_070 :=
  ⟨syntax_070_safe, tail_071_safe⟩

theorem tail_069_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_069 :=
  ⟨syntax_069_safe, tail_070_safe⟩

theorem tail_068_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_068 :=
  ⟨syntax_068_safe, tail_069_safe⟩

theorem tail_067_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_067 :=
  ⟨syntax_067_safe, tail_068_safe⟩

theorem tail_066_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_066 :=
  ⟨syntax_066_safe, tail_067_safe⟩

theorem tail_065_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_065 :=
  ⟨syntax_065_safe, tail_066_safe⟩

theorem tail_064_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_064 :=
  ⟨syntax_064_safe, tail_065_safe⟩

theorem tail_063_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_063 :=
  ⟨syntax_063_safe, tail_064_safe⟩

theorem tail_062_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_062 :=
  ⟨syntax_062_safe, tail_063_safe⟩

theorem tail_061_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_061 :=
  ⟨syntax_061_safe, tail_062_safe⟩

theorem tail_060_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_060 :=
  ⟨syntax_060_safe, tail_061_safe⟩

theorem tail_059_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_059 :=
  ⟨syntax_059_safe, tail_060_safe⟩

theorem tail_058_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_058 :=
  ⟨syntax_058_safe, tail_059_safe⟩

theorem tail_057_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_057 :=
  ⟨syntax_057_safe, tail_058_safe⟩

theorem tail_056_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_056 :=
  ⟨syntax_056_safe, tail_057_safe⟩

theorem tail_055_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_055 :=
  ⟨syntax_055_safe, tail_056_safe⟩

theorem tail_054_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_054 :=
  ⟨syntax_054_safe, tail_055_safe⟩

theorem tail_053_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_053 :=
  ⟨syntax_053_safe, tail_054_safe⟩

theorem tail_052_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_052 :=
  ⟨syntax_052_safe, tail_053_safe⟩

theorem tail_051_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_051 :=
  ⟨syntax_051_safe, tail_052_safe⟩

theorem tail_050_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_050 :=
  ⟨syntax_050_safe, tail_051_safe⟩

theorem tail_049_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_049 :=
  ⟨syntax_049_safe, tail_050_safe⟩

theorem tail_048_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_048 :=
  ⟨syntax_048_safe, tail_049_safe⟩

theorem tail_047_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_047 :=
  ⟨syntax_047_safe, tail_048_safe⟩

theorem tail_046_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_046 :=
  ⟨syntax_046_safe, tail_047_safe⟩

theorem tail_045_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_045 :=
  ⟨syntax_045_safe, tail_046_safe⟩

theorem tail_044_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_044 :=
  ⟨syntax_044_safe, tail_045_safe⟩

theorem tail_043_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_043 :=
  ⟨syntax_043_safe, tail_044_safe⟩

theorem tail_042_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_042 :=
  ⟨syntax_042_safe, tail_043_safe⟩

theorem tail_041_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_041 :=
  ⟨syntax_041_safe, tail_042_safe⟩

theorem tail_040_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_040 :=
  ⟨syntax_040_safe, tail_041_safe⟩

theorem tail_039_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_039 :=
  ⟨syntax_039_safe, tail_040_safe⟩

theorem tail_038_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_038 :=
  ⟨syntax_038_safe, tail_039_safe⟩

theorem tail_037_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_037 :=
  ⟨syntax_037_safe, tail_038_safe⟩

theorem tail_036_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_036 :=
  ⟨syntax_036_safe, tail_037_safe⟩

theorem tail_035_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_035 :=
  ⟨syntax_035_safe, tail_036_safe⟩

theorem tail_034_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_034 :=
  ⟨syntax_034_safe, tail_035_safe⟩

theorem tail_033_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_033 :=
  ⟨syntax_033_safe, tail_034_safe⟩

theorem tail_032_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_032 :=
  ⟨syntax_032_safe, tail_033_safe⟩

theorem tail_031_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_031 :=
  ⟨syntax_031_safe, tail_032_safe⟩

theorem tail_030_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_030 :=
  ⟨syntax_030_safe, tail_031_safe⟩

theorem tail_029_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_029 :=
  ⟨syntax_029_safe, tail_030_safe⟩

theorem tail_028_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_028 :=
  ⟨syntax_028_safe, tail_029_safe⟩

theorem tail_027_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_027 :=
  ⟨syntax_027_safe, tail_028_safe⟩

theorem tail_026_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_026 :=
  ⟨syntax_026_safe, tail_027_safe⟩

theorem tail_025_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_025 :=
  ⟨syntax_025_safe, tail_026_safe⟩

theorem tail_024_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_024 :=
  ⟨syntax_024_safe, tail_025_safe⟩

theorem tail_023_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_023 :=
  ⟨syntax_023_safe, tail_024_safe⟩

theorem tail_022_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_022 :=
  ⟨syntax_022_safe, tail_023_safe⟩

theorem tail_021_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_021 :=
  ⟨syntax_021_safe, tail_022_safe⟩

theorem tail_020_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_020 :=
  ⟨syntax_020_safe, tail_021_safe⟩

theorem tail_019_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_019 :=
  ⟨syntax_019_safe, tail_020_safe⟩

theorem tail_018_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_018 :=
  ⟨syntax_018_safe, tail_019_safe⟩

theorem tail_017_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_017 :=
  ⟨syntax_017_safe, tail_018_safe⟩

theorem tail_016_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_016 :=
  ⟨syntax_016_safe, tail_017_safe⟩

theorem tail_015_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_015 :=
  ⟨syntax_015_safe, tail_016_safe⟩

theorem tail_014_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_014 :=
  ⟨syntax_014_safe, tail_015_safe⟩

theorem tail_013_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_013 :=
  ⟨syntax_013_safe, tail_014_safe⟩

theorem tail_012_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_012 :=
  ⟨syntax_012_safe, tail_013_safe⟩

theorem tail_011_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_011 :=
  ⟨syntax_011_safe, tail_012_safe⟩

theorem tail_010_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_010 :=
  ⟨syntax_010_safe, tail_011_safe⟩

theorem tail_009_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_009 :=
  ⟨syntax_009_safe, tail_010_safe⟩

theorem tail_008_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_008 :=
  ⟨syntax_008_safe, tail_009_safe⟩

theorem tail_007_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_007 :=
  ⟨syntax_007_safe, tail_008_safe⟩

theorem tail_006_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_006 :=
  ⟨syntax_006_safe, tail_007_safe⟩

theorem tail_005_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_005 :=
  ⟨syntax_005_safe, tail_006_safe⟩

theorem tail_004_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_004 :=
  ⟨syntax_004_safe, tail_005_safe⟩

theorem tail_003_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_003 :=
  ⟨syntax_003_safe, tail_004_safe⟩

theorem tail_002_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_002 :=
  ⟨syntax_002_safe, tail_003_safe⟩

theorem tail_001_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_001 :=
  ⟨syntax_001_safe, tail_002_safe⟩

theorem tail_000_safe : SExprTokenRoundTrip.childrenSafe syntaxTail_000 :=
  ⟨syntax_000_safe, tail_001_safe⟩

theorem source_syntax_safe : SExprTokenRoundTrip.safe sourceSyntax := by
  change SExprTokenRoundTrip.safe (.atom "gslt-native-ops-v1") ∧
    SExprTokenRoundTrip.safe (.atom "VibeITPKernel") ∧
    SExprTokenRoundTrip.childrenSafe syntaxTail_000
  exact ⟨by simp [SExprTokenRoundTrip.safe], by simp [SExprTokenRoundTrip.safe],
    tail_000_safe⟩

theorem source_parsed : Algorithms.MeTTa.Simple.Parser.parseSExprWithDetailed
    MeTTailCore.MeTTaSyntax.petta componentText = .ok sourceSyntax :=
  SourceSExprAdmission.parsed_of_forms componentText sourceSyntax
    NativeOpsSourceGuestScan.split_forms_exact
    (SourceSExprAdmission.single_of_tokens componentText sourceSyntax source_syntax_safe
      NativeOpsSourceGuestLex.tokenized_exact)

theorem source_text_admitted : admitProgramText? primitiveCatalogue componentText =
    some expectedProgram :=
  admitProgramText?_of_parsed primitiveCatalogue componentText sourceSyntax expectedProgram
    source_parsed source_admitted

theorem source_text_no_extra_program (program : Program) :
    admitProgramText? primitiveCatalogue componentText = some program ↔ program = expectedProgram := by
  rw [source_text_admitted, Option.some.injEq]
  exact eq_comm

theorem source_text_factorization : sourceText =
    String.ofList leadingChars ++ componentText ++ String.ofList trailingChars := by
  rw [sourceText, source_character_factorization, String.ofList_append, String.ofList_append]
  rfl

end Mettapedia.GSLT.LanguageDef.NativeOpsSourceGuestAdmission
