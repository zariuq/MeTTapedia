import Mathlib.Data.Nat.Factorial.Basic
import Mettapedia.Sequences.OEIS.Basic

namespace Mettapedia.Sequences.OEIS.Elementary49

def snapshotRevision : String :=
  "a6e0f22854cc1c307da428e9d6295093781df7fa"

def sourceOf (oeisId entrySha256 : String) (offset : Int) : EntrySource where
  oeisId := oeisId
  snapshotRevision := snapshotRevision
  entrySha256 := entrySha256
  offset := offset

def specOf (offset : Int) (value : Int → Int) : SequenceSpec where
  offset := offset
  Domain := fun index => offset ≤ index
  value := value

def formalizationOf (source : EntrySource) (spec : SequenceSpec)
    (offsetMatches : spec.offset = source.offset := by rfl) : Formalization where
  source := source
  spec := spec
  offsetMatches := offsetMatches

namespace A002063
def source := sourceOf "A002063" "699537be1bd01e32f23cee5328bd5567866da92ad086c537175ee80ad188b061" 0
def spec := specOf 0 (fun n => 9 * 4 ^ n.toNat)
def formalization := formalizationOf source spec
end A002063

namespace A002276
def source := sourceOf "A002276" "8992b3355354cf0712b823eb09e4b4aee6ffef41c3783b93ac50cae3377f9fcc" 0
def spec := specOf 0 (fun n => 2 * (10 ^ n.toNat - 1) / 9)
def formalization := formalizationOf source spec
end A002276

namespace A002277
def source := sourceOf "A002277" "d4ab0fe64553849af9f60ebe37395e8558149411167baeefc56325381978c4a8" 0
def spec := specOf 0 (fun n => 3 * (10 ^ n.toNat - 1) / 9)
def formalization := formalizationOf source spec
end A002277

namespace A002452
def source := sourceOf "A002452" "d4bbd0134312d8d07c8204f32ee319b3a73686d83e2f48258500b2be0e193d52" 0
def spec := specOf 0 (fun n => (9 ^ n.toNat - 1) / 8)
def formalization := formalizationOf source spec
end A002452

namespace A003464
def source := sourceOf "A003464" "0baefdf3f7468e10ea0af5293af2b0693c6a11939f670a248506b4407d74ee45" 0
def spec := specOf 0 (fun n => (6 ^ n.toNat - 1) / 5)
def formalization := formalizationOf source spec
end A003464

namespace A008455
def source := sourceOf "A008455" "57ceb3d6b41d1e6a6d8b258710cd72c82466293b4a263593a6f86631ad7c8476" 0
def spec := specOf 0 (fun n => n ^ 11)
def formalization := formalizationOf source spec
end A008455

namespace A008790
def source := sourceOf "A008790" "eb1a16f15bff3909a4524744a47efbc0000d19ddb3699af901a5a9b4ad1de1cd" 0
def spec := specOf 0 (fun n => n ^ (n.toNat + 4))
def formalization := formalizationOf source spec
end A008790

namespace A009975
def source := sourceOf "A009975" "ed9f4917cb91049c7e6d405fac9081b22fa12d83ea47b07314e755f2bc9380c6" 0
def spec := specOf 0 (fun n => 31 ^ n.toNat)
def formalization := formalizationOf source spec
end A009975

namespace A009992
def source := sourceOf "A009992" "b60abf13fef47eea8babe33bb2257dbba4a450623b1a25e910d95e563c383eb2" 0
def spec := specOf 0 (fun n => 48 ^ n.toNat)
def formalization := formalizationOf source spec
end A009992

namespace A010807
def source := sourceOf "A010807" "3273f1dd19138223cfaaa9d1b0f18c508e72e946f04110cf02561f9f1b7de7fb" 0
def spec := specOf 0 (fun n => n ^ 19)
def formalization := formalizationOf source spec
end A010807

namespace A011865
def source := sourceOf "A011865" "8fd4a561701b357ad53256dc9821a460722257abcd1c956202326f9aeb5485a0" 0
def spec := specOf 0 (fun n => n * (n - 1) / 12)
def formalization := formalizationOf source spec
end A011865

namespace A013708
def source := sourceOf "A013708" "195c26b0b7dfe4390fa3397cc949e5c3cbd16ddd0a2cdb3562994b1cd5250a6d" 0
def spec := specOf 0 (fun n => 3 ^ (2 * n.toNat + 1))
def formalization := formalizationOf source spec
end A013708

namespace A013710
def source := sourceOf "A013710" "d5323457ad71473d786adcd1d23643cbcbe02b88e7562b2da34de65932b2cf1e" 0
def spec := specOf 0 (fun n => 5 ^ (2 * n.toNat + 1))
def formalization := formalizationOf source spec
end A013710

namespace A014899
def source := sourceOf "A014899" "90ef7480676d138945cedb6a93c2a6954357a37b1659b0583d7ae6726f09777b" 0
def spec := specOf 0 (fun n => (16 ^ (n.toNat + 1) - 15 * n - 16) / 225)
def formalization := formalizationOf source spec
end A014899

namespace A014992
def source := sourceOf "A014992" "ebbf4236f34151ab03a5ba148176a467d4f8a73195b2dcb9c95f5af87835ad90" 1
def spec := specOf 1 (fun n => (1 - (-10 : Int) ^ n.toNat) / 11)
def formalization := formalizationOf source spec
end A014992

namespace A016779
def source := sourceOf "A016779" "56bc1bf16ed408a98b0d997bc8006d1b34e8796dcaf47bfbd91586155f526b97" 0
def spec := specOf 0 (fun n => (3 * n + 1) ^ 3)
def formalization := formalizationOf source spec
end A016779

namespace A016780
def source := sourceOf "A016780" "86c883b0debc37c8ada7ab8f7e0414d0f6f156b2533f6090d993718f45737168" 0
def spec := specOf 0 (fun n => (3 * n + 1) ^ 4)
def formalization := formalizationOf source spec
end A016780

namespace A016814
def source := sourceOf "A016814" "2bb3a661541a70b58c6a0e2fd6b96931502217d3eead53dd16a0d04607b4a3a2" 0
def spec := specOf 0 (fun n => (4 * n + 1) ^ 2)
def formalization := formalizationOf source spec
end A016814

namespace A022521
def source := sourceOf "A022521" "9e35ce7e71d7f5fd49ae14fc9258220a029d69f16f959f9a42ee3e9f4b087501" 0
def spec := specOf 0 (fun n => (n + 1) ^ 5 - n ^ 5)
def formalization := formalizationOf source spec
end A022521

namespace A024064
def source := sourceOf "A024064" "2177a5686b01edfc1b647edf5a392b86c582b6c5c4b4fe77b68a63ec5567f47e" 0
def spec := specOf 0 (fun n => 6 ^ n.toNat - n ^ 2)
def formalization := formalizationOf source spec
end A024064

namespace A028895
def source := sourceOf "A028895" "cad5c4594ee64e634d1afcd0c21baebc3ecedfd578cb6b3d0b283ba058fd0773" 0
def spec := specOf 0 (fun n => 5 * n * (n + 1) / 2)
def formalization := formalizationOf source spec
end A028895

namespace A033436
def source := sourceOf "A033436" "95d6b4d95293af8e175740758f0c398e1987613df7e7d6b76fb244ad80eba292" 0
def spec := specOf 0 (fun n => 3 * n ^ 2 / 8)
def formalization := formalizationOf source spec
end A033436

namespace A036087
def source := sourceOf "A036087" "83b4926a9f6c40e66ec83635ebfaf9a27d1168a437a921730fdf34ec639afb52" 0
def spec := specOf 0 (fun n => (n + 1) ^ 9 + n ^ 9)
def formalization := formalizationOf source spec
end A036087

namespace A047656
def source := sourceOf "A047656" "527a12ecf73f0f587dccec66ca861eb297aa55dd0d6d0a11079ca54ce210b24a" 0
def spec := specOf 0 (fun n => 3 ^ ((n ^ 2 - n) / 2).toNat)
def formalization := formalizationOf source spec
end A047656

namespace A053540
def source := sourceOf "A053540" "63f4ae20a49ac24f04049253e8c05ae8b24d119c410ece0cd73e2a3d8ff08865" 1
def spec := specOf 1 (fun n => n * 9 ^ (n - 1).toNat)
def formalization := formalizationOf source spec
end A053540

namespace A057358
def source := sourceOf "A057358" "23bfd1400a5824adbd63ab16b236adce2ec644dfb18f5da99505b68b0fdd3e1e" 0
def spec := specOf 0 (fun n => 4 * n / 7)
def formalization := formalizationOf source spec
end A057358

namespace A064751
def source := sourceOf "A064751" "fee1a1fe1a8071a96205e840befe112c2ce38abc02ed5fe375a09640c75cd4b0" 1
def spec := specOf 1 (fun n => n * 5 ^ n.toNat - 1)
def formalization := formalizationOf source spec
end A064751

namespace A070439
def source := sourceOf "A070439" "df5acb01e6c2570f6b4592782d285292d0cb69a4cd1987052c2f5ac6b0cc6de4" 0
def spec := specOf 0 (fun n => n ^ 2 % 16)
def formalization := formalizationOf source spec
end A070439

namespace A070478
def source := sourceOf "A070478" "cd9f8752f701420ceb43a72e77db95d1d3816fddc6db55c8b531aabbab41947b" 0
def spec := specOf 0 (fun n => n ^ 3 % 16)
def formalization := formalizationOf source spec
end A070478

namespace A070512
def source := sourceOf "A070512" "e2227f208a936e5f1879f2219bfd1ff0e8d34ef9de4f77a87165733b4c0238b0" 0
def spec := specOf 0 (fun n => n ^ 4 % 7)
def formalization := formalizationOf source spec
end A070512

namespace A085473
def source := sourceOf "A085473" "2ffd1430ffd95f85ae575a08cdc4e438ccfd445180c68eea7969da4c25b6131d" 0
def spec := specOf 0 (fun n => 6 * n ^ 2 + 3 * n + 1)
def formalization := formalizationOf source spec
end A085473

namespace A089081
def source := sourceOf "A089081" "79c80377a91d420b1062aadfcc90769241c5c4d9356a485b91e8708ea8d6b1ec" 0
def spec := specOf 0 (fun n => n ^ 26)
def formalization := formalizationOf source spec
end A089081

namespace A099762
def source := sourceOf "A099762" "08737ea56e1e29ecbdad07bedb94cb06719d546bc6411815acfc3f2740fb6dc8" 0
def spec := specOf 0 (fun n => n ^ 2 * (n + 1) ^ 3)
def formalization := formalizationOf source spec
end A099762

namespace A102083
def source := sourceOf "A102083" "427330f12f0ede7a653d50582bacc7ef6161615bc5cd5630cafb279b0a22873c" 0
def spec := specOf 0 (fun n => 8 * n ^ 2 + 4 * n + 1)
def formalization := formalizationOf source spec
end A102083

namespace A116156
def source := sourceOf "A116156" "b8fd023fa3710ffdff6a561045b7bf4c97c33d849c7d5cd91e6b2caa738deccf" 0
def spec := specOf 0 (fun n => 5 ^ n.toNat * n * (n + 1))
def formalization := formalizationOf source spec
end A116156

namespace A132754
def source := sourceOf "A132754" "6b861e8c8ffb870dfa7d1fc4363d9ca09882337f10ce45a4bbd172eafe78bfd6" 0
def spec := specOf 0 (fun n => n * (n + 23) / 2)
def formalization := formalizationOf source spec
end A132754

namespace A140689
def source := sourceOf "A140689" "ce5ee836499ebc58727b8cdc6e162ec4f8331efc88a544210bb7c41613a732c1" 0
def spec := specOf 0 (fun n => n * (3 * n + 20))
def formalization := formalizationOf source spec
end A140689

namespace A147875
def source := sourceOf "A147875" "7f734259ab21b3aea0b904e808ffe6a94f68c9f65cf158cceebdb6d07dcce09b" 0
def spec := specOf 0 (fun n => n * (5 * n + 3) / 2)
def formalization := formalizationOf source spec
end A147875

namespace A155957
def source := sourceOf "A155957" "11cfe40a8db8c96bf3f28b8bdfa293a325e252d958aa5c2a8e28ad79b60d8239" 0
def spec := specOf 0 (fun n => (2 * n ^ 2) ^ n.toNat)
def formalization := formalizationOf source spec
end A155957

namespace A168416
def source := sourceOf "A168416" "b51489aa9626d423a93f85fce548e2d5d02dafdf2fc6c20a5b6cb09cf1f2ea24" 1
def spec := specOf 1 (fun n => 1 + 9 * (n / 2))
def formalization := formalizationOf source spec
end A168416

namespace A190578
def source := sourceOf "A190578" "b224a94e8f2e975fe5559948765c79b65d5e345221fba378c57f440b7afd7a40" 0
def spec := specOf 0 (fun n => n ^ 7 + n)
def formalization := formalizationOf source spec
end A190578

namespace A194268
def source := sourceOf "A194268" "c07da9d67ae17d7a6b0ced0248576c41e07b3fb90b76ff1d938db82d4c9e95da" 0
def spec := specOf 0 (fun n => 8 * n ^ 2 + 7 * n + 1)
def formalization := formalizationOf source spec
end A194268

namespace A196258
def source := sourceOf "A196258" "d165c91ecbedef9ee466f51931426414b15686448e0feaf5fb8a2bebb36d76ae" 0
def spec := specOf 0 (fun n => 11 ^ n.toNat * Int.ofNat n.toNat.factorial)
def formalization := formalizationOf source spec
end A196258

namespace A209294
def source := sourceOf "A209294" "59a61dad68e3781f1c855ae7a717b4b41e11c8f266e84c28420f732a98ceecc5" 1
def spec := specOf 1 (fun n => (7 * n ^ 2 - 7 * n + 4) / 2)
def formalization := formalizationOf source spec
end A209294

namespace A212697
def source := sourceOf "A212697" "016e31b9048a598182d6dae53c6f92322b9ecc9ceb286f86fa132dfc7d3993a4" 1
def spec := specOf 1 (fun n => 2 * n * 3 ^ (n - 1).toNat)
def formalization := formalizationOf source spec
end A212697

namespace A236267
def source := sourceOf "A236267" "4185051c7958ca43e882f2a7808208b4b1bfbc82fe568fb7e54ff0c322184a89" 0
def spec := specOf 0 (fun n => 8 * n ^ 2 + 3 * n + 1)
def formalization := formalizationOf source spec
end A236267

namespace A244630
def source := sourceOf "A244630" "48ff1d4636f1eb6a0e239dff5b6d16b7ae742fab69a5bf18faeaa49011925d5a" 0
def spec := specOf 0 (fun n => 17 * n ^ 2)
def formalization := formalizationOf source spec
end A244630

namespace A249013
def source := sourceOf "A249013" "6ab8c821211d7e552f508f2ba7642876ce10e9a6a7ac9a2b3d5446ba76ac3a9a" 1
def spec := specOf 1 (fun n => (n - 1) * (n + 4) / 10)
def formalization := formalizationOf source spec
end A249013

namespace A343028
def source := sourceOf "A343028" "58518bbdc70cb5182372f3c7a8067dcf8892bc07185f30056840f33df1ca1ac9" 0
def spec := specOf 0 (fun n => 11 * n / 3)
def formalization := formalizationOf source spec
end A343028

/-- The frozen metadata-only elementary seed, in selection order. -/
def registry : List Formalization :=
  [ A002063.formalization, A002276.formalization, A002277.formalization,
    A002452.formalization, A003464.formalization, A008455.formalization,
    A008790.formalization, A009975.formalization, A009992.formalization,
    A010807.formalization, A011865.formalization, A013708.formalization,
    A013710.formalization, A014899.formalization, A014992.formalization,
    A016779.formalization, A016780.formalization, A016814.formalization,
    A022521.formalization, A024064.formalization, A028895.formalization,
    A033436.formalization, A036087.formalization, A047656.formalization,
    A053540.formalization, A057358.formalization, A064751.formalization,
    A070439.formalization, A070478.formalization, A070512.formalization,
    A085473.formalization, A089081.formalization, A099762.formalization,
    A102083.formalization, A116156.formalization, A132754.formalization,
    A140689.formalization, A147875.formalization, A155957.formalization,
    A168416.formalization, A190578.formalization, A194268.formalization,
    A196258.formalization, A209294.formalization, A212697.formalization,
    A236267.formalization, A244630.formalization, A249013.formalization,
    A343028.formalization ]

theorem registry_length : registry.length = 49 := by decide

#print axioms registry_length

end Mettapedia.Sequences.OEIS.Elementary49
