fof(c_Subq,axiom,(! [X0:$i] : (! [X1:$i] : (c_Subq(c_X0,c_X1) <=> (! [X2] : (c_In(X2,c_X0) => c_In(X2,c_X1))))))). % 8a8e36b858cd07fc5e5f164d8075dc68a88221ed1e4c9f28dac4a6fdb2172e87
fof(set_5Fext,axiom,(! [X0] : (! [X1] : (c_Subq(X0,X1) => (c_Subq(X1,X0) => (X0 = X1)))))). % 5189b0389a1efe35ba744aa1436bb23541e75e8a85658313375e1e0b3321128f
fof(c_EmptyAx,axiom,~ (? [X0] : c_In(X0,c_Empty))). % 920f955f033a1286fcaba96c8eb55d2079812a3041ff6b812df4cc2636156b59
fof(c_UnionEq,axiom,(! [X0] : (! [X1] : (c_In(X1,c_Union(X0)) <=> (? [X2] : (c_In(X1,X2) & c_In(X2,X0))))))). % 0b67fbe4188c03468f8cd69c462ea8e5fb2269bf1fd67125a6456853d4ab7c74
fof(c_PowerEq,axiom,(! [X0] : (! [X1] : (c_In(X1,c_Power(X0)) <=> c_Subq(X1,X0))))). % b492ab96942311595fd53c93243cb7ab5314986bb8460d580d9382dfab90f7d1
fof(c_TransSet,axiom,(! [X0:$i] : (c_TransSet(c_X0) <=> (! [X1] : (c_In(X1,c_X0) => c_Subq(X1,c_X0)))))). % e7493d5f5a73b6cb40310f6fcb87d02b2965921a25ab96d312adf7eb8157e4b3
fof(c_Union_5Fclosed,axiom,(! [X0:$i] : (c_Union_5Fclosed(c_X0) <=> (! [X1] : (c_In(X1,c_X0) => c_In(c_Union(X1),c_X0)))))). % 54850182033d0575e98bc2b12aa8b9baaa7a541e9d5abc7fddeb74fc5d0a19ac
fof(c_Power_5Fclosed,axiom,(! [X0:$i] : (c_Power_5Fclosed(c_X0) <=> (! [X1] : (c_In(X1,c_X0) => c_In(c_Power(X1),c_X0)))))). % 5a811b601343da9ff9d05d188d672be567de94b980bbbe0e04e628d817f4c7ac
fof(c_ZF_5Fclosed,axiom,(! [X0:$i] : (c_ZF_5Fclosed(c_X0) <=> ((c_Union_5Fclosed(c_X0) & c_Power_5Fclosed(c_X0)) & c_Repl_5Fclosed(c_X0))))). % 43f34d6a2314b56cb12bf5cf84f271f3f02a3e68417b09404cc73152523dbfa0
fof(c_UnivOf_5FIn,axiom,(! [X0] : c_In(X0,c_UnivOf(X0)))). % 64ad93d240a001e91d619642c36f7ea8387780b9860b748f282d12bc22d4a677
fof(c_UnivOf_5FTransSet,axiom,(! [X0] : c_TransSet(c_UnivOf(X0)))). % 40723e6db0df4f3bce8b35ba709f46fd1f4a94f61bdd2e206b8d4e21ea660332
fof(c_UnivOf_5FZF_5Fclosed,axiom,(! [X0] : c_ZF_5Fclosed(c_UnivOf(X0)))). % 4181a4a1a92ac574d2c6208a18ed79b8773a8c1de9330f96e76e3edabcf083ea
fof(c_UnivOf_5FMin,axiom,(! [X0] : (! [X1] : (c_In(X0,X1) => (c_TransSet(X1) => (c_ZF_5Fclosed(X1) => c_Subq(c_UnivOf(X0),X1))))))). % 9a6fd4292d63e7be0caf7c85f8d8c56e3be3c23ff46c2001263cd459da21e6ed
fof(nIn,axiom,(! [X0:$i] : (! [X1:$i] : (nIn(c_X0,c_X1) <=> ~ c_In(c_X0,c_X1))))). % 2f8b7f287504f141b0f821928ac62823a377717763a224067702eee02fc1f359
fof(c_EmptyE,axiom,(! [X0] : nIn(X0,c_Empty))). % db69db5fe0ab30c62cbb6c6a5585580d13a89b7a739501bf6ab7f69ba07ed65e
fof(c_PowerI,axiom,(! [X0] : (! [X1] : (c_Subq(X1,X0) => c_In(X1,c_Power(X0)))))). % 8ec4fb130787ca0a60ebd05ea54a7a9f309a462585bcc1ee86952371bbf7d709
fof(c_Subq_5FEmpty,axiom,(! [X0] : c_Subq(c_Empty,X0))). % ec40ffd5e1efa2305904493e93693c9ded9ce1a6c83c767acc34b0a727c8c8ff
fof(c_Empty_5FIn_5FPower,axiom,(! [X0] : c_In(c_Empty,c_Power(X0)))). % 57bdeb692b87bc968dc5c4c76518265b349fad59aa9d410f1763da99db3af2d7
fof(eq_5Fi_5Ftra,axiom,(! [X0] : (! [X1] : (! [X2] : ((X0 = X1) => ((X1 = X2) => (X0 = X2))))))). % ebaf3a176014e42e2f894150fb11347d641abecb9be82d29a784bb9b0312d2e8
fof(neq_5Fi_5Fsym,axiom,(! [X0] : (! [X1] : (~ (X0 = X1) => ~ (X1 = X0))))). % 5975ea0d667ef81890db1136e825d1bda7a0dec6bacfabb8f8c03bae6c9d6bde
fof(c_Subq_5Fref,axiom,(! [X0] : c_Subq(X0,X0))). % 8cc027a87882f9d68d5bb3a254ca44809bb1f7acc0d6ad2ed1d5aa7f040b3422
fof(c_Subq_5Ftra,axiom,(! [X0] : (! [X1] : (! [X2] : (c_Subq(X0,X1) => (c_Subq(X1,X2) => c_Subq(X0,X2))))))). % 065e1c25434d58f32a87cf53ecf8bea2d3e1eb2dc3e022e6bd6f5e03e5f845a5
fof(c_Empty_5FSubq_5Feq,axiom,(! [X0] : (c_Subq(X0,c_Empty) => (X0 = c_Empty)))). % 3eadb639389a682a69e54b191ac296a25a1a39baabdefa25ba9bccbeb7038d35
fof(c_Empty_5Feq,axiom,(! [X0] : ((! [X1] : nIn(X1,X0)) => (X0 = c_Empty)))). % 4b1c3808883170ae2c35267bed4184182595364acf85a55cf81ba0b3c95c9de5
fof(c_UnionI,axiom,(! [X0] : (! [X1] : (! [X2] : (c_In(X1,X2) => (c_In(X2,X0) => c_In(X1,c_Union(X0)))))))). % 681f08928f47fe62e4803e6fa2b70b4ea7a5d093a6d00273519a068fea82736f
fof(c_UnionE,axiom,(! [X0] : (! [X1] : (c_In(X1,c_Union(X0)) => (? [X2] : (c_In(X1,X2) & c_In(X2,X0))))))). % 704291d62c629bb6d6fba75f33b0b13133e87259f1defdfafd1142825f56775c
fof(c_PowerE,axiom,(! [X0] : (! [X1] : (c_In(X1,c_Power(X0)) => c_Subq(X1,X0))))). % e6c5658300fbb425904a43da92acd1b8285eb12502cbe3e889df5f01952d03f8
fof(c_Self_5FIn_5FPower,axiom,(! [X0] : c_In(X0,c_Power(X0)))). % 9e7d17e9e24e10742a1db89c76f516cfd1d826d9141665d2cdfcc8973b143d8d
fof(c_UPairE,axiom,(! [X0] : (! [X1] : (! [X2] : (c_In(X0,c_UPair(X1,X2)) => ((X0 = X1) | (X0 = X2))))))). % 27295eee731b2e2ca8dcbae7e034df4ffc68d79fa2eb3e5177a683f5e766fc73
fof(c_UPairI1,axiom,(! [X0] : (! [X1] : c_In(X0,c_UPair(X0,X1))))). % d4cb6fc9a2dc09ce7fcb98d747c419612bff8c7c54b31e61eadaac97237200dc
fof(c_UPairI2,axiom,(! [X0] : (! [X1] : c_In(X1,c_UPair(X0,X1))))). % 17192a1a43d5167598e15fcb1851bd723fde74be514850fe1f482a3de4a622a3
fof(c_Sing,axiom,(! [X0:$i] : (c_Sing(c_X0) = c_UPair(c_X0,c_X0)))). % 158bae29452f8cbf276df6f8db2be0a5d20290e15eca88ffe1e7b41d211d41d7
fof(c_SingI,axiom,(! [X0] : c_In(X0,c_Sing(X0)))). % 77b0506ab5458ffa86830e02cd5fb26c1a1bd554e0216a7393a1bc0caac25b87
fof(c_SingE,axiom,(! [X0] : (! [X1] : (c_In(X1,c_Sing(X0)) => (X1 = X0))))). % 032df44ded59d711a15139bdf4096b5420fd1483acfe697faa4c76557c931e91
fof(binunion,axiom,(! [X0:$i] : (! [X1:$i] : (binunion(c_X0,c_X1) = c_Union(c_UPair(c_X0,c_X1)))))). % 0a445311c45f0eb3ba2217c35ecb47f122b2301b2b80124922fbf03a5c4d223e
fof(binunionI1,axiom,(! [X0] : (! [X1] : (! [X2] : (c_In(X2,X0) => c_In(X2,binunion(X0,X1))))))). % 9e9f1f4dffcf252f2a92d22b0643d42fab016ee86072c0d9d927a0865dcb1c66
fof(binunionI2,axiom,(! [X0] : (! [X1] : (! [X2] : (c_In(X2,X1) => c_In(X2,binunion(X0,X1))))))). % c5d368c671e9b46c609a1d230dfb54bcf83cb15c2467e38febbebbaae3b135e5
fof(binunionE,axiom,(! [X0] : (! [X1] : (! [X2] : (c_In(X2,binunion(X0,X1)) => (c_In(X2,X0) | c_In(X2,X1))))))). % f270d6aed9b2d86fc0b81ffd22ec16d7b33f0b58017f24581b824b49fb600f05
fof(binunion_5Fasso,axiom,(! [X0] : (! [X1] : (! [X2] : (binunion(X0,binunion(X1,X2)) = binunion(binunion(X0,X1),X2)))))). % 67721cc3000e8d5807e36d600cacd6c66b8482e28b0bfbcdf3a5f78c7eb0f18e
fof(binunion_5Fcom_5FSubq,axiom,(! [X0] : (! [X1] : c_Subq(binunion(X0,X1),binunion(X1,X0))))). % a282be30deb1c298c1256b7a3e4687c02915664d968f0a9c14405d1a1f469395
fof(binunion_5Fcom,axiom,(! [X0] : (! [X1] : (binunion(X0,X1) = binunion(X1,X0))))). % 006fa5505501fe20cccbbc89f12002205a374c3e66a087a028160c507518e332
fof(binunion_5Fidl,axiom,(! [X0] : (binunion(c_Empty,X0) = X0))). % 0d9845e947d190c3e834c5c20eafe01a72e43069e4fab7c05fa73da195474514
fof(binunion_5Fidr,axiom,(! [X0] : (binunion(X0,c_Empty) = X0))). % 9e1ff5e3ef71b4e993dc9b4f0b8a6a1bfbc89716b71b564cfe9d7b2d4e782dc9
fof(binunion_5FSubq_5F1,axiom,(! [X0] : (! [X1] : c_Subq(X0,binunion(X0,X1))))). % 91a0993badea53aedb20396d62ea57d213095e6eef8e9372a21e105c45c931b7
fof(binunion_5FSubq_5F2,axiom,(! [X0] : (! [X1] : c_Subq(X1,binunion(X0,X1))))). % 08072961243ad5b744fa95095981b56ea524a7b80b12f8b044fd9adc9bd624ff
fof(binunion_5FSubq_5Fmin,axiom,(! [X0] : (! [X1] : (! [X2] : (c_Subq(X0,X2) => (c_Subq(X1,X2) => c_Subq(binunion(X0,X1),X2))))))). % 3cf55cc72fc63a566988ee47c2c423883980d19b8bca9f80dd660ff2565ae091
fof(c_SetAdjoin,axiom,(! [X0:$i] : (! [X1:$i] : (c_SetAdjoin(c_X0,c_X1) = binunion(c_X0,c_Sing(c_X1)))))). % 153bff87325a9c7569e721334015eeaf79acf75a785b960eb1b46ee9a5f023f8
fof(binintersectI,axiom,(! [X0] : (! [X1] : (! [X2] : (c_In(X2,X0) => (c_In(X2,X1) => c_In(X2,binintersect(X0,X1)))))))). % 60326596dd1073df96277e47a8ce32cc389745008f601b6a7af467ea84120040
fof(binintersectE,axiom,(! [X0] : (! [X1] : (! [X2] : (c_In(X2,binintersect(X0,X1)) => (c_In(X2,X0) & c_In(X2,X1))))))). % 776f7336d9260a7b2828f159460596cc0a08aad88f391f6eb9376b54a43169d0
fof(binintersectE1,axiom,(! [X0] : (! [X1] : (! [X2] : (c_In(X2,binintersect(X0,X1)) => c_In(X2,X0)))))). % 96356c122c520f01fe41aa000a6de495dc464356a7c61fe73edc453b21e3f3d0
fof(binintersectE2,axiom,(! [X0] : (! [X1] : (! [X2] : (c_In(X2,binintersect(X0,X1)) => c_In(X2,X1)))))). % 6f07a0620ab1e814630e155438f468c3ce47cf098a5d32757b8140821b528717
fof(binintersect_5FSubq_5F1,axiom,(! [X0] : (! [X1] : c_Subq(binintersect(X0,X1),X0)))). % ab22d20197cad203d5c9fe3d418292777f2d18e81c63de21cadf3e3a7810788b
fof(binintersect_5FSubq_5F2,axiom,(! [X0] : (! [X1] : c_Subq(binintersect(X0,X1),X1)))). % 1631379e768fcf9991063853f9d83e6639fd0a8eca9c6c6aecc03cd8b25a5d46
fof(binintersect_5FSubq_5Feq_5F1,axiom,(! [X0] : (! [X1] : (c_Subq(X0,X1) => (binintersect(X0,X1) = X0))))). % 9b8243c8d51df36232595bb6a54ef1efd7733b7e96b02b9faf1bf6ddb9cf204a
fof(binintersect_5FSubq_5Fmax,axiom,(! [X0] : (! [X1] : (! [X2] : (c_Subq(X2,X0) => (c_Subq(X2,X1) => c_Subq(X2,binintersect(X0,X1)))))))). % dc091d6184740a0ec73da1102fea8faf4bb3ffb9a908411cac31c0353a026173
fof(binintersect_5Fcom_5FSubq,axiom,(! [X0] : (! [X1] : c_Subq(binintersect(X0,X1),binintersect(X1,X0))))). % b04f1c0d7b7ab06346edf7b046833c6bd75692afd8136d6451229650cbfc8ab8
fof(binintersect_5Fcom,axiom,(! [X0] : (! [X1] : (binintersect(X0,X1) = binintersect(X1,X0))))). % 89b32b84af8e516fb5cde0f0ca143563535a8971e687e30a69e4ae28c8db1afb
fof(setminusI,axiom,(! [X0] : (! [X1] : (! [X2] : (c_In(X2,X0) => (nIn(X2,X1) => c_In(X2,setminus(X0,X1)))))))). % 8288e93b6088e201e20ca0b2b0b72fe9d40cba3051ebbe3f888bb9ae974f4ce7
fof(setminusE,axiom,(! [X0] : (! [X1] : (! [X2] : (c_In(X2,setminus(X0,X1)) => (c_In(X2,X0) & nIn(X2,X1))))))). % 400e4bb15cd50b24f37f239fc7c0d228c3410893b31102399aa59d2ea875fb60
fof(setminusE1,axiom,(! [X0] : (! [X1] : (! [X2] : (c_In(X2,setminus(X0,X1)) => c_In(X2,X0)))))). % 8e1526a7d7bcb5f7eb8fc3a14a2d7fc79d0bc15338f8e4e8b21da538cba4cf64
fof(setminusE2,axiom,(! [X0] : (! [X1] : (! [X2] : (c_In(X2,setminus(X0,X1)) => nIn(X2,X1)))))). % c8507f03e73a7f171961c01a49c0bec6f4a5ef95d09e5a1bc5a6aabcfbcae855
fof(setminus_5FSubq,axiom,(! [X0] : (! [X1] : c_Subq(setminus(X0,X1),X0)))). % 691304ddc6e76e363620558b1c9367048bde82b40c830ee183051e96f35ee022
fof(setminus_5FIn_5FPower,axiom,(! [X0] : (! [X1] : c_In(setminus(X0,X1),c_Power(X0))))). % 83b53c6e2122cffca9796caa4c5b1431d936e3b5694255b74ebc24a115abc75a
fof(binunion_5Fremove1_5Feq,axiom,(! [X0] : (! [X1] : (c_In(X1,X0) => (X0 = binunion(setminus(X0,c_Sing(X1)),c_Sing(X1))))))). % 296b1a8abc25c8b9087e3238156fab3ca312e7c26b6549b3378a98e1f1eaad1b
fof(c_In_5Firref,axiom,(! [X0] : nIn(X0,X0))). % 32d1b89792462a93a3f0b39fd0af65084fc19951789fbfedaf1434075442a3f9
fof(c_In_5Fno2cycle,axiom,(! [X0] : (! [X1] : (c_In(X0,X1) => (c_In(X1,X0) => $false))))). % 092f94151e13afcf352cc284da6b0c8dc39ee950c68abf2b8a08684a9649dca6
fof(ordsucc,axiom,(! [X0:$i] : (ordsucc(c_X0) = binunion(c_X0,c_Sing(c_X0))))). % 9db634daee7fc36315ddda5f5f694934869921e9c5f55e8b25c91c0a07c5cbec
fof(ordsuccI1,axiom,(! [X0] : c_Subq(X0,ordsucc(X0)))). % 1d5d5b7b71ce4bb9a73edbf50070235dcc5bed8bf5dd7baab447bbd91db9807a
fof(ordsuccI2,axiom,(! [X0] : c_In(X0,ordsucc(X0)))). % 0bce99a2a196c1d6c6e5f195bcbe470674eab0f020f5c6768ba374f8363f164a
fof(ordsuccE,axiom,(! [X0] : (! [X1] : (c_In(X1,ordsucc(X0)) => (c_In(X1,X0) | (X1 = X0)))))). % 86defe2eaec7e0a7514339bd4f70688a0055e97b2bccbb0ea3ae8c06f32ce88a
fof(neq_5F0_5Fordsucc,axiom,(! [X0] : ~ (c_Empty = ordsucc(X0)))). % cd16045e375d4af84d5e4935492f9372af2c1df516250653f67f2eabce3e1a96
fof(neq_5Fordsucc_5F0,axiom,(! [X0] : ~ (ordsucc(X0) = c_Empty))). % 10d9661442ca65e01bc41935f4cb9aa6a33342df51d9e7dd2fd94e6c575e9dda
fof(ordsucc_5Finj,axiom,(! [X0] : (! [X1] : ((ordsucc(X0) = ordsucc(X1)) => (X0 = X1))))). % c0e03f00abde433cdda0dcc6cbe3d8c75fab364b4e5ec7433aeb6e1955558a49
fof(c_In_5F0_5F1,axiom,c_In(c_Empty,ordsucc(c_Empty))). % 4675abc9d31454cce6f27f63bfaacf6fc539a2b864cdd7bb9bf34598e85c9ff3
fof(c_In_5F0_5F2,axiom,c_In(c_Empty,ordsucc(ordsucc(c_Empty)))). % 4dcf737d976ab59871f178ab4227edffb26181c236613caeb68c84de8f2e6aa1
fof(c_In_5F1_5F2,axiom,c_In(ordsucc(c_Empty),ordsucc(ordsucc(c_Empty)))). % b28b8818076ea2727fe37ccdc19db7910186e7991e3cd809d9bd88239f294936
fof(nat_5F0,axiom,nat_5Fp(c_Empty)). % 8184e026ae720ae8ac54902d7e3149de08f2ad09a231d1695d0c97a705e1f859
fof(nat_5Fordsucc,axiom,(! [X0] : (nat_5Fp(X0) => nat_5Fp(ordsucc(X0))))). % c3f39850f8a787c21c048322f3dda0ed87723efae7899cefd3c49775f471b99b
fof(nat_5F1,axiom,nat_5Fp(ordsucc(c_Empty))). % a985fbd82807c603866f35d87f9d2827902df20043761c604b521c2cfc62c64e
fof(nat_5F2,axiom,nat_5Fp(ordsucc(ordsucc(c_Empty)))). % 28f0901270c9b9323f9278a82b158ea70a40f1d4ddfee5861486d22dc1bd7606
fof(nat_5F0_5Fin_5Fordsucc,axiom,(! [X0] : (nat_5Fp(X0) => c_In(c_Empty,ordsucc(X0))))). % cb67919398db6f11c2a4b410dd7fa5874724b7d2e2e1405849af78dca03a95bc
fof(nat_5Fordsucc_5Fin_5Fordsucc,axiom,(! [X0] : (nat_5Fp(X0) => (! [X1] : (c_In(X1,X0) => c_In(ordsucc(X1),ordsucc(X0))))))). % f2c2ec5ac5f1007b6100f9d8d698faba5c4a7de8b14e107578eca0163c7799c4
fof(nat_5Finv,axiom,(! [X0] : (nat_5Fp(X0) => ((X0 = c_Empty) | (? [X1] : (nat_5Fp(X1) & (X0 = ordsucc(X1)))))))). % 60e4d8db528b021fa7054c4e234c2b8f3ed4167b57341e3126724755a2dfd20c
fof(nat_5Fp_5Ftrans,axiom,(! [X0] : (nat_5Fp(X0) => (! [X1] : (c_In(X1,X0) => nat_5Fp(X1)))))). % 02c1be4fb7e8692a5ff13768a268b8f86936de1e79562d2d1c2a93838bee6cd2
fof(nat_5Ftrans,axiom,(! [X0] : (nat_5Fp(X0) => (! [X1] : (c_In(X1,X0) => c_Subq(X1,X0)))))). % ad6e9c68eaa15a57bb52641b049653bf19e99a0d8e5402cb7b6214d594de8561
fof(nat_5Fordsucc_5Ftrans,axiom,(! [X0] : (nat_5Fp(X0) => (! [X1] : (c_In(X1,ordsucc(X0)) => c_Subq(X1,X0)))))). % 28c5ca659f843c7e84c84347ea693e3888da4e8d9dceab0c3fff0d616d9c06cc
fof(atleastp_5Ftra,axiom,(! [X0] : (! [X1] : (! [X2] : (atleastp(X0,X1) => (atleastp(X1,X2) => atleastp(X0,X2))))))). % a459514f533af0aa0f5c35dd114f33e34ae4d322e63c0410f91bf58d79ff13fe
fof(c_Subq_5Fatleastp,axiom,(! [X0] : (! [X1] : (c_Subq(X0,X1) => atleastp(X0,X1))))). % 877fe5b0cb6b8287108ca9aed1cdfdbc86e682215073795072a2da6e0d9db6b1
fof(equip_5Fatleastp,axiom,(! [X0] : (! [X1] : (equip(X0,X1) => atleastp(X0,X1))))). % 2ee17981b64518f1ca9743636c2c6c25551021a5c12b392c0f0351e7cfd3b6cd
fof(equip_5Fref,axiom,(! [X0] : equip(X0,X0))). % 71d8f2d93ec37cf4fa76487b6d2eb9d0410051bc927d2f35b2f987a884b7d002
fof(equip_5Fsym,axiom,(! [X0] : (! [X1] : (equip(X0,X1) => equip(X1,X0))))). % c07b874e6900f27e8a8737c2b8783387617c954dec4a46b9b3cc1cbaea9c6b37
fof(equip_5Ftra,axiom,(! [X0] : (! [X1] : (! [X2] : (equip(X0,X1) => (equip(X1,X2) => equip(X0,X2))))))). % cb492df6d2d7489aa739f1c9ce70981c4c20fc2c8838171108a88b39af10e525
fof(equip_5F0_5FEmpty,axiom,(! [X0] : (equip(X0,c_Empty) => (X0 = c_Empty)))). % 2f0f69d51bec45a7b8f8d9a4907763107b173ff71c45a381664c7488ca7096bf
fof(equip_5Fadjoin_5Fordsucc,axiom,(! [X0] : (! [X1] : (! [X2] : (nIn(X2,X1) => (equip(X0,X1) => equip(ordsucc(X0),binunion(X1,c_Sing(X2))))))))). % 37a2e00564e7b2e38ac1de48eff4f00da7a08c692da0ce036bf8f04de888c32e
fof(equip_5Fordsucc_5Fremove1,axiom,(! [X0] : (! [X1] : (! [X2] : (c_In(X2,X0) => (equip(X0,ordsucc(X1)) => equip(setminus(X0,c_Sing(X2)),X1))))))). % 019bf79338f95afa8d2c797734f29d7b4f36277e078b647e09c3fee4fb79f778
fof(setminus_5Fantimonotone,axiom,(! [X0] : (! [X1] : (! [X2] : (c_Subq(X1,X2) => c_Subq(setminus(X0,X2),setminus(X0,X1))))))). % f834915e222d99d9adaad0c8e862bc1384c10d3f4b9ce045b11fb075f120d5f3
fof(atleastp_5Fantisym_5Fequip,axiom,(! [X0] : (! [X1] : (atleastp(X0,X1) => (atleastp(X1,X0) => equip(X0,X1)))))). % 07130b13e2a320ff06b472a2707f24947179f2ecfa5a15e59205b817291fd2f8
fof(c_Pigeonhole_5Fnot_5Fatleastp_5Fordsucc,axiom,(! [X0] : (nat_5Fp(X0) => ~ atleastp(ordsucc(X0),X0)))). % c29d57653c9c5b2e351c04de5e8ef10584e9651a9247d5654d2f5c956ad51a77
fof(c_Union_5Fordsucc_5Feq,axiom,(! [X0] : (nat_5Fp(X0) => (c_Union(ordsucc(X0)) = X0)))). % 73f4179688eb6f1e9c80d6a1b13947b195e20a128e2e7dcbd7a7ca3d84a91857
fof(neq_5F0_5F1,axiom,~ (c_Empty = ordsucc(c_Empty))). % 2a012236fc59f277a006afea6589576917b98079dfa3b365b27050d0e9d91f80
fof(neq_5F1_5F0,axiom,~ (ordsucc(c_Empty) = c_Empty)). % a96636a83cef72bedda13177ba1f197ac6b6dab4613cc8062584e25c143b84fa
fof(neq_5F0_5F2,axiom,~ (c_Empty = ordsucc(ordsucc(c_Empty)))). % d7185afea09cc857260bbddd424bfd78941c0b9280cbff99a37a204ade989ef0
fof(neq_5F2_5F0,axiom,~ (ordsucc(ordsucc(c_Empty)) = c_Empty)). % 76555b2fee92c2ef5efd3b1992a67dc11fd63bdea9e5147e490c7e1ae4ee037b
fof(ordinal,axiom,(! [X0:$i] : (ordinal(c_X0) <=> (c_TransSet(c_X0) & (! [X1] : (c_In(X1,c_X0) => c_TransSet(X1))))))). % dab6e51db9653e58783a3fde73d4f2dc2637891208c92c998709e8795ba4326f
fof(ordinal_5FTransSet,axiom,(! [X0] : (ordinal(X0) => c_TransSet(X0)))). % 8ef2ed23b3b181d1f2866781c9670cf9202d68293220ee4017dc30c5aa44991e
fof(ordinal_5FEmpty,axiom,ordinal(c_Empty)). % 1408f7bc0af4e611ec201b7f4d5d48ea1e8af2a84e7bdd2923141bd0f00f4e36
fof(ordinal_5FHered,axiom,(! [X0] : (ordinal(X0) => (! [X1] : (c_In(X1,X0) => ordinal(X1)))))). % 88a5e775f9178814d4ac516ab2e90f62b1393b491f11d4cbda17569605b6b82e
fof(c_TransSet_5Fordsucc,axiom,(! [X0] : (c_TransSet(X0) => c_TransSet(ordsucc(X0))))). % e362a16ce7aaa089e050c0ef8bf8bd25dee8e26cadb02548ecd1f64c467e8d0b
fof(ordinal_5Fordsucc,axiom,(! [X0] : (ordinal(X0) => ordinal(ordsucc(X0))))). % 1bb64afeb45eb7e44f74789457d255605af7c85c76037aa9c9dba6265adc92b2
fof(nat_5Fp_5Fordinal,axiom,(! [X0] : (nat_5Fp(X0) => ordinal(X0)))). % b1aeca813733e9bbe781f7d8fc79da579625ae776d0e98b141d5690c4b87e1b7
fof(ordinal_5F1,axiom,ordinal(ordsucc(c_Empty))). % 8bc99d25e11f658b1faeb2fa614f072422a08e2ffaa923924de7d01c2670e457
fof(ordinal_5F2,axiom,ordinal(ordsucc(ordsucc(c_Empty)))). % 81861e7027b170e26e8b9a3f71517df823903aa67a501f9c1a7ed9f7b0acda73
fof(c_TransSet_5Fordsucc_5FIn_5FSubq,axiom,(! [X0] : (c_TransSet(X0) => (! [X1] : (c_In(X1,X0) => c_Subq(ordsucc(X1),X0)))))). % 77f8eee076133d5b75a09afa7d0e04bce51157c96b55da20f79f3dc4d7a65a0b
fof(ordinal_5Fordsucc_5FIn_5FSubq,axiom,(! [X0] : (ordinal(X0) => (! [X1] : (c_In(X1,X0) => c_Subq(ordsucc(X1),X0)))))). % 6d5288e7c58d020453e7c521d00208b382c456f71bb78d30eb1709f2cb54fcd1
fof(ordinal_5Ftrichotomy_5For,axiom,(! [X0] : (! [X1] : (ordinal(X0) => (ordinal(X1) => ((c_In(X0,X1) | (X0 = X1)) | c_In(X1,X0))))))). % a054b9f2adc3c9aa1a08efff8ca5d3860648fdd30782e256d62d4780928f0527
fof(ordinal_5FIn_5FOr_5FSubq,axiom,(! [X0] : (! [X1] : (ordinal(X0) => (ordinal(X1) => (c_In(X0,X1) | c_Subq(X1,X0))))))). % 09da9fad48807fad9f2b9721559a05e7578fedd1db356b3d19a5b495a8705ca1
fof(ordinal_5Flinear,axiom,(! [X0] : (! [X1] : (ordinal(X0) => (ordinal(X1) => (c_Subq(X0,X1) | c_Subq(X1,X0))))))). % d4adb7ddf915ec8cb21856079ef7187f8913b56182627cf9fd90e92247cc6386
fof(ordinal_5Fordsucc_5FIn_5Feq,axiom,(! [X0] : (! [X1] : (ordinal(X0) => (c_In(X1,X0) => (c_In(ordsucc(X1),X0) | (X0 = ordsucc(X1)))))))). % 220049d253ebf539e8a1443b2a67713d383fd26cd6866bb9965dabb35dce3b5c
fof(ordinal_5Flim_5For_5Fsucc,axiom,(! [X0] : (ordinal(X0) => ((! [X1] : (c_In(X1,X0) => c_In(ordsucc(X1),X0))) | (? [X1] : (c_In(X1,X0) & (X0 = ordsucc(X1)))))))). % fbbd3e5e926d98e8040a13a3cfaea218849f729cf2b37f371009301dfd1bf1e5
fof(ordinal_5Fordsucc_5FIn,axiom,(! [X0] : (ordinal(X0) => (! [X1] : (c_In(X1,X0) => c_In(ordsucc(X1),ordsucc(X0))))))). % ac83daedcf407d89b72e0c78791eadd4340bd2ce588ae6a25475567214c2882e
fof(ordinal_5Fbinintersect,axiom,(! [X0] : (! [X1] : (ordinal(X0) => (ordinal(X1) => ordinal(binintersect(X0,X1))))))). % d4f47492790cc73f4b9cb9a88f2af365da9a5e26beea013a378fb362e91654d0
fof(ordinal_5Fbinunion,axiom,(! [X0] : (! [X1] : (ordinal(X0) => (ordinal(X1) => ordinal(binunion(X0,X1))))))). % 2497d01bc684e95b825b420569be58c8f9bf47a427ebdc577e04495a75b977ca
fof(equip_5FSing_5F1,axiom,(! [X0] : equip(c_Sing(X0),ordsucc(c_Empty)))). % 2935454ba5e75673d42d6f1e97ef47ba8c5a190549194d417decdd893b6213d8
fof(c_TransSet_5FIn_5Fordsucc_5FSubq,axiom,(! [X0] : (! [X1] : (c_TransSet(X1) => (c_In(X0,ordsucc(X1)) => c_Subq(X0,X1)))))). % 45f286c22bbf504814edc27760e94b06ac05ad12bdc770d46d62391637088cf3
fof(add_5Fnat_5F0R,axiom,(! [X0] : (add_5Fnat(X0,c_Empty) = X0))). % 7d61592cda992271a7e6273ed2263332d27657c2e385c19edf62c6c68c47f52f
fof(add_5Fnat_5FSR,axiom,(! [X0] : (! [X1] : (nat_5Fp(X1) => (add_5Fnat(X0,ordsucc(X1)) = ordsucc(add_5Fnat(X0,X1))))))). % 3ff28336099e542946c343bfde70e14dae575e7382099fe159f6105bdcef171c
fof(add_5Fnat_5Fp,axiom,(! [X0] : (nat_5Fp(X0) => (! [X1] : (nat_5Fp(X1) => nat_5Fp(add_5Fnat(X0,X1))))))). % 730437b6bf6db9b377d1098f35bc67a27dc4c6620cb59b925ad2595dec5284b6
fof(add_5Fnat_5F1_5F1_5F2,axiom,(add_5Fnat(ordsucc(c_Empty),ordsucc(c_Empty)) = ordsucc(ordsucc(c_Empty)))). % 2d50c38a5daaaa1e2c39a30b90bf8956629f9bf990af51b24d1e928c9c144ad0
fof(add_5Fnat_5Fasso,axiom,(! [X0] : (nat_5Fp(X0) => (! [X1] : (nat_5Fp(X1) => (! [X2] : (nat_5Fp(X2) => (add_5Fnat(add_5Fnat(X0,X1),X2) = add_5Fnat(X0,add_5Fnat(X1,X2)))))))))). % 045e42255a92977b903c8c6967b3fa2c10b099a88cbb5c1d3a8a32c286a752d4
fof(add_5Fnat_5F0L,axiom,(! [X0] : (nat_5Fp(X0) => (add_5Fnat(c_Empty,X0) = X0)))). % 1fa7e354a68b10497d3645fc92610e4e0eccaf341e22ef75fe9ba35800ece955
fof(add_5Fnat_5FSL,axiom,(! [X0] : (nat_5Fp(X0) => (! [X1] : (nat_5Fp(X1) => (add_5Fnat(ordsucc(X0),X1) = ordsucc(add_5Fnat(X0,X1)))))))). % 7d3a5854eed1c707b1f7ebe50b01fe7c200bc104673844fa4f7c47a914025b0c
fof(add_5Fnat_5Fcom,axiom,(! [X0] : (nat_5Fp(X0) => (! [X1] : (nat_5Fp(X1) => (add_5Fnat(X0,X1) = add_5Fnat(X1,X0))))))). % 56d5f409ad087402acbd486475b43da7169b8f1f7930430f9b032c6eea4cd8c7
fof(add_5Fnat_5FIn_5FR,axiom,(! [X0] : (nat_5Fp(X0) => (! [X1] : (c_In(X1,X0) => (! [X2] : (nat_5Fp(X2) => c_In(add_5Fnat(X1,X2),add_5Fnat(X0,X2))))))))). % a9f8678f6b9aff4e2c3675bb0143fe714bb7400b33971be867b41dff25a8f875
fof(add_5Fnat_5FIn_5FL,axiom,(! [X0] : (nat_5Fp(X0) => (! [X1] : (nat_5Fp(X1) => (! [X2] : (c_In(X2,X1) => c_In(add_5Fnat(X0,X2),add_5Fnat(X0,X1))))))))). % e4f48f0fe940261152085e80bc7d1e10ac9d8d4d69233cb7cc4a6cce3b667bdf
fof(add_5Fnat_5FSubq_5FR,axiom,(! [X0] : (nat_5Fp(X0) => (! [X1] : (nat_5Fp(X1) => (c_Subq(X0,X1) => (! [X2] : (nat_5Fp(X2) => c_Subq(add_5Fnat(X0,X2),add_5Fnat(X1,X2)))))))))). % ec5b18493779f2d893a481d507c4bc20edde931f109adc736428d5f3027a6b22
fof(add_5Fnat_5FSubq_5FL,axiom,(! [X0] : (nat_5Fp(X0) => (! [X1] : (nat_5Fp(X1) => (! [X2] : (nat_5Fp(X2) => (c_Subq(X1,X2) => c_Subq(add_5Fnat(X0,X1),add_5Fnat(X0,X2)))))))))). % cdfee7ce10cffc1f878cf6e8d01acc82467a574cdfd4d33f0f67a88e5d189987
fof(add_5Fnat_5FSubq_5FR_27,axiom,(! [X0] : (nat_5Fp(X0) => (! [X1] : (nat_5Fp(X1) => c_Subq(X0,add_5Fnat(X0,X1))))))). % 237818149ba4d8d868d91e9064674ba5c420319b6651be940087cf2a788be19a
fof(nat_5FSubq_5Fadd_5Fex,axiom,(! [X0] : (nat_5Fp(X0) => (! [X1] : (nat_5Fp(X1) => (c_Subq(X0,X1) => (? [X2] : (nat_5Fp(X2) & (X1 = add_5Fnat(X2,X0)))))))))). % f74b4d9205544b3b06be1a1c60f23e14f9f9235bc5528e481761c8016835cf16
fof(add_5Fnat_5Fcancel_5FR,axiom,(! [X0] : (nat_5Fp(X0) => (! [X1] : (nat_5Fp(X1) => (! [X2] : (nat_5Fp(X2) => ((add_5Fnat(X0,X2) = add_5Fnat(X1,X2)) => (X0 = X1))))))))). % 27d1f65ac2897c5ba2a7224055e76b822a51bd43226ab030fd091a65740699b0
fof(mul_5Fnat_5F0R,axiom,(! [X0] : (mul_5Fnat(X0,c_Empty) = c_Empty))). % 1c25e05c4603a77785aed53a6a5209909fe7f4cd5953eebc28df5e21c9ab4ba5
fof(mul_5Fnat_5FSR,axiom,(! [X0] : (! [X1] : (nat_5Fp(X1) => (mul_5Fnat(X0,ordsucc(X1)) = add_5Fnat(X0,mul_5Fnat(X0,X1))))))). % a0997331d770097ccd784eb8ced2e8f44d0e2dcf9e3dd39011faa28e689f4353
fof(mul_5Fnat_5F1R,axiom,(! [X0] : (mul_5Fnat(X0,ordsucc(c_Empty)) = X0))). % 6aa56ecf8db3206c2d10629077762b8cb5ae9d122f1ce6a47664d3b394a01ebe
fof(mul_5Fnat_5Fp,axiom,(! [X0] : (nat_5Fp(X0) => (! [X1] : (nat_5Fp(X1) => nat_5Fp(mul_5Fnat(X0,X1))))))). % 81282d41c191f806a5174aabeb00a18b90d6a03adb1b8c65816c0d4aabe3436c
fof(mul_5Fnat_5F0L,axiom,(! [X0] : (nat_5Fp(X0) => (mul_5Fnat(c_Empty,X0) = c_Empty)))). % 5c6e8dcdbb30039a623b8d6fcd1507ddb3cee643a49cf25865a2693cf62ecc18
fof(mul_5Fnat_5FSL,axiom,(! [X0] : (nat_5Fp(X0) => (! [X1] : (nat_5Fp(X1) => (mul_5Fnat(ordsucc(X0),X1) = add_5Fnat(mul_5Fnat(X0,X1),X1))))))). % 7f25b75f5d7c951c5be77314eb5f5237721ad7d145b1317f6052cf266af1267b
fof(mul_5Fnat_5Fcom,axiom,(! [X0] : (nat_5Fp(X0) => (! [X1] : (nat_5Fp(X1) => (mul_5Fnat(X0,X1) = mul_5Fnat(X1,X0))))))). % 5dafc018f318b9cfdc486791b3c1f84536f5175ecc52be50ef0dcdaf3023f5c1
fof(mul_5Fadd_5Fnat_5FdistrL,axiom,(! [X0] : (nat_5Fp(X0) => (! [X1] : (nat_5Fp(X1) => (! [X2] : (nat_5Fp(X2) => (mul_5Fnat(X0,add_5Fnat(X1,X2)) = add_5Fnat(mul_5Fnat(X0,X1),mul_5Fnat(X0,X2)))))))))). % 36b92bfa9dca102e751ebfc48f8b7c82aabda4df92d7d80af98748fca048a4c7
fof(mul_5Fnat_5Fasso,axiom,(! [X0] : (nat_5Fp(X0) => (! [X1] : (nat_5Fp(X1) => (! [X2] : (nat_5Fp(X2) => (mul_5Fnat(mul_5Fnat(X0,X1),X2) = mul_5Fnat(X0,mul_5Fnat(X1,X2)))))))))). % fe1cdc6bebe8e400d978f991f61a3cff9ec1d80c9cf2833c67e4a43170838ad2
fof(mul_5Fnat_5FSubq_5FR,axiom,(! [X0] : (! [X1] : (nat_5Fp(X0) => (nat_5Fp(X1) => (c_Subq(X0,X1) => (! [X2] : (nat_5Fp(X2) => c_Subq(mul_5Fnat(X0,X2),mul_5Fnat(X1,X2)))))))))). % 1a501261276e127b7641814d8a2a88d4486ff19b28650314e9c7fbacb9bc079f
fof(mul_5Fnat_5FSubq_5FL,axiom,(! [X0] : (! [X1] : (nat_5Fp(X0) => (nat_5Fp(X1) => (c_Subq(X0,X1) => (! [X2] : (nat_5Fp(X2) => c_Subq(mul_5Fnat(X2,X0),mul_5Fnat(X2,X1)))))))))). % fd275249cf976f2a7760093cdfd7fd450e9aac3f63fcb090fef1e7745d533f8b
fof(mul_5Fnat_5F0_5For_5FSubq,axiom,(! [X0] : (nat_5Fp(X0) => (! [X1] : (nat_5Fp(X1) => ((X1 = c_Empty) | c_Subq(X0,mul_5Fnat(X0,X1)))))))). % 75872195071aa84c44e054a56ae06391025a38dd49b18bb95f2a42422afb9799
fof(mul_5Fnat_5F0_5Finv,axiom,(! [X0] : (nat_5Fp(X0) => (! [X1] : (nat_5Fp(X1) => ((mul_5Fnat(X0,X1) = c_Empty) => ((X0 = c_Empty) | (X1 = c_Empty)))))))). % 5aa784292ac64fec0bf2ae2b51b5fa973081f2136cbd872acd256c46c1b4d5e5
fof(mul_5Fnat_5F0m_5F1n_5FIn,axiom,(! [X0] : (nat_5Fp(X0) => (! [X1] : (nat_5Fp(X1) => (c_In(c_Empty,X0) => (c_In(ordsucc(c_Empty),X1) => c_In(X0,mul_5Fnat(X0,X1))))))))). % 4c7fa729d227c63fc80a97a88bd99633026314aa1764dc50e3c5c09097a46777
fof(nat_5Fle1_5Fcases,axiom,(! [X0] : (nat_5Fp(X0) => (c_Subq(X0,ordsucc(c_Empty)) => ((X0 = c_Empty) | (X0 = ordsucc(c_Empty))))))). % 4cb18344605410558b1bb29d78334e3787b34a88d79a2a10b160f26232b03d68
fof(exp_5Fnat_5F0,axiom,(! [X0] : (exp_5Fnat(X0,c_Empty) = ordsucc(c_Empty)))). % 64564fa8ee47854d18ef03b8a47d2e0b0f3148e289b0cfab9d98148f6e4f0e8c
fof(exp_5Fnat_5FS,axiom,(! [X0] : (! [X1] : (nat_5Fp(X1) => (exp_5Fnat(X0,ordsucc(X1)) = mul_5Fnat(X0,exp_5Fnat(X0,X1))))))). % 00cabf9080858792f3b0322de8dd7a30042ce20af578b0b520ca754e27a25bae
fof(exp_5Fnat_5Fp,axiom,(! [X0] : (nat_5Fp(X0) => (! [X1] : (nat_5Fp(X1) => nat_5Fp(exp_5Fnat(X0,X1))))))). % 143a34da955b23f8477b50fe3b38275242d92ae47db85be2244f277897c9b4c6
fof(exp_5Fnat_5F1,axiom,(! [X0] : (exp_5Fnat(X0,ordsucc(c_Empty)) = X0))). % 5005740bcd195374ecccf262b6836f4cb342fa466b2c1cae583001974e1384c2
fof(c_Subq_5FSing0_5F1,axiom,c_Subq(c_Sing(c_Empty),ordsucc(c_Empty))). % 0e40fcb04a8f7ad1d0405977385db9860ab8b5dbcb5dd05429b29635bd9c752d
fof(c_Subq_5F1_5FSing0,axiom,c_Subq(ordsucc(c_Empty),c_Sing(c_Empty))). % 3daeac206ef9dbd4f7a4aa8765e6686fd85e62ef77021e1eea726d043250e165
fof(eq_5F1_5FSing0,axiom,(ordsucc(c_Empty) = c_Sing(c_Empty))). % 462eb66d70f8968cc23223145b623b832440f8e9ac6e2df1a4ec85b1216c46e4
fof(c_Power_5F0_5FSing_5F0,axiom,(c_Power(c_Empty) = c_Sing(c_Empty))). % ca046301fdb4edaca3fc29972d19e61ea46190504ad75cc052cd41e0767cacf5
fof(equip_5Ffinite_5FPower,axiom,(! [X0] : (nat_5Fp(X0) => (! [X1] : (equip(X1,X0) => equip(c_Power(X1),exp_5Fnat(ordsucc(ordsucc(c_Empty)),X0))))))). % bcba661c1f665d04a40219fdcc5ec90606df3614ffb0b04f17c8e8bcd445618c
fof(c_ZF_5FUnion_5Fclosed,axiom,(! [X0] : (c_ZF_5Fclosed(X0) => (! [X1] : (c_In(X1,X0) => c_In(c_Union(X1),X0)))))). % 770bbc340371270dd000db2a2b4eb42d80f7c8f91c73432d4ff222192397d9f2
fof(c_ZF_5FPower_5Fclosed,axiom,(! [X0] : (c_ZF_5Fclosed(X0) => (! [X1] : (c_In(X1,X0) => c_In(c_Power(X1),X0)))))). % a6534f04454d7edd053388350167f3e7187d43f2b4e4bdacfa1f0cf6f5437f40
fof(c_ZF_5FUPair_5Fclosed,axiom,(! [X0] : (c_ZF_5Fclosed(X0) => (! [X1] : (c_In(X1,X0) => (! [X2] : (c_In(X2,X0) => c_In(c_UPair(X1,X2),X0)))))))). % 0813b3bb3dfa22cc009caa082ba9f5c37806be52dd7d1b4d83b8f6c689aee42a
fof(c_ZF_5FSing_5Fclosed,axiom,(! [X0] : (c_ZF_5Fclosed(X0) => (! [X1] : (c_In(X1,X0) => c_In(c_Sing(X1),X0)))))). % 66716e1d543ac0baf231dae6744a4a5a10a0930d17fab90dfdd4eec7816751d2
fof(c_ZF_5Fbinunion_5Fclosed,axiom,(! [X0] : (c_ZF_5Fclosed(X0) => (! [X1] : (c_In(X1,X0) => (! [X2] : (c_In(X2,X0) => c_In(binunion(X1,X2),X0)))))))). % f9a9a882ac70cbe15a495176ab8d179454f9f4eb33566565c252adf93e844c44
fof(c_ZF_5Fordsucc_5Fclosed,axiom,(! [X0] : (c_ZF_5Fclosed(X0) => (! [X1] : (c_In(X1,X0) => c_In(ordsucc(X1),X0)))))). % 957b86f89abb0956046fc26b27566c10a6578da9b07758782786a09f83a32280
fof(nat_5Fp_5FUnivOf_5FEmpty,axiom,(! [X0] : (nat_5Fp(X0) => c_In(X0,c_UnivOf(c_Empty))))). % 2d41721b17a0e4d156482e1a80913710c514d5acabff7e406829794525ab748f
fof(omega_5Fnat_5Fp,axiom,(! [X0] : (c_In(X0,omega) => nat_5Fp(X0)))). % 7d6896163f052ef582e2a72a8911b4c98c592a603f8a706a5b5bcba281c2441b
fof(nat_5Fp_5Fomega,axiom,(! [X0] : (nat_5Fp(X0) => c_In(X0,omega)))). % cd49a636af3e3734e4fffd883d424478c3079474a4c7d6e668a59efdabd07c2a
fof(omega_5Fordsucc,axiom,(! [X0] : (c_In(X0,omega) => c_In(ordsucc(X0),omega)))). % f88efc1bceb13c969121ead8cc2c43f0ce2f1c2aeeab14ec80e7cbae241b81b8
fof(form100_5F22_5Fv1,axiom,~ equip(omega,c_Power(omega))). % 744d1c153770611409ad98e77d0da8f38633e60aca3593e2132aeca6f62fb81f
fof(omega_5FTransSet,axiom,c_TransSet(omega)). % cda7674a8828a6006cdfe366c73bf45ef99744f0bfee24f192a44ef757bfae32
fof(omega_5Fordinal,axiom,ordinal(omega)). % 97063ca4238502077443b4213f8c0c8a5c92df74c58379dad63ffd89d8611645
fof(ordsucc_5Fomega_5Fordinal,axiom,ordinal(ordsucc(omega))). % c4e4e9e852b1530c752302ce07df33b34a78bafefb18949ae499d84519158cf5
fof(finite,axiom,(! [X0:$i] : (finite(c_X0) <=> (? [X1] : (c_In(X1,omega) & equip(c_X0,X1)))))). % 0498e68493e445a8fce3569ba778f96fe83f914d7905473f18fe1fee01869f5f
fof(nat_5Ffinite,axiom,(! [X0] : (nat_5Fp(X0) => finite(X0)))). % 7310a8b96bbcae7357ad95ec125c7d9c323451f363bc3ea9741756c5987ed644
fof(finite_5FEmpty,axiom,finite(c_Empty)). % 8ac4c6dd26a01fcc1131a5780ad957823abee3db4e69cc636b7ffa9d5fd3f6ac
fof(c_Sing_5Ffinite,axiom,(! [X0] : finite(c_Sing(X0)))). % 347250bb7c9d481f3038d5884e7719044bdccb65ce3d1b2a23e422bd90e91bd3
fof(adjoin_5Ffinite,axiom,(! [X0] : (! [X1] : (finite(X0) => finite(binunion(X0,c_Sing(X1))))))). % 994213b5f728ade8d57935c4a138f1aba2693e608c68a30fefdacc9488294b76
fof(binunion_5Ffinite,axiom,(! [X0] : (finite(X0) => (! [X1] : (finite(X1) => finite(binunion(X0,X1))))))). % 214d9a120bc124776b330eba7fd4ccf5fb691aa1523337cdd88fd4e3bddc3fef
fof(c_Subq_5Ffinite,axiom,(! [X0] : (finite(X0) => (! [X1] : (c_Subq(X1,X0) => finite(X1)))))). % b0bc93a82c39c3c1201ba05be25fbc07327f36a3a002d4000e2c4b8504ea2bf2
fof(infinite,axiom,(! [X0:$i] : (infinite(c_X0) <=> ~ finite(c_X0)))). % 7b21e4abd94d496fba9bd902c949754d45c46d1896ef4a724d6867561c7055ed
fof(divides_5Fnat,axiom,(! [X0:$i] : (! [X1:$i] : (divides_5Fnat(c_X0,c_X1) <=> ((c_In(c_X0,omega) & c_In(c_X1,omega)) & (? [X2] : (c_In(X2,omega) & (mul_5Fnat(c_X0,X2) = c_X1)))))))). % d4edc81b103a7f8386389b4214215e09786f1c39c399dd0cc78b51305ee606ce
fof(divides_5Fnat_5Fref,axiom,(! [X0] : (nat_5Fp(X0) => divides_5Fnat(X0,X0)))). % ed482f4339e840cef384668b52215697f2dba16af99ff1b1a7e89168852e6fe4
fof(divides_5Fnat_5Ftra,axiom,(! [X0] : (! [X1] : (! [X2] : (divides_5Fnat(X0,X1) => (divides_5Fnat(X1,X2) => divides_5Fnat(X0,X2))))))). % 5cd17604b841b72089f518d8c0024fe75500eea06497bfcfba3ad681df2bbb23
fof(prime_5Fnat,axiom,(! [X0:$i] : (prime_5Fnat(c_X0) <=> ((c_In(c_X0,omega) & c_In(ordsucc(c_Empty),c_X0)) & (! [X1] : (c_In(X1,omega) => (divides_5Fnat(X1,c_X0) => ((X1 = ordsucc(c_Empty)) | (X1 = c_X0))))))))). % 894d319b8678a53d5ba0debfa7c31b2615043dbd1e2916815fe1b2e94b3bb6c4
fof(divides_5Fnat_5FmulR,axiom,(! [X0] : (c_In(X0,omega) => (! [X1] : (c_In(X1,omega) => divides_5Fnat(X0,mul_5Fnat(X0,X1))))))). % 9e83030b6521c73982823df0ef60403113facc6234c2f758585df04fa52c3ea6
fof(divides_5Fnat_5FmulL,axiom,(! [X0] : (c_In(X0,omega) => (! [X1] : (c_In(X1,omega) => divides_5Fnat(X1,mul_5Fnat(X0,X1))))))). % 37d28bd76657b898d02f70620f8cfd71d7fa1bfb25a5a7271e163046364ee96d
fof(composite_5Fnat,axiom,(! [X0:$i] : (composite_5Fnat(c_X0) <=> (c_In(c_X0,omega) & (? [X1] : (c_In(X1,omega) & (? [X2] : (c_In(X2,omega) & ((c_In(ordsucc(c_Empty),X1) & c_In(ordsucc(c_Empty),X2)) & (mul_5Fnat(X1,X2) = c_X0)))))))))). % 139cb816cd2cc78d77099c5118e6cc48108521f2e7f1338351b7c6c10db4341e
fof(prime_5Fnat_5For_5Fcomposite_5Fnat,axiom,(! [X0] : (c_In(X0,omega) => (c_In(ordsucc(c_Empty),X0) => (prime_5Fnat(X0) | composite_5Fnat(X0)))))). % 76dd5e2590174c494d2ccee1d9bb1570b4473d5df5da09c5c3c3229f8db34d71
fof(prime_5Fnat_5Fdivisor_5Fex,axiom,(! [X0] : (nat_5Fp(X0) => (c_In(ordsucc(c_Empty),X0) => (? [X1] : (prime_5Fnat(X1) & divides_5Fnat(X1,X0))))))). % 24eee661d4abf80e8f6ab082cd3582dce30a5226c65c99920435af4988297192
fof(nat_5F1In_5Fnot_5Fdivides_5Fordsucc,axiom,(! [X0] : (! [X1] : (c_In(ordsucc(c_Empty),X0) => (divides_5Fnat(X0,X1) => ~ divides_5Fnat(X0,ordsucc(X1))))))). % 1e0906006cb582285bddc00c6d5f60b5739c50fcd71814d655f22a588bc21837
fof(form100_5F11_5Finfinite_5Fprimes,axiom,infinite(primes)). % b74b5f1af364a75e0b81351febbe7be21811efdf114d70d2a2319d7391e79230
fof(atleastp_5Fomega_5Finfinite,axiom,(! [X0] : (atleastp(omega,X0) => infinite(X0)))). % bf226a0b1ea7fb05a4da7f5527cb83fb1ed8ecf88bf564ed2bf8f49981de71f9
fof(infinite_5Fremove1,axiom,(! [X0] : (infinite(X0) => (! [X1] : infinite(setminus(X0,c_Sing(X1))))))). % 02fae027b5f3a44a9e176923884ad5fc5b832ce65e511e47adebd37d8c8bdcd0
fof(infinite_5FFinite_5FSubq_5Fex,axiom,(! [X0] : (infinite(X0) => (! [X1] : (nat_5Fp(X1) => (? [X2] : (c_Subq(X2,X0) & equip(X2,X1)))))))). % d2068956af6c99c46fd2eb835031b1c182bd6c0100cd2c9953e35a9eb1a47b64
fof(c_Inj1I1,axiom,(! [X0] : c_In(c_Empty,c_Inj1(X0)))). % fd47fce7492115008e84f96242887df63f2c25b934e43b78bb7a40f737203d3e
fof(c_Inj1I2,axiom,(! [X0] : (! [X1] : (c_In(X1,X0) => c_In(c_Inj1(X1),c_Inj1(X0)))))). % f6517cd4bea9a42fec27e2960fbf0a487ed7bd0d925f0ad4868c80591ff00f05
fof(c_Inj1E,axiom,(! [X0] : (! [X1] : (c_In(X1,c_Inj1(X0)) => ((X1 = c_Empty) | (? [X2] : (c_In(X2,X0) & (X1 = c_Inj1(X2))))))))). % e1d2bb83f1a5a2ee1607e06fd7503dbc8fbb5ec1f3c7dd2d799aed18d4a5ab8b
fof(c_Inj1NE1,axiom,(! [X0] : ~ (c_Inj1(X0) = c_Empty))). % 738faec82062038b781daa79c023afae5797d97ddda4c3fb46b416fb01adca9b
fof(c_Inj1NE2,axiom,(! [X0] : nIn(c_Inj1(X0),c_Sing(c_Empty)))). % c34503dfb4a66da3255cda46d2ad4afc254b91bc7e1fb5556a7412db6fe897e7
fof(c_Inj0I,axiom,(! [X0] : (! [X1] : (c_In(X1,X0) => c_In(c_Inj1(X1),c_Inj0(X0)))))). % d0db97710b54b3d4b3760d1b977dba2a0cac4f88805706e1045bfbe39c70d3e7
fof(c_Inj0E,axiom,(! [X0] : (! [X1] : (c_In(X1,c_Inj0(X0)) => (? [X2] : (c_In(X2,X0) & (X1 = c_Inj1(X2)))))))). % 8bd5ce42b204f22a170d994b0b30a00aa42803457f63be71fe5abaadf7d62357
fof(c_Unj_5FInj1_5Feq,axiom,(! [X0] : (c_Unj(c_Inj1(X0)) = X0))). % 6781de11ad3549d51983b4f6d68d0ba6ca8d08c124b3730db0d2bbd36e4b34d4
fof(c_Inj1_5Finj,axiom,(! [X0] : (! [X1] : ((c_Inj1(X0) = c_Inj1(X1)) => (X0 = X1))))). % 6143505926f2a52ef470cdd14557be4b20217acdafe8fe22045d8a8737c59826
fof(c_Unj_5FInj0_5Feq,axiom,(! [X0] : (c_Unj(c_Inj0(X0)) = X0))). % 484ae1a22b173961b4935f82308b8c3228ade330857ff5b364b82ed4928be58d
fof(c_Inj0_5Finj,axiom,(! [X0] : (! [X1] : ((c_Inj0(X0) = c_Inj0(X1)) => (X0 = X1))))). % 2ee431f4aa3ae125e32ae68cf882ab59e65e812b2eeb61a4e9928c5aa55799e7
fof(c_Inj0_5F0,axiom,(c_Inj0(c_Empty) = c_Empty)). % 4373dae6b59b877246ee56295dc5b1b7a50bba331863147aa9b8d955c62593f6
fof(c_Inj0_5FInj1_5Fneq,axiom,(! [X0] : (! [X1] : ~ (c_Inj0(X0) = c_Inj1(X1))))). % 8538b2a67bd1750a16d74b25123502e94d8a36dceec1ca6bc2a25bd39ee77eef
fof(c_Inj0_5Fsetsum,axiom,(! [X0] : (! [X1] : (! [X2] : (c_In(X2,X0) => c_In(c_Inj0(X2),setsum(X0,X1))))))). % 766879245550a679e80f1cfe45bdb81458755b15090bd4139138664d3e059f4e
fof(c_Inj1_5Fsetsum,axiom,(! [X0] : (! [X1] : (! [X2] : (c_In(X2,X1) => c_In(c_Inj1(X2),setsum(X0,X1))))))). % 96787ab4522603ed0a9c0d49f640b466ac23e204e4d893e0e5286fb80dc6e304
fof(setsum_5FInj_5Finv,axiom,(! [X0] : (! [X1] : (! [X2] : (c_In(X2,setsum(X0,X1)) => ((? [X3] : (c_In(X3,X0) & (X2 = c_Inj0(X3)))) | (? [X3] : (c_In(X3,X1) & (X2 = c_Inj1(X3)))))))))). % caf4d23eb5c23adcd7765914d08d1fea446064d3a43ac60356f9bfdf7959fc1c
fof(c_Inj0_5Fsetsum_5F0L,axiom,(! [X0] : (setsum(c_Empty,X0) = c_Inj0(X0)))). % cfa10490ab2b5a68cdcc29d20d402ab4c778e2dcb24a49fc70b19a4c49725a26
fof(c_Inj1_5Fsetsum_5F1L,axiom,(! [X0] : (setsum(ordsucc(c_Empty),X0) = c_Inj1(X0)))). % 64441bd03320644fe91d6f303460858abbd281f41478d528259ed6336c579fad
fof(pairI0,axiom,(! [X0] : (! [X1] : (! [X2] : (c_In(X2,X0) => c_In(setsum(c_Empty,X2),setsum(X0,X1))))))). % 0804a802aaa3dcd31866602001d233f0586dec6358f1b5a66e2bf57153997bc2
fof(pairI1,axiom,(! [X0] : (! [X1] : (! [X2] : (c_In(X2,X1) => c_In(setsum(ordsucc(c_Empty),X2),setsum(X0,X1))))))). % 3f8a360d22ed18a4f87ea857a20b041400df72686a549905e83a13f79d5b05ce
fof(pairE,axiom,(! [X0] : (! [X1] : (! [X2] : (c_In(X2,setsum(X0,X1)) => ((? [X3] : (c_In(X3,X0) & (X2 = setsum(c_Empty,X3)))) | (? [X3] : (c_In(X3,X1) & (X2 = setsum(ordsucc(c_Empty),X3)))))))))). % 3799560e6c62d771e822549a283ac35b47249b561dcba22623ddb762bb120f65
fof(pairE0,axiom,(! [X0] : (! [X1] : (! [X2] : (c_In(setsum(c_Empty,X2),setsum(X0,X1)) => c_In(X2,X0)))))). % 0b843a4a65b099d398936e97e23546403ea21f3b55e68363644786b521514cbc
fof(pairE1,axiom,(! [X0] : (! [X1] : (! [X2] : (c_In(setsum(ordsucc(c_Empty),X2),setsum(X0,X1)) => c_In(X2,X1)))))). % 180235049e02e795a7cf966ec6493a6152e3ed9fc6eaa2f5bfe3b40482c413b6
fof(proj0I,axiom,(! [X0] : (! [X1] : (c_In(setsum(c_Empty,X1),X0) => c_In(X1,proj0(X0)))))). % ecde17c57f66ca17a6d8933369505476f3e7e78d2872b01bd09e8eb11a8aeb42
fof(proj0E,axiom,(! [X0] : (! [X1] : (c_In(X1,proj0(X0)) => c_In(setsum(c_Empty,X1),X0))))). % 614eb94c05c40e8e3a01f177d4a3be4966982f4b8429194dcbd088893e9247f9
fof(proj1I,axiom,(! [X0] : (! [X1] : (c_In(setsum(ordsucc(c_Empty),X1),X0) => c_In(X1,proj1(X0)))))). % db372cdab16550941b13ec55dbf160533b5af327ba9e1a5a66835dc6a5c2e5aa
fof(proj1E,axiom,(! [X0] : (! [X1] : (c_In(X1,proj1(X0)) => c_In(setsum(ordsucc(c_Empty),X1),X0))))). % 7498b22a5d3e0a65a58c859b0b46474211fe10352426978ae231141e7cb2e52a
fof(proj0_5Fpair_5Feq,axiom,(! [X0] : (! [X1] : (proj0(setsum(X0,X1)) = X0)))). % 3dacec991c0175748339f82f4e97d87062afee69fc856d4f3cb0395746726ae8
fof(proj1_5Fpair_5Feq,axiom,(! [X0] : (! [X1] : (proj1(setsum(X0,X1)) = X1)))). % 6db62e7454cac410c1bb7d47ca5ffb422be541b403aa5a5676fae0d637c290cd
fof(apI,axiom,(! [X0] : (! [X1] : (! [X2] : (c_In(setsum(X1,X2),X0) => c_In(X2,ap(X0,X1))))))). % 15e9c8a0f131914afadc04844c57cf3bac3970b6f5f268cd61a9b37723a1fb95
fof(apE,axiom,(! [X0] : (! [X1] : (! [X2] : (c_In(X2,ap(X0,X1)) => c_In(setsum(X1,X2),X0)))))). % f9d8af4a594df743259a9c0028fc982f3bbeb975295317cebe7ba9c3f9be234b
fof(proj0_5Fap_5F0,axiom,(! [X0] : (proj0(X0) = ap(X0,c_Empty)))). % 26848cea1a3da4464d0a7249309d20679d7b3ffbc61d5824da9abcefccc3565a
fof(proj1_5Fap_5F1,axiom,(! [X0] : (proj1(X0) = ap(X0,ordsucc(c_Empty))))). % f61e23e9dec80e1890e4293ed4e1d499602206878db13b432092ce8bc86e2601
fof(pair_5Fap_5F0,axiom,(! [X0] : (! [X1] : (ap(setsum(X0,X1),c_Empty) = X0)))). % eb48f25ea7b16be838069cb5889e7fb2965a9fd09cc1c2203335e3b297b2ac1b
fof(pair_5Fap_5F1,axiom,(! [X0] : (! [X1] : (ap(setsum(X0,X1),ordsucc(c_Empty)) = X1)))). % 98f3fca14a994b9fc3b4e6acd3fbc640bdf7b3c7ad847101cbeb85e22724a4e4
fof(pair_5Fp,axiom,(! [X0:$i] : (pair_5Fp(c_X0) <=> (setsum(ap(c_X0,c_Empty),ap(c_X0,ordsucc(c_Empty))) = c_X0)))). % dac986a57e8eb6cc7f35dc0ecc031b9ba0403416fabe2dbe130edd287a499231
fof(pair_5Fp_5FI,axiom,(! [X0] : (! [X1] : pair_5Fp(setsum(X0,X1))))). % 5c2096adf43a959f74630a66ca405b93edaa1197665480d76cfd66ae0151fc16
fof(c_Subq_5F2_5FUPair01,axiom,c_Subq(ordsucc(ordsucc(c_Empty)),c_UPair(c_Empty,ordsucc(c_Empty)))). % 4b24ca0dbe2f22bc64343d6ab8bca154ae06cbbd76d1f9d87416b8c01bc7ea60
fof(not_5FTransSet_5FSing1,axiom,~ c_TransSet(c_Sing(ordsucc(c_Empty)))). % 093e2d964b4774cb1ee77de1e48378d6d53d0fdd8cc4f792cb5ad9f56f6f4561
fof(not_5Fordinal_5FSing1,axiom,~ ordinal(c_Sing(ordsucc(c_Empty)))). % 8e1d083d5e1185b5e77d838f9a9112a747bdf48a5538e18f5c3f5e31be27d26a
fof(c_SNoElts_5Fmon,axiom,(! [X0] : (! [X1] : (c_Subq(X0,X1) => c_Subq(c_SNoElts_5F(X0),c_SNoElts_5F(X1)))))). % 4764d732f9298d5803593d4faf40fab0596b57ab994078a37f147c6fa7d87399
fof(c_SNo,axiom,(! [X0:$i] : (c_SNo(c_X0) <=> (? [X1] : (ordinal(X1) & c_SNo_5F(X1,c_X0)))))). % 87d7604c7ea9a2ae0537066afb358a94e6ac0cd80ba277e6b064422035a620cf
fof(c_SNo_5FSNo,axiom,(! [X0] : (ordinal(X0) => (! [X1] : (c_SNo_5F(X0,X1) => c_SNo(X1)))))). % fecf6a95dbdb07b07d7bf3811dd8f0089dc18d53039a95db44e515cb0eb585c3
fof(c_SNoLev_5Funiq_5FSubq,axiom,(! [X0] : (! [X1] : (! [X2] : (ordinal(X1) => (ordinal(X2) => (c_SNo_5F(X1,X0) => (c_SNo_5F(X2,X0) => c_Subq(X1,X2))))))))). % e05ee4347bd149842d7b3edee8c878e6fa2bcc8a4a5cd39e00285e0f618301f2
fof(c_SNoLev_5Funiq,axiom,(! [X0] : (! [X1] : (! [X2] : (ordinal(X1) => (ordinal(X2) => (c_SNo_5F(X1,X0) => (c_SNo_5F(X2,X0) => (X1 = X2))))))))). % 552f468a0b086a991689da666f7dd31eb36a4d3fb2dad0bbedc53e8ad7bf44fb
fof(c_SNoLev_5Fprop,axiom,(! [X0] : (c_SNo(X0) => (ordinal(c_SNoLev(X0)) & c_SNo_5F(c_SNoLev(X0),X0))))). % 432132c44a0a73294ec279a4cab5a152c8aecdcb5b2f925eb83d2b9e6b1d92b9
fof(c_SNoLev_5Fordinal,axiom,(! [X0] : (c_SNo(X0) => ordinal(c_SNoLev(X0))))). % 76299915fe11f8b6e7bed7dcac4f5b8d2502a490d3272ec1870391240616ea4f
fof(c_SNoLev_5F,axiom,(! [X0] : (c_SNo(X0) => c_SNo_5F(c_SNoLev(X0),X0)))). % 502e374188aa2b77376eae38b3998f21b5c757dd15d82fafda92a367eb41a69a
fof(c_SNo_5FSubq,axiom,(! [X0] : (! [X1] : (c_SNo(X0) => (c_SNo(X1) => (c_Subq(c_SNoLev(X0),c_SNoLev(X1)) => ((! [X2] : (c_In(X2,c_SNoLev(X0)) => (c_In(X2,X0) <=> c_In(X2,X1)))) => c_Subq(X0,X1)))))))). % 7d40ec6c0664737dcb97c06fea7dc6f41c479c89efec6b773906d8f3234e20ae
fof(c_SNoEq_5FI,axiom,(! [X0] : (! [X1] : (! [X2] : ((! [X3] : (c_In(X3,X0) => (c_In(X3,X1) <=> c_In(X3,X2)))) => c_SNoEq_5F(X0,X1,X2)))))). % c04fa5fc0c6dda287b5ebad6549ba5cdafbd4c3d0591adc7f31994ae1426ff4f
fof(c_SNo_5Feq,axiom,(! [X0] : (! [X1] : (c_SNo(X0) => (c_SNo(X1) => ((c_SNoLev(X0) = c_SNoLev(X1)) => (c_SNoEq_5F(c_SNoLev(X0),X0,X1) => (X0 = X1)))))))). % 479426bf6abc2a8eda4059fe0bdc2edb80783dacc2a7df6bbe5433cf47f59c96
fof(c_SNoLtLe,axiom,(! [X0] : (! [X1] : (c_SNoLt(X0,X1) => c_SNoLe(X0,X1))))). % b2e99a4053967efc919aa08fba88456eddf5ffebeb551f15077f6b621163d8f2
fof(c_SNoLeE,axiom,(! [X0] : (! [X1] : (c_SNo(X0) => (c_SNo(X1) => (c_SNoLe(X0,X1) => (c_SNoLt(X0,X1) | (X0 = X1)))))))). % ef9e3f9d2222a01c51ff9486f5f3449c10510b4a8940840b102afcc4538f1d9e
fof(c_SNoEq_5Fsym_5F,axiom,(! [X0] : (! [X1] : (! [X2] : (c_SNoEq_5F(X0,X1,X2) => c_SNoEq_5F(X0,X2,X1)))))). % 22b85a4ee842bf39960f0f7e7beca0e13dcd25083183e0630c3a63c22057f455
fof(c_SNoEq_5Ftra_5F,axiom,(! [X0] : (! [X1] : (! [X2] : (! [X3] : (c_SNoEq_5F(X0,X1,X2) => (c_SNoEq_5F(X0,X2,X3) => c_SNoEq_5F(X0,X1,X3)))))))). % 6b40401717316359f67cc99bee04cf85b28ba3a4b51b9f52a691ef2c53bebf0e
fof(c_SNoLtI2,axiom,(! [X0] : (! [X1] : (c_In(c_SNoLev(X0),c_SNoLev(X1)) => (c_SNoEq_5F(c_SNoLev(X0),X0,X1) => (c_In(c_SNoLev(X0),X1) => c_SNoLt(X0,X1))))))). % d78a55852c0d0d9d8b46a6b33d806ba852e2232ea9445b4aeb3cdc6885b01b4b
fof(c_SNoLtI3,axiom,(! [X0] : (! [X1] : (c_In(c_SNoLev(X1),c_SNoLev(X0)) => (c_SNoEq_5F(c_SNoLev(X1),X0,X1) => (nIn(c_SNoLev(X1),X0) => c_SNoLt(X0,X1))))))). % c17fb3121e022878d6db635b543ff130da6281e427b7cc0b9c32d7b7cacc8707
fof(c_SNoLt_5Firref,axiom,(! [X0] : ~ c_SNoLt(X0,X0))). % dcba6b19fa17f4b0070048f6407b74125a46efc0bd4a786380f86268f13359a9
fof(c_SNoLt_5Ftrichotomy_5For,axiom,(! [X0] : (! [X1] : (c_SNo(X0) => (c_SNo(X1) => ((c_SNoLt(X0,X1) | (X0 = X1)) | c_SNoLt(X1,X0))))))). % eaa81842fa36739c725e0b4f550ab1b3fdaf5ea0024cbad1c4aaaa20cc860aa2
fof(c_SNoLt_5Ftra,axiom,(! [X0] : (! [X1] : (! [X2] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (c_SNoLt(X0,X1) => (c_SNoLt(X1,X2) => c_SNoLt(X0,X2)))))))))). % fe300caf8beb0e008565ecc98206bb89404165fbe74886e66fcfc15ba45be4c6
fof(c_SNoLe_5Fref,axiom,(! [X0] : c_SNoLe(X0,X0))). % 7c1d85be4b629afce831e99f2f5867d8051fdb880bbadf0748409d3d3c73a749
fof(c_SNoLe_5Fantisym,axiom,(! [X0] : (! [X1] : (c_SNo(X0) => (c_SNo(X1) => (c_SNoLe(X0,X1) => (c_SNoLe(X1,X0) => (X0 = X1)))))))). % f1491688a56a2ff41f99dd44dc5bf8d50214c4c1d8288e53a65961d2cee48eca
fof(c_SNoLtLe_5Ftra,axiom,(! [X0] : (! [X1] : (! [X2] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (c_SNoLt(X0,X1) => (c_SNoLe(X1,X2) => c_SNoLt(X0,X2)))))))))). % 9bb662aa88ce9484c04396bb643e5f4437c310dd2750ee33faa2f16c2472b262
fof(c_SNoLeLt_5Ftra,axiom,(! [X0] : (! [X1] : (! [X2] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (c_SNoLe(X0,X1) => (c_SNoLt(X1,X2) => c_SNoLt(X0,X2)))))))))). % f6332de7a8cd08127aa67545930bdd077a519a694d9260d593650fec916e076b
fof(c_SNoLe_5Ftra,axiom,(! [X0] : (! [X1] : (! [X2] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (c_SNoLe(X0,X1) => (c_SNoLe(X1,X2) => c_SNoLe(X0,X2)))))))))). % b7b67d5efc7b9a820b8d91fa7c2352a70b61503c01a5833b444112c3c112d7e0
fof(c_SNoLtLe_5For,axiom,(! [X0] : (! [X1] : (c_SNo(X0) => (c_SNo(X1) => (c_SNoLt(X0,X1) | c_SNoLe(X1,X0))))))). % e851573527054dcf54f90c6b08e7b6fd425782807e0c97aa07c487752c64e990
fof(c_SNoCutP,axiom,(! [X0:$i] : (! [X1:$i] : (c_SNoCutP(c_X0,c_X1) <=> (((! [X2] : (c_In(X2,c_X0) => c_SNo(X2))) & (! [X2] : (c_In(X2,c_X1) => c_SNo(X2)))) & (! [X2] : (c_In(X2,c_X0) => (! [X3] : (c_In(X3,c_X1) => c_SNoLt(X2,X3)))))))))). % b102ccc5bf572aba76b2c5ff3851795ba59cb16151277dbee9ce5a1aad694334
fof(c_SNoCutP_5FL_5F0,axiom,(! [X0] : ((! [X1] : (c_In(X1,X0) => c_SNo(X1))) => c_SNoCutP(X0,c_Empty)))). % 74c4c96cc11dac54739265f965b4422d0b21ceda1b81b9730e989adc795916fb
fof(c_SNoCutP_5F0_5F0,axiom,c_SNoCutP(c_Empty,c_Empty)). % daa10b937db5e34057f9f72c338217e38a0e3d1dc4bc988b3f02b15983810750
fof(c_SNoS_5FE,axiom,(! [X0] : (ordinal(X0) => (! [X1] : (c_In(X1,c_SNoS_5F(X0)) => (? [X2] : (c_In(X2,X0) & c_SNo_5F(X2,X1)))))))). % 97de8c3d29c4c7e283fc254718af55a3dfda4f90ee242381cecf08b09f30c302
fof(c_SNoS_5FI,axiom,(! [X0] : (ordinal(X0) => (! [X1] : (! [X2] : (c_In(X2,X0) => (c_SNo_5F(X2,X1) => c_In(X1,c_SNoS_5F(X0))))))))). % b7009b09601d36ed20880e893510e7a2965140f6b62e77401a6e32b5b0e324ac
fof(c_SNoS_5FI2,axiom,(! [X0] : (! [X1] : (c_SNo(X0) => (c_SNo(X1) => (c_In(c_SNoLev(X0),c_SNoLev(X1)) => c_In(X0,c_SNoS_5F(c_SNoLev(X1))))))))). % 475ee31bb5ef4f03e03d96e927e4ace9a008c9a1c68a5546a4ef654e978b3226
fof(c_SNoS_5FSubq,axiom,(! [X0] : (! [X1] : (ordinal(X0) => (ordinal(X1) => (c_Subq(X0,X1) => c_Subq(c_SNoS_5F(X0),c_SNoS_5F(X1)))))))). % 63c027b06a4763947b80f631b3d62f50df10796c8c086849c42193973d9b2df9
fof(c_SNoLev_5Funiq2,axiom,(! [X0] : (ordinal(X0) => (! [X1] : (c_SNo_5F(X0,X1) => (c_SNoLev(X1) = X0)))))). % 7b558aaf28019b1565ea6ff06c78503b94a010d4e5bd1b25ac4cf29a18530d0a
fof(c_SNoS_5FIn_5Fneq,axiom,(! [X0] : (c_SNo(X0) => (! [X1] : (c_In(X1,c_SNoS_5F(c_SNoLev(X0))) => ~ (X1 = X0)))))). % 93b189c1e4800c0d3c162c802dd4f52d19cd98fa9e2d5680a74131ce119c26c8
fof(c_SNoS_5FSNoLev,axiom,(! [X0] : (c_SNo(X0) => c_In(X0,c_SNoS_5F(ordsucc(c_SNoLev(X0))))))). % c24bf222996f26ea3382318d614c67514b579f8d323cc3a93f9285b313a83c2e
fof(c_SNoCutP_5FSNoL_5FSNoR,axiom,(! [X0] : (c_SNo(X0) => c_SNoCutP(c_SNoL(X0),c_SNoR(X0))))). % 7d1173c52036f1f582722d0108ff0cd223892b1fe60e091c7e9f2f9e96d512a4
fof(c_SNoL_5FSNoS_5F,axiom,(! [X0] : c_Subq(c_SNoL(X0),c_SNoS_5F(c_SNoLev(X0))))). % f90534db883f5bb2c52c93984cd12ae464948251dce304b03d8e1f2534a63513
fof(c_SNoR_5FSNoS_5F,axiom,(! [X0] : c_Subq(c_SNoR(X0),c_SNoS_5F(c_SNoLev(X0))))). % 5cf4d5e518354f5ce261ec05e6e745fd6d21450bdc562c3a463235fe83d25ab4
fof(c_SNoL_5FSNoS,axiom,(! [X0] : (c_SNo(X0) => (! [X1] : (c_In(X1,c_SNoL(X0)) => c_In(X1,c_SNoS_5F(c_SNoLev(X0)))))))). % 31b2acc9913487882ffe3c822bc0c494155391a322ce1d3249565219cb708a2f
fof(c_SNoR_5FSNoS,axiom,(! [X0] : (c_SNo(X0) => (! [X1] : (c_In(X1,c_SNoR(X0)) => c_In(X1,c_SNoS_5F(c_SNoLev(X0)))))))). % 2dc5ff1f91f112208eb5f90b5c5b6fdb2d125dcae839b69164a58ec5469aa65a
fof(c_SNoL_5FI,axiom,(! [X0] : (c_SNo(X0) => (! [X1] : (c_SNo(X1) => (c_In(c_SNoLev(X1),c_SNoLev(X0)) => (c_SNoLt(X1,X0) => c_In(X1,c_SNoL(X0))))))))). % f02ec179e267b36be969b299fb8ae9580a08d3064b27b7332233dbadddc3c246
fof(c_SNoR_5FI,axiom,(! [X0] : (c_SNo(X0) => (! [X1] : (c_SNo(X1) => (c_In(c_SNoLev(X1),c_SNoLev(X0)) => (c_SNoLt(X0,X1) => c_In(X1,c_SNoR(X0))))))))). % 31011169cc97e07cf57a1ccbd467da7bf80acd392d9f1f785b48e3245dac8137
fof(c_SNo_5Feta,axiom,(! [X0] : (c_SNo(X0) => (X0 = c_SNoCut(c_SNoL(X0),c_SNoR(X0)))))). % 34518fedfeb7bc35495c1c6e8734d6d144213f84fcfa61bc56966af8b0f92cb8
fof(c_SNoCutP_5FSNo_5FSNoCut,axiom,(! [X0] : (! [X1] : (c_SNoCutP(X0,X1) => c_SNo(c_SNoCut(X0,X1)))))). % ca54060a6e00f4ffd391ac769875cafd14cb3d24db12192911ec5c5ff1f36994
fof(c_SNoCutP_5FSNoCut_5FL,axiom,(! [X0] : (! [X1] : (c_SNoCutP(X0,X1) => (! [X2] : (c_In(X2,X0) => c_SNoLt(X2,c_SNoCut(X0,X1)))))))). % b7924f3025effa9b29256ec8f68a28ef3d342290838d6b39144c7538888720d3
fof(c_SNoCutP_5FSNoCut_5FR,axiom,(! [X0] : (! [X1] : (c_SNoCutP(X0,X1) => (! [X2] : (c_In(X2,X1) => c_SNoLt(c_SNoCut(X0,X1),X2))))))). % 2794d31553dcbea2f1323dbd107a1eb8163d5edf3562dab8aeb926b173dfbdf1
fof(c_SNoCutP_5FSNoCut_5Ffst,axiom,(! [X0] : (! [X1] : (c_SNoCutP(X0,X1) => (! [X2] : (c_SNo(X2) => ((! [X3] : (c_In(X3,X0) => c_SNoLt(X3,X2))) => ((! [X3] : (c_In(X3,X1) => c_SNoLt(X2,X3))) => (c_Subq(c_SNoLev(c_SNoCut(X0,X1)),c_SNoLev(X2)) & c_SNoEq_5F(c_SNoLev(c_SNoCut(X0,X1)),c_SNoCut(X0,X1),X2)))))))))). % e31de79e7cf55139d68085146942314c9df8e4a33f5cd5c0210d5597df5abf92
fof(c_SNoCut_5FLe,axiom,(! [X0] : (! [X1] : (! [X2] : (! [X3] : (c_SNoCutP(X0,X1) => (c_SNoCutP(X2,X3) => ((! [X4] : (c_In(X4,X0) => c_SNoLt(X4,c_SNoCut(X2,X3)))) => ((! [X4] : (c_In(X4,X3) => c_SNoLt(c_SNoCut(X0,X1),X4))) => c_SNoLe(c_SNoCut(X0,X1),c_SNoCut(X2,X3))))))))))). % 82a3a816b0841a7a0b73886488227426f419a833bf69e9c434c263171deb6131
fof(c_SNoCut_5Fext,axiom,(! [X0] : (! [X1] : (! [X2] : (! [X3] : (c_SNoCutP(X0,X1) => (c_SNoCutP(X2,X3) => ((! [X4] : (c_In(X4,X0) => c_SNoLt(X4,c_SNoCut(X2,X3)))) => ((! [X4] : (c_In(X4,X1) => c_SNoLt(c_SNoCut(X2,X3),X4))) => ((! [X4] : (c_In(X4,X2) => c_SNoLt(X4,c_SNoCut(X0,X1)))) => ((! [X4] : (c_In(X4,X3) => c_SNoLt(c_SNoCut(X0,X1),X4))) => (c_SNoCut(X0,X1) = c_SNoCut(X2,X3))))))))))))). % 0788edd7addced6766367b48c8b84ea4229876e4b4f5dfb5f1c8764be5c0d785
fof(c_SNoL_5FSNoCutP_5Fex,axiom,(! [X0] : (! [X1] : (c_SNoCutP(X0,X1) => (! [X2] : (c_In(X2,c_SNoL(c_SNoCut(X0,X1))) => (? [X3] : (c_In(X3,X0) & c_SNoLe(X2,X3))))))))). % a47ca6334991b18639d78e98e1c1d94a62953f884ec1e0a5678bf51fea7caf44
fof(c_SNoR_5FSNoCutP_5Fex,axiom,(! [X0] : (! [X1] : (c_SNoCutP(X0,X1) => (! [X2] : (c_In(X2,c_SNoR(c_SNoCut(X0,X1))) => (? [X3] : (c_In(X3,X1) & c_SNoLe(X3,X2))))))))). % a29c0f1ec3d14458a4b0ac6ebec560fd2fe602afc845ff6f22f7d93c53002e2c
fof(ordinal_5FSNo_5F,axiom,(! [X0] : (ordinal(X0) => c_SNo_5F(X0,X0)))). % cdef53a4ce934d1c854dc1eea05e945d707294231bbcd3360eef22a232331af6
fof(ordinal_5FSNo,axiom,(! [X0] : (ordinal(X0) => c_SNo(X0)))). % 6afdc162fed382883368bd387c9daaf8b5b27a23e9e1749ce359d06d2525d1b3
fof(ordinal_5FSNoLev,axiom,(! [X0] : (ordinal(X0) => (c_SNoLev(X0) = X0)))). % 44ede44f9f54c62bf399d1bb1b751e91bd9e3bcb799eab8f41ea4896698914db
fof(ordinal_5FSNoLev_5Fmax,axiom,(! [X0] : (ordinal(X0) => (! [X1] : (c_SNo(X1) => (c_In(c_SNoLev(X1),X0) => c_SNoLt(X1,X0))))))). % 026ca7627c4817cb9b704eeace9a23c6e028109172ea917bcc6429fe2ff05c13
fof(ordinal_5FSNoL,axiom,(! [X0] : (ordinal(X0) => (c_SNoL(X0) = c_SNoS_5F(X0))))). % 8d823ad1e617ec80fa1b1db2568883e94eb1c9e1b0095a0fb0ae7f7db4dde967
fof(ordinal_5FSNoR,axiom,(! [X0] : (ordinal(X0) => (c_SNoR(X0) = c_Empty)))). % 7e4e318555459f28aebd28ae28e883fb56182ad83938e606bc0eba941d53ef2f
fof(nat_5Fp_5FSNo,axiom,(! [X0] : (nat_5Fp(X0) => c_SNo(X0)))). % 2ac1aa136404b01e6a45a3a2fbc56f071a8ad744a5c5a75b81020960959f7bff
fof(omega_5FSNo,axiom,(! [X0] : (c_In(X0,omega) => c_SNo(X0)))). % 4db46e69c527658700c8e8d4094e99be3332a20c2cf96d073256ad0c0923280d
fof(omega_5FSNoS_5Fomega,axiom,c_Subq(omega,c_SNoS_5F(omega))). % 6d33626658a4a4bff176c9fc5a8d63a07632084198a79b50c57c309e8cb290eb
fof(ordinal_5FIn_5FSNoLt,axiom,(! [X0] : (ordinal(X0) => (! [X1] : (c_In(X1,X0) => c_SNoLt(X1,X0)))))). % 465965f88e5b6325526aa87f8bce31a2e2456489625957d5a57431830753e04b
fof(ordinal_5FSNoLev_5Fmax_5F2,axiom,(! [X0] : (ordinal(X0) => (! [X1] : (c_SNo(X1) => (c_In(c_SNoLev(X1),ordsucc(X0)) => c_SNoLe(X1,X0))))))). % 1fe4358fe0378b3047dc5d377b687b90557d060eb3433cb433fc6aacba9c89da
fof(ordinal_5FSubq_5FSNoLe,axiom,(! [X0] : (! [X1] : (ordinal(X0) => (ordinal(X1) => (c_Subq(X0,X1) => c_SNoLe(X0,X1))))))). % 83abc3785d6e7d3059b4a191ca04bc227f27e8012aabd967c9c6e6c74c34cc60
fof(ordinal_5FSNoLt_5FIn,axiom,(! [X0] : (! [X1] : (ordinal(X0) => (ordinal(X1) => (c_SNoLt(X0,X1) => c_In(X0,X1))))))). % 0ab4dd6bddbb2c3138b9dd53c39618ecb32b8d81f92c41ed64c472f08e7aed50
fof(omega_5Fnonneg,axiom,(! [X0] : (c_In(X0,omega) => c_SNoLe(c_Empty,X0)))). % 811b09f828140649bc0a8ea290d58cb191e178293d917c8bb2dbd07e3e2f6614
fof(c_SNo_5F0,axiom,c_SNo(c_Empty)). % 6dfb8d5a17ba782c7e754a491898e6a92bd7d657ed37b281156f977019a20522
fof(c_SNo_5F1,axiom,c_SNo(ordsucc(c_Empty))). % 9c3b2441459e801ab1755c20be37f38d1596b7dadbe27d4e50bc4beafb5e3074
fof(c_SNo_5F2,axiom,c_SNo(ordsucc(ordsucc(c_Empty)))). % e294feb06b6142fa0c75cdbed265d96e77d84f1ceb480d3536848cdd00510cfd
fof(c_SNoLev_5F0,axiom,(c_SNoLev(c_Empty) = c_Empty)). % 99a927e455525a9647b14da05ae24eb3287e06ec4957e3647f95443063fdbb77
fof(c_SNoCut_5F0_5F0,axiom,(c_SNoCut(c_Empty,c_Empty) = c_Empty)). % 97c6c6c64f4ecb67e6f2daf0f342eddc466f5b64df4dca9d0bf9103c26cfffad
fof(c_SNoL_5F0,axiom,(c_SNoL(c_Empty) = c_Empty)). % 79e765a76846c3210566ce9d5b6bae92c053395c972a54d3a3a728cf4579e7ec
fof(c_SNoR_5F0,axiom,(c_SNoR(c_Empty) = c_Empty)). % 8590c7bedb0aab3bc93a1006cef7778a9261d0f5a48cd27237c2c4acbc38c627
fof(c_SNoL_5F1,axiom,(c_SNoL(ordsucc(c_Empty)) = ordsucc(c_Empty))). % af01ba3982914cb9a8de39720a9197b6bf1df85c72fd34fbfb1c89a02bac5eae
fof(c_SNoR_5F1,axiom,(c_SNoR(ordsucc(c_Empty)) = c_Empty)). % fa8a68d5dfb20cb2c5ff6a662640f5d7c0359cfe3e7cceb9221e83401ca280a4
fof(c_SNo_5Fmax_5FSNoLev,axiom,(! [X0] : (c_SNo(X0) => ((! [X1] : (c_In(X1,c_SNoS_5F(c_SNoLev(X0))) => c_SNoLt(X1,X0))) => (c_SNoLev(X0) = X0))))). % cdf05a00ded204b8d5108be8d85dc82cf0e566a000208a8bb132da59e037873d
fof(c_SNo_5Fmax_5Fordinal,axiom,(! [X0] : (c_SNo(X0) => ((! [X1] : (c_In(X1,c_SNoS_5F(c_SNoLev(X0))) => c_SNoLt(X1,X0))) => ordinal(X0))))). % b1d76aacbc7e47448d9367e0d51f5709dc819c051b4f086783d3c62e446c6839
fof(pos_5Flow_5Feq_5Fone,axiom,(! [X0] : (c_SNo(X0) => (c_SNoLt(c_Empty,X0) => (c_Subq(c_SNoLev(X0),ordsucc(c_Empty)) => (X0 = ordsucc(c_Empty))))))). % ed6fa2612031c233f73ec003c65e8c4b1030000b016df0d356929c73717c257a
fof(c_SNo_5Fextend0_5FSNo_5F,axiom,(! [X0] : (c_SNo(X0) => c_SNo_5F(ordsucc(c_SNoLev(X0)),c_SNo_5Fextend0(X0))))). % fef25aeef23d261d035dfacfeff93368e62c4a7ddda4cfb4741d65ea37a2107d
fof(c_SNo_5Fextend1_5FSNo_5F,axiom,(! [X0] : (c_SNo(X0) => c_SNo_5F(ordsucc(c_SNoLev(X0)),c_SNo_5Fextend1(X0))))). % 44989ac43b56bc8e7c4ce5fdedbd25d27322e5b0c8d3440859aa5559ccd54269
fof(c_SNo_5Fextend0_5FSNo,axiom,(! [X0] : (c_SNo(X0) => c_SNo(c_SNo_5Fextend0(X0))))). % b6a2dded101e3f2f16bcb078c91ce460768d53f90698e32862e62f3a4a900dd4
fof(c_SNo_5Fextend1_5FSNo,axiom,(! [X0] : (c_SNo(X0) => c_SNo(c_SNo_5Fextend1(X0))))). % 3b2267323d57ac2088d7c93dc2ace6961c405473f62cbfcb65bb567bd7642df8
fof(c_SNo_5Fextend0_5FSNoLev,axiom,(! [X0] : (c_SNo(X0) => (c_SNoLev(c_SNo_5Fextend0(X0)) = ordsucc(c_SNoLev(X0)))))). % 3669e75c41ab4cf81723929a0d6067b65d1a5a3a49aaeda2b974c5a172cb7970
fof(c_SNo_5Fextend1_5FSNoLev,axiom,(! [X0] : (c_SNo(X0) => (c_SNoLev(c_SNo_5Fextend1(X0)) = ordsucc(c_SNoLev(X0)))))). % 6aea3176b270ffa6a214c90cd4298e9992df86d81e41a79d66eac6141a7b464c
fof(c_SNo_5Fextend0_5FnIn,axiom,(! [X0] : (c_SNo(X0) => nIn(c_SNoLev(X0),c_SNo_5Fextend0(X0))))). % 9836d4e2244e04cf3524268487274764d4ef2f2a69a8ed1a8c2cc28e1f38bab2
fof(c_SNo_5Fextend1_5FIn,axiom,(! [X0] : (c_SNo(X0) => c_In(c_SNoLev(X0),c_SNo_5Fextend1(X0))))). % 87133378942c010bc557995c7271932aa37d540657d5326563c05aba70834249
fof(c_SNo_5Fextend0_5FSNoEq,axiom,(! [X0] : (c_SNo(X0) => c_SNoEq_5F(c_SNoLev(X0),c_SNo_5Fextend0(X0),X0)))). % ffabe30821c305f07a517c4e8ee012976edc1e421cec26d3d66149c5b36a5171
fof(c_SNo_5Fextend1_5FSNoEq,axiom,(! [X0] : (c_SNo(X0) => c_SNoEq_5F(c_SNoLev(X0),c_SNo_5Fextend1(X0),X0)))). % d4c1e61d138ed7f77b261805aa96926d31e4354e74950fbe01dab1eb180340a2
fof(c_SNoLev_5F0_5Feq_5F0,axiom,(! [X0] : (c_SNo(X0) => ((c_SNoLev(X0) = c_Empty) => (X0 = c_Empty))))). % cf450d97f4cddd3515ed72f191f90b6056355ee584c83b0a425668fa97388b57
fof(eps_5Fordinal_5FIn_5Feq_5F0,axiom,(! [X0] : (! [X1] : (ordinal(X1) => (c_In(X1,eps_5F(X0)) => (X1 = c_Empty)))))). % 0eeb608768de70c1a6488a66fc07fa14a2266e2c49e854784fb131c89fd4d1ee
fof(eps_5F0_5F1,axiom,(eps_5F(c_Empty) = ordsucc(c_Empty))). % 4450114bd8fd1f52bc30eb38b25332a9c49582f4d0b15ac9594e6861f91dca1e
fof(c_SNo_5F_5Feps_5F,axiom,(! [X0] : (c_In(X0,omega) => c_SNo_5F(ordsucc(X0),eps_5F(X0))))). % e0fa2176fdae121e3d9092553ea61b60ba6f57aa1386d22c4ad38934768f72f8
fof(c_SNo_5Feps_5F,axiom,(! [X0] : (c_In(X0,omega) => c_SNo(eps_5F(X0))))). % bad8d3abde1059b5d5a897709f01b01990ccbd33f061ef50ca87baa3c919b810
fof(c_SNo_5Feps_5F1,axiom,c_SNo(eps_5F(ordsucc(c_Empty)))). % acc1fde9b5c32690fd0f37b266431aa75dcfc4bc0c96ce019ab9cb8986d69d12
fof(c_SNoLev_5Feps_5F,axiom,(! [X0] : (c_In(X0,omega) => (c_SNoLev(eps_5F(X0)) = ordsucc(X0))))). % ccef402c6c4586f8aa02d7c907de601583bc7ba976500b43c510abff29c7f4b3
fof(c_SNo_5Feps_5FSNoS_5Fomega,axiom,(! [X0] : (c_In(X0,omega) => c_In(eps_5F(X0),c_SNoS_5F(omega))))). % f8e000c80f123a7847ac12cdb3aa15a3ea1ad70430bae7bc57842a3baeba7288
fof(c_SNo_5Feps_5Fdecr,axiom,(! [X0] : (c_In(X0,omega) => (! [X1] : (c_In(X1,X0) => c_SNoLt(eps_5F(X0),eps_5F(X1))))))). % a51c462fc90941afde8a0803eef6045b68b208ab7c044c2f0295842922322000
fof(c_SNo_5Feps_5Fpos,axiom,(! [X0] : (c_In(X0,omega) => c_SNoLt(c_Empty,eps_5F(X0))))). % 0b490342ca66792c71340524f1aa07719c0c07289d2d56aaae97eb838f5cacd6
fof(c_SNo_5Fpos_5Feps_5FLt,axiom,(! [X0] : (nat_5Fp(X0) => (! [X1] : (c_In(X1,c_SNoS_5F(ordsucc(X0))) => (c_SNoLt(c_Empty,X1) => c_SNoLt(eps_5F(X0),X1))))))). % 22bd50a50f0d9f44c932634deec60285b5efb2d4606653500ebf9a4e3b8de83d
fof(c_SNo_5Fpos_5Feps_5FLe,axiom,(! [X0] : (nat_5Fp(X0) => (! [X1] : (c_In(X1,c_SNoS_5F(ordsucc(ordsucc(X0)))) => (c_SNoLt(c_Empty,X1) => c_SNoLe(eps_5F(X0),X1))))))). % 8fa70e5fde9407a4e39f6abdf9d08b2d42fbabbc5184dab14e3821a3570acbef
fof(eps_5FSNo_5Feq,axiom,(! [X0] : (nat_5Fp(X0) => (! [X1] : (c_In(X1,c_SNoS_5F(ordsucc(X0))) => (c_SNoLt(c_Empty,X1) => (c_SNoEq_5F(c_SNoLev(X1),eps_5F(X0),X1) => (? [X2] : (c_In(X2,X0) & (X1 = eps_5F(X2))))))))))). % 4eaa8ef92e10751d83ef42571a03f059cc34533c7c5d755128bbd54989d74f46
fof(c_SNo_5Fomega,axiom,c_SNo(omega)). % 25813a1e615fbdc44e13fe144cc5ef235cf3e3a9b2e0625ec44d2cf3edea2f4c
fof(c_SNoLt_5F0_5F1,axiom,c_SNoLt(c_Empty,ordsucc(c_Empty))). % dd5b1c1b26f377cf8c7522889c2309802b8ad9145c68c3e332e44365f37ada4c
fof(c_SNoLt_5F0_5F2,axiom,c_SNoLt(c_Empty,ordsucc(ordsucc(c_Empty)))). % c4a336580396d372e4b6d61f7434e8cd5f52b05d83a883996ce39b4bf107f6dd
fof(c_SNoLt_5F1_5F2,axiom,c_SNoLt(ordsucc(c_Empty),ordsucc(ordsucc(c_Empty)))). % 71747d7a4865b720092fdd99741f28bef0ef622820336142524ad08ac800e682
fof(restr_5FSNo_5F,axiom,(! [X0] : (c_SNo(X0) => (! [X1] : (c_In(X1,c_SNoLev(X0)) => c_SNo_5F(X1,binintersect(X0,c_SNoElts_5F(X1)))))))). % 8f1d48e10c7e94943b31be44d4a4009c51b4e492170ee9bf7f3085a066c556d1
fof(restr_5FSNo,axiom,(! [X0] : (c_SNo(X0) => (! [X1] : (c_In(X1,c_SNoLev(X0)) => c_SNo(binintersect(X0,c_SNoElts_5F(X1)))))))). % 3acb346ab27b9826a616730f87f1a711568d2cc3ab03c1a418d417557466bdc5
fof(restr_5FSNoLev,axiom,(! [X0] : (c_SNo(X0) => (! [X1] : (c_In(X1,c_SNoLev(X0)) => (c_SNoLev(binintersect(X0,c_SNoElts_5F(X1))) = X1)))))). % cc9258d054b6c568e8d39d5a6a81aa512b31fdb24061f7e3a4f9e0a7e99a2f64
fof(restr_5FSNoEq,axiom,(! [X0] : (c_SNo(X0) => (! [X1] : (c_In(X1,c_SNoLev(X0)) => c_SNoEq_5F(X1,binintersect(X0,c_SNoElts_5F(X1)),X0)))))). % 1bbfcbdc71210669c4c1b09c8ab17dee6be28c2debeb2433a33f73b8af865057
fof(c_SNo_5Fextend0_5Frestr_5Feq,axiom,(! [X0] : (c_SNo(X0) => (X0 = binintersect(c_SNo_5Fextend0(X0),c_SNoElts_5F(c_SNoLev(X0))))))). % 4ce2932b395693b2772a1097c96e74eaaaa6a06bf1bd5099c052bcaaeb6fc459
fof(c_SNo_5Fextend1_5Frestr_5Feq,axiom,(! [X0] : (c_SNo(X0) => (X0 = binintersect(c_SNo_5Fextend1(X0),c_SNoElts_5F(c_SNoLev(X0))))))). % c43f3b0d6bc33d6172fb6886b4e0a29425fdad7e40b386ef9431ed67a3c08c09
fof(c_SNo_5Fminus_5FSNo,axiom,(! [X0] : (c_SNo(X0) => c_SNo(minus_5FSNo(X0))))). % 5fc6b424fa17791172da437df8be1755f600b86002fd5d0270e07122f49bdcc0
fof(minus_5FSNo_5FLt_5Fcontra,axiom,(! [X0] : (! [X1] : (c_SNo(X0) => (c_SNo(X1) => (c_SNoLt(X0,X1) => c_SNoLt(minus_5FSNo(X1),minus_5FSNo(X0)))))))). % ec6933f4cb503e850dcd1f504380d69ed1c379cd12018438810d19adf8999167
fof(minus_5FSNo_5FLe_5Fcontra,axiom,(! [X0] : (! [X1] : (c_SNo(X0) => (c_SNo(X1) => (c_SNoLe(X0,X1) => c_SNoLe(minus_5FSNo(X1),minus_5FSNo(X0)))))))). % 682d29f0d7a4cdc87c42e3e05882c73c15d251ea581b052c2a5d11013d2bcdee
fof(minus_5FSNo_5FLev_5Flem1,axiom,(! [X0] : (ordinal(X0) => (! [X1] : (c_In(X1,c_SNoS_5F(X0)) => c_Subq(c_SNoLev(minus_5FSNo(X1)),c_SNoLev(X1))))))). % 25606447d2092e488105b00bc91d94c30231f6c4769b3b052fbd90450f3d36e0
fof(minus_5FSNo_5FLev_5Flem2,axiom,(! [X0] : (c_SNo(X0) => c_Subq(c_SNoLev(minus_5FSNo(X0)),c_SNoLev(X0))))). % 41a09b63ff81c80af766b7e2b8195b037cd8d40171d79a4d6f42c907652d1b0e
fof(minus_5FSNo_5Finvol,axiom,(! [X0] : (c_SNo(X0) => (minus_5FSNo(minus_5FSNo(X0)) = X0)))). % a2228d8879267f1dd4f30002bcf4afe0ddf7c0c48c6946b256c77e83e3d9a4a5
fof(minus_5FSNo_5FLev,axiom,(! [X0] : (c_SNo(X0) => (c_SNoLev(minus_5FSNo(X0)) = c_SNoLev(X0))))). % 1df9aae6d40286e3dfad11fbb5211cade26dc1f1c7df779c5387b1b89bc860a4
fof(minus_5FSNo_5FSNo_5F,axiom,(! [X0] : (ordinal(X0) => (! [X1] : (c_SNo_5F(X0,X1) => c_SNo_5F(X0,minus_5FSNo(X1))))))). % d6520d06c1c2ec741ec70e297b69bc5935729504982c3e82ad10e2095173796a
fof(minus_5FSNo_5FSNoS_5F,axiom,(! [X0] : (ordinal(X0) => (! [X1] : (c_In(X1,c_SNoS_5F(X0)) => c_In(minus_5FSNo(X1),c_SNoS_5F(X0))))))). % 5401ebf619ada9e9c5df57551325cf0e0e1f721da8edbf367c87ec9687083c6b
fof(minus_5FSNo_5FLt_5Fcontra1,axiom,(! [X0] : (! [X1] : (c_SNo(X0) => (c_SNo(X1) => (c_SNoLt(minus_5FSNo(X0),X1) => c_SNoLt(minus_5FSNo(X1),X0))))))). % 8be3042fca19823ba47809faf25b877ca38eead705765ea87ec38fa54f01022e
fof(minus_5FSNo_5FLt_5Fcontra2,axiom,(! [X0] : (! [X1] : (c_SNo(X0) => (c_SNo(X1) => (c_SNoLt(X0,minus_5FSNo(X1)) => c_SNoLt(X1,minus_5FSNo(X0)))))))). % d65517fd522fe7b3d6314bb71592ae3ee8a828d6d569a8eff7966da2b729661b
fof(mordinal_5FSNoLev_5Fmin_5F2,axiom,(! [X0] : (ordinal(X0) => (! [X1] : (c_SNo(X1) => (c_In(c_SNoLev(X1),ordsucc(X0)) => c_SNoLe(minus_5FSNo(X0),X1))))))). % 76e0882b8d62649d311868302527966fbdef020e1a46774d8b95fa21c80c5c66
fof(minus_5FSNo_5FSNoS_5Fomega,axiom,(! [X0] : (c_In(X0,c_SNoS_5F(omega)) => c_In(minus_5FSNo(X0),c_SNoS_5F(omega))))). % c1b37e4f20f8dbe985cd74fc20d56b1175fba702fccd3d6ed6949856bda10b27
fof(c_SNo_5Fadd_5FSNo,axiom,(! [X0] : (! [X1] : (c_SNo(X0) => (c_SNo(X1) => c_SNo(add_5FSNo(X0,X1))))))). % 6aafd837e0a0618c37ad12fb26684a5921d44547ba020d3625be2de433b8e029
fof(c_SNo_5Fadd_5FSNo_5F3,axiom,(! [X0] : (! [X1] : (! [X2] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => c_SNo(add_5FSNo(X0,add_5FSNo(X1,X2)))))))))). % ec060afb75068cb06797af886cc3372b17752e09add15bafe34c6f6591697089
fof(c_SNo_5Fadd_5FSNo_5F3c,axiom,(! [X0] : (! [X1] : (! [X2] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => c_SNo(add_5FSNo(X0,add_5FSNo(X1,minus_5FSNo(X2))))))))))). % 30b881ecd6c7983aad6ff1f597cb168ad9c1dad82ecde2f2eb5d529e96ca8096
fof(c_SNo_5Fadd_5FSNo_5F4,axiom,(! [X0] : (! [X1] : (! [X2] : (! [X3] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (c_SNo(X3) => c_SNo(add_5FSNo(X0,add_5FSNo(X1,add_5FSNo(X2,X3))))))))))))). % 0b0d8df3e9b66c26851601036f3c06b82efb4a8522fec7734fdc616e2d96a258
fof(add_5FSNo_5FLt1,axiom,(! [X0] : (! [X1] : (! [X2] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (c_SNoLt(X0,X2) => c_SNoLt(add_5FSNo(X0,X1),add_5FSNo(X2,X1)))))))))). % ade9d7b33e343a927d553210e3e19745855dff428b44d08a783afd6b1e189b64
fof(add_5FSNo_5FLe1,axiom,(! [X0] : (! [X1] : (! [X2] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (c_SNoLe(X0,X2) => c_SNoLe(add_5FSNo(X0,X1),add_5FSNo(X2,X1)))))))))). % 9f2dbcf458723b5299ff820bb44bff18592c9b16d511f3f8647d7b672a83577d
fof(add_5FSNo_5FLt2,axiom,(! [X0] : (! [X1] : (! [X2] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (c_SNoLt(X1,X2) => c_SNoLt(add_5FSNo(X0,X1),add_5FSNo(X0,X2)))))))))). % 759677c45b73afd86fabc4bad7c0696b368b58d51666f9534c48fc051c8de801
fof(add_5FSNo_5FLe2,axiom,(! [X0] : (! [X1] : (! [X2] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (c_SNoLe(X1,X2) => c_SNoLe(add_5FSNo(X0,X1),add_5FSNo(X0,X2)))))))))). % cb25b3d8c88f9f70b4db9ced1d6985375eaf2125446f415a95a6ec386514c61e
fof(add_5FSNo_5FLt3a,axiom,(! [X0] : (! [X1] : (! [X2] : (! [X3] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (c_SNo(X3) => (c_SNoLt(X0,X2) => (c_SNoLe(X1,X3) => c_SNoLt(add_5FSNo(X0,X1),add_5FSNo(X2,X3))))))))))))). % 90ed31d2ce84dc27cf0305b845de7897e98e3a277a157017d5ec97701d3b9866
fof(add_5FSNo_5FLt3b,axiom,(! [X0] : (! [X1] : (! [X2] : (! [X3] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (c_SNo(X3) => (c_SNoLe(X0,X2) => (c_SNoLt(X1,X3) => c_SNoLt(add_5FSNo(X0,X1),add_5FSNo(X2,X3))))))))))))). % 184e2f41b80c0c2370762803a93c384184fb141850a4fed7ffc14fc84496d434
fof(add_5FSNo_5FLt3,axiom,(! [X0] : (! [X1] : (! [X2] : (! [X3] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (c_SNo(X3) => (c_SNoLt(X0,X2) => (c_SNoLt(X1,X3) => c_SNoLt(add_5FSNo(X0,X1),add_5FSNo(X2,X3))))))))))))). % 36349186ebba11c379d6db9201c7f98c5d7b6480161300e077db4afff07ac5ba
fof(add_5FSNo_5FLe3,axiom,(! [X0] : (! [X1] : (! [X2] : (! [X3] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (c_SNo(X3) => (c_SNoLe(X0,X2) => (c_SNoLe(X1,X3) => c_SNoLe(add_5FSNo(X0,X1),add_5FSNo(X2,X3))))))))))))). % 7aad2f3f16b3d75fd2b5fc4a98612f11d8de4bb6a98d2884eb56b0e57d10e58e
fof(add_5FSNo_5Fcom,axiom,(! [X0] : (! [X1] : (c_SNo(X0) => (c_SNo(X1) => (add_5FSNo(X0,X1) = add_5FSNo(X1,X0))))))). % ccbcc874643c8e73c8e68259a58ad308dbec318a0d9b3dee2c2d0b79d6c6c46c
fof(add_5FSNo_5F0L,axiom,(! [X0] : (c_SNo(X0) => (add_5FSNo(c_Empty,X0) = X0)))). % f113ad14494e14757c38a92f369aa38e4e5699681152b547dcf66fe6889a2776
fof(add_5FSNo_5F0R,axiom,(! [X0] : (c_SNo(X0) => (add_5FSNo(X0,c_Empty) = X0)))). % 75b04e11158df96fb891cbff4ded4c33fe9b6861265d0f11da3175ebf863d5d0
fof(add_5FSNo_5Fminus_5FSNo_5Flinv,axiom,(! [X0] : (c_SNo(X0) => (add_5FSNo(minus_5FSNo(X0),X0) = c_Empty)))). % 97c4bd2d5316d0c2d2950caf9a25ee0ab4592cec378fa89d33d632d35dc6a192
fof(add_5FSNo_5Fminus_5FSNo_5Frinv,axiom,(! [X0] : (c_SNo(X0) => (add_5FSNo(X0,minus_5FSNo(X0)) = c_Empty)))). % 59d0f33e810cd3043e3b9d65e50a2a24bac520c0e6b11cf9d7b9faac53876900
fof(add_5FSNo_5Fordinal_5Fordinal,axiom,(! [X0] : (ordinal(X0) => (! [X1] : (ordinal(X1) => ordinal(add_5FSNo(X0,X1))))))). % 60f71e925f0d1fc58f64eafd37767c017e0a62c122bd439dc588c15ebd18f83a
fof(add_5FSNo_5Fordinal_5FSL,axiom,(! [X0] : (ordinal(X0) => (! [X1] : (ordinal(X1) => (add_5FSNo(ordsucc(X0),X1) = ordsucc(add_5FSNo(X0,X1)))))))). % f34bdfef50c56a7c47292994360b8d859866260dac4f981e5b8c368596868cbc
fof(add_5FSNo_5Fordinal_5FSR,axiom,(! [X0] : (ordinal(X0) => (! [X1] : (ordinal(X1) => (add_5FSNo(X0,ordsucc(X1)) = ordsucc(add_5FSNo(X0,X1)))))))). % 87a52e664d08deba5ddb24c4f31709a0b959b7bc6f1266dc67ec80c4f5a7219a
fof(add_5FSNo_5Fordinal_5FInL,axiom,(! [X0] : (ordinal(X0) => (! [X1] : (ordinal(X1) => (! [X2] : (c_In(X2,X0) => c_In(add_5FSNo(X2,X1),add_5FSNo(X0,X1))))))))). % 30498eefc872dd11feaecd0698cbdd1d4ee272b107885dbacdfa1d9a8f4aa34a
fof(add_5FSNo_5Fordinal_5FInR,axiom,(! [X0] : (ordinal(X0) => (! [X1] : (ordinal(X1) => (! [X2] : (c_In(X2,X1) => c_In(add_5FSNo(X0,X2),add_5FSNo(X0,X1))))))))). % cb41598d464d2534b088282da886d80fbf746ee86602aa72d5875f47f4a5cdbd
fof(add_5Fnat_5Fadd_5FSNo,axiom,(! [X0] : (c_In(X0,omega) => (! [X1] : (c_In(X1,omega) => (add_5Fnat(X0,X1) = add_5FSNo(X0,X1))))))). % 12436e1c95e6f14b80c42e1b8e0313dd4ff933bffc960dd67e8b6f0f2cc6617a
fof(add_5FSNo_5FIn_5Fomega,axiom,(! [X0] : (c_In(X0,omega) => (! [X1] : (c_In(X1,omega) => c_In(add_5FSNo(X0,X1),omega)))))). % 16765f75ba8cbee474cc065884a78870fac79d92f5a1ab0168046f9d45a69a5e
fof(add_5FSNo_5F1_5F1_5F2,axiom,(add_5FSNo(ordsucc(c_Empty),ordsucc(c_Empty)) = ordsucc(ordsucc(c_Empty)))). % d45e045365f4d8b41e28ee5af34f3ff9684523dc81a6ff285b6209d4ff5ec2e4
fof(add_5FSNo_5FSNoL_5Finterpolate,axiom,(! [X0] : (! [X1] : (c_SNo(X0) => (c_SNo(X1) => (! [X2] : (c_In(X2,c_SNoL(add_5FSNo(X0,X1))) => ((? [X3] : (c_In(X3,c_SNoL(X0)) & c_SNoLe(X2,add_5FSNo(X3,X1)))) | (? [X3] : (c_In(X3,c_SNoL(X1)) & c_SNoLe(X2,add_5FSNo(X0,X3)))))))))))). % bdd01cdc104724d84ff4e49ed1f72238e24799c6ed4d4d2081dec9b92458697f
fof(add_5FSNo_5FSNoR_5Finterpolate,axiom,(! [X0] : (! [X1] : (c_SNo(X0) => (c_SNo(X1) => (! [X2] : (c_In(X2,c_SNoR(add_5FSNo(X0,X1))) => ((? [X3] : (c_In(X3,c_SNoR(X0)) & c_SNoLe(add_5FSNo(X3,X1),X2))) | (? [X3] : (c_In(X3,c_SNoR(X1)) & c_SNoLe(add_5FSNo(X0,X3),X2))))))))))). % 850cf64ddb35b184077a5faabf3fc5780695426d3a9b776d607ee7b74a29a6dc
fof(add_5FSNo_5Fassoc,axiom,(! [X0] : (! [X1] : (! [X2] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (add_5FSNo(X0,add_5FSNo(X1,X2)) = add_5FSNo(add_5FSNo(X0,X1),X2))))))))). % 76f099f33692024e90cb89dcbb03e003f04277f24d2999f8188e23a53916de1e
fof(add_5FSNo_5Fminus_5FR2,axiom,(! [X0] : (! [X1] : (c_SNo(X0) => (c_SNo(X1) => (add_5FSNo(add_5FSNo(X0,X1),minus_5FSNo(X1)) = X0)))))). % 209612e11c97bd6f5b275877870242dcbff7d55d5cdccc8d5be631d04fb9798a
fof(add_5FSNo_5Fminus_5FR2_27,axiom,(! [X0] : (! [X1] : (c_SNo(X0) => (c_SNo(X1) => (add_5FSNo(add_5FSNo(X0,minus_5FSNo(X1)),X1) = X0)))))). % f70a9a28cbb959e1050eedd609e31869363aa211d4e662f918a7e25f2c7fb725
fof(add_5FSNo_5Fminus_5FL2,axiom,(! [X0] : (! [X1] : (c_SNo(X0) => (c_SNo(X1) => (add_5FSNo(minus_5FSNo(X0),add_5FSNo(X0,X1)) = X1)))))). % 59fa30fc43c7d7cd6ceb15f964f2605ea43373287dd79fc6ae173423370d3f1b
fof(add_5FSNo_5Fminus_5FL2_27,axiom,(! [X0] : (! [X1] : (c_SNo(X0) => (c_SNo(X1) => (add_5FSNo(X0,add_5FSNo(minus_5FSNo(X0),X1)) = X1)))))). % c4340a7e55c5c7ed0af5ff893e19e157692b6e5d9c7c283a680b6a515ce1bc20
fof(add_5FSNo_5Fcancel_5FL,axiom,(! [X0] : (! [X1] : (! [X2] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => ((add_5FSNo(X0,X1) = add_5FSNo(X0,X2)) => (X1 = X2))))))))). % 3f9f0821c9c0345a8ac0542c7724549fd6f110a6c49b60b21e47a6f79ed69c2c
fof(add_5FSNo_5Fcancel_5FR,axiom,(! [X0] : (! [X1] : (! [X2] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => ((add_5FSNo(X0,X1) = add_5FSNo(X2,X1)) => (X0 = X2))))))))). % 5e9470b73019d823740d4eb87c633d33cdae8157bde2a55539ce42450d9b156a
fof(minus_5FSNo_5F0,axiom,(minus_5FSNo(c_Empty) = c_Empty)). % 6e45a13829da3ab409078fa3274743887c25871b3ac238dcd7d2d4d532a6ee40
fof(minus_5Fadd_5FSNo_5Fdistr,axiom,(! [X0] : (! [X1] : (c_SNo(X0) => (c_SNo(X1) => (minus_5FSNo(add_5FSNo(X0,X1)) = add_5FSNo(minus_5FSNo(X0),minus_5FSNo(X1)))))))). % 715e4a0cc34884475d28d3454883a9c62b1096a49aa5ecdc7e11df3e08505b1f
fof(minus_5Fadd_5FSNo_5Fdistr_5F3,axiom,(! [X0] : (! [X1] : (! [X2] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (minus_5FSNo(add_5FSNo(X0,add_5FSNo(X1,X2))) = add_5FSNo(minus_5FSNo(X0),add_5FSNo(minus_5FSNo(X1),minus_5FSNo(X2))))))))))). % 623ca84d0796d46b97fa3d8a9135efac57b91d45a162c594c9f1548b9f65a9d5
fof(add_5FSNo_5FLev_5Fbd,axiom,(! [X0] : (! [X1] : (c_SNo(X0) => (c_SNo(X1) => c_Subq(c_SNoLev(add_5FSNo(X0,X1)),add_5FSNo(c_SNoLev(X0),c_SNoLev(X1)))))))). % 10936c9f043816b125348f293e5324cc07ae6f944ed92e3b2a985b9d174d26ea
fof(add_5FSNo_5FSNoS_5Fomega,axiom,(! [X0] : (c_In(X0,c_SNoS_5F(omega)) => (! [X1] : (c_In(X1,c_SNoS_5F(omega)) => c_In(add_5FSNo(X0,X1),c_SNoS_5F(omega))))))). % b6e57b081c34853a5ec3d08e48b6df5445989e557765d3cb7d73195c67c6ee83
fof(add_5FSNo_5FLt1_5Fcancel,axiom,(! [X0] : (! [X1] : (! [X2] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (c_SNoLt(add_5FSNo(X0,X1),add_5FSNo(X2,X1)) => c_SNoLt(X0,X2))))))))). % 509597d410f559441deffaf476f1ef8ea0b3a2281387fc53446b21d897076c32
fof(add_5FSNo_5FLt2_5Fcancel,axiom,(! [X0] : (! [X1] : (! [X2] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (c_SNoLt(add_5FSNo(X0,X1),add_5FSNo(X0,X2)) => c_SNoLt(X1,X2))))))))). % 4884e797f38db54192a65cc6777bbe130ea8235f3e2421355447c0c121ad52af
fof(add_5FSNo_5FLe1_5Fcancel,axiom,(! [X0] : (! [X1] : (! [X2] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (c_SNoLe(add_5FSNo(X0,X1),add_5FSNo(X2,X1)) => c_SNoLe(X0,X2))))))))). % 82160a0836c825a662bf27e3e7e8c1ddfb286314f0c43c724ac0c952980d75cb
fof(add_5FSNo_5Fassoc_5F4,axiom,(! [X0] : (! [X1] : (! [X2] : (! [X3] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (c_SNo(X3) => (add_5FSNo(X0,add_5FSNo(X1,add_5FSNo(X2,X3))) = add_5FSNo(add_5FSNo(X0,add_5FSNo(X1,X2)),X3))))))))))). % de09a7230aace5365d271e78f0190859498152ab2301afaf71a6c6b2a13a6d4d
fof(add_5FSNo_5Fcom_5F3_5F0_5F1,axiom,(! [X0] : (! [X1] : (! [X2] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (add_5FSNo(X0,add_5FSNo(X1,X2)) = add_5FSNo(X1,add_5FSNo(X0,X2)))))))))). % 57619e0ef041e8687b697d9d5c2482e840430d6c4ad52227e8040bb0d8f7cc63
fof(add_5FSNo_5Fcom_5F3b_5F1_5F2,axiom,(! [X0] : (! [X1] : (! [X2] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (add_5FSNo(add_5FSNo(X0,X1),X2) = add_5FSNo(add_5FSNo(X0,X2),X1))))))))). % c5e1bd4f6de5cb2c6cb2a8b2f98d8f16bf6f1489e0eec573be348f115f0104db
fof(add_5FSNo_5Fcom_5F4_5Finner_5Fmid,axiom,(! [X0] : (! [X1] : (! [X2] : (! [X3] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (c_SNo(X3) => (add_5FSNo(add_5FSNo(X0,X1),add_5FSNo(X2,X3)) = add_5FSNo(add_5FSNo(X0,X2),add_5FSNo(X1,X3)))))))))))). % 1ac1c52f6a378e7baf6f332b0c70bb0f22999a5eb3d512f775e821aa7983c5be
fof(add_5FSNo_5Frotate_5F3_5F1,axiom,(! [X0] : (! [X1] : (! [X2] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (add_5FSNo(X0,add_5FSNo(X1,X2)) = add_5FSNo(X2,add_5FSNo(X0,X1)))))))))). % ff769d066e27caccec068affd0245edc54a4d22872f86b01a2da7fd24ea23af5
fof(add_5FSNo_5Frotate_5F4_5F1,axiom,(! [X0] : (! [X1] : (! [X2] : (! [X3] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (c_SNo(X3) => (add_5FSNo(X0,add_5FSNo(X1,add_5FSNo(X2,X3))) = add_5FSNo(X3,add_5FSNo(X0,add_5FSNo(X1,X2))))))))))))). % 09517946bd1c666c42f471a62f112d3eaed806a28ac9f546fcbed16ce9f18cc3
fof(add_5FSNo_5Frotate_5F5_5F1,axiom,(! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (c_SNo(X3) => (c_SNo(X4) => (add_5FSNo(X0,add_5FSNo(X1,add_5FSNo(X2,add_5FSNo(X3,X4)))) = add_5FSNo(X4,add_5FSNo(X0,add_5FSNo(X1,add_5FSNo(X2,X3)))))))))))))))). % 8ef2be266f829e413e0482994d0a69fd0594e6de981f07877ade48477c9a578c
fof(add_5FSNo_5Frotate_5F5_5F2,axiom,(! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (c_SNo(X3) => (c_SNo(X4) => (add_5FSNo(X0,add_5FSNo(X1,add_5FSNo(X2,add_5FSNo(X3,X4)))) = add_5FSNo(X3,add_5FSNo(X4,add_5FSNo(X0,add_5FSNo(X1,X2)))))))))))))))). % da9ad7113f2b7f908213d0399e207ea670599a58a6897b622978d16b2e32ea7c
fof(add_5FSNo_5Fminus_5FSNo_5Fprop2,axiom,(! [X0] : (! [X1] : (c_SNo(X0) => (c_SNo(X1) => (add_5FSNo(X0,add_5FSNo(minus_5FSNo(X0),X1)) = X1)))))). % c4340a7e55c5c7ed0af5ff893e19e157692b6e5d9c7c283a680b6a515ce1bc20
fof(add_5FSNo_5Fminus_5FSNo_5Fprop3,axiom,(! [X0] : (! [X1] : (! [X2] : (! [X3] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (c_SNo(X3) => (add_5FSNo(add_5FSNo(X0,add_5FSNo(X1,X2)),add_5FSNo(minus_5FSNo(X2),X3)) = add_5FSNo(X0,add_5FSNo(X1,X3)))))))))))). % ebc792d9d917af320f9ede3a672b8cb69614b093c05ec153f7b300e48db93046
fof(add_5FSNo_5Fminus_5FSNo_5Fprop5,axiom,(! [X0] : (! [X1] : (! [X2] : (! [X3] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (c_SNo(X3) => (add_5FSNo(add_5FSNo(X0,add_5FSNo(X1,minus_5FSNo(X2))),add_5FSNo(X2,X3)) = add_5FSNo(X0,add_5FSNo(X1,X3)))))))))))). % aef870c2f823dd46e7e79d2b31ce756fbdde911fb1f531671f99ed9c4b35a5ef
fof(add_5FSNo_5Fminus_5FLt1,axiom,(! [X0] : (! [X1] : (! [X2] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (c_SNoLt(add_5FSNo(X0,minus_5FSNo(X1)),X2) => c_SNoLt(X0,add_5FSNo(X2,X1)))))))))). % 9c9e775566c0273dc23894851e4b4521314249c1ef39e67c68929d3ab11d3b0f
fof(add_5FSNo_5Fminus_5FLt2,axiom,(! [X0] : (! [X1] : (! [X2] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (c_SNoLt(X2,add_5FSNo(X0,minus_5FSNo(X1))) => c_SNoLt(add_5FSNo(X2,X1),X0))))))))). % f8859ecf5278e98fe0cfd737f26b1eac748f6868ace4ee143d48d5777e087751
fof(add_5FSNo_5Fminus_5FLt1b,axiom,(! [X0] : (! [X1] : (! [X2] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (c_SNoLt(X0,add_5FSNo(X2,X1)) => c_SNoLt(add_5FSNo(X0,minus_5FSNo(X1)),X2))))))))). % 2a7bc1eb055a0b8c935246573c8a9e2312c6d036343562993fc0fcb06c3bce5e
fof(add_5FSNo_5Fminus_5FLt2b,axiom,(! [X0] : (! [X1] : (! [X2] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (c_SNoLt(add_5FSNo(X2,X1),X0) => c_SNoLt(X2,add_5FSNo(X0,minus_5FSNo(X1))))))))))). % 6fe490efc04857edf0391a3a1a521fe46ef55b0693eeed2292a75a8b17d9b731
fof(add_5FSNo_5Fminus_5FLt1b3,axiom,(! [X0] : (! [X1] : (! [X2] : (! [X3] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (c_SNo(X3) => (c_SNoLt(add_5FSNo(X0,X1),add_5FSNo(X3,X2)) => c_SNoLt(add_5FSNo(X0,add_5FSNo(X1,minus_5FSNo(X2))),X3))))))))))). % d8da1783fd72b4522a2ef2674aefa0d3c7cad944ade5891e0940902db944480f
fof(add_5FSNo_5Fminus_5FLt2b3,axiom,(! [X0] : (! [X1] : (! [X2] : (! [X3] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (c_SNo(X3) => (c_SNoLt(add_5FSNo(X3,X2),add_5FSNo(X0,X1)) => c_SNoLt(X3,add_5FSNo(X0,add_5FSNo(X1,minus_5FSNo(X2)))))))))))))). % d75f1f3f3c26b052c2204170060cf8a44e80ad69368be646ebf5926be25e2242
fof(add_5FSNo_5Fminus_5FLt_5Flem,axiom,(! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (c_SNo(X3) => (c_SNo(X4) => (c_SNo(X5) => (c_SNoLt(add_5FSNo(X0,add_5FSNo(X1,X5)),add_5FSNo(X3,add_5FSNo(X4,X2))) => c_SNoLt(add_5FSNo(X0,add_5FSNo(X1,minus_5FSNo(X2))),add_5FSNo(X3,add_5FSNo(X4,minus_5FSNo(X5)))))))))))))))))). % 116297ac8c12e169a975d84e9e09540b823936165a8d5775b8490edd35dd4072
fof(add_5FSNo_5Fminus_5FLe2,axiom,(! [X0] : (! [X1] : (! [X2] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (c_SNoLe(X2,add_5FSNo(X0,minus_5FSNo(X1))) => c_SNoLe(add_5FSNo(X2,X1),X0))))))))). % fa732270742bbccf7d4505579ce91ff34e8adbd3f64b3fa6786d609cf02abf68
fof(add_5FSNo_5Fminus_5FLe2b,axiom,(! [X0] : (! [X1] : (! [X2] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (c_SNoLe(add_5FSNo(X2,X1),X0) => c_SNoLe(X2,add_5FSNo(X0,minus_5FSNo(X1))))))))))). % 99b67d3acf970712c44474047af6ab9f4b6ab5400d96f36b9e45fca74f1946c2
fof(add_5FSNo_5FLt_5Fsubprop2,axiom,(! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (c_SNo(X3) => (c_SNo(X4) => (c_SNo(X5) => (c_SNoLt(add_5FSNo(X0,X4),add_5FSNo(X2,X5)) => (c_SNoLt(add_5FSNo(X1,X5),add_5FSNo(X3,X4)) => c_SNoLt(add_5FSNo(X0,X1),add_5FSNo(X2,X3))))))))))))))))). % 8702ab0cdb90636fa46d36f24d6b385e649ecf85066b6d9fcd404a45ae17bffd
fof(add_5FSNo_5FLt_5Fsubprop3a,axiom,(! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (c_SNo(X3) => (c_SNo(X4) => (c_SNo(X5) => (c_SNoLt(add_5FSNo(X0,X2),add_5FSNo(X3,X5)) => (c_SNoLt(add_5FSNo(X1,X5),X4) => c_SNoLt(add_5FSNo(X0,add_5FSNo(X1,X2)),add_5FSNo(X3,X4))))))))))))))))). % 6272a75cb3d9ad292cecedcbbb2df67141ed37853f77445140d94c96593e02c5
fof(add_5FSNo_5FLt_5Fsubprop3b,axiom,(! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (c_SNo(X3) => (c_SNo(X4) => (c_SNo(X5) => (c_SNoLt(add_5FSNo(X0,X5),add_5FSNo(X2,X4)) => (c_SNoLt(X1,add_5FSNo(X5,X3)) => c_SNoLt(add_5FSNo(X0,X1),add_5FSNo(X2,add_5FSNo(X3,X4)))))))))))))))))). % 3c8360eb8a9c9b2650272fb8f8654d59b3d72f61e10053d05bf095c195f59a4d
fof(add_5FSNo_5FLt_5Fsubprop3c,axiom,(! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (c_SNo(X3) => (c_SNo(X4) => (c_SNo(X5) => (c_SNo(X6) => (c_SNo(X7) => (c_SNoLt(add_5FSNo(X0,X5),add_5FSNo(X6,X7)) => (c_SNoLt(add_5FSNo(X1,X7),X4) => (c_SNoLt(add_5FSNo(X6,X2),add_5FSNo(X3,X5)) => c_SNoLt(add_5FSNo(X0,add_5FSNo(X1,X2)),add_5FSNo(X3,X4)))))))))))))))))))))). % 25de5ebb098e89883aa187a57411fa5eedc570f0e6ae0f0d506ca924d06f46c3
fof(add_5FSNo_5FLt_5Fsubprop3d,axiom,(! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (c_SNo(X3) => (c_SNo(X4) => (c_SNo(X5) => (c_SNo(X6) => (c_SNo(X7) => (c_SNoLt(add_5FSNo(X0,X5),add_5FSNo(X6,X4)) => (c_SNoLt(X1,add_5FSNo(X7,X3)) => (c_SNoLt(add_5FSNo(X6,X7),add_5FSNo(X2,X5)) => c_SNoLt(add_5FSNo(X0,X1),add_5FSNo(X2,add_5FSNo(X3,X4))))))))))))))))))))))). % a3e3aaebe95a2d6972db592818d391cde4b8d6672ae4e2477e4056e011b080a2
fof(ordinal_5Fordsucc_5FSNo_5Feq,axiom,(! [X0] : (ordinal(X0) => (ordsucc(X0) = add_5FSNo(ordsucc(c_Empty),X0))))). % 120aedf0e10d032185e4ee76965659599bd865b5fc3a49d6c606fbfb083eb2f5
fof(add_5FSNo_5F3a_5F2b,axiom,(! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (c_SNo(X3) => (c_SNo(X4) => (add_5FSNo(add_5FSNo(X0,add_5FSNo(X1,X2)),add_5FSNo(X3,X4)) = add_5FSNo(add_5FSNo(X4,add_5FSNo(X1,X2)),add_5FSNo(X3,X0)))))))))))))). % 39f1ad98dd6c6755b37e826b5bb29e7a1f278cfaf2baaf5ba86dc193f8eec5ea
fof(add_5FSNo_5F1_5Fordsucc,axiom,(! [X0] : (c_In(X0,omega) => (add_5FSNo(X0,ordsucc(c_Empty)) = ordsucc(X0))))). % 8c729c530d69502cc13890766571341da3e9f182521ce06746ec93158ce9b70d
fof(add_5FSNo_5Feps_5FLt,axiom,(! [X0] : (c_SNo(X0) => (! [X1] : (c_In(X1,omega) => c_SNoLt(X0,add_5FSNo(X0,eps_5F(X1)))))))). % d4057184df5419caf7a89ee72afad6aea75ea6ba613f0a418b6212aad7e3c113
fof(add_5FSNo_5Feps_5FLt_27,axiom,(! [X0] : (! [X1] : (c_SNo(X0) => (c_SNo(X1) => (! [X2] : (c_In(X2,omega) => (c_SNoLt(X0,X1) => c_SNoLt(X0,add_5FSNo(X1,eps_5F(X2))))))))))). % 828de3c936e0e94e085e74c796291b3d030aed4b7f6713729f67858fb8beb2f5
fof(c_SNoLt_5Fminus_5Fpos,axiom,(! [X0] : (! [X1] : (c_SNo(X0) => (c_SNo(X1) => (c_SNoLt(X0,X1) => c_SNoLt(c_Empty,add_5FSNo(X1,minus_5FSNo(X0))))))))). % 0d2079601a24db480cc841c195e65ba72a36ebb2ffc34103b2442a161a96c13b
fof(add_5FSNo_5Fomega_5FIn_5Fcases,axiom,(! [X0] : (! [X1] : (c_In(X1,omega) => (! [X2] : (nat_5Fp(X2) => (c_In(X0,add_5FSNo(X1,X2)) => (c_In(X0,X1) | c_In(add_5FSNo(X0,minus_5FSNo(X1)),X2))))))))). % c40e3c217023c3b2e804242607d4749651dba6f72882fefaf73bc685fa243acf
fof(add_5FSNo_5FLt4,axiom,(! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (c_SNo(X3) => (c_SNo(X4) => (c_SNo(X5) => (c_SNoLt(X0,X3) => (c_SNoLt(X1,X4) => (c_SNoLt(X2,X5) => c_SNoLt(add_5FSNo(X0,add_5FSNo(X1,X2)),add_5FSNo(X3,add_5FSNo(X4,X5))))))))))))))))))). % 78e284814f9716881818d30a144bab05a8e0ade5bb5505c35571d59145cfd7e6
fof(add_5FSNo_5F3_5F3_5F3_5FLt1,axiom,(! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (c_SNo(X3) => (c_SNo(X4) => (c_SNoLt(add_5FSNo(X0,X1),add_5FSNo(X2,X3)) => c_SNoLt(add_5FSNo(X0,add_5FSNo(X1,X4)),add_5FSNo(X2,add_5FSNo(X3,X4))))))))))))))). % 489c063ec5b2e4dc303adc3b6c9eb96b86edeb6bb8f7a6893446758318f45c0a
fof(add_5FSNo_5F3_5F2_5F3_5FLt1,axiom,(! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (c_SNo(X3) => (c_SNo(X4) => (c_SNoLt(add_5FSNo(X1,X0),add_5FSNo(X2,X3)) => c_SNoLt(add_5FSNo(X0,add_5FSNo(X4,X1)),add_5FSNo(X2,add_5FSNo(X3,X4))))))))))))))). % c9b42593c013c64db9bffb5f2c3673e950e80ed6b4243b52f7abf10c0145f44e
fof(add_5FSNo_5Fminus_5FLt12b3,axiom,(! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (c_SNo(X3) => (c_SNo(X4) => (c_SNo(X5) => (c_SNoLt(add_5FSNo(X0,add_5FSNo(X1,X5)),add_5FSNo(X3,add_5FSNo(X4,X2))) => c_SNoLt(add_5FSNo(X0,add_5FSNo(X1,minus_5FSNo(X2))),add_5FSNo(X3,add_5FSNo(X4,minus_5FSNo(X5)))))))))))))))))). % 116297ac8c12e169a975d84e9e09540b823936165a8d5775b8490edd35dd4072
fof(add_5FSNo_5Fminus_5FLe1b,axiom,(! [X0] : (! [X1] : (! [X2] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (c_SNoLe(X0,add_5FSNo(X2,X1)) => c_SNoLe(add_5FSNo(X0,minus_5FSNo(X1)),X2))))))))). % f0ae325c7dca2bed5d41977fe03301138174ea4c3b8c47eaad1ae661a2fdd658
fof(add_5FSNo_5Fminus_5FLe1b3,axiom,(! [X0] : (! [X1] : (! [X2] : (! [X3] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (c_SNo(X3) => (c_SNoLe(add_5FSNo(X0,X1),add_5FSNo(X3,X2)) => c_SNoLe(add_5FSNo(X0,add_5FSNo(X1,minus_5FSNo(X2))),X3))))))))))). % 1610b141171381ed8723bd8548997aac3e5d384108ad5d5acb87919f4b76013c
fof(add_5FSNo_5Fminus_5FLe12b3,axiom,(! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (c_SNo(X3) => (c_SNo(X4) => (c_SNo(X5) => (c_SNoLe(add_5FSNo(X0,add_5FSNo(X1,X5)),add_5FSNo(X3,add_5FSNo(X4,X2))) => c_SNoLe(add_5FSNo(X0,add_5FSNo(X1,minus_5FSNo(X2))),add_5FSNo(X3,add_5FSNo(X4,minus_5FSNo(X5)))))))))))))))))). % 2c6422b311e37926a9b0fc7b30ceb6385cd048b261f783397a6554e433544608
fof(nonneg_5Fabs_5FSNo,axiom,(! [X0] : (c_SNoLe(c_Empty,X0) => (abs_5FSNo(X0) = X0)))). % 2c604e9e021cea943cc5529bbbef151d94934570e0a50f4767c57d0d8b684087
fof(not_5Fnonneg_5Fabs_5FSNo,axiom,(! [X0] : (~ c_SNoLe(c_Empty,X0) => (abs_5FSNo(X0) = minus_5FSNo(X0))))). % e90c3bba16bfccfeb4fa0e7b9e3eedbe7a6d951d8bc98765e508689fee4f13d9
fof(pos_5Fabs_5FSNo,axiom,(! [X0] : (c_SNoLt(c_Empty,X0) => (abs_5FSNo(X0) = X0)))). % a31e0afec627b74b2b4db8b5f0b39163ee0b60232b430e1549580cf250b09ecc
fof(neg_5Fabs_5FSNo,axiom,(! [X0] : (c_SNo(X0) => (c_SNoLt(X0,c_Empty) => (abs_5FSNo(X0) = minus_5FSNo(X0)))))). % b387ac89845af7f29b202087c9a61b166e652e59cfdad166ee1ccc82ca2dc158
fof(c_SNo_5Fabs_5FSNo,axiom,(! [X0] : (c_SNo(X0) => c_SNo(abs_5FSNo(X0))))). % 8681473e66211258e46efdcd2b340f334d5de2aa863bc9bbfd42ec7ee454fbf9
fof(abs_5FSNo_5Fminus,axiom,(! [X0] : (c_SNo(X0) => (abs_5FSNo(minus_5FSNo(X0)) = abs_5FSNo(X0))))). % 81e8115de42258106d400c46c8ca1256e26496885c020452836992db452bd2a7
fof(abs_5FSNo_5Fdist_5Fswap,axiom,(! [X0] : (! [X1] : (c_SNo(X0) => (c_SNo(X1) => (abs_5FSNo(add_5FSNo(X0,minus_5FSNo(X1))) = abs_5FSNo(add_5FSNo(X1,minus_5FSNo(X0))))))))). % 30e19f6d815313840d83a133675d87c745c9f694f80f978995b30af5470ac042
fof(c_SNo_5Fmul_5FSNo,axiom,(! [X0] : (! [X1] : (c_SNo(X0) => (c_SNo(X1) => c_SNo(mul_5FSNo(X0,X1))))))). % 0cc799c87dcca4c63fe0bf7a1c701f843bbb0054761c565b5b6b12d01e4c036b
fof(c_SNo_5Fmul_5FSNo_5Flem,axiom,(! [X0] : (! [X1] : (! [X2] : (! [X3] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (c_SNo(X3) => c_SNo(add_5FSNo(mul_5FSNo(X2,X1),add_5FSNo(mul_5FSNo(X0,X3),minus_5FSNo(mul_5FSNo(X2,X3)))))))))))))). % ccf21f4e350282f7875222df08b3f7268e4077cd84eda9d87a674f494b5bf623
fof(c_SNo_5Fmul_5FSNo_5F3,axiom,(! [X0] : (! [X1] : (! [X2] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => c_SNo(mul_5FSNo(X0,mul_5FSNo(X1,X2)))))))))). % b70df20e6fcb52c273ae83ccfaf0cbe195e72c4beb5cc35d0e442a50494d7de3
fof(mul_5FSNo_5FLt,axiom,(! [X0] : (! [X1] : (! [X2] : (! [X3] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (c_SNo(X3) => (c_SNoLt(X2,X0) => (c_SNoLt(X3,X1) => c_SNoLt(add_5FSNo(mul_5FSNo(X2,X1),mul_5FSNo(X0,X3)),add_5FSNo(mul_5FSNo(X0,X1),mul_5FSNo(X2,X3)))))))))))))). % 67ffeda4c6f74ca733ab0dd5882c87418e1134f3278c41e1b9e3a49fd8b7c4aa
fof(mul_5FSNo_5FLe,axiom,(! [X0] : (! [X1] : (! [X2] : (! [X3] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (c_SNo(X3) => (c_SNoLe(X2,X0) => (c_SNoLe(X3,X1) => c_SNoLe(add_5FSNo(mul_5FSNo(X2,X1),mul_5FSNo(X0,X3)),add_5FSNo(mul_5FSNo(X0,X1),mul_5FSNo(X2,X3)))))))))))))). % 64604522ec7a66c898a2719a43331e8790ceb95a98415a95b5db616afa379124
fof(mul_5FSNo_5FSNoL_5Finterpolate,axiom,(! [X0] : (! [X1] : (c_SNo(X0) => (c_SNo(X1) => (! [X2] : (c_In(X2,c_SNoL(mul_5FSNo(X0,X1))) => ((? [X3] : (c_In(X3,c_SNoL(X0)) & (? [X4] : (c_In(X4,c_SNoL(X1)) & c_SNoLe(add_5FSNo(X2,mul_5FSNo(X3,X4)),add_5FSNo(mul_5FSNo(X3,X1),mul_5FSNo(X0,X4))))))) | (? [X3] : (c_In(X3,c_SNoR(X0)) & (? [X4] : (c_In(X4,c_SNoR(X1)) & c_SNoLe(add_5FSNo(X2,mul_5FSNo(X3,X4)),add_5FSNo(mul_5FSNo(X3,X1),mul_5FSNo(X0,X4))))))))))))))). % 1ec79f4e34f9a4bb648d04419699d58f578b07dfe41b8c3c8fd6c0e2e7404b94
fof(mul_5FSNo_5FSNoR_5Finterpolate,axiom,(! [X0] : (! [X1] : (c_SNo(X0) => (c_SNo(X1) => (! [X2] : (c_In(X2,c_SNoR(mul_5FSNo(X0,X1))) => ((? [X3] : (c_In(X3,c_SNoL(X0)) & (? [X4] : (c_In(X4,c_SNoR(X1)) & c_SNoLe(add_5FSNo(mul_5FSNo(X3,X1),mul_5FSNo(X0,X4)),add_5FSNo(X2,mul_5FSNo(X3,X4))))))) | (? [X3] : (c_In(X3,c_SNoR(X0)) & (? [X4] : (c_In(X4,c_SNoL(X1)) & c_SNoLe(add_5FSNo(mul_5FSNo(X3,X1),mul_5FSNo(X0,X4)),add_5FSNo(X2,mul_5FSNo(X3,X4))))))))))))))). % ddd8b597fe66298a07ccc759aa1f5daa6503c2d9d59bdcca8429866876189f00
fof(mul_5FSNo_5FzeroR,axiom,(! [X0] : (c_SNo(X0) => (mul_5FSNo(X0,c_Empty) = c_Empty)))). % 46a9007a33dfdd41067dbe8b2990876300c9f36f17eda790f636160738c20e25
fof(mul_5FSNo_5FoneR,axiom,(! [X0] : (c_SNo(X0) => (mul_5FSNo(X0,ordsucc(c_Empty)) = X0)))). % bd601b8e3252eb28873719169159ee0ef30c2303c64a80b24aa26881dbe4f6ed
fof(mul_5FSNo_5Fcom,axiom,(! [X0] : (! [X1] : (c_SNo(X0) => (c_SNo(X1) => (mul_5FSNo(X0,X1) = mul_5FSNo(X1,X0))))))). % b53e7266d2b8331cdd95ca20b7f6811d0a460fc67be322cf74fb2af1d281ea4c
fof(mul_5FSNo_5Fminus_5FdistrL,axiom,(! [X0] : (! [X1] : (c_SNo(X0) => (c_SNo(X1) => (mul_5FSNo(minus_5FSNo(X0),X1) = minus_5FSNo(mul_5FSNo(X0,X1)))))))). % 9de1fa9b8752ee1153e808caa30232b5ec190b9a3cddd23374a7c3af91b8fb06
fof(mul_5FSNo_5Fminus_5FdistrR,axiom,(! [X0] : (! [X1] : (c_SNo(X0) => (c_SNo(X1) => (mul_5FSNo(X0,minus_5FSNo(X1)) = minus_5FSNo(mul_5FSNo(X0,X1)))))))). % 5a89ae19d86363148009688c2986255511fec80a8c867821e8e6798abc0319e6
fof(mul_5FSNo_5FdistrR,axiom,(! [X0] : (! [X1] : (! [X2] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (mul_5FSNo(add_5FSNo(X0,X1),X2) = add_5FSNo(mul_5FSNo(X0,X2),mul_5FSNo(X1,X2)))))))))). % 08c5d8f719c3a9264700e7ca466ad688c4fa5a14fa259fbbeca65986de1d1831
fof(mul_5FSNo_5FdistrL,axiom,(! [X0] : (! [X1] : (! [X2] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (mul_5FSNo(X0,add_5FSNo(X1,X2)) = add_5FSNo(mul_5FSNo(X0,X1),mul_5FSNo(X0,X2)))))))))). % 58251a89cd22b894687387772513303547a43dbdb1887246ba5b5c889f271651
fof(mul_5FSNo_5Fassoc,axiom,(! [X0] : (! [X1] : (! [X2] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (mul_5FSNo(X0,mul_5FSNo(X1,X2)) = mul_5FSNo(mul_5FSNo(X0,X1),X2))))))))). % 486865c3188385931c49f470667cf40aed4fd0ae74607f2310f86efc829888ba
fof(mul_5Fnat_5Fmul_5FSNo,axiom,(! [X0] : (c_In(X0,omega) => (! [X1] : (c_In(X1,omega) => (mul_5Fnat(X0,X1) = mul_5FSNo(X0,X1))))))). % d488daae49a28a575741be5a526a525621d1e4bcc346fa8339b1216ee1837b49
fof(mul_5FSNo_5FIn_5Fomega,axiom,(! [X0] : (c_In(X0,omega) => (! [X1] : (c_In(X1,omega) => c_In(mul_5FSNo(X0,X1),omega)))))). % f4015fb6b89cc9918460b7475d37f56eddd61aa8a138170b5f9d63669ad7dca2
fof(mul_5FSNo_5FzeroL,axiom,(! [X0] : (c_SNo(X0) => (mul_5FSNo(c_Empty,X0) = c_Empty)))). % 3a96865454e2d5a1ae5de0ccf8412535af06ee5813a0c3b5ab43575f54ee8e0f
fof(mul_5FSNo_5FoneL,axiom,(! [X0] : (c_SNo(X0) => (mul_5FSNo(ordsucc(c_Empty),X0) = X0)))). % ed70c7de23ba2c1bf90761c9dc07579f6bde720cf11f99ecd684f271d7a9f904
fof(mul_5FSNo_5Frotate_5F3_5F1,axiom,(! [X0] : (! [X1] : (! [X2] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (mul_5FSNo(X0,mul_5FSNo(X1,X2)) = mul_5FSNo(X2,mul_5FSNo(X0,X1)))))))))). % b3c87bb18e8e46b69cbd8c05402461abe5fad7a4dff9d87f496776bb7ba0a081
fof(pos_5Fmul_5FSNo_5FLt,axiom,(! [X0] : (! [X1] : (! [X2] : (c_SNo(X0) => (c_SNoLt(c_Empty,X0) => (c_SNo(X1) => (c_SNo(X2) => (c_SNoLt(X1,X2) => c_SNoLt(mul_5FSNo(X0,X1),mul_5FSNo(X0,X2))))))))))). % cc45b1564fb6e160fca709ac04672be251b7bdec3d8a6fc9933464dfe6f1b151
fof(nonneg_5Fmul_5FSNo_5FLe,axiom,(! [X0] : (! [X1] : (! [X2] : (c_SNo(X0) => (c_SNoLe(c_Empty,X0) => (c_SNo(X1) => (c_SNo(X2) => (c_SNoLe(X1,X2) => c_SNoLe(mul_5FSNo(X0,X1),mul_5FSNo(X0,X2))))))))))). % e77048acfcb89323115156e60b1da3d9d5a827e5b06dcb30107b411cf46bc9eb
fof(neg_5Fmul_5FSNo_5FLt,axiom,(! [X0] : (! [X1] : (! [X2] : (c_SNo(X0) => (c_SNoLt(X0,c_Empty) => (c_SNo(X1) => (c_SNo(X2) => (c_SNoLt(X2,X1) => c_SNoLt(mul_5FSNo(X0,X1),mul_5FSNo(X0,X2))))))))))). % 73a4e89a0edaa811d194eed40e30f1af76f2ee6de2569b81307d2028d758dc96
fof(pos_5Fmul_5FSNo_5FLt_27,axiom,(! [X0] : (! [X1] : (! [X2] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (c_SNoLt(c_Empty,X2) => (c_SNoLt(X0,X1) => c_SNoLt(mul_5FSNo(X0,X2),mul_5FSNo(X1,X2))))))))))). % ceb619cdd9295fb3445cd619e45d7571f114e00cf450ab99d321b73539a6b4cd
fof(mul_5FSNo_5FLt1_5Fpos_5FLt,axiom,(! [X0] : (! [X1] : (c_SNo(X0) => (c_SNo(X1) => (c_SNoLt(X0,ordsucc(c_Empty)) => (c_SNoLt(c_Empty,X1) => c_SNoLt(mul_5FSNo(X0,X1),X1)))))))). % 85a30a765bf2814fc57bdd1108b9c3d83dfced17ec4b754095717b0d713b513e
fof(nonneg_5Fmul_5FSNo_5FLe_27,axiom,(! [X0] : (! [X1] : (! [X2] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (c_SNoLe(c_Empty,X2) => (c_SNoLe(X0,X1) => c_SNoLe(mul_5FSNo(X0,X2),mul_5FSNo(X1,X2))))))))))). % 278f1e92f0d412f224c6273f959298bf130acae0e052514730d5f50cd437ce26
fof(mul_5FSNo_5FLe1_5Fnonneg_5FLe,axiom,(! [X0] : (! [X1] : (c_SNo(X0) => (c_SNo(X1) => (c_SNoLe(X0,ordsucc(c_Empty)) => (c_SNoLe(c_Empty,X1) => c_SNoLe(mul_5FSNo(X0,X1),X1)))))))). % a5b38b524b7755e9262aa68a02d3dcf5d4ca5c590fbc38127b6e69d7c9f97b4b
fof(pos_5Fmul_5FSNo_5FLt2,axiom,(! [X0] : (! [X1] : (! [X2] : (! [X3] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (c_SNo(X3) => (c_SNoLt(c_Empty,X0) => (c_SNoLt(c_Empty,X1) => (c_SNoLt(X0,X2) => (c_SNoLt(X1,X3) => c_SNoLt(mul_5FSNo(X0,X1),mul_5FSNo(X2,X3))))))))))))))). % 974e24114ccd304e5645147e0f3b0ccb0fbaa1fe2c982c486ae4f1e55a166240
fof(nonneg_5Fmul_5FSNo_5FLe2,axiom,(! [X0] : (! [X1] : (! [X2] : (! [X3] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (c_SNo(X3) => (c_SNoLe(c_Empty,X0) => (c_SNoLe(c_Empty,X1) => (c_SNoLe(X0,X2) => (c_SNoLe(X1,X3) => c_SNoLe(mul_5FSNo(X0,X1),mul_5FSNo(X2,X3))))))))))))))). % 2ebb224922eb4de41080727f7fcf43d3dec77cb077b80fa3abbe7e9ab075f150
fof(mul_5FSNo_5Fpos_5Fpos,axiom,(! [X0] : (! [X1] : (c_SNo(X0) => (c_SNo(X1) => (c_SNoLt(c_Empty,X0) => (c_SNoLt(c_Empty,X1) => c_SNoLt(c_Empty,mul_5FSNo(X0,X1))))))))). % d3b05b9692591b95f07be342649cb40d78b96676b4451291f94b808e8f4b8667
fof(mul_5FSNo_5Fpos_5Fneg,axiom,(! [X0] : (! [X1] : (c_SNo(X0) => (c_SNo(X1) => (c_SNoLt(c_Empty,X0) => (c_SNoLt(X1,c_Empty) => c_SNoLt(mul_5FSNo(X0,X1),c_Empty)))))))). % c075932f0cc0b492572611e5a46f6dfbe7b594e4f5db7811f7e084f39449e3a7
fof(mul_5FSNo_5Fneg_5Fpos,axiom,(! [X0] : (! [X1] : (c_SNo(X0) => (c_SNo(X1) => (c_SNoLt(X0,c_Empty) => (c_SNoLt(c_Empty,X1) => c_SNoLt(mul_5FSNo(X0,X1),c_Empty)))))))). % 7856441fba4d9fd1087da0c9765ae8948a05fceb99c47c8218760586854636cd
fof(mul_5FSNo_5Fneg_5Fneg,axiom,(! [X0] : (! [X1] : (c_SNo(X0) => (c_SNo(X1) => (c_SNoLt(X0,c_Empty) => (c_SNoLt(X1,c_Empty) => c_SNoLt(c_Empty,mul_5FSNo(X0,X1))))))))). % d63f91a24d8f6dd9e9eefee56a81afaa58b9307dbc14aa5d88a393eed886a5ff
fof(mul_5FSNo_5Fnonneg_5Fnonneg,axiom,(! [X0] : (! [X1] : (c_SNo(X0) => (c_SNo(X1) => (c_SNoLe(c_Empty,X0) => (c_SNoLe(c_Empty,X1) => c_SNoLe(c_Empty,mul_5FSNo(X0,X1))))))))). % 6ddfb1ddab64532ee9e19b4e6b9e46b8b343dd842b45abcb9a5be28acb61ef39
fof(mul_5FSNo_5Fnonpos_5Fpos,axiom,(! [X0] : (! [X1] : (c_SNo(X0) => (c_SNo(X1) => (c_SNoLe(X0,c_Empty) => (c_SNoLt(c_Empty,X1) => c_SNoLe(mul_5FSNo(X0,X1),c_Empty)))))))). % e6f79d08137c685cf464467704f67d93b25245aa7a32cff58d372559839081fc
fof(mul_5FSNo_5Fnonpos_5Fneg,axiom,(! [X0] : (! [X1] : (c_SNo(X0) => (c_SNo(X1) => (c_SNoLe(X0,c_Empty) => (c_SNoLt(X1,c_Empty) => c_SNoLe(c_Empty,mul_5FSNo(X0,X1))))))))). % 3b95e211bb911e2969d483448fa4b162546ed05b26f8d803e6e6a272aaa136ff
fof(nonpos_5Fmul_5FSNo_5FLe,axiom,(! [X0] : (! [X1] : (! [X2] : (c_SNo(X0) => (c_SNoLe(X0,c_Empty) => (c_SNo(X1) => (c_SNo(X2) => (c_SNoLe(X2,X1) => c_SNoLe(mul_5FSNo(X0,X1),mul_5FSNo(X0,X2))))))))))). % cea26ac3e7afddd8dc5c614739062d6954c328b66525e5db0c907222196ffd9f
fof(c_SNo_5Fzero_5For_5Fsqr_5Fpos,axiom,(! [X0] : (c_SNo(X0) => ((X0 = c_Empty) | c_SNoLt(c_Empty,mul_5FSNo(X0,X0)))))). % 8f939aa3127093659ddddd5d938dddcf4ab93517e7062e806099ec4d4e865145
fof(c_SNo_5Fpos_5Fsqr_5Funiq,axiom,(! [X0] : (! [X1] : (c_SNo(X0) => (c_SNo(X1) => (c_SNoLt(c_Empty,X0) => (c_SNoLt(c_Empty,X1) => ((mul_5FSNo(X0,X0) = mul_5FSNo(X1,X1)) => (X0 = X1))))))))). % 6383e2385db28e3d1daf37b9a2e779c12368c6c95d9b946d5dea250e1fffdb60
fof(c_SNo_5Fnonneg_5Fsqr_5Funiq,axiom,(! [X0] : (! [X1] : (c_SNo(X0) => (c_SNo(X1) => (c_SNoLe(c_Empty,X0) => (c_SNoLe(c_Empty,X1) => ((mul_5FSNo(X0,X0) = mul_5FSNo(X1,X1)) => (X0 = X1))))))))). % 171cb357e0552171770ca487792f93ba45d96302002b7ce0163743f6d800b45c
fof(c_SNo_5Ffoil,axiom,(! [X0] : (! [X1] : (! [X2] : (! [X3] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (c_SNo(X3) => (mul_5FSNo(add_5FSNo(X0,X1),add_5FSNo(X2,X3)) = add_5FSNo(mul_5FSNo(X0,X2),add_5FSNo(mul_5FSNo(X0,X3),add_5FSNo(mul_5FSNo(X1,X2),mul_5FSNo(X1,X3)))))))))))))). % ff59ccdf6b73c74ba0be299e771917d934e9490bdbf71de8580eb0f5dc876c0b
fof(mul_5FSNo_5Fminus_5Fminus,axiom,(! [X0] : (! [X1] : (c_SNo(X0) => (c_SNo(X1) => (mul_5FSNo(minus_5FSNo(X0),minus_5FSNo(X1)) = mul_5FSNo(X0,X1))))))). % 84bbb9763ab9578e83a87565f23eac12c4f88f047ab6ec5956cb272c300874b8
fof(mul_5FSNo_5Fcom_5F3_5F0_5F1,axiom,(! [X0] : (! [X1] : (! [X2] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (mul_5FSNo(X0,mul_5FSNo(X1,X2)) = mul_5FSNo(X1,mul_5FSNo(X0,X2)))))))))). % 930ac35c938cfb7aed6810577eddc774adb186b6f2e6efc12321484746134e07
fof(mul_5FSNo_5Fcom_5F3b_5F1_5F2,axiom,(! [X0] : (! [X1] : (! [X2] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (mul_5FSNo(mul_5FSNo(X0,X1),X2) = mul_5FSNo(mul_5FSNo(X0,X2),X1))))))))). % 4dfe2a5c7cc0482c9552f7a18f300a9efc78b1b485993a90a3a147517a9cb604
fof(mul_5FSNo_5Fcom_5F4_5Finner_5Fmid,axiom,(! [X0] : (! [X1] : (! [X2] : (! [X3] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (c_SNo(X3) => (mul_5FSNo(mul_5FSNo(X0,X1),mul_5FSNo(X2,X3)) = mul_5FSNo(mul_5FSNo(X0,X2),mul_5FSNo(X1,X3)))))))))))). % 9f37e4d849faf81abbe79ce265fcf91a68500da0f82ca7e303ed2370ca680d6a
fof(c_SNo_5Ffoil_5Fmm,axiom,(! [X0] : (! [X1] : (! [X2] : (! [X3] : (c_SNo(X0) => (c_SNo(X1) => (c_SNo(X2) => (c_SNo(X3) => (mul_5FSNo(add_5FSNo(X0,minus_5FSNo(X1)),add_5FSNo(X2,minus_5FSNo(X3))) = add_5FSNo(mul_5FSNo(X0,X2),add_5FSNo(minus_5FSNo(mul_5FSNo(X0,X3)),add_5FSNo(minus_5FSNo(mul_5FSNo(X1,X2)),mul_5FSNo(X1,X3)))))))))))))). % 7c43f66fda3a6e2b8ba405710b3299453dcb052d55ab66e7fd6a7f3888dd443e
fof(mul_5FSNo_5Fnonzero_5Fcancel,axiom,(! [X0] : (! [X1] : (! [X2] : (c_SNo(X0) => (~ (X0 = c_Empty) => (c_SNo(X1) => (c_SNo(X2) => ((mul_5FSNo(X0,X1) = mul_5FSNo(X0,X2)) => (X1 = X2)))))))))). % 837ded32a294988a8831d2d67f0fdee970f56365ec41c6e0fe7a3cf2a355df58
fof(mul_5FSNo_5FSNoCut_5FSNoL_5Finterpolate,axiom,(! [X0] : (! [X1] : (! [X2] : (! [X3] : (c_SNoCutP(X0,X1) => (c_SNoCutP(X2,X3) => (! [X4] : (! [X5] : ((X4 = c_SNoCut(X0,X1)) => ((X5 = c_SNoCut(X2,X3)) => (! [X6] : (c_In(X6,c_SNoL(mul_5FSNo(X4,X5))) => ((? [X7] : (c_In(X7,X0) & (? [X8] : (c_In(X8,X2) & c_SNoLe(add_5FSNo(X6,mul_5FSNo(X7,X8)),add_5FSNo(mul_5FSNo(X7,X5),mul_5FSNo(X4,X8))))))) | (? [X7] : (c_In(X7,X1) & (? [X8] : (c_In(X8,X3) & c_SNoLe(add_5FSNo(X6,mul_5FSNo(X7,X8)),add_5FSNo(mul_5FSNo(X7,X5),mul_5FSNo(X4,X8))))))))))))))))))))). % 9dafc2e9ddb3518e25cc11db2288dd0b8a236f2dd39de1cc0d151dca8438d7e5
fof(mul_5FSNo_5FSNoCut_5FSNoR_5Finterpolate,axiom,(! [X0] : (! [X1] : (! [X2] : (! [X3] : (c_SNoCutP(X0,X1) => (c_SNoCutP(X2,X3) => (! [X4] : (! [X5] : ((X4 = c_SNoCut(X0,X1)) => ((X5 = c_SNoCut(X2,X3)) => (! [X6] : (c_In(X6,c_SNoR(mul_5FSNo(X4,X5))) => ((? [X7] : (c_In(X7,X0) & (? [X8] : (c_In(X8,X3) & c_SNoLe(add_5FSNo(mul_5FSNo(X7,X5),mul_5FSNo(X4,X8)),add_5FSNo(X6,mul_5FSNo(X7,X8))))))) | (? [X7] : (c_In(X7,X1) & (? [X8] : (c_In(X8,X2) & c_SNoLe(add_5FSNo(mul_5FSNo(X7,X5),mul_5FSNo(X4,X8)),add_5FSNo(X6,mul_5FSNo(X7,X8))))))))))))))))))))). % ad7d653d7122b47bc1f9eb6e60091640913149befe9bc454990f64ca3e6fe123
fof(nonpos_5Fnonneg_5F0,axiom,(! [X0] : (c_In(X0,omega) => (! [X1] : (c_In(X1,omega) => ((X0 = minus_5FSNo(X1)) => ((X0 = c_Empty) & (X1 = c_Empty)))))))). % 287a9d3f9c689b9bbae44ccf02f040ff691ccafe4b16e89ecfd4b4f532a617a0
fof(mul_5Fminus_5FSNo_5FdistrR,axiom,(! [X0] : (! [X1] : (c_SNo(X0) => (c_SNo(X1) => (mul_5FSNo(X0,minus_5FSNo(X1)) = minus_5FSNo(mul_5FSNo(X0,X1)))))))). % 5a89ae19d86363148009688c2986255511fec80a8c867821e8e6798abc0319e6
fof(int_5FSNo,axiom,(! [X0] : (c_In(X0,int) => c_SNo(X0)))). % 3cb32f6feca180abbe9da1bb6e08373f6631378e67f87dc7df714f85860c8c68
fof(c_Subq_5Fomega_5Fint,axiom,c_Subq(omega,int)). % 8c51136a419d0f0b0ca871ef6e4977b53653c0976ba1b25b27dfa5daf3e18100
fof(int_5Fminus_5FSNo_5Fomega,axiom,(! [X0] : (c_In(X0,omega) => c_In(minus_5FSNo(X0),int)))). % 8144289bc4661b1c16b556930e35bf1f16fa2e8126c61a3c291a26b530c4333f
fof(int_5Fadd_5FSNo_5Flem,axiom,(! [X0] : (c_In(X0,omega) => (! [X1] : (nat_5Fp(X1) => c_In(add_5FSNo(minus_5FSNo(X0),X1),int)))))). % df8b86b670ce860fadce2e1c29b4ff3fdfab58b6e3a23f44b1548338a1712a82
fof(int_5Fadd_5FSNo,axiom,(! [X0] : (c_In(X0,int) => (! [X1] : (c_In(X1,int) => c_In(add_5FSNo(X0,X1),int)))))). % 8470044530cddfd5313e241558e18bc1b8646b4d2c1f5c44b26fc3978c1d631d
fof(int_5Fminus_5FSNo,axiom,(! [X0] : (c_In(X0,int) => c_In(minus_5FSNo(X0),int)))). % 77c8fb29530ed89ad7e50b011056f84efaede92e9fb01aa94dbff0d0320e0e9c
fof(int_5Fmul_5FSNo,axiom,(! [X0] : (c_In(X0,int) => (! [X1] : (c_In(X1,int) => c_In(mul_5FSNo(X0,X1),int)))))). % 1a5465f940a029eb51d3f635ea2bbc8b265c0e75328df51a2a3f4892cc5c890c
fof(nonneg_5Fint_5Fnat_5Fp,axiom,(! [X0] : (c_In(X0,int) => (c_SNoLe(c_Empty,X0) => nat_5Fp(X0))))). % fa892b590cae7a4909089212c8f2871dcf245cd87aca4a8d7a5961d072ecf13d
fof(quotient_5Fremainder_5Fnat,axiom,(! [X0] : (c_In(X0,setminus(omega,c_Sing(c_Empty))) => (! [X1] : (nat_5Fp(X1) => (? [X2] : (c_In(X2,omega) & (? [X3] : (c_In(X3,X0) & (X1 = add_5Fnat(mul_5Fnat(X2,X0),X3))))))))))). % 6d5933f70f115713a55aa8ab5e6e874c767b2610b7fa9e721fa2118ed3bcbaf9
fof(mul_5FSNo_5Fnonpos_5Fnonneg,axiom,(! [X0] : (! [X1] : (c_SNo(X0) => (c_SNo(X1) => (c_SNoLe(X0,c_Empty) => (c_SNoLe(c_Empty,X1) => c_SNoLe(mul_5FSNo(X0,X1),c_Empty)))))))). % 7f598b2c6fd019af1b47986a4293da5a9a643205862c1d9972207240d6cfba8c
fof(ordinal_5F0_5FIn_5Fordsucc,axiom,(! [X0] : (ordinal(X0) => c_In(c_Empty,ordsucc(X0))))). % 7bf9bfd96a57b754e64077e271d746012482bd13d20a3bcda01087a4be44cc42
fof(ordinal_5Fordsucc_5Fpos,axiom,(! [X0] : (ordinal(X0) => c_SNoLt(c_Empty,ordsucc(X0))))). % 5f96d3d4388174504c7352fae25f5a4053763d684d98363c3a24f3fd7b47643c
fof(quotient_5Fremainder_5Fint,axiom,(! [X0] : (c_In(X0,setminus(omega,c_Sing(c_Empty))) => (! [X1] : (c_In(X1,int) => (? [X2] : (c_In(X2,int) & (? [X3] : (c_In(X3,X0) & (X1 = add_5FSNo(mul_5FSNo(X2,X0),X3))))))))))). % d096b825ff201e99d71ae0a2c40198caca0338583f2f8708d14c988daf0b1e3e
fof(divides_5Fint,axiom,(! [X0:$i] : (! [X1:$i] : (divides_5Fint(c_X0,c_X1) <=> ((c_In(c_X0,int) & c_In(c_X1,int)) & (? [X2] : (c_In(X2,int) & (mul_5FSNo(c_X0,X2) = c_X1)))))))). % d276f2dfb1476a71df81f0b8734bd5a4d2f97aec7458d5454984c5b810b377b5
fof(divides_5Fint_5Fref,axiom,(! [X0] : (c_In(X0,int) => divides_5Fint(X0,X0)))). % ec79d9810a994ea0d9759063a11216a5ee741f0e3d4dd9c9d0917b33bf2cd744
fof(divides_5Fint_5F0,axiom,(! [X0] : (c_In(X0,int) => divides_5Fint(X0,c_Empty)))). % 9ae68607e83ba0cd88a6f2df86fb0cec3cffef859abb679d8f4281999a0e2283
fof(divides_5Fint_5Fadd_5FSNo,axiom,(! [X0] : (! [X1] : (! [X2] : (divides_5Fint(X0,X1) => (divides_5Fint(X0,X2) => divides_5Fint(X0,add_5FSNo(X1,X2)))))))). % abc895429a0374a1f54fcf54ee0b2f8a085850f251e764083e1fbfa1402b3a31
fof(divides_5Fint_5Fmul_5FSNo,axiom,(! [X0] : (! [X1] : (! [X2] : (! [X3] : (divides_5Fint(X0,X2) => (divides_5Fint(X1,X3) => divides_5Fint(mul_5FSNo(X0,X1),mul_5FSNo(X2,X3))))))))). % 6c4e99caa9e0a31d62201eb57289321a170f7fe6dbcc89b750a805b54b0f7a7d
fof(conj_hammer_test_10847,conjecture,(! [X0] : (! [X1] : (divides_5Fnat(X0,X1) => divides_5Fint(X0,X1))))).
