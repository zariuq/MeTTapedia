import Mettapedia.Languages.Megalodon.SourceAdmission

/-! Untrusted source items; checked by NaturalRecursion. -/

namespace Mettapedia.Languages.Megalodon.NaturalRecursion.Evidence

open MathdataKernel NativeAdmission

private def fragment0 : Tm :=
  Tm.app
    (Tm.app
       (Tm.app
          (Tm.app
             (Tm.app
                (Tm.app
                   (Tm.typeApp
                      (Tm.named
                         "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                      (Tp.var 0))
                   (Tm.db 5))
                (Tm.db 4))
             (Tm.db 3))
          (Tm.db 2))
       (Tm.db 1))
    (Tm.db 0)

private def fragment1 : Tm :=
  Tm.app
    (Tm.app
       (Tm.app
          (Tm.app
             (Tm.app
                (Tm.app
                   (Tm.typeApp
                      (Tm.named
                         "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                      (Tp.var 0))
                   (Tm.db 6))
                (Tm.db 5))
             (Tm.db 4))
          (Tm.db 3))
       (Tm.db 1))
    (Tm.db 0)

private def fragment2 : Tm := Tm.lam (Tp.var 0) fragment1

private def fragment3 : Tm :=
  Tm.app
    (Tm.typeApp
       (Tm.named "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099")
       (Tp.var 0))
    fragment2

private def fragment4 : Tm :=
  Tm.app
    (Tm.app
       (Tm.app
          (Tm.app
             (Tm.app
                (Tm.app
                   (Tm.typeApp
                      (Tm.named
                         "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                      (Tp.var 0))
                   (Tm.db 7))
                (Tm.db 6))
             (Tm.db 5))
          (Tm.db 4))
       (Tm.app (Tm.db 6) (Tm.db 2)))
    (Tm.db 0)

private def fragment5 : Tm :=
  Tm.app
    (Tm.app
       (Tm.app
          (Tm.app
             (Tm.app
                (Tm.app
                   (Tm.typeApp
                      (Tm.named
                         "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                      (Tp.var 0))
                   (Tm.db 4))
                (Tm.db 3))
             (Tm.db 2))
          (Tm.db 1))
       (Tm.db 4))
    (Tm.db 0)

private def fragment6 : Tm :=
  Tm.app
    (Tm.app
       (Tm.app
          (Tm.app
             (Tm.app
                (Tm.app
                   (Tm.typeApp
                      (Tm.named
                         "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                      (Tp.var 0))
                   (Tm.db 5))
                (Tm.db 4))
             (Tm.db 3))
          (Tm.db 2))
       (Tm.app (Tm.db 4) (Tm.db 1)))
    (Tm.db 0)

private def fragment7 : Tm :=
  Tm.app
    (Tm.app
       (Tm.app
          (Tm.app
             (Tm.app
                (Tm.app
                   (Tm.typeApp
                      (Tm.named
                         "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                      (Tp.var 0))
                   (Tm.db 6))
                (Tm.db 5))
             (Tm.db 4))
          (Tm.db 3))
       (Tm.db 2))
    (Tm.db 0)

private def fragment8 : Tm :=
  Tm.app
    (Tm.app
       (Tm.app
          (Tm.app
             (Tm.app
                (Tm.app
                   (Tm.typeApp
                      (Tm.named
                         "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                      (Tp.var 0))
                   (Tm.db 5))
                (Tm.db 4))
             (Tm.db 3))
          (Tm.db 2))
       (Tm.db 5))
    (Tm.db 3)

private def fragment9 : Tm :=
  Tm.app
    (Tm.app
       (Tm.app
          (Tm.app
             (Tm.app
                (Tm.app
                   (Tm.typeApp
                      (Tm.named
                         "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                      (Tp.var 0))
                   (Tm.db 7))
                (Tm.db 6))
             (Tm.db 5))
          (Tm.db 4))
       (Tm.db 1))
    (Tm.db 0)

private def fragment10 : Tm :=
  Tm.app (Tm.named "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738") fragment9

private def fragment11 : Tm :=
  Tm.app
    (Tm.typeApp
       (Tm.named "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099")
       (Tp.var 0))
    (Tm.lam
       (Tp.var 0)
       (Tm.app
          fragment10
          (Tm.app
             (Tm.app
                (Tm.typeApp
                   (Tm.named "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                   (Tp.var 0))
                (Tm.app (Tm.app (Tm.db 4) (Tm.db 1)) (Tm.db 0)))
             (Tm.db 5))))

private def fragment12 : Tm :=
  Tm.all
    (Tp.base 0)
    (Tm.imp
       (Tm.app
          (Tm.app
             (Tm.typeApp
                (Tm.named "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                (Tp.base 0))
             (Tm.app (Tm.db 5) (Tm.db 0)))
          (Tm.db 6))
       fragment11)

private def fragment13 : Tm :=
  Tm.app
    (Tm.named "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
    (Tm.app
       (Tm.app
          (Tm.app
             (Tm.app
                (Tm.app
                   (Tm.app
                      (Tm.typeApp
                         (Tm.named
                            "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                         (Tp.var 0))
                      (Tm.db 9))
                   (Tm.db 8))
                (Tm.db 7))
             (Tm.db 6))
          (Tm.db 1))
       (Tm.db 0))

private def fragment14 : Tm :=
  Tm.all
    (Tp.base 0)
    (Tm.imp
       (Tm.app
          (Tm.app
             (Tm.typeApp
                (Tm.named "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                (Tp.base 0))
             (Tm.app (Tm.db 7) (Tm.db 0)))
          (Tm.db 2))
       (Tm.app
          (Tm.typeApp
             (Tm.named "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099")
             (Tp.var 0))
          (Tm.lam
             (Tp.var 0)
             (Tm.app
                fragment13
                (Tm.app
                   (Tm.app
                      (Tm.typeApp
                         (Tm.named
                            "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                         (Tp.var 0))
                      (Tm.app (Tm.app (Tm.db 6) (Tm.db 1)) (Tm.db 0)))
                   (Tm.db 2))))))

private def fragment15 : Tm := Tm.app fragment10 fragment14

private def fragment16 : Tm :=
  Tm.app
    (Tm.app
       (Tm.app
          (Tm.app
             (Tm.app
                (Tm.app
                   (Tm.typeApp
                      (Tm.named
                         "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                      (Tp.var 0))
                   (Tm.db 7))
                (Tm.db 6))
             (Tm.db 5))
          (Tm.db 4))
       (Tm.app (Tm.db 6) (Tm.db 1)))
    (Tm.app (Tm.app (Tm.db 4) (Tm.db 1)) (Tm.db 0))

private def fragment17 : Tm :=
  Tm.lam
    (Tp.var 0)
    (Tm.app
       fragment13
       (Tm.app
          (Tm.app
             (Tm.typeApp
                (Tm.named "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                (Tp.var 0))
             (Tm.app (Tm.app (Tm.db 6) (Tm.db 1)) (Tm.db 0)))
          (Tm.app (Tm.app (Tm.db 6) (Tm.db 3)) (Tm.db 2))))

private def fragment18 : Tm :=
  Tm.all
    (Tp.base 0)
    (Tm.imp
       (Tm.app
          (Tm.app
             (Tm.typeApp
                (Tm.named "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                (Tp.base 0))
             (Tm.app (Tm.db 7) (Tm.db 0)))
          (Tm.app (Tm.db 7) (Tm.db 2)))
       (Tm.app
          (Tm.typeApp
             (Tm.named "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099")
             (Tp.var 0))
          fragment17))

private def fragment19 : Tm :=
  Tm.all
    (Tp.base 0)
    (Tm.imp
       (Tm.app
          (Tm.app
             (Tm.typeApp
                (Tm.named "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                (Tp.base 0))
             (Tm.app (Tm.db 5) (Tm.db 0)))
          (Tm.app (Tm.db 5) (Tm.db 2)))
       (Tm.app
          (Tm.typeApp
             (Tm.named "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099")
             (Tp.var 0))
          (Tm.lam
             (Tp.var 0)
             (Tm.app
                fragment10
                (Tm.app
                   (Tm.app
                      (Tm.typeApp
                         (Tm.named
                            "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                         (Tp.var 0))
                      (Tm.app (Tm.app (Tm.db 4) (Tm.db 1)) (Tm.db 0)))
                   (Tm.db 2))))))

private def fragment20 : Tm :=
  Tm.app
    (Tm.app
       (Tm.app
          (Tm.app
             (Tm.app
                (Tm.app
                   (Tm.typeApp
                      (Tm.named
                         "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                      (Tp.var 0))
                   (Tm.db 6))
                (Tm.db 5))
             (Tm.db 4))
          (Tm.db 3))
       (Tm.db 6))
    (Tm.db 1)

private def fragment21 : Tm :=
  Tm.app
    (Tm.app
       (Tm.app
          (Tm.app
             (Tm.app
                (Tm.app
                   (Tm.typeApp
                      (Tm.named
                         "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                      (Tp.var 0))
                   (Tm.db 6))
                (Tm.db 5))
             (Tm.db 4))
          (Tm.db 3))
       (Tm.db 6))
    (Tm.db 0)

private def fragment22 : Tm :=
  Tm.all
    (Tp.var 0)
    (Tm.all
       (Tp.var 0)
       (Tm.imp
          (Tm.app
             (Tm.app
                (Tm.app
                   (Tm.app
                      (Tm.app
                         (Tm.app
                            (Tm.typeApp
                               (Tm.named
                                  "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                               (Tp.var 0))
                            (Tm.db 7))
                         (Tm.db 6))
                      (Tm.db 5))
                   (Tm.db 4))
                (Tm.db 2))
             (Tm.db 1))
          (Tm.imp
             (Tm.app
                (Tm.app
                   (Tm.app
                      (Tm.app
                         (Tm.app
                            (Tm.app
                               (Tm.typeApp
                                  (Tm.named
                                     "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                  (Tp.var 0))
                               (Tm.db 7))
                            (Tm.db 6))
                         (Tm.db 5))
                      (Tm.db 4))
                   (Tm.db 2))
                (Tm.db 0))
             (Tm.app
                (Tm.app
                   (Tm.typeApp
                      (Tm.named
                         "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                      (Tp.var 0))
                   (Tm.db 1))
                (Tm.db 0)))))

private def fragment23 : Tm :=
  Tm.app
    (Tm.app
       (Tm.app
          (Tm.app
             (Tm.app
                (Tm.app
                   (Tm.typeApp
                      (Tm.named
                         "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                      (Tp.var 0))
                   (Tm.db 7))
                (Tm.db 6))
             (Tm.db 5))
          (Tm.db 4))
       (Tm.app (Tm.db 6) (Tm.db 2)))
    (Tm.db 1)

private def fragment24 : Tm :=
  Tm.app
    (Tm.named "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
    (Tm.app
       (Tm.app
          (Tm.app
             (Tm.app
                (Tm.app
                   (Tm.app
                      (Tm.typeApp
                         (Tm.named
                            "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                         (Tp.var 0))
                      (Tm.db 8))
                   (Tm.db 7))
                (Tm.db 6))
             (Tm.db 5))
          (Tm.db 3))
       (Tm.db 0))

private def fragment25 : Tm :=
  Tm.app
    fragment24
    (Tm.app
       (Tm.app
          (Tm.typeApp
             (Tm.named "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
             (Tp.var 0))
          (Tm.app (Tm.app (Tm.db 5) (Tm.db 3)) (Tm.db 0)))
       (Tm.db 2))

private def fragment26 : Tm :=
  Tm.app
    (Tm.app
       (Tm.app
          (Tm.app
             (Tm.app
                (Tm.app
                   (Tm.typeApp
                      (Tm.named
                         "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                      (Tp.var 0))
                   (Tm.db 9))
                (Tm.db 8))
             (Tm.db 7))
          (Tm.db 6))
       (Tm.db 4))
    (Tm.db 0)

private def fragment27 : Tm :=
  Tm.app
    (Tm.app
       (Tm.app
          (Tm.app
             (Tm.app
                (Tm.app
                   (Tm.typeApp
                      (Tm.named
                         "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                      (Tp.var 0))
                   (Tm.db 9))
                (Tm.db 8))
             (Tm.db 7))
          (Tm.db 6))
       (Tm.db 4))
    (Tm.db 1)

private def fragment28 : Tm :=
  Tm.app
    (Tm.app
       (Tm.app
          (Tm.app
             (Tm.app
                (Tm.app
                   (Tm.typeApp
                      (Tm.named
                         "07c6d5bb8b1b51acf568b644d496c3805612be5b440432b88ee69c28280f8c5d")
                      (Tp.var 0))
                   (Tm.db 5))
                (Tm.db 4))
             (Tm.db 3))
          (Tm.db 2))
       (Tm.db 1))
    (Tm.db 0)

private def fragment29 : Tm :=
  Tm.app
    (Tm.app
       (Tm.app
          (Tm.app
             (Tm.app
                (Tm.app
                   (Tm.typeApp
                      (Tm.named
                         "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                      (Tp.var 0))
                   (Tm.db 5))
                (Tm.db 4))
             (Tm.db 3))
          (Tm.db 2))
       (Tm.db 0))
    fragment28

private def fragment30 : Tm :=
  Tm.app
    (Tm.app
       (Tm.app
          (Tm.app
             (Tm.app
                (Tm.app
                   (Tm.typeApp
                      (Tm.named
                         "07c6d5bb8b1b51acf568b644d496c3805612be5b440432b88ee69c28280f8c5d")
                      (Tp.var 0))
                   (Tm.db 4))
                (Tm.db 3))
             (Tm.db 2))
          (Tm.db 1))
       (Tm.db 0))
    (Tm.db 4)

private def fragment31 : Tm :=
  Tm.app
    (Tm.app
       (Tm.typeApp
          (Tm.named "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
          (Tp.var 0))
       (Tm.db 2))
    fragment30

private def fragment32 : Tm := Tm.app (Tm.app (Tm.db 2) (Tm.db 0)) fragment28

private def fragment33 : Tm :=
  Tm.app
    (Tm.app
       (Tm.app
          (Tm.app
             (Tm.app
                (Tm.app
                   (Tm.typeApp
                      (Tm.named
                         "07c6d5bb8b1b51acf568b644d496c3805612be5b440432b88ee69c28280f8c5d")
                      (Tp.var 0))
                   (Tm.db 5))
                (Tm.db 4))
             (Tm.db 3))
          (Tm.db 2))
       (Tm.db 1))
    (Tm.app (Tm.db 4) (Tm.db 0))

private def fragment34 : Tm :=
  Tm.all
    (Tp.base 0)
    (Tm.imp
       (Tm.app
          (Tm.app
             (Tm.app
                (Tm.named "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                (Tm.db 5))
             (Tm.db 4))
          (Tm.db 0))
       (Tm.app
          (Tm.app
             (Tm.typeApp
                (Tm.named "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                (Tp.var 0))
             fragment32)
          fragment33))

private def fragment35 : Tm :=
  Tm.app
    (Tm.app
       (Tm.app
          (Tm.app
             (Tm.app
                (Tm.app
                   (Tm.typeApp
                      (Tm.named
                         "07c6d5bb8b1b51acf568b644d496c3805612be5b440432b88ee69c28280f8c5d")
                      (Tp.var 0))
                   (Tm.db 6))
                (Tm.db 5))
             (Tm.db 4))
          (Tm.db 3))
       (Tm.db 2))
    (Tm.db 0)

private def fragment36 : Tm :=
  Tm.app
    (Tm.typeApp
       (Tm.named "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
       (Tp.var 0))
    fragment35

private def fragment37 : Tm :=
  Tm.all
    (Tp.arr (Tp.base 0) (Tp.var 0))
    (Tm.imp
       (Tm.app
          (Tm.app
             (Tm.typeApp
                (Tm.named "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                (Tp.var 0))
             (Tm.db 3))
          (Tm.app (Tm.db 0) (Tm.db 5)))
       (Tm.imp
          (Tm.all
             (Tp.base 0)
             (Tm.imp
                (Tm.app
                   (Tm.app
                      (Tm.app
                         (Tm.named
                            "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                         (Tm.db 6))
                      (Tm.db 5))
                   (Tm.db 0))
                (Tm.app
                   (Tm.app
                      (Tm.typeApp
                         (Tm.named
                            "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                         (Tp.var 0))
                      (Tm.app (Tm.app (Tm.db 3) (Tm.db 0)) (Tm.app (Tm.db 1) (Tm.db 0))))
                   (Tm.app (Tm.db 1) (Tm.app (Tm.db 5) (Tm.db 0))))))
          (Tm.all
             (Tp.base 0)
             (Tm.imp
                (Tm.app
                   (Tm.app
                      (Tm.app
                         (Tm.named
                            "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                         (Tm.db 6))
                      (Tm.db 5))
                   (Tm.db 0))
                (Tm.app fragment36 (Tm.app (Tm.db 1) (Tm.db 0)))))))

private def fragment38 : Tm :=
  Tm.lam
    (Tp.arr (Tp.base 0) (Tp.var 0))
    (Tm.app
       (Tm.app
          (Tm.named "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
          (Tm.app
             (Tm.app
                (Tm.typeApp
                   (Tm.named "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                   (Tp.var 0))
                (Tm.db 3))
             (Tm.app (Tm.db 0) (Tm.db 5))))
       (Tm.app
          (Tm.app
             (Tm.named "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
             (Tm.all
                (Tp.base 0)
                (Tm.imp
                   (Tm.app
                      (Tm.app
                         (Tm.app
                            (Tm.named
                               "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                            (Tm.db 6))
                         (Tm.db 5))
                      (Tm.db 0))
                   (Tm.app
                      (Tm.app
                         (Tm.typeApp
                            (Tm.named
                               "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                            (Tp.var 0))
                         (Tm.app (Tm.app (Tm.db 3) (Tm.db 0)) (Tm.app (Tm.db 1) (Tm.db 0))))
                      (Tm.app (Tm.db 1) (Tm.app (Tm.db 5) (Tm.db 0)))))))
          (Tm.all
             (Tp.arr (Tp.base 0) (Tp.var 0))
             (Tm.imp
                (Tm.app
                   (Tm.app
                      (Tm.typeApp
                         (Tm.named
                            "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                         (Tp.var 0))
                      (Tm.db 4))
                   (Tm.app (Tm.db 0) (Tm.db 6)))
                (Tm.imp
                   (Tm.all
                      (Tp.base 0)
                      (Tm.imp
                         (Tm.app
                            (Tm.app
                               (Tm.app
                                  (Tm.named
                                     "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                  (Tm.db 7))
                               (Tm.db 6))
                            (Tm.db 0))
                         (Tm.app
                            (Tm.app
                               (Tm.typeApp
                                  (Tm.named
                                     "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                  (Tp.var 0))
                               (Tm.app (Tm.app (Tm.db 4) (Tm.db 0)) (Tm.app (Tm.db 1) (Tm.db 0))))
                            (Tm.app (Tm.db 1) (Tm.app (Tm.db 6) (Tm.db 0))))))
                   (Tm.all
                      (Tp.base 0)
                      (Tm.imp
                         (Tm.app
                            (Tm.app
                               (Tm.app
                                  (Tm.named
                                     "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                  (Tm.db 7))
                               (Tm.db 6))
                            (Tm.db 0))
                         (Tm.app
                            (Tm.app
                               (Tm.typeApp
                                  (Tm.named
                                     "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                  (Tp.var 0))
                               (Tm.app (Tm.db 2) (Tm.db 0)))
                            (Tm.app (Tm.db 1) (Tm.db 0))))))))))

def ncAnd : Item :=
  Item.definition
    "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738"
    (Tp.arr Tp.prop (Tp.arr Tp.prop Tp.prop))
    (Tm.lam
       Tp.prop
       (Tm.lam
          Tp.prop
          (Tm.all Tp.prop (Tm.imp (Tm.imp (Tm.db 2) (Tm.imp (Tm.db 1) (Tm.db 0))) (Tm.db 0)))))

def naturalClosure : Item :=
  Item.definition
    "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be"
    (Tp.arr (Tp.base 0) (Tp.arr (Tp.arr (Tp.base 0) (Tp.base 0)) (Tp.arr (Tp.base 0) Tp.prop)))
    (Tm.lam
       (Tp.base 0)
       (Tm.lam
          (Tp.arr (Tp.base 0) (Tp.base 0))
          (Tm.lam
             (Tp.base 0)
             (Tm.all
                (Tp.arr (Tp.base 0) Tp.prop)
                (Tm.imp
                   (Tm.app (Tm.db 0) (Tm.db 3))
                   (Tm.imp
                      (Tm.all
                         (Tp.base 0)
                         (Tm.imp
                            (Tm.app (Tm.db 1) (Tm.db 0))
                            (Tm.app (Tm.db 1) (Tm.app (Tm.db 3) (Tm.db 0)))))
                      (Tm.app (Tm.db 0) (Tm.db 1))))))))

def ncAndIntro : Item :=
  Item.theorem_
    "7f6246d08629eeb16eab93529ffe4f929f43344833ab88c7786393693520e82b"
    (Tm.all
       Tp.prop
       (Tm.all
          Tp.prop
          (Tm.imp
             (Tm.db 1)
             (Tm.imp
                (Tm.db 0)
                (Tm.app
                   (Tm.app
                      (Tm.named
                         "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
                      (Tm.db 1))
                   (Tm.db 0))))))
    (Pf.termLam
       Tp.prop
       (Pf.termLam
          Tp.prop
          (Pf.proofLam
             (Tm.db 1)
             (Pf.proofLam
                (Tm.db 0)
                (Pf.termLam
                   Tp.prop
                   (Pf.proofLam
                      (Tm.imp (Tm.db 2) (Tm.imp (Tm.db 1) (Tm.db 0)))
                      (Pf.proofApp (Pf.proofApp (Pf.hyp 0) (Pf.hyp 2)) (Pf.hyp 1))))))))

def ncAndLeft : Item :=
  Item.theorem_
    "eb8814e5b67181dcc2fdd7f757e9f1e3c90bcd9b3117f2bb9aa7650cdaac5b42"
    (Tm.all
       Tp.prop
       (Tm.all
          Tp.prop
          (Tm.imp
             (Tm.app
                (Tm.app
                   (Tm.named "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
                   (Tm.db 1))
                (Tm.db 0))
             (Tm.db 1))))
    (Pf.termLam
       Tp.prop
       (Pf.termLam
          Tp.prop
          (Pf.proofLam
             (Tm.app
                (Tm.app
                   (Tm.named "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
                   (Tm.db 1))
                (Tm.db 0))
             (Pf.proofApp
                (Pf.termApp (Pf.hyp 0) (Tm.db 1))
                (Pf.proofLam (Tm.db 1) (Pf.proofLam (Tm.db 0) (Pf.hyp 1)))))))

def ncAndRight : Item :=
  Item.theorem_
    "fec5ab340a042c8361bb0564ac980cfe10dabcf5c4aeacb0746c0daa4ac55417"
    (Tm.all
       Tp.prop
       (Tm.all
          Tp.prop
          (Tm.imp
             (Tm.app
                (Tm.app
                   (Tm.named "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
                   (Tm.db 1))
                (Tm.db 0))
             (Tm.db 0))))
    (Pf.termLam
       Tp.prop
       (Pf.termLam
          Tp.prop
          (Pf.proofLam
             (Tm.app
                (Tm.app
                   (Tm.named "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
                   (Tm.db 1))
                (Tm.db 0))
             (Pf.proofApp
                (Pf.termApp (Pf.hyp 0) (Tm.db 0))
                (Pf.proofLam (Tm.db 1) (Pf.proofLam (Tm.db 0) (Pf.hyp 0)))))))

def naturalClosureZero : Item :=
  Item.theorem_
    "a7a2e1cb291bdfdc11661c2875e62b3fb8fb502cb3c1f594c4e6f50789e4f911"
    (Tm.all
       (Tp.base 0)
       (Tm.all
          (Tp.arr (Tp.base 0) (Tp.base 0))
          (Tm.app
             (Tm.app
                (Tm.app
                   (Tm.named "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                   (Tm.db 1))
                (Tm.db 0))
             (Tm.db 1))))
    (Pf.termLam
       (Tp.base 0)
       (Pf.termLam
          (Tp.arr (Tp.base 0) (Tp.base 0))
          (Pf.termLam
             (Tp.arr (Tp.base 0) Tp.prop)
             (Pf.proofLam
                (Tm.app (Tm.db 0) (Tm.db 2))
                (Pf.proofLam
                   (Tm.all
                      (Tp.base 0)
                      (Tm.imp
                         (Tm.app (Tm.db 1) (Tm.db 0))
                         (Tm.app (Tm.db 1) (Tm.app (Tm.db 2) (Tm.db 0)))))
                   (Pf.hyp 1))))))

def naturalClosureSuccessor : Item :=
  Item.theorem_
    "877913cb39467cac5218f875864ba9d5f794a079e124c150a2aa99edb28f6861"
    (Tm.all
       (Tp.base 0)
       (Tm.all
          (Tp.arr (Tp.base 0) (Tp.base 0))
          (Tm.all
             (Tp.base 0)
             (Tm.imp
                (Tm.app
                   (Tm.app
                      (Tm.app
                         (Tm.named
                            "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                         (Tm.db 2))
                      (Tm.db 1))
                   (Tm.db 0))
                (Tm.app
                   (Tm.app
                      (Tm.app
                         (Tm.named
                            "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                         (Tm.db 2))
                      (Tm.db 1))
                   (Tm.app (Tm.db 1) (Tm.db 0)))))))
    (Pf.termLam
       (Tp.base 0)
       (Pf.termLam
          (Tp.arr (Tp.base 0) (Tp.base 0))
          (Pf.termLam
             (Tp.base 0)
             (Pf.proofLam
                (Tm.app
                   (Tm.app
                      (Tm.app
                         (Tm.named
                            "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                         (Tm.db 2))
                      (Tm.db 1))
                   (Tm.db 0))
                (Pf.termLam
                   (Tp.arr (Tp.base 0) Tp.prop)
                   (Pf.proofLam
                      (Tm.app (Tm.db 0) (Tm.db 3))
                      (Pf.proofLam
                         (Tm.all
                            (Tp.base 0)
                            (Tm.imp
                               (Tm.app (Tm.db 1) (Tm.db 0))
                               (Tm.app (Tm.db 1) (Tm.app (Tm.db 3) (Tm.db 0)))))
                         (Pf.proofApp
                            (Pf.termApp (Pf.hyp 0) (Tm.db 1))
                            (Pf.proofApp
                               (Pf.proofApp (Pf.termApp (Pf.hyp 2) (Tm.db 0)) (Pf.hyp 1))
                               (Pf.hyp 0))))))))))

def naturalClosureInduction : Item :=
  Item.theorem_
    "77e10b9988f12dc528ad73906107175925091da967df0552db1799b699955593"
    (Tm.all
       (Tp.base 0)
       (Tm.all
          (Tp.arr (Tp.base 0) (Tp.base 0))
          (Tm.all
             (Tp.arr (Tp.base 0) Tp.prop)
             (Tm.imp
                (Tm.app (Tm.db 0) (Tm.db 2))
                (Tm.imp
                   (Tm.all
                      (Tp.base 0)
                      (Tm.imp
                         (Tm.app
                            (Tm.app
                               (Tm.app
                                  (Tm.named
                                     "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                  (Tm.db 3))
                               (Tm.db 2))
                            (Tm.db 0))
                         (Tm.imp
                            (Tm.app (Tm.db 1) (Tm.db 0))
                            (Tm.app (Tm.db 1) (Tm.app (Tm.db 2) (Tm.db 0))))))
                   (Tm.all
                      (Tp.base 0)
                      (Tm.imp
                         (Tm.app
                            (Tm.app
                               (Tm.app
                                  (Tm.named
                                     "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                  (Tm.db 3))
                               (Tm.db 2))
                            (Tm.db 0))
                         (Tm.app (Tm.db 1) (Tm.db 0)))))))))
    (Pf.termLam
       (Tp.base 0)
       (Pf.termLam
          (Tp.arr (Tp.base 0) (Tp.base 0))
          (Pf.termLam
             (Tp.arr (Tp.base 0) Tp.prop)
             (Pf.proofLam
                (Tm.app (Tm.db 0) (Tm.db 2))
                (Pf.proofLam
                   (Tm.all
                      (Tp.base 0)
                      (Tm.imp
                         (Tm.app
                            (Tm.app
                               (Tm.app
                                  (Tm.named
                                     "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                  (Tm.db 3))
                               (Tm.db 2))
                            (Tm.db 0))
                         (Tm.imp
                            (Tm.app (Tm.db 1) (Tm.db 0))
                            (Tm.app (Tm.db 1) (Tm.app (Tm.db 2) (Tm.db 0))))))
                   (Pf.termLam
                      (Tp.base 0)
                      (Pf.proofLam
                         (Tm.app
                            (Tm.app
                               (Tm.app
                                  (Tm.named
                                     "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                  (Tm.db 3))
                               (Tm.db 2))
                            (Tm.db 0))
                         (Pf.proofApp
                            (Pf.proofLam
                               (Tm.app
                                  (Tm.app
                                     (Tm.named
                                        "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
                                     (Tm.app
                                        (Tm.app
                                           (Tm.app
                                              (Tm.named
                                                 "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                              (Tm.db 3))
                                           (Tm.db 2))
                                        (Tm.db 3)))
                                  (Tm.app (Tm.db 1) (Tm.db 3)))
                               (Pf.proofApp
                                  (Pf.proofLam
                                     (Tm.all
                                        (Tp.base 0)
                                        (Tm.imp
                                           (Tm.app
                                              (Tm.app
                                                 (Tm.named
                                                    "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
                                                 (Tm.app
                                                    (Tm.app
                                                       (Tm.app
                                                          (Tm.named
                                                             "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                                          (Tm.db 4))
                                                       (Tm.db 3))
                                                    (Tm.db 0)))
                                              (Tm.app (Tm.db 2) (Tm.db 0)))
                                           (Tm.app
                                              (Tm.app
                                                 (Tm.named
                                                    "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
                                                 (Tm.app
                                                    (Tm.app
                                                       (Tm.app
                                                          (Tm.named
                                                             "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                                          (Tm.db 4))
                                                       (Tm.db 3))
                                                    (Tm.app (Tm.db 3) (Tm.db 0))))
                                              (Tm.app (Tm.db 2) (Tm.app (Tm.db 3) (Tm.db 0))))))
                                     (Pf.proofApp
                                        (Pf.proofLam
                                           (Tm.app
                                              (Tm.app
                                                 (Tm.named
                                                    "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
                                                 (Tm.app
                                                    (Tm.app
                                                       (Tm.app
                                                          (Tm.named
                                                             "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                                          (Tm.db 3))
                                                       (Tm.db 2))
                                                    (Tm.db 0)))
                                              (Tm.app (Tm.db 1) (Tm.db 0)))
                                           (Pf.proofApp
                                              (Pf.termApp
                                                 (Pf.termApp
                                                    (Pf.known
                                                       "fec5ab340a042c8361bb0564ac980cfe10dabcf5c4aeacb0746c0daa4ac55417")
                                                    (Tm.app
                                                       (Tm.app
                                                          (Tm.app
                                                             (Tm.named
                                                                "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                                             (Tm.db 3))
                                                          (Tm.db 2))
                                                       (Tm.db 0)))
                                                 (Tm.app (Tm.db 1) (Tm.db 0)))
                                              (Pf.hyp 0)))
                                        (Pf.proofApp
                                           (Pf.proofApp
                                              (Pf.termApp
                                                 (Pf.hyp 2)
                                                 (Tm.lam
                                                    (Tp.base 0)
                                                    (Tm.app
                                                       (Tm.app
                                                          (Tm.named
                                                             "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
                                                          (Tm.app
                                                             (Tm.app
                                                                (Tm.app
                                                                   (Tm.named
                                                                      "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                                                   (Tm.db 4))
                                                                (Tm.db 3))
                                                             (Tm.db 0)))
                                                       (Tm.app (Tm.db 2) (Tm.db 0)))))
                                              (Pf.hyp 1))
                                           (Pf.hyp 0))))
                                  (Pf.termLam
                                     (Tp.base 0)
                                     (Pf.proofLam
                                        (Tm.app
                                           (Tm.app
                                              (Tm.named
                                                 "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
                                              (Tm.app
                                                 (Tm.app
                                                    (Tm.app
                                                       (Tm.named
                                                          "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                                       (Tm.db 4))
                                                    (Tm.db 3))
                                                 (Tm.db 0)))
                                           (Tm.app (Tm.db 2) (Tm.db 0)))
                                        (Pf.proofApp
                                           (Pf.proofLam
                                              (Tm.app
                                                 (Tm.app
                                                    (Tm.app
                                                       (Tm.named
                                                          "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                                       (Tm.db 4))
                                                    (Tm.db 3))
                                                 (Tm.db 0))
                                              (Pf.proofApp
                                                 (Pf.proofLam
                                                    (Tm.app (Tm.db 2) (Tm.db 0))
                                                    (Pf.proofApp
                                                       (Pf.proofApp
                                                          (Pf.termApp
                                                             (Pf.termApp
                                                                (Pf.known
                                                                   "7f6246d08629eeb16eab93529ffe4f929f43344833ab88c7786393693520e82b")
                                                                (Tm.app
                                                                   (Tm.app
                                                                      (Tm.app
                                                                         (Tm.named
                                                                            "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                                                         (Tm.db 4))
                                                                      (Tm.db 3))
                                                                   (Tm.app (Tm.db 3) (Tm.db 0))))
                                                             (Tm.app
                                                                (Tm.db 2)
                                                                (Tm.app (Tm.db 3) (Tm.db 0))))
                                                          (Pf.proofApp
                                                             (Pf.termApp
                                                                (Pf.termApp
                                                                   (Pf.termApp
                                                                      (Pf.known
                                                                         "877913cb39467cac5218f875864ba9d5f794a079e124c150a2aa99edb28f6861")
                                                                      (Tm.db 4))
                                                                   (Tm.db 3))
                                                                (Tm.db 0))
                                                             (Pf.hyp 1)))
                                                       (Pf.proofApp
                                                          (Pf.proofApp
                                                             (Pf.termApp (Pf.hyp 5) (Tm.db 0))
                                                             (Pf.hyp 1))
                                                          (Pf.hyp 0))))
                                                 (Pf.proofApp
                                                    (Pf.termApp
                                                       (Pf.termApp
                                                          (Pf.known
                                                             "fec5ab340a042c8361bb0564ac980cfe10dabcf5c4aeacb0746c0daa4ac55417")
                                                          (Tm.app
                                                             (Tm.app
                                                                (Tm.app
                                                                   (Tm.named
                                                                      "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                                                   (Tm.db 4))
                                                                (Tm.db 3))
                                                             (Tm.db 0)))
                                                       (Tm.app (Tm.db 2) (Tm.db 0)))
                                                    (Pf.hyp 1))))
                                           (Pf.proofApp
                                              (Pf.termApp
                                                 (Pf.termApp
                                                    (Pf.known
                                                       "eb8814e5b67181dcc2fdd7f757e9f1e3c90bcd9b3117f2bb9aa7650cdaac5b42")
                                                    (Tm.app
                                                       (Tm.app
                                                          (Tm.app
                                                             (Tm.named
                                                                "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                                             (Tm.db 4))
                                                          (Tm.db 3))
                                                       (Tm.db 0)))
                                                 (Tm.app (Tm.db 2) (Tm.db 0)))
                                              (Pf.hyp 0)))))))
                            (Pf.proofApp
                               (Pf.proofApp
                                  (Pf.termApp
                                     (Pf.termApp
                                        (Pf.known
                                           "7f6246d08629eeb16eab93529ffe4f929f43344833ab88c7786393693520e82b")
                                        (Tm.app
                                           (Tm.app
                                              (Tm.app
                                                 (Tm.named
                                                    "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                                 (Tm.db 3))
                                              (Tm.db 2))
                                           (Tm.db 3)))
                                     (Tm.app (Tm.db 1) (Tm.db 3)))
                                  (Pf.termApp
                                     (Pf.termApp
                                        (Pf.known
                                           "a7a2e1cb291bdfdc11661c2875e62b3fb8fb502cb3c1f594c4e6f50789e4f911")
                                        (Tm.db 3))
                                     (Tm.db 2)))
                               (Pf.hyp 2))))))))))

def nrFalse : Item :=
  Item.definition
    "5bf697cb0d1cdefbe881504469f6c48cc388994115b82514dfc4fb5e67ac1a87"
    Tp.prop
    (Tm.all Tp.prop (Tm.db 0))

def nrEq : Item :=
  Item.definition
    "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89"
    (Tp.all (Tp.arr (Tp.var 0) (Tp.arr (Tp.var 0) Tp.prop)))
    (Tm.typeLam
       (Tm.lam
          (Tp.var 0)
          (Tm.lam
             (Tp.var 0)
             (Tm.all
                (Tp.arr (Tp.var 0) Tp.prop)
                (Tm.imp (Tm.app (Tm.db 0) (Tm.db 2)) (Tm.app (Tm.db 0) (Tm.db 1)))))))

def nrExists : Item :=
  Item.definition
    "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099"
    (Tp.all (Tp.arr (Tp.arr (Tp.var 0) Tp.prop) Tp.prop))
    (Tm.typeLam
       (Tm.lam
          (Tp.arr (Tp.var 0) Tp.prop)
          (Tm.all
             Tp.prop
             (Tm.imp
                (Tm.all (Tp.var 0) (Tm.imp (Tm.app (Tm.db 2) (Tm.db 0)) (Tm.db 1)))
                (Tm.db 0)))))

def nrEqRefl : Item :=
  Item.theorem_
    "0f730be4ec19d9c14f6f80059c561f714dcecb54d8fa04f3570d0607e71d8331"
    (Tm.typeAll
       (Tm.all
          (Tp.var 0)
          (Tm.app
             (Tm.app
                (Tm.typeApp
                   (Tm.named "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                   (Tp.var 0))
                (Tm.db 0))
             (Tm.db 0))))
    (Pf.typeLam
       (Pf.termLam
          (Tp.var 0)
          (Pf.termLam
             (Tp.arr (Tp.var 0) Tp.prop)
             (Pf.proofLam (Tm.app (Tm.db 0) (Tm.db 1)) (Pf.hyp 0)))))

def nrEqSym : Item :=
  Item.theorem_
    "284ee58e7aea454281b73a0d0acb6efade8eeb4f2f3bf29aaf48a8fef862ceff"
    (Tm.typeAll
       (Tm.all
          (Tp.var 0)
          (Tm.all
             (Tp.var 0)
             (Tm.imp
                (Tm.app
                   (Tm.app
                      (Tm.typeApp
                         (Tm.named
                            "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                         (Tp.var 0))
                      (Tm.db 1))
                   (Tm.db 0))
                (Tm.app
                   (Tm.app
                      (Tm.typeApp
                         (Tm.named
                            "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                         (Tp.var 0))
                      (Tm.db 0))
                   (Tm.db 1))))))
    (Pf.typeLam
       (Pf.termLam
          (Tp.var 0)
          (Pf.termLam
             (Tp.var 0)
             (Pf.proofLam
                (Tm.app
                   (Tm.app
                      (Tm.typeApp
                         (Tm.named
                            "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                         (Tp.var 0))
                      (Tm.db 1))
                   (Tm.db 0))
                (Pf.proofApp
                   (Pf.termApp
                      (Pf.hyp 0)
                      (Tm.lam
                         (Tp.var 0)
                         (Tm.app
                            (Tm.app
                               (Tm.typeApp
                                  (Tm.named
                                     "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                  (Tp.var 0))
                               (Tm.db 0))
                            (Tm.db 2))))
                   (Pf.termApp
                      (Pf.typeApp
                         (Pf.known
                            "0f730be4ec19d9c14f6f80059c561f714dcecb54d8fa04f3570d0607e71d8331")
                         (Tp.var 0))
                      (Tm.db 1)))))))

def nrEqTrans : Item :=
  Item.theorem_
    "0224060d7b7d5b6b2e8e4157524c8e4a18e5d17073c5b2fb2bb0c2583274fbc7"
    (Tm.typeAll
       (Tm.all
          (Tp.var 0)
          (Tm.all
             (Tp.var 0)
             (Tm.all
                (Tp.var 0)
                (Tm.imp
                   (Tm.app
                      (Tm.app
                         (Tm.typeApp
                            (Tm.named
                               "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                            (Tp.var 0))
                         (Tm.db 2))
                      (Tm.db 1))
                   (Tm.imp
                      (Tm.app
                         (Tm.app
                            (Tm.typeApp
                               (Tm.named
                                  "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                               (Tp.var 0))
                            (Tm.db 1))
                         (Tm.db 0))
                      (Tm.app
                         (Tm.app
                            (Tm.typeApp
                               (Tm.named
                                  "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                               (Tp.var 0))
                            (Tm.db 2))
                         (Tm.db 0))))))))
    (Pf.typeLam
       (Pf.termLam
          (Tp.var 0)
          (Pf.termLam
             (Tp.var 0)
             (Pf.termLam
                (Tp.var 0)
                (Pf.proofLam
                   (Tm.app
                      (Tm.app
                         (Tm.typeApp
                            (Tm.named
                               "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                            (Tp.var 0))
                         (Tm.db 2))
                      (Tm.db 1))
                   (Pf.proofLam
                      (Tm.app
                         (Tm.app
                            (Tm.typeApp
                               (Tm.named
                                  "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                               (Tp.var 0))
                            (Tm.db 1))
                         (Tm.db 0))
                      (Pf.termLam
                         (Tp.arr (Tp.var 0) Tp.prop)
                         (Pf.proofLam
                            (Tm.app (Tm.db 0) (Tm.db 3))
                            (Pf.proofApp
                               (Pf.termApp (Pf.hyp 1) (Tm.db 0))
                               (Pf.proofApp (Pf.termApp (Pf.hyp 2) (Tm.db 0)) (Pf.hyp 0)))))))))))

def nrExistsIntro : Item :=
  Item.theorem_
    "cb01597ac16d6df38d6f584e549edd3603cd7abc72e2a1cfcc2ba44fc649758e"
    (Tm.typeAll
       (Tm.all
          (Tp.arr (Tp.var 0) Tp.prop)
          (Tm.all
             (Tp.var 0)
             (Tm.imp
                (Tm.app (Tm.db 1) (Tm.db 0))
                (Tm.app
                   (Tm.typeApp
                      (Tm.named
                         "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099")
                      (Tp.var 0))
                   (Tm.db 1))))))
    (Pf.typeLam
       (Pf.termLam
          (Tp.arr (Tp.var 0) Tp.prop)
          (Pf.termLam
             (Tp.var 0)
             (Pf.proofLam
                (Tm.app (Tm.db 1) (Tm.db 0))
                (Pf.termLam
                   Tp.prop
                   (Pf.proofLam
                      (Tm.all (Tp.var 0) (Tm.imp (Tm.app (Tm.db 3) (Tm.db 0)) (Tm.db 1)))
                      (Pf.proofApp (Pf.termApp (Pf.hyp 0) (Tm.db 1)) (Pf.hyp 1))))))))

def nrGraph : Item :=
  Item.definition
    "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688"
    (Tp.all
       (Tp.arr
          (Tp.base 0)
          (Tp.arr
             (Tp.arr (Tp.base 0) (Tp.base 0))
             (Tp.arr
                (Tp.var 0)
                (Tp.arr
                   (Tp.arr (Tp.base 0) (Tp.arr (Tp.var 0) (Tp.var 0)))
                   (Tp.arr (Tp.base 0) (Tp.arr (Tp.var 0) Tp.prop)))))))
    (Tm.typeLam
       (Tm.lam
          (Tp.base 0)
          (Tm.lam
             (Tp.arr (Tp.base 0) (Tp.base 0))
             (Tm.lam
                (Tp.var 0)
                (Tm.lam
                   (Tp.arr (Tp.base 0) (Tp.arr (Tp.var 0) (Tp.var 0)))
                   (Tm.lam
                      (Tp.base 0)
                      (Tm.lam
                         (Tp.var 0)
                         (Tm.all
                            (Tp.arr (Tp.base 0) (Tp.arr (Tp.var 0) Tp.prop))
                            (Tm.imp
                               (Tm.app (Tm.app (Tm.db 0) (Tm.db 6)) (Tm.db 4))
                               (Tm.imp
                                  (Tm.all
                                     (Tp.base 0)
                                     (Tm.all
                                        (Tp.var 0)
                                        (Tm.imp
                                           (Tm.app (Tm.app (Tm.db 2) (Tm.db 1)) (Tm.db 0))
                                           (Tm.app
                                              (Tm.app (Tm.db 2) (Tm.app (Tm.db 7) (Tm.db 1)))
                                              (Tm.app (Tm.app (Tm.db 5) (Tm.db 1)) (Tm.db 0))))))
                                  (Tm.app (Tm.app (Tm.db 0) (Tm.db 2)) (Tm.db 1))))))))))))

def nrGraphZero : Item :=
  Item.theorem_
    "87808ea7afe4abaac2f5537926b3f5aa22f42a8fd3ae8dbc26e5b2a1c8fdf8e6"
    (Tm.typeAll
       (Tm.all
          (Tp.base 0)
          (Tm.all
             (Tp.arr (Tp.base 0) (Tp.base 0))
             (Tm.all
                (Tp.var 0)
                (Tm.all
                   (Tp.arr (Tp.base 0) (Tp.arr (Tp.var 0) (Tp.var 0)))
                   (Tm.app
                      (Tm.app
                         (Tm.app
                            (Tm.app
                               (Tm.app
                                  (Tm.app
                                     (Tm.typeApp
                                        (Tm.named
                                           "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                        (Tp.var 0))
                                     (Tm.db 3))
                                  (Tm.db 2))
                               (Tm.db 1))
                            (Tm.db 0))
                         (Tm.db 3))
                      (Tm.db 1)))))))
    (Pf.typeLam
       (Pf.termLam
          (Tp.base 0)
          (Pf.termLam
             (Tp.arr (Tp.base 0) (Tp.base 0))
             (Pf.termLam
                (Tp.var 0)
                (Pf.termLam
                   (Tp.arr (Tp.base 0) (Tp.arr (Tp.var 0) (Tp.var 0)))
                   (Pf.termLam
                      (Tp.arr (Tp.base 0) (Tp.arr (Tp.var 0) Tp.prop))
                      (Pf.proofLam
                         (Tm.app (Tm.app (Tm.db 0) (Tm.db 4)) (Tm.db 2))
                         (Pf.proofLam
                            (Tm.all
                               (Tp.base 0)
                               (Tm.all
                                  (Tp.var 0)
                                  (Tm.imp
                                     (Tm.app (Tm.app (Tm.db 2) (Tm.db 1)) (Tm.db 0))
                                     (Tm.app
                                        (Tm.app (Tm.db 2) (Tm.app (Tm.db 5) (Tm.db 1)))
                                        (Tm.app (Tm.app (Tm.db 3) (Tm.db 1)) (Tm.db 0))))))
                            (Pf.hyp 1)))))))))

def nrGraphSuccessor : Item :=
  Item.theorem_
    "96c29789eac08b76f3030c1438fa2ff7ca40becb4c3216e4f228b35b1177143b"
    (Tm.typeAll
       (Tm.all
          (Tp.base 0)
          (Tm.all
             (Tp.arr (Tp.base 0) (Tp.base 0))
             (Tm.all
                (Tp.var 0)
                (Tm.all
                   (Tp.arr (Tp.base 0) (Tp.arr (Tp.var 0) (Tp.var 0)))
                   (Tm.all
                      (Tp.base 0)
                      (Tm.all
                         (Tp.var 0)
                         (Tm.imp
                            fragment0
                            (Tm.app
                               (Tm.app
                                  (Tm.app
                                     (Tm.app
                                        (Tm.app
                                           (Tm.app
                                              (Tm.typeApp
                                                 (Tm.named
                                                    "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                                 (Tp.var 0))
                                              (Tm.db 5))
                                           (Tm.db 4))
                                        (Tm.db 3))
                                     (Tm.db 2))
                                  (Tm.app (Tm.db 4) (Tm.db 1)))
                               (Tm.app (Tm.app (Tm.db 2) (Tm.db 1)) (Tm.db 0)))))))))))
    (Pf.typeLam
       (Pf.termLam
          (Tp.base 0)
          (Pf.termLam
             (Tp.arr (Tp.base 0) (Tp.base 0))
             (Pf.termLam
                (Tp.var 0)
                (Pf.termLam
                   (Tp.arr (Tp.base 0) (Tp.arr (Tp.var 0) (Tp.var 0)))
                   (Pf.termLam
                      (Tp.base 0)
                      (Pf.termLam
                         (Tp.var 0)
                         (Pf.proofLam
                            fragment0
                            (Pf.termLam
                               (Tp.arr (Tp.base 0) (Tp.arr (Tp.var 0) Tp.prop))
                               (Pf.proofLam
                                  (Tm.app (Tm.app (Tm.db 0) (Tm.db 6)) (Tm.db 4))
                                  (Pf.proofLam
                                     (Tm.all
                                        (Tp.base 0)
                                        (Tm.all
                                           (Tp.var 0)
                                           (Tm.imp
                                              (Tm.app (Tm.app (Tm.db 2) (Tm.db 1)) (Tm.db 0))
                                              (Tm.app
                                                 (Tm.app (Tm.db 2) (Tm.app (Tm.db 7) (Tm.db 1)))
                                                 (Tm.app
                                                    (Tm.app (Tm.db 5) (Tm.db 1))
                                                    (Tm.db 0))))))
                                     (Pf.proofApp
                                        (Pf.termApp (Pf.termApp (Pf.hyp 0) (Tm.db 2)) (Tm.db 1))
                                        (Pf.proofApp
                                           (Pf.proofApp
                                              (Pf.termApp (Pf.hyp 2) (Tm.db 0))
                                              (Pf.hyp 1))
                                           (Pf.hyp 0))))))))))))))

def nrGraphNatural : Item :=
  Item.theorem_
    "0c18ad07c050c2a11411a41a052edf0b03abaee9a9944d919b0661c4452a4e71"
    (Tm.typeAll
       (Tm.all
          (Tp.base 0)
          (Tm.all
             (Tp.arr (Tp.base 0) (Tp.base 0))
             (Tm.all
                (Tp.var 0)
                (Tm.all
                   (Tp.arr (Tp.base 0) (Tp.arr (Tp.var 0) (Tp.var 0)))
                   (Tm.all
                      (Tp.base 0)
                      (Tm.all
                         (Tp.var 0)
                         (Tm.imp
                            fragment0
                            (Tm.app
                               (Tm.app
                                  (Tm.app
                                     (Tm.named
                                        "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                     (Tm.db 5))
                                  (Tm.db 4))
                               (Tm.db 1))))))))))
    (Pf.typeLam
       (Pf.termLam
          (Tp.base 0)
          (Pf.termLam
             (Tp.arr (Tp.base 0) (Tp.base 0))
             (Pf.termLam
                (Tp.var 0)
                (Pf.termLam
                   (Tp.arr (Tp.base 0) (Tp.arr (Tp.var 0) (Tp.var 0)))
                   (Pf.termLam
                      (Tp.base 0)
                      (Pf.termLam
                         (Tp.var 0)
                         (Pf.proofLam
                            fragment0
                            (Pf.proofApp
                               (Pf.proofApp
                                  (Pf.termApp
                                     (Pf.hyp 0)
                                     (Tm.lam
                                        (Tp.base 0)
                                        (Tm.lam
                                           (Tp.var 0)
                                           (Tm.app
                                              (Tm.app
                                                 (Tm.app
                                                    (Tm.named
                                                       "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                                    (Tm.db 7))
                                                 (Tm.db 6))
                                              (Tm.db 1)))))
                                  (Pf.termApp
                                     (Pf.termApp
                                        (Pf.known
                                           "a7a2e1cb291bdfdc11661c2875e62b3fb8fb502cb3c1f594c4e6f50789e4f911")
                                        (Tm.db 5))
                                     (Tm.db 4)))
                               (Pf.termLam
                                  (Tp.base 0)
                                  (Pf.termLam
                                     (Tp.var 0)
                                     (Pf.proofLam
                                        (Tm.app
                                           (Tm.app
                                              (Tm.app
                                                 (Tm.named
                                                    "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                                 (Tm.db 7))
                                              (Tm.db 6))
                                           (Tm.db 1))
                                        (Pf.proofApp
                                           (Pf.termApp
                                              (Pf.termApp
                                                 (Pf.termApp
                                                    (Pf.known
                                                       "877913cb39467cac5218f875864ba9d5f794a079e124c150a2aa99edb28f6861")
                                                    (Tm.db 7))
                                                 (Tm.db 6))
                                              (Tm.db 1))
                                           (Pf.hyp 0))))))))))))))

def nrGraphExists : Item :=
  Item.theorem_
    "e9bc3463274b5a8e5dfe44cf95087e1baa1298d95aa1f8a771bfa5a4ae9b58bd"
    (Tm.typeAll
       (Tm.all
          (Tp.base 0)
          (Tm.all
             (Tp.arr (Tp.base 0) (Tp.base 0))
             (Tm.all
                (Tp.var 0)
                (Tm.all
                   (Tp.arr (Tp.base 0) (Tp.arr (Tp.var 0) (Tp.var 0)))
                   (Tm.all
                      (Tp.base 0)
                      (Tm.imp
                         (Tm.app
                            (Tm.app
                               (Tm.app
                                  (Tm.named
                                     "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                  (Tm.db 4))
                               (Tm.db 3))
                            (Tm.db 0))
                         (Tm.app
                            (Tm.typeApp
                               (Tm.named
                                  "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099")
                               (Tp.var 0))
                            (Tm.lam (Tp.var 0) fragment0)))))))))
    (Pf.typeLam
       (Pf.termLam
          (Tp.base 0)
          (Pf.termLam
             (Tp.arr (Tp.base 0) (Tp.base 0))
             (Pf.termLam
                (Tp.var 0)
                (Pf.termLam
                   (Tp.arr (Tp.base 0) (Tp.arr (Tp.var 0) (Tp.var 0)))
                   (Pf.termLam
                      (Tp.base 0)
                      (Pf.proofLam
                         (Tm.app
                            (Tm.app
                               (Tm.app
                                  (Tm.named
                                     "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                  (Tm.db 4))
                               (Tm.db 3))
                            (Tm.db 0))
                         (Pf.proofApp
                            (Pf.proofApp
                               (Pf.termApp (Pf.hyp 0) (Tm.lam (Tp.base 0) fragment3))
                               (Pf.proofApp
                                  (Pf.termApp
                                     (Pf.termApp
                                        (Pf.typeApp
                                           (Pf.known
                                              "cb01597ac16d6df38d6f584e549edd3603cd7abc72e2a1cfcc2ba44fc649758e")
                                           (Tp.var 0))
                                        (Tm.lam
                                           (Tp.var 0)
                                           (Tm.app
                                              (Tm.app
                                                 (Tm.app
                                                    (Tm.app
                                                       (Tm.app
                                                          (Tm.app
                                                             (Tm.typeApp
                                                                (Tm.named
                                                                   "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                                                (Tp.var 0))
                                                             (Tm.db 5))
                                                          (Tm.db 4))
                                                       (Tm.db 3))
                                                    (Tm.db 2))
                                                 (Tm.db 5))
                                              (Tm.db 0))))
                                     (Tm.db 2))
                                  (Pf.termApp
                                     (Pf.termApp
                                        (Pf.termApp
                                           (Pf.termApp
                                              (Pf.typeApp
                                                 (Pf.known
                                                    "87808ea7afe4abaac2f5537926b3f5aa22f42a8fd3ae8dbc26e5b2a1c8fdf8e6")
                                                 (Tp.var 0))
                                              (Tm.db 4))
                                           (Tm.db 3))
                                        (Tm.db 2))
                                     (Tm.db 1))))
                            (Pf.termLam
                               (Tp.base 0)
                               (Pf.proofLam
                                  fragment3
                                  (Pf.proofApp
                                     (Pf.termApp
                                        (Pf.hyp 0)
                                        (Tm.app
                                           (Tm.typeApp
                                              (Tm.named
                                                 "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099")
                                              (Tp.var 0))
                                           (Tm.lam
                                              (Tp.var 0)
                                              (Tm.app
                                                 (Tm.app
                                                    (Tm.app
                                                       (Tm.app
                                                          (Tm.app
                                                             (Tm.app
                                                                (Tm.typeApp
                                                                   (Tm.named
                                                                      "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                                                   (Tp.var 0))
                                                                (Tm.db 6))
                                                             (Tm.db 5))
                                                          (Tm.db 4))
                                                       (Tm.db 3))
                                                    (Tm.app (Tm.db 5) (Tm.db 1)))
                                                 (Tm.db 0)))))
                                     (Pf.termLam
                                        (Tp.var 0)
                                        (Pf.proofLam
                                           fragment1
                                           (Pf.proofApp
                                              (Pf.termApp
                                                 (Pf.termApp
                                                    (Pf.typeApp
                                                       (Pf.known
                                                          "cb01597ac16d6df38d6f584e549edd3603cd7abc72e2a1cfcc2ba44fc649758e")
                                                       (Tp.var 0))
                                                    (Tm.lam (Tp.var 0) fragment4))
                                                 (Tm.app (Tm.app (Tm.db 3) (Tm.db 1)) (Tm.db 0)))
                                              (Pf.proofApp
                                                 (Pf.termApp
                                                    (Pf.termApp
                                                       (Pf.termApp
                                                          (Pf.termApp
                                                             (Pf.termApp
                                                                (Pf.termApp
                                                                   (Pf.typeApp
                                                                      (Pf.known
                                                                         "96c29789eac08b76f3030c1438fa2ff7ca40becb4c3216e4f228b35b1177143b")
                                                                      (Tp.var 0))
                                                                   (Tm.db 6))
                                                                (Tm.db 5))
                                                             (Tm.db 4))
                                                          (Tm.db 3))
                                                       (Tm.db 1))
                                                    (Tm.db 0))
                                                 (Pf.hyp 0))))))))))))))))

def nrGraphZeroUnique : Item :=
  Item.theorem_
    "f91a57a5bd78694e5884aa1b325509ba1c324bb735928e38924bb7081d7e567b"
    (Tm.typeAll
       (Tm.all
          (Tp.base 0)
          (Tm.all
             (Tp.arr (Tp.base 0) (Tp.base 0))
             (Tm.imp
                (Tm.all
                   (Tp.base 0)
                   (Tm.imp
                      (Tm.app
                         (Tm.app
                            (Tm.typeApp
                               (Tm.named
                                  "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                               (Tp.base 0))
                            (Tm.app (Tm.db 1) (Tm.db 0)))
                         (Tm.db 2))
                      (Tm.named
                         "5bf697cb0d1cdefbe881504469f6c48cc388994115b82514dfc4fb5e67ac1a87")))
                (Tm.all
                   (Tp.var 0)
                   (Tm.all
                      (Tp.arr (Tp.base 0) (Tp.arr (Tp.var 0) (Tp.var 0)))
                      (Tm.all
                         (Tp.var 0)
                         (Tm.imp
                            fragment5
                            (Tm.app
                               (Tm.app
                                  (Tm.typeApp
                                     (Tm.named
                                        "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                     (Tp.var 0))
                                  (Tm.db 2))
                               (Tm.db 0))))))))))
    (Pf.typeLam
       (Pf.termLam
          (Tp.base 0)
          (Pf.termLam
             (Tp.arr (Tp.base 0) (Tp.base 0))
             (Pf.proofLam
                (Tm.all
                   (Tp.base 0)
                   (Tm.imp
                      (Tm.app
                         (Tm.app
                            (Tm.typeApp
                               (Tm.named
                                  "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                               (Tp.base 0))
                            (Tm.app (Tm.db 1) (Tm.db 0)))
                         (Tm.db 2))
                      (Tm.named
                         "5bf697cb0d1cdefbe881504469f6c48cc388994115b82514dfc4fb5e67ac1a87")))
                (Pf.termLam
                   (Tp.var 0)
                   (Pf.termLam
                      (Tp.arr (Tp.base 0) (Tp.arr (Tp.var 0) (Tp.var 0)))
                      (Pf.termLam
                         (Tp.var 0)
                         (Pf.proofLam
                            fragment5
                            (Pf.termLam
                               (Tp.arr (Tp.var 0) Tp.prop)
                               (Pf.proofLam
                                  (Tm.app (Tm.db 0) (Tm.db 3))
                                  (Pf.proofApp
                                     (Pf.proofApp
                                        (Pf.proofApp
                                           (Pf.termApp
                                              (Pf.hyp 1)
                                              (Tm.lam
                                                 (Tp.base 0)
                                                 (Tm.lam
                                                    (Tp.var 0)
                                                    (Tm.imp
                                                       (Tm.app
                                                          (Tm.app
                                                             (Tm.typeApp
                                                                (Tm.named
                                                                   "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                                (Tp.base 0))
                                                             (Tm.db 1))
                                                          (Tm.db 7))
                                                       (Tm.app (Tm.db 2) (Tm.db 0))))))
                                           (Pf.proofLam
                                              (Tm.app
                                                 (Tm.app
                                                    (Tm.typeApp
                                                       (Tm.named
                                                          "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                       (Tp.base 0))
                                                    (Tm.db 5))
                                                 (Tm.db 5))
                                              (Pf.hyp 1)))
                                        (Pf.termLam
                                           (Tp.base 0)
                                           (Pf.termLam
                                              (Tp.var 0)
                                              (Pf.proofLam
                                                 (Tm.imp
                                                    (Tm.app
                                                       (Tm.app
                                                          (Tm.typeApp
                                                             (Tm.named
                                                                "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                             (Tp.base 0))
                                                          (Tm.db 1))
                                                       (Tm.db 7))
                                                    (Tm.app (Tm.db 2) (Tm.db 0)))
                                                 (Pf.proofLam
                                                    (Tm.app
                                                       (Tm.app
                                                          (Tm.typeApp
                                                             (Tm.named
                                                                "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                             (Tp.base 0))
                                                          (Tm.app (Tm.db 6) (Tm.db 1)))
                                                       (Tm.db 7))
                                                    (Pf.termApp
                                                       (Pf.proofApp
                                                          (Pf.termApp (Pf.hyp 4) (Tm.db 1))
                                                          (Pf.hyp 0))
                                                       (Tm.app
                                                          (Tm.db 2)
                                                          (Tm.app
                                                             (Tm.app (Tm.db 4) (Tm.db 1))
                                                             (Tm.db 0)))))))))
                                     (Pf.termApp
                                        (Pf.typeApp
                                           (Pf.known
                                              "0f730be4ec19d9c14f6f80059c561f714dcecb54d8fa04f3570d0607e71d8331")
                                           (Tp.base 0))
                                        (Tm.db 5)))))))))))))

def nrGraphSuccessorInverse : Item :=
  Item.theorem_
    "b6f91526fffc2274b066d609cf61e85df750465fdcfcc883602660ea5efff74c"
    (Tm.typeAll
       (Tm.all
          (Tp.base 0)
          (Tm.all
             (Tp.arr (Tp.base 0) (Tp.base 0))
             (Tm.imp
                (Tm.all
                   (Tp.base 0)
                   (Tm.imp
                      (Tm.app
                         (Tm.app
                            (Tm.typeApp
                               (Tm.named
                                  "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                               (Tp.base 0))
                            (Tm.app (Tm.db 1) (Tm.db 0)))
                         (Tm.db 2))
                      (Tm.named
                         "5bf697cb0d1cdefbe881504469f6c48cc388994115b82514dfc4fb5e67ac1a87")))
                (Tm.imp
                   (Tm.all
                      (Tp.base 0)
                      (Tm.all
                         (Tp.base 0)
                         (Tm.imp
                            (Tm.app
                               (Tm.app
                                  (Tm.typeApp
                                     (Tm.named
                                        "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                     (Tp.base 0))
                                  (Tm.app (Tm.db 2) (Tm.db 1)))
                               (Tm.app (Tm.db 2) (Tm.db 0)))
                            (Tm.app
                               (Tm.app
                                  (Tm.typeApp
                                     (Tm.named
                                        "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                     (Tp.base 0))
                                  (Tm.db 1))
                               (Tm.db 0)))))
                   (Tm.all
                      (Tp.var 0)
                      (Tm.all
                         (Tp.arr (Tp.base 0) (Tp.arr (Tp.var 0) (Tp.var 0)))
                         (Tm.all
                            (Tp.base 0)
                            (Tm.all
                               (Tp.var 0)
                               (Tm.imp
                                  fragment6
                                  (Tm.app
                                     (Tm.typeApp
                                        (Tm.named
                                           "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099")
                                        (Tp.var 0))
                                     (Tm.lam
                                        (Tp.var 0)
                                        (Tm.app
                                           (Tm.app
                                              (Tm.named
                                                 "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
                                              fragment7)
                                           (Tm.app
                                              (Tm.app
                                                 (Tm.typeApp
                                                    (Tm.named
                                                       "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                    (Tp.var 0))
                                                 (Tm.app (Tm.app (Tm.db 3) (Tm.db 2)) (Tm.db 0)))
                                              (Tm.db 1)))))))))))))))
    (Pf.typeLam
       (Pf.termLam
          (Tp.base 0)
          (Pf.termLam
             (Tp.arr (Tp.base 0) (Tp.base 0))
             (Pf.proofLam
                (Tm.all
                   (Tp.base 0)
                   (Tm.imp
                      (Tm.app
                         (Tm.app
                            (Tm.typeApp
                               (Tm.named
                                  "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                               (Tp.base 0))
                            (Tm.app (Tm.db 1) (Tm.db 0)))
                         (Tm.db 2))
                      (Tm.named
                         "5bf697cb0d1cdefbe881504469f6c48cc388994115b82514dfc4fb5e67ac1a87")))
                (Pf.proofLam
                   (Tm.all
                      (Tp.base 0)
                      (Tm.all
                         (Tp.base 0)
                         (Tm.imp
                            (Tm.app
                               (Tm.app
                                  (Tm.typeApp
                                     (Tm.named
                                        "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                     (Tp.base 0))
                                  (Tm.app (Tm.db 2) (Tm.db 1)))
                               (Tm.app (Tm.db 2) (Tm.db 0)))
                            (Tm.app
                               (Tm.app
                                  (Tm.typeApp
                                     (Tm.named
                                        "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                     (Tp.base 0))
                                  (Tm.db 1))
                               (Tm.db 0)))))
                   (Pf.termLam
                      (Tp.var 0)
                      (Pf.termLam
                         (Tp.arr (Tp.base 0) (Tp.arr (Tp.var 0) (Tp.var 0)))
                         (Pf.termLam
                            (Tp.base 0)
                            (Pf.termLam
                               (Tp.var 0)
                               (Pf.proofLam
                                  fragment6
                                  (Pf.proofApp
                                     (Pf.proofLam
                                        (Tm.app
                                           (Tm.app
                                              (Tm.named
                                                 "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
                                              fragment8)
                                           fragment12)
                                        (Pf.proofApp
                                           (Pf.proofLam
                                              (Tm.all
                                                 (Tp.base 0)
                                                 (Tm.all
                                                    (Tp.var 0)
                                                    (Tm.imp
                                                       fragment15
                                                       (Tm.app
                                                          (Tm.app
                                                             (Tm.named
                                                                "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
                                                             fragment16)
                                                          fragment18))))
                                              (Pf.proofApp
                                                 (Pf.proofLam
                                                    (Tm.app
                                                       (Tm.app
                                                          (Tm.named
                                                             "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
                                                          fragment6)
                                                       fragment19)
                                                    (Pf.proofApp
                                                       (Pf.termApp
                                                          (Pf.proofApp
                                                             (Pf.termApp
                                                                (Pf.termApp
                                                                   (Pf.known
                                                                      "fec5ab340a042c8361bb0564ac980cfe10dabcf5c4aeacb0746c0daa4ac55417")
                                                                   fragment6)
                                                                fragment19)
                                                             (Pf.hyp 0))
                                                          (Tm.db 1))
                                                       (Pf.termApp
                                                          (Pf.typeApp
                                                             (Pf.known
                                                                "0f730be4ec19d9c14f6f80059c561f714dcecb54d8fa04f3570d0607e71d8331")
                                                             (Tp.base 0))
                                                          (Tm.app (Tm.db 4) (Tm.db 1)))))
                                                 (Pf.proofApp
                                                    (Pf.proofApp
                                                       (Pf.termApp
                                                          (Pf.hyp 2)
                                                          (Tm.lam
                                                             (Tp.base 0)
                                                             (Tm.lam (Tp.var 0) fragment15)))
                                                       (Pf.hyp 1))
                                                    (Pf.hyp 0))))
                                           (Pf.termLam
                                              (Tp.base 0)
                                              (Pf.termLam
                                                 (Tp.var 0)
                                                 (Pf.proofLam
                                                    fragment15
                                                    (Pf.proofApp
                                                       (Pf.proofLam
                                                          fragment9
                                                          (Pf.proofApp
                                                             (Pf.proofApp
                                                                (Pf.termApp
                                                                   (Pf.termApp
                                                                      (Pf.known
                                                                         "7f6246d08629eeb16eab93529ffe4f929f43344833ab88c7786393693520e82b")
                                                                      fragment16)
                                                                   fragment18)
                                                                (Pf.proofApp
                                                                   (Pf.termApp
                                                                      (Pf.termApp
                                                                         (Pf.termApp
                                                                            (Pf.termApp
                                                                               (Pf.termApp
                                                                                  (Pf.termApp
                                                                                     (Pf.typeApp
                                                                                        (Pf.known
                                                                                           "96c29789eac08b76f3030c1438fa2ff7ca40becb4c3216e4f228b35b1177143b")
                                                                                        (Tp.var
                                                                                           0))
                                                                                     (Tm.db 7))
                                                                                  (Tm.db 6))
                                                                               (Tm.db 5))
                                                                            (Tm.db 4))
                                                                         (Tm.db 1))
                                                                      (Tm.db 0))
                                                                   (Pf.hyp 0)))
                                                             (Pf.termLam
                                                                (Tp.base 0)
                                                                (Pf.proofLam
                                                                   (Tm.app
                                                                      (Tm.app
                                                                         (Tm.typeApp
                                                                            (Tm.named
                                                                               "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                                            (Tp.base 0))
                                                                         (Tm.app
                                                                            (Tm.db 7)
                                                                            (Tm.db 0)))
                                                                      (Tm.app
                                                                         (Tm.db 7)
                                                                         (Tm.db 2)))
                                                                   (Pf.proofApp
                                                                      (Pf.proofLam
                                                                         (Tm.app
                                                                            (Tm.app
                                                                               (Tm.typeApp
                                                                                  (Tm.named
                                                                                     "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                                                  (Tp.base 0))
                                                                               (Tm.db 0))
                                                                            (Tm.db 2))
                                                                         (Pf.proofApp
                                                                            (Pf.termApp
                                                                               (Pf.termApp
                                                                                  (Pf.typeApp
                                                                                     (Pf.known
                                                                                        "cb01597ac16d6df38d6f584e549edd3603cd7abc72e2a1cfcc2ba44fc649758e")
                                                                                     (Tp.var 0))
                                                                                  fragment17)
                                                                               (Tm.db 1))
                                                                            (Pf.proofApp
                                                                               (Pf.proofApp
                                                                                  (Pf.termApp
                                                                                     (Pf.termApp
                                                                                        (Pf.known
                                                                                           "7f6246d08629eeb16eab93529ffe4f929f43344833ab88c7786393693520e82b")
                                                                                        (Tm.app
                                                                                           (Tm.app
                                                                                              (Tm.app
                                                                                                 (Tm.app
                                                                                                    (Tm.app
                                                                                                       (Tm.app
                                                                                                          (Tm.typeApp
                                                                                                             (Tm.named
                                                                                                                "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                                                                                             (Tp.var
                                                                                                                0))
                                                                                                          (Tm.db
                                                                                                             8))
                                                                                                       (Tm.db
                                                                                                          7))
                                                                                                    (Tm.db
                                                                                                       6))
                                                                                                 (Tm.db
                                                                                                    5))
                                                                                              (Tm.db
                                                                                                 0))
                                                                                           (Tm.db
                                                                                              1)))
                                                                                     (Tm.app
                                                                                        (Tm.app
                                                                                           (Tm.typeApp
                                                                                              (Tm.named
                                                                                                 "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                                                              (Tp.var
                                                                                                 0))
                                                                                           (Tm.app
                                                                                              (Tm.app
                                                                                                 (Tm.db
                                                                                                    5)
                                                                                                 (Tm.db
                                                                                                    0))
                                                                                              (Tm.db
                                                                                                 1)))
                                                                                        (Tm.app
                                                                                           (Tm.app
                                                                                              (Tm.db
                                                                                                 5)
                                                                                              (Tm.db
                                                                                                 2))
                                                                                           (Tm.db
                                                                                              1))))
                                                                                  (Pf.proofApp
                                                                                     (Pf.termApp
                                                                                        (Pf.proofApp
                                                                                           (Pf.termApp
                                                                                              (Pf.termApp
                                                                                                 (Pf.typeApp
                                                                                                    (Pf.known
                                                                                                       "284ee58e7aea454281b73a0d0acb6efade8eeb4f2f3bf29aaf48a8fef862ceff")
                                                                                                    (Tp.base
                                                                                                       0))
                                                                                                 (Tm.db
                                                                                                    0))
                                                                                              (Tm.db
                                                                                                 2))
                                                                                           (Pf.hyp
                                                                                              0))
                                                                                        (Tm.lam
                                                                                           (Tp.base
                                                                                              0)
                                                                                           (Tm.app
                                                                                              (Tm.app
                                                                                                 (Tm.app
                                                                                                    (Tm.app
                                                                                                       (Tm.app
                                                                                                          (Tm.app
                                                                                                             (Tm.typeApp
                                                                                                                (Tm.named
                                                                                                                   "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                                                                                                (Tp.var
                                                                                                                   0))
                                                                                                             (Tm.db
                                                                                                                9))
                                                                                                          (Tm.db
                                                                                                             8))
                                                                                                       (Tm.db
                                                                                                          7))
                                                                                                    (Tm.db
                                                                                                       6))
                                                                                                 (Tm.db
                                                                                                    0))
                                                                                              (Tm.db
                                                                                                 2))))
                                                                                     (Pf.hyp 2)))
                                                                               (Pf.proofApp
                                                                                  (Pf.termApp
                                                                                     (Pf.hyp 0)
                                                                                     (Tm.lam
                                                                                        (Tp.base
                                                                                           0)
                                                                                        (Tm.app
                                                                                           (Tm.app
                                                                                              (Tm.typeApp
                                                                                                 (Tm.named
                                                                                                    "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                                                                 (Tp.var
                                                                                                    0))
                                                                                              (Tm.app
                                                                                                 (Tm.app
                                                                                                    (Tm.db
                                                                                                       6)
                                                                                                    (Tm.db
                                                                                                       1))
                                                                                                 (Tm.db
                                                                                                    2)))
                                                                                           (Tm.app
                                                                                              (Tm.app
                                                                                                 (Tm.db
                                                                                                    6)
                                                                                                 (Tm.db
                                                                                                    0))
                                                                                              (Tm.db
                                                                                                 2)))))
                                                                                  (Pf.termApp
                                                                                     (Pf.typeApp
                                                                                        (Pf.known
                                                                                           "0f730be4ec19d9c14f6f80059c561f714dcecb54d8fa04f3570d0607e71d8331")
                                                                                        (Tp.var
                                                                                           0))
                                                                                     (Tm.app
                                                                                        (Tm.app
                                                                                           (Tm.db
                                                                                              5)
                                                                                           (Tm.db
                                                                                              0))
                                                                                        (Tm.db
                                                                                           1)))))))
                                                                      (Pf.proofApp
                                                                         (Pf.termApp
                                                                            (Pf.termApp
                                                                               (Pf.hyp 5)
                                                                               (Tm.db 0))
                                                                            (Tm.db 2))
                                                                         (Pf.hyp 0)))))))
                                                       (Pf.proofApp
                                                          (Pf.termApp
                                                             (Pf.termApp
                                                                (Pf.known
                                                                   "eb8814e5b67181dcc2fdd7f757e9f1e3c90bcd9b3117f2bb9aa7650cdaac5b42")
                                                                fragment9)
                                                             fragment14)
                                                          (Pf.hyp 0))))))))
                                     (Pf.proofApp
                                        (Pf.proofApp
                                           (Pf.termApp
                                              (Pf.termApp
                                                 (Pf.known
                                                    "7f6246d08629eeb16eab93529ffe4f929f43344833ab88c7786393693520e82b")
                                                 fragment8)
                                              fragment12)
                                           (Pf.termApp
                                              (Pf.termApp
                                                 (Pf.termApp
                                                    (Pf.termApp
                                                       (Pf.typeApp
                                                          (Pf.known
                                                             "87808ea7afe4abaac2f5537926b3f5aa22f42a8fd3ae8dbc26e5b2a1c8fdf8e6")
                                                          (Tp.var 0))
                                                       (Tm.db 5))
                                                    (Tm.db 4))
                                                 (Tm.db 3))
                                              (Tm.db 2)))
                                        (Pf.termLam
                                           (Tp.base 0)
                                           (Pf.proofLam
                                              (Tm.app
                                                 (Tm.app
                                                    (Tm.typeApp
                                                       (Tm.named
                                                          "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                       (Tp.base 0))
                                                    (Tm.app (Tm.db 5) (Tm.db 0)))
                                                 (Tm.db 6))
                                              (Pf.termApp
                                                 (Pf.proofApp
                                                    (Pf.termApp (Pf.hyp 3) (Tm.db 0))
                                                    (Pf.hyp 0))
                                                 fragment11)))))))))))))))

def nrGraphFunctional : Item :=
  Item.theorem_
    "653fd64163dedfee84cae7ddf348949c2cfc59c5db33f3b662cc8fba4f41634a"
    (Tm.typeAll
       (Tm.all
          (Tp.base 0)
          (Tm.all
             (Tp.arr (Tp.base 0) (Tp.base 0))
             (Tm.imp
                (Tm.all
                   (Tp.base 0)
                   (Tm.imp
                      (Tm.app
                         (Tm.app
                            (Tm.typeApp
                               (Tm.named
                                  "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                               (Tp.base 0))
                            (Tm.app (Tm.db 1) (Tm.db 0)))
                         (Tm.db 2))
                      (Tm.named
                         "5bf697cb0d1cdefbe881504469f6c48cc388994115b82514dfc4fb5e67ac1a87")))
                (Tm.imp
                   (Tm.all
                      (Tp.base 0)
                      (Tm.all
                         (Tp.base 0)
                         (Tm.imp
                            (Tm.app
                               (Tm.app
                                  (Tm.typeApp
                                     (Tm.named
                                        "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                     (Tp.base 0))
                                  (Tm.app (Tm.db 2) (Tm.db 1)))
                               (Tm.app (Tm.db 2) (Tm.db 0)))
                            (Tm.app
                               (Tm.app
                                  (Tm.typeApp
                                     (Tm.named
                                        "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                     (Tp.base 0))
                                  (Tm.db 1))
                               (Tm.db 0)))))
                   (Tm.all
                      (Tp.var 0)
                      (Tm.all
                         (Tp.arr (Tp.base 0) (Tp.arr (Tp.var 0) (Tp.var 0)))
                         (Tm.all
                            (Tp.base 0)
                            (Tm.imp
                               (Tm.app
                                  (Tm.app
                                     (Tm.app
                                        (Tm.named
                                           "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                        (Tm.db 4))
                                     (Tm.db 3))
                                  (Tm.db 0))
                               (Tm.all
                                  (Tp.var 0)
                                  (Tm.all
                                     (Tp.var 0)
                                     (Tm.imp
                                        (Tm.app
                                           (Tm.app
                                              (Tm.app
                                                 (Tm.app
                                                    (Tm.app
                                                       (Tm.app
                                                          (Tm.typeApp
                                                             (Tm.named
                                                                "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                                             (Tp.var 0))
                                                          (Tm.db 6))
                                                       (Tm.db 5))
                                                    (Tm.db 4))
                                                 (Tm.db 3))
                                              (Tm.db 2))
                                           (Tm.db 1))
                                        (Tm.imp
                                           fragment7
                                           (Tm.app
                                              (Tm.app
                                                 (Tm.typeApp
                                                    (Tm.named
                                                       "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                    (Tp.var 0))
                                                 (Tm.db 1))
                                              (Tm.db 0)))))))))))))))
    (Pf.typeLam
       (Pf.termLam
          (Tp.base 0)
          (Pf.termLam
             (Tp.arr (Tp.base 0) (Tp.base 0))
             (Pf.proofLam
                (Tm.all
                   (Tp.base 0)
                   (Tm.imp
                      (Tm.app
                         (Tm.app
                            (Tm.typeApp
                               (Tm.named
                                  "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                               (Tp.base 0))
                            (Tm.app (Tm.db 1) (Tm.db 0)))
                         (Tm.db 2))
                      (Tm.named
                         "5bf697cb0d1cdefbe881504469f6c48cc388994115b82514dfc4fb5e67ac1a87")))
                (Pf.proofLam
                   (Tm.all
                      (Tp.base 0)
                      (Tm.all
                         (Tp.base 0)
                         (Tm.imp
                            (Tm.app
                               (Tm.app
                                  (Tm.typeApp
                                     (Tm.named
                                        "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                     (Tp.base 0))
                                  (Tm.app (Tm.db 2) (Tm.db 1)))
                               (Tm.app (Tm.db 2) (Tm.db 0)))
                            (Tm.app
                               (Tm.app
                                  (Tm.typeApp
                                     (Tm.named
                                        "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                     (Tp.base 0))
                                  (Tm.db 1))
                               (Tm.db 0)))))
                   (Pf.termLam
                      (Tp.var 0)
                      (Pf.termLam
                         (Tp.arr (Tp.base 0) (Tp.arr (Tp.var 0) (Tp.var 0)))
                         (Pf.termLam
                            (Tp.base 0)
                            (Pf.proofLam
                               (Tm.app
                                  (Tm.app
                                     (Tm.app
                                        (Tm.named
                                           "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                        (Tm.db 4))
                                     (Tm.db 3))
                                  (Tm.db 0))
                               (Pf.proofApp
                                  (Pf.proofLam
                                     (Tm.all
                                        (Tp.var 0)
                                        (Tm.all
                                           (Tp.var 0)
                                           (Tm.imp
                                              fragment20
                                              (Tm.imp
                                                 fragment21
                                                 (Tm.app
                                                    (Tm.app
                                                       (Tm.typeApp
                                                          (Tm.named
                                                             "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                          (Tp.var 0))
                                                       (Tm.db 1))
                                                    (Tm.db 0))))))
                                     (Pf.proofApp
                                        (Pf.proofLam
                                           (Tm.all
                                              (Tp.base 0)
                                              (Tm.imp
                                                 (Tm.app
                                                    (Tm.app
                                                       (Tm.app
                                                          (Tm.named
                                                             "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                                          (Tm.db 5))
                                                       (Tm.db 4))
                                                    (Tm.db 0))
                                                 (Tm.imp
                                                    fragment22
                                                    (Tm.all
                                                       (Tp.var 0)
                                                       (Tm.all
                                                          (Tp.var 0)
                                                          (Tm.imp
                                                             fragment23
                                                             (Tm.imp
                                                                fragment4
                                                                (Tm.app
                                                                   (Tm.app
                                                                      (Tm.typeApp
                                                                         (Tm.named
                                                                            "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                                         (Tp.var 0))
                                                                      (Tm.db 1))
                                                                   (Tm.db 0)))))))))
                                           (Pf.proofApp
                                              (Pf.termApp
                                                 (Pf.proofApp
                                                    (Pf.proofApp
                                                       (Pf.termApp
                                                          (Pf.termApp
                                                             (Pf.termApp
                                                                (Pf.known
                                                                   "77e10b9988f12dc528ad73906107175925091da967df0552db1799b699955593")
                                                                (Tm.db 4))
                                                             (Tm.db 3))
                                                          (Tm.lam (Tp.base 0) fragment22))
                                                       (Pf.hyp 1))
                                                    (Pf.hyp 0))
                                                 (Tm.db 0))
                                              (Pf.hyp 2)))
                                        (Pf.termLam
                                           (Tp.base 0)
                                           (Pf.proofLam
                                              (Tm.app
                                                 (Tm.app
                                                    (Tm.app
                                                       (Tm.named
                                                          "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                                       (Tm.db 5))
                                                    (Tm.db 4))
                                                 (Tm.db 0))
                                              (Pf.proofLam
                                                 fragment22
                                                 (Pf.termLam
                                                    (Tp.var 0)
                                                    (Pf.termLam
                                                       (Tp.var 0)
                                                       (Pf.proofLam
                                                          fragment23
                                                          (Pf.proofLam
                                                             fragment4
                                                             (Pf.proofApp
                                                                (Pf.proofLam
                                                                   (Tm.app
                                                                      (Tm.typeApp
                                                                         (Tm.named
                                                                            "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099")
                                                                         (Tp.var 0))
                                                                      (Tm.lam
                                                                         (Tp.var 0)
                                                                         fragment25))
                                                                   (Pf.proofApp
                                                                      (Pf.proofLam
                                                                         (Tm.app
                                                                            (Tm.typeApp
                                                                               (Tm.named
                                                                                  "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099")
                                                                               (Tp.var 0))
                                                                            (Tm.lam
                                                                               (Tp.var 0)
                                                                               (Tm.app
                                                                                  fragment24
                                                                                  (Tm.app
                                                                                     (Tm.app
                                                                                        (Tm.typeApp
                                                                                           (Tm.named
                                                                                              "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                                                           (Tp.var
                                                                                              0))
                                                                                        (Tm.app
                                                                                           (Tm.app
                                                                                              (Tm.db
                                                                                                 5)
                                                                                              (Tm.db
                                                                                                 3))
                                                                                           (Tm.db
                                                                                              0)))
                                                                                     (Tm.db 1)))))
                                                                         (Pf.proofApp
                                                                            (Pf.termApp
                                                                               (Pf.hyp 1)
                                                                               (Tm.app
                                                                                  (Tm.app
                                                                                     (Tm.typeApp
                                                                                        (Tm.named
                                                                                           "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                                                        (Tp.var
                                                                                           0))
                                                                                     (Tm.db 1))
                                                                                  (Tm.db 0)))
                                                                            (Pf.termLam
                                                                               (Tp.var 0)
                                                                               (Pf.proofLam
                                                                                  fragment25
                                                                                  (Pf.proofApp
                                                                                     (Pf.termApp
                                                                                        (Pf.hyp 1)
                                                                                        (Tm.app
                                                                                           (Tm.app
                                                                                              (Tm.typeApp
                                                                                                 (Tm.named
                                                                                                    "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                                                                 (Tp.var
                                                                                                    0))
                                                                                              (Tm.db
                                                                                                 2))
                                                                                           (Tm.db
                                                                                              1)))
                                                                                     (Pf.termLam
                                                                                        (Tp.var 0)
                                                                                        (Pf.proofLam
                                                                                           (Tm.app
                                                                                              (Tm.app
                                                                                                 (Tm.named
                                                                                                    "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
                                                                                                 fragment26)
                                                                                              (Tm.app
                                                                                                 (Tm.app
                                                                                                    (Tm.typeApp
                                                                                                       (Tm.named
                                                                                                          "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                                                                       (Tp.var
                                                                                                          0))
                                                                                                    (Tm.app
                                                                                                       (Tm.app
                                                                                                          (Tm.db
                                                                                                             6)
                                                                                                          (Tm.db
                                                                                                             4))
                                                                                                       (Tm.db
                                                                                                          0)))
                                                                                                 (Tm.db
                                                                                                    2)))
                                                                                           (Pf.proofApp
                                                                                              (Pf.proofLam
                                                                                                 fragment27
                                                                                                 (Pf.proofApp
                                                                                                    (Pf.proofLam
                                                                                                       fragment26
                                                                                                       (Pf.proofApp
                                                                                                          (Pf.proofLam
                                                                                                             (Tm.app
                                                                                                                (Tm.app
                                                                                                                   (Tm.typeApp
                                                                                                                      (Tm.named
                                                                                                                         "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                                                                                      (Tp.var
                                                                                                                         0))
                                                                                                                   (Tm.app
                                                                                                                      (Tm.app
                                                                                                                         (Tm.db
                                                                                                                            6)
                                                                                                                         (Tm.db
                                                                                                                            4))
                                                                                                                      (Tm.db
                                                                                                                         1)))
                                                                                                                (Tm.db
                                                                                                                   3))
                                                                                                             (Pf.proofApp
                                                                                                                (Pf.proofLam
                                                                                                                   (Tm.app
                                                                                                                      (Tm.app
                                                                                                                         (Tm.typeApp
                                                                                                                            (Tm.named
                                                                                                                               "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                                                                                            (Tp.var
                                                                                                                               0))
                                                                                                                         (Tm.app
                                                                                                                            (Tm.app
                                                                                                                               (Tm.db
                                                                                                                                  6)
                                                                                                                               (Tm.db
                                                                                                                                  4))
                                                                                                                            (Tm.db
                                                                                                                               0)))
                                                                                                                      (Tm.db
                                                                                                                         2))
                                                                                                                   (Pf.proofApp
                                                                                                                      (Pf.proofLam
                                                                                                                         (Tm.app
                                                                                                                            (Tm.app
                                                                                                                               (Tm.typeApp
                                                                                                                                  (Tm.named
                                                                                                                                     "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                                                                                                  (Tp.var
                                                                                                                                     0))
                                                                                                                               (Tm.db
                                                                                                                                  1))
                                                                                                                            (Tm.db
                                                                                                                               0))
                                                                                                                         (Pf.proofApp
                                                                                                                            (Pf.proofLam
                                                                                                                               (Tm.app
                                                                                                                                  (Tm.app
                                                                                                                                     (Tm.typeApp
                                                                                                                                        (Tm.named
                                                                                                                                           "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                                                                                                        (Tp.var
                                                                                                                                           0))
                                                                                                                                     (Tm.app
                                                                                                                                        (Tm.app
                                                                                                                                           (Tm.db
                                                                                                                                              6)
                                                                                                                                           (Tm.db
                                                                                                                                              4))
                                                                                                                                        (Tm.db
                                                                                                                                           1)))
                                                                                                                                  (Tm.app
                                                                                                                                     (Tm.app
                                                                                                                                        (Tm.db
                                                                                                                                           6)
                                                                                                                                        (Tm.db
                                                                                                                                           4))
                                                                                                                                     (Tm.db
                                                                                                                                        0)))
                                                                                                                               (Pf.proofApp
                                                                                                                                  (Pf.proofApp
                                                                                                                                     (Pf.termApp
                                                                                                                                        (Pf.termApp
                                                                                                                                           (Pf.termApp
                                                                                                                                              (Pf.typeApp
                                                                                                                                                 (Pf.known
                                                                                                                                                    "0224060d7b7d5b6b2e8e4157524c8e4a18e5d17073c5b2fb2bb0c2583274fbc7")
                                                                                                                                                 (Tp.var
                                                                                                                                                    0))
                                                                                                                                              (Tm.db
                                                                                                                                                 3))
                                                                                                                                           (Tm.app
                                                                                                                                              (Tm.app
                                                                                                                                                 (Tm.db
                                                                                                                                                    6)
                                                                                                                                                 (Tm.db
                                                                                                                                                    4))
                                                                                                                                              (Tm.db
                                                                                                                                                 1)))
                                                                                                                                        (Tm.db
                                                                                                                                           2))
                                                                                                                                     (Pf.proofApp
                                                                                                                                        (Pf.termApp
                                                                                                                                           (Pf.termApp
                                                                                                                                              (Pf.typeApp
                                                                                                                                                 (Pf.known
                                                                                                                                                    "284ee58e7aea454281b73a0d0acb6efade8eeb4f2f3bf29aaf48a8fef862ceff")
                                                                                                                                                 (Tp.var
                                                                                                                                                    0))
                                                                                                                                              (Tm.app
                                                                                                                                                 (Tm.app
                                                                                                                                                    (Tm.db
                                                                                                                                                       6)
                                                                                                                                                    (Tm.db
                                                                                                                                                       4))
                                                                                                                                                 (Tm.db
                                                                                                                                                    1)))
                                                                                                                                           (Tm.db
                                                                                                                                              3))
                                                                                                                                        (Pf.hyp
                                                                                                                                           3)))
                                                                                                                                  (Pf.proofApp
                                                                                                                                     (Pf.proofApp
                                                                                                                                        (Pf.termApp
                                                                                                                                           (Pf.termApp
                                                                                                                                              (Pf.termApp
                                                                                                                                                 (Pf.typeApp
                                                                                                                                                    (Pf.known
                                                                                                                                                       "0224060d7b7d5b6b2e8e4157524c8e4a18e5d17073c5b2fb2bb0c2583274fbc7")
                                                                                                                                                    (Tp.var
                                                                                                                                                       0))
                                                                                                                                                 (Tm.app
                                                                                                                                                    (Tm.app
                                                                                                                                                       (Tm.db
                                                                                                                                                          6)
                                                                                                                                                       (Tm.db
                                                                                                                                                          4))
                                                                                                                                                    (Tm.db
                                                                                                                                                       1)))
                                                                                                                                              (Tm.app
                                                                                                                                                 (Tm.app
                                                                                                                                                    (Tm.db
                                                                                                                                                       6)
                                                                                                                                                    (Tm.db
                                                                                                                                                       4))
                                                                                                                                                 (Tm.db
                                                                                                                                                    0)))
                                                                                                                                           (Tm.db
                                                                                                                                              2))
                                                                                                                                        (Pf.hyp
                                                                                                                                           0))
                                                                                                                                     (Pf.hyp
                                                                                                                                        2))))
                                                                                                                            (Pf.proofApp
                                                                                                                               (Pf.termApp
                                                                                                                                  (Pf.hyp
                                                                                                                                     0)
                                                                                                                                  (Tm.lam
                                                                                                                                     (Tp.var
                                                                                                                                        0)
                                                                                                                                     (Tm.app
                                                                                                                                        (Tm.app
                                                                                                                                           (Tm.typeApp
                                                                                                                                              (Tm.named
                                                                                                                                                 "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                                                                                                              (Tp.var
                                                                                                                                                 0))
                                                                                                                                           (Tm.app
                                                                                                                                              (Tm.app
                                                                                                                                                 (Tm.db
                                                                                                                                                    7)
                                                                                                                                                 (Tm.db
                                                                                                                                                    5))
                                                                                                                                              (Tm.db
                                                                                                                                                 2)))
                                                                                                                                        (Tm.app
                                                                                                                                           (Tm.app
                                                                                                                                              (Tm.db
                                                                                                                                                 7)
                                                                                                                                              (Tm.db
                                                                                                                                                 5))
                                                                                                                                           (Tm.db
                                                                                                                                              0)))))
                                                                                                                               (Pf.termApp
                                                                                                                                  (Pf.typeApp
                                                                                                                                     (Pf.known
                                                                                                                                        "0f730be4ec19d9c14f6f80059c561f714dcecb54d8fa04f3570d0607e71d8331")
                                                                                                                                     (Tp.var
                                                                                                                                        0))
                                                                                                                                  (Tm.app
                                                                                                                                     (Tm.app
                                                                                                                                        (Tm.db
                                                                                                                                           6)
                                                                                                                                        (Tm.db
                                                                                                                                           4))
                                                                                                                                     (Tm.db
                                                                                                                                        1))))))
                                                                                                                      (Pf.proofApp
                                                                                                                         (Pf.proofApp
                                                                                                                            (Pf.termApp
                                                                                                                               (Pf.termApp
                                                                                                                                  (Pf.hyp
                                                                                                                                     10)
                                                                                                                                  (Tm.db
                                                                                                                                     1))
                                                                                                                               (Tm.db
                                                                                                                                  0))
                                                                                                                            (Pf.hyp
                                                                                                                               3))
                                                                                                                         (Pf.hyp
                                                                                                                            2))))
                                                                                                                (Pf.proofApp
                                                                                                                   (Pf.termApp
                                                                                                                      (Pf.termApp
                                                                                                                         (Pf.known
                                                                                                                            "fec5ab340a042c8361bb0564ac980cfe10dabcf5c4aeacb0746c0daa4ac55417")
                                                                                                                         fragment26)
                                                                                                                      (Tm.app
                                                                                                                         (Tm.app
                                                                                                                            (Tm.typeApp
                                                                                                                               (Tm.named
                                                                                                                                  "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                                                                                               (Tp.var
                                                                                                                                  0))
                                                                                                                            (Tm.app
                                                                                                                               (Tm.app
                                                                                                                                  (Tm.db
                                                                                                                                     6)
                                                                                                                                  (Tm.db
                                                                                                                                     4))
                                                                                                                               (Tm.db
                                                                                                                                  0)))
                                                                                                                         (Tm.db
                                                                                                                            2)))
                                                                                                                   (Pf.hyp
                                                                                                                      3))))
                                                                                                          (Pf.proofApp
                                                                                                             (Pf.termApp
                                                                                                                (Pf.termApp
                                                                                                                   (Pf.known
                                                                                                                      "fec5ab340a042c8361bb0564ac980cfe10dabcf5c4aeacb0746c0daa4ac55417")
                                                                                                                   fragment27)
                                                                                                                (Tm.app
                                                                                                                   (Tm.app
                                                                                                                      (Tm.typeApp
                                                                                                                         (Tm.named
                                                                                                                            "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                                                                                         (Tp.var
                                                                                                                            0))
                                                                                                                      (Tm.app
                                                                                                                         (Tm.app
                                                                                                                            (Tm.db
                                                                                                                               6)
                                                                                                                            (Tm.db
                                                                                                                               4))
                                                                                                                         (Tm.db
                                                                                                                            1)))
                                                                                                                   (Tm.db
                                                                                                                      3)))
                                                                                                             (Pf.hyp
                                                                                                                3))))
                                                                                                    (Pf.proofApp
                                                                                                       (Pf.termApp
                                                                                                          (Pf.termApp
                                                                                                             (Pf.known
                                                                                                                "eb8814e5b67181dcc2fdd7f757e9f1e3c90bcd9b3117f2bb9aa7650cdaac5b42")
                                                                                                             fragment26)
                                                                                                          (Tm.app
                                                                                                             (Tm.app
                                                                                                                (Tm.typeApp
                                                                                                                   (Tm.named
                                                                                                                      "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                                                                                   (Tp.var
                                                                                                                      0))
                                                                                                                (Tm.app
                                                                                                                   (Tm.app
                                                                                                                      (Tm.db
                                                                                                                         6)
                                                                                                                      (Tm.db
                                                                                                                         4))
                                                                                                                   (Tm.db
                                                                                                                      0)))
                                                                                                             (Tm.db
                                                                                                                2)))
                                                                                                       (Pf.hyp
                                                                                                          1))))
                                                                                              (Pf.proofApp
                                                                                                 (Pf.termApp
                                                                                                    (Pf.termApp
                                                                                                       (Pf.known
                                                                                                          "eb8814e5b67181dcc2fdd7f757e9f1e3c90bcd9b3117f2bb9aa7650cdaac5b42")
                                                                                                       fragment27)
                                                                                                    (Tm.app
                                                                                                       (Tm.app
                                                                                                          (Tm.typeApp
                                                                                                             (Tm.named
                                                                                                                "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                                                                             (Tp.var
                                                                                                                0))
                                                                                                          (Tm.app
                                                                                                             (Tm.app
                                                                                                                (Tm.db
                                                                                                                   6)
                                                                                                                (Tm.db
                                                                                                                   4))
                                                                                                             (Tm.db
                                                                                                                1)))
                                                                                                       (Tm.db
                                                                                                          3)))
                                                                                                 (Pf.hyp
                                                                                                    1))))))))))
                                                                      (Pf.proofApp
                                                                         (Pf.termApp
                                                                            (Pf.termApp
                                                                               (Pf.termApp
                                                                                  (Pf.termApp
                                                                                     (Pf.proofApp
                                                                                        (Pf.proofApp
                                                                                           (Pf.termApp
                                                                                              (Pf.termApp
                                                                                                 (Pf.typeApp
                                                                                                    (Pf.known
                                                                                                       "b6f91526fffc2274b066d609cf61e85df750465fdcfcc883602660ea5efff74c")
                                                                                                    (Tp.var
                                                                                                       0))
                                                                                                 (Tm.db
                                                                                                    7))
                                                                                              (Tm.db
                                                                                                 6))
                                                                                           (Pf.hyp
                                                                                              8))
                                                                                        (Pf.hyp
                                                                                           7))
                                                                                     (Tm.db 5))
                                                                                  (Tm.db 4))
                                                                               (Tm.db 2))
                                                                            (Tm.db 0))
                                                                         (Pf.hyp 1))))
                                                                (Pf.proofApp
                                                                   (Pf.termApp
                                                                      (Pf.termApp
                                                                         (Pf.termApp
                                                                            (Pf.termApp
                                                                               (Pf.proofApp
                                                                                  (Pf.proofApp
                                                                                     (Pf.termApp
                                                                                        (Pf.termApp
                                                                                           (Pf.typeApp
                                                                                              (Pf.known
                                                                                                 "b6f91526fffc2274b066d609cf61e85df750465fdcfcc883602660ea5efff74c")
                                                                                              (Tp.var
                                                                                                 0))
                                                                                           (Tm.db
                                                                                              7))
                                                                                        (Tm.db 6))
                                                                                     (Pf.hyp 7))
                                                                                  (Pf.hyp 6))
                                                                               (Tm.db 5))
                                                                            (Tm.db 4))
                                                                         (Tm.db 2))
                                                                      (Tm.db 1))
                                                                   (Pf.hyp 1))))))))))))
                                  (Pf.termLam
                                     (Tp.var 0)
                                     (Pf.termLam
                                        (Tp.var 0)
                                        (Pf.proofLam
                                           fragment20
                                           (Pf.proofLam
                                              fragment21
                                              (Pf.proofApp
                                                 (Pf.proofApp
                                                    (Pf.termApp
                                                       (Pf.termApp
                                                          (Pf.termApp
                                                             (Pf.typeApp
                                                                (Pf.known
                                                                   "0224060d7b7d5b6b2e8e4157524c8e4a18e5d17073c5b2fb2bb0c2583274fbc7")
                                                                (Tp.var 0))
                                                             (Tm.db 1))
                                                          (Tm.db 4))
                                                       (Tm.db 0))
                                                    (Pf.proofApp
                                                       (Pf.termApp
                                                          (Pf.termApp
                                                             (Pf.typeApp
                                                                (Pf.known
                                                                   "284ee58e7aea454281b73a0d0acb6efade8eeb4f2f3bf29aaf48a8fef862ceff")
                                                                (Tp.var 0))
                                                             (Tm.db 4))
                                                          (Tm.db 1))
                                                       (Pf.proofApp
                                                          (Pf.termApp
                                                             (Pf.termApp
                                                                (Pf.termApp
                                                                   (Pf.proofApp
                                                                      (Pf.termApp
                                                                         (Pf.termApp
                                                                            (Pf.typeApp
                                                                               (Pf.known
                                                                                  "f91a57a5bd78694e5884aa1b325509ba1c324bb735928e38924bb7081d7e567b")
                                                                               (Tp.var 0))
                                                                            (Tm.db 6))
                                                                         (Tm.db 5))
                                                                      (Pf.hyp 4))
                                                                   (Tm.db 4))
                                                                (Tm.db 3))
                                                             (Tm.db 1))
                                                          (Pf.hyp 1))))
                                                 (Pf.proofApp
                                                    (Pf.termApp
                                                       (Pf.termApp
                                                          (Pf.termApp
                                                             (Pf.proofApp
                                                                (Pf.termApp
                                                                   (Pf.termApp
                                                                      (Pf.typeApp
                                                                         (Pf.known
                                                                            "f91a57a5bd78694e5884aa1b325509ba1c324bb735928e38924bb7081d7e567b")
                                                                         (Tp.var 0))
                                                                      (Tm.db 6))
                                                                   (Tm.db 5))
                                                                (Pf.hyp 4))
                                                             (Tm.db 4))
                                                          (Tm.db 3))
                                                       (Tm.db 0))
                                                    (Pf.hyp 0)))))))))))))))))

def nrRecursor : Item :=
  Item.definition
    "07c6d5bb8b1b51acf568b644d496c3805612be5b440432b88ee69c28280f8c5d"
    (Tp.all
       (Tp.arr
          (Tp.base 0)
          (Tp.arr
             (Tp.arr (Tp.base 0) (Tp.base 0))
             (Tp.arr
                (Tp.var 0)
                (Tp.arr
                   (Tp.arr (Tp.base 0) (Tp.arr (Tp.var 0) (Tp.var 0)))
                   (Tp.arr
                      (Tp.arr (Tp.arr (Tp.var 0) Tp.prop) (Tp.var 0))
                      (Tp.arr (Tp.base 0) (Tp.var 0))))))))
    (Tm.typeLam
       (Tm.lam
          (Tp.base 0)
          (Tm.lam
             (Tp.arr (Tp.base 0) (Tp.base 0))
             (Tm.lam
                (Tp.var 0)
                (Tm.lam
                   (Tp.arr (Tp.base 0) (Tp.arr (Tp.var 0) (Tp.var 0)))
                   (Tm.lam
                      (Tp.arr (Tp.arr (Tp.var 0) Tp.prop) (Tp.var 0))
                      (Tm.lam
                         (Tp.base 0)
                         (Tm.app
                            (Tm.db 1)
                            (Tm.app
                               (Tm.app
                                  (Tm.app
                                     (Tm.app
                                        (Tm.app
                                           (Tm.typeApp
                                              (Tm.named
                                                 "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                              (Tp.var 0))
                                           (Tm.db 5))
                                        (Tm.db 4))
                                     (Tm.db 3))
                                  (Tm.db 2))
                               (Tm.db 0))))))))))

def nrRecursorGraph : Item :=
  Item.theorem_
    "fcb71074cf42d8987389724f3694303d976cba70c34d7ab333bd93760834c280"
    (Tm.typeAll
       (Tm.all
          (Tp.base 0)
          (Tm.all
             (Tp.arr (Tp.base 0) (Tp.base 0))
             (Tm.all
                (Tp.var 0)
                (Tm.all
                   (Tp.arr (Tp.base 0) (Tp.arr (Tp.var 0) (Tp.var 0)))
                   (Tm.all
                      (Tp.arr (Tp.arr (Tp.var 0) Tp.prop) (Tp.var 0))
                      (Tm.imp
                         (Tm.all
                            (Tp.arr (Tp.var 0) Tp.prop)
                            (Tm.imp
                               (Tm.app
                                  (Tm.typeApp
                                     (Tm.named
                                        "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099")
                                     (Tp.var 0))
                                  (Tm.db 0))
                               (Tm.app (Tm.db 0) (Tm.app (Tm.db 1) (Tm.db 0)))))
                         (Tm.all
                            (Tp.base 0)
                            (Tm.imp
                               (Tm.app
                                  (Tm.app
                                     (Tm.app
                                        (Tm.named
                                           "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                        (Tm.db 5))
                                     (Tm.db 4))
                                  (Tm.db 0))
                               fragment29)))))))))
    (Pf.typeLam
       (Pf.termLam
          (Tp.base 0)
          (Pf.termLam
             (Tp.arr (Tp.base 0) (Tp.base 0))
             (Pf.termLam
                (Tp.var 0)
                (Pf.termLam
                   (Tp.arr (Tp.base 0) (Tp.arr (Tp.var 0) (Tp.var 0)))
                   (Pf.termLam
                      (Tp.arr (Tp.arr (Tp.var 0) Tp.prop) (Tp.var 0))
                      (Pf.proofLam
                         (Tm.all
                            (Tp.arr (Tp.var 0) Tp.prop)
                            (Tm.imp
                               (Tm.app
                                  (Tm.typeApp
                                     (Tm.named
                                        "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099")
                                     (Tp.var 0))
                                  (Tm.db 0))
                               (Tm.app (Tm.db 0) (Tm.app (Tm.db 1) (Tm.db 0)))))
                         (Pf.termLam
                            (Tp.base 0)
                            (Pf.proofLam
                               (Tm.app
                                  (Tm.app
                                     (Tm.app
                                        (Tm.named
                                           "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                        (Tm.db 5))
                                     (Tm.db 4))
                                  (Tm.db 0))
                               (Pf.proofApp
                                  (Pf.termApp (Pf.hyp 1) fragment2)
                                  (Pf.proofApp
                                     (Pf.termApp
                                        (Pf.termApp
                                           (Pf.termApp
                                              (Pf.termApp
                                                 (Pf.termApp
                                                    (Pf.typeApp
                                                       (Pf.known
                                                          "e9bc3463274b5a8e5dfe44cf95087e1baa1298d95aa1f8a771bfa5a4ae9b58bd")
                                                       (Tp.var 0))
                                                    (Tm.db 5))
                                                 (Tm.db 4))
                                              (Tm.db 3))
                                           (Tm.db 2))
                                        (Tm.db 0))
                                     (Pf.hyp 0))))))))))))

def nrRecursorZero : Item :=
  Item.theorem_
    "22e3b03874328016e540ab23671ef8d65aedae835b5a6300a63169ce15d2cf5c"
    (Tm.typeAll
       (Tm.all
          (Tp.base 0)
          (Tm.all
             (Tp.arr (Tp.base 0) (Tp.base 0))
             (Tm.imp
                (Tm.all
                   (Tp.base 0)
                   (Tm.imp
                      (Tm.app
                         (Tm.app
                            (Tm.typeApp
                               (Tm.named
                                  "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                               (Tp.base 0))
                            (Tm.app (Tm.db 1) (Tm.db 0)))
                         (Tm.db 2))
                      (Tm.named
                         "5bf697cb0d1cdefbe881504469f6c48cc388994115b82514dfc4fb5e67ac1a87")))
                (Tm.all
                   (Tp.var 0)
                   (Tm.all
                      (Tp.arr (Tp.base 0) (Tp.arr (Tp.var 0) (Tp.var 0)))
                      (Tm.all
                         (Tp.arr (Tp.arr (Tp.var 0) Tp.prop) (Tp.var 0))
                         (Tm.imp
                            (Tm.all
                               (Tp.arr (Tp.var 0) Tp.prop)
                               (Tm.imp
                                  (Tm.app
                                     (Tm.typeApp
                                        (Tm.named
                                           "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099")
                                        (Tp.var 0))
                                     (Tm.db 0))
                                  (Tm.app (Tm.db 0) (Tm.app (Tm.db 1) (Tm.db 0)))))
                            fragment31))))))))
    (Pf.typeLam
       (Pf.termLam
          (Tp.base 0)
          (Pf.termLam
             (Tp.arr (Tp.base 0) (Tp.base 0))
             (Pf.proofLam
                (Tm.all
                   (Tp.base 0)
                   (Tm.imp
                      (Tm.app
                         (Tm.app
                            (Tm.typeApp
                               (Tm.named
                                  "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                               (Tp.base 0))
                            (Tm.app (Tm.db 1) (Tm.db 0)))
                         (Tm.db 2))
                      (Tm.named
                         "5bf697cb0d1cdefbe881504469f6c48cc388994115b82514dfc4fb5e67ac1a87")))
                (Pf.termLam
                   (Tp.var 0)
                   (Pf.termLam
                      (Tp.arr (Tp.base 0) (Tp.arr (Tp.var 0) (Tp.var 0)))
                      (Pf.termLam
                         (Tp.arr (Tp.arr (Tp.var 0) Tp.prop) (Tp.var 0))
                         (Pf.proofLam
                            (Tm.all
                               (Tp.arr (Tp.var 0) Tp.prop)
                               (Tm.imp
                                  (Tm.app
                                     (Tm.typeApp
                                        (Tm.named
                                           "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099")
                                        (Tp.var 0))
                                     (Tm.db 0))
                                  (Tm.app (Tm.db 0) (Tm.app (Tm.db 1) (Tm.db 0)))))
                            (Pf.proofApp
                               (Pf.termApp
                                  (Pf.termApp
                                     (Pf.termApp
                                        (Pf.proofApp
                                           (Pf.termApp
                                              (Pf.termApp
                                                 (Pf.typeApp
                                                    (Pf.known
                                                       "f91a57a5bd78694e5884aa1b325509ba1c324bb735928e38924bb7081d7e567b")
                                                    (Tp.var 0))
                                                 (Tm.db 4))
                                              (Tm.db 3))
                                           (Pf.hyp 1))
                                        (Tm.db 2))
                                     (Tm.db 1))
                                  fragment30)
                               (Pf.proofApp
                                  (Pf.termApp
                                     (Pf.proofApp
                                        (Pf.termApp
                                           (Pf.termApp
                                              (Pf.termApp
                                                 (Pf.termApp
                                                    (Pf.termApp
                                                       (Pf.typeApp
                                                          (Pf.known
                                                             "fcb71074cf42d8987389724f3694303d976cba70c34d7ab333bd93760834c280")
                                                          (Tp.var 0))
                                                       (Tm.db 4))
                                                    (Tm.db 3))
                                                 (Tm.db 2))
                                              (Tm.db 1))
                                           (Tm.db 0))
                                        (Pf.hyp 0))
                                     (Tm.db 4))
                                  (Pf.termApp
                                     (Pf.termApp
                                        (Pf.known
                                           "a7a2e1cb291bdfdc11661c2875e62b3fb8fb502cb3c1f594c4e6f50789e4f911")
                                        (Tm.db 4))
                                     (Tm.db 3))))))))))))

def nrRecursorSuccessor : Item :=
  Item.theorem_
    "1d0d22f0333064db2f7008d20316b35d84fc8bf4adc664060b8860cd94977e5f"
    (Tm.typeAll
       (Tm.all
          (Tp.base 0)
          (Tm.all
             (Tp.arr (Tp.base 0) (Tp.base 0))
             (Tm.imp
                (Tm.all
                   (Tp.base 0)
                   (Tm.imp
                      (Tm.app
                         (Tm.app
                            (Tm.typeApp
                               (Tm.named
                                  "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                               (Tp.base 0))
                            (Tm.app (Tm.db 1) (Tm.db 0)))
                         (Tm.db 2))
                      (Tm.named
                         "5bf697cb0d1cdefbe881504469f6c48cc388994115b82514dfc4fb5e67ac1a87")))
                (Tm.imp
                   (Tm.all
                      (Tp.base 0)
                      (Tm.all
                         (Tp.base 0)
                         (Tm.imp
                            (Tm.app
                               (Tm.app
                                  (Tm.typeApp
                                     (Tm.named
                                        "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                     (Tp.base 0))
                                  (Tm.app (Tm.db 2) (Tm.db 1)))
                               (Tm.app (Tm.db 2) (Tm.db 0)))
                            (Tm.app
                               (Tm.app
                                  (Tm.typeApp
                                     (Tm.named
                                        "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                     (Tp.base 0))
                                  (Tm.db 1))
                               (Tm.db 0)))))
                   (Tm.all
                      (Tp.var 0)
                      (Tm.all
                         (Tp.arr (Tp.base 0) (Tp.arr (Tp.var 0) (Tp.var 0)))
                         (Tm.all
                            (Tp.arr (Tp.arr (Tp.var 0) Tp.prop) (Tp.var 0))
                            (Tm.imp
                               (Tm.all
                                  (Tp.arr (Tp.var 0) Tp.prop)
                                  (Tm.imp
                                     (Tm.app
                                        (Tm.typeApp
                                           (Tm.named
                                              "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099")
                                           (Tp.var 0))
                                        (Tm.db 0))
                                     (Tm.app (Tm.db 0) (Tm.app (Tm.db 1) (Tm.db 0)))))
                               fragment34)))))))))
    (Pf.typeLam
       (Pf.termLam
          (Tp.base 0)
          (Pf.termLam
             (Tp.arr (Tp.base 0) (Tp.base 0))
             (Pf.proofLam
                (Tm.all
                   (Tp.base 0)
                   (Tm.imp
                      (Tm.app
                         (Tm.app
                            (Tm.typeApp
                               (Tm.named
                                  "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                               (Tp.base 0))
                            (Tm.app (Tm.db 1) (Tm.db 0)))
                         (Tm.db 2))
                      (Tm.named
                         "5bf697cb0d1cdefbe881504469f6c48cc388994115b82514dfc4fb5e67ac1a87")))
                (Pf.proofLam
                   (Tm.all
                      (Tp.base 0)
                      (Tm.all
                         (Tp.base 0)
                         (Tm.imp
                            (Tm.app
                               (Tm.app
                                  (Tm.typeApp
                                     (Tm.named
                                        "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                     (Tp.base 0))
                                  (Tm.app (Tm.db 2) (Tm.db 1)))
                               (Tm.app (Tm.db 2) (Tm.db 0)))
                            (Tm.app
                               (Tm.app
                                  (Tm.typeApp
                                     (Tm.named
                                        "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                     (Tp.base 0))
                                  (Tm.db 1))
                               (Tm.db 0)))))
                   (Pf.termLam
                      (Tp.var 0)
                      (Pf.termLam
                         (Tp.arr (Tp.base 0) (Tp.arr (Tp.var 0) (Tp.var 0)))
                         (Pf.termLam
                            (Tp.arr (Tp.arr (Tp.var 0) Tp.prop) (Tp.var 0))
                            (Pf.proofLam
                               (Tm.all
                                  (Tp.arr (Tp.var 0) Tp.prop)
                                  (Tm.imp
                                     (Tm.app
                                        (Tm.typeApp
                                           (Tm.named
                                              "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099")
                                           (Tp.var 0))
                                        (Tm.db 0))
                                     (Tm.app (Tm.db 0) (Tm.app (Tm.db 1) (Tm.db 0)))))
                               (Pf.termLam
                                  (Tp.base 0)
                                  (Pf.proofLam
                                     (Tm.app
                                        (Tm.app
                                           (Tm.app
                                              (Tm.named
                                                 "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                              (Tm.db 5))
                                           (Tm.db 4))
                                        (Tm.db 0))
                                     (Pf.proofApp
                                        (Pf.proofLam
                                           fragment29
                                           (Pf.proofApp
                                              (Pf.proofApp
                                                 (Pf.termApp
                                                    (Pf.termApp
                                                       (Pf.proofApp
                                                          (Pf.termApp
                                                             (Pf.termApp
                                                                (Pf.termApp
                                                                   (Pf.proofApp
                                                                      (Pf.proofApp
                                                                         (Pf.termApp
                                                                            (Pf.termApp
                                                                               (Pf.typeApp
                                                                                  (Pf.known
                                                                                     "653fd64163dedfee84cae7ddf348949c2cfc59c5db33f3b662cc8fba4f41634a")
                                                                                  (Tp.var 0))
                                                                               (Tm.db 5))
                                                                            (Tm.db 4))
                                                                         (Pf.hyp 4))
                                                                      (Pf.hyp 3))
                                                                   (Tm.db 3))
                                                                (Tm.db 2))
                                                             (Tm.app (Tm.db 4) (Tm.db 0)))
                                                          (Pf.proofApp
                                                             (Pf.termApp
                                                                (Pf.termApp
                                                                   (Pf.termApp
                                                                      (Pf.known
                                                                         "877913cb39467cac5218f875864ba9d5f794a079e124c150a2aa99edb28f6861")
                                                                      (Tm.db 5))
                                                                   (Tm.db 4))
                                                                (Tm.db 0))
                                                             (Pf.hyp 1)))
                                                       fragment32)
                                                    fragment33)
                                                 (Pf.proofApp
                                                    (Pf.termApp
                                                       (Pf.termApp
                                                          (Pf.termApp
                                                             (Pf.termApp
                                                                (Pf.termApp
                                                                   (Pf.termApp
                                                                      (Pf.typeApp
                                                                         (Pf.known
                                                                            "96c29789eac08b76f3030c1438fa2ff7ca40becb4c3216e4f228b35b1177143b")
                                                                         (Tp.var 0))
                                                                      (Tm.db 5))
                                                                   (Tm.db 4))
                                                                (Tm.db 3))
                                                             (Tm.db 2))
                                                          (Tm.db 0))
                                                       fragment28)
                                                    (Pf.hyp 0)))
                                              (Pf.proofApp
                                                 (Pf.termApp
                                                    (Pf.proofApp
                                                       (Pf.termApp
                                                          (Pf.termApp
                                                             (Pf.termApp
                                                                (Pf.termApp
                                                                   (Pf.termApp
                                                                      (Pf.typeApp
                                                                         (Pf.known
                                                                            "fcb71074cf42d8987389724f3694303d976cba70c34d7ab333bd93760834c280")
                                                                         (Tp.var 0))
                                                                      (Tm.db 5))
                                                                   (Tm.db 4))
                                                                (Tm.db 3))
                                                             (Tm.db 2))
                                                          (Tm.db 1))
                                                       (Pf.hyp 2))
                                                    (Tm.app (Tm.db 4) (Tm.db 0)))
                                                 (Pf.proofApp
                                                    (Pf.termApp
                                                       (Pf.termApp
                                                          (Pf.termApp
                                                             (Pf.known
                                                                "877913cb39467cac5218f875864ba9d5f794a079e124c150a2aa99edb28f6861")
                                                             (Tm.db 5))
                                                          (Tm.db 4))
                                                       (Tm.db 0))
                                                    (Pf.hyp 1)))))
                                        (Pf.proofApp
                                           (Pf.termApp
                                              (Pf.proofApp
                                                 (Pf.termApp
                                                    (Pf.termApp
                                                       (Pf.termApp
                                                          (Pf.termApp
                                                             (Pf.termApp
                                                                (Pf.typeApp
                                                                   (Pf.known
                                                                      "fcb71074cf42d8987389724f3694303d976cba70c34d7ab333bd93760834c280")
                                                                   (Tp.var 0))
                                                                (Tm.db 5))
                                                             (Tm.db 4))
                                                          (Tm.db 3))
                                                       (Tm.db 2))
                                                    (Tm.db 1))
                                                 (Pf.hyp 1))
                                              (Tm.db 0))
                                           (Pf.hyp 0))))))))))))))

def nrGraphAgrees : Item :=
  Item.theorem_
    "3861803eb83e09998ef34c354bc50aff520951f2031b7842559c0195eed45b6a"
    (Tm.typeAll
       (Tm.all
          (Tp.base 0)
          (Tm.all
             (Tp.arr (Tp.base 0) (Tp.base 0))
             (Tm.all
                (Tp.var 0)
                (Tm.all
                   (Tp.arr (Tp.base 0) (Tp.arr (Tp.var 0) (Tp.var 0)))
                   (Tm.all
                      (Tp.arr (Tp.base 0) (Tp.var 0))
                      (Tm.imp
                         (Tm.app
                            (Tm.app
                               (Tm.typeApp
                                  (Tm.named
                                     "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                  (Tp.var 0))
                               (Tm.db 2))
                            (Tm.app (Tm.db 0) (Tm.db 4)))
                         (Tm.imp
                            (Tm.all
                               (Tp.base 0)
                               (Tm.imp
                                  (Tm.app
                                     (Tm.app
                                        (Tm.app
                                           (Tm.named
                                              "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                           (Tm.db 5))
                                        (Tm.db 4))
                                     (Tm.db 0))
                                  (Tm.app
                                     (Tm.app
                                        (Tm.typeApp
                                           (Tm.named
                                              "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                           (Tp.var 0))
                                        (Tm.app
                                           (Tm.app (Tm.db 2) (Tm.db 0))
                                           (Tm.app (Tm.db 1) (Tm.db 0))))
                                     (Tm.app (Tm.db 1) (Tm.app (Tm.db 4) (Tm.db 0))))))
                            (Tm.all
                               (Tp.base 0)
                               (Tm.all
                                  (Tp.var 0)
                                  (Tm.imp
                                     fragment1
                                     (Tm.app
                                        (Tm.app
                                           (Tm.typeApp
                                              (Tm.named
                                                 "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                              (Tp.var 0))
                                           (Tm.db 0))
                                        (Tm.app (Tm.db 2) (Tm.db 1))))))))))))))
    (Pf.typeLam
       (Pf.termLam
          (Tp.base 0)
          (Pf.termLam
             (Tp.arr (Tp.base 0) (Tp.base 0))
             (Pf.termLam
                (Tp.var 0)
                (Pf.termLam
                   (Tp.arr (Tp.base 0) (Tp.arr (Tp.var 0) (Tp.var 0)))
                   (Pf.termLam
                      (Tp.arr (Tp.base 0) (Tp.var 0))
                      (Pf.proofLam
                         (Tm.app
                            (Tm.app
                               (Tm.typeApp
                                  (Tm.named
                                     "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                  (Tp.var 0))
                               (Tm.db 2))
                            (Tm.app (Tm.db 0) (Tm.db 4)))
                         (Pf.proofLam
                            (Tm.all
                               (Tp.base 0)
                               (Tm.imp
                                  (Tm.app
                                     (Tm.app
                                        (Tm.app
                                           (Tm.named
                                              "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                           (Tm.db 5))
                                        (Tm.db 4))
                                     (Tm.db 0))
                                  (Tm.app
                                     (Tm.app
                                        (Tm.typeApp
                                           (Tm.named
                                              "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                           (Tp.var 0))
                                        (Tm.app
                                           (Tm.app (Tm.db 2) (Tm.db 0))
                                           (Tm.app (Tm.db 1) (Tm.db 0))))
                                     (Tm.app (Tm.db 1) (Tm.app (Tm.db 4) (Tm.db 0))))))
                            (Pf.termLam
                               (Tp.base 0)
                               (Pf.termLam
                                  (Tp.var 0)
                                  (Pf.proofLam
                                     fragment1
                                     (Pf.proofApp
                                        (Pf.proofLam
                                           (Tm.app
                                              (Tm.app
                                                 (Tm.named
                                                    "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
                                                 (Tm.app
                                                    (Tm.app
                                                       (Tm.app
                                                          (Tm.named
                                                             "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                                          (Tm.db 6))
                                                       (Tm.db 5))
                                                    (Tm.db 6)))
                                              (Tm.app
                                                 (Tm.app
                                                    (Tm.typeApp
                                                       (Tm.named
                                                          "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                       (Tp.var 0))
                                                    (Tm.db 4))
                                                 (Tm.app (Tm.db 2) (Tm.db 6))))
                                           (Pf.proofApp
                                              (Pf.proofLam
                                                 (Tm.all
                                                    (Tp.base 0)
                                                    (Tm.all
                                                       (Tp.var 0)
                                                       (Tm.imp
                                                          (Tm.app
                                                             (Tm.app
                                                                (Tm.named
                                                                   "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
                                                                (Tm.app
                                                                   (Tm.app
                                                                      (Tm.app
                                                                         (Tm.named
                                                                            "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                                                         (Tm.db 8))
                                                                      (Tm.db 7))
                                                                   (Tm.db 1)))
                                                             (Tm.app
                                                                (Tm.app
                                                                   (Tm.typeApp
                                                                      (Tm.named
                                                                         "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                                      (Tp.var 0))
                                                                   (Tm.db 0))
                                                                (Tm.app (Tm.db 4) (Tm.db 1))))
                                                          (Tm.app
                                                             (Tm.app
                                                                (Tm.named
                                                                   "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
                                                                (Tm.app
                                                                   (Tm.app
                                                                      (Tm.app
                                                                         (Tm.named
                                                                            "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                                                         (Tm.db 8))
                                                                      (Tm.db 7))
                                                                   (Tm.app (Tm.db 7) (Tm.db 1))))
                                                             (Tm.app
                                                                (Tm.app
                                                                   (Tm.typeApp
                                                                      (Tm.named
                                                                         "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                                      (Tp.var 0))
                                                                   (Tm.app
                                                                      (Tm.app (Tm.db 5) (Tm.db 1))
                                                                      (Tm.db 0)))
                                                                (Tm.app
                                                                   (Tm.db 4)
                                                                   (Tm.app
                                                                      (Tm.db 7)
                                                                      (Tm.db 1))))))))
                                                 (Pf.proofApp
                                                    (Pf.proofLam
                                                       (Tm.app
                                                          (Tm.app
                                                             (Tm.named
                                                                "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
                                                             (Tm.app
                                                                (Tm.app
                                                                   (Tm.app
                                                                      (Tm.named
                                                                         "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                                                      (Tm.db 6))
                                                                   (Tm.db 5))
                                                                (Tm.db 1)))
                                                          (Tm.app
                                                             (Tm.app
                                                                (Tm.typeApp
                                                                   (Tm.named
                                                                      "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                                   (Tp.var 0))
                                                                (Tm.db 0))
                                                             (Tm.app (Tm.db 2) (Tm.db 1))))
                                                       (Pf.proofApp
                                                          (Pf.termApp
                                                             (Pf.termApp
                                                                (Pf.known
                                                                   "fec5ab340a042c8361bb0564ac980cfe10dabcf5c4aeacb0746c0daa4ac55417")
                                                                (Tm.app
                                                                   (Tm.app
                                                                      (Tm.app
                                                                         (Tm.named
                                                                            "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                                                         (Tm.db 6))
                                                                      (Tm.db 5))
                                                                   (Tm.db 1)))
                                                             (Tm.app
                                                                (Tm.app
                                                                   (Tm.typeApp
                                                                      (Tm.named
                                                                         "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                                      (Tp.var 0))
                                                                   (Tm.db 0))
                                                                (Tm.app (Tm.db 2) (Tm.db 1))))
                                                          (Pf.hyp 0)))
                                                    (Pf.proofApp
                                                       (Pf.proofApp
                                                          (Pf.termApp
                                                             (Pf.hyp 2)
                                                             (Tm.lam
                                                                (Tp.base 0)
                                                                (Tm.lam
                                                                   (Tp.var 0)
                                                                   (Tm.app
                                                                      (Tm.app
                                                                         (Tm.named
                                                                            "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
                                                                         (Tm.app
                                                                            (Tm.app
                                                                               (Tm.app
                                                                                  (Tm.named
                                                                                     "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                                                                  (Tm.db 8))
                                                                               (Tm.db 7))
                                                                            (Tm.db 1)))
                                                                      (Tm.app
                                                                         (Tm.app
                                                                            (Tm.typeApp
                                                                               (Tm.named
                                                                                  "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                                               (Tp.var 0))
                                                                            (Tm.db 0))
                                                                         (Tm.app
                                                                            (Tm.db 4)
                                                                            (Tm.db 1)))))))
                                                          (Pf.hyp 1))
                                                       (Pf.hyp 0))))
                                              (Pf.termLam
                                                 (Tp.base 0)
                                                 (Pf.termLam
                                                    (Tp.var 0)
                                                    (Pf.proofLam
                                                       (Tm.app
                                                          (Tm.app
                                                             (Tm.named
                                                                "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
                                                             (Tm.app
                                                                (Tm.app
                                                                   (Tm.app
                                                                      (Tm.named
                                                                         "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                                                      (Tm.db 8))
                                                                   (Tm.db 7))
                                                                (Tm.db 1)))
                                                          (Tm.app
                                                             (Tm.app
                                                                (Tm.typeApp
                                                                   (Tm.named
                                                                      "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                                   (Tp.var 0))
                                                                (Tm.db 0))
                                                             (Tm.app (Tm.db 4) (Tm.db 1))))
                                                       (Pf.proofApp
                                                          (Pf.proofLam
                                                             (Tm.app
                                                                (Tm.app
                                                                   (Tm.app
                                                                      (Tm.named
                                                                         "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                                                      (Tm.db 8))
                                                                   (Tm.db 7))
                                                                (Tm.db 1))
                                                             (Pf.proofApp
                                                                (Pf.proofLam
                                                                   (Tm.app
                                                                      (Tm.app
                                                                         (Tm.typeApp
                                                                            (Tm.named
                                                                               "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                                            (Tp.var 0))
                                                                         (Tm.db 0))
                                                                      (Tm.app
                                                                         (Tm.db 4)
                                                                         (Tm.db 1)))
                                                                   (Pf.proofApp
                                                                      (Pf.proofApp
                                                                         (Pf.termApp
                                                                            (Pf.termApp
                                                                               (Pf.known
                                                                                  "7f6246d08629eeb16eab93529ffe4f929f43344833ab88c7786393693520e82b")
                                                                               (Tm.app
                                                                                  (Tm.app
                                                                                     (Tm.app
                                                                                        (Tm.named
                                                                                           "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                                                                        (Tm.db 8))
                                                                                     (Tm.db 7))
                                                                                  (Tm.app
                                                                                     (Tm.db 7)
                                                                                     (Tm.db 1))))
                                                                            (Tm.app
                                                                               (Tm.app
                                                                                  (Tm.typeApp
                                                                                     (Tm.named
                                                                                        "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                                                     (Tp.var 0))
                                                                                  (Tm.app
                                                                                     (Tm.app
                                                                                        (Tm.db 5)
                                                                                        (Tm.db 1))
                                                                                     (Tm.db 0)))
                                                                               (Tm.app
                                                                                  (Tm.db 4)
                                                                                  (Tm.app
                                                                                     (Tm.db 7)
                                                                                     (Tm.db 1)))))
                                                                         (Pf.proofApp
                                                                            (Pf.termApp
                                                                               (Pf.termApp
                                                                                  (Pf.termApp
                                                                                     (Pf.known
                                                                                        "877913cb39467cac5218f875864ba9d5f794a079e124c150a2aa99edb28f6861")
                                                                                     (Tm.db 8))
                                                                                  (Tm.db 7))
                                                                               (Tm.db 1))
                                                                            (Pf.hyp 1)))
                                                                      (Pf.proofApp
                                                                         (Pf.proofApp
                                                                            (Pf.termApp
                                                                               (Pf.termApp
                                                                                  (Pf.termApp
                                                                                     (Pf.typeApp
                                                                                        (Pf.known
                                                                                           "0224060d7b7d5b6b2e8e4157524c8e4a18e5d17073c5b2fb2bb0c2583274fbc7")
                                                                                        (Tp.var
                                                                                           0))
                                                                                     (Tm.app
                                                                                        (Tm.app
                                                                                           (Tm.db
                                                                                              5)
                                                                                           (Tm.db
                                                                                              1))
                                                                                        (Tm.db
                                                                                           0)))
                                                                                  (Tm.app
                                                                                     (Tm.app
                                                                                        (Tm.db 5)
                                                                                        (Tm.db 1))
                                                                                     (Tm.app
                                                                                        (Tm.db 4)
                                                                                        (Tm.db
                                                                                           1))))
                                                                               (Tm.app
                                                                                  (Tm.db 4)
                                                                                  (Tm.app
                                                                                     (Tm.db 7)
                                                                                     (Tm.db 1))))
                                                                            (Pf.proofApp
                                                                               (Pf.termApp
                                                                                  (Pf.hyp 0)
                                                                                  (Tm.lam
                                                                                     (Tp.var 0)
                                                                                     (Tm.app
                                                                                        (Tm.app
                                                                                           (Tm.typeApp
                                                                                              (Tm.named
                                                                                                 "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                                                              (Tp.var
                                                                                                 0))
                                                                                           (Tm.app
                                                                                              (Tm.app
                                                                                                 (Tm.db
                                                                                                    6)
                                                                                                 (Tm.db
                                                                                                    2))
                                                                                              (Tm.db
                                                                                                 1)))
                                                                                        (Tm.app
                                                                                           (Tm.app
                                                                                              (Tm.db
                                                                                                 6)
                                                                                              (Tm.db
                                                                                                 2))
                                                                                           (Tm.db
                                                                                              0)))))
                                                                               (Pf.termApp
                                                                                  (Pf.typeApp
                                                                                     (Pf.known
                                                                                        "0f730be4ec19d9c14f6f80059c561f714dcecb54d8fa04f3570d0607e71d8331")
                                                                                     (Tp.var 0))
                                                                                  (Tm.app
                                                                                     (Tm.app
                                                                                        (Tm.db 5)
                                                                                        (Tm.db 1))
                                                                                     (Tm.db 0)))))
                                                                         (Pf.proofApp
                                                                            (Pf.termApp
                                                                               (Pf.hyp 5)
                                                                               (Tm.db 1))
                                                                            (Pf.hyp 1)))))
                                                                (Pf.proofApp
                                                                   (Pf.termApp
                                                                      (Pf.termApp
                                                                         (Pf.known
                                                                            "fec5ab340a042c8361bb0564ac980cfe10dabcf5c4aeacb0746c0daa4ac55417")
                                                                         (Tm.app
                                                                            (Tm.app
                                                                               (Tm.app
                                                                                  (Tm.named
                                                                                     "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                                                                  (Tm.db 8))
                                                                               (Tm.db 7))
                                                                            (Tm.db 1)))
                                                                      (Tm.app
                                                                         (Tm.app
                                                                            (Tm.typeApp
                                                                               (Tm.named
                                                                                  "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                                               (Tp.var 0))
                                                                            (Tm.db 0))
                                                                         (Tm.app
                                                                            (Tm.db 4)
                                                                            (Tm.db 1))))
                                                                   (Pf.hyp 1))))
                                                          (Pf.proofApp
                                                             (Pf.termApp
                                                                (Pf.termApp
                                                                   (Pf.known
                                                                      "eb8814e5b67181dcc2fdd7f757e9f1e3c90bcd9b3117f2bb9aa7650cdaac5b42")
                                                                   (Tm.app
                                                                      (Tm.app
                                                                         (Tm.app
                                                                            (Tm.named
                                                                               "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                                                            (Tm.db 8))
                                                                         (Tm.db 7))
                                                                      (Tm.db 1)))
                                                                (Tm.app
                                                                   (Tm.app
                                                                      (Tm.typeApp
                                                                         (Tm.named
                                                                            "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                                         (Tp.var 0))
                                                                      (Tm.db 0))
                                                                   (Tm.app (Tm.db 4) (Tm.db 1))))
                                                             (Pf.hyp 0))))))))
                                        (Pf.proofApp
                                           (Pf.proofApp
                                              (Pf.termApp
                                                 (Pf.termApp
                                                    (Pf.known
                                                       "7f6246d08629eeb16eab93529ffe4f929f43344833ab88c7786393693520e82b")
                                                    (Tm.app
                                                       (Tm.app
                                                          (Tm.app
                                                             (Tm.named
                                                                "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                                             (Tm.db 6))
                                                          (Tm.db 5))
                                                       (Tm.db 6)))
                                                 (Tm.app
                                                    (Tm.app
                                                       (Tm.typeApp
                                                          (Tm.named
                                                             "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                          (Tp.var 0))
                                                       (Tm.db 4))
                                                    (Tm.app (Tm.db 2) (Tm.db 6))))
                                              (Pf.termApp
                                                 (Pf.termApp
                                                    (Pf.known
                                                       "a7a2e1cb291bdfdc11661c2875e62b3fb8fb502cb3c1f594c4e6f50789e4f911")
                                                    (Tm.db 6))
                                                 (Tm.db 5)))
                                           (Pf.hyp 2))))))))))))))

def nrRecursorUnique : Item :=
  Item.theorem_
    "70070a87b34c9fe09d07002bd1a4cc494307f58100fa9aa1954e741d15c1d028"
    (Tm.typeAll
       (Tm.all
          (Tp.base 0)
          (Tm.all
             (Tp.arr (Tp.base 0) (Tp.base 0))
             (Tm.all
                (Tp.var 0)
                (Tm.all
                   (Tp.arr (Tp.base 0) (Tp.arr (Tp.var 0) (Tp.var 0)))
                   (Tm.all
                      (Tp.arr (Tp.arr (Tp.var 0) Tp.prop) (Tp.var 0))
                      (Tm.imp
                         (Tm.all
                            (Tp.arr (Tp.var 0) Tp.prop)
                            (Tm.imp
                               (Tm.app
                                  (Tm.typeApp
                                     (Tm.named
                                        "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099")
                                     (Tp.var 0))
                                  (Tm.db 0))
                               (Tm.app (Tm.db 0) (Tm.app (Tm.db 1) (Tm.db 0)))))
                         fragment37)))))))
    (Pf.typeLam
       (Pf.termLam
          (Tp.base 0)
          (Pf.termLam
             (Tp.arr (Tp.base 0) (Tp.base 0))
             (Pf.termLam
                (Tp.var 0)
                (Pf.termLam
                   (Tp.arr (Tp.base 0) (Tp.arr (Tp.var 0) (Tp.var 0)))
                   (Pf.termLam
                      (Tp.arr (Tp.arr (Tp.var 0) Tp.prop) (Tp.var 0))
                      (Pf.proofLam
                         (Tm.all
                            (Tp.arr (Tp.var 0) Tp.prop)
                            (Tm.imp
                               (Tm.app
                                  (Tm.typeApp
                                     (Tm.named
                                        "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099")
                                     (Tp.var 0))
                                  (Tm.db 0))
                               (Tm.app (Tm.db 0) (Tm.app (Tm.db 1) (Tm.db 0)))))
                         (Pf.termLam
                            (Tp.arr (Tp.base 0) (Tp.var 0))
                            (Pf.proofLam
                               (Tm.app
                                  (Tm.app
                                     (Tm.typeApp
                                        (Tm.named
                                           "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                        (Tp.var 0))
                                     (Tm.db 3))
                                  (Tm.app (Tm.db 0) (Tm.db 5)))
                               (Pf.proofLam
                                  (Tm.all
                                     (Tp.base 0)
                                     (Tm.imp
                                        (Tm.app
                                           (Tm.app
                                              (Tm.app
                                                 (Tm.named
                                                    "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                                 (Tm.db 6))
                                              (Tm.db 5))
                                           (Tm.db 0))
                                        (Tm.app
                                           (Tm.app
                                              (Tm.typeApp
                                                 (Tm.named
                                                    "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                 (Tp.var 0))
                                              (Tm.app
                                                 (Tm.app (Tm.db 3) (Tm.db 0))
                                                 (Tm.app (Tm.db 1) (Tm.db 0))))
                                           (Tm.app (Tm.db 1) (Tm.app (Tm.db 5) (Tm.db 0))))))
                                  (Pf.termLam
                                     (Tp.base 0)
                                     (Pf.proofLam
                                        (Tm.app
                                           (Tm.app
                                              (Tm.app
                                                 (Tm.named
                                                    "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                                 (Tm.db 6))
                                              (Tm.db 5))
                                           (Tm.db 0))
                                        (Pf.proofApp
                                           (Pf.termApp
                                              (Pf.termApp
                                                 (Pf.proofApp
                                                    (Pf.proofApp
                                                       (Pf.termApp
                                                          (Pf.termApp
                                                             (Pf.termApp
                                                                (Pf.termApp
                                                                   (Pf.termApp
                                                                      (Pf.typeApp
                                                                         (Pf.known
                                                                            "3861803eb83e09998ef34c354bc50aff520951f2031b7842559c0195eed45b6a")
                                                                         (Tp.var 0))
                                                                      (Tm.db 6))
                                                                   (Tm.db 5))
                                                                (Tm.db 4))
                                                             (Tm.db 3))
                                                          (Tm.db 1))
                                                       (Pf.hyp 2))
                                                    (Pf.hyp 1))
                                                 (Tm.db 0))
                                              fragment35)
                                           (Pf.proofApp
                                              (Pf.termApp
                                                 (Pf.proofApp
                                                    (Pf.termApp
                                                       (Pf.termApp
                                                          (Pf.termApp
                                                             (Pf.termApp
                                                                (Pf.termApp
                                                                   (Pf.typeApp
                                                                      (Pf.known
                                                                         "fcb71074cf42d8987389724f3694303d976cba70c34d7ab333bd93760834c280")
                                                                      (Tp.var 0))
                                                                   (Tm.db 6))
                                                                (Tm.db 5))
                                                             (Tm.db 4))
                                                          (Tm.db 3))
                                                       (Tm.db 2))
                                                    (Pf.hyp 3))
                                                 (Tm.db 0))
                                              (Pf.hyp 0)))))))))))))))

def nrRecursorChoiceIndependent : Item :=
  Item.theorem_
    "774b429367f63d3e6b40bf4661f1818d19b4a7cb60f28dccfc014f27da5348f8"
    (Tm.typeAll
       (Tm.all
          (Tp.base 0)
          (Tm.all
             (Tp.arr (Tp.base 0) (Tp.base 0))
             (Tm.imp
                (Tm.all
                   (Tp.base 0)
                   (Tm.imp
                      (Tm.app
                         (Tm.app
                            (Tm.typeApp
                               (Tm.named
                                  "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                               (Tp.base 0))
                            (Tm.app (Tm.db 1) (Tm.db 0)))
                         (Tm.db 2))
                      (Tm.named
                         "5bf697cb0d1cdefbe881504469f6c48cc388994115b82514dfc4fb5e67ac1a87")))
                (Tm.imp
                   (Tm.all
                      (Tp.base 0)
                      (Tm.all
                         (Tp.base 0)
                         (Tm.imp
                            (Tm.app
                               (Tm.app
                                  (Tm.typeApp
                                     (Tm.named
                                        "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                     (Tp.base 0))
                                  (Tm.app (Tm.db 2) (Tm.db 1)))
                               (Tm.app (Tm.db 2) (Tm.db 0)))
                            (Tm.app
                               (Tm.app
                                  (Tm.typeApp
                                     (Tm.named
                                        "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                     (Tp.base 0))
                                  (Tm.db 1))
                               (Tm.db 0)))))
                   (Tm.all
                      (Tp.var 0)
                      (Tm.all
                         (Tp.arr (Tp.base 0) (Tp.arr (Tp.var 0) (Tp.var 0)))
                         (Tm.all
                            (Tp.arr (Tp.arr (Tp.var 0) Tp.prop) (Tp.var 0))
                            (Tm.all
                               (Tp.arr (Tp.arr (Tp.var 0) Tp.prop) (Tp.var 0))
                               (Tm.imp
                                  (Tm.all
                                     (Tp.arr (Tp.var 0) Tp.prop)
                                     (Tm.imp
                                        (Tm.app
                                           (Tm.typeApp
                                              (Tm.named
                                                 "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099")
                                              (Tp.var 0))
                                           (Tm.db 0))
                                        (Tm.app (Tm.db 0) (Tm.app (Tm.db 2) (Tm.db 0)))))
                                  (Tm.imp
                                     (Tm.all
                                        (Tp.arr (Tp.var 0) Tp.prop)
                                        (Tm.imp
                                           (Tm.app
                                              (Tm.typeApp
                                                 (Tm.named
                                                    "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099")
                                                 (Tp.var 0))
                                              (Tm.db 0))
                                           (Tm.app (Tm.db 0) (Tm.app (Tm.db 1) (Tm.db 0)))))
                                     (Tm.all
                                        (Tp.base 0)
                                        (Tm.imp
                                           (Tm.app
                                              (Tm.app
                                                 (Tm.app
                                                    (Tm.named
                                                       "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                                    (Tm.db 6))
                                                 (Tm.db 5))
                                              (Tm.db 0))
                                           (Tm.app
                                              fragment36
                                              (Tm.app
                                                 (Tm.app
                                                    (Tm.app
                                                       (Tm.app
                                                          (Tm.app
                                                             (Tm.app
                                                                (Tm.typeApp
                                                                   (Tm.named
                                                                      "07c6d5bb8b1b51acf568b644d496c3805612be5b440432b88ee69c28280f8c5d")
                                                                   (Tp.var 0))
                                                                (Tm.db 6))
                                                             (Tm.db 5))
                                                          (Tm.db 4))
                                                       (Tm.db 3))
                                                    (Tm.db 1))
                                                 (Tm.db 0))))))))))))))))
    (Pf.typeLam
       (Pf.termLam
          (Tp.base 0)
          (Pf.termLam
             (Tp.arr (Tp.base 0) (Tp.base 0))
             (Pf.proofLam
                (Tm.all
                   (Tp.base 0)
                   (Tm.imp
                      (Tm.app
                         (Tm.app
                            (Tm.typeApp
                               (Tm.named
                                  "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                               (Tp.base 0))
                            (Tm.app (Tm.db 1) (Tm.db 0)))
                         (Tm.db 2))
                      (Tm.named
                         "5bf697cb0d1cdefbe881504469f6c48cc388994115b82514dfc4fb5e67ac1a87")))
                (Pf.proofLam
                   (Tm.all
                      (Tp.base 0)
                      (Tm.all
                         (Tp.base 0)
                         (Tm.imp
                            (Tm.app
                               (Tm.app
                                  (Tm.typeApp
                                     (Tm.named
                                        "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                     (Tp.base 0))
                                  (Tm.app (Tm.db 2) (Tm.db 1)))
                               (Tm.app (Tm.db 2) (Tm.db 0)))
                            (Tm.app
                               (Tm.app
                                  (Tm.typeApp
                                     (Tm.named
                                        "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                     (Tp.base 0))
                                  (Tm.db 1))
                               (Tm.db 0)))))
                   (Pf.termLam
                      (Tp.var 0)
                      (Pf.termLam
                         (Tp.arr (Tp.base 0) (Tp.arr (Tp.var 0) (Tp.var 0)))
                         (Pf.termLam
                            (Tp.arr (Tp.arr (Tp.var 0) Tp.prop) (Tp.var 0))
                            (Pf.termLam
                               (Tp.arr (Tp.arr (Tp.var 0) Tp.prop) (Tp.var 0))
                               (Pf.proofLam
                                  (Tm.all
                                     (Tp.arr (Tp.var 0) Tp.prop)
                                     (Tm.imp
                                        (Tm.app
                                           (Tm.typeApp
                                              (Tm.named
                                                 "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099")
                                              (Tp.var 0))
                                           (Tm.db 0))
                                        (Tm.app (Tm.db 0) (Tm.app (Tm.db 2) (Tm.db 0)))))
                                  (Pf.proofLam
                                     (Tm.all
                                        (Tp.arr (Tp.var 0) Tp.prop)
                                        (Tm.imp
                                           (Tm.app
                                              (Tm.typeApp
                                                 (Tm.named
                                                    "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099")
                                                 (Tp.var 0))
                                              (Tm.db 0))
                                           (Tm.app (Tm.db 0) (Tm.app (Tm.db 1) (Tm.db 0)))))
                                     (Pf.proofApp
                                        (Pf.proofApp
                                           (Pf.termApp
                                              (Pf.proofApp
                                                 (Pf.termApp
                                                    (Pf.termApp
                                                       (Pf.termApp
                                                          (Pf.termApp
                                                             (Pf.termApp
                                                                (Pf.typeApp
                                                                   (Pf.known
                                                                      "70070a87b34c9fe09d07002bd1a4cc494307f58100fa9aa1954e741d15c1d028")
                                                                   (Tp.var 0))
                                                                (Tm.db 5))
                                                             (Tm.db 4))
                                                          (Tm.db 3))
                                                       (Tm.db 2))
                                                    (Tm.db 1))
                                                 (Pf.hyp 1))
                                              (Tm.app
                                                 (Tm.app
                                                    (Tm.app
                                                       (Tm.app
                                                          (Tm.app
                                                             (Tm.typeApp
                                                                (Tm.named
                                                                   "07c6d5bb8b1b51acf568b644d496c3805612be5b440432b88ee69c28280f8c5d")
                                                                (Tp.var 0))
                                                             (Tm.db 5))
                                                          (Tm.db 4))
                                                       (Tm.db 3))
                                                    (Tm.db 2))
                                                 (Tm.db 0)))
                                           (Pf.proofApp
                                              (Pf.termApp
                                                 (Pf.termApp
                                                    (Pf.termApp
                                                       (Pf.proofApp
                                                          (Pf.termApp
                                                             (Pf.termApp
                                                                (Pf.typeApp
                                                                   (Pf.known
                                                                      "22e3b03874328016e540ab23671ef8d65aedae835b5a6300a63169ce15d2cf5c")
                                                                   (Tp.var 0))
                                                                (Tm.db 5))
                                                             (Tm.db 4))
                                                          (Pf.hyp 3))
                                                       (Tm.db 3))
                                                    (Tm.db 2))
                                                 (Tm.db 0))
                                              (Pf.hyp 0)))
                                        (Pf.proofApp
                                           (Pf.termApp
                                              (Pf.termApp
                                                 (Pf.termApp
                                                    (Pf.proofApp
                                                       (Pf.proofApp
                                                          (Pf.termApp
                                                             (Pf.termApp
                                                                (Pf.typeApp
                                                                   (Pf.known
                                                                      "1d0d22f0333064db2f7008d20316b35d84fc8bf4adc664060b8860cd94977e5f")
                                                                   (Tp.var 0))
                                                                (Tm.db 5))
                                                             (Tm.db 4))
                                                          (Pf.hyp 3))
                                                       (Pf.hyp 2))
                                                    (Tm.db 3))
                                                 (Tm.db 2))
                                              (Tm.db 0))
                                           (Pf.hyp 0))))))))))))))

def nrRecursion : Item :=
  Item.theorem_
    "c68747a1a75e217cf39d616a8d4b4d58b3cb63e8e0a2cedb9e8b17094aaae1f4"
    (Tm.typeAll
       (Tm.all
          (Tp.base 0)
          (Tm.all
             (Tp.arr (Tp.base 0) (Tp.base 0))
             (Tm.imp
                (Tm.all
                   (Tp.base 0)
                   (Tm.imp
                      (Tm.app
                         (Tm.app
                            (Tm.typeApp
                               (Tm.named
                                  "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                               (Tp.base 0))
                            (Tm.app (Tm.db 1) (Tm.db 0)))
                         (Tm.db 2))
                      (Tm.named
                         "5bf697cb0d1cdefbe881504469f6c48cc388994115b82514dfc4fb5e67ac1a87")))
                (Tm.imp
                   (Tm.all
                      (Tp.base 0)
                      (Tm.all
                         (Tp.base 0)
                         (Tm.imp
                            (Tm.app
                               (Tm.app
                                  (Tm.typeApp
                                     (Tm.named
                                        "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                     (Tp.base 0))
                                  (Tm.app (Tm.db 2) (Tm.db 1)))
                               (Tm.app (Tm.db 2) (Tm.db 0)))
                            (Tm.app
                               (Tm.app
                                  (Tm.typeApp
                                     (Tm.named
                                        "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                     (Tp.base 0))
                                  (Tm.db 1))
                               (Tm.db 0)))))
                   (Tm.all
                      (Tp.var 0)
                      (Tm.all
                         (Tp.arr (Tp.base 0) (Tp.arr (Tp.var 0) (Tp.var 0)))
                         (Tm.all
                            (Tp.arr (Tp.arr (Tp.var 0) Tp.prop) (Tp.var 0))
                            (Tm.imp
                               (Tm.all
                                  (Tp.arr (Tp.var 0) Tp.prop)
                                  (Tm.imp
                                     (Tm.app
                                        (Tm.typeApp
                                           (Tm.named
                                              "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099")
                                           (Tp.var 0))
                                        (Tm.db 0))
                                     (Tm.app (Tm.db 0) (Tm.app (Tm.db 1) (Tm.db 0)))))
                               (Tm.app
                                  (Tm.typeApp
                                     (Tm.named
                                        "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099")
                                     (Tp.arr (Tp.base 0) (Tp.var 0)))
                                  fragment38))))))))))
    (Pf.typeLam
       (Pf.termLam
          (Tp.base 0)
          (Pf.termLam
             (Tp.arr (Tp.base 0) (Tp.base 0))
             (Pf.proofLam
                (Tm.all
                   (Tp.base 0)
                   (Tm.imp
                      (Tm.app
                         (Tm.app
                            (Tm.typeApp
                               (Tm.named
                                  "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                               (Tp.base 0))
                            (Tm.app (Tm.db 1) (Tm.db 0)))
                         (Tm.db 2))
                      (Tm.named
                         "5bf697cb0d1cdefbe881504469f6c48cc388994115b82514dfc4fb5e67ac1a87")))
                (Pf.proofLam
                   (Tm.all
                      (Tp.base 0)
                      (Tm.all
                         (Tp.base 0)
                         (Tm.imp
                            (Tm.app
                               (Tm.app
                                  (Tm.typeApp
                                     (Tm.named
                                        "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                     (Tp.base 0))
                                  (Tm.app (Tm.db 2) (Tm.db 1)))
                               (Tm.app (Tm.db 2) (Tm.db 0)))
                            (Tm.app
                               (Tm.app
                                  (Tm.typeApp
                                     (Tm.named
                                        "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                     (Tp.base 0))
                                  (Tm.db 1))
                               (Tm.db 0)))))
                   (Pf.termLam
                      (Tp.var 0)
                      (Pf.termLam
                         (Tp.arr (Tp.base 0) (Tp.arr (Tp.var 0) (Tp.var 0)))
                         (Pf.termLam
                            (Tp.arr (Tp.arr (Tp.var 0) Tp.prop) (Tp.var 0))
                            (Pf.proofLam
                               (Tm.all
                                  (Tp.arr (Tp.var 0) Tp.prop)
                                  (Tm.imp
                                     (Tm.app
                                        (Tm.typeApp
                                           (Tm.named
                                              "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099")
                                           (Tp.var 0))
                                        (Tm.db 0))
                                     (Tm.app (Tm.db 0) (Tm.app (Tm.db 1) (Tm.db 0)))))
                               (Pf.proofApp
                                  (Pf.termApp
                                     (Pf.termApp
                                        (Pf.typeApp
                                           (Pf.known
                                              "cb01597ac16d6df38d6f584e549edd3603cd7abc72e2a1cfcc2ba44fc649758e")
                                           (Tp.arr (Tp.base 0) (Tp.var 0)))
                                        fragment38)
                                     (Tm.app
                                        (Tm.app
                                           (Tm.app
                                              (Tm.app
                                                 (Tm.app
                                                    (Tm.typeApp
                                                       (Tm.named
                                                          "07c6d5bb8b1b51acf568b644d496c3805612be5b440432b88ee69c28280f8c5d")
                                                       (Tp.var 0))
                                                    (Tm.db 4))
                                                 (Tm.db 3))
                                              (Tm.db 2))
                                           (Tm.db 1))
                                        (Tm.db 0)))
                                  (Pf.proofApp
                                     (Pf.proofApp
                                        (Pf.termApp
                                           (Pf.termApp
                                              (Pf.known
                                                 "7f6246d08629eeb16eab93529ffe4f929f43344833ab88c7786393693520e82b")
                                              fragment31)
                                           (Tm.app
                                              (Tm.app
                                                 (Tm.named
                                                    "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
                                                 fragment34)
                                              fragment37))
                                        (Pf.proofApp
                                           (Pf.termApp
                                              (Pf.termApp
                                                 (Pf.termApp
                                                    (Pf.proofApp
                                                       (Pf.termApp
                                                          (Pf.termApp
                                                             (Pf.typeApp
                                                                (Pf.known
                                                                   "22e3b03874328016e540ab23671ef8d65aedae835b5a6300a63169ce15d2cf5c")
                                                                (Tp.var 0))
                                                             (Tm.db 4))
                                                          (Tm.db 3))
                                                       (Pf.hyp 2))
                                                    (Tm.db 2))
                                                 (Tm.db 1))
                                              (Tm.db 0))
                                           (Pf.hyp 0)))
                                     (Pf.proofApp
                                        (Pf.proofApp
                                           (Pf.termApp
                                              (Pf.termApp
                                                 (Pf.known
                                                    "7f6246d08629eeb16eab93529ffe4f929f43344833ab88c7786393693520e82b")
                                                 fragment34)
                                              fragment37)
                                           (Pf.proofApp
                                              (Pf.termApp
                                                 (Pf.termApp
                                                    (Pf.termApp
                                                       (Pf.proofApp
                                                          (Pf.proofApp
                                                             (Pf.termApp
                                                                (Pf.termApp
                                                                   (Pf.typeApp
                                                                      (Pf.known
                                                                         "1d0d22f0333064db2f7008d20316b35d84fc8bf4adc664060b8860cd94977e5f")
                                                                      (Tp.var 0))
                                                                   (Tm.db 4))
                                                                (Tm.db 3))
                                                             (Pf.hyp 2))
                                                          (Pf.hyp 1))
                                                       (Tm.db 2))
                                                    (Tm.db 1))
                                                 (Tm.db 0))
                                              (Pf.hyp 0)))
                                        (Pf.proofApp
                                           (Pf.termApp
                                              (Pf.termApp
                                                 (Pf.termApp
                                                    (Pf.termApp
                                                       (Pf.termApp
                                                          (Pf.typeApp
                                                             (Pf.known
                                                                "70070a87b34c9fe09d07002bd1a4cc494307f58100fa9aa1954e741d15c1d028")
                                                             (Tp.var 0))
                                                          (Tm.db 4))
                                                       (Tm.db 3))
                                                    (Tm.db 2))
                                                 (Tm.db 1))
                                              (Tm.db 0))
                                           (Pf.hyp 0))))))))))))))

def items : List Item := [ncAnd, naturalClosure, ncAndIntro, ncAndLeft, ncAndRight, naturalClosureZero, naturalClosureSuccessor, naturalClosureInduction, nrFalse, nrEq, nrExists, nrEqRefl, nrEqSym, nrEqTrans, nrExistsIntro, nrGraph, nrGraphZero, nrGraphSuccessor, nrGraphNatural, nrGraphExists, nrGraphZeroUnique, nrGraphSuccessorInverse, nrGraphFunctional, nrRecursor, nrRecursorGraph, nrRecursorZero, nrRecursorSuccessor, nrGraphAgrees, nrRecursorUnique, nrRecursorChoiceIndependent, nrRecursion]

def inputBytes : Nat := 88744

end Mettapedia.Languages.Megalodon.NaturalRecursion.Evidence
