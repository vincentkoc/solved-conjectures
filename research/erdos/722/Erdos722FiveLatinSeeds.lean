import Erdos722FiveOrthogonalArrays

/-!
# Orthogonal-array ingredients at orders 14 and 15

The letters in each row give the symbols of a Latin square in order.
These three squares at each order are from the matrices shared by Ian
Wanless in the SageMath design database. The projection test checks all
ordered pairs independently of the source.
-/

namespace Erdos722.Five.Array
open Erdos722.Quartet

private def entries {t : ℕ} [NeZero t] (rows : Fin 3 → Fin t → String)
    (r : Fin (t*t)) : Fin 5 → Fin t :=
  let p := finProdFinEquiv.symm r
  let read := fun s : Fin 3 =>
    Fin.ofNat t (((rows s p.1).toList[p.2.val]?.getD 'a').toNat - 'a'.toNat)
  ![p.1,p.2,read 0,read 1,read 2]

set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

private def squares14 : Fin 3 → Fin 14 → String :=
  ![!["bjihgkecalnfmd",
      "fckjbhledimagn",
      "mgdlkcbafejnih",
      "cnhemldbigfkaj",
      "edabfnmkcjhgli",
      "nfeicgajldkbhm",
      "iagfjdhnkmelcb",
      "dlnkeafimhcjbg",
      "gemalfihjnbdkc",
      "jhfnimgdbkacel",
      "hkbgajnmeclidf",
      "ablchikgnfdmje",
      "licmdbjfhagenk",
      "kmjdneclgbihfa"],
    !["bfmcenidgjhalk",
      "jcgndfalehkbim",
      "ikdhaegnmfblcj",
      "hjlebifkangcmd",
      "gbkmfcjeliahdn",
      "khclngdafmjibe",
      "elbdmahfignkjc",
      "ceabkjnihdmgfl",
      "adficlkmjbenhg",
      "liegjdmhnkcfab",
      "nmjfhkecbaldgi",
      "fankgbljdcimeh",
      "mgialhcbkedjnf",
      "dnhjimbgclfeka"],
    !["bcdefghijklmna",
      "gnkjdmiclbhaef",
      "lifhbjemkangcd",
      "dalmgnbjehcfik",
      "njcaeifhbdgkml",
      "mfbkcdlagnjihe",
      "aemnhkjdcifblg",
      "hdnikbagmcelfj",
      "cgjflhnbiekdam",
      "fkibmagenldhjc",
      "imhlneckdfajgb",
      "klegafdnhjmcbi",
      "jhadicmlfgbekn",
      "ebgcjlkfamindh"]]

private theorem pairs14 : ∀ i j, i ≠ j →
    codes (entries squares14) i j = 2^(14*14)-1 := by decide +kernel

theorem columns14 {S : ℕ → Prop} (h5 : S 5) (ht : Has S 15) : Has S 71 :=
  fill (a := 1) (entries squares14) pairs14 h5 (by decide) ht

#print axioms columns14

private def squares15 : Fin 3 → Fin 15 → String :=
  ![!["bcdefghijklmnoa",
      "abcdefghijklmno",
      "oabcdefghijklmn",
      "noabcdefghijklm",
      "mnoabcdefghijkl",
      "lmnoabcdefghijk",
      "klmnoabcdefghij",
      "jklmnoabcdefghi",
      "ijklmnoabcdefgh",
      "hijklmnoabcdefg",
      "ghijklmnoabcdef",
      "fghijklmnoabcde",
      "efghijklmnoabcd",
      "defghijklmnoabc",
      "cdefghijklmnoab"],
    !["bdgiknfcamehjlo",
      "acehjlogdbnfikm",
      "nbdfikmahecogjl",
      "mocegjlnbifdahk",
      "lnadfhkmocjgebi",
      "jmobegilnadkhfc",
      "dknacfhjmobelig",
      "helobdgiknacfmj",
      "kifmacehjlobdgn",
      "oljgnbdfikmaceh",
      "iamkhocegjlnbdf",
      "gjbnliadfhkmoce",
      "fhkcomjbegilnad",
      "egildankcfhjmob",
      "cfhjmeboldgikna"],
    !["bhealiofmdjgcnk",
      "lcifbmjagnekhdo",
      "amdjgcnkbhoflie",
      "fbnekhdolciagmj",
      "kgcoflieamdjbhn",
      "olhdagmjfbnekci",
      "jamiebhnkgcofld",
      "ekbnjfciolhdagm",
      "nflcokgdjamiebh",
      "iogmdalhekbnjfc",
      "djahnebmiflcokg",
      "hekbiofcnjgmdal",
      "miflcjagdokhneb",
      "cnjgmdkbhealiof",
      "gdokhnelcifbmja"]]

private theorem pairs15 : ∀ i j, i ≠ j →
    codes (entries squares15) i j = 2^(15*15)-1 := by decide +kernel

theorem columns15 {S : ℕ → Prop} {a : ℕ} (h5 : S 5) (ha : a≤1) (ht : Has S (15+a)) :
    Has S (75+a) := fill (entries squares15) pairs15 h5 ha ht

#print axioms columns15

end Erdos722.Five.Array
