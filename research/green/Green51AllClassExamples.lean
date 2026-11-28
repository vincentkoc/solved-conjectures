import Green51AllDenseTranslationClasses
import Green51EvenMissingExample

/-! # Dense translation classes in dimension sixteen with 41 or 58 missing points -/

namespace Green51AffineTranslation
open Finset Green53ParityThreshold Green51AffineEnumeration Green51OriginRecovery Green51MissingMasks Green51Hyperplane
open scoped Classical

private theorem at_dimension {s r k n d : ℕ} (dim : 2*(s+1)+r=n) (cut : 2*s=d) (hs : 5 ≤ s)
    (near : min (5*(2*s+3)+12) (4*(2*s+3)+20)*2^r < 8*k) (cap : k≤(2*s+3)*2^r) :
    ((allDenseDoubles n k (threshold d)).image translationClass).card =
      affineOrbitNumber n k + ((countedDoubles n k (threshold d)).image translationClass).card := by
  subst n; subst d
  rw [dense_class_partition hs near cap,affine_orbit_number (by omega)]

theorem all_classes_at_forty_one :
    ((allDenseDoubles 16 41 (threshold 12)).image translationClass).card =
      7928103728893487990109864810634378435175833774100514925748982106775103444530718458370026409348564137075472953894377471628212171318289433 := by
  have aff : affineOrbitNumber 16 41=7928103728893487990109864810634378435175833774100514925748982106767929677132387280101874659406213426783042906253583060166346518701073433 := by decide +kernel
  rw [at_dimension (n := 16) (d := 12) (s := 6) (r := 2) rfl rfl (by decide) (by decide) (by decide),
    aff,classes_at_forty_one]

theorem all_classes_at_fifty_eight :
    ((allDenseDoubles 16 58 (threshold 12)).image translationClass).card =
      6368350476526998256950146054994540322347144801703302664917853315196231359843774702614515975622268215474313199772947819962780871863140322390448187723876204335334699876155870892625683915 := by
  have aff : affineOrbitNumber 16 58=6368350476526998256950146054994540322347144801703302664917853315196231359843774702614515975622268215474313199772947819962780864480239818987067203127661394339776032879046317748673504715 := by decide +kernel
  rw [at_dimension (n := 16) (d := 12) (s := 6) (r := 2) rfl rfl (by decide) (by decide) (by decide),
    aff,Green51PeriodQuotients.classes_at_fifty_eight]

end Green51AffineTranslation
#print axioms Green51AffineTranslation.all_classes_at_forty_one
#print axioms Green51AffineTranslation.all_classes_at_fifty_eight
