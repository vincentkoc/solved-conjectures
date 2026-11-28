import Green51PeriodClassCount

/-! # A mixed-period example with 58 missing directions -/

namespace Green51PeriodQuotients
open Finset Green53ParityThreshold Green51MissingMasks Green51OriginRecovery Green51Hyperplane
open scoped Classical

private theorem labelled_58 : (countedDoubles 16 58 (threshold 12)).card=28102653529083837296204946696112126538892223460354398617600 := by
  have count := count_dense_doubles (s := 6) (r := 2) (by decide) 58 (by decide)
  have exact_count :
      (((∏ i : Fin 14, (2^16-2^i.val : ℕ)) : ℕ) : ℤ) *
        (∑ j∈range 16, ((Nat.choose 15 j : ℕ) : ℤ) * ((-1 : ℤ)^j * (((15-j)*2^2).choose 58 : ℕ))) =
        (28102653529083837296204946696112126538892223460354398617600 : ℤ)*(Nat.factorial 15 : ℕ) := by
    simp_rw [Nat.choose_eq_descFactorial_div_factorial]
    decide +kernel
  apply Nat.cast_injective (R := ℤ)
  exact mul_right_cancel₀ (by positivity : ((Nat.factorial 15 : ℕ) : ℤ) ≠ 0) (count.trans exact_count)

private theorem labelled_29 : (countedDoubles 15 29 (threshold 12)).card=21804356214689656552680438603343375739623327263621120 := by
  have count := count_dense_doubles (s := 6) (r := 1) (by decide) 29 (by decide)
  have exact_count :
      (((∏ i : Fin 14, (2^15-2^i.val : ℕ)) : ℕ) : ℤ) *
        (∑ j∈range 16, ((Nat.choose 15 j : ℕ) : ℤ) * ((-1 : ℤ)^j * (((15-j)*2^1).choose 29 : ℕ))) =
        (21804356214689656552680438603343375739623327263621120 : ℤ)*(Nat.factorial 15 : ℕ) := by
    simp_rw [Nat.choose_eq_descFactorial_div_factorial]
    decide +kernel
  apply Nat.cast_injective (R := ℤ)
  exact mul_right_cancel₀ (by positivity : ((Nat.factorial 15 : ℕ) : ℤ) ≠ 0) (count.trans exact_count)

private theorem even_instance {s r k n d j b a t : ℕ} (hs : 5 ≤ s)
    (near : min (5*(2*s+3)+12) (4*(2*s+3)+20)*2^r < 8*k) (even : 2∣k)
    (dim : 2*(s+1)+r=n) (smaller : n-1=d) (half : k/2=j) (level : 2*s=b)
    (period : 2^r=a) (directions : 2^n-1=t) :
    ((countedDoubles n k (threshold b)).image translationClass).card*a =
      (countedDoubles n k (threshold b)).card+t*(countedDoubles d j (threshold b)).card := by
  have result := all_class_counts hs near
  dsimp only at result
  rw [dim,smaller,half,level,period,directions,if_pos even] at result
  exact result

/-- Translation classes in the dimension-sixteen example with an even missing count. -/
theorem classes_at_fifty_eight :
    ((countedDoubles 16 58 (threshold 12)).image translationClass).card=7382900503403380984596214809995558666997109553143952179200 := by
  have count := even_instance (s := 6) (r := 2) (k := 58) (n := 16) (d := 15) (j := 29)
    (b := 12) (a := 4) (t := 65535) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have arithmetic (x y z : ℕ) (base : x*4=y+65535*z) (big : y=28102653529083837296204946696112126538892223460354398617600)
      (small : z=21804356214689656552680438603343375739623327263621120) : x=7382900503403380984596214809995558666997109553143952179200 := by omega
  let x := ((countedDoubles 16 58 (threshold 12)).image translationClass).card
  let y := (countedDoubles 16 58 (threshold 12)).card
  let z := (countedDoubles 15 29 (threshold 12)).card
  exact arithmetic x y z count labelled_58 labelled_29

end Green51PeriodQuotients
#print axioms Green51PeriodQuotients.classes_at_fifty_eight
