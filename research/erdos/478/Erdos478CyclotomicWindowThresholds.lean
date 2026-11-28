import Erdos478PoweredFactorialProfiles
import Erdos478CompleteFactorialProfiles
import Mathlib.NumberTheory.PrimesCongruentOne

/-! # Moving factorial-power windows for primes in an arithmetic progression -/

namespace Erdos478.CyclotomicProfiles
open Finset
open scoped Classical

/-- At scale `t`, every window contains more than `t^12` power residues.
Every target of at most `t^10` residues has an explicit upper bound on its visits. -/
def windowSpread (p t a : ℕ) : Prop :=
  let h := 2*t^18
  let I := Icc a (a+h^2+1)
  t^12 < (I.image (fun i => i.factorial^h%p)).card ∧
    ∀ T : Finset ℕ, T.card ≤ t^10 →
      3*(I.filter fun i => i.factorial^h%p∈T).card ≤ 2*(h^2+2)+2+3*t^33

/-- The estimate holds for every qualifying prime and every placement of the window. -/
theorem progression_windows {p : ℕ} [Fact p.Prime] (t a : ℕ) (ht : 2 ≤ t)
    (cong : p ≡ 1 [MOD 2*t^18]) (hi : a+(2*t^18)^2+1 < p) : windowSpread p t a := by
  let h := 2*t^18
  let b := a+h^2+1
  let I := Icc a b
  have lim : b < p := hi
  have gcd : (p-1).gcd h=h := Nat.gcd_eq_right cong.symm.dvd'
  have span : b-a-1=h^2 := by dsimp [b]; omega
  have card : I.card=h^2+2 := by dsimp [I,b]; rw [Nat.card_Icc]; omega
  have prod : (h-1)*(h-2)≤h^2 := by rw [pow_two]; exact Nat.mul_le_mul (Nat.sub_le ..) (Nat.sub_le ..)
  have le : h^2+(h-1)*(h-2)≤2*h^2 := by omega
  change t^12 < (I.image (fun i => i.factorial^h%p)).card ∧ _
  constructor
  · let s := (I.image (fun i => i.factorial^h%p)).card
    have eq := powered_window_bound (p:=p) h a b lim
    change (b-a-1)^2≤s^3*((b-a-1)+((p-1).gcd h-1)*((p-1).gcd h-2)) at eq
    rw [gcd,span] at eq
    change t^12 < s
    by_contra! few
    have upper := eq.trans (Nat.mul_le_mul (Nat.pow_le_pow_left few 3) le)
    dsimp [h] at upper
    have pos : 0<t^72 := by positivity
    nlinarith only [upper,pos]
  · intro T small
    let M := (I.filter fun i => i.factorial^h%p∈T).card
    have eq := powered_excess_mass (p:=p) h a b lim T
    change (3*M-(2*I.card+2))^2≤T.card^3*((b-a-1)+((p-1).gcd h-1)*((p-1).gcd h-2)) at eq
    rw [gcd,span,card] at eq
    have bound := eq.trans (Nat.mul_le_mul (Nat.pow_le_pow_left small 3) le)
    have last : (t^10)^3*(2*h^2) ≤ (3*t^33)^2 := by dsimp [h]; nlinarith only [Nat.zero_le (t^66)]
    have root := (Nat.pow_le_pow_iff_left (by decide : (2:ℕ) ≠ 0)).mp (bound.trans last)
    change 3*M≤2*(h^2+2)+2+3*t^33
    omega

/-- The window is nonvacuous at each scale and at arbitrarily large prime moduli. -/
theorem unbounded_progression_windows (t L : ℕ) (ht : 2 ≤ t) :
    ∃ p : ℕ, p.Prime ∧ max L ((2*t^18)^2+2)<p ∧ p ≡ 1 [MOD 2*t^18] ∧
      ∀ a : ℕ, 1 ≤ a → a+(2*t^18)^2+1 < p → windowSpread p t a := by
  obtain ⟨p,hp,large,cong⟩ := Nat.exists_prime_gt_modEq_one (max L ((2*t^18)^2+2))
    (by positivity : 2*t^18≠0)
  let : Fact p.Prime := ⟨hp⟩
  exact ⟨p,hp,large,cong,fun a _ => progression_windows t a ht cong⟩

#print axioms windowSpread
#print axioms progression_windows
#print axioms unbounded_progression_windows
end Erdos478.CyclotomicProfiles
