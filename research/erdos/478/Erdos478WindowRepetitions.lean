import Erdos478LocalCollisionResultant
import Mathlib.Data.Nat.Prime.Factorial

/-! # Separation of distinct pairs of equal factorial residues inside an interval -/

namespace Erdos478.LocalSpacing
open Finset Polynomial

/-- Both indices lie in the closed interval of span `H`, and are strictly ordered. -/
def Repetition (p a H i j : ℕ) : Prop :=
  a ≤ i ∧ i < j ∧ j≤a+H ∧ i.factorial%p=j.factorial%p

theorem collision_root {p a i j : ℕ} (hp : p.Prime) (ai : a ≤ i) (ij : i < j) (jp : j<p)
    (he : i.factorial%p=j.factorial%p) :
    (translatedGap (ZMod p) (j-a) (j-i)).IsRoot (a:ZMod p) := by
  let : Fact p.Prime := ⟨hp⟩
  have hn : (i.factorial:ZMod p)≠0 := by
    rw [Ne,CharP.cast_eq_zero_iff (ZMod p) p]
    exact fun h => (ij.trans jp).not_ge (hp.dvd_factorial.mp h)
  have pair := (ZMod.natCast_eq_natCast_iff' _ _ _).mpr he
  have pr := congrArg (fun n : ℕ => (n:ZMod p)) (Nat.factorial_mul_descFactorial (by omega : j-i≤j))
  rw [show j-(j-i)=i by omega,Nat.cast_mul] at pr
  have h : (j.descFactorial (j-i):ZMod p)=1 := by
    apply mul_left_cancel₀ hn
    simpa only [mul_one] using pr.trans pair.symm
  rw [IsRoot.def,translatedGap,taylor_eval,← Nat.cast_add,show a+(j-a)=j by omega,
    eval_sub,eval_one,descPochhammer_eval_eq_descFactorial,h,sub_self]

/-- The two actual gaps appear separately in the exponent. The common
interval may start anywhere in the pinned positive factorial domain. -/
theorem prime_le_of_two_repetitions {p a H i j u v : ℕ} (hp : p.Prime) (hu : a+H<p)
    (h : Repetition p a H i j) (g : Repetition p a H u v) (ne : (i,j)≠(u,v)) :
    p≤(H+2)^((j-i)*(v-u)) := by
  obtain ⟨ai,ij,jH,he⟩ := h
  obtain ⟨au,uv,vH,ge⟩ := g
  have h1 : 0<j-i := by omega
  have h2 : 0<v-u := by omega
  have dif : (j-a,j-i)≠(v-a,v-u) := by
    intro e
    obtain ⟨a1,a2⟩ := Prod.mk.inj e
    exact ne (Prod.ext (by omega) (by omega))
  let : Fact p.Prime := ⟨hp⟩
  have div := prime_dvd_resultant h1 h2 (collision_root hp ai ij (by omega) he)
    (collision_root hp au uv (by omega) ge)
  exact (Nat.le_of_dvd (Int.natAbs_pos.mpr (gapResultant_ne h1 h2 dif)) div).trans
    (gapResultant_bound h1 h2 (by omega) (by omega) (by omega) (by omega))

theorem unique_repetition {p a H i j u v : ℕ} (hp : p.Prime) (hu : a+H<p)
    (cut : (H+2)^(H^2)<p) (h : Repetition p a H i j) (g : Repetition p a H u v) :
    (i,j)=(u,v) := by
  by_contra ne
  have lim := prime_le_of_two_repetitions hp hu h g ne
  have len {x y : ℕ} (q : Repetition p a H x y) : y-x≤H := by
    obtain ⟨lo,_,hi,_⟩ := q
    omega
  have e : (j-i)*(v-u)≤H^2 := by simpa [pow_two] using Nat.mul_le_mul (len h) (len g)
  exact cut.not_ge (lim.trans (Nat.pow_le_pow_right (by omega) e))

#print axioms Repetition
#print axioms collision_root
#print axioms prime_le_of_two_repetitions
#print axioms unique_repetition
end Erdos478.LocalSpacing
