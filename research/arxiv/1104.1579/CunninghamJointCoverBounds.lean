import CunninghamJointOrbitCover

/-! Counts of surviving exponents and the Euler cost of the seed congruence. -/

namespace CunninghamChain.PrimePeriodSupply.PeriodSupply
open Finset Real
variable {T : ℝ} (S : PeriodSupply T)

theorem period_fraction (b : Bool) :
    ((S.periodProduct b).totient:ℝ)/(S.periodProduct b) ≤ exp (-T) := by
  let L := S.periodProduct b
  have lp : 0<(L:ℝ) := by exact_mod_cast S.periodProduct_pos b
  have factors : L.primeFactors=S.selected b := Nat.primeFactors_prod fun l hl => (S.spec l (S.selected_mem hl)).1
  have eq : (L.totient:ℝ)=L*∏ l∈L.primeFactors, (1-(l:ℝ)⁻¹) := by
    have h := congrArg (fun x : ℚ => (x:ℝ)) (Nat.totient_eq_mul_prod_factors L)
    push_cast at h
    simpa only [one_div] using h
  change (L.totient:ℝ)/L≤_
  rw [eq,mul_div_cancel_left₀ _ lp.ne',factors]
  have lo : T≤∑ l∈S.selected b, (l:ℝ)⁻¹ := by cases b <;> first | exact S.plus_mass | exact S.minus_mass
  calc _ ≤ ∏ l∈S.selected b, exp (-(l:ℝ)⁻¹) := by
            apply prod_le_prod
            · intro l hl
              exact sub_nonneg.mpr (inv_le_one_of_one_le₀ (by exact_mod_cast (S.spec l (S.selected_mem hl)).1.one_le))
            · intro l _
              linarith [Real.add_one_le_exp (-(l:ℝ)⁻¹)]
       _ ≤ _ := by rw [←Real.exp_sum,sum_neg_distrib]; exact exp_le_exp.mpr (neg_le_neg lo)

theorem surviving_offset_count (b : Bool) (H : ℕ) :
    (((range H).filter fun i => i.Coprime (S.periodProduct b)).card:ℝ) ≤
      exp (-T)*H+S.periodProduct b := by
  let L := S.periodProduct b
  have lp := S.periodProduct_pos b
  have count : ((range H).filter fun i => i.Coprime L).card≤ L.totient*(H/L+1) := by
    have flip (i : ℕ) : L.Coprime i ↔ i.Coprime L := Nat.coprime_comm
    simpa only [zero_add,Nat.Ico_zero_eq_range,flip] using Nat.Ico_filter_coprime_le (a:=L) 0 H lp.ne'
  have ratio := S.period_fraction b
  change (L.totient:ℝ)/L≤exp (-T) at ratio
  have small : ((H/L:ℕ):ℝ)≤(H:ℝ)/L := Nat.cast_div_le
  have ht : (L.totient:ℝ)≤L := by exact_mod_cast Nat.totient_le L
  calc _ ≤ (L.totient:ℝ)*(((H/L:ℕ):ℝ)+1) := by exact_mod_cast count
       _ ≤ (L.totient:ℝ)*((H:ℝ)/L+1) := by gcongr
       _ = ((L.totient:ℝ)/L)*H+L.totient := by ring
       _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right ratio (Nat.cast_nonneg _)) ht

private lemma prime_factor_loss {q : ℕ} (hq : q.Prime) :
    ((1-1/(q:ℝ))⁻¹)^2 ≤ exp (4*(q:ℝ)⁻¹) := by
  have qp : (2:ℝ)≤q := by exact_mod_cast hq.two_le
  have qpos : (0:ℝ)<q := by linarith
  have pos : 0<1-1/(q:ℝ) := sub_pos.mpr ((div_lt_one qpos).mpr (by linarith))
  have first : (1-1/(q:ℝ))⁻¹ ≤ exp (2*(q:ℝ)⁻¹) := by
    apply le_trans _ (Real.add_one_le_exp _)
    apply (inv_le_iff_one_le_mul₀ pos).mpr
    field_simp
    nlinarith
  have bound := pow_le_pow_left₀ (inv_nonneg.mpr pos.le) first 2
  rw [←Real.exp_nat_mul] at bound
  apply bound.trans_eq
  congr 1
  norm_num
  ring

theorem seed_euler_cost :
    ∏ q∈S.seedModulus.primeFactors, ((1-1/(q:ℝ))⁻¹)^2 ≤ exp 4 := by
  let U := S.plus∪S.minus
  have sub : S.seedModulus.primeFactors ⊆ U.image S.q := by
    intro p hp
    have pr := Nat.prime_of_mem_primeFactors hp
    have dv := Nat.dvd_of_mem_primeFactors hp
    obtain ⟨l,hl,dq⟩ := (pr.prime.dvd_finsetProd_iff S.q).mp dv
    exact mem_image.mpr ⟨l,hl,((Nat.prime_dvd_prime_iff_eq pr (S.spec l hl).2.1).mp dq).symm⟩
  have inj : Set.InjOn S.q U := by
    intro a ha b hb eq
    rw [←(S.spec a ha).2.2.2,←(S.spec b hb).2.2.2,eq]
  have cost : ∑ p∈S.seedModulus.primeFactors, (p:ℝ)⁻¹ ≤ 1 := by
    apply le_trans (sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => by positivity))
    rw [sum_image inj]
    exact S.cost
  calc _ ≤ ∏ p∈S.seedModulus.primeFactors, exp (4*(p:ℝ)⁻¹) := by
            apply prod_le_prod (fun _ _ => sq_nonneg _) (fun _ hp => prime_factor_loss (Nat.prime_of_mem_primeFactors hp))
       _ ≤ _ := by rw [←Real.exp_sum,←mul_sum]; exact exp_le_exp.mpr (by linarith)

#print axioms period_fraction
#print axioms surviving_offset_count
#print axioms seed_euler_cost

end CunninghamChain.PrimePeriodSupply.PeriodSupply
