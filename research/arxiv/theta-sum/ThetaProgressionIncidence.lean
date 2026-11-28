import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

/-! A second-moment estimate for one independently chosen residue per modulus. -/
namespace Arxiv.«2501.03234».ThetaProgressionIncidence
open Finset Real
noncomputable section

def pair (u H q d b c : ℕ) :=
  (range (H+1)).filter (fun j => (u+j)%q=b ∧ (u+j)%d=c)

theorem pair_count (u H q d b c : ℕ) (hq : 0<q) (hd : 0<d) :
    ((pair u H q d b c).card:ℝ) ≤ (H:ℝ)/(q.lcm d)+1 := by
  let m := q.lcm d
  have hm : 0<m := Nat.lcm_pos hq hd
  have hcard : (pair u H q d b c).card ≤ (range (H/m+1)).card := by
    apply card_le_card_of_injOn (fun j => j/m)
    · intro j hj
      have h := mem_range.mp (mem_filter.mp hj).1
      exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (by omega : j≤H)))
    · intro x hx y hy hdiv
      obtain ⟨_,hxq,hxd⟩ := mem_filter.mp hx
      obtain ⟨_,hyq,hyd⟩ := mem_filter.mp hy
      have h : x ≡ y [MOD m] := Nat.ModEq.add_left_cancel' u (Nat.mod_lcm (hxq.trans hyq.symm) (hxd.trans hyd.symm))
      change x%m=y%m at h
      have Hx := Nat.mod_add_div x m
      have Hy := Nat.mod_add_div y m
      change x/m=y/m at hdiv
      rw [h,hdiv] at Hx
      exact Hx.symm.trans Hy
  simp only [card_range] at hcard
  have hdiv : ((H/m:ℕ):ℝ) ≤ (H:ℝ)/m := by
    rw [le_div_iff₀ (Nat.cast_pos.mpr hm)]
    exact_mod_cast Nat.div_mul_le_self H m
  calc _ ≤ ((H/m+1:ℕ):ℝ) := Nat.cast_le.mpr hcard
       _ ≤ _ := by push_cast;exact add_le_add hdiv le_rfl

def harmonicSum (Q : ℕ) := ∑ d∈Icc 1 Q,(d:ℝ)⁻¹

theorem harmonic_bound (Q : ℕ) : harmonicSum Q ≤ 1+log Q := by
  have h := harmonic_le_one_add_log Q
  simpa only [harmonicSum,harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast] using h

private def triple (x : ℕ × ℕ) := (x.1.gcd x.2,x.1/(x.1.gcd x.2),x.2/(x.1.gcd x.2))

private theorem recover (x : ℕ × ℕ) :
    ((triple x).1*(triple x).2.1,(triple x).1*(triple x).2.2)=x := by
  ext <;> simp [triple,Nat.mul_div_cancel' (Nat.gcd_dvd_left x.1 x.2),Nat.mul_div_cancel' (Nat.gcd_dvd_right x.1 x.2)]

theorem lcm_sum (Q : ℕ) :
    ∑ q∈Icc 1 Q,∑ d∈Icc 1 Q,((q.lcm d:ℕ):ℝ)⁻¹ ≤ (harmonicSum Q)^3 := by
  let I := Icc 1 Q
  let F (v : ℕ × ℕ × ℕ) := (v.1:ℝ)⁻¹*(v.2.1:ℝ)⁻¹*(v.2.2:ℝ)⁻¹
  have hsub : (I ×ˢ I).image triple ⊆ I ×ˢ (I ×ˢ I) := by
    intro v hv
    obtain ⟨⟨q,d⟩,h, rfl⟩ := mem_image.mp hv
    obtain ⟨hq,hd⟩ := mem_product.mp h
    obtain ⟨hq₁,hq₂⟩ := mem_Icc.mp hq
    obtain ⟨hd₁,hd₂⟩ := mem_Icc.mp hd
    have hg : 0<q.gcd d := Nat.gcd_pos_of_pos_left d hq₁
    have hpq := Nat.le_of_dvd hq₁ (Nat.gcd_dvd_left q d)
    have hpd := Nat.le_of_dvd hd₁ (Nat.gcd_dvd_right q d)
    exact mem_product.mpr ⟨mem_Icc.mpr ⟨hg,hpq.trans hq₂⟩,mem_product.mpr
      ⟨mem_Icc.mpr ⟨Nat.div_pos hpq hg,(Nat.div_le_self ..).trans hq₂⟩,
       mem_Icc.mpr ⟨Nat.div_pos hpd hg,(Nat.div_le_self ..).trans hd₂⟩⟩⟩
  have he (q d : ℕ) (hq : 0<q) :
      ((q.lcm d:ℕ):ℝ)⁻¹=F (triple (q,d)) := by
    let g := q.gcd d
    have hgp : 0<g := Nat.gcd_pos_of_pos_left d hq
    have h₁ : g*(q/g)=q := Nat.mul_div_cancel' (Nat.gcd_dvd_left ..)
    have h₂ : g*(d/g)=d := Nat.mul_div_cancel' (Nat.gcd_dvd_right ..)
    have hh : q.lcm d=g*(q/g)*(d/g) := by
      apply Nat.eq_of_mul_eq_mul_left hgp
      calc g*q.lcm d=q*d := Nat.gcd_mul_lcm ..
           _ = (g*(q/g))*(g*(d/g)) := congrArg₂ (·*·) h₁.symm h₂.symm
           _ = _ := by ring
    rw [hh];push_cast;dsimp [F,triple,g];simp only [mul_inv_rev];ring
  calc _ = ∑ x∈I ×ˢ I,F (triple x) := by
           rw [sum_product];apply sum_congr rfl;intro q hq
           exact sum_congr rfl (fun d _ => he q d (mem_Icc.mp hq).1)
       _ = ∑ v∈(I ×ˢ I).image triple,F v := by
           rw [sum_image];intro x _ y _ hxy
           simpa only [recover] using congrArg (fun v : ℕ × ℕ × ℕ => (v.1*v.2.1,v.1*v.2.2)) hxy
       _ ≤ ∑ v∈I ×ˢ (I ×ˢ I),F v := sum_le_sum_of_subset_of_nonneg hsub (fun v _ _ => by dsimp [F];positivity)
       _ = _ := by
           simp only [sum_product,F,harmonicSum,I,pow_succ,pow_zero,one_mul,mul_sum,sum_mul]
           apply sum_congr rfl;intro i _;apply sum_congr rfl;intro j _
           apply sum_congr rfl;intros;ring

#print axioms pair_count
#print axioms lcm_sum
end
end Arxiv.«2501.03234».ThetaProgressionIncidence
