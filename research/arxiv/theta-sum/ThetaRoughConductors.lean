import ThetaPrimitiveCount
import ThetaTotientTail
import Mathlib.NumberTheory.Harmonic.Bounds

/-! Counting conductors with small imprimitive character density in long intervals. -/
namespace Arxiv.«2501.03234».ThetaRoughConductors
open Finset Filter Topology ThetaPrimitiveCount
noncomputable section

private theorem fiber (N M p : ℕ) (hp : p.Prime) :
    (((Ico N (2*N)).filter (fun k => p∣M*k+1)).card:ℝ) ≤ 2*N/p+1 := by
  let s := (Ico N (2*N)).filter (fun k => p∣M*k+1)
  have hbound (k) (hk : k∈s) := mem_Ico.mp (mem_filter.mp hk).1
  have hinj : Set.InjOn (·/p) (s:Set ℕ) := by
    intro i hi j hj hjj
    have hi0 := (mem_filter.mp hi).2
    have hj0 := (mem_filter.mp hj).2
    have hcop : p.Coprime M := hp.coprime_iff_not_dvd.mpr (fun h =>
      hp.not_dvd_one ((Nat.dvd_add_right (dvd_mul_of_dvd_left h i)).mp hi0))
    have hmod := (Nat.modEq_zero_iff_dvd.mpr hi0).trans (Nat.modEq_zero_iff_dvd.mpr hj0).symm
    have hmul := Nat.ModEq.add_right_cancel' 1 hmod
    have himod : i%p=j%p := Nat.ModEq.cancel_left_of_coprime hcop hmul
    change i/p=j/p at hjj
    exact (Nat.modEq_iff_eq_of_div_eq hjj).mp himod
  have hm : Set.MapsTo (·/p) (s:Set ℕ) (range (2*N/p+1):Set ℕ) := by
    intro k hk
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (hbound k hk).2.le))
  have hc := card_le_card_of_injOn _ hm hinj
  rw [card_range] at hc
  have hh : (s.card:ℝ)≤((2*N/p:ℕ):ℝ)+1 := by exact_mod_cast hc
  apply hh.trans
  gcongr
  apply (le_div_iff₀ (by exact_mod_cast hp.pos)).mpr
  exact_mod_cast Nat.div_mul_le_self (2*N) p

private theorem one_weight (p : ℕ) (hp : p.Prime) : 1/((p:ℝ)-1)≤2*(p:ℝ)⁻¹ := by
  have hh : (2:ℝ)≤p := by exact_mod_cast hp.two_le
  rw [←div_eq_mul_inv,div_le_div_iff₀ (by linarith) (by linarith)]
  linarith

theorem defect_sum (T N : ℕ) (hT : 2≤T) :
    ∑ k∈Ico N (2*N),defect (T.factorial*k+1)
      ≤ 2*N/T + 2*(1+Real.log (2*T.factorial*N+1)) := by
  classical
  let M := T.factorial
  let s := Ico N (2*N)
  let R := 2*M*N+1
  let P := s.biUnion (fun k => (M*k+1).primeFactors)
  have hmem (p) (hp : p∈P) : p.Prime ∧ T<p ∧ p≤R := by
    obtain ⟨k,hk,hpk⟩ := mem_biUnion.mp hp
    obtain ⟨hprime,hdiv,_⟩ := Nat.mem_primeFactors.mp hpk
    have hgt : T<p := by
      by_contra! h
      have hM : p∣M := Nat.dvd_factorial hprime.pos h
      exact hprime.not_dvd_one ((Nat.dvd_add_right (dvd_mul_of_dvd_left hM k)).mp hdiv)
    have hbound : M*k+1≤R := by
      have h := Nat.mul_le_mul_left M (mem_Ico.mp hk).2.le
      dsimp only [R]; nlinarith only [h]
    exact ⟨hprime,hgt,(Nat.le_of_dvd (by omega) hdiv).trans hbound⟩
  let w (p : ℕ) := 1/((p:ℝ)-1)
  have hsumW : ∑ p∈P,w p ≤ 2*(1+Real.log R) := by
    have hh : ∑ i∈range (R+1),(i:ℝ)⁻¹=(harmonic R:ℝ) := by
      rw [sum_range_succ',harmonic]; push_cast; simp
    have hsub : P⊆range (R+1) := fun p hp => mem_range.mpr (Nat.lt_succ_of_le (hmem p hp).2.2)
    calc _ ≤ ∑ p∈P,2*(p:ℝ)⁻¹ := sum_le_sum (fun p hp => one_weight p (hmem p hp).1)
         _ = _ := (mul_sum ..).symm
         _ ≤ 2*∑ i∈range (R+1),(i:ℝ)⁻¹ := by
               exact mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)) (by norm_num)
         _ ≤ _ := by rw [hh]; gcongr; exact harmonic_le_one_add_log R
  have htail : ∑ p∈P,w p/p ≤ 1/(T:ℝ) := by
    have h := ThetaTotientTail.reciprocal_pair_tail P (T+1) (by omega) (fun p hp => (hmem p hp).2.1)
    simpa only [w,one_div,Nat.cast_add,Nat.cast_one,add_sub_cancel_right] using h
  have hrow (k) (hk : k∈s) : defect (M*k+1)=∑ p∈P,if p∣M*k+1 then w p else 0 := by
    have he : P.filter (fun p => p∣M*k+1)=(M*k+1).primeFactors := by
      ext p
      constructor
      · intro h; obtain ⟨hp,hd⟩ := mem_filter.mp h
        exact Nat.mem_primeFactors.mpr ⟨(hmem p hp).1,hd,by omega⟩
      · intro h; exact mem_filter.mpr ⟨mem_biUnion.mpr ⟨k,hk,h⟩,Nat.dvd_of_mem_primeFactors h⟩
    rw [←sum_filter,he]; rfl
  calc _ = ∑ k∈s,∑ p∈P,if p∣M*k+1 then w p else 0 := sum_congr rfl hrow
       _ = ∑ p∈P,((s.filter (fun k => p∣M*k+1)).card:ℝ)*w p := by
             rw [sum_comm]; simp only [←sum_filter,sum_const,nsmul_eq_mul]
       _ ≤ ∑ p∈P,(2*N/p+1)*w p := by
             apply sum_le_sum
             intro p hp
             have hh : (2:ℝ)≤p := by exact_mod_cast (hmem p hp).1.two_le
             exact mul_le_mul_of_nonneg_right (fiber N M p (hmem p hp).1) (div_nonneg zero_le_one (by linarith))
       _ = (2*N)*∑ p∈P,w p/p + ∑ p∈P,w p := by
             rw [mul_sum,←sum_add_distrib]; apply sum_congr rfl; intros; ring
       _ ≤ (2*N)*(1/(T:ℝ)) + 2*(1+Real.log R) := by gcongr
       _ = _ := by dsimp [M,R]; push_cast; ring

/-- Indices furnishing a conductor with small density of imprimitive characters. -/
def candidates (T N : ℕ) : Finset ℕ := by
  classical exact (Ico N (2*N)).filter (fun k => defect (T.factorial*k+1)≤1/1024)

theorem many (T : ℕ) (hT : 16384≤T) :
    ∀ᶠ N : ℕ in atTop,(N:ℝ)/2 ≤ (candidates T N).card := by
  classical
  let M := T.factorial
  let D : ℝ := 2*M+1
  have hD : 0<D := by dsimp only [D]; positivity
  have hlog := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually (Real.isLittleO_log_id_atTop.bound (by norm_num : (0:ℝ)<1/16384))
  have hc := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop (16384*(1+Real.log D))
  filter_upwards [eventually_ge_atTop 1, hc, hlog] with N hN hC hL
  have hn : (1:ℝ)≤N := by exact_mod_cast hN
  have hN' : 0<(N:ℝ) := by linarith
  change 16384*(1+Real.log D)≤(N:ℝ) at hC
  change ‖Real.log N‖ ≤ 1/16384*‖(N:ℝ)‖ at hL
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg hn),abs_of_pos hN'] at hL
  have hdom : 2*(M:ℝ)*N+1 ≤ D*N := by dsimp only [D]; nlinarith only [hn]
  have hlg := Real.log_le_log (by positivity) hdom
  rw [Real.log_mul hD.ne' hN'.ne'] at hlg
  have hcut : (2:ℝ)*N/T≤2*N/16384 := by
    apply div_le_div_of_nonneg_left (by positivity) (by norm_num)
    exact_mod_cast hT
  have H := defect_sum T N (by omega)
  change ∑ k∈Ico N (2*N),defect (M*k+1) ≤ 2*(N:ℝ)/T + 2*(1+Real.log (2*(M:ℝ)*N+1)) at H
  have hsum : ∑ k∈Ico N (2*N),defect (M*k+1) ≤ (N:ℝ)/2048 := by linarith
  let bad := Ico N (2*N) \ candidates T N
  have hsub : candidates T N⊆Ico N (2*N) := filter_subset ..
  have hh (k) (hk : k∈bad) : 1/1024≤defect (M*k+1) := by
    have hn := (mem_sdiff.mp hk).2
    exact le_of_not_ge (fun h => hn (mem_filter.mpr ⟨(mem_sdiff.mp hk).1,h⟩))
  have hsmall : (bad.card:ℝ)*(1/1024)≤(N:ℝ)/2048 := by
    calc _ = ∑ _k∈bad,1/1024 := by rw [sum_const,nsmul_eq_mul]
         _ ≤ ∑ k∈bad,defect (M*k+1) := sum_le_sum hh
         _ ≤ _ := by
               apply (sum_le_sum_of_subset_of_nonneg sdiff_subset _).trans hsum
               intro k _ _
               apply sum_nonneg
               intro p hp
               have h2 : (2:ℝ)≤p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
               exact div_nonneg zero_le_one (by linarith)
  have he := card_sdiff_add_card_eq_card hsub
  change bad.card+(candidates T N).card=(Ico N (2*N)).card at he
  rw [Nat.card_Ico,show 2*N-N=N by omega] at he
  have hr : (bad.card:ℝ)+(candidates T N).card=N := by exact_mod_cast he
  linarith

#print axioms many
#print axioms defect_sum
end
end Arxiv.«2501.03234».ThetaRoughConductors
