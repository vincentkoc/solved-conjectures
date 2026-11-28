import CunninghamSparseCollisionAverage
import CunninghamProgressionPairSieve

/-! Uniform counts for prime pairs in sparse offset sets and a seed progression. -/

namespace CunninghamChain.OrbitIsolation
open Finset Filter Real

theorem sparse_affine_pair_scale {ε : ℝ} (he : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ X : ℕ in atTop, ∀ (b : Bool) (A W H : ℕ) (I : Finset ℕ),
      0<W → (∏ q∈W.primeFactors, ((1-1/(q:ℝ))⁻¹)^2)≤exp 4 → I⊆range H →
      (∑ i∈I, ((affinePairs b A W i X).card:ℝ))*(log (X:ℝ))^2 ≤
        X*(C*I.card+ε*H) := by
  let J := 54*exp 4
  have jp : 0<J := by dsimp [J]; positivity
  let η := ε/(32^2*J)
  have ηp : 0<η := div_pos he (by positivity)
  obtain ⟨K,kp,sparse⟩ := sparse_collision_loss ηp
  refine ⟨32^2*(2+J*K),by positivity,?_⟩
  filter_upwards [pair_sieve_cutoff,eventually_ge_atTop 2] with X cz xp
  intro b A W H I wp cost sub
  obtain ⟨z,hz,cut,lg,small⟩ := cz
  let Q := collisionPrimes z W
  let L := log ((z:ℝ)+1)
  let F (i : ℕ) := ∏ q∈Q.filter (fun q => orderOf (2:ZMod q)∣i+1), ((1-1/(q:ℝ))⁻¹)^2
  have Fpos (i : ℕ) : 0≤F i := prod_nonneg fun _ _ => sq_nonneg _
  have cost' : 54*(∏ q∈W.primeFactors, ((1-1/(q:ℝ))⁻¹)^2)≤J := by
    dsimp [J]
    linarith
  have each (i : ℕ) : ((affinePairs b A W i X).card:ℝ)*L^2 ≤ (2+J*F i)*X := by
    apply (affine_offset_bound b A i wp hz cut).trans
    have mul := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right cost' (Fpos i)) (Nat.cast_nonneg X)
    change ((z+1:ℕ):ℝ)*L^2+54*_*(F i)*X≤_
    push_cast
    change ((z:ℝ)+1)*L^2 ≤ 2*X at small
    linarith only [mul,small]
  let S := ∑ i∈I, ((affinePairs b A W i X).card:ℝ)
  have non : 0≤S := sum_nonneg fun _ _ => Nat.cast_nonneg _
  have basic : S*L^2 ≤ (2*I.card+J*(∑ i∈I,F i))*X := by
    have sum := sum_le_sum (s:=I) (fun i _ => each i)
    rw [←sum_mul,←sum_mul,sum_add_distrib,←mul_sum,sum_const,nsmul_eq_mul] at sum
    simpa only [mul_comm (I.card:ℝ) 2] using sum
  have sparseQ := sparse Q I H (fun _ h => collisionPrimes_prime_gt_two h) sub
  change (∑ i∈I, F i)≤K*I.card+η*H at sparseQ
  have hbase := basic.trans (mul_le_mul_of_nonneg_right (add_le_add_right (mul_le_mul_of_nonneg_left sparseQ jp.le) _) (Nat.cast_nonneg X))
  have norm : S*(log (X:ℝ))^2 ≤ S*(32*L)^2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (log_nonneg (by exact_mod_cast (by omega : 1≤X))) lg _) non
  have eq : 32^2*J*η=ε := by dsimp [η]; field_simp
  calc _ ≤ (32:ℝ)^2*((2*I.card+J*(K*I.card+η*H))*X) := by
            apply norm.trans
            calc S*(32*L)^2 = 32^2*(S*L^2) := by ring
                 _ ≤ _ := mul_le_mul_of_nonneg_left hbase (by positivity)
       _ = _ := by rw [←eq]; dsimp [η]; field_simp; ring

#print axioms sparse_affine_pair_scale

end CunninghamChain.OrbitIsolation
