import research.arxiv.«1104.1579».CunninghamSquarefreeEulerDensity
import research.arxiv.«1104.1579».CunninghamSingularSeriesGrowth

/-! # Tail of the first square obstruction at Cunningham prime seeds -/

namespace CunninghamChain.SquarefreeDensity
open Finset Filter Real Topology

private theorem eventually_prime_log_lower :
    ∀ᶠ x : ℕ in atTop, (x:ℝ)*log 2/2 ≤ ∑ q ∈ x.primesLE,log (q:ℝ) := by
  have h2 : 0 < log 2 := log_pos (by norm_num)
  have hsucc : Tendsto (fun x : ℕ => (x:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have h₁ := hsucc.eventually (isLittleO_log_id_atTop.bound (show 0<log 2/8 by positivity))
  have h₂ := tendsto_natCast_atTop_atTop.eventually
    ((isLittleO_log_rpow_atTop (by norm_num : 0<(1/2:ℝ))).bound (show 0<log 2/8 by positivity))
  filter_upwards [h₁,h₂,eventually_ge_atTop 2] with x ha hb hx
  have hx' : (2:ℝ) ≤ x := by exact_mod_cast hx
  simp only [id_eq,Real.norm_eq_abs,abs_of_nonneg (log_nonneg (by linarith : (1:ℝ)≤x+1)),
    abs_of_nonneg (by positivity : (0:ℝ)≤x+1)] at ha
  simp only [←sqrt_eq_rpow,Real.norm_eq_abs,abs_of_nonneg (log_natCast_nonneg x),
    abs_of_nonneg (sqrt_nonneg _)] at hb
  have hθ := Chebyshev.theta_ge x
  rw [Chebyshev.theta_eq_sum_primesLE_log] at hθ
  have hr := mul_le_mul_of_nonneg_left hb (sqrt_nonneg (x:ℝ))
  nlinarith only [hθ,ha,hr,congrArg (fun y : ℝ => log 2*y) (sq_sqrt (Nat.cast_nonneg x)),
    mul_nonneg (by linarith : (0:ℝ)≤x-1) h2.le]

private theorem large_orders (n X : ℕ) (hn : 1≤n) (hX : X=16*n^2)
    (hθ : (X:ℝ)*log 2/2 ≤ ∑ q ∈ X.primesLE,log (q:ℝ)) :
    ∃ Q ⊆ X.primesLE, (∀ q∈Q, 2<q ∧ n < orderOf (2 : ZMod q)) ∧
      (n:ℝ)^2 * log 2 ≤ (Q.card:ℝ)*log X := by
  classical
  let B := X.primesLE.filter (fun q => 2<q ∧ orderOf (2 : ZMod q) ≤ n)
  let Q := X.primesLE \ insert 2 B
  have upper := small_order_prime_log_sum (n+1) B fun q hq => by
    obtain ⟨hp,hl,hd⟩ := mem_filter.mp hq
    exact ⟨Nat.prime_of_mem_primesLE hp,hl,by omega⟩
  have hb : 2∉B := fun h => (lt_irrefl 2) (mem_filter.mp h).2.1
  have hsub : insert 2 B ⊆ X.primesLE := by
    apply insert_subset
    · exact Nat.mem_primesLE.mpr ⟨by nlinarith,Nat.prime_two⟩
    · exact filter_subset ..
  have hsum := sum_sdiff (f:=fun q : ℕ => log (q:ℝ)) hsub
  rw [sum_insert hb] at hsum
  have hi {q : ℕ} (h : q∈Q) : 2<q ∧ n<orderOf (2 : ZMod q) := by
    obtain ⟨hp,hb'⟩ := Finset.mem_sdiff.mp h
    have hq := (Nat.prime_of_mem_primesLE hp).two_le
    have hne : q≠2 := fun he => hb' (mem_insert.mpr (Or.inl he))
    refine ⟨by omega,lt_of_not_ge fun hd => hb' (mem_insert_of_mem (mem_filter.mpr ⟨hp,by omega,hd⟩))⟩
  refine ⟨Q,sdiff_subset,fun _ => hi,?_⟩
  have hlog : ∑ q ∈ Q,log (q:ℝ) ≤ Q.card*log X := calc
    _ ≤ ∑ _ ∈ Q,log (X:ℝ) := sum_le_sum (fun q hq => by
      obtain ⟨hle,hp⟩ := Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hq).1
      exact log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast hle))
    _ = _ := by simp
  change ∑ q ∈ Q,log (q:ℝ) + _ = _ at hsum
  have hx : (X:ℝ)=16*(n:ℝ)^2 := by exact_mod_cast hX
  have hn' : (1:ℝ)≤n := by exact_mod_cast hn
  have hs : ((n:ℝ)+1)^2+1 ≤ 7*(n:ℝ)^2 := by nlinarith [sq_nonneg ((n:ℝ)-1)]
  push_cast at upper hsum
  rw [hx] at hθ
  nlinarith only [hθ,hsum,hlog,upper,mul_le_mul_of_nonneg_right hs (show 0≤log 2 by positivity),
    congrArg (fun x : ℝ => x*log 2) hx]

/-- Uniform tail bound. At every sufficiently large n, the probability of
surviving 32 n² sites is at most exp(−n log 2 / (16 log(16 n²))). -/
theorem prefixDensity_tail :
    ∀ᶠ n : ℕ in atTop, prefixDensity (32*n^2) ≤
      exp (-(n:ℝ)*log 2/(16*log (16*(n:ℝ)^2))) := by
  have hx : Tendsto (fun n : ℕ => 16*n^2) atTop atTop := by
    apply tendsto_atTop_mono (f:=id) _ tendsto_id
    intro n
    change n ≤ 16*n^2
    have hl : n ≤ n^2 := Nat.le_pow (by decide)
    omega
  filter_upwards [hx.eventually eventually_prime_log_lower,eventually_ge_atTop 2] with n hθ hn
  let X := 16*n^2
  have hn' : (2:ℝ)≤n := by exact_mod_cast hn
  have hX : (X:ℝ) = 16*(n:ℝ)^2 := by dsimp [X]; push_cast; rfl
  have hXpos : 0<(X:ℝ) := by rw [hX]; positivity
  have hlog : 0<log (X:ℝ) := log_pos (by rw [hX]; nlinarith)
  obtain ⟨Q,hQ,ho,hcount⟩ := large_orders n X (by omega) rfl hθ
  have hfactor (q : ℕ) (hq : q∈Q) :
      localFactor true q (32*n^2) ≤ exp (-(n:ℝ)/X) := by
    obtain ⟨hle,hp⟩ := Nat.mem_primesLE.mp (hQ hq)
    let : Fact q.Prime := ⟨hp⟩
    obtain ⟨hq₂,hd⟩ := ho q hq
    rw [localFactor_saturated true hq₂ (by dsimp [X] at hle; omega)]
    have hq' : 0<((q-1 : ℕ):ℝ) := by exact_mod_cast (by omega : 0<q-1)
    have hr : (n:ℝ)/X ≤ (orderOf (2 : ZMod q)-1 : ℕ)/((q-1 : ℕ):ℝ) :=
      div_le_div₀ (by positivity) (by exact_mod_cast (by omega : n≤orderOf (2:ZMod q)-1))
        hq' (by exact_mod_cast (Nat.sub_le q 1).trans hle)
    apply (sub_le_sub_left hr 1).trans
    simpa only [neg_div,sub_eq_add_neg,add_comm] using Real.add_one_le_exp (-(n:ℝ)/X)
  have hprod := (prefixDensity_le_product (32*n^2) Q (fun q hq => Nat.prime_of_mem_primesLE (hQ hq))).trans
    (prod_le_prod (fun q hq => (localFactor_pos true (Nat.prime_of_mem_primesLE (hQ hq)) _).le) hfactor)
  rw [prod_const,←Real.exp_nat_mul] at hprod
  apply hprod.trans (Real.exp_le_exp.mpr ?_)
  rw [←hX]
  field_simp [hlog.ne',hXpos.ne']
  nlinarith only [mul_le_mul_of_nonneg_left hcount (by norm_num : (0:ℝ)≤16),
    congrArg (fun x : ℝ => log 2*x) hX]

private theorem quartic_tail :
    ∀ᶠ n : ℕ in atTop, prefixDensity (32*n^4) ≤ exp (-(n:ℝ)) := by
  have h2 : 0<log 2 := log_pos (by norm_num)
  have hlog := tendsto_natCast_atTop_atTop.eventually
    (isLittleO_log_id_atTop.bound (show 0<log 2/128 by positivity))
  have ht : Tendsto (fun n : ℕ => n^2) atTop atTop :=
    tendsto_atTop_mono (f:=id) (fun n => (Nat.le_pow (by decide) : n≤n^2)) tendsto_id
  filter_upwards [ht.eventually prefixDensity_tail,hlog,eventually_ge_atTop 128] with n h hn hlarge
  have hn' : (128:ℝ)≤n := by exact_mod_cast hlarge
  simp only [id_eq,Real.norm_eq_abs,abs_of_nonneg (log_natCast_nonneg _),
    abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) n)] at hn
  rw [show n^4=(n^2)^2 by ring]
  apply h.trans (Real.exp_le_exp.mpr ?_)
  push_cast
  have hlog' : 0<log (16*((n:ℝ)^2)^2) := log_pos (by nlinarith [show (1:ℝ)≤(n:ℝ)^2 by nlinarith])
  rw [div_le_iff₀ (by positivity)]
  have he : log (16*((n:ℝ)^2)^2) = 4*log 2 + 4*log n := by
    rw [log_mul (by norm_num) (by positivity),log_pow,log_pow,show (16:ℝ)=2^4 by norm_num,log_pow]
    norm_num
    ring
  have hh : 16*log (16*((n:ℝ)^2)^2) ≤ n*log 2 := by
    rw [he]; nlinarith only [hn,mul_nonneg (by linarith : (0:ℝ)≤n-128) h2.le]
  nlinarith only [mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg n)]

/-- All polynomial moments of the survival tail are finite. -/
theorem summable_prefixDensity_moments (m : ℕ) : Summable (fun k : ℕ => (k:ℝ)^m*prefixDensity k) := by
  let g (n : ℕ) := 32*n^4
  have hg (n : ℕ) : n≤g n := by
    have h : n≤n^4 := Nat.le_pow (by decide)
    dsimp [g]; omega
  let M := m+2
  have hsum := (summable_pow_mul_exp_neg_nat_mul (4*M) (by norm_num : (0:ℝ)<1)).mul_left ((512:ℝ)^M)
  have hpoly : ∀ᶠ n : ℕ in atTop, (512*(n:ℝ)^4)^M * exp (-(n:ℝ)) ≤ 1 := by
    filter_upwards [hsum.tendsto_atTop_zero.eventually_lt_const zero_lt_one] with n hn
    simpa [mul_pow,←pow_mul,mul_assoc] using hn.le
  obtain ⟨N,hN⟩ := eventually_atTop.mp (quartic_tail.and (hpoly.and (eventually_ge_atTop 1)))
  apply Summable.of_norm_bounded_eventually_nat (Real.summable_one_div_nat_pow.mpr (by decide : 1<2))
  filter_upwards [eventually_ge_atTop (g N),eventually_ge_atTop 1] with k hk hk'
  let j := Nat.findGreatest (fun i => g i≤k) k
  have hj : g j≤k := Nat.findGreatest_spec (P:=fun i => g i≤k) ((hg N).trans hk) hk
  have hNj : N≤j := Nat.le_findGreatest (P:=fun i => g i≤k) ((hg N).trans hk) hk
  have hlt : k<g (j+1) := lt_of_not_ge fun hh => Nat.findGreatest_is_greatest
    (P:=fun i => g i≤k) (Nat.lt_succ_self j) ((hg (j+1)).trans hh) hh
  obtain ⟨ht,hp,hj1⟩ := hN j hNj
  have hle : (k:ℝ) ≤ 512*(j:ℝ)^4 := by
    have h : k ≤ 32*(2*j)^4 := hlt.le.trans (Nat.mul_le_mul_left 32 (Nat.pow_le_pow_left (by omega) 4))
    exact_mod_cast (by simpa [mul_pow,mul_assoc,←mul_assoc] using h : k ≤ 512*j^4)
  have hden : prefixDensity k ≤ exp (-(j:ℝ)) := (antitone_nat_of_succ_le density_succ_le hj).trans ht
  have hh : (k:ℝ)^M*prefixDensity k ≤ 1 :=
    (mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg k) hle M) hden (prefixDensity_pos k).le (by positivity)).trans hp
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (by positivity) (prefixDensity_pos k).le)]
  apply (le_div_iff₀ (by positivity : 0<(k:ℝ)^2)).mpr
  simpa [M,pow_add,mul_assoc,mul_comm,mul_left_comm] using hh

theorem prefixDensity_tendsto_zero : Tendsto prefixDensity atTop (𝓝 0) := by
  simpa using (summable_prefixDensity_moments 0).tendsto_atTop_zero

/-- The positive first-obstruction masses, starting with site one, sum to one. -/
theorem first_square_total :
    HasSum (fun j : ℕ => prefixDensity (j+1) - prefixDensity (j+2)) 1 := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun j => sub_nonneg.mpr (density_succ_le _)) 1]
  have h := tendsto_const_nhds (x:=prefixDensity 1) |>.sub
    (prefixDensity_tendsto_zero.comp (tendsto_add_atTop_nat 1))
  simp only [sub_zero,prefixDensity_one] at h
  apply h.congr
  intro n
  change 1 - prefixDensity (n+1) = _
  rw [←prefixDensity_one]
  exact (Finset.sum_range_sub' (fun i => prefixDensity (i+1)) n).symm

#print axioms first_square_total
#print axioms summable_prefixDensity_moments
#print axioms prefixDensity_tail

end CunninghamChain.SquarefreeDensity
