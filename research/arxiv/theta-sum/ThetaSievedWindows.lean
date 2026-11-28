import ThetaRowCorrelations

/-! Finite prime averages of low-denominator theta windows. -/
namespace Arxiv.«2501.03234».ThetaSievedWindows

open Finset ThetaPeriodMeans ThetaPrimeSieve ThetaRowCorrelations

theorem normalizer_bound {N : ℕ} (hN : 2≤N) :
    (normalizer N)⁻¹ ≤ (∑' i : ℕ, ((i:ℝ)^2)⁻¹)/Real.log N := by
  have hp : (1:ℝ)<N := by exact_mod_cast hN
  have hlog := Real.log_pos hp
  have hZ : 0≤∑' i : ℕ, ((i:ℝ)^2)⁻¹ := tsum_nonneg (fun i => by positivity)
  have h1 : 1∈moduli N := mem_filter.mpr ⟨mem_Icc.mpr ⟨le_rfl,by omega⟩,squarefree_one⟩
  have hG : 0<normalizer N := by
    have h := single_le_sum (f:=fun r : ℕ => (r.totient:ℝ)⁻¹) (fun i _ => by positivity) h1
    simpa [normalizer] using (lt_of_lt_of_le (by norm_num : 0<((1:ℕ).totient:ℝ)⁻¹) h)
  have H := (log_le_harmonic_floor (N:ℝ) (Nat.cast_nonneg N))
  rw [Nat.floor_natCast] at H
  rw [← one_div,div_le_div_iff₀ hG hlog,one_mul]
  exact H.trans (harmonic_le_normalizer N)

private lemma row_bound {d : ℕ} (hd : 1<d) (k n : ℕ) : |row d k n| ≤ 6*d := by
  have h := row_fiber (q:=d) (m:=1) (by omega) (by decide) (by simpa) (Nat.mod_lt n (by omega)) k
  have h' : |row d k (n%d)| ≤ 3*(harmonic d:ℝ) := by simpa using h
  rw [row_onMod] at h'
  have hlog := harmonic_le_one_add_log d
  have hself := Real.log_le_self (Nat.cast_nonneg d)
  have h1 : (1:ℝ)≤d := by exact_mod_cast (show 1≤d by omega)
  linarith

private noncomputable def unitTerm (r n : ℕ) : ℝ := ramanujan r n/r.totient

private lemma unitTerm_bound {r N : ℕ} (hr : r∈moduli N) (n : ℕ) : |unitTerm r n|≤N := by
  have hr₁ := (mem_Icc.mp (mem_filter.mp hr).1).1
  have hrN := (mem_Icc.mp (mem_filter.mp hr).1).2
  have hφ : (1:ℝ)≤r.totient := by exact_mod_cast (Nat.totient_pos.mpr hr₁)
  rw [unitTerm,abs_div,abs_of_nonneg (Nat.cast_nonneg r.totient (α:=ℝ))]
  exact (div_le_self (abs_nonneg _) hφ).trans ((ramanujan_bound (mem_filter.mp hr).2 n).trans (by exact_mod_cast hrN))

/-- On primes above N, each low-window moment is bounded by its complete
sieved moment plus a polynomial endpoint error. -/
private theorem low_endpoint {N X : ℕ} (hN : 2≤N) (K : ℕ → ℕ) (a : ℕ → ℝ) {B : ℝ} (hB : 0≤B)
    (ha : ∀ d∈Icc 2 N, |a d|≤B) (s : Finset ℕ)
    (hs : ∀ p∈s, p.Prime ∧ N<p ∧ p<X) :
    ∑ p∈s,(low N K a p)^2 ≤ X*mean (N.factorial^4)
      (fun n => weight N n*(low N K a n)^2) + (72*B^2)*(N:ℝ)^12 := by
  classical
  let D := Icc 2 N
  let U := moduli N
  let I := U ×ˢ D
  let b (d : ℕ) := a d/d
  let G := normalizer N
  let f (i : ℕ×ℕ) (n : ℕ) := (unitTerm i.1 n/G)*(b i.2*row i.2 (K i.2) n)
  let period (i : ℕ×ℕ) := i.1*i.2
  let P := N.factorial^4
  have hp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have h1 : 1∈moduli N := mem_filter.mpr ⟨mem_Icc.mpr ⟨le_rfl,by omega⟩,squarefree_one⟩
  have hG : 1≤G := by
    simpa [G,normalizer] using (single_le_sum (f:=fun r : ℕ => (r.totient:ℝ)⁻¹) (fun _ _ => by positivity) h1)
  have hpos : 0<P := pow_pos (Nat.factorial_pos _) _
  have hper (i : ℕ×ℕ) (hi : i∈I) : 0<period i ∧ period i≤N^2 ∧ period i∣N.factorial^2 := by
    obtain ⟨hr,hd⟩ := mem_product.mp hi
    obtain ⟨hr₁,hrN⟩ := mem_Icc.mp (mem_filter.mp hr).1
    obtain ⟨hd₂,hdN⟩ := mem_Icc.mp hd
    dsimp [period]; rw [pow_two,pow_two]
    exact ⟨Nat.mul_pos hr₁ (by omega),Nat.mul_le_mul hrN hdN,
      Nat.mul_dvd_mul (Nat.dvd_factorial hr₁ hrN) (Nat.dvd_factorial (by omega) hdN)⟩
  have hpp (i) (hi : i∈I) (j) (hj : j∈I) : period i*period j∣P := by
    simpa only [P,← pow_add] using Nat.mul_dvd_mul (hper i hi).2.2 (hper j hj).2.2
  have hf (i) (hi : i∈I) : OnMod (period i) (f i) := by
    intro n; dsimp [f,unitTerm]
    obtain ⟨hr,_⟩ := mem_product.mp hi
    rw [onMod_lift (Nat.dvd_mul_right i.1 i.2) (ramanujan_onMod (mem_filter.mp hr).2) n,
      onMod_lift (Nat.dvd_mul_left i.2 i.1) (row_onMod i.2 (K i.2)) n]
  have hsup (i) (hi : i∈I) (n) : |f i n| ≤ 6*B*(N:ℝ)^2 := by
    obtain ⟨hr,hd⟩ := mem_product.mp hi
    have ha' : |b i.2|≤B := by
      dsimp [b]; rw [abs_div,abs_of_nonneg (Nat.cast_nonneg _ (α:=ℝ))]
      exact (div_le_self (abs_nonneg _) (by exact_mod_cast ((mem_Icc.mp hd).1.trans' (by decide : 1≤2)))).trans (ha _ hd)
    have hrow := (row_bound (mem_Icc.mp hd).1 (K i.2) n).trans
      (mul_le_mul_of_nonneg_left (show (i.2:ℝ)≤N by exact_mod_cast (mem_Icc.mp hd).2) (by norm_num))
    dsimp [f]; rw [abs_mul,abs_mul,abs_div,abs_of_nonneg (by linarith : 0≤G)]
    apply (mul_le_mul ((div_le_self (abs_nonneg _) hG).trans (unitTerm_bound hr n))
      (mul_le_mul ha' hrow (abs_nonneg _) hB) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      (Nat.cast_nonneg _)).trans_eq
    ring
  have hcard : (I.card:ℝ)≤(N:ℝ)^2 := by
    have hu := card_le_card (filter_subset (p:=Squarefree) (Icc 1 N))
    change (moduli N).card≤_ at hu
    dsimp [I,U,D]; rw [card_product,Nat.cast_mul]; rw [pow_two]
    have hU : (moduli N).card≤N := by simpa [Nat.card_Icc] using hu
    exact_mod_cast (Nat.mul_le_mul hU (by simp [Nat.card_Icc] : (Icc 2 N).card≤N))
  have hexp (n) : (∑ i∈I, f i n)^2=weight N n*low N K a n^2 := by
    rw [sum_product]; dsimp only [f,U,D,b,unitTerm]; unfold weight low
    simp_rw [← mul_sum,← sum_mul]; rw [← sum_div,mul_pow]
  have hs' : s⊆range X := fun p hp => mem_range.mpr (hs p hp).2.2
  have hmain := finite_period_square I period f hpos (fun i hi => ⟨(hper i hi).1,(hper i hi).2.1⟩)
    hpp hf (show 0≤6*B*(N:ℝ)^2 by positivity) hsup X
  simp_rw [hexp] at hmain
  calc
    _ = ∑ p∈s, weight N p*(low N K a p)^2 := by
      apply sum_congr rfl; intro p hp; rw [weight_prime (by omega) (hs p hp).1 (hs p hp).2.1,one_mul]
    _ ≤ ∑ p∈range X, weight N p*(low N K a p)^2 :=
      sum_le_sum_of_subset_of_nonneg hs' (fun i _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    _ ≤ _ := hmain.trans (add_le_add le_rfl (by
      calc
        _ ≤ ((N:ℝ)^2)^2*(2*((N^2:ℕ):ℝ)^2*(6*B*(N:ℝ)^2)^2) := by gcongr
        _ = _ := by push_cast; ring))

/-- The prime second moment remains bounded on the prime-counting scale when
coefficient sizes grow as the sixteenth root of the denominator. -/
theorem weighted_low_prime_band : ∃ C : ℝ, 0≤C ∧ ∀ (N : ℕ), 2≤N →
    ∀ (K : ℕ → ℕ) (a : ℕ → ℝ) (B : ℝ), 0≤B → (∀ d∈Icc 2 N, |a d|≤B*denominatorWeight d) →
    ∀ s : Finset ℕ, (∀ p∈s, p.Prime ∧ N<p ∧ p≤N^64) →
      ∑ p∈s,(low N K a p)^2 ≤ C*B^2*(N:ℝ)^64/Real.log N := by
  obtain ⟨C,hC,hcomplete⟩ := weighted_low_complete
  let Z := ∑' i : ℕ, ((i:ℝ)^2)⁻¹
  have hZ : 0≤Z := tsum_nonneg (fun _ => by positivity)
  refine ⟨2*Z*C+72,by positivity,?_⟩
  intro N hN K a B hB ha s hs
  let P := N.factorial^4
  have hN' : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have hl : 0<Real.log N := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  have hdvd (d : ℕ) (hd : 1≤d) (h : d≤N) : d∣P :=
    (Nat.dvd_factorial hd h).trans (dvd_pow_self _ (by decide : 4≠0))
  have hmean := hcomplete N N P (by omega) (pow_pos (Nat.factorial_pos _) _)
    (fun d hd => hdvd d (by have := (mem_Icc.mp hd).1; omega) (mem_Icc.mp hd).2)
    (fun r hr => hdvd r (mem_Icc.mp (mem_filter.mp hr).1).1 (mem_Icc.mp (mem_filter.mp hr).1).2) K a B hB ha
  have hg := normalizer_bound hN
  have hmajor := hmean.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hg (sq_nonneg B)) hC)
  have hbound (d : ℕ) (hd : d∈Icc 2 N) : |a d|≤B*N := by
    apply (ha d hd).trans; apply mul_le_mul_of_nonneg_left _ hB
    calc
      denominatorWeight d ≤ (d:ℝ)^((1:ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1≤d by have := (mem_Icc.mp hd).1; omega)) (by norm_num)
      _ ≤ N := by rw [Real.rpow_one]; exact_mod_cast (mem_Icc.mp hd).2
  have h := low_endpoint (X:=N^64+1) hN K a (mul_nonneg hB (Nat.cast_nonneg _)) hbound s
    (fun p hp => ⟨(hs p hp).1,(hs p hp).2.1,Nat.lt_succ_of_le (hs p hp).2.2⟩)
  have hp64 : 1≤(N:ℝ)^64 := one_le_pow₀ hN'
  have hX : ((N^64+1:ℕ):ℝ) ≤ 2*(N:ℝ)^64 := by push_cast; linarith
  have hmul := mul_le_mul hX hmajor (show 0 ≤ mean P (fun x => weight N x*low N K a x^2) by
    unfold mean; apply div_nonneg (sum_nonneg (fun _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))) (Nat.cast_nonneg _))
    (by positivity)
  have htail : (N:ℝ)^14*Real.log N ≤ (N:ℝ)^64 := calc
    _ ≤ (N:ℝ)^14*N := mul_le_mul_of_nonneg_left (Real.log_le_self (Nat.cast_nonneg N)) (by positivity)
    _ = (N:ℝ)^15 := by ring
    _ ≤ _ := pow_le_pow_right₀ hN' (by decide)
  apply h.trans ((add_le_add hmul le_rfl).trans ?_)
  change 2*(N:ℝ)^64*(Z/Real.log N*B^2*C)+72*(B*N)^2*(N:ℝ)^12 ≤ _
  rw [le_div_iff₀ hl]
  have hh := mul_le_mul_of_nonneg_left htail (show 0≤72*B^2 by positivity)
  calc
    _ = 2*Z*C*B^2*(N:ℝ)^64+72*B^2*((N:ℝ)^14*Real.log N) := by field_simp
    _ ≤ _ := by linarith only [hh]

/-- On prime arguments between N and N^64, the low-row prime second moment
saves the full prime-density logarithm. -/
theorem low_prime_band : ∃ C : ℝ, 0≤C ∧ ∀ (N : ℕ), 2≤N →
    ∀ (K : ℕ → ℕ) (a : ℕ → ℝ) (B : ℝ), 0≤B → (∀ d∈Icc 2 N, |a d|≤B) →
    ∀ s : Finset ℕ, (∀ p∈s, p.Prime ∧ N<p ∧ p≤N^64) →
      ∑ p∈s,(low N K a p)^2 ≤ C*B^2*(N:ℝ)^64/Real.log N := by
  obtain ⟨C,hC,H⟩ := weighted_low_prime_band
  refine ⟨C,hC,?_⟩; intro N hN K a B hB ha s hs
  apply H N hN K a B hB _ s hs; intro d hd
  apply (ha d hd).trans
  apply le_mul_of_one_le_right hB (Real.one_le_rpow _ (by norm_num))
  exact_mod_cast (show 1≤d by have := (mem_Icc.mp hd).1; omega)

/-- Discarding denominators through T saves T^(-1/8) in the squared moment
over primes from N to N^64, with no loss from the endpoint. -/
theorem tail_prime_band : ∃ C : ℝ, 0≤C ∧ ∀ (N T : ℕ), 2≤N → 0<T →
    ∀ (K : ℕ → ℕ) (a : ℕ → ℝ) (B : ℝ), 0≤B → (∀ d∈Icc 2 N, |a d|≤B) →
    ∀ s : Finset ℕ, (∀ p∈s, p.Prime ∧ N<p ∧ p≤N^64) →
      ∑ p∈s,(low N K (fun d => if T<d then a d else 0) p)^2 ≤
        C*(B/denominatorWeight T)^2*(N:ℝ)^64/Real.log N := by
  obtain ⟨C,hC,H⟩ := weighted_low_prime_band
  refine ⟨C,hC,?_⟩; intro N T hN hT K a B hB ha s hs
  have hpos : 0<denominatorWeight T := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hT) _
  apply H N hN K _ _ (div_nonneg hB hpos.le) _ s hs
  intro d hd; split_ifs with hh
  · apply (ha d hd).trans
    rw [div_mul_eq_mul_div,le_div_iff₀ hpos]
    apply mul_le_mul_of_nonneg_left _ hB
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hh.le) (by norm_num)
  · rw [abs_zero]; unfold denominatorWeight; positivity

end Arxiv.«2501.03234».ThetaSievedWindows
#print axioms Arxiv.«2501.03234».ThetaSievedWindows.weighted_low_prime_band
#print axioms Arxiv.«2501.03234».ThetaSievedWindows.tail_prime_band
#print axioms Arxiv.«2501.03234».ThetaSievedWindows.low_prime_band
