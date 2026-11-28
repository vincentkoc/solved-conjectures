import ThetaGrowingPrimeExcursions
import ThetaEmpiricalPrimeMoments

/-! A uniform second moment and a finite upper quantile convert a rare-class
signed mean into a positive fraction of the expected class count. -/
namespace Arxiv.«2501.03234».ThetaGrowingExcursionCounts
open Finset Real Filter ThetaSiegelWalfiszBand ThetaCompactModulus
noncomputable section

private theorem trim {s D : Finset ℕ} (hDs : D⊆s) (R : ℕ → ℝ)
    {w α u J M K m : ℝ} (hw : 0≤w) (hα : 1≤α) (hu : 0≤u) (hJ : 4*α≤J)
    (hM : 0≤M) (hm : 0 < m) (hkm : K≤ m^2) (hmw : M/m≤w) (hD : (D.card:ℝ)≤2*w)
    (hmean : w*J≤∑ p∈D,R p)
    (hbad : ((s.filter (fun p => u≤|R p|)).card:ℝ)≤M/m^4)
    (hE : (∑ p∈s,(R p)^2)≤M*K) :
    w*α ≤ ((D.filter (fun p => α≤R p)).card:ℝ)*u := by
  classical
  let B := s.filter (fun p => u≤|R p|)
  let A := D.filter (fun p => α≤R p)
  have hd : (∑ p∈B,|R p|)^2≤(M/m)^2 := by
    have hcs := sum_mul_sq_le_sq_mul_sq B (fun _ => (1:ℝ)) (fun p => |R p|)
    simp only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one,sq_abs] at hcs
    have hBs : B⊆s := filter_subset _ _
    have he := (sum_le_sum_of_subset_of_nonneg hBs (fun p _ _ => sq_nonneg (R p))).trans hE
    calc _ ≤ (B.card:ℝ)*∑ p∈B,(R p)^2 := hcs
         _ ≤ (M/m^4)*(M*K) := mul_le_mul hbad he (sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
         _ ≤ (M/m^4)*(M*m^2) := by gcongr
         _ = _ := by field_simp
  have hmass : (∑ p∈B,|R p|)≤w := by
    have hh : (∑ p∈B,|R p|)≤M/m := by
      by_contra! h
      exact (not_lt_of_ge hd) (pow_lt_pow_left₀ h (by positivity) (by decide))
    exact hh.trans hmw
  have hab : (∑ p∈D,R p) ≤ (D.card:ℝ)*α+(A.card:ℝ)*u+∑ p∈B,|R p| := by
    calc _ ≤ ∑ p∈D,(α+(if α≤R p then u else 0)+(if u≤|R p| then |R p| else 0)) := by
             apply sum_le_sum; intro p _
             split_ifs <;> linarith [le_abs_self (R p)]
         _ ≤ _ := by
             simp only [sum_add_distrib,sum_const,nsmul_eq_mul,←sum_filter]
             apply add_le_add_right
             exact sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ hDs) (fun p _ _ => abs_nonneg _)
  change w*α≤(A.card:ℝ)*u
  nlinarith only [hmean,hab,hmass,mul_le_mul_of_nonneg_right hD (show 0≤α by linarith),
    mul_le_mul_of_nonneg_left hJ hw,mul_le_mul_of_nonneg_left hα hw]

/-- Past an absolute cutoff in the modulus, the sum from primes above the
upper quantile costs at most the expected count in a single reduced class. -/
private theorem quantile :
    ∃ C K : ℝ, 0<C ∧ 0<K ∧ ∃ X₀ m₀ : ℕ, ∀ {T m X : ℕ}, 4≤T → m₀≤ m → X₀≤X →
    log (m:ℝ)≤(T:ℝ)^3 → 16*(m:ℝ)≤log X →
    let R (p : ℕ) := (S p:ℝ)/p-log p/2
    let u := C*(log T)^2
    (K≤(m:ℝ)^2 ∧ ((Nat.primesLE X).filter (fun p => u≤|R p|)).card ≤
      (X.primeCounting:ℝ)/(m:ℝ)^4 ∧ (∑ p∈Nat.primesLE X,(R p)^2)≤X.primeCounting*K) := by
  obtain ⟨A,hA,ha⟩ := ThetaPrimeQuantiles.original
  obtain ⟨D,hD,hd⟩ := ThetaEmpiricalPrimeMoments.logarithmic
  let K := (D*(1+log 2)^2)^2
  have hK : 0<K := by have := log_pos (by norm_num : (1:ℝ)<2); dsimp [K]; positivity
  have hl : Tendsto (fun m : ℕ => log (m:ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨m₀,hm₀⟩ := eventually_atTop.mp ((hl.eventually_ge_atTop (1:ℝ)).and ((log_power 2).and
    (((tendsto_pow_atTop (n:=2) (by decide)).comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop K)))
  obtain ⟨X₀,hX₀⟩ := eventually_atTop.mp (ha.and (hd.and (hl.eventually_ge_atTop 4)))
  refine ⟨26*A,K,by positivity,hK,X₀,m₀,?_⟩
  intro T m X hT hm hX hlog hL R u
  obtain ⟨hm1,hm2,hm3⟩ := hm₀ m hm
  obtain ⟨hQ,hE,hX4⟩ := hX₀ X hX
  change 1≤log (m:ℝ) at hm1
  change 4≤log (X:ℝ) at hX4
  have hmp : 0<(m:ℝ) := by by_contra! hn; have := Nat.cast_nonneg (α:=ℝ) m; simp [le_antisymm hn this] at hm1; linarith only [hm1]
  have hTp : 0<(T:ℝ) := by exact_mod_cast (show 0<T by omega)
  have hfour := log_le_log (by norm_num : (0:ℝ)<4) (show (4:ℝ)≤T by exact_mod_cast hT)
  have hT1 : 1≤log (T:ℝ) := by linarith only [hfour,Real.log_two_gt_d9,show log (4:ℝ)=2*log 2 by rw [show (4:ℝ)=2^2 by norm_num,log_pow]; norm_num]
  let t := 4*log (m:ℝ)
  have ht : 1≤t := by dsimp [t]; linarith
  have htlog : log t≤4*log T := by
    have hh := log_le_log (by linarith only [hm1] : 0<log (m:ℝ)) hlog
    rw [log_pow] at hh
    dsimp [t]; rw [log_mul (by norm_num) (by linarith only [hm1] : log (m:ℝ)≠0)]
    norm_num at hh; linarith
  have hHt : ThetaPrimeQuantiles.height (log X) t≤26*(log T)^2 := by
    have ht2 : t^2/log X≤1 := by
      rw [div_le_one (by linarith only [hX4])]
      dsimp [t]; nlinarith only [hm2,hL]
    have hn : 0≤t^2/log X := div_nonneg (sq_nonneg _) (by linarith only [hX4])
    have hh := pow_le_pow_left₀ (by have := log_nonneg ht; linarith : 0≤1+log t)
      (show 1+log t≤5*log T by linarith only [hT1,htlog]) 2
    unfold ThetaPrimeQuantiles.height
    nlinarith only [hh,pow_le_pow_left₀ hn ht2 2,pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1) hT1 2]
  have hU : A*ThetaPrimeQuantiles.height (log X) t≤u := by
    dsimp [u]; nlinarith only [mul_le_mul_of_nonneg_left hHt hA.le]
  have hsub : (Nat.primesLE X).filter (fun p => u≤|R p|)⊆
      ThetaMovingOriginalTail.exceptions (A*ThetaPrimeQuantiles.height (log X) t) X := by
    intro p hp; obtain ⟨hp,hpu⟩ := mem_filter.mp hp
    exact ThetaPrimeQuantiles.member.mpr ⟨(Nat.mem_primesLE.mp hp).1,(Nat.mem_primesLE.mp hp).2,hU.trans hpu⟩
  have he : exp (-t)=((m:ℝ)^4)⁻¹ := by
    dsimp [t]; rw [exp_neg,show 4*log (m:ℝ)=log ((m:ℝ)^4) by rw [log_pow]; norm_num,exp_log (pow_pos hmp _)]
  have hQ' := (Nat.cast_le.mpr (card_le_card hsub)).trans (hQ t ht)
  rw [he,←div_eq_mul_inv] at hQ'
  refine ⟨hm3,hQ',?_⟩
  have h2log : 0≤log (2:ℝ) := log_nonneg (by norm_num)
  have h2 := hE 2 (by decide) (by norm_num; nlinarith only [hX4,mul_nonneg h2log (show 0≤log (X:ℝ) by linarith)])
  simpa only [Nat.cast_ofNat,sq_abs,K,R] using h2

/-- A fixed positive proportion of the expected size of a growing reduced
class has a positive deviation of order (log T)^2, at every admissible endpoint. -/
theorem uniform (hsw : Ordinary) : ∃ β η : ℝ, 0<β ∧ 0<η ∧ ∃ N₀ : ℕ, ∀ᶠ T : ℕ in atTop,
    ∀ q r : ℕ, 0 < q → r < q → r.Coprime q → Real.log q≤η*Real.log T → ∀ z : ℝ, |z|=1 →
    let m := modulus T
    1 < m ∧ q∣m ∧ ∃ b < m, b.Coprime m ∧ b%q=r ∧ ∀ N≥N₀, (m:ℝ)≤log N →
      β*(N^64).primeCounting/m.totient ≤ (((band N).filter (fun p =>
        p%m=b ∧ (log T)^2/(64*Real.pi^2)≤z*((S p:ℝ)/p-log p/2))).card:ℝ) := by
  obtain ⟨C,K,hC,hK,X₀,m₀,hQ⟩ := quantile
  let a := 1/(64*Real.pi^2)
  have ha : 0<a := by dsimp [a]; positivity
  obtain ⟨η,hη,N₁,H⟩ := ThetaGrowingPrimeExcursions.uniform hsw
  refine ⟨a/C,η,div_pos ha hC,hη,max N₁ X₀,?_⟩
  have hlim : Tendsto (fun T : ℕ => (log (T:ℝ))^2) atTop atTop :=
    (tendsto_pow_atTop (n:=2) (by decide)).comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [H,eventually_ge_atTop (max 8 m₀),hlim.eventually_ge_atTop (1/a)] with T hU hT hlimT
  intro q r hq hr hc hqt z hz
  have HH := hU q r hq hr hc hqt z hz
  obtain ⟨hm,qm,b,hb,hbc,hbr,h⟩ := HH
  let m := modulus T
  have hm0 : 0 < m := positive T
  have hT4 := (le_max_left 8 m₀).trans hT
  have hTm : T≤ m := Nat.le_of_dvd hm0 (contains (by omega) le_rfl)
  refine ⟨hm,qm,b,hb,hbc,hbr,?_⟩
  intro N hN hmL
  let X := N^64
  let M : ℝ := X.primeCounting
  let R (p : ℕ) := z*((S p:ℝ)/p-log p/2)
  let D := (band N).filter (fun p => p%m=b)
  let w := M/m.totient
  let v := (log T)^2
  have hv : 0<v := by
    have hl : 1/a≤v := hlimT
    exact lt_of_lt_of_le (by positivity) hl
  have hmhp : 0<(m:ℝ) := by exact_mod_cast hm0
  have hφ : 0<(m.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hm0
  have hw : 0≤w := div_nonneg (Nat.cast_nonneg _) hφ.le
  have hX : X₀≤X := ((le_max_right N₁ X₀).trans hN).trans (Nat.le_self_pow (by decide : 64≠0) N)
  have hL : 16*(m:ℝ)≤log X := by
    dsimp [X]; rw [Nat.cast_pow,log_pow]; norm_num
    linarith only [hmL,Nat.cast_nonneg m (α:=ℝ)]
  obtain ⟨hkm,hbad,hE⟩ := hQ (by omega : 4≤T) ((le_max_right ..).trans (hT.trans hTm)) hX
    ((size T).trans (by
      have ht : (8:ℝ)≤T := by exact_mod_cast hT4
      have h4 := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)
      nlinarith only [mul_le_mul_of_nonneg_right (show 4*(log 4+4)≤(T:ℝ)^2 by nlinarith only [h4,ht,sq_nonneg ((T:ℝ)-8)]) (Nat.cast_nonneg T : 0≤(T:ℝ))])) hL
  have hDsub : D⊆Nat.primesLE X := fun p hp => (mem_filter.mp (mem_filter.mp hp).1).1
  obtain ⟨hDc,hmean⟩ := h N ((le_max_left ..).trans hN) hmL
  rw [mul_div_assoc] at hDc
  have hJ : w*(4*(a*v))≤∑ p∈D,R p := by
    apply le_trans _ hmean
    change w*(4*(a*v))≤w*v/(16*Real.pi^2)
    apply le_of_eq; dsimp [a]; ring
  have hav : 1≤a*v := by
    have hx := (div_le_iff₀ ha).mp hlimT
    change 1≤v*a at hx; linarith
  have habs (p : ℕ) : |R p|=|(S p:ℝ)/p-log p/2| := by simp only [R,abs_mul,hz,one_mul]
  have hsquare (p : ℕ) : (R p)^2=((S p:ℝ)/p-log p/2)^2 := by rw [←sq_abs (R p),habs,sq_abs]
  have hbad' : (((Nat.primesLE X).filter (fun p => C*v≤|R p|)).card:ℝ)≤M/(m:ℝ)^4 := by simpa only [habs] using hbad
  have hE' : (∑ p∈Nat.primesLE X,(R p)^2)≤M*K := by simpa only [hsquare] using hE
  have hh := trim hDsub R (m:=(m:ℝ)) (w:=w) (M:=M) hw hav (mul_nonneg hC.le hv.le) le_rfl
    (Nat.cast_nonneg _) hmhp hkm
    (div_le_div_of_nonneg_left (Nat.cast_nonneg _) hφ (by exact_mod_cast Nat.totient_le m)) hDc hJ hbad' hE'
  let G := (band N).filter (fun p => p%m=b ∧ a*v≤R p)
  have heq : D.filter (fun p => a*v≤R p)=G := by ext p; simp [D,G,and_assoc]
  rw [heq] at hh
  change w*(a*v)≤(G.card:ℝ)*(C*v) at hh
  have hc' : w*a≤G.card*C := (mul_le_mul_iff_left₀ hv).mp (by linarith only [show w*a*v≤G.card*C*v by simpa only [mul_assoc] using hh])
  have hα (p : ℕ) : a*v≤R p ↔ (log T)^2/(64*Real.pi^2)≤z*((S p:ℝ)/p-log p/2) := by
    rw [show a*v=(log T)^2/(64*Real.pi^2) by dsimp [a,v]; ring]
  have heq' : G=(band N).filter (fun p => p%m=b ∧ (log T)^2/(64*Real.pi^2)≤z*((S p:ℝ)/p-log p/2)) := by
    ext p; simp [G,hα]
  rw [←heq']
  calc a/C*(N^64).primeCounting/m.totient = (w*a)/C := by dsimp [w,M,X]; ring
       _ ≤ _ := (div_le_iff₀ hC).mpr hc'

#print axioms uniform
end
end Arxiv.«2501.03234».ThetaGrowingExcursionCounts
