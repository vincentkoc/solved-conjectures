import ThetaPrimeTailTransfer

/-! Signed linear excursions of the original theta sum about the divisible diagonal. -/
namespace Arxiv.«2501.03234».ThetaOffDiagonalSigns
open Finset Filter ThetaPeriodMeans ThetaConditionalRows ThetaAbelPrimes ThetaPrimeTailTransfer
open ThetaRowCorrelations ThetaReciprocalInversion ThetaReciprocalBlocks ThetaPrimeMeanSquare
open ThetaDivisibleDiagonal

private lemma class_mass {q r : ℕ} [NeZero q] (hq : 24∣q) (hr : r=1 ∨ r=17) :
    unitMean q (fun n => if n%24=r then (1:ℝ) else 0)=1/8 := by
  rw [unitMean_lift hq (by intro n; simp),unitMean,
    ThetaReciprocalFibers.unit_sum_nat (fun n => if n%24=r then (1:ℝ) else 0),sum_filter]
  have ht : Nat.totient 24=8 := by decide +kernel
  rcases hr with rfl|rfl <;> norm_num [sum_range_succ,Nat.Coprime,ht]

private lemma test_mean {q r : ℕ} [NeZero q] (hq : 24∣q) (hr : r=1 ∨ r=17)
    (s c e : ℝ) (F : ℕ → ℝ) :
    unitMean q (fun n => (if n%24=r then s*F n-c else 0)-e) =
      s*unitMean q (fun n => if n%24=r then F n else 0)-c/8-e := by
  have h (n : ℕ) : (if n%24=r then s*F n-c else 0)=
      s*(if n%24=r then F n else 0)-c*(if n%24=r then 1 else 0) := by split_ifs <;> ring
  have hm := class_mass hq hr
  unfold unitMean at hm ⊢
  simp_rw [h,sum_sub_distrib,← mul_sum]
  simp only [sum_const,card_univ,ZMod.card_units_eq_totient,nsmul_eq_mul]
  have ht : (q.totient:ℝ)≠0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  field_simp [ht] at hm ⊢
  linear_combination -c*hm

private lemma frequently_positive_prefix {q : ℕ} [NeZero q] {g : ℕ → ℝ} (hg : OnMod q g)
    (hm : 0<unitMean q g) : ∃ᶠ X : ℕ in atTop, 0<∑ p∈Nat.primesLE X,g p := by
  apply frequently_atTop.mpr
  intro B
  let f (n : ℕ) := ∑ p∈Nat.primesLE n,g p
  let C := ∑ n∈range B,|f n|
  have hc : 0≤C := sum_nonneg (fun _ _ => abs_nonneg _)
  obtain ⟨X,h⟩ := prime_prefix_unbounded hg hm C
  refine ⟨X,?_,hc.trans_lt h⟩
  by_contra! hx
  exact h.not_ge ((le_abs_self (f X)).trans (single_le_sum (f:=fun n => |f n|)
    (fun _ _ => abs_nonneg _) (mem_range.mpr hx)))

private lemma transfer {q r : ℕ} [NeZero q] {s c ε : ℝ} {F : ℕ → ℝ}
    (hs : |s|=1) (hε : 0<ε) (hq : 24∣q) (hf : OnMod q F)
    (hm : 0<unitMean q (fun n => (if n%24=r then s*F n-c else 0)-2*ε))
    (herr : ∀ᶠ X : ℕ in atTop, ∑ p∈Nat.primesLE X,|scaledOff p-F p|≤ε*Nat.primeCounting X) :
    ∃ δ : ℝ, 0<δ ∧ ∃ᶠ X : ℕ in atTop, δ*Nat.primeCounting X ≤
      (((Nat.primesLE X).filter (fun p => p%24=r ∧ c<s*scaledOff p)).card:ℝ) := by
  classical
  let g (n : ℕ) := (if n%24=r then s*F n-c else 0)-2*ε
  have hg : OnMod q g := by intro n; dsimp only [g]; rw [Nat.mod_mod_of_dvd _ hq,hf]
  let M := 1+|c|+∑ n∈range q,|F n|
  have hM : 0<M := by dsimp [M]; positivity
  have hbound (n : ℕ) : s*F n-c≤M := by
    have h := single_le_sum (f:=fun i => |F i|) (fun _ _ => abs_nonneg _) (mem_range.mpr (Nat.mod_lt n (NeZero.pos q)))
    rw [hf] at h
    have hsf := le_abs_self (s*F n)
    rw [abs_mul,hs,one_mul] at hsf
    dsimp only [M]; linarith only [h,hsf,neg_le_abs c]
  have hpoint (p : ℕ) : g p ≤ |scaledOff p-F p|+
      (if p%24=r ∧ c<s*scaledOff p then M else 0)-2*ε := by
    dsimp only [g]
    by_cases hr : p%24=r
    · simp only [hr,ite_true,true_and]
      split_ifs with h
      · linarith only [hbound p,abs_nonneg (scaledOff p-F p)]
      · have hh := le_abs_self (s*(F p-scaledOff p))
        rw [abs_mul,hs,one_mul,abs_sub_comm] at hh
        linarith only [le_of_not_gt h,hh]
    · simp [hr,abs_nonneg]
  refine ⟨ε/M,div_pos hε hM,?_⟩
  apply ((frequently_positive_prefix hg hm).and_eventually herr).mono
  intro X hh
  have hu := sum_le_sum (s:=Nat.primesLE X) (fun p _ => hpoint p)
  simp only [sum_sub_distrib,sum_add_distrib,← sum_filter,sum_const,nsmul_eq_mul,
    Nat.primesLE_card_eq_primeCounting] at hu
  rw [div_mul_eq_mul_div,div_le_iff₀ hM]
  linarith only [hh.1,hh.2,hu]

private lemma scaled_excursions {r : ℕ} {s c a₀ : ℝ}
    (hweight : ∀ V : ℕ, 2≤V → a₀≤commonWeight (2*V^52) 3)
    (hrs : (r=1 ∧ s=1) ∨ (r=17 ∧ s= -1)) (hc : c<4*a₀/15) :
    ∃ δ : ℝ, 0<δ ∧ ∃ᶠ X : ℕ in atTop, δ*Nat.primeCounting X ≤
      ((ThetaPrimeDensity.primeSet (fun p => p%24=r ∧ c<s*scaledOff p) X).card:ℝ) := by
  classical
  let ε := (a₀/30-c/8)/4
  have hε : 0<ε := by dsimp [ε]; linarith
  obtain ⟨T,V,hT,hV,herr⟩ := prime_model_absolute hε
  let t := (Icc 2 T).filter Odd
  let M := ∏ d∈t,d
  have hM : Odd M := Finset.prod_induction (s:=t) id Odd (fun _ _ => Odd.mul) (by decide)
    (fun _ hd => (mem_filter.mp hd).2)
  let : NeZero M := ⟨hM.pos.ne'⟩
  have hdM (d) (hd : d∈Icc 2 T) (ho : Odd d) : d∣M := dvd_prod_of_mem id (mem_filter.mpr ⟨hd,ho⟩)
  have h24 : 24∣8*M := Nat.mul_dvd_mul_left 8 (hdM 3 (mem_Icc.mpr ⟨by decide,hT⟩) (by decide))
  let a := commonWeight (2*V^52)
  let K := coneWindow (coneWidth V)
  have hper : OnMod (8*M) (model T V) := onMod_lift (Nat.dvd_mul_left M 8) (low_onMod hdM K a)
  have h₃ : a₀≤a 3 := hweight V hV
  obtain ⟨hp,hn⟩ := low_class_bias hM hT hdM K (by dsimp [K,coneWindow,coneWidth]; omega)
    a (fun d _ => (commonWeight_bounds _ d).1)
  change a 3/30≤unitMean (8*M) (fun n => if n%24=1 then model T V n else 0) at hp
  change unitMean (8*M) (fun n => if n%24=17 then model T V n else 0)≤ -(a 3/30) at hn
  have hr := hrs.imp And.left And.left
  have hs : |s|=1 := by rcases hrs with ⟨_,rfl⟩|⟨_,rfl⟩ <;> norm_num
  have hm : 0<unitMean (8*M) (fun n => (if n%24=r then s*model T V n-c else 0)-2*ε) := by
    rw [test_mean h24 hr]
    dsimp only [ε]
    rcases hrs with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · linarith only [hp,h₃,hc]
    · linarith only [hn,h₃,hc]
  obtain ⟨δ,hδ,H⟩ := transfer hs hε h24 hper hm herr
  refine ⟨δ,hδ,H.mono (fun X hX => hX.trans ?_)⟩
  apply Nat.cast_le.mpr; apply card_le_card
  intro p hp
  simpa only [ThetaPrimeDensity.primeSet,mem_filter] using hp

private lemma original_excursions {r : ℕ} {s c a₀ : ℝ}
    (hweight : ∀ V : ℕ, 2≤V → a₀≤commonWeight (2*V^52) 3)
    (hrs : (r=1 ∧ s=1) ∨ (r=17 ∧ s= -1)) (hc : c<32*a₀/(15*Real.pi^2)) :
    ∃ δ : ℝ, 0<δ ∧ ∃ᶠ X : ℕ in atTop, δ*Nat.primeCounting X ≤
      ((ThetaPrimeDensity.primeSet (fun p => p%24=r ∧ c*p<s*((S p:ℝ)-divisibleDiagonal p)) X).card:ℝ) := by
  have hπ : 0<Real.pi^2 := sq_pos_of_pos Real.pi_pos
  have hc' : c*(Real.pi^2/8)<4*a₀/15 := by
    rw [lt_div_iff₀ (by positivity)] at hc
    linarith only [hc]
  obtain ⟨δ,hδ,H⟩ := scaled_excursions hweight hrs hc'
  refine ⟨δ,hδ,H.mono (fun X hX => hX.trans ?_)⟩
  apply Nat.cast_le.mpr; apply card_le_card
  classical
  intro p hp
  simp only [ThetaPrimeDensity.primeSet,mem_filter] at hp ⊢
  obtain ⟨hp,hr,hh⟩ := hp
  have hprime := (Nat.mem_primesLE.mp hp).2
  let : Fact p.Prime := ⟨hprime⟩
  have ho : p%2=1 := by rcases hrs with ⟨rfl,_⟩|⟨rfl,_⟩ <;> omega
  refine ⟨hp,hr,?_⟩
  rw [S_eq_diagonal_add_offDiagonal ho,add_sub_cancel_left]
  have hpos : 0<(p:ℝ) := by exact_mod_cast hprime.pos
  unfold scaledOff at hh
  rw [show s*(Real.pi^2/8*(offDiagonal p/p))=(s*offDiagonal p/p)*(Real.pi^2/8) by ring] at hh
  exact (lt_div_iff₀ hpos).mp ((mul_lt_mul_iff_left₀ (by positivity : 0<Real.pi^2/8)).mp hh)

/-- Any uniform lower bound for the denominator-three weight transfers to
opposite signed excursions on sets of positive upper prime density. -/
theorem S_prime_excursion_densities_of_weight {a₀ c : ℝ}
    (hweight : ∀ V : ℕ, 2≤V → a₀≤commonWeight (2*V^52) 3) (hc : c<32*a₀/(15*Real.pi^2)) :
    (∃ δ : ℝ, 0<δ ∧ ∃ᶠ X : ℕ in atTop, δ*Nat.primeCounting X ≤
      ((ThetaPrimeDensity.primeSet (fun p => p%24=1 ∧ c*p<(S p:ℝ)-divisibleDiagonal p) X).card:ℝ)) ∧
    (∃ δ : ℝ, 0<δ ∧ ∃ᶠ X : ℕ in atTop, δ*Nat.primeCounting X ≤
      ((ThetaPrimeDensity.primeSet (fun p => p%24=17 ∧ (S p:ℝ)-divisibleDiagonal p< -(c*p)) X).card:ℝ)) := by
  constructor
  · simpa only [one_mul] using original_excursions hweight (Or.inl ⟨rfl,rfl⟩) hc
  · have he (p : ℕ) : c*p< -((S p:ℝ)-divisibleDiagonal p) ↔ (S p:ℝ)-divisibleDiagonal p< -(c*p) := by
      constructor <;> intro h <;> linarith
    simpa only [neg_one_mul,he] using original_excursions hweight (Or.inr ⟨rfl,rfl⟩) hc

/-- For every c below 32/(15π²), each signed excursion of the original
theta sum about its divisible diagonal has positive upper density relative
to all primes. The two progressions both lie in 1 modulo 8. -/
theorem S_prime_excursion_densities {c : ℝ} (hc : c<32/(15*Real.pi^2)) :
    (∃ δ : ℝ, 0<δ ∧ ∃ᶠ X : ℕ in atTop, δ*Nat.primeCounting X ≤
      ((ThetaPrimeDensity.primeSet (fun p => p%24=1 ∧ c*p<(S p:ℝ)-divisibleDiagonal p) X).card:ℝ)) ∧
    (∃ δ : ℝ, 0<δ ∧ ∃ᶠ X : ℕ in atTop, δ*Nat.primeCounting X ≤
      ((ThetaPrimeDensity.primeSet (fun p => p%24=17 ∧ (S p:ℝ)-divisibleDiagonal p< -(c*p)) X).card:ℝ)) := by
  apply S_prime_excursion_densities_of_weight (a₀:=1)
  · intro V hV
    apply commonWeight_three
    have := Nat.pow_le_pow_left hV 52; omega
  · simpa only [mul_one] using hc

end Arxiv.«2501.03234».ThetaOffDiagonalSigns
#print axioms Arxiv.«2501.03234».ThetaOffDiagonalSigns.S_prime_excursion_densities_of_weight
#print axioms Arxiv.«2501.03234».ThetaOffDiagonalSigns.S_prime_excursion_densities
