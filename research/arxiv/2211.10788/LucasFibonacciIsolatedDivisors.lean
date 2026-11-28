import research.arxiv.«2211.10788».LucasFibonacciToralGaps
import research.arxiv.«2211.10788».LucasFibonacciLargeFactors

/-! Prime divisors shared across shifted upper and lower Hosoya sites. -/

namespace Arxiv.«2211.10788»
namespace HosoyaNeighbor

/-- The absolute determinant of consecutive values at a fixed separation. -/
def shiftDet (s t : HosoyaNeighbor) (h : ℕ) : ℕ :=
  ((s.value 0 : ℤ) * t.value (1+h) - (s.value 1 : ℤ) * t.value h).natAbs

private def detAt (s t : HosoyaNeighbor) (h n : ℕ) : ℤ :=
  (s.value n : ℤ)*t.value (n+1+h) - (s.value (n+1) : ℤ)*t.value (n+h)

private theorem det_succ (s t : HosoyaNeighbor) (h n : ℕ) :
    detAt s t h (n+1) = -detAt s t h n := by
  unfold detAt
  rw [show n+1+1+h = (n+h)+2 by omega, t.value_step,
    show n+1+1 = n+2 by omega,s.value_step,show n+1+h = n+h+1 by omega]
  push_cast
  ring

private theorem abs_det (s t : HosoyaNeighbor) (h n : ℕ) :
    (detAt s t h n).natAbs = shiftDet s t h := by
  induction n with
  | zero => simp [detAt,shiftDet]
  | succ n ih => rw [det_succ,Int.natAbs_neg,ih]

theorem shiftDet_pos (s t : HosoyaNeighbor) (h : ℕ) (hd : s ≠ t ∨ 0 < h) :
    0 < shiftDet s t h := by
  apply Int.natAbs_pos.mpr
  have hh := pair_independent s t h hd
  rw [Nat.zero_add] at hh
  exact_mod_cast hh

/-- Every common divisor of two sites divides the same determinant at all translations. -/
theorem dvd_shiftDet_of_dvd {s t : HosoyaNeighbor} {h n p : ℕ}
    (ha : p ∣ s.value n) (hb : p ∣ t.value (n+h)) : p ∣ shiftDet s t h := by
  rw [← abs_det s t h n]
  have ha' : (p : ℤ) ∣ s.value n := by exact_mod_cast ha
  have hb' : (p : ℤ) ∣ t.value (n+h) := by exact_mod_cast hb
  have hh : (p : ℤ) ∣ detAt s t h n :=
    dvd_sub (dvd_mul_of_dvd_left ha' _) (dvd_mul_of_dvd_right hb' _)
  simpa using Int.natAbs_dvd_natAbs.mpr hh

private theorem value_upper (s : HosoyaNeighbor) (n : ℕ) : s.value n ≤ 2^(n+3) := by
  induction n using Nat.twoStepInduction with
  | zero => cases s <;> decide
  | one => cases s <;> decide
  | more n h₀ h₁ =>
    rw [s.value_step]
    have h₂ : 2^(n+3) ≤ (2:ℕ)^(n+1+3) := Nat.pow_le_pow_right (by decide) (by omega)
    rw [show n+2+3 = (n+1+3)+1 by omega,pow_succ]
    exact (Nat.add_le_add h₁ (h₀.trans h₂)).trans_eq (by ring)

private theorem shiftDet_le (s t : HosoyaNeighbor) (h : ℕ) : shiftDet s t h ≤ 2^(h+10) := by
  have bound (u : HosoyaNeighbor) (n : ℕ) : u.value n ≤ 2^(n+4) :=
    (u.value_upper n).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have h₀ := bound s 0
  have h₁ := bound s 1
  have h₂ := bound t (1+h)
  have h₃ := bound t h
  have b₁ := Nat.mul_le_mul h₀ h₂
  have b₂ := Nat.mul_le_mul h₁ h₃
  have e₁ : (2:ℕ)^(0+4) * 2^(1+h+4) = 2^(h+9) := by rw [←pow_add]; congr 1; omega
  have e₂ : (2:ℕ)^(1+4) * 2^(h+4) = 2^(h+9) := by rw [←pow_add]; congr 1; omega
  rw [e₁] at b₁
  rw [e₂] at b₂
  have ha := Int.natAbs_add_le ((s.value 0 : ℤ)*t.value (1+h)) (-((s.value 1 : ℤ)*t.value h))
  simp only [shiftDet,sub_eq_add_neg,Int.natAbs_neg,Int.natAbs_mul,Int.natAbs_natCast] at *
  rw [show h+10 = (h+9)+1 by omega,pow_succ]
  omega

open Finset

/-- A common multiple of all nonzero shifted determinants through distance H. -/
def shiftDetProduct (H : ℕ) : ℕ :=
  ∏ h ∈ range (H+1), ∏ s : HosoyaNeighbor, ∏ t : HosoyaNeighbor, max 1 (shiftDet s t h)

theorem shiftDetProduct_pos (H : ℕ) : 0 < shiftDetProduct H :=
  prod_pos fun _ _ => prod_pos fun _ _ => prod_pos fun _ _ => (le_max_left 1 _).trans_lt' Nat.zero_lt_one

theorem shiftDetProduct_le (H : ℕ) : shiftDetProduct H ≤ 2^((H+1)*(4*(H+10))) := by
  have base {h : ℕ} (hh : h ∈ range (H+1)) (s t : HosoyaNeighbor) :
      max 1 (shiftDet s t h) ≤ 2^(H+10) := by
    apply max_le Nat.one_le_two_pow
    exact (shiftDet_le s t h).trans (Nat.pow_le_pow_right (by decide) (by simp at hh; omega))
  have card : Fintype.card HosoyaNeighbor = 2 := by decide
  calc
    shiftDetProduct H ≤ ∏ h ∈ range (H+1), ∏ _s : HosoyaNeighbor, ∏ _t : HosoyaNeighbor, 2^(H+10) :=
      prod_le_prod' fun h hh => prod_le_prod' fun s _ => prod_le_prod' fun t _ => base hh s t
    _ = _ := by
      simp only [prod_const, card_univ, card, card_range, ←pow_mul]
      apply congrArg (fun e : ℕ => (2:ℕ)^e)
      ring

/-- Two distinct sites at separation at most H can share only divisors of this fixed integer. -/
theorem dvd_shiftDetProduct_of_shared {s t : HosoyaNeighbor} {m n p H : ℕ}
    (hd : s ≠ t ∨ m ≠ n) (hgap : Nat.dist m n ≤ H)
    (hp : p ∣ s.value m) (hq : p ∣ t.value n) : p ∣ shiftDetProduct H := by
  have ordered {x y : HosoyaNeighbor} {j h : ℕ} (hh : h ≤ H) (hne : x ≠ y ∨ 0 < h)
      (ha : p ∣ x.value j) (hb : p ∣ y.value (j+h)) : p ∣ shiftDetProduct H := by
    have hdv := dvd_shiftDet_of_dvd ha hb
    have hm := dvd_prod_of_mem (fun t : HosoyaNeighbor => max 1 (shiftDet x t h)) (mem_univ y)
    rw [max_eq_right (shiftDet_pos x y h hne)] at hm
    have hs := dvd_prod_of_mem (fun s : HosoyaNeighbor => ∏ t : HosoyaNeighbor, max 1 (shiftDet s t h)) (mem_univ x)
    have hj := dvd_prod_of_mem (fun j : ℕ => ∏ s : HosoyaNeighbor, ∏ t : HosoyaNeighbor,
      max 1 (shiftDet s t j)) (mem_range.mpr (by omega : h < H+1))
    exact hdv.trans (hm.trans (hs.trans hj))
  rcases le_total m n with hm|hn
  · obtain ⟨h,rfl⟩ := Nat.exists_eq_add_of_le hm
    exact ordered (by simpa [Nat.dist] using hgap) (hd.imp_right (by omega)) hp hq
  · obtain ⟨h,rfl⟩ := Nat.exists_eq_add_of_le hn
    exact ordered (by simpa [Nat.dist] using hgap) (hd.imp Ne.symm (by omega)) hq hp

private theorem value_add (s : HosoyaNeighbor) (n j : ℕ) :
    s.value (n+j+1) = Nat.fib j*s.value n + Nat.fib (j+1)*s.value (n+1) := by
  induction j using Nat.twoStepInduction with
  | zero => simp
  | one => simpa only [show 1+1 = 2 by rfl,Nat.fib_one,Nat.fib_two,one_mul] using (s.value_step n).trans (Nat.add_comm ..)
  | more j h₀ h₁ =>
    rw [show n+(j+2)+1=(n+j+1)+2 by omega,s.value_step,
      show n+j+1+1=n+(j+1)+1 by omega,h₁,h₀,
      Nat.fib_add_two (n:=j+1),Nat.fib_add_two (n:=j)]
    ring

private theorem consecutive_coprime (s : HosoyaNeighbor) (n : ℕ) :
    (s.value n).Coprime (s.value (n+1)) := by
  induction n with
  | zero => cases s <;> decide
  | succ n ih => simpa [s.value_step, Nat.Coprime, Nat.gcd_comm] using ih.symm

theorem supportBounds (s : HosoyaNeighbor) : FibonacciSupportBounds s.value := by
  constructor
  · intro n
    have hf := Nat.fib_mono (show n ≤ n+2 by omega)
    have hf' := Nat.fib_mono (show n+2 ≤ n+2+2 by omega)
    refine (two_pow_le_lucasFibonacciSum_sq n).trans (Nat.pow_le_pow_left ?_ 2)
    cases s <;> simp only [value, lowerNeighborAtAddTwo, lucasFibonacciSum] <;> omega
  · exact s.value_upper
  · intro m i j _ hm hj
    cases j with
    | zero => simp
    | succ j =>
      rw [show i+(j+1)=i+j+1 by omega,s.value_add] at hj
      have he := (Nat.dvd_add_iff_right (dvd_mul_of_dvd_right hm (Nat.fib j))).mpr hj
      exact Nat.Coprime.dvd_of_dvd_mul_right ((s.consecutive_coprime i).of_dvd_left hm) he

open Filter
open scoped Topology Classical

private theorem large_primeFactor_count {a N : ℕ} (hN : 1 < N) (ha : 0 < a) :
    (((a.primeFactors.filter (N < ·)).card : ℝ) * Real.log N) ≤ Real.log a := by
  let S := a.primeFactors.filter (N < ·)
  have small : N^S.card ≤ S.prod id := by
    simpa only [prod_const] using (prod_le_prod' (s:=S) (f:=fun _ => N) (g:=id)
      (fun p hp => (mem_filter.mp hp).2.le))
  have big := (prod_dvd_prod_of_subset S a.primeFactors id (filter_subset ..)).trans (Nat.prod_primeFactors_dvd a)
  have h := small.trans (Nat.le_of_dvd ha big)
  have logbound := Real.log_le_log (by positivity : (0:ℝ) < (N:ℝ)^S.card) (by exact_mod_cast h : (N:ℝ)^S.card ≤ a)
  simpa only [Real.log_pow] using logbound

private theorem primeCounting_ratio : Tendsto (fun N : ℕ => (N.primeCounting : ℝ)/N) atTop (𝓝 0) := by
  have hπ := tendsto_natCast_atTop_atTop (R:=ℝ) |>.eventually (Chebyshev.eventually_primeCounting_le (ε:=1) (by norm_num))
  have hl := tendsto_const_nhds (x:=Real.log 4+1) |>.div_atTop (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ)))
  refine squeeze_zero' (Eventually.of_forall fun _ => by positivity) ?_ hl
  filter_upwards [hπ,eventually_gt_atTop 1] with N hN hgt
  have hn : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  rw [div_le_iff₀ hn]
  simpa only [Function.comp_apply,Nat.floor_natCast,mul_div_assoc,div_mul_eq_mul_div,mul_comm,mul_left_comm,mul_assoc] using hN

/-- The shift determinants exclude a sublinear number of primes at these radii. -/
theorem sparse_shift_primes (H : ℕ → ℕ)
    (hh : Tendsto (fun N : ℕ => (H N : ℝ)^2/(N*Real.log N)) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => ((shiftDetProduct (H N)).primeFactors.card : ℝ)/N) atTop (𝓝 0) := by
  let B (N : ℕ) := shiftDetProduct (H N)
  let S (N : ℕ) := (B N).primeFactors.filter (N < ·)
  have hing : Tendsto (fun N : ℕ => (1:ℝ)/(N*Real.log N)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_mul_atTop₀
      (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))))
  have hlim : Tendsto (fun N : ℕ => (N.primeCounting:ℝ)/N +
      (100*Real.log 2)*((H N : ℝ)^2/(N*Real.log N)+1/(N*Real.log N))) atTop (𝓝 0) := by
    simpa using primeCounting_ratio.add ((hh.add hing).const_mul (100*Real.log 2))
  refine squeeze_zero' (Eventually.of_forall fun _ => by positivity) ?_ hlim
  filter_upwards [eventually_gt_atTop 1] with N hN
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hl : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have hw := large_primeFactor_count hN (shiftDetProduct_pos (H N))
  change (S N).card * Real.log N ≤ Real.log (B N) at hw
  have he : (B N:ℝ) ≤ 2^((H N+1)*(4*(H N+10))) := by exact_mod_cast shiftDetProduct_le (H N)
  have hb := Real.log_le_log (by exact_mod_cast shiftDetProduct_pos (H N) : (0:ℝ)<B N) he
  rw [Real.log_pow] at hb
  push_cast at hb
  have hexp : ((H N:ℝ)+1)*(4*((H N:ℝ)+10)) ≤ 100*((H N:ℝ)^2+1) := by
    nlinarith [sq_nonneg ((H N:ℝ)-1)]
  have htail := le_trans (hw.trans hb) (mul_le_mul_of_nonneg_right hexp (Real.log_nonneg (by norm_num)))
  have hs : (B N).primeFactors ⊆ N.primesLE ∪ S N := by
    intro p hp
    by_cases h : N < p
    · exact mem_union_right _ (mem_filter.mpr ⟨hp,h⟩)
    · exact mem_union_left _ (Nat.mem_primesLE.mpr ⟨by omega,Nat.prime_of_mem_primeFactors hp⟩)
  have hc : ((B N).primeFactors.card : ℝ) ≤ N.primeCounting+(S N).card := by
    exact_mod_cast (card_le_card hs).trans ((card_union_le ..).trans_eq (by rw [Nat.primesLE_card_eq_primeCounting]))
  have h := mul_le_mul_of_nonneg_right hc hl.le
  change ((B N).primeFactors.card : ℝ)/N ≤ _
  field_simp [hn.ne',hl.ne']
  nlinarith only [htail,h]

/-- A prime divisor exclusive to this site on both diagonals within H steps. -/
def HasIsolatedPrime (s : HosoyaNeighbor) (n H Y : ℕ) : Prop :=
  ∃ p, p.Prime ∧ Y < p ∧ p ∣ s.value n ∧
    ∀ t m, s ≠ t ∨ n ≠ m → Nat.dist n m ≤ H → ¬p ∣ value t m

private theorem support_of_no_isolated {s : HosoyaNeighbor} {n H Y : ℕ}
    (hn : ¬HasIsolatedPrime s n H Y) :
    (s.value n).primeFactors ⊆ Y.primesLE ∪ (shiftDetProduct H).primeFactors := by
  classical
  intro p hp
  have pp := Nat.prime_of_mem_primeFactors hp
  have dv := Nat.dvd_of_mem_primeFactors hp
  by_cases hy : Y < p
  · apply mem_union_right
    apply Nat.mem_primeFactors.mpr
    refine ⟨pp,?_,(shiftDetProduct_pos H).ne'⟩
    by_contra h
    exact hn ⟨p,pp,hy,dv,fun t m hd hh hm => h (dvd_shiftDetProduct_of_shared hd hh dv hm)⟩
  · exact mem_union_left _ (Nat.mem_primesLE.mpr ⟨by omega,pp⟩)

/-- On any positive-step progression, almost every parameter up to N has
an isolated prime on each diagonal, simultaneously, for the indicated radius and cutoff. -/
theorem almost_all_isolated_primes (r d : ℕ) (hd : 0 < d) (H Y : ℕ → ℕ)
    (hh : Tendsto (fun N : ℕ => (H N : ℝ)^2/(N*Real.log N)) atTop (𝓝 0))
    (hy : Tendsto (fun N : ℕ => ((Y N).primeCounting : ℝ)/N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (Nat.count (fun n => ¬∀ s : HosoyaNeighbor,
      HasIsolatedPrime s (r+d*n) (H N) (Y N)) N : ℝ)/N) atTop (𝓝 0) := by
  classical
  let P (N : ℕ) := (Y N).primesLE ∪ (shiftDetProduct (H N)).primeFactors
  have hs : Tendsto (fun N : ℕ => ((P N).card : ℝ)/N) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun _ => by positivity) ?_ (by simpa using hy.add (sparse_shift_primes H hh))
    apply Eventually.of_forall
    intro N
    rw [←add_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast (card_union_le ..).trans_eq (by rw [Nat.primesLE_card_eq_primeCounting])
  let S (s : HosoyaNeighbor) (N : ℕ) :=
    (range N).filter fun n => (s.value (r+d*n)).primeFactors ⊆ P N
  have hlim (s : HosoyaNeighbor) : Tendsto (fun N : ℕ => ((S s N).card : ℝ)/N) atTop (𝓝 0) :=
    s.supportBounds.sparse_support r d hd P hs
  refine squeeze_zero' (Eventually.of_forall fun _ => by positivity) ?_
    (by simpa using (hlim .upper).add (hlim .lower))
  apply Eventually.of_forall
  intro N
  rw [←add_div,Nat.count_eq_card_filter_range]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have incl : ((range N).filter fun n => ¬∀ s : HosoyaNeighbor, HasIsolatedPrime s (r+d*n) (H N) (Y N)) ⊆
      S .upper N ∪ S .lower N := by
    intro n hn
    obtain ⟨hr,h⟩ := mem_filter.mp hn
    obtain ⟨s,hbad⟩ := not_forall.mp h
    have hm : n ∈ S s N := mem_filter.mpr ⟨hr,support_of_no_isolated hbad⟩
    cases s
    · exact mem_union_left _ hm
    · exact mem_union_right _ hm
  exact_mod_cast (card_le_card incl).trans (card_union_le ..)


private lemma maximal_cutoff_ratio (A : ℕ → ℕ) (v w : ℕ → ℝ)
    (hv : ∀ a, 0 ≤ v a) (hm : Monotone v) (hw : ∀ a, 0 ≤ w a)
    (hpos : ∀ a, 1 < a → 0 < w a) (hmono : ∀ a b, 1 < a → a ≤ b → w a ≤ w b)
    (hwlim : Tendsto w atTop atTop) (ha : Tendsto (fun n => v (A n)/w n) atTop (𝓝 0)) :
    Tendsto (fun N => v ((range N).sup A)/w N) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨L,hL⟩ := eventually_atTop.mp (ha.eventually_lt_const hε)
  let D := (range (max 2 L + 1)).sup A
  have hc := (tendsto_const_nhds (x:=v D)).div_atTop hwlim
  filter_upwards [eventually_gt_atTop 1,hc.eventually_lt_const hε] with N hN hD
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (div_nonneg (hv _) (hw _))]
  obtain ⟨j,hj,he⟩ := exists_mem_eq_sup (range N) (by exact ⟨0,mem_range.mpr (by omega)⟩) A
  rw [he]
  by_cases h : j ≤ max 2 L
  · exact lt_of_le_of_lt (div_le_div_of_nonneg_right (hm (le_sup (f:=A) (mem_range.mpr (by omega)))) (hw _)) hD
  · have h₁ : 1 < j := by omega
    exact (div_le_div_of_nonneg_left (hv _) (hpos _ h₁) (hmono j N h₁ (mem_range.mp hj).le)).trans_lt
      (hL j (by omega))

private lemma isolated_mono {s : HosoyaNeighbor} {n h H y Y : ℕ} (hh : h ≤ H) (hy : y ≤ Y)
    (hit : HasIsolatedPrime s n H Y) : HasIsolatedPrime s n h y := by
  obtain ⟨p,hp,hY,hd,ex⟩ := hit
  exact ⟨p,hp,hy.trans_lt hY,hd,fun t m hne hm => ex t m hne (hm.trans hh)⟩

/-- The density-one conclusion also holds with both cutoffs evaluated at the
individual parameter. Neither cutoff needs to be monotone. -/
theorem isolated_primes_at_moving_cutoffs (r d : ℕ) (hd : 0 < d) (H Y : ℕ → ℕ)
    (hh : Tendsto (fun n : ℕ => (H n : ℝ)^2/(n*Real.log n)) atTop (𝓝 0))
    (hy : Tendsto (fun n : ℕ => ((Y n).primeCounting : ℝ)/n) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (Nat.count (fun n => ¬∀ s : HosoyaNeighbor,
      HasIsolatedPrime s (r+d*n) (H n) (Y n)) N : ℝ)/N) atTop (𝓝 0) := by
  let hmax N := (range N).sup H
  let ymax N := (range N).sup Y
  have hhn : Tendsto (fun n : ℕ => (hmax n : ℝ)^2/(n*Real.log n)) atTop (𝓝 0) := by
    apply maximal_cutoff_ratio H (fun t => (t:ℝ)^2) (fun n => n*Real.log n) (fun _ => by positivity)
      (fun _ _ h => by dsimp only; exact_mod_cast Nat.pow_le_pow_left h 2) _ _ _ _ hh
    · intro a
      exact mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
    · intro a ha
      exact mul_pos (by exact_mod_cast (by omega : 0 < a)) (Real.log_pos (by exact_mod_cast ha))
    · intro a b ha hab
      exact mul_le_mul (by exact_mod_cast hab) (Real.log_le_log (by exact_mod_cast (by omega : 0<a)) (by exact_mod_cast hab))
        (Real.log_natCast_nonneg _) (by positivity)
    · exact tendsto_natCast_atTop_atTop.atTop_mul_atTop₀ (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ)))
  have hyn : Tendsto (fun n : ℕ => ((ymax n).primeCounting : ℝ)/n) atTop (𝓝 0) :=
    maximal_cutoff_ratio Y (fun a => (a.primeCounting:ℝ)) (fun n => n) (fun _ => by positivity)
      (fun _ _ h => by dsimp only; exact_mod_cast Nat.monotone_primeCounting h) (fun _ => by positivity)
      (fun a ha => by exact_mod_cast (show 0 < a by omega)) (fun _ _ _ hab => by exact_mod_cast hab)
      tendsto_natCast_atTop_atTop hy
  refine squeeze_zero' (Eventually.of_forall fun _ => by positivity) ?_ (almost_all_isolated_primes r d hd hmax ymax hhn hyn)
  apply Eventually.of_forall
  intro N
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [Nat.count_eq_card_filter_range,Nat.count_eq_card_filter_range]
  norm_cast
  apply card_le_card
  intro n hn
  obtain ⟨hr,h⟩ := mem_filter.mp hn
  exact mem_filter.mpr ⟨hr,fun good => h fun s => isolated_mono (le_sup (f:=H) hr) (le_sup (f:=Y) hr) (good s)⟩

/-- At almost every parameter, each diagonal has a prime exceeding e(n)n log n
which divides no other site within f(n)√(n log n) steps, for arbitrary e,f tending to zero. -/
theorem isolated_primes_on_both_diagonals (r d : ℕ) (hd : 0 < d) (e f : ℕ → ℝ)
    (he : Tendsto e atTop (𝓝 0)) (hf : Tendsto f atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (Nat.count (fun n => ¬∀ s : HosoyaNeighbor,
      HasIsolatedPrime s (r+d*n) ⌊f n * Real.sqrt (n*Real.log n)⌋₊ ⌊e n*n*Real.log n⌋₊) N : ℝ)/N)
        atTop (𝓝 0) := by
  apply isolated_primes_at_moving_cutoffs r d hd _ _ _ (prime_count_threshold e he)
  refine squeeze_zero' (Eventually.of_forall fun n => div_nonneg (sq_nonneg _)
    (mul_nonneg (Nat.cast_nonneg n) (Real.log_natCast_nonneg n))) ?_ (by simpa using hf.pow 2)
  filter_upwards [eventually_gt_atTop 1] with n hn
  have h : (0:ℝ) < n*Real.log n :=
    mul_pos (by exact_mod_cast (show 0<n by omega)) (Real.log_pos (by exact_mod_cast hn))
  rw [div_le_iff₀ h]
  by_cases hfn : 0 ≤ f n
  · have bound := Nat.floor_le (mul_nonneg hfn (Real.sqrt_nonneg (n*Real.log n)))
    exact (pow_le_pow_left₀ (by positivity) bound 2).trans_eq (by rw [mul_pow,Real.sq_sqrt h.le])
  · have hz := Nat.floor_of_nonpos (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hfn) (Real.sqrt_nonneg (n*Real.log n)))
    rw [hz]
    simpa only [Nat.cast_zero,zero_pow (by decide : 2 ≠ 0)] using mul_nonneg (sq_nonneg (f n)) h.le



end HosoyaNeighbor
#print axioms HosoyaNeighbor.sparse_shift_primes
#print axioms HosoyaNeighbor.almost_all_isolated_primes
#print axioms HosoyaNeighbor.isolated_primes_at_moving_cutoffs
#print axioms HosoyaNeighbor.isolated_primes_on_both_diagonals
#print axioms HosoyaNeighbor.dvd_shiftDetProduct_of_shared
#print axioms HosoyaNeighbor.shiftDetProduct_pos
#print axioms HosoyaNeighbor.shiftDetProduct_le
#print axioms HosoyaNeighbor.supportBounds
#print axioms HosoyaNeighbor.shiftDet_pos
#print axioms HosoyaNeighbor.dvd_shiftDet_of_dvd

end Arxiv.«2211.10788»
