import HosoyaPrimePowerLayers

/-! The logarithmic size contributed by a varying set of prime factors. -/

namespace Arxiv.«2211.10788».FactorMass

open Finset Real

/-- Logarithm of the S-part, retaining the full multiplicity of each prime. -/
noncomputable def logPart (S : Finset ℕ) (n : ℕ) :=
  ∑ p∈S, (n.factorization p:ℝ)*log p

theorem logPart_nonneg (S : Finset ℕ) (n : ℕ) : 0≤logPart S n :=
  sum_nonneg fun p _ => mul_nonneg (Nat.cast_nonneg _) (log_natCast_nonneg p)

theorem logPart_le (S : Finset ℕ) (n : ℕ) : logPart S n≤log n := by
  classical
  rw [log_nat_eq_sum_factorization n]
  change (∑ p∈S, (n.factorization p:ℝ)*log p) ≤ ∑ p∈n.primeFactors, (n.factorization p:ℝ)*log p
  rw [←sum_subset (inter_subset_left (s₁:=S) (s₂:=n.primeFactors)) (by
    intro p mem no
    have miss : p∉n.factorization.support := fun h => no (mem_inter.mpr ⟨mem,h⟩)
    simp [Finsupp.notMem_support_iff.mp miss])]
  exact sum_le_sum_of_subset_of_nonneg inter_subset_right
    (fun p _ _ => mul_nonneg (Nat.cast_nonneg _) (log_natCast_nonneg _))

/-- The sum of the logarithms of the S-parts in any interval. The first term
allows one maximal prime power per member of S, and the second pays for
all its repeated levels through the Fibonacci gap factors. -/
theorem interval_logPart {f : ℕ → ℕ} (bnd : FibonacciSupportBounds f)
    (T S : Finset ℕ) {r d a L : ℕ} (hd : 0<d) (inside : T⊆Ico a (a+L)) :
    ∑ t∈T, logPart S (f (r+d*t)) ≤
      (((r+d*(a+L)+3:ℕ):ℝ)*S.card+(d:ℝ)*L^2)*log 2 := by
  classical
  let u (t) := f (r+d*t)
  let g (j) := Nat.fib (d*j)
  let E := r+d*(a+L)+3
  have l₂ := log_pos (by norm_num : (1:ℝ)<2)
  rcases T.eq_empty_or_nonempty with rfl|nt
  · simp only [sum_empty];positivity
  have bounded (t) (mem : t∈T) : log (u t)≤(E:ℝ)*log 2 := by
    have hi := (mem_Ico.mp (inside mem)).2.le
    have ub : u t ≤ 2^E := (bnd.upper _).trans (Nat.pow_le_pow_right (by decide)
      (by dsimp [E];gcongr))
    have nz : 0<u t := by
      have h := bnd.lower (r+d*t)
      by_contra! zz
      change u t^2 ≥ _ at h
      simp [Nat.eq_zero_of_le_zero zz] at h
    simpa only [Nat.cast_pow,Nat.cast_ofNat,log_pow] using
      log_le_log (by exact_mod_cast nz : 0<(u t:ℝ)) (by exact_mod_cast ub : (u t:ℝ)≤(2^E:ℕ))
  have per (p : ℕ) :
      ∑ t∈T, ((u t).factorization p:ℝ)*log p ≤
      (E:ℝ)*log 2 + ∑ j∈Ico 1 L, ((g j).factorization p:ℝ)*log p := by
    obtain ⟨t,ht,cap⟩ := exists_max_image T (fun t => (u t).factorization p) nt
    have w := window_orders bnd T hd inside cap
    have wr : (∑ i∈T, ((u i).factorization p:ℝ)) ≤ ((u t).factorization p:ℝ)+∑ j∈Ico 1 L, ((g j).factorization p:ℝ) := by exact_mod_cast w
    have one : ((u t).factorization p:ℝ)*log p≤(E:ℝ)*log 2 := by
      have l := logPart_le {p} (u t)
      simpa only [logPart,sum_singleton] using l.trans (bounded t ht)
    rw [←sum_mul,←sum_mul]
    grw [wr,add_mul,one]
  have gx (j) (mem : j∈Ico 1 L) : logPart S (g j) ≤ (d:ℝ)*L*log 2 := by
    have pos := Nat.fib_pos.mpr (Nat.mul_pos hd (mem_Ico.mp mem).1)
    have ub : g j≤2^(d*L) := (fib_le_two_pow _).trans
      (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left d (mem_Ico.mp mem).2.le))
    have l := (logPart_le S (g j)).trans (log_le_log
      (by exact_mod_cast pos : 0<(g j:ℝ)) (by exact_mod_cast ub : (g j:ℝ)≤(2^(d*L):ℕ)))
    simpa only [Nat.cast_pow,Nat.cast_ofNat,log_pow,Nat.cast_mul] using l
  change (∑ t∈T, ∑ p∈S, ((u t).factorization p:ℝ)*log p)≤_
  rw [sum_comm]
  have total := sum_le_sum (s:=S) fun p _ => per p
  rw [sum_add_distrib,sum_comm (s:=S) (t:=Ico 1 L)] at total
  have gsum := sum_le_sum gx
  have length : (((Ico 1 L).card:ℕ):ℝ)≤L := by exact_mod_cast (by simp : (Ico 1 L).card≤L)
  simp only [sum_const,nsmul_eq_mul] at total gsum
  have gd : (∑ j∈Ico 1 L, logPart S (g j)) ≤ (L:ℝ)*(d*L*log 2) := gsum.trans
    (mul_le_mul_of_nonneg_right length (by positivity))
  change _ ≤ (S.card:ℝ)*(E*log 2)+∑ j∈Ico 1 L, logPart S (g j) at total
  change _ ≤ ((E:ℝ)*S.card+d*L^2)*log 2
  linarith only [total,gd,show (S.card:ℝ)*(E*log 2)+(L:ℝ)*(d*L*log 2)=((E:ℝ)*S.card+d*L^2)*log 2 by ring]

#print axioms logPart_nonneg
#print axioms logPart_le
#print axioms interval_logPart

end Arxiv.«2211.10788».FactorMass
