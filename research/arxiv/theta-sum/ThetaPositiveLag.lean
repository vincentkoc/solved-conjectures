import ThetaSlidingCorrelation

/-! The off-diagonal term of the finite sliding-window bound measures
positive signed correlations at nonzero displacements. -/
namespace Arxiv.«2501.03234».ThetaPositiveLag
open Finset ThetaSlidingCorrelation
noncomputable section

def offsets (L : ℕ) := (range L).erase 0

def mass (N q L : ℕ) (f : ℕ → ℝ) := ∑ k∈offsets L,max 0 (lag N (q*k) f)
def energy (N q L : ℕ) (f : ℕ → ℝ) := ∑ k∈offsets L,(lag N (q*k) f)^2

private theorem image_le (s t : Finset ℕ) (u : ℕ → ℕ) (g : ℕ → ℝ)
    (hg : ∀ k,0≤g k) (hm : ∀ j∈s,u j∈t)
    (hi : ∀ a∈s,∀ b∈s,u a=u b → a=b) : (∑ j∈s,g (u j))≤∑ k∈t,g k := by
  rw [←sum_image (g:=u) (f:=g) hi]
  exact sum_le_sum_of_subset_of_nonneg (fun k hk => by
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hk
    exact hm j hj) (fun k _ _ => hg k)

private theorem one_side (i L : ℕ) (g : ℕ → ℝ) (hg : ∀ k,0≤g k) (_hi : i<L) :
    (∑ j∈(range L).filter (fun j => i<j),g (j-i))≤∑ k∈offsets L,g k := by
  apply image_le _ _ (fun j => j-i) g hg
  · intro j hj
    obtain ⟨hj,hij⟩ := mem_filter.mp hj
    exact mem_erase.mpr ⟨by omega,mem_range.mpr (by have := mem_range.mp hj;omega)⟩
  · intro a ha b hb he
    obtain ⟨_,h₁⟩ := mem_filter.mp ha
    obtain ⟨_,h₂⟩ := mem_filter.mp hb
    omega

private theorem other_side (i L : ℕ) (g : ℕ → ℝ) (hg : ∀ k,0≤g k) (hi : i<L) :
    (∑ j∈(range L).filter (fun j => j < i),g (i-j))≤∑ k∈offsets L,g k := by
  apply image_le _ _ (fun j => i-j) g hg
  · intro j hj
    obtain ⟨hj,hji⟩ := mem_filter.mp hj
    exact mem_erase.mpr ⟨by omega,mem_range.mpr (by omega)⟩
  · intro a ha b hb he
    obtain ⟨_,h₁⟩ := mem_filter.mp ha
    obtain ⟨_,h₂⟩ := mem_filter.mp hb
    omega

private theorem row {i L : ℕ} (hi : i<L) (a : ℕ → ℝ) :
    (∑ j∈range L,a (max i j-min i j))≤a 0+2*(∑ k∈offsets L,max 0 (a k)) := by
  classical
  let g (k : ℕ) := max 0 (a k)
  have hg (k : ℕ) : 0≤g k := le_max_left ..
  have hh (j : ℕ) : a (max i j-min i j) ≤ (if i=j then a 0 else 0)+
      (if i<j then g (j-i) else 0)+(if j < i then g (i-j) else 0) := by
    rcases lt_trichotomy i j with h|h|h
    · simp [h,h.ne,not_lt_of_ge h.le,max_eq_right h.le,min_eq_left h.le,g]
    · subst j;simp
    · simp [h,h.ne.symm,not_lt_of_ge h.le,max_eq_left h.le,min_eq_right h.le,g]
  have h := sum_le_sum (s:=range L) (fun j _ => hh j)
  simp only [sum_add_distrib,←sum_filter] at h
  have eqn : (∑ j∈(range L).filter (fun j => i=j),a 0)=a 0 := by
    rw [show (range L).filter (fun j => i=j)={i} by ext j;simp;omega,sum_singleton]
  rw [eqn] at h
  exact h.trans (by linarith only [one_side i L g hg hi,other_side i L g hg hi])

theorem positive {N q L : ℕ} (hL : 0<L) (f v : ℕ → ℝ) (hf : ∀ n≥N,f n=0) (hv : ∀ n,|v n|≤1)
    (hper : ∀ n j,v (n+q*j)=v n) :
    L*(∑ n∈range N,v n*f n)^2≤(N+q*L:ℕ)*(lag N 0 f+2*mass N q L f) := by
  have hh := bound (L:=L) f v hf hv hper
  have hsum := sum_le_sum (s:=range L) (fun i hi => row (mem_range.mp hi) (fun k => lag N (q*k) f))
  simp only [sum_const,nsmul_eq_mul,card_range,mul_zero] at hsum
  have hb := hh.trans (mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _))
  apply (mul_le_mul_iff_right₀ (Nat.cast_pos.mpr hL : (0:ℝ)<L)).mp
  dsimp only [mass]
  nlinarith only [hb]

theorem square (N q L : ℕ) (f : ℕ → ℝ) : (mass N q L f)^2≤L*energy N q L f := by
  let g (k : ℕ) := max 0 (lag N (q*k) f)
  have h := sum_mul_sq_le_sq_mul_sq (offsets L) (fun _ => (1:ℝ)) g
  simp only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one] at h
  have hs : (∑ k∈offsets L,g k^2)≤energy N q L f := by
    apply sum_le_sum;intro k _
    by_cases h : 0≤lag N (q*k) f
    · simp [g,max_eq_right h]
    · simpa [g,max_eq_left (le_of_not_ge h)] using sq_nonneg (lag N (q*k) f)
  have hc : (offsets L).card≤L := (card_le_card (erase_subset ..)).trans (by simp)
  exact h.trans (mul_le_mul (Nat.cast_le.mpr hc) hs (sum_nonneg fun _ _ => sq_nonneg _) (Nat.cast_nonneg _))

#print axioms positive
#print axioms square
end
end Arxiv.«2501.03234».ThetaPositiveLag
