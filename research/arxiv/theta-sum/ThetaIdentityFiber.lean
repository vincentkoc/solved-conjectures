import ThetaConditionalRows
import ThetaIdentityRow

/-! A progression sees a reciprocal row through the residue modulo the gcd. -/
namespace Arxiv.«2501.03234».ThetaIdentityFiber
open Finset ThetaPeriodMeans ThetaConditionalRows ThetaRowCorrelations
noncomputable section

def select (m n : ℕ) : ℝ := if n%m=1 then 1 else 0

theorem select_mod (m : ℕ) : OnMod m (select m) := fun n => by simp [select]

private theorem zero_out (m d K n : ℕ) (h : ¬n.Coprime d) : select m n * row d K n=0 := by
  simp [row,wave_of_not_coprime h]

private theorem slice {g a k : ℕ} (hg : 0<g) (hm : 1<g*a) (hk : k<g) :
    ∑ i∈range a,select (g*a) (k+g*i)=if k=1%g then 1 else 0 := by
  classical
  have hi : 1/g<a := (Nat.div_lt_iff_lt_mul hg).mpr (by simpa [Nat.mul_comm] using hm)
  have H (i : ℕ) (hh : i∈range a) : select (g*a) (k+g*i)=
      if k=1%g then (if i=1/g then 1 else 0) else 0 := by
    have hl := Nat.mul_le_mul_left g (show i+1≤a by exact mem_range.mp hh)
    have ht : k+g*i<g*a := by nlinarith
    have he : k+g*i=1 ↔ k=1%g ∧ i=1/g := by
      constructor
      · intro eq
        have h₁ := congrArg (·%g) eq
        have h₂ := congrArg (·/g) eq
        simpa only [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hk] using
          (show (k+g*i)%g=1%g ∧ i=1/g from ⟨h₁,by simpa [Nat.add_mul_div_left _ _ hg,Nat.div_eq_of_lt hk] using h₂⟩)
      · rintro ⟨rfl,rfl⟩; exact Nat.mod_add_div ..
    simp only [select,Nat.mod_eq_of_lt ht,he]
    split_ifs <;> simp_all
  rw [sum_congr rfl H]
  by_cases he : k=1%g <;> simp [he,mem_range.mpr hi]

/-- Periodic unit averages with the conditional prime normalization. -/
def rowMean (m d P : ℕ) [NeZero P] (K : ℕ) : ℝ :=
  (m.totient:ℝ)*unitMean P (fun n => select m n * row d K n)

private theorem lifted {m d L P : ℕ} [NeZero L] [NeZero P] (hL : L∣P) (hm : m∣L) (hd : d∣L) (K : ℕ) :
    rowMean m d P K=rowMean m d L K := by
  unfold rowMean
  rw [unitMean_lift hL (show OnMod L _ from fun n => congrArg₂ (·*·)
    (onMod_lift hm (select_mod m) n) (onMod_lift hd (row_onMod d K) n))]

private theorem exact_slice {g a s : ℕ} (hg : 0<g) (ha : 0<a) (hs : 0<s)
    (hm : 1<g*a) (hc : a.Coprime s) (K : ℕ) :
    letI : NeZero (g*(a*s)) := ⟨(by positivity : 0<g*(a*s)).ne'⟩
    rowMean (g*a) (g*s) (g*(a*s)) K=
      ((g*a).totient:ℝ)/(g*(a*s)).totient*∑ i∈range s,row (g*s) K (1%g+g*i) := by
  let L := g*(a*s)
  have hL : 0<L := by dsimp only [L]; positivity
  have hr := mean_fiber_product hg ha hs hc (select_mod (g*a)) (row_onMod (g*s) K)
  have he (k : ℕ) (hk : k∈range g) :
      (∑ i∈range a,select (g*a) (k+g*i))*(∑ j∈range s,row (g*s) K (k+g*j)) =
      if k=1%g then ∑ j∈range s,row (g*s) K (k+g*j) else 0 := by
    rw [slice hg hm (mem_range.mp hk),ite_mul,one_mul,zero_mul]
  rw [sum_congr rfl he,sum_ite_eq',if_pos (mem_range.mpr (Nat.mod_lt _ hg))] at hr
  have hz (n : ℕ) : (if n.Coprime L then select (g*a) n*row (g*s) K n else 0)=select (g*a) n*row (g*s) K n := by
    split_ifs with h
    · rfl
    by_cases he : n%(g*a)=1
    · have hh : n.Coprime (g*a) := by
        change n.gcd (g*a)=1
        rw [Nat.gcd_comm,Nat.gcd_rec,he]; simp
      have hd : ¬n.Coprime (g*s) := by
        intro hh'
        apply h
        change n.Coprime (g*(a*s))
        rw [←Nat.mul_assoc]
        exact hh.mul_right (hh'.coprime_dvd_right (dvd_mul_left s g))
      exact (zero_out _ _ _ _ hd).symm
    · simp [select,he]
  rw [rowMean,unitMean_mean]
  change (g*a).totient*(((L:ℝ)/L.totient)*mean L _) = _
  change (g*a).totient*(((L:ℝ)/L.totient)*mean L (fun n => if n.Coprime L then select (g*a) n*row (g*s) K n else 0)) = _
  simp_rw [hz]
  rw [show L=g*(a*s) from rfl,hr]
  push_cast
  field_simp

theorem bound {m d P : ℕ} [NeZero P] (hm : 1 < m) (hd : 1 < d) (hmP : m∣P) (hdP : d∣P) (K : ℕ) :
    |rowMean m d P K| ≤ 3*(harmonic d:ℝ)*(d/(m.gcd d)).divisors.card/(d/(m.gcd d)).totient := by
  let g := m.gcd d
  let a := m/g
  let s := d/g
  have hg : 0<g := Nat.gcd_pos_of_pos_left _ (by omega)
  have hma : g*a=m := Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
  have hds : g*s=d := Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
  have ha : 0<a := Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left _ _)) hg
  have hs : 0<s := Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right _ _)) hg
  have hc : a.Coprime s := Nat.coprime_div_gcd_div_gcd hg
  let L := g*(a*s)
  have heL : L=m.lcm d := by
    have hh := Nat.gcd_mul_lcm m d
    change g*m.lcm d=m*d at hh
    apply Nat.eq_of_mul_eq_mul_left hg
    calc g*L=(g*a)*(g*s) := by dsimp only [L]; ring
         _ = _ := by rw [hma,hds,hh]
  let : NeZero L := ⟨(by dsimp only [L]; positivity : 0<L).ne'⟩
  have h := exact_slice hg ha hs (hma.symm ▸ hm) hc K
  change rowMean (g*a) (g*s) L K=_ at h
  rw [hma,hds] at h
  rw [lifted (L:=L) (heL.symm ▸ Nat.lcm_dvd hmP hdP) (heL.symm ▸ Nat.dvd_lcm_left ..) (heL.symm ▸ Nat.dvd_lcm_right ..),h,abs_mul]
  have hratio : ((m.totient:ℝ)/L.totient)*s.totient ≤ 1 := by
    have he : L=m*s := by dsimp only [L]; rw [←Nat.mul_assoc,hma]
    have hf := Nat.totient_super_multiplicative m s
    rw [←he] at hf
    have hp : 0<(L.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos L)
    rw [div_mul_eq_mul_div,div_le_one hp]; exact_mod_cast hf
  have hf := row_fiber hg hs (hds.symm ▸ hd) (Nat.mod_lt 1 hg) K
  rw [hds] at hf
  have ht : 0<(s.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hs
  rw [abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
  change _ ≤ 3*(harmonic d:ℝ)*s.divisors.card/s.totient
  apply (le_div_iff₀ ht).mpr
  calc _ = (((m.totient:ℝ)/L.totient)*s.totient)*|∑ i∈range s,row d K (1%g+g*i)| := by ring
       _ ≤ 1*(3*((harmonic d:ℝ)*s.divisors.card)) := mul_le_mul hratio hf (abs_nonneg _) (by norm_num)
       _ = _ := by ring

theorem captured {m d P : ℕ} [NeZero P] (hm : 1 < m) (hd : 1 < d) (hmP : m∣P) (hdm : d∣m) (K : ℕ) :
    rowMean m d P K=row d K 1 := by
  let a := m/d
  have hm' : d*a=m := Nat.mul_div_cancel' hdm
  have ha : 0<a := Nat.div_pos (Nat.le_of_dvd (by omega) hdm) (by omega)
  let : NeZero m := ⟨by omega⟩
  have H := exact_slice (g:=d) (a:=a) (s:=1) (by omega) ha (by decide) (hm'.symm ▸ hm) (Nat.coprime_one_right _) K
  simp only [Nat.mul_one,sum_range_one,Nat.mul_zero,Nat.add_zero,Nat.mod_eq_of_lt hd,hm'] at H
  rw [lifted hmP (dvd_refl _) hdm,H,div_self (by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos m)).ne'),one_mul]

#print axioms captured
#print axioms bound
end
end Arxiv.«2501.03234».ThetaIdentityFiber
