import ThetaConditionalRows
import ThetaIdentityRow

/-! A progression sees a reciprocal row through the residue modulo the gcd. -/
namespace Arxiv.«2501.03234».ThetaIdentityFiber
open Finset ThetaPeriodMeans ThetaConditionalRows ThetaRowCorrelations
noncomputable section

def selectClass (r m n : ℕ) : ℝ := if n%m=r then 1 else 0

theorem selectClass_mod (r m : ℕ) : OnMod m (selectClass r m) := fun n => by simp [selectClass]

private theorem zero_out (r m d K n : ℕ) (h : ¬n.Coprime d) : selectClass r m n * row d K n=0 := by
  simp [row,wave_of_not_coprime h]

private theorem slice {r g a k : ℕ} (hg : 0<g) (hm : r<g*a) (hk : k<g) :
    ∑ i∈range a,selectClass r (g*a) (k+g*i)=if k=r%g then 1 else 0 := by
  classical
  have hi : r/g<a := (Nat.div_lt_iff_lt_mul hg).mpr (by simpa [Nat.mul_comm] using hm)
  have H (i : ℕ) (hh : i∈range a) : selectClass r (g*a) (k+g*i)=
      if k=r%g then (if i=r/g then 1 else 0) else 0 := by
    have hl := Nat.mul_le_mul_left g (show i+1≤a by exact mem_range.mp hh)
    have ht : k+g*i<g*a := by nlinarith
    have he : k+g*i=r ↔ k=r%g ∧ i=r/g := by
      constructor
      · intro eq
        have h₁ := congrArg (·%g) eq
        have h₂ := congrArg (·/g) eq
        simpa only [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hk] using
          (show (k+g*i)%g=r%g ∧ i=r/g from ⟨h₁,by simpa [Nat.add_mul_div_left _ _ hg,Nat.div_eq_of_lt hk] using h₂⟩)
      · rintro ⟨rfl,rfl⟩; exact Nat.mod_add_div ..
    simp only [selectClass,Nat.mod_eq_of_lt ht,he]
    split_ifs <;> simp_all
  rw [sum_congr rfl H]
  by_cases he : k=r%g <;> simp [he,mem_range.mpr hi]

/-- Periodic unit averages with the conditional prime normalization. -/
def residueMean (r m d P : ℕ) [NeZero P] (K : ℕ) : ℝ :=
  (m.totient:ℝ)*unitMean P (fun n => selectClass r m n * row d K n)

private theorem lifted {r m d L P : ℕ} [NeZero L] [NeZero P] (hL : L∣P) (hm : m∣L) (hd : d∣L) (K : ℕ) :
    residueMean r m d P K=residueMean r m d L K := by
  unfold residueMean
  rw [unitMean_lift hL (show OnMod L _ from fun n => congrArg₂ (·*·)
    (onMod_lift hm (selectClass_mod r m) n) (onMod_lift hd (row_onMod d K) n))]

private theorem exact_slice {r g a s : ℕ} (hg : 0<g) (ha : 0<a) (hs : 0<s)
    (hm : r<g*a) (hcop : r.Coprime (g*a)) (hc : a.Coprime s) (K : ℕ) :
    letI : NeZero (g*(a*s)) := ⟨(by positivity : 0<g*(a*s)).ne'⟩
    residueMean r (g*a) (g*s) (g*(a*s)) K=
      ((g*a).totient:ℝ)/(g*(a*s)).totient*∑ i∈range s,row (g*s) K (r%g+g*i) := by
  let L := g*(a*s)
  have hL : 0<L := by dsimp only [L]; positivity
  have hr := mean_fiber_product hg ha hs hc (selectClass_mod r (g*a)) (row_onMod (g*s) K)
  have he (k : ℕ) (hk : k∈range g) :
      (∑ i∈range a,selectClass r (g*a) (k+g*i))*(∑ j∈range s,row (g*s) K (k+g*j)) =
      if k=r%g then ∑ j∈range s,row (g*s) K (k+g*j) else 0 := by
    rw [slice hg hm (mem_range.mp hk),ite_mul,one_mul,zero_mul]
  rw [sum_congr rfl he,sum_ite_eq',if_pos (mem_range.mpr (Nat.mod_lt _ hg))] at hr
  have hz (n : ℕ) : (if n.Coprime L then selectClass r (g*a) n*row (g*s) K n else 0)=selectClass r (g*a) n*row (g*s) K n := by
    split_ifs with h
    · rfl
    by_cases he : n%(g*a)=r
    · have hh : n.Coprime (g*a) := by
        change n.gcd (g*a)=1
        rw [Nat.gcd_comm,Nat.gcd_rec,he]; exact hcop
      have hd : ¬n.Coprime (g*s) := by
        intro hh'
        apply h
        change n.Coprime (g*(a*s))
        rw [←Nat.mul_assoc]
        exact hh.mul_right (hh'.coprime_dvd_right (dvd_mul_left s g))
      exact (zero_out _ _ _ _ _ hd).symm
    · simp [selectClass,he]
  rw [residueMean,unitMean_mean]
  change (g*a).totient*(((L:ℝ)/L.totient)*mean L _) = _
  change (g*a).totient*(((L:ℝ)/L.totient)*mean L (fun n => if n.Coprime L then selectClass r (g*a) n*row (g*s) K n else 0)) = _
  simp_rw [hz]
  rw [show L=g*(a*s) from rfl,hr]
  push_cast
  field_simp

/-- At a fixed modulus and row the conditional mean depends only on the
residue class modulo the gcd of the two moduli. -/
theorem residue_congr {r u m d P : ℕ} [NeZero P] (hm : 1 < m)
    (hr : r < m) (hu : u < m) (hrc : r.Coprime m) (huc : u.Coprime m)
    (hmod : r ≡ u [MOD m.gcd d]) (hd : 1 < d) (hmP : m∣P) (hdP : d∣P) (K : ℕ) :
    residueMean r m d P K = residueMean u m d P K := by
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
  have he (x : ℕ) (hx : x < m) (hxc : x.Coprime m) :
      residueMean x m d P K = ((m.totient:ℝ)/L.totient)*∑ i∈range s,row d K (x%g+g*i) := by
    rw [lifted (L:=L) (heL.symm ▸ Nat.lcm_dvd hmP hdP) (heL.symm ▸ Nat.dvd_lcm_left ..) (heL.symm ▸ Nat.dvd_lcm_right ..)]
    have h := exact_slice hg ha hs (hma.symm ▸ hx) (hma.symm ▸ hxc) hc K
    change residueMean x (g*a) (g*s) L K = _ at h
    simpa only [hma,hds] using h
  rw [he r hr hrc,he u hu huc,show r%g=u%g from hmod]

theorem residue_bound {r m d P : ℕ} [NeZero P] (hm : 1 < m) (hr : r < m) (hcop : r.Coprime m) (hd : 1 < d) (hmP : m∣P) (hdP : d∣P) (K : ℕ) :
    |residueMean r m d P K| ≤ 3*(harmonic d:ℝ)*(d/(m.gcd d)).divisors.card/(d/(m.gcd d)).totient := by
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
  have h := exact_slice hg ha hs (hma.symm ▸ hr) (hma.symm ▸ hcop) hc K
  change residueMean r (g*a) (g*s) L K=_ at h
  rw [hma,hds] at h
  rw [lifted (L:=L) (heL.symm ▸ Nat.lcm_dvd hmP hdP) (heL.symm ▸ Nat.dvd_lcm_left ..) (heL.symm ▸ Nat.dvd_lcm_right ..),h,abs_mul]
  have hratio : ((m.totient:ℝ)/L.totient)*s.totient ≤ 1 := by
    have he : L=m*s := by dsimp only [L]; rw [←Nat.mul_assoc,hma]
    have hf := Nat.totient_super_multiplicative m s
    rw [←he] at hf
    have hp : 0<(L.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos L)
    rw [div_mul_eq_mul_div,div_le_one hp]; exact_mod_cast hf
  have hf := row_fiber hg hs (hds.symm ▸ hd) (Nat.mod_lt r hg) K
  rw [hds] at hf
  have ht : 0<(s.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hs
  rw [abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
  change _ ≤ 3*(harmonic d:ℝ)*s.divisors.card/s.totient
  apply (le_div_iff₀ ht).mpr
  calc _ = (((m.totient:ℝ)/L.totient)*s.totient)*|∑ i∈range s,row d K (r%g+g*i)| := by ring
       _ ≤ 1*(3*((harmonic d:ℝ)*s.divisors.card)) := mul_le_mul hratio hf (abs_nonneg _) (by norm_num)
       _ = _ := by ring

theorem residue_captured {r m d P : ℕ} [NeZero P] (hm : 1 < m) (hr : r < m) (hcop : r.Coprime m) (hd : 1 < d) (hmP : m∣P) (hdm : d∣m) (K : ℕ) :
    residueMean r m d P K=row d K r := by
  let a := m/d
  have hm' : d*a=m := Nat.mul_div_cancel' hdm
  have ha : 0<a := Nat.div_pos (Nat.le_of_dvd (by omega) hdm) (by omega)
  let : NeZero m := ⟨by omega⟩
  have H := exact_slice (g:=d) (a:=a) (s:=1) (by omega) ha (by decide) (hm'.symm ▸ hr) (hm'.symm ▸ hcop) (Nat.coprime_one_right _) K
  simp only [Nat.mul_one,sum_range_one,Nat.mul_zero,Nat.add_zero,row_onMod d K r,hm'] at H
  rw [lifted hmP (dvd_refl _) hdm,H,div_self (by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos m)).ne'),one_mul]

def select (m n : ℕ) : ℝ := if n%m=1 then 1 else 0

theorem select_mod (m : ℕ) : OnMod m (select m) := fun n => by simp [select]

/-- Periodic unit averages with the conditional prime normalization. -/
def rowMean (m d P : ℕ) [NeZero P] (K : ℕ) : ℝ :=
  (m.totient:ℝ)*unitMean P (fun n => select m n * row d K n)

theorem bound {m d P : ℕ} [NeZero P] (hm : 1 < m) (hd : 1 < d) (hmP : m∣P) (hdP : d∣P) (K : ℕ) :
    |rowMean m d P K| ≤ 3*(harmonic d:ℝ)*(d/(m.gcd d)).divisors.card/(d/(m.gcd d)).totient :=
  residue_bound hm hm (Nat.coprime_one_left _) hd hmP hdP K

theorem captured {m d P : ℕ} [NeZero P] (hm : 1 < m) (hd : 1 < d) (hmP : m∣P) (hdm : d∣m) (K : ℕ) :
    rowMean m d P K=row d K 1 :=
  residue_captured hm hm (Nat.coprime_one_left _) hd hmP hdm K

#print axioms residue_congr
#print axioms residue_bound
#print axioms residue_captured
#print axioms captured
#print axioms bound
end
end Arxiv.«2501.03234».ThetaIdentityFiber
