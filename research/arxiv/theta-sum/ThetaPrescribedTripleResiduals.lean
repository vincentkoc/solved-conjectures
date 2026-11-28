import ThetaCentralResidualCells

/-! Prescribed residual interval at every vertex of many disjoint ternary
representations of each eligible odd target in one fixed progression. -/
namespace Arxiv.«2501.03234».ThetaPrescribedTripleResiduals
open Real Filter Finset ThetaTernaryErrorBudget ThetaTernaryWindows ThetaTernaryPacking
open ThetaTernaryDeletion ThetaTernaryIncidence ThetaTernaryTransfer ThetaFivePrimeMoment
open ThetaLocalIntervalTests ThetaCalibratedCone ThetaClassConcentration ThetaNaturalPrimeMeans
open ThetaCentralResidualCells ThetaBoundedResidualTriples ThetaCharacterPrimeMeans
noncomputable section

def lowerScale (b : ℝ) (M : ℕ) := b*M/(M.totient:ℝ)^3
def upperScale (C : ℝ) (M : ℕ) := C*(M:ℝ)^2/(M.totient:ℝ)^5

/-- Constants are uniform in the fixed modulus. Thresholds may depend on it. -/
def OrdinaryClasses (θ b C : ℝ) : Prop := ∀ M a : ℕ,0<M → a<M → a.Coprime M →
  ∀ᶠ n : ℕ in atTop,Odd n → n%M=(3*a)%M →
    let A := cell M a (window n θ)
    lowerScale b M*((n:ℝ)^θ)^2≤((triples A A A n).card:ℝ)*(width n)^3 ∧
      (five A n:ℝ)*(width n)^5≤upperScale C M*((n:ℝ)^θ)^3

private theorem ratio {b C : ℝ} {M : ℕ} (hm : 0<M) (hC : 0<C) :
    (lowerScale b M)^2/(upperScale C M)=b^2/(C*M.totient) := by
  have hM : (0:ℝ)<M := by exact_mod_cast hm
  have hφ : (0:ℝ)<M.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  unfold lowerScale upperScale
  field_simp

theorem original {e : ℕ} (he : 32≤e) (ht : e≤48) (hk : Kernel e)
    {β θ b C : ℝ} (hβ : (e:ℝ)/64<β) (hθ : β<θ) (htop : θ<1)
    (ord : ThetaLocalPrimeCounts.Ordinary β) (hAP : ProgressionMangoldt)
    (hb : 0<b) (hC : 0<C) (hc : OrdinaryClasses θ b C)
    {q r : ℕ} (hq : 0<q) (hr : r<q) (hu : r.Coprime q)
    (y : ℝ) {d : ℝ} (hd : 0<d) (N : ℕ) :
    ∃ T≥N, q∣m T ∧ ∃ a < m T,a.Coprime (m T) ∧ a%q=r ∧
      ∀ᶠ n : ℕ in atTop,Odd n → n%(m T)=(3*a)%(m T) →
      ∃ D : Finset Triple,
        b^2*(n:ℝ)^θ/(108*C*(m T).totient*(1+log n))≤D.card ∧ separated D ∧
        ∀ t∈D,t.1+t.2.1+t.2.2=n ∧ t.1≠t.2.1 ∧ t.1≠t.2.2 ∧ t.2.1≠t.2.2 ∧
          ∀ p∈vertices t,p.Prime ∧ |(p:ℝ)-(n:ℝ)/3|≤(n:ℝ)^θ ∧ p%(m T)=a ∧
            |(S p:ℝ)/p-log p/2-y|<d := by
  let η := b^2/(144*C)
  have hη : 0<η := by dsimp [η];positivity
  obtain ⟨T,hT,hMT,a,ha,hu',har,htail⟩ := sparse he ht hk hβ hθ htop ord hAP hq hr hu y hd hη N
  let M := m T
  have hM : 0<M := ThetaCompactModulus.positive T
  have hm₁ : 0<(M:ℝ) := by exact_mod_cast hM
  have hφ : 0<(M.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hM
  let b' := lowerScale b M
  let C' := upperScale C M
  have hb' : 0<b' := by dsimp [b',lowerScale];positivity
  have hC' : 0<C' := by dsimp [C',upperScale];positivity
  have hr' : b'^2/C'=b^2/(C*M.totient) := ratio hM hC
  have ctrl : Control θ := of_power (by positivity) (hβ.trans hθ) htop (ThetaShortPrimeInterval.exceptional_for he ht hk)
  refine ⟨T,hT,hMT,a,ha,hu',har,?_⟩
  filter_upwards [htail,hc M a hM ha hu',diagonal_budget ctrl hb'] with n hE hcounts hdiag hodd hmod
  let A := cell M a (window n θ)
  let E := misses M a y d (window n θ)
  let L := width n
  let R := (n:ℝ)^θ
  have hL : 0<L := hdiag.1.1
  have hR : 0<R := hdiag.1.2
  have hexc : (E.card:ℝ)*L≤b'^2*R/(144*C') := by
    change (E.card:ℝ)*L≤η*R/M.totient at hE
    apply hE.trans_eq
    calc η*R/M.totient = (b^2/(C*M.totient))*(R/144) := by dsimp [η];ring
         _ = _ := by rw [←hr'];ring
  have hsub : A⊆window n θ := filter_subset ..
  have hdi : 3*(A.card:ℝ)*L^3≤b'*R^2/4 := by
    apply le_trans _ hdiag.2
    gcongr
  obtain ⟨hl,hm⟩ := hcounts hodd hmod
  obtain ⟨D,hD,hsep,hlo⟩ := ThetaResilientCentralTriples.original A E n hR hL hb' hC'
    hl hm hexc hdi
  refine ⟨D,?_,hsep,?_⟩
  · apply le_trans _ hlo
    apply le_of_eq
    change b^2*R/(108*C*M.totient*L)=b'^2*R/(108*C'*L)
    calc _ = (b^2/(C*M.totient))*(R/(108*L)) := by ring
         _ = _ := by rw [←hr'];ring
  intro t ht
  obtain ⟨hh,hd'⟩ := mem_filter.mp (hD ht)
  obtain ⟨h₁,h₂,h₃,hn'⟩ := mem.mp hh
  refine ⟨hn',hd'.1,hd'.2.1,hd'.2.2,?_⟩
  intro p hp
  have hmem : p∈A\E := by
    simp only [vertices,mem_insert,mem_singleton] at hp
    rcases hp with rfl|rfl|rfl;exact h₁;exact h₂;exact h₃
  obtain ⟨hw,hnot⟩ := mem_sdiff.mp hmem
  obtain ⟨hwin,hres⟩ := mem_filter.mp hw
  exact ⟨(Nat.mem_primesLE.mp (mem_filter.mp hwin).1).2,(mem_filter.mp hwin).2,hres,
    lt_of_not_ge (fun hh => hnot (mem_filter.mpr ⟨hw,hh⟩))⟩

/-- There are arbitrarily large odd targets in the selected progression,
including when its residue 3a is divisible by a factor of the modulus. -/
theorem cofinal {M a : ℕ} (hm : 0<M) (hu : a.Coprime M) (X : ℕ) :
    ∃ n : ℕ,X<n ∧ Odd n ∧ n%M=(3*a)%M := by
  have hx : X<2*(X+1)*M := by
    have h := Nat.mul_le_mul_left (2*(X+1)) hm
    omega
  by_cases ha : Odd a
  · refine ⟨3*a+2*(X+1)*M,by omega,?_,by simp⟩
    exact (Odd.mul (by decide : Odd 3) ha).add_even ⟨(X+1)*M,by ring⟩
  · have he := Nat.not_odd_iff_even.mp ha
    have hMo : Odd M := by
      apply Nat.not_even_iff_odd.mp
      intro hen
      have h := Nat.dvd_gcd (even_iff_two_dvd.mp he) (even_iff_two_dvd.mp hen)
      rw [show a.gcd M=1 from hu] at h
      norm_num at h
    refine ⟨3*a+M+2*(X+1)*M,by omega,?_,by simp [Nat.add_mod]⟩
    exact ((he.mul_left 3).add_odd hMo).add_even ⟨(X+1)*M,by ring⟩

#print axioms cofinal

#print axioms original
end
end Arxiv.«2501.03234».ThetaPrescribedTripleResiduals
