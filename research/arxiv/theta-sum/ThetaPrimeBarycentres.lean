import ThetaPrescribedTripleResiduals

/-! Every large prime in a selected reduced class is the exact arithmetic mean
of many disjoint triples of other primes with the prescribed theta residual. -/
namespace Arxiv.«2501.03234».ThetaPrimeBarycentres
open Real Filter Finset ThetaTernaryPacking ThetaTernaryIncidence ThetaCalibratedCone
open ThetaPrescribedTripleResiduals ThetaClassConcentration ThetaNaturalPrimeMeans
noncomputable section

theorem discard_vertex (D : Finset Triple) (hd : separated D) (p : ℕ) :
    D.card≤(D.filter (fun t => p∉vertices t)).card+1 := by
  have hsmall : (D.filter (fun t => p∈vertices t)).card≤1 := by
    apply card_le_one.mpr
    intro t ht u hu
    obtain ⟨ht,hp⟩ := mem_filter.mp ht
    obtain ⟨hu,hp'⟩ := mem_filter.mp hu
    by_contra hne
    exact disjoint_left.mp (hd t ht u hu hne) hp hp'
  have h := card_filter_add_card_filter_not (s:=D) (p:=fun t => p∈vertices t)
  calc D.card = _ := h.symm
       _ ≤ _ := by simpa only [Nat.add_comm] using Nat.add_le_add_right hsmall (D.filter (fun t => p∉vertices t)).card

def Rich (θ b C : ℝ) (M a : ℕ) (y d : ℝ) (p : ℕ) : Prop :=
  ∃ D : Finset Triple,
        b^2*(3*(p:ℝ))^θ/(108*C*M.totient*(1+log (3*(p:ℝ))))≤D.card+1 ∧ separated D ∧
        ∀ t∈D,t.1+t.2.1+t.2.2=3*p ∧ t.1≠t.2.1 ∧ t.1≠t.2.2 ∧ t.2.1≠t.2.2 ∧
          ∀ v∈vertices t,v≠p ∧ v.Prime ∧ |(v:ℝ)-p|≤(3*(p:ℝ))^θ ∧ v%M=a ∧
            |(S v:ℝ)/v-log v/2-y|<d

theorem original {e : ℕ} (he : 32≤e) (ht : e≤48) (hk : Kernel e)
    {β θ b C : ℝ} (hβ : (e:ℝ)/64<β) (hθ : β<θ) (htop : θ<1)
    (ord : ThetaLocalPrimeCounts.Ordinary β) (hAP : ProgressionMangoldt)
    (hb : 0<b) (hC : 0<C) (hc : OrdinaryClasses θ b C)
    {q r : ℕ} (hq : 0<q) (hr : r<q) (hu : r.Coprime q)
    (y : ℝ) {d : ℝ} (hd : 0<d) (N : ℕ) :
    ∃ T≥N,q∣m T ∧ ∃ a < m T,a.Coprime (m T) ∧ a%q=r ∧
      ∀ᶠ p : ℕ in atTop,p.Prime → p%(m T)=a → Rich θ b C (m T) a y d p := by
  obtain ⟨T,hT,hM,a,ha,hau,har,h⟩ :=
    ThetaPrescribedTripleResiduals.original he ht hk hβ hθ htop ord hAP hb hC hc hq hr hu y hd N
  obtain ⟨X,hX⟩ := eventually_atTop.mp h
  refine ⟨T,hT,hM,a,ha,hau,har,?_⟩
  filter_upwards [eventually_ge_atTop X,eventually_gt_atTop (2:ℕ)] with p hpX hp₂ hp hclass
  have hop : Odd p := Nat.odd_iff.mpr (hp.eq_two_or_odd.resolve_left (by omega))
  have hcong : (3*p)%(m T)=(3*a)%(m T) := by simp [Nat.mul_mod,hclass,Nat.mod_eq_of_lt ha]
  obtain ⟨D,hlo,hs,hmem⟩ := hX (3*p) (by omega) ((by decide : Odd 3).mul hop) hcong
  let D' := D.filter (fun t => p∉vertices t)
  have hcD : (D.card:ℝ)≤(D'.card:ℝ)+1 := by exact_mod_cast discard_vertex D hs p
  refine ⟨D',?_,fun t ht u hu hne => hs t (mem_filter.mp ht).1 u (mem_filter.mp hu).1 hne,?_⟩
  · simpa only [Nat.cast_mul,Nat.cast_ofNat] using hlo.trans hcD
  intro t ht
  obtain ⟨ht,hnp⟩ := mem_filter.mp ht
  obtain ⟨hn,h₁,h₂,h₃,hw⟩ := hmem t ht
  refine ⟨hn,h₁,h₂,h₃,?_⟩
  intro v hv
  have h := hw v hv
  have hmean : 3*(p:ℝ)/3=p := by ring
  have hne : v≠p := by intro hh;subst v;exact hnp hv
  exact ⟨hne,by simpa only [Nat.cast_mul,Nat.cast_ofNat,hmean] using h⟩

/-- The target and all three summands satisfy the same prescribed test. -/
noncomputable def marked (θ b C : ℝ) (M a : ℕ) (y d : ℝ) (X H : ℕ) : Finset ℕ := by
  classical
  exact (ThetaLocalIntervalTests.hits M a y d (ThetaLocalPrimeCounts.sample X H)).filter
    (Rich θ b C M a y d)

theorem four_marks {e : ℕ} (he : 32≤e) (ht : e≤48) (hk : Kernel e)
    {β θ b C : ℝ} (hβ : (e:ℝ)/64<β) (hθ : β<θ) (htop : θ<1)
    (ord : ThetaLocalPrimeCounts.Ordinary β) (hAP : ProgressionMangoldt)
    (hb : 0<b) (hC : 0<C) (hc : OrdinaryClasses θ b C)
    {q r : ℕ} (hq : 0<q) (hr : r<q) (hu : r.Coprime q)
    (y : ℝ) {d : ℝ} (hd : 0<d) (N : ℕ) :
    ∃ T≥N,q∣m T ∧ ∃ a < m T,a.Coprime (m T) ∧ a%q=r ∧ ∃ δ : ℝ,0<δ ∧
      ∀ᶠ X : ℕ in atTop,∀ H : ℕ,H≤X → (X:ℝ)^β≤H →
        δ*H/log X≤((marked θ b C (m T) a y d X H).card:ℝ) := by
  classical
  obtain ⟨T,hT,hM,a,ha,hau,har,hrep⟩ := original he ht hk hβ hθ htop ord hAP hb hC hc hq hr hu y hd N
  obtain ⟨Y,hY⟩ := eventually_atTop.mp hrep
  obtain ⟨δ,hδ,hdens⟩ := ThetaShortResidualSupport.density he ht hk hβ (hθ.trans htop).le
    ord hAP (ThetaCompactModulus.positive T) ha hau y hd
  refine ⟨T,hT,hM,a,ha,hau,har,δ,hδ,?_⟩
  filter_upwards [hdens,eventually_ge_atTop Y] with X hden hX H hHX hlen
  apply (hden H hHX hlen).trans
  apply Nat.cast_le.mpr
  apply card_le_card
  intro p hp
  obtain ⟨hclass,_⟩ := mem_filter.mp hp
  obtain ⟨hpr,hr⟩ := mem_filter.mp hclass
  obtain ⟨hwin,hprime,_⟩ := ThetaShortPrimeInterval.mem_primes.mp hpr
  exact mem_filter.mpr ⟨hp,hY p (hX.trans (mem_Ioc.mp hwin).1.le) hprime hr⟩

#print axioms four_marks
#print axioms discard_vertex
#print axioms original
end
end Arxiv.«2501.03234».ThetaPrimeBarycentres
