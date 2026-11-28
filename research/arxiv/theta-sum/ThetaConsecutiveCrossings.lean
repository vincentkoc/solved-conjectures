import ThetaShortExcursionTails

/-! Distinct prime logarithms are rationally independent in pairs. Thus at
most one prime can have zero centered residual, and opposite excursions in a
late interval force a strict sign change across consecutive progression primes. -/
namespace Arxiv.«2501.03234».ThetaConsecutiveCrossings
open Real Finset Filter ThetaShortPrimeInterval ThetaLocalPrimeCounts
open ThetaLocalSignedExcursions ThetaShortExcursionTails
noncomputable section

def deviation (p : ℕ) : ℝ := (S p:ℝ)/p-log p/2

private theorem zero_identity {p : ℕ} (hp : p.Prime) (hz : deviation p=0) :
    0<(S p).toNat ∧ (p:ℝ)*log p=2*((S p).toNat:ℝ) := by
  have hpos : 0<(p:ℝ) := by exact_mod_cast hp.pos
  have hl := log_pos (show 1<(p:ℝ) by exact_mod_cast hp.one_lt)
  change (S p:ℝ)/p-log p/2=0 at hz
  field_simp [hpos.ne'] at hz
  have hsp : 0<S p := by exact_mod_cast (show 0<(S p:ℝ) by nlinarith [mul_pos hpos hl])
  have heq : ((S p).toNat:ℤ)=S p := Int.toNat_of_nonneg hsp.le
  refine ⟨by omega,?_⟩
  have hcast : ((S p).toNat:ℝ)=(S p:ℝ) := by exact_mod_cast heq
  rw [hcast]; linarith only [hz, mul_comm (log (p:ℝ)) p]

theorem zero_unique {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp₀ : deviation p=0) (hq₀ : deviation q=0) : p=q := by
  obtain ⟨hsp,hep⟩ := zero_identity hp hp₀
  obtain ⟨hsq,heq⟩ := zero_identity hq hq₀
  let a := p*(S q).toNat
  let b := q*(S p).toNat
  have ha : 0<a := Nat.mul_pos hp.pos hsq
  have hb : 0<b := Nat.mul_pos hq.pos hsp
  have hp' : 0<(p:ℝ) := by exact_mod_cast hp.pos
  have hq' : 0<(q:ℝ) := by exact_mod_cast hq.pos
  have H : (p:ℝ)^a=(q:ℝ)^b := by
    apply log_injOn_pos (pow_pos hp' _) (pow_pos hq' _)
    rw [log_pow,log_pow]
    dsimp only [a,b]; push_cast
    linear_combination ((S q).toNat:ℝ)*hep-((S p).toNat:ℝ)*heq
  exact (hp.pow_inj' hq ha.ne' hb.ne' (by exact_mod_cast H)).1

theorem eventually_nonzero : ∀ᶠ p : ℕ in atTop, p.Prime → deviation p≠0 := by
  by_cases h : ∃ p : ℕ, p.Prime ∧ deviation p=0
  · obtain ⟨q,hq,hqz⟩ := h
    filter_upwards [eventually_gt_atTop q] with p hp hpr hz
    exact hp.ne' (zero_unique hpr hq hz hqz)
  · exact Eventually.of_forall (fun p hpr hz => h ⟨p,hpr,hz⟩)

private theorem adjacent {s : Finset ℕ} (f : ℕ → ℝ)
    (hz : ∀ n∈s, f n≠0) (hpos : ∃ n∈s, 0<f n) (hneg : ∃ n∈s, f n<0) :
    ∃ a∈s, ∃ b∈s, a<b ∧ f a*f b<0 ∧ ∀ t∈s, a<t → ¬t<b := by
  classical
  obtain ⟨u,hu,hu'⟩ := hpos
  obtain ⟨v,hv,hv'⟩ := hneg
  let first := s.min' ⟨u,hu⟩
  have hf : first∈s := s.min'_mem _
  let opp := s.filter (fun n => ¬ (0<f n ↔ 0<f first))
  have ho : opp.Nonempty := by
    by_cases h : 0<f first
    · exact ⟨v,mem_filter.mpr ⟨hv,fun eq => (not_lt_of_ge hv'.le) (eq.mpr h)⟩⟩
    · exact ⟨u,mem_filter.mpr ⟨hu,fun eq => h (eq.mp hu')⟩⟩
  let b := opp.min' ho
  obtain ⟨hb,hb'⟩ := mem_filter.mp (opp.min'_mem ho)
  have hfb : first<b := lt_of_le_of_ne (s.min'_le _ hb) (fun e => hb' (by rw [e]))
  let before := s.filter (·<b)
  have hbefore : before.Nonempty := ⟨first,mem_filter.mpr ⟨hf,hfb⟩⟩
  let a := before.max' hbefore
  obtain ⟨ha,hab⟩ := mem_filter.mp (before.max'_mem hbefore)
  have ha' : 0<f a ↔ 0<f first := by
    by_contra hn
    exact (not_le_of_gt hab) (opp.min'_le _ (mem_filter.mpr ⟨ha,hn⟩))
  have sign : f a*f b<0 := by
    by_cases hap : 0<f a
    · have hbp : ¬0<f b := fun h => hb' (iff_of_true h (ha'.mp hap))
      exact mul_neg_of_pos_of_neg hap (lt_of_le_of_ne (le_of_not_gt hbp) (hz b hb))
    · have hbp : 0<f b := by
        by_contra h
        exact hb' (iff_of_false h (fun hh => hap (ha'.mpr hh)))
      exact mul_neg_of_neg_of_pos (lt_of_le_of_ne (le_of_not_gt hap) (hz a ha)) hbp
  exact ⟨a,ha,b,hb,hab,sign,fun t ht hat htb =>
    (not_le_of_gt hat) (before.le_max' t (mem_filter.mpr ⟨ht,htb⟩))⟩


/-- A strict crossing between consecutive primes of the specified residue class. -/
def Crossing (X H q r : ℕ) := ∃ a b : ℕ, X<a ∧ a<b ∧ b≤X+H ∧
    a.Prime ∧ b.Prime ∧ a%q=r ∧ b%q=r ∧ deviation a*deviation b<0 ∧
    ∀ t : ℕ, a<t → t<b → t.Prime → t%q≠r

/-- Opposite residual signs among the progression primes of a window with
no zero residual give an adjacent strict crossing in that same window. -/
theorem of_signs {X H q r : ℕ}
    (hz : ∀ n∈(sample X H).filter (fun t => t%q=r), deviation n≠0)
    (hpos : ∃ n∈(sample X H).filter (fun t => t%q=r), 0<deviation n)
    (hneg : ∃ n∈(sample X H).filter (fun t => t%q=r), deviation n<0) : Crossing X H q r := by
  classical
  obtain ⟨p,hp,t,ht,hpt,hsign,hbetween⟩ := adjacent deviation hz
    hpos hneg
  obtain ⟨hpS,hpr⟩ := mem_filter.mp hp
  obtain ⟨htS,htr⟩ := mem_filter.mp ht
  obtain ⟨hpI,hp',_⟩ := mem_primes.mp hpS
  obtain ⟨htI,ht',_⟩ := mem_primes.mp htS
  have hx := (mem_Ioc.mp hpI).1
  have hend := (mem_Ioc.mp htI).2
  refine ⟨p,t,hx,hpt,hend,hp',ht',hpr,htr,hsign,?_⟩
  intro n hpn hnt hn heqr
  exact hbetween n (mem_filter.mpr ⟨mem_primes.mpr ⟨mem_Ioc.mpr ⟨hx.trans hpn,hnt.le.trans hend⟩,hn,trivial⟩,heqr⟩) hpn hnt

theorem intervals {θ : ℝ} (hedge : Edge θ) :
    ∃ η b : ℝ, 0<η ∧ 0≤b ∧ ∀ᶠ X : ℕ in atTop,
    ∀ H : ℕ, H≤X → (X:ℝ)^θ≤H → ∀ q r : ℕ, 0 < q → r < q → r.Coprime q →
      log q≤η*(log (log (log X))-b) → Crossing X H q r := by
  classical
  obtain ⟨η,hη,he⟩ := hedge
  obtain ⟨b,hb,he⟩ := he (show (0:ℝ)<1 by norm_num)
  obtain ⟨P,hP⟩ := eventually_atTop.mp eventually_nonzero
  have hlog := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have h₃ := tendsto_log_atTop.comp (tendsto_log_atTop.comp hlog)
  refine ⟨η,b,hη,hb,?_⟩
  filter_upwards [he,eventually_ge_atTop P,eventually_ge_atTop (2:ℕ),h₃.eventually_gt_atTop b] with X h hXP hX hh
  intro H hHX hlen q r hq hr hqr hqz
  let s := (sample X H).filter (fun p => p%q=r)
  let v := log (log (log X))-b
  have hv : 0<v := sub_pos.mpr hh
  have hX' : 1<(X:ℝ) := by exact_mod_cast (show 1<X by omega)
  have hH : 0<(H:ℝ) := (rpow_pos_of_pos (by linarith) θ).trans_le hlen
  have hl := log_pos hX'
  have select : ∀ z : ℝ, |z|=1 → ∃ p∈s, 0<z*deviation p := by
    intro z hz
    have he := h H hHX hlen q r hq hr hqr hqz z hz
    have hc : 0<((excursions X H q r z v).card:ℝ) := lt_of_lt_of_le (by positivity) he
    obtain ⟨p,hp⟩ := card_pos.mp (by exact_mod_cast hc)
    obtain ⟨hs,hr',hgt⟩ := mem_filter.mp hp
    exact ⟨p,mem_filter.mpr ⟨hs,hr'⟩,lt_of_lt_of_le (by positivity : 0<v^2/(64*π^2)) hgt⟩
  have nz : ∀ n∈s, deviation n≠0 := by
    intro n hn
    obtain ⟨hI,hpr,_⟩ := mem_primes.mp (mem_filter.mp hn).1
    exact hP n (hXP.trans (mem_Ioc.mp hI).1.le) hpr
  obtain ⟨a,ha,ha'⟩ := select 1 (by norm_num)
  obtain ⟨b,hb,hb'⟩ := select (-1) (by norm_num)
  exact of_signs nz ⟨a,ha,by simpa only [one_mul] using ha'⟩ ⟨b,hb,by linarith only [hb']⟩

#print axioms intervals

#print axioms zero_unique
#print axioms eventually_nonzero
end
end Arxiv.«2501.03234».ThetaConsecutiveCrossings
