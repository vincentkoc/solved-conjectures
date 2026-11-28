import ThetaConsecutiveClusters
import Mathlib.Combinatorics.Pigeonhole

/-! A recurring fixed pattern of consecutive primes with simultaneous theta asymptotics. -/
namespace Arxiv.«2501.03234».ThetaRecurringPrimePattern
open Finset Filter Real ThetaPrimeClusterTransfer ThetaConsecutiveClusters ThetaMaynardClusters
open ThetaShortPrimeInterval ThetaPrimeDensity ThetaStrongOriginalTail ThetaStrongDeviation
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable _

def pattern (D n : ℕ) := (range (D+1)).filter (fun j => (n+j).Prime)

def bases (m D X : ℕ) (T : Finset ℕ) := (Ioc X (X+(X-D))).filter
  (fun n => classCluster m D n ∧ allOne D n ∧ pattern D n=T)

def good (ε : ℝ) (m D X : ℕ) (T : Finset ℕ) := (Ioc X (X+(X-D))).filter
  (fun n => goodCluster ε m D n ∧ allOne D n ∧ pattern D n=T)

theorem mem_pattern {D n j : ℕ} : j∈pattern D n ↔ j≤D ∧ (n+j).Prime := by
  simp [pattern]

theorem size {m D n : ℕ} (h : classCluster m D n) : m≤(pattern D n).card := by
  apply h.trans
  apply card_le_card_of_injOn (fun p => p-n)
  · intro p hp
    obtain ⟨hm,hp,_⟩ := mem_filter.mp hp
    obtain ⟨hl,hu⟩ := mem_Icc.mp hm
    exact mem_pattern.mpr ⟨by change p-n≤D;omega,by change (n+(p-n)).Prime;rwa [Nat.add_sub_of_le hl]⟩
  · intro p hp q hq he
    have hp' := (mem_Icc.mp (mem_filter.mp hp).1).1
    have hq' := (mem_Icc.mp (mem_filter.mp hq).1).1
    change p-n=q-n at he
    omega

/-- Pick a full offset pattern, before fixing any accuracy, on a common
unbounded set of dyadic endpoints. -/
theorem ordinary_pattern {m k : ℕ} {A : ℝ} (hA : 0<A) (sieve : Sieve m k A) :
    ∃ T ∈ (range (diameter k+1)).powerset, m≤T.card ∧ ∃ β : ℝ, 0<β ∧
      ∃ᶠ X : ℕ in atTop, β*X/(1+log X)^k≤((bases m (diameter k) X T).card:ℝ) := by
  classical
  let D := diameter k
  let F := (range (D+1)).powerset
  have hF : F.Nonempty := ⟨∅,mem_powerset.mpr (empty_subset _)⟩
  have hFc : 0<(F.card:ℝ) := Nat.cast_pos.mpr (card_pos.mpr hF)
  have hL : 0<(cost k:ℝ) := by
    have h1 : 1≤ThetaConsecutiveProgression.period (diameter k) := by rw [ThetaConsecutiveProgression.period_eq];omega
    exact_mod_cast (show 0<ThetaConsecutiveClusters.cost k by dsimp only [ThetaConsecutiveClusters.cost,ThetaConsecutiveClusters.slope];omega)
  let β := A/(cost k:ℝ)/F.card
  have hb : 0<β := div_pos (div_pos hA hL) hFc
  have ht := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<19/40)).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have evt : ∀ᶠ X : ℕ in atTop, ∃ T∈F, β*X/(1+log X)^k≤((bases m D X T).card:ℝ) := by
    filter_upwards [ThetaConsecutiveClusters.ordinary hA sieve,ht.eventually_ge_atTop (cost k:ℝ),
      eventually_ge_atTop 1] with X hX hroot hpos
    have hx : 0<(X:ℝ) := by exact_mod_cast (show 0<X by omega)
    change (cost k:ℝ)≤(X:ℝ)^(19/40:ℝ) at hroot
    have hscale : (cost k:ℝ)*(X:ℝ)^(21/40:ℝ)≤X := by
      apply (mul_le_mul_of_nonneg_right hroot (rpow_nonneg hx.le _)).trans_eq
      rw [←rpow_add hx,show (19/40:ℝ)+21/40=1 by norm_num,rpow_one]
    let S := (Ioc X (X+(X-D))).filter (fun n => classCluster m D n ∧ allOne D n)
    have H : A/(cost k:ℝ)*X/(1+log X)^k≤(S.card:ℝ) := hX X hscale le_rfl
    have hcost : F.card • (β*X/(1+log X)^k) ≤ (S.card:ℝ) := by
      apply le_trans _ H
      rw [nsmul_eq_mul]
      dsimp [β]
      field_simp
      norm_num
    obtain ⟨T,hT,hc⟩ := exists_le_card_fiber_of_nsmul_le_card_of_maps_to
      (s:=S) (t:=F) (f:=pattern D) (fun n _ => mem_powerset.mpr (filter_subset ..)) hF hcost
    refine ⟨T,hT,?_⟩
    have he : S.filter (fun n => pattern D n=T)=bases m D X T := by
      ext n;simp [S,bases,and_assoc]
    rwa [he] at hc
  obtain ⟨T,hT,hf⟩ := (frequently_exists_finite F.finite_toSet).mp evt.frequently
  obtain ⟨X,hp,hpos⟩ := (hf.and_eventually (eventually_ge_atTop 1)).exists
  have hx : 0<(X:ℝ) := by exact_mod_cast (show 0<X by omega)
  have hv : 0<1+log (X:ℝ) := by linarith only [log_nonneg (by exact_mod_cast hpos : (1:ℝ)≤X)]
  have hc : 0<(bases m D X T).card := Nat.cast_pos.mp ((div_pos (mul_pos hb hx) (pow_pos hv k)).trans_le hp)
  obtain ⟨n,hn⟩ := card_pos.mp hc
  obtain ⟨_,hm,_,he⟩ := mem_filter.mp hn
  refine ⟨T,hT,he ▸ size hm,β,hb,hf⟩

/-- Uniform loss for every pattern of diameter D at a dyadic endpoint. The
global theta estimate suffices for this step. -/
theorem dyadic_loss {ε δ : ℝ} (he : 0<ε) (hδ : 0<δ) (D k : ℕ) : ∀ᶠ X : ℕ in atTop,
    ((contaminated ε X (X-D) D).card:ℝ)≤δ*X/(1+log X)^k := by
  let d := ((D+1:ℕ):ℝ)
  have hd : 0<d := by dsimp [d];positivity
  have htwo : Tendsto (fun X : ℕ => 2*X) atTop atTop :=
    tendsto_atTop.mpr (fun z => (eventually_ge_atTop z).mono fun _ h => by omega)
  filter_upwards [htwo.eventually (ThetaStrongOriginalTail.original he),
    htwo.eventually (absorb_log_power (show 0<3*d/δ by positivity) (by norm_num : (0:ℝ)<2048) k),
    eventually_ge_atTop D,eventually_ge_atTop 1] with X hE hsmall hDX hX
  let P := fun p : ℕ => ε*(p:ℝ)*log p≤|(S p:ℝ)-p*log p/2|
  let V := 1+log (X:ℝ)
  let F := exp (rate (2*X:ℕ)/2048)
  have hF : 0<F := exp_pos _
  have hxp : 0<(X:ℝ) := by exact_mod_cast (show 0<X by omega)
  have hV : 0<V := by dsimp [V];linarith only [log_nonneg (by exact_mod_cast hX : (1:ℝ)≤X)]
  have hX2 : X≤2*X := by omega
  have hlog := log_le_log hxp (show (X:ℝ)≤((2*X:ℕ):ℝ) by exact_mod_cast hX2)
  have hsub : primes X X P⊆primeSet P (2*X) := by
    intro p hp
    obtain ⟨hm,hp,hP⟩ := mem_primes.mp hp
    have hl := (mem_Ioc.mp hm).2
    exact mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨by omega,hp⟩,hP⟩
  have hπ : (Nat.primeCounting (2*X):ℝ)≤3*X := by
    have hs : Nat.primesLE (2*X)⊆range (2*X+1) := fun p hp => mem_range.mpr (Nat.lt_succ_of_le (Nat.mem_primesLE.mp hp).1)
    have h := card_le_card hs
    rw [Nat.primesLE_card_eq_primeCounting,card_range] at h
    exact_mod_cast (show Nat.primeCounting (2*X)≤3*X by omega)
  rw [show -rate (2*X:ℕ)/2048= -(rate (2*X:ℕ)/2048) by ring,exp_neg] at hE
  have hh := (Nat.cast_le (α:=ℝ)).mpr (count ε X (X-D) D)
  rw [Nat.sub_add_cancel hDX,Nat.cast_mul] at hh
  have hcost : ((contaminated ε X (X-D) D).card:ℝ)≤d*(3*X*F⁻¹) := by
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ hd.le
    exact ((Nat.cast_le.mpr (card_le_card hsub)).trans hE).trans (mul_le_mul_of_nonneg_right hπ (inv_nonneg.mpr hF.le))
  have hpoly : 3*d*V^k≤δ*F := by
    change 3*d/δ*(1+log ((2*X:ℕ):ℝ))^k≤F at hsmall
    have hh₀ : V≤1+log ((2*X:ℕ):ℝ) := add_le_add_right hlog 1
    have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hV.le hh₀ k)
      (show 0≤3*d/δ by positivity)
    have h := hh.trans hsmall
    rw [div_mul_eq_mul_div,div_le_iff₀ hδ] at h
    linarith only [h]
  apply hcost.trans
  change d*(3*X*F⁻¹)≤δ*X/V^k
  rw [le_div_iff₀ (pow_pos hV k)]
  apply (mul_le_mul_iff_left₀ hF).mp
  rw [show d*(3*X*F⁻¹)*V^k*F=3*d*V^k*X by field_simp]
  nlinarith only [mul_le_mul_of_nonneg_right hpoly hxp.le]

/-- One fixed full set of offsets recurs quantitatively along the same
unbounded set of endpoints at every precision, using only the ordinary sieve input. -/
theorem original {m k : ℕ} {A : ℝ} (hA : 0<A) (sieve : Sieve m k A) :
    ∃ T ∈ (range (diameter k+1)).powerset, m≤T.card ∧ ∃ β : ℝ, 0<β ∧
      ∃ E : Set ℕ, (∃ᶠ X : ℕ in atTop, X∈E) ∧ ∀ ε : ℝ, 0<ε → ∀ᶠ X : ℕ in atTop,
        X∈E → β*X/(1+log X)^k≤((good ε m (diameter k) X T).card:ℝ) := by
  obtain ⟨T,hT,hm,B,hB,hf⟩ := ordinary_pattern hA sieve
  let β := B/2
  have hβ : 0<β := by dsimp [β];positivity
  let D := diameter k
  let E := {X : ℕ | B*X/(1+log X)^k≤((bases m D X T).card:ℝ)}
  refine ⟨T,hT,hm,β,hβ,E,hf,?_⟩
  intro ε he
  filter_upwards [dyadic_loss he hβ D k] with X hl
  intro hE
  change B*X/(1+log X)^k≤((bases m D X T).card:ℝ) at hE
  have h := (Nat.cast_le (α:=ℝ)).mpr (lost_where ε m D X (X-D) (fun n => allOne D n ∧ pattern D n=T))
  rw [Nat.cast_add] at h
  have hh : ((bases m D X T).card:ℝ)≤((good ε m D X T).card:ℝ)+((contaminated ε X (X-D) D).card:ℝ) := by
    convert! h using 1 <;> simp only [good,bases] <;> congr
  have heq : B*(X:ℝ)/(1+log X)^k=2*(β*X/(1+log X)^k) := by dsimp [β];ring
  rw [heq] at hE
  linarith only [hE,hh,hl]

open scoped Topology in
/-- Along a single increasing sequence the same full pattern of ordinary
consecutive primes recurs, and every one of its normalized theta sums tends to 1/2. -/
theorem common_limit {m k : ℕ} {A : ℝ} (hA : 0<A) (sieve : Sieve m k A) :
    ∃ T ∈ (range (diameter k+1)).powerset, m≤T.card ∧ ∃ n : ℕ → ℕ, StrictMono n ∧
      (∀ t,pattern (diameter k) (n t)=T ∧ allOne (diameter k) (n t)) ∧
      ∀ h∈T, Tendsto (fun t => (S (n t+h):ℝ)/((n t+h:ℕ)*log (n t+h:ℕ))) atTop (𝓝 (1/2)) := by
  obtain ⟨T,hT,hm,β,hβ,E,hfreq,h⟩ := original hA sieve
  let D := diameter k
  let ε (t : ℕ) := 1/((t:ℝ)+1)
  have he (t : ℕ) : 0<ε t := by dsimp [ε];positivity
  have pick (t : ℕ) : ∃ n : ℕ,t≤n ∧ goodCluster (ε t) m D n ∧ allOne D n ∧ pattern D n=T := by
    obtain ⟨X,hE,hcard,hpos,hlarge⟩ :=
      (hfreq.and_eventually ((h (ε t) (he t)).and ((eventually_ge_atTop 1).and (eventually_ge_atTop t)))).exists
    have hxp : 0<(X:ℝ) := by exact_mod_cast (show 0<X by omega)
    have hv : 0<1+log (X:ℝ) := by linarith only [log_nonneg (by exact_mod_cast hpos : (1:ℝ)≤X)]
    have H : 0<(good (ε t) m D X T).card := Nat.cast_pos.mp ((div_pos (mul_pos hβ hxp) (pow_pos hv _)).trans_le (hcard hE))
    obtain ⟨n,hn⟩ := card_pos.mp H
    obtain ⟨hi,hg,hc,hp⟩ := mem_filter.mp hn
    exact ⟨n,hlarge.trans (mem_Ioc.mp hi).1.le,hg,hc,hp⟩
  choose g hg hgood hone hpat using pick
  have hg' : Tendsto g atTop atTop := tendsto_atTop_mono hg tendsto_id
  obtain ⟨φ,hφ,hgφ⟩ := strictMono_subseq_of_tendsto_atTop hg'
  refine ⟨T,hT,hm,g ∘ φ,hgφ,fun t => ⟨hpat _,hone _⟩,?_⟩
  intro j hj
  have H : Tendsto (fun t => (S (g t+j):ℝ)/((g t+j:ℕ)*log (g t+j:ℕ))) atTop (𝓝 (1/2)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    apply squeeze_zero (fun _ => norm_nonneg _) _ (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ))
    intro t
    let p := g t+j
    have hp := mem_pattern.mp (show j∈pattern D (g t) by rw [hpat];exact hj)
    have hh := (hgood t).2 p (mem_Icc.mpr ⟨by dsimp [p];omega,by dsimp [p];omega⟩) hp.2
    have hp1 : (1:ℝ)<p := by exact_mod_cast hp.2.one_lt
    have hden : 0<(p:ℝ)*log p := mul_pos (by linarith) (log_pos hp1)
    have hid : (S p:ℝ)/(p*log p)-1/2=((S p:ℝ)-p*log p/2)/(p*log p) := by field_simp [ne_of_gt (log_pos hp1)]
    change ‖(S p:ℝ)/(p*log p)-1/2‖≤ε t
    rw [Real.norm_eq_abs,hid,abs_div,abs_of_pos hden,div_le_iff₀ hden]
    linarith only [hh]
  exact H.comp hφ.tendsto_atTop

open scoped Topology in
/-- Consecutive prime pairs in the class one modulo eight, with simultaneous
convergence of the original signed theta ratios. -/
def Realized (g : ℕ) : Prop :=
    ∃ p : ℕ → ℕ, StrictMono p ∧
      (∀ t, (p t).Prime ∧ (p t+g).Prime ∧ p t%8=1 ∧ (p t+g)%8=1 ∧
        ∀ q, p t<q → q<p t+g → ¬q.Prime) ∧
      Tendsto (fun t => (S (p t):ℝ)/((p t:ℝ)*log (p t))) atTop (𝓝 (1/2)) ∧
      Tendsto (fun t => (S (p t+g):ℝ)/((p t+g:ℕ)*log (p t+g:ℕ))) atTop (𝓝 (1/2))

open scoped Topology in
theorem gap_of_pair {D u v : ℕ} {T : Finset ℕ} (hT : T⊆range (D+1))
    (hu : u∈T) (hv : v∈T) (huv : u<v) (adj : ∀ j∈T,u<j → j<v → False)
    {n : ℕ → ℕ} (hn : StrictMono n) (hpat : ∀ t,pattern D (n t)=T ∧ allOne D (n t))
    (hlim : ∀ h∈T, Tendsto (fun t => (S (n t+h):ℝ)/((n t+h:ℕ)*log (n t+h:ℕ))) atTop (𝓝 (1/2))) :
    8∣v-u ∧ Realized (v-u) := by
  let g := v-u
  let p (t : ℕ) := n t+u
  have heq (t : ℕ) : p t+g=n t+v := by dsimp [p,g];omega
  have hp (t j : ℕ) (hj : j∈T) : (n t+j).Prime ∧ (n t+j)%8=1 := by
    have hj' : j∈pattern D (n t) := (hpat t).1 ▸ hj
    have h := mem_pattern.mp hj'
    exact ⟨h.2,(hpat t).2 _ (mem_Icc.mpr ⟨by omega,by omega⟩) h.2⟩
  have hmod : 8∣g := by
    have h1 := (hp 0 u hu).2
    have h2 := (hp 0 v hv).2
    dsimp [g];omega
  refine ⟨hmod,p,(fun i j hij => Nat.add_lt_add_right (hn hij) u),?_,hlim u hu,?_⟩
  · intro t
    rw [heq]
    refine ⟨(hp t u hu).1,(hp t v hv).1,(hp t u hu).2,(hp t v hv).2,?_⟩
    intro q hl hh hq
    change n t+u<q at hl
    let j := q-n t
    have hj₁ : u<j := by dsimp [j];omega
    have hj₂ : j<v := by dsimp [j];omega
    have hvD : v≤D := mem_range.mp (hT hv) |> Nat.le_of_lt_succ
    have hj : j∈pattern D (n t) := mem_pattern.mpr ⟨by omega,by rwa [show n t+j=q by dsimp [j];omega]⟩
    rw [(hpat t).1] at hj
    exact adj j hj hj₁ hj₂
  · have heq' (t : ℕ) : p t+(v-u)=n t+v := heq t
    simpa only [heq'] using hlim v hv


theorem fixed_gap {k : ℕ} {A : ℝ} (hA : 0<A) (sieve : Sieve 2 k A) :
    ∃ g : ℕ, 0<g ∧ 8∣g ∧ Realized g := by
  classical
  obtain ⟨T,hT,hm,n,hn,hpat,hlim⟩ := common_limit hA sieve
  have hT₀ : T.Nonempty := card_pos.mp (by omega)
  let u := T.min' hT₀
  have hu : u∈T := min'_mem ..
  have hT₁ : (T.erase u).Nonempty := card_pos.mp (by rw [card_erase_of_mem hu];omega)
  let v := (T.erase u).min' hT₁
  have hv₀ : v∈T.erase u := min'_mem ..
  obtain ⟨hne,hv⟩ := mem_erase.mp hv₀
  have huv : u<v := lt_of_le_of_ne (min'_le T v hv) hne.symm
  refine ⟨v-u,by omega,gap_of_pair (mem_powerset.mp hT) hu hv huv ?_ hn hpat hlim⟩
  intro j hj hj₁ hj₂
  exact hj₂.not_ge (min'_le (T.erase u) j (mem_erase.mpr ⟨hj₁.ne',hj⟩))

#print axioms fixed_gap

#print axioms common_limit

#print axioms original

#print axioms ordinary_pattern
end
end Arxiv.«2501.03234».ThetaRecurringPrimePattern
