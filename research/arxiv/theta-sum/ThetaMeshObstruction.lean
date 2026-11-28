import ThetaReciprocalMesh

/-! Sparse deterministic test lengths for the lower-growth obstruction in the original theta sum. -/
namespace Arxiv.«2501.03234».ThetaMeshObstruction
open Finset Filter Real ThetaResonanceScales ThetaReciprocalPrefixes ThetaReciprocalResonance
open ThetaReciprocalMesh ThetaResonantLengths ThetaSquareRootWindow ThetaBourgainGaraev
noncomputable section

def tests (p : ℕ) (δ : ℝ) : Finset ℕ := (grid p (resolution p)).filter fun n =>
  3*exp (sqrt (log p)/512)≤4*(n:ℝ) ∧ (n:ℝ)≤(p:ℝ)^(3/4+δ) ∧ n<p

def large (p : ℕ) [Fact p.Prime] (n : ℕ) : Prop :=
  ∃ a : ZMod p, a≠0 ∧ 4*(n:ℝ)<resolution p*‖recipSum n a‖

theorem controls : ∀ᶠ p : ℕ in atTop, 4≤resolution p ∧
    ∀ N : ℕ, exp (sqrt (log p)/512)≤(N:ℝ) → 1<(N:ℝ) ∧ 1≤log (log (N:ℝ)) := by
  have h := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [h.eventually_ge_atTop (2048^2),(tendsto_log_atTop.comp h).eventually_ge_atTop 1] with p hu hv
  change 2048^2 ≤ log (p:ℝ) at hu
  change 1≤log (log (p:ℝ)) at hv
  have hM := Nat.le_ceil (1073741824*log (p:ℝ)*log (log p))
  have h₁ : 1≤log (p:ℝ) := by linarith only [hu]
  have hpos := mul_le_mul h₁ hv (by norm_num : 0≤(1:ℝ)) (by linarith only [h₁] : 0≤log (p:ℝ))
  constructor
  · change 4≤⌈1073741824*log (p:ℝ)*log (log p)⌉₊
    exact_mod_cast (by linarith only [hM,hpos] : (4:ℝ)≤(⌈1073741824*log (p:ℝ)*log (log p)⌉₊:ℝ))
  intro N hN
  have hn := (exp_pos _).trans_le hN
  have hs := sqrt_le_sqrt hu
  rw [sqrt_sq (by norm_num : 0≤(2048:ℝ))] at hs
  have hl := (le_log_iff_exp_le hn).mpr hN
  have hg : 3≤log (N:ℝ) := by linarith only [hs,hl]
  exact ⟨(log_pos_iff hn.le).mp (by linarith),
    (le_log_iff_exp_le (by linarith)).mpr (exp_one_lt_three.le.trans hg)⟩

theorem test_count : ∀ᶠ p : ℕ in atTop, ∀ δ : ℝ,
    ((tests p δ).card:ℝ)≤34359738368*(log p)^2*log (log p) := by
  have h := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [scales,h.eventually_ge_atTop 1,(tendsto_log_atTop.comp h).eventually_ge_atTop 1] with p hs hu hv
  intro δ
  change 1≤log (p:ℝ) at hu
  change 1≤log (log (p:ℝ)) at hv
  obtain ⟨_,_,_,_,_,_,ht,_⟩ := hs
  have hsub : tests p δ ⊆ grid p (resolution p) := filter_subset _ _
  have hc := (Nat.cast_le (α:=ℝ)).mpr ((card_le_card hsub).trans (ThetaReciprocalMesh.card p (resolution p)))
  change ((tests p δ).card:ℝ)≤_ at hc
  push_cast at hc
  have hm := Nat.ceil_lt_add_one (by positivity : 0≤1073741824*log (p:ℝ)*log (log p))
  change (resolution p:ℝ)<_ at hm
  have hprod := mul_le_mul hu hv (by norm_num : 0≤(1:ℝ)) (by linarith)
  have hMu : 4*(resolution p:ℝ)≤(2:ℝ)^33*(log p*log (log p)) := by
    norm_num
    linarith only [hm,hprod]
  have hlog : ((Nat.log 2 p:ℕ):ℝ)+1≤3*log p := by change (depth p:ℝ)+1≤_;linarith only [ht,hu]
  exact hc.trans ((mul_le_mul hlog hMu (by positivity) (by positivity)).trans (by
    norm_num
    nlinarith only [mul_nonneg (sq_nonneg (log (p:ℝ))) (show 0≤log (log (p:ℝ)) by linarith)]))

private theorem round {p N : ℕ} [Fact p.Prime] (hM : 4≤resolution p)
    {δ : ℝ} (hw : window p N δ) (hn : 1<(N:ℝ)) (hl : 1≤log (log (N:ℝ))) {a : ZMod p}
    (ha : a≠0) (hs : signal N a) :
    ∃ n∈tests p δ, n≤N ∧ 3*N≤4*n ∧ large p n := by
  obtain ⟨n,hgrid,h₁,hgap,hs'⟩ := detect hw.2.2.le hl hn hs
  have hh := (Nat.mul_le_mul_right (N-n) hM).trans hgap
  have h₃ : 3*N≤4*n := by omega
  refine ⟨n,mem_filter.mpr ⟨hgrid,?_,?_,h₁.trans_lt hw.2.2⟩,h₁,h₃,a,ha,hs'⟩
  · exact (mul_le_mul_of_nonneg_left hw.1 (by norm_num : (0:ℝ)≤3)).trans (by exact_mod_cast h₃)
  · exact (Nat.cast_le.mpr h₁).trans hw.2.1

theorem witness {δ : ℝ} (hδ : 0<δ) : ∀ᶠ p : ℕ in atTop, ∀ hp : p.Prime, _root_.Odd p →
    letI : Fact p.Prime := ⟨hp⟩
    (S p:ℝ)≤(p:ℝ)*log p/100 → ∃ n∈tests p δ, large p n := by
  filter_upwards [ThetaReciprocalResonance.witness hδ,controls] with p hh hc
  intro hp ho
  let : Fact p.Prime := ⟨hp⟩
  intro hS
  obtain ⟨N,hwin,a,ha,hs⟩ := hh hp ho hS
  obtain ⟨hn,hl⟩ := hc.2 N hwin.1
  obtain ⟨n,hm,_,_,hg⟩ := round hc.1 hwin hn hl ha hs
  exact ⟨n,hm,hg⟩

theorem growth {δ : ℝ} (hδ : 0<δ)
    (hcancel : ∀ᶠ p : ℕ in atTop, ∀ hp : p.Prime, _root_.Odd p →
      letI : Fact p.Prime := ⟨hp⟩
      ∀ n∈tests p δ, ¬large p n) (n : ℕ) : type_of% (conjecture_4_4 n) := by
  have hlog := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [witness hδ,hcancel,hlog.eventually_gt_atTop (100*(n:ℝ))] with p hh hd hl
  intro hp ho
  let : Fact p.Prime := ⟨hp⟩
  have hS : (p:ℝ)*log p/100<(S p:ℝ) := by
    by_contra! hs
    obtain ⟨m,hm,hlarge⟩ := hh hp ho hs
    exact hd hp ho m hm hlarge
  change 100*(n:ℝ)<log (p:ℝ) at hl
  have ht := mul_lt_mul_of_pos_right hl (Nat.cast_pos.mpr hp.pos : 0<(p:ℝ))
  exact_mod_cast (show (n:ℝ)*(p:ℝ)<(S p:ℝ) by linarith)

/-- Rounding each length down by at most a quarter preserves the count and
changes factor-two spacing to factor-three-halves spacing. -/
theorem image_separated (E : Finset ℕ) (f : ℕ → ℕ) (hs : separated E)
    (hf : ∀ n∈E, f n≤n ∧ 3*n≤4*f n) :
    (E.image f).card=E.card ∧
    ∀ n m : ℕ, n∈E.image f → m∈E.image f → n < m → 3*n≤2*m := by
  have hord (n m : ℕ) (hn : n∈E) (hm : m∈E) (hlt : n < m) : f n < f m ∧ 3*f n≤2*f m := by
    obtain ⟨h₁,h₂⟩ := hf n hn
    obtain ⟨h₃,h₄⟩ := hf m hm
    have h := hs n m hn hm hlt
    omega
  constructor
  · apply card_image_of_injOn
    intro n hn m hm h
    rcases lt_trichotomy n m with hl|he|hl
    · exact ((hord n m hn hm hl).1.ne h).elim
    · exact he
    · exact ((hord m n hm hn hl).1.ne h.symm).elim
  intro n m hn hm hlt
  obtain ⟨x,hx,rfl⟩ := mem_image.mp hn
  obtain ⟨y,hy,rfl⟩ := mem_image.mp hm
  rcases lt_trichotomy x y with h|h|h
  · exact (hord x y hx hy h).2
  · simp [h] at hlt
  · exact ((hord y x hy hx h).1.not_gt hlt).elim

/-- A small original sum forces many distinct positive tests on the same deterministic
grid, with a margin at both logarithmic endpoints. -/
theorem many_tests (estimate : InitialSumEstimate) : ∃ b : ℝ, 0<b ∧
    ∀ᶠ p : ℕ in atTop, ∀ hp : p.Prime, _root_.Odd p →
      letI : Fact p.Prime := ⟨hp⟩
      ∀ B : ℝ, 0<B → (∀ t a : ZMod p, a≠0 → ‖ThetaReciprocalCutoff.kloosterman t a‖≤2*B) →
        (S p:ℝ)≤(p:ℝ)*log p/100 →
        let d := b*ThetaInteriorResonance.weight (log p)
        ∃ G⊆tests p 1, 8*d≤G.card ∧
          (∀ n∈G, large p n ∧ 3*exp (sqrt (log p)/512+d)≤4*(n:ℝ) ∧ (n:ℝ)≤B*exp (-d)) ∧
          ∀ n m : ℕ, n∈G → m∈G → n < m → 3*n≤2*m := by
  classical
  obtain ⟨b,hb,H⟩ := ThetaInteriorResonance.interior estimate
  refine ⟨b,hb,?_⟩
  filter_upwards [H,controls] with p hh hc
  intro hp ho
  let : Fact p.Prime := ⟨hp⟩
  intro B hB hK hS
  obtain ⟨E,hE,hsep,hband,hsize⟩ := hh hp ho B hB hK hS
  have hround (N : ℕ) (h : N∈E) : ∃ n∈tests p 1, n≤N ∧ 3*N≤4*n ∧ large p n := by
    obtain ⟨_,hw,a,ha,hs⟩ := mem_filter.mp (hE h)
    obtain ⟨hn,hl⟩ := hc.2 N hw.1
    exact round hc.1 hw hn hl ha hs
  choose g hg hlo hhi hlarge using hround
  let f (n : ℕ) := if h : n∈E then g n h else 0
  have hval {n : ℕ} (hn : n∈E) : f n=g n hn := dif_pos hn
  obtain ⟨hcard,hs⟩ := image_separated E f hsep (fun n hn => by rw [hval hn]; exact ⟨hlo n hn,hhi n hn⟩)
  refine ⟨E.image f,?_,hcard ▸ hsize,?_,hs⟩
  · intro n hn
    obtain ⟨m,hm,rfl⟩ := mem_image.mp hn
    exact (hval hm) ▸ hg m hm
  · intro n hn
    obtain ⟨m,hm,rfl⟩ := mem_image.mp hn
    rw [hval hm]
    obtain ⟨hl,hu⟩ := hband m hm
    exact ⟨hlarge m hm,(mul_le_mul_of_nonneg_left hl (by norm_num : (0:ℝ)≤3)).trans
      (by exact_mod_cast hhi m hm),(Nat.cast_le.mpr (hlo m hm)).trans hu⟩

#print axioms image_separated
#print axioms many_tests

#print axioms test_count
#print axioms witness
#print axioms growth
end
end Arxiv.«2501.03234».ThetaMeshObstruction
