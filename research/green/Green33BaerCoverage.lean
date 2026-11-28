import Green33BaerLayers
/-! Coverage and repair bounds for cyclic doubles with a balanced Baer coset. -/
open Finset Green33PerfectDifferenceCenters Green33SingerBlockingLayers
open scoped Pointwise
namespace Green33BaerLayers

private theorem density_error {t h j n b : ℕ} (pos : 0<t)
    (hl : h=t^2+t+1) (jr : j+t=t^2+1) (cap : b≤t^2+t)
    (count : 2*n=2*(t+j*(t^2+1))+(t^2+1)*(t^2+2)+b) :
    |(n:ℝ)/(2*h*j)-3/4|≤2/(t:ℝ) := by
  have x : (1:ℝ)≤t := by exact_mod_cast pos
  have h1:=congrArg (Nat.cast (R:=ℝ)) hl
  have j1:=congrArg (Nat.cast (R:=ℝ)) jr
  have n1:=congrArg (Nat.cast (R:=ℝ)) count
  push_cast at h1 j1 n1
  have j2 : (j:ℝ)=(t:ℝ)^2-t+1 := by linarith only [j1]
  have v : (h:ℝ)*j=(t:ℝ)^4+t^2+1 := by rw [h1,j2];ring
  have count' : 2*(n:ℝ)=3*(t:ℝ)^4-2*t^3+7*t^2+4+b := by rw [n1,j2];ring
  have bound : (b:ℝ)≤(t:ℝ)^2+t := by exact_mod_cast cap
  have power (i : ℕ) : (t:ℝ)^i≤(t:ℝ)^(i+1) := by
    rw [pow_succ];exact le_mul_of_one_le_right (by positivity) x
  have tn : (0:ℝ)<t := by positivity
  have vp : 0<(h:ℝ)*j := by rw [v];positivity
  have hn : (h:ℝ)≠0 := (mul_ne_zero_iff.mp vp.ne').1
  have jn : (j:ℝ)≠0 := (mul_ne_zero_iff.mp vp.ne').2
  rw [show (n:ℝ)/(2*h*j)-3/4=(2*n-3*(h*j))/(4*(h*j)) by field_simp [hn,jn];ring,
    abs_div,abs_of_pos (mul_pos (by norm_num) vp),div_le_div_iff₀ (mul_pos (by norm_num) vp) tn,
    ←abs_of_pos tn,←abs_mul,abs_le,v,count']
  constructor <;> nlinarith only [power 0,power 1,power 2,power 3,mul_le_mul_of_nonneg_right bound tn.le,
    mul_nonneg (Nat.cast_nonneg b) tn.le]

open Filter
open scoped Topology

/-- Every growing square-order family, with any balanced subset of any one
Baer coset in its odd layer, covers asymptotically three quarters of the double. -/
theorem cyclic_density (t : ℕ→ℕ) (h j : ℕ→ℕ+) (pos : ∀ i,0<t i)
    (hl : ∀ i,(h i).val=(t i)^2+t i+1) (jr : ∀ i,(j i).val+t i=(t i)^2+1)
    (D B : (i : ℕ)→Finset (ZMod (h i*j i : ℕ+)))
    (perfect : ∀ i,Perfect (D i)) (size : ∀ i,(D i).card=(t i)^2+1)
    (bal : ∀ i,(B i).card=(t i)^2+1)
    (support : ∀ i, ∃ s, ∀ z∈B i,(chart _ _ _ (hl i) (jr i) z).2=s)
    (big : Tendsto t atTop atTop) :
    Tendsto (fun i => ((split (D i) (B i)+split (D i) (B i)).card:ℝ)/
      (2*(h i).val*(j i).val)) atTop (𝓝 (3/4)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have zero := (tendsto_const_nhds (x:=(2:ℝ))).div_atTop (tendsto_natCast_atTop_atTop.comp big)
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) (Eventually.of_forall ?_) zero
  intro i
  obtain ⟨s,hs⟩:=support i
  have eq:=cyclic_coverage (chart _ _ _ (hl i) (jr i)) (D i) (B i) (pos i) (perfect i) (size i)
    (bal i) (by simpa only [ZMod.card] using hl i) (by simpa only [ZMod.card] using jr i) s hs
  simp only [ZMod.card] at eq
  change ‖((split (D i) (B i)+split (D i) (B i)).card:ℝ)/(2*(h i).val*(j i).val)-3/4‖≤2/(t i:ℝ)
  rw [Real.norm_eq_abs]
  exact density_error (pos i) (hl i) (jr i) (by split <;> omega) eq

#print axioms cyclic_density

/-- A completion must supply a fresh unordered pair for each missing residue.
Here both cardinalities are normalized in the ambient cyclic group. -/
theorem completion_floor (N : ℕ→ℕ+) (R T : ∀ i, Finset (ZMod (N i)))
    (sub : ∀ i,R i⊆T i) (full : ∀ i,T i+T i=univ)
    (big : Tendsto (fun i => (N i).val) atTop atTop) {σ ρ : ℝ}
    (seed : Tendsto (fun i => ((R i).card:ℝ)/Real.sqrt (N i).val) atTop (𝓝 σ))
    (density : Tendsto (fun i => ((R i+R i).card:ℝ)/(N i).val) atTop (𝓝 ρ))
    {s : ℝ} (below : s<Real.sqrt (2*(1-ρ)+σ^2)) :
    ∀ᶠ i in atTop,s<((T i).card:ℝ)/Real.sqrt (N i).val := by
  let n (i : ℕ) : ℝ := (N i).val
  let a (i : ℕ) : ℝ := (R i).card
  let b (i : ℕ) : ℝ := (T i).card
  let holes (i : ℕ) : ℝ := n i-(R i+R i).card
  have pos (i) : 0<n i := by dsimp only [n];exact_mod_cast (N i).property
  have hn (i) : 0≤holes i := by
    have cap:=(R i+R i).card_le_univ
    rw [ZMod.card] at cap
    exact sub_nonneg.mpr (by dsimp only [n];exact_mod_cast cap)
  have h := (((tendsto_const_nhds (x:=(1:ℝ))).sub density).const_mul 2).add (seed.pow 2)
  have sq : Tendsto (fun i => 2*(holes i/n i)+(a i)^2/n i) atTop (𝓝 (2*(1-ρ)+σ^2)) := by
    apply h.congr
    intro i
    change 2*(1-((R i+R i).card:ℝ)/n i)+(a i/Real.sqrt (n i))^2=_
    rw [div_pow,Real.sq_sqrt (pos i).le]
    dsimp only [holes]
    rw [sub_div,div_self (pos i).ne']
  have nt : Tendsto n atTop atTop:=tendsto_natCast_atTop_atTop.comp big
  have lim:=sq.sqrt.sub ((tendsto_const_nhds (x:=(1:ℝ))).div_atTop (Real.tendsto_sqrt_atTop.comp nt))
  rw [sub_zero] at lim
  filter_upwards [lim.eventually_const_lt below] with i hi
  have cost:=Green33ReflectedLayers.extension_cost (sub i) (full i)
  rw [ZMod.card] at cost
  change 2*holes i+(a i)^2+a i≤(b i)^2+b i at cost
  have pa : 0≤a i := Nat.cast_nonneg _
  have pb : 0≤b i := Nat.cast_nonneg _
  have ph:=hn i
  have bound : Real.sqrt (2*holes i+(a i)^2)≤b i+1 :=
    Real.sqrt_le_iff.mpr ⟨by linarith,by nlinarith only [cost,pa,pb]⟩
  change s<Real.sqrt (2*(holes i/n i)+(a i)^2/n i)-1/Real.sqrt (n i) at hi
  rw [←mul_div_assoc,←add_div,Real.sqrt_div (by positivity),←sub_div] at hi
  exact hi.trans_le (div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg _))

#print axioms completion_floor

/-- The balanced seed attains the target size ratio. Every full cyclic basis
containing it has eventual size ratio above each constant below `sqrt (5/2)`. -/
theorem size_and_repair (t : ℕ→ℕ) (h j : ℕ→ℕ+) (pos : ∀ i,0<t i)
    (hl : ∀ i,(h i).val=(t i)^2+t i+1) (jr : ∀ i,(j i).val+t i=(t i)^2+1)
    (D B : (i : ℕ)→Finset (ZMod (h i*j i : ℕ+)))
    (perfect : ∀ i,Perfect (D i)) (size : ∀ i,(D i).card=(t i)^2+1)
    (bal : ∀ i,(B i).card=(t i)^2+1)
    (support : ∀ i, ∃ s, ∀ z∈B i,(chart _ _ _ (hl i) (jr i) z).2=s)
    (big : Tendsto t atTop atTop) :
    let v:=fun i => h i*j i
    let R:=fun i => split (D i) (B i)
    Tendsto (fun i => ((R i).card:ℝ)/Real.sqrt ((2*(v i).val:ℕ):ℝ)) atTop (𝓝 (Real.sqrt 2)) ∧
    ∀ T : ∀ i, Finset (ZMod (2*(v i).val)), (∀ i,R i⊆T i) → (∀ i,T i+T i=univ) →
      ∀ s : ℝ,s<Real.sqrt (5/2) → ∀ᶠ i in atTop, s<((T i).card:ℝ)/Real.sqrt ((2*(v i).val:ℕ):ℝ) := by
  let v (i) := h i*j i
  have grow : Tendsto (fun i => (v i).val) atTop atTop := by
    apply tendsto_atTop_mono (f:=t) _ big
    intro i
    change t i≤(h i).val*(j i).val
    have lower : t i≤(h i).val := by rw [hl];omega
    exact lower.trans (Nat.le_mul_of_pos_right _ (j i).property)
  have seed:=balanced_size_limit D B perfect (fun i => (bal i).trans (size i).symm) grow
  refine ⟨seed,?_⟩
  intro T sub full s below
  let N (i) : ℕ+ := 2*v i
  have bigN : Tendsto (fun i => (N i).val) atTop atTop := by
    apply tendsto_atTop_mono (f:=fun i => (v i).val) _ grow
    intro i; change _≤2*(v i).val; omega
  have dens:=cyclic_density t h j pos hl jr D B perfect size bal support big
  apply completion_floor N (fun i => split (D i) (B i)) T sub full bigN seed (ρ:=3/4)
  · apply dens.congr
    intro i
    change ((split (D i) (B i)+split (D i) (B i)).card:ℝ)/(2*(h i).val*(j i).val)=
      _/((2*((h i).val*(j i).val):ℕ):ℝ)
    simp only [Nat.cast_mul,Nat.cast_ofNat,mul_assoc]
    rfl
  · rwa [Real.sq_sqrt (by norm_num),show 2*(1-3/4)+2=(5/2:ℝ) by norm_num]

#print axioms size_and_repair
end Green33BaerLayers
