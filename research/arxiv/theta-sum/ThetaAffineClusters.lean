import ThetaClassOneClusters

/-! From an ordinary prime tuple at 8n+h to bounded positive clusters inside (X,X+H]. -/
namespace Arxiv.«2501.03234».ThetaAffineClusters
open Finset Real Filter ThetaPrimeClusterTransfer ThetaClassOneClusters
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- A lower count for ordinary prime clusters at eight times the base. -/
def Scaled (m D k : ℕ) (α : ℝ) : Prop :=
  ∀ᶠ x : ℕ in atTop, ∀ y : ℕ, (x:ℝ)^(5/8:ℝ)≤y → y≤x →
    α*y/(1+log x)^k≤(((Icc x (x+y)).filter (fun n => classCluster m D (8*n))).card:ℝ)

/-- Dilate the sieve bases, reserving room for the integer endpoints. -/
theorem ordinary_of_scaled {m D k : ℕ} {α : ℝ} (hα : 0<α) (scaled : Scaled m D k α) :
    Ordinary m D k (α/32) := by
  obtain ⟨x₀,hbase⟩ := eventually_atTop.mp scaled
  filter_upwards [eventually_ge_atTop (8*x₀),eventually_ge_atTop (32^24:ℕ)] with X hg hbig
  intro H hlow hhigh
  let x := X/8+1
  let y := H/16
  have hX : 32≤X := by omega
  have hx : 1≤x := Nat.succ_pos _
  have h₁ : x≤X := by dsimp [x];omega
  have ha : x₀≤x := by dsimp [x];omega
  have hgain : 32≤(X:ℝ)^(1/24:ℝ) := by
    have h := rpow_le_rpow (by positivity : 0≤(32:ℝ)^24)
      (show (32:ℝ)^24≤X by exact_mod_cast hbig) (by norm_num : (0:ℝ)≤1/24)
    rw [←rpow_natCast_mul (by norm_num : 0≤(32:ℝ))] at h
    norm_num at h
    exact h
  have hr : 32*(x:ℝ)^(5/8:ℝ)≤(H:ℝ) := calc
    _ ≤ (X:ℝ)^(1/24:ℝ)*(X:ℝ)^(5/8:ℝ) := mul_le_mul hgain
      (rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast h₁) (by norm_num)) (by positivity) (by positivity)
    _ = (X:ℝ)^(2/3:ℝ) := by rw [←rpow_add (by exact_mod_cast (show 0<X by omega))];norm_num
    _ ≤ _ := hlow
  have hpow : 1≤(x:ℝ)^(5/8:ℝ) := one_le_rpow (by exact_mod_cast hx) (by norm_num)
  have hH : 32≤H := by exact_mod_cast (by linarith : (32:ℝ)≤H)
  have h32 : H≤32*y := by dsimp [y];omega
  have hy : (x:ℝ)^(5/8:ℝ)≤y := by
    have h : (H:ℝ)≤32*(y:ℝ) := by exact_mod_cast h32
    linarith
  have h := hbase x ha y hy (by dsimp [x,y];omega)
  let A := (Icc x (x+y)).filter (fun n => classCluster m D (8*n))
  let B := (Ioc X (X+H)).filter (classCluster m D)
  have hc : A.card≤B.card := by
    apply card_le_card_of_injOn (fun n => 8*n)
    · intro n hn
      obtain ⟨hn,hc⟩ := mem_filter.mp hn
      obtain ⟨hlo,hhi⟩ := mem_Icc.mp hn
      refine mem_filter.mpr ⟨mem_Ioc.mpr ⟨?_,?_⟩,hc⟩ <;> dsimp [x,y] at * <;> omega
    · intro n _ m' _ he
      dsimp at he
      omega
  have hpos : 0<1+log (x:ℝ) := by linarith only [log_nonneg (by exact_mod_cast hx : 1≤(x:ℝ))]
  have hlog := log_le_log (by exact_mod_cast hx : 0<(x:ℝ)) (show (x:ℝ)≤X by exact_mod_cast h₁)
  change _≤(B.card:ℝ)
  apply le_trans _ (h.trans (by exact_mod_cast hc))
  apply div_le_div₀ (by positivity) _ (pow_pos hpos k) (pow_le_pow_left₀ hpos.le (by linarith) k)
  have hreal : (H:ℝ)≤32*(y:ℝ) := by exact_mod_cast h32
  nlinarith only [mul_le_mul_of_nonneg_left hreal hα.le]

/-- The whole cluster lies inside the prescribed interval, including all
intervening primes to which the theta inequality applies. -/
theorem contained {m D k : ℕ} {α c : ℝ} (hα : 0<α) (hc : c<1/2) (scaled : Scaled m D k α) :
    ∃ K : ℝ, 0<K ∧ ∀ᶠ X : ℕ in atTop, ∀ H : ℕ, 2*D≤H → H≤X →
    K*(X:ℝ)^(3/4:ℝ)*(1+log X)^(8+k)≤H →
    (α/128)*H/(1+log X)^k ≤ (((Ioc X (X+(H-D))).filter (positive c m D)).card:ℝ) := by
  obtain ⟨K,hK,hh⟩ := original (by positivity : 0<α/32) hc (ordinary_of_scaled hα scaled)
  refine ⟨2*K,by positivity,?_⟩
  filter_upwards [hh] with X hX
  intro H hD hHX hsize
  have hhalf : (H:ℝ)≤2*((H-D:ℕ):ℝ) := by exact_mod_cast (by omega : H≤2*(H-D))
  have hlen : K*(X:ℝ)^(3/4:ℝ)*(1+log X)^(8+k)≤((H-D:ℕ):ℝ) := by linarith only [hsize,hhalf]
  apply le_trans _ (hX (H-D) hlen (by omega) (by omega))
  apply div_le_div_of_nonneg_right _ (pow_nonneg (by
    by_cases h : X=0
    · simp [h]
    · linarith only [log_nonneg (by exact_mod_cast (Nat.pos_of_ne_zero h) : 1≤(X:ℝ))]) k)
  nlinarith only [mul_le_mul_of_nonneg_left hhalf hα.le]

#print axioms ordinary_of_scaled
#print axioms contained
end
end Arxiv.«2501.03234».ThetaAffineClusters
