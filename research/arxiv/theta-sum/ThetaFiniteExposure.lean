import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Finite partition averages and the exponential bound for one refinement. -/
namespace Arxiv.«2501.03234».ThetaFiniteExposure
open Finset Real
noncomputable section
variable {Ω : Type*} [Fintype Ω]
open Classical in
def fiber (key : Ω → ℕ) (r : ℕ) := univ.filter (fun x => key x=r)
def avg (A : Finset Ω) (f : Ω → ℝ) := (∑ x∈A,f x)/A.card
def proj (key : Ω → ℕ) (f : Ω → ℝ) (x : Ω) := avg (fiber key (key x)) f

theorem fiber_nonempty (key : Ω → ℕ) (x : Ω) : (fiber key (key x)).Nonempty :=
  ⟨x,mem_filter.mpr ⟨mem_univ _,rfl⟩⟩

theorem weighted (key : Ω → ℕ) (f w : Ω → ℝ)
    (hw : ∀ x y, key x=key y → w x=w y) :
    ∑ x,w x*proj key f x=∑ x,w x*f x := by
  classical
  let R := univ.image key
  have hm : ∀ x∈univ,key x∈R := fun x hx => mem_image.mpr ⟨x,hx,rfl⟩
  rw [←sum_fiberwise_of_maps_to hm,←sum_fiberwise_of_maps_to hm (fun x => w x*f x)]
  apply sum_congr rfl
  intro r hr
  obtain ⟨a,_,rfl⟩ := mem_image.mp hr
  let A := fiber key (key a)
  have hcard : 0<(A.card:ℝ) := Nat.cast_pos.mpr (card_pos.mpr (fiber_nonempty key a))
  have eqn (x : Ω) (hx : x∈A) : key x=key a := (mem_filter.mp hx).2
  change (∑ x∈A,w x*proj key f x)=∑ x∈A,w x*f x
  calc
    _ = ∑ _x∈A,w a*avg A f := sum_congr rfl (fun x hx => by rw [hw x a (eqn x hx),proj,eqn x hx])
    _ = w a*∑ x∈A,f x := by simp only [sum_const,nsmul_eq_mul,avg];field_simp
    _ = _ := by rw [mul_sum];exact sum_congr rfl fun x hx => by rw [hw x a (eqn x hx)]

theorem tower (k l : Ω → ℕ) (f : Ω → ℝ) (href : ∀ x y,l x=l y → k x=k y) (x : Ω) :
    proj k (proj l f) x=proj k f x := by
  classical
  let w (y : Ω) : ℝ := if k y=k x then 1 else 0
  have H := weighted l f w (fun a b hab => by dsimp [w];rw [href a b hab])
  have eqn (g : Ω → ℝ) : (∑ y,w y*g y) = ∑ y∈fiber k (k x),g y := by
    unfold fiber
    rw [sum_filter]
    apply sum_congr rfl
    intro j _
    simp only [w,ite_mul,one_mul,zero_mul]
  change (∑ y∈fiber k (k x),proj l f y)/_=(∑ y∈fiber k (k x),f y)/_
  rw [←eqn,←eqn,H]

theorem increment (k l : Ω → ℕ) (f : Ω → ℝ) (href : ∀ x y,l x=l y → k x=k y)
    {a : ℝ} (h : ∀ x y,k x=k y → |proj l f x-proj l f y|≤a) (x : Ω) :
    |proj l f x-proj k f x|≤a := by
  classical
  rw [←tower k l f href x]
  let A := fiber k (k x)
  have hcard : 0<(A.card:ℝ) := Nat.cast_pos.mpr (card_pos.mpr (fiber_nonempty k x))
  change |proj l f x-(∑ y∈A,proj l f y)/(A.card:ℝ)|≤_
  have he : proj l f x-(∑ y∈A,proj l f y)/(A.card:ℝ)=
      (∑ y∈A,(proj l f x-proj l f y))/(A.card:ℝ) := by
    rw [sum_sub_distrib,sum_const,nsmul_eq_mul];field_simp
  rw [he,abs_div,abs_of_pos hcard]
  apply (div_le_iff₀ hcard).mpr
  calc
    _ ≤ ∑ y∈A,|proj l f x-proj l f y| := abs_sum_le_sum_abs ..
    _ ≤ ∑ _y∈A,a := sum_le_sum fun y hy => h x y (mem_filter.mp hy).2.symm
    _ = _ := by simp [mul_comm]

theorem step_weighted (k l : Ω → ℕ) (f : Ω → ℝ) (href : ∀ x y,l x=l y → k x=k y)
    (weight : Ω → ℝ) (hn : ∀ x,0≤weight x) (fixed : ∀ x y,k x=k y → weight x=weight y)
    {a v : ℝ} (_ha : 0≤a) (hs : |v| * a≤1) (h : ∀ x y,k x=k y → |proj l f x-proj l f y|≤a) :
    (∑ x,weight x*exp (v*proj l f x)) ≤ exp (v^2*a^2)*∑ x,weight x*exp (v*proj k f x) := by
  classical
  let w := fun x => weight x*exp (v*proj k f x)
  let d := fun x => proj l f x-proj k f x
  have hw (x y : Ω) (he : k x=k y) : w x=w y := by simp only [w,proj,he,fixed x y he]
  have hz : (∑ x,w x*d x)=0 := by
    simp only [d,mul_sub,sum_sub_distrib]
    rw [weighted l f w (fun x y he => hw x y (href x y he)),weighted k f w hw,sub_self]
  have hloc (x : Ω) : weight x*exp (v*proj l f x) ≤ w x*(1+v*d x+v^2*a^2) := by
    have hd := increment k l f href h x
    change |d x|≤a at hd
    have hab : |v*d x|≤1 := (abs_mul v (d x)).le.trans ((mul_le_mul_of_nonneg_left hd (abs_nonneg v)).trans hs)
    have he := (le_abs_self _).trans (Real.abs_exp_sub_one_sub_id_le hab)
    have hh := pow_le_pow_left₀ (abs_nonneg _) hd 2
    rw [sq_abs] at hh
    have hsq := mul_le_mul_of_nonneg_left hh (sq_nonneg v)
    rw [show v*proj l f x=v*proj k f x+v*d x by dsimp [d];ring,exp_add]
    rw [←mul_assoc]; exact mul_le_mul_of_nonneg_left (by nlinarith only [he,hsq]) (mul_nonneg (hn _) (exp_pos _).le)
  apply (sum_le_sum fun x _ => hloc x).trans
  calc
    _ = (1+v^2*a^2)*(∑ x,w x)+v*∑ x,w x*d x := by
      rw [mul_sum,mul_sum,←sum_add_distrib];apply sum_congr rfl;intros;ring
    _ ≤ _ := by
      rw [hz,mul_zero,add_zero]
      exact mul_le_mul_of_nonneg_right (by linarith only [add_one_le_exp (v^2*a^2)])
        (sum_nonneg fun x _ => mul_nonneg (hn _) (exp_pos _).le)

theorem step (k l : Ω → ℕ) (f : Ω → ℝ) (href : ∀ x y,l x=l y → k x=k y)
    {a v : ℝ} (ha : 0≤a) (hs : |v| * a≤1) (h : ∀ x y,k x=k y → |proj l f x-proj l f y|≤a) :
    (∑ x,exp (v*proj l f x)) ≤ exp (v^2*a^2)*∑ x,exp (v*proj k f x) := by
  simpa using step_weighted k l f href (fun _ => 1) (fun _ => zero_le_one) (fun _ _ _ => rfl) ha hs h

#print axioms increment
#print axioms step_weighted
#print axioms step
end
end Arxiv.«2501.03234».ThetaFiniteExposure
