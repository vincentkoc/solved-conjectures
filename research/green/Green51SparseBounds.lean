import Green51SparseDimensions
import Green50BCH
import FormalConjectures.GreensOpenProblems.«51»

/-! # Sparse ranges of Green's guaranteed sumset dimension -/

open Finset Green50Sharp Green50Downsets Green51SparseDimensions
open scoped Classical Pointwise
namespace Green51SparseBounds
local notation "F" => ZMod 2

private theorem padded_check {n m t : ℕ} (ht : 0 < t) (hm : 0 < m) (fits : t*m≤n) :
    ∃ N : ℕ, ∃ P : Cube N →ₗ[F] Cube n,
      (∀ z, (supp z).card≤2*t → P z=0 → z=0) ∧ ((ball N 1).image P).card=2^m := by
  obtain ⟨N,Q,kernel,size⟩ := Green50BCH.sparse_check_map t m ht hm
  let J : Cube (t*m) →ₗ[F] Cube n :=
    { toFun := fun x i => if h : i.val<t*m then x ⟨i.val,h⟩ else 0
      map_add' := by intro x y; funext i; split <;> simp [*]
      map_smul' := by intro c y; funext i; split <;> simp [*] }
  have inj : Function.Injective J := by
    intro x y eq
    funext i
    simpa [J,i.isLt] using congrFun eq (i.castLE fits)
  refine ⟨N,J.comp Q,fun z hz eq => kernel z hz (inj (eq.trans J.map_zero.symm)),?_⟩
  change ((ball N 1).image (J ∘ Q)).card=_
  rw [← image_image,card_image_of_injective _ inj,size]

private theorem double_image {N n : ℕ} (P : Cube N →ₗ[F] Cube n) :
    (ball N 1).image P+(ball N 1).image P⊆(ball N 2).image P := by
  rw [←two_nsmul,←image_nsmul]
  apply image_subset_image
  intro z hz
  exact mem_filter.mpr ⟨mem_univ _,by simpa using weight_of_mem_sum hz⟩

/-- In every dimension at least three, a double of a set of size
2^floor(n/3) can exclude every three-dimensional linear space. -/
theorem linear_examples (n : ℕ) (hn : 3≤n) :
    ∃ A : Finset (Cube n), A.card=2^(n/3) ∧
      ∀ W : Submodule F (Cube n), (∀ w∈W,w∈A+A) → Module.finrank F W≤2 := by
  obtain ⟨N,P,kernel,size⟩ := padded_check (n:=n) (t:=3) (m:=n/3) (by decide) (by omega) (by omega)
  refine ⟨_,size,fun W inside => sparse_linear_flat P kernel W ?_⟩
  exact fun w hw => double_image P (inside w hw)

/-- Four BCH coordinates exclude every three-dimensional affine space in a
double of a set of size 2^floor(n/4), for every n≥4. -/
theorem affine_examples (n : ℕ) (hn : 4≤n) :
    ∃ A : Finset (Cube n), A.card=2^(n/4) ∧
      ∀ (W : Submodule F (Cube n)) (x : Cube n),
        x +ᵥ (W : Set (Cube n)) ⊆ ↑(A+A) → Module.finrank F W≤2 := by
  obtain ⟨N,P,kernel,size⟩ := padded_check (n:=n) (t:=4) (m:=n/4) (by decide) (by omega) (by omega)
  refine ⟨_,size,fun W x h => Green50BCH.sparse_image_flat P kernel W x (h.trans (double_image P))⟩

private theorem plane {n : ℕ} (A : Finset (Cube n)) (large : 3≤A.card) :
    ∃ W : Submodule F (Cube n), Module.finrank F W=2 ∧ ∀ w∈W,w∈A+A := by
  obtain ⟨T,sub,size⟩ := exists_subset_card_eq large
  obtain ⟨a,b,c,ab,ac,bc,rfl⟩ := card_eq_three.mp size
  obtain ⟨ha,hb,hc⟩ : a∈A ∧ b∈A ∧ c∈A := by simpa only [insert_subset_iff,singleton_subset_iff] using sub
  let L : (Fin 2 → F) →ₗ[F] Cube n := Fintype.linearCombination F ![a+b,a+c]
  have eval (v : Fin 2 → F) : L v=v 0 • (a+b)+v 1 • (a+c) := by
    simp [L,Fintype.linearCombination_apply,Fin.sum_univ_two]
  have pair : (a+b)+(a+c)=b+c := by rw [add_add_add_comm,ZModModule.add_self,zero_add]
  have bit (u : F) : u=0 ∨ u=1 := (show ∀ t:F,t=0 ∨ t=1 from by decide) u
  have nz {u v : Cube n} (ne : u≠v) : u+v≠0 := fun eq =>
    ne (add_right_cancel (eq.trans (ZModModule.add_self v).symm))
  have inj : Function.Injective L := by
    apply (injective_iff_map_eq_zero L).mpr
    intro v hv
    rcases bit (v 0) with h0|h0 <;> rcases bit (v 1) with h1|h1 <;>
      simp [eval,h0,h1,pair,nz ab,nz ac,nz bc] at hv
    funext i; fin_cases i <;> assumption
  refine ⟨L.range,by rw [L.finrank_range_of_inj inj]; simp,?_⟩
  rintro _ ⟨v,rfl⟩
  rcases bit (v 0) with h0|h0 <;> rcases bit (v 1) with h1|h1 <;>
    simp only [eval,h0,h1,zero_smul,one_smul,zero_add,add_zero,pair]
  · exact (ZModModule.add_self a) ▸ add_mem_add ha ha
  · exact add_mem_add ha hc
  · exact add_mem_add ha hb
  · exact add_mem_add hb hc

/-- The largest size of a set whose double avoids every linear three-space. -/
noncomputable def linearAvoidanceSize (n : ℕ) : ℕ :=
  (univ.filter fun A : Finset (Cube n) =>
    ¬∃ W : Submodule F (Cube n), Module.finrank F W=3 ∧ ∀ w∈W,w∈A+A).sup card

/-- The linear avoidance threshold has exponential scale 2^(n/3) with
absolute constants in every dimension at least three. -/
theorem linear_size_bounds (n : ℕ) (hn : 3≤n) :
    2^(n/3)≤linearAvoidanceSize n ∧ linearAvoidanceSize n≤4*2^(n/3) := by
  classical
  let L := 2^(n/3)
  have two : 2≤L := Nat.le_self_pow (show n/3≠0 by omega) 2
  constructor
  · obtain ⟨A,sz,flat⟩ := linear_examples n hn
    rw [←sz]
    apply le_sup (f:=card)
    refine mem_filter.mpr ⟨mem_univ _,?_⟩
    rintro ⟨W,h,inside⟩
    have := flat W inside
    omega
  · apply Finset.sup_le
    intro A ha
    change A.card≤4*L
    by_cases large : 5≤A.card
    · have packed := triple_packing A large (mem_filter.mp ha).2
      have cube : Fintype.card (Cube n)=2^n := by simp [Cube]
      rw [cube] at packed
      have prod := A.card.pow_sub_le_descFactorial 3
      rw [Nat.descFactorial_eq_factorial_mul_choose] at prod
      have fac : Nat.factorial 3=6 := by decide
      rw [fac,show A.card+1-3=A.card-2 by omega] at prod
      have powBound : (A.card-2)^3≤6*2^n := by omega
      have rem : 2^(n%3)≤4 := Nat.pow_le_pow_right (by decide) (show n%3≤2 by omega)
      have split : 2^n=2^(n%3)*L^3 := by
        dsimp [L]; rw [←pow_mul,←pow_add]; congr 1; omega
      have ub : (A.card-2)^3≤(3*L)^3 := calc
        _ ≤ 6*2^n := powBound
        _ = 6*(2^(n%3)*L^3) := by rw [split]
        _ ≤ 6*(4*L^3) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ rem)
        _ ≤ _ := by rw [mul_pow]; omega
      have root : A.card-2≤3*L := by
        by_contra! h
        exact (not_lt_of_ge ub) (Nat.pow_lt_pow_left h (by decide))
      omega
    · omega

open Filter Topology in
/-- The base-two exponential growth rate of the largest linear-three-space
avoiding set is exactly one third. -/
theorem linear_growth_rate :
    Tendsto (fun n : ℕ => Real.log (linearAvoidanceSize n)/(n:ℝ)) atTop (𝓝 (Real.log 2/3)) := by
  let c := Real.log 2/3
  have vanish (a : ℝ) : Tendsto (fun n : ℕ => a/(n:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have bounds : ∀ᶠ n : ℕ in atTop,
      c-Real.log 2/n ≤ Real.log (linearAvoidanceSize n)/n ∧
      Real.log (linearAvoidanceSize n)/n ≤ c+Real.log 4/n := by
    filter_upwards [eventually_ge_atTop 3] with n hn
    obtain ⟨lo,hi⟩ := linear_size_bounds n hn
    have pos : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
    have lower : (2:ℝ)^(n/3 : ℕ)≤linearAvoidanceSize n := by exact_mod_cast lo
    have upper : (linearAvoidanceSize n : ℝ)≤4*(2:ℝ)^(n/3 : ℕ) := by exact_mod_cast hi
    have l := Real.log_le_log (by positivity) lower
    have u := Real.log_le_log (lt_of_lt_of_le (by positivity) lower) upper
    rw [Real.log_pow] at l
    rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow] at u
    have a : (3:ℝ)*(↑(n/3 : ℕ):ℝ)≤n := by exact_mod_cast (show 3*(n/3)≤n by omega)
    have b : (n:ℝ)≤3*(↑(n/3 : ℕ):ℝ)+3 := by exact_mod_cast (show n≤3*(n/3)+3 by omega)
    have logpos : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
    dsimp only [c]
    constructor
    · rw [le_div_iff₀ pos,sub_mul,div_mul_cancel₀ _ pos.ne']
      nlinarith [mul_le_mul_of_nonneg_right b logpos]
    · rw [div_le_iff₀ pos,add_mul,div_mul_cancel₀ _ pos.ne']
      nlinarith [mul_le_mul_of_nonneg_right a logpos]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' _ _ (bounds.mono fun _ h => h.1) (bounds.mono fun _ h => h.2)
  · simpa only [sub_zero] using (tendsto_const_nhds (x:=c)).sub (vanish (Real.log 2))
  · simpa only [add_zero] using (tendsto_const_nhds (x:=c)).add (vanish (Real.log 4))

private theorem density {n : ℕ} (A : Finset (𝔽₂ n)) :
    (A.dens : ℝ) = (A.card : ℝ)/2^n := by
  rw [nnratCast_dens]
  simp [𝔽₂,𝔽]

private theorem guarantee_of_linear {n d : ℕ} {α : ℝ} (one : α≤1)
    (each : ∀ A : Finset (𝔽₂ n), α≤(A.dens : ℝ) →
      ∃ W : Submodule F (𝔽₂ n), Module.finrank F W=d ∧ ∀ w∈W,w∈A+A) :
    d≤Green51.guaranteedMaxCosetDim n α := by
  classical
  unfold Green51.guaranteedMaxCosetDim
  apply le_csInf
  · refine ⟨_,univ,?_,rfl⟩; simpa using one
  · rintro _ ⟨A,ha,rfl⟩
    obtain ⟨W,rank,inside⟩ := each A ha
    apply le_csSup
    · refine ⟨Module.finrank F (𝔽₂ n),?_⟩
      rintro _ ⟨S,_,rfl⟩; exact Submodule.finrank_le _
    · exact ⟨W.toAffineSubspace,fun _ h => inside _ h,by rwa [Submodule.toAffineSubspace_direction]⟩

/-- Green's affine guarantee is exactly two on this sparse density interval,
including its upper endpoint. -/
theorem sparse_plateau {n : ℕ} (hn : 4≤n) {α : ℝ}
    (lo : 2/(2:ℝ)^n<α) (hi : α≤(2:ℝ)^(n/4)/2^n) :
    Green51.guaranteedMaxCosetDim n α=2 := by
  classical
  obtain ⟨A,size,avoid⟩ := affine_examples n hn
  have admitted : α≤(A.dens : ℝ) := by rw [density,size]; exact_mod_cast hi
  apply le_antisymm
  · have candidate : Green51.guaranteedMaxCosetDim n α ≤ maxCosetDim F (𝔽₂ n) ↑(A+A) :=
      csInf_le (OrderBot.bddBelow _) ⟨A,admitted,rfl⟩
    apply candidate.trans
    apply csSup_le
    · exact ⟨0,⊥,by simp,by simp⟩
    · rintro _ ⟨S,inside,rfl⟩
      by_cases non : ∃ x,x∈S
      · obtain ⟨x,hx⟩ := non
        apply avoid S.direction x
        rintro _ ⟨w,hw,rfl⟩
        apply inside
        simpa [vadd_eq_add,add_comm] using AffineSubspace.vadd_mem_of_mem_direction hw hx
      · have bot : S=⊥ := by
          ext x; simp only [AffineSubspace.notMem_bot,iff_false]; exact fun hx => non ⟨x,hx⟩
        rw [bot,AffineSubspace.direction_bot]; simp
  · apply guarantee_of_linear (admitted.trans (by exact_mod_cast A.dens_le_one))
    intro B hb
    have l := lo.trans_le hb
    rw [density,div_lt_div_iff_of_pos_right (by positivity)] at l
    exact plane B (by exact_mod_cast l)

/-- The packing obstruction forces an affine three-space as soon as k
labels and their triples exceed the ambient cardinality. -/
theorem three_above_packing {n k : ℕ} (large : 5≤k) (fits : k≤2^n)
    (packed : 2^n<k+k.choose 3) :
    3≤Green51.guaranteedMaxCosetDim n ((k:ℝ)/2^n) := by
  apply guarantee_of_linear (by rw [div_le_one (by positivity)]; exact_mod_cast fits)
  intro A h
  rw [density,div_le_div_iff_of_pos_right (by positivity)] at h
  have le : k≤A.card := by exact_mod_cast h
  by_contra avoid
  have bound := triple_packing A (large.trans le) avoid
  have cube : Fintype.card (𝔽₂ n)=2^n := by simp [𝔽₂,𝔽]
  rw [cube] at bound
  exact (not_lt_of_ge bound) (packed.trans_le (Nat.add_le_add le (Nat.choose_le_choose _ le)))

end Green51SparseBounds

#print axioms Green51SparseBounds.linear_examples
#print axioms Green51SparseBounds.affine_examples
#print axioms Green51SparseBounds.linear_size_bounds
#print axioms Green51SparseBounds.linear_growth_rate
#print axioms Green51SparseBounds.sparse_plateau
#print axioms Green51SparseBounds.three_above_packing
