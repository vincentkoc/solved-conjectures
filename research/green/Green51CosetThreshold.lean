import Green51ThresholdExample
import FormalConjectures.GreensOpenProblems.«51»

/-! # Exact codimension-one range of Green's guaranteed coset dimension -/

open Finset Filter Real Green53ParityThreshold
open scoped Classical Pointwise
namespace Green51Hyperplane

/-- Half the mass of the middle layer in dimension `2*k`. -/
noncomputable def halfLayer (k : ℕ) : ℝ :=
  ((2*k).choose k : ℝ)/(2*2^(2*k : ℕ))

/-- The largest density at which a sumset can miss all affine hyperplanes. -/
noncomputable def threshold (n : ℕ) : ℝ := 1/2-halfLayer (n/2)

private theorem rescale (n : ℕ) (A : Finset (𝔽₂ n)) :
    (A.dens : ℝ)-threshold n =
    (2*(A.card : ℝ)+(2:ℝ)^(n%2)*((2*(n/2)).choose (n/2) : ℝ)-2^n)/(2*2^n) := by
  have split : (2:ℝ)^n=2^(n%2)*2^(2*(n/2)) := by rw [←pow_add,Nat.mod_add_div]
  rw [nnratCast_dens]
  simp only [𝔽₂,𝔽,Fintype.card_fun,Fintype.card_fin,ZMod.card]
  unfold threshold halfLayer
  push_cast
  rw [split]; field_simp; ring

/-- For each dimension at least two the strict inequality is exact, including
at the boundary, for the host's affine-coset extremal function. -/
theorem guaranteed_hyperplane_iff {n : ℕ} (hn : 2≤n) {α : ℝ} (hα : α≤1) :
    n ≤ Green51.guaranteedMaxCosetDim n α+1 ↔ threshold n<α := by
  classical
  let dim (A : Finset (𝔽₂ n)) := maxCosetDim F (𝔽₂ n) ((A+A : Finset _) : Set _)
  let dims : Set ℕ := {t | ∃ A : Finset (𝔽₂ n), (A.dens : ℝ)≥α ∧ dim A=t}
  have defn : Green51.guaranteedMaxCosetDim n α=sInf dims := by
    unfold Green51.guaranteedMaxCosetDim
    congr 1
    ext t
    simp [dims,dim]
  rw [defn]
  constructor
  · intro h
    by_contra! small
    obtain ⟨A,size,avoid⟩ := extremal_example n
    have eq : (A.dens : ℝ)=threshold n := by
      apply sub_eq_zero.mp
      rw [rescale]; have hh : 2*(A.card : ℝ)+(2:ℝ)^(n%2)*((2*(n/2)).choose (n/2) : ℝ)=2^n := by exact_mod_cast size
      rw [hh,sub_self,zero_div]
    have member : dim A∈dims := ⟨A,by rwa [eq],rfl⟩
    have lo := csInf_le (OrderBot.bddBelow _) member
    have ub : dim A ≤ n-2 := by
      apply csSup_le
      · exact ⟨0,⊥,by simp,by simp⟩
      · rintro _ ⟨S,sub,rfl⟩
        by_cases non : ∃ x,x∈S
        · have lt : Module.finrank F S.direction+1<n := avoid S non (fun _ hx => sub hx)
          exact Nat.le_sub_of_add_le lt
        · have bot : S=⊥ := by
            ext x; simp only [AffineSubspace.notMem_bot,iff_false]; exact fun hx => non ⟨x,hx⟩
          rw [bot,AffineSubspace.direction_bot]; simp
    omega
  · intro h
    have non : dims.Nonempty := ⟨dim univ,univ,by simpa using hα,rfl⟩
    suffices n-1 ≤ sInf dims by omega
    apply le_csInf non
    rintro _ ⟨A,ha,rfl⟩
    have d : 0<(A.dens : ℝ)-threshold n := sub_pos.mpr (h.trans_le ha)
    rw [rescale] at d
    have l : (2:ℝ)^n<2*A.card+2^(n%2)*((2*(n/2)).choose (n/2):ℝ) :=
      sub_pos.mp ((div_pos_iff_of_pos_right (by positivity)).mp d)
    obtain ⟨f,hf⟩ := hyperplane_above A (by exact_mod_cast l)
    have kd := f.finrank_range_add_finrank_ker
    have rd := Submodule.finrank_le f.range
    have full : Module.finrank F (𝔽₂ n)=n := by simp [𝔽₂,𝔽]
    rw [full] at kd; simp only [Module.finrank_self] at rd
    have rank : Module.finrank F f.ker≤dim A := by
      apply le_csSup
      · refine ⟨n,?_⟩
        rintro _ ⟨S,_,rfl⟩; simpa [full] using Submodule.finrank_le S.direction
      · exact ⟨f.ker.toAffineSubspace,hf,by rw [Submodule.toAffineSubspace_direction]⟩
    omega

private theorem halfLayer_pos (k : ℕ) : 0<halfLayer k := by
  unfold halfLayer
  have pos := Nat.choose_pos (n:=2*k) (k:=k) (by omega)
  positivity
private theorem wallis_identity (k : ℕ) :
    halfLayer k ^ 2 * (2*k+1) * Wallis.W k = 1/4 := by
  have size : ((2*k).choose k : ℝ)*(k.factorial:ℝ)*(k.factorial:ℝ)=(2*k).factorial := by
    exact_mod_cast (by simpa [two_mul] using Nat.add_choose_mul_factorial_mul_factorial k k :
      (2*k).choose k*k.factorial*k.factorial=(2*k).factorial)
  rw [Wallis.W_eq_factorial_ratio]
  unfold halfLayer
  rw [←size]
  have power : (2:ℝ)^(4*k)=((2:ℝ)^(2*k))^2 := by rw [←pow_mul]; ring_nf
  rw [power]
  have pos := Nat.choose_pos (n:=2*k) (k:=k) (by omega)
  have pf := Nat.factorial_pos k
  have ck : ((2*k).choose k:ℝ)≠0 := by positivity
  have fk : (k.factorial:ℝ)≠0 := by positivity
  have dk : 2*(k:ℝ)+1≠0 := by positivity
  field_simp
  ring
private theorem even_layer_strict (k : ℕ) :
    Real.sqrt (2*(k:ℝ))*halfLayer k < 1/Real.sqrt (2*Real.pi) := by
  have id := wallis_identity k
  have lo := Wallis.le_W k
  have pos := halfLayer_pos k
  have pi := Real.pi_pos
  have floor : 2*(k:ℝ)*(Real.pi/2)<(2*k+1)*Wallis.W k := by
    calc
      _ < (2*(k:ℝ)+1)*(((2*k+1)/(2*k+2))*(Real.pi/2)) := by
        field_simp; nlinarith [Real.pi_pos]
      _ ≤ _ := mul_le_mul_of_nonneg_left lo (by positivity)
  have gap := mul_lt_mul_of_pos_right floor (sq_pos_of_pos pos)
  have sq := Real.sq_sqrt (show 0≤2*(k:ℝ) by positivity)
  have sp := Real.sq_sqrt (show 0≤2*Real.pi by positivity)
  apply (lt_div_iff₀ (by positivity : 0<Real.sqrt (2*Real.pi))).mpr
  have sqr : (Real.sqrt (2*(k:ℝ))*halfLayer k*Real.sqrt (2*Real.pi))^2<1 := by
    rw [mul_pow,mul_pow,sq,sp]; nlinarith
  nlinarith [sq_nonneg (Real.sqrt (2*(k:ℝ))*halfLayer k*Real.sqrt (2*Real.pi)-1)]

private theorem eventually_layer {C : ℝ} (nn : 0≤C)
    (small : C<1/Real.sqrt (2*Real.pi)) :
    ∀ᶠ n : ℕ in atTop, C < Real.sqrt n * halfLayer (n/2) := by
  have spi := Real.sq_sqrt (show 0≤2*Real.pi by positivity)
  have cc := (lt_div_iff₀ (by positivity : 0 < Real.sqrt (2*Real.pi))).mp small
  have cc' : (C*Real.sqrt (2*Real.pi))^2 < 1 := by
    nlinarith [mul_pos (sub_pos.mpr cc) (by positivity : 0<1+C*Real.sqrt (2*Real.pi))]
  rw [mul_pow,spi] at cc'
  obtain ⟨N,hN⟩ := exists_nat_gt (C^2*(2*Real.pi)/(1-C^2*(2*Real.pi)))
  have bound := (div_lt_iff₀ (sub_pos.mpr cc')).mp hN
  filter_upwards [eventually_ge_atTop N] with n hn
  have en : (N:ℝ)≤n := by exact_mod_cast hn
  have bigger := mul_le_mul_of_nonneg_right en (sub_pos.mpr cc').le
  have loss : C^2*(2*Real.pi)*((n:ℝ)+1)<n := by linarith
  let k := n/2
  have level := wallis_identity k
  have w := Wallis.W_le k
  have wn := (Wallis.W_pos k).le
  have kdim : 2*(k:ℝ)≤n := by exact_mod_cast (Nat.mul_div_le n 2)
  have hh := halfLayer_pos k
  have lower : 1 ≤ (2*Real.pi)*((n:ℝ)+1)*(halfLayer k)^2 := by
    calc
      1 = 4*((halfLayer k)^2*(2*(k:ℝ)+1)*Wallis.W k) := by rw [level]; norm_num
      _ ≤ 4*((halfLayer k)^2*((n:ℝ)+1)*(Real.pi/2)) := by
        gcongr
      _ = _ := by ring
  have lower' := mul_le_mul_of_nonneg_left lower (Nat.cast_nonneg n : (0:ℝ)≤n)
  have sq : C^2 < n*(halfLayer k)^2 := by
    apply lt_of_mul_lt_mul_right (a := (2*Real.pi)*((n:ℝ)+1))
    · nlinarith only [loss,lower']
    · positivity
  change C < Real.sqrt (n:ℝ)*halfLayer k
  have non := mul_nonneg (Real.sqrt_nonneg (n:ℝ)) hh.le
  have sq' : C^2 < (Real.sqrt (n:ℝ)*halfLayer k)^2 := by rwa [mul_pow,Real.sq_sqrt (Nat.cast_nonneg _)]
  nlinarith only [sq',non,sq_nonneg (C-Real.sqrt (n:ℝ)*halfLayer k),nn]

/-- The sharp asymptotic constant for setting `c = 1` in the exact host
quantifiers. At the endpoint the even-dimensional Hamming balls still obstruct. -/
theorem one_half_codimension_one_iff (C : ℝ) (nn : 0≤C) :
    (∀ᶠ n : ℕ in atTop, ∀ α : ℝ, α>1/2-C/Real.sqrt n → α≤1 →
      n≤Green51.guaranteedMaxCosetDim n α+1) ↔ C<1/Real.sqrt (2*Real.pi) := by
  constructor
  · intro ev
    by_contra! big
    obtain ⟨N,all⟩ := eventually_atTop.mp ev
    let k := N+1
    have dim : 2≤2*k := by dsimp [k]; omega
    have strict := (even_layer_strict k).trans_le big
    have hp : 0<(2*(k:ℝ)) := by exact_mod_cast (show 0<2*k by omega)
    have cmp : halfLayer k<C/Real.sqrt (2*(k:ℝ)) := by
      apply (lt_div_iff₀ (Real.sqrt_pos.mpr hp)).mpr; rwa [mul_comm]
    have den : threshold (2*k)>1/2-C/Real.sqrt (2*k : ℕ) := by
      unfold threshold; simp only [Nat.mul_div_cancel_left _ (by decide : 0<2),
        Nat.cast_mul,Nat.cast_ofNat]; linarith
    have ub : threshold (2*k)≤1 := by unfold threshold; linarith [halfLayer_pos (2*k/2)]
    have ans := all (2*k) (by dsimp [k]; omega) _ den ub
    exact (lt_irrefl _ : ¬threshold (2*k)<threshold (2*k)) ((guaranteed_hyperplane_iff dim ub).mp ans)
  · intro small
    filter_upwards [eventually_layer nn small,eventually_ge_atTop 2] with n high hn
    intro α ha hα
    apply (guaranteed_hyperplane_iff hn hα).mpr
    have hp : 0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
    have g : C/Real.sqrt n < halfLayer (n/2) := by
      apply (div_lt_iff₀ (Real.sqrt_pos.mpr hp)).mpr; rwa [mul_comm]
    unfold threshold; linarith


private theorem half_space_seed (n : ℕ) (hn : 0<n) :
    ∃ A : Finset (𝔽₂ n), (A.dens : ℝ)=1/2 ∧
      maxCosetDim F (𝔽₂ n) ((A+A : Finset _) : Set _)=n-1 := by
  classical
  let i : Fin n := ⟨0,hn⟩
  let f : (𝔽₂ n) →ₗ[F] F := LinearMap.proj i
  let H := f.ker
  have sur : Function.Surjective f := fun a => ⟨fun _ => a,rfl⟩
  have rank := f.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr sur] at rank
  have rank' : 1+Module.finrank F H=n := by simpa [H,𝔽₂,𝔽] using rank
  let A := (H : Set (𝔽₂ n)).toFinset
  have hc : A.card=2^(Module.finrank F H) := by
    calc
      _ = Fintype.card H := Set.toFinset_card _
      _ = _ := by rw [Module.card_eq_pow_finrank (K:=F)]; simp [F,ZMod.card]
  have eq : ((A+A : Finset _) : Set (𝔽₂ n)) = (H.toAffineSubspace : Set (𝔽₂ n)) := by
    ext x
    constructor
    · intro hx
      obtain ⟨a,ha,b,hb,rfl⟩ := mem_add.mp hx
      exact H.add_mem (Set.mem_toFinset.mp ha) (Set.mem_toFinset.mp hb)
    · intro hx
      exact mem_add.mpr ⟨x,Set.mem_toFinset.mpr hx,0,Set.mem_toFinset.mpr H.zero_mem,add_zero x⟩
  refine ⟨A,?_,?_⟩
  · rw [nnratCast_dens,hc]
    simp only [𝔽₂,𝔽,Fintype.card_fun,Fintype.card_fin,ZMod.card,Nat.cast_pow,Nat.cast_ofNat]
    have p : (2:ℝ)^n=2*2^(Module.finrank F H) := by
      calc
        _ = (2:ℝ)^(1+Module.finrank F H) := congrArg (fun j : ℕ => (2:ℝ)^j) rank'.symm
        _ = _ := by rw [pow_add,pow_one]
    rw [p]; field_simp
  · rw [eq,maxCosetDim_affineSubspace,Submodule.toAffineSubspace_direction]; omega

/-- The exact value of Green's function throughout the two density intervals
above the hyperplane threshold. -/
theorem guaranteed_above_threshold {n : ℕ} (hn : 2≤n) {α : ℝ}
    (ha : threshold n<α) (one : α≤1) :
    Green51.guaranteedMaxCosetDim n α = if α≤1/2 then n-1 else n := by
  classical
  by_cases small : α≤1/2
  · rw [if_pos small]
    have lo := (guaranteed_hyperplane_iff hn one).mpr ha
    obtain ⟨A,d,rank⟩ := half_space_seed n (by omega)
    have ub : Green51.guaranteedMaxCosetDim n α≤n-1 := by
      apply csInf_le (OrderBot.bddBelow _)
      exact ⟨A,by rwa [d],rank⟩
    omega
  rw [if_neg small]
  have full (A : Finset (𝔽₂ n)) (h : α≤A.dens) : A+A=univ := by
    apply eq_univ_of_forall
    intro x
    by_contra out
    let B := A.map (Equiv.addLeft x).toEmbedding
    have dis : Disjoint A B := by
      rw [disjoint_left]; intro b hb hb'
      obtain ⟨a,ha,e⟩ := mem_map.mp hb'
      change x+a=b at e
      have same : b+a=x := by rw [←e,add_assoc,ZModModule.add_self,add_zero]
      exact out (same ▸ add_mem_add hb ha)
    have cnt := (A∪B).card_le_univ
    rw [card_union_of_disjoint dis] at cnt
    have big : (1/2:ℝ)<A.dens := (lt_of_not_ge small).trans_le h
    rw [nnratCast_dens] at big
    have bb := (lt_div_iff₀ (by positivity : 0<(Fintype.card (𝔽₂ n):ℝ))).mp big
    have bound : (A.card:ℝ)+A.card ≤ Fintype.card (𝔽₂ n) := by
      exact_mod_cast (by simpa [B] using cnt : A.card+A.card≤Fintype.card (𝔽₂ n))
    linarith
  have eq (A : Finset (𝔽₂ n)) (h : α≤A.dens) :
      maxCosetDim F (𝔽₂ n) ((A+A : Finset _) : Set _) = n := by
    rw [full A h,coe_univ,maxCosetDim_univ]; simp [𝔽₂,𝔽]
  unfold Green51.guaranteedMaxCosetDim
  apply le_antisymm
  · apply csInf_le (OrderBot.bddBelow _)
    have h : α≤((univ : Finset (𝔽₂ n)).dens : ℝ) := by simpa using one
    exact ⟨univ,h,eq _ h⟩
  · apply le_csInf
    · have h : α≤((univ : Finset (𝔽₂ n)).dens : ℝ) := by simpa using one
      exact ⟨n,univ,h,eq _ h⟩
    · rintro _ ⟨A,h,rfl⟩; exact (eq A h).ge

end Green51Hyperplane
#print axioms Green51Hyperplane.guaranteed_hyperplane_iff
#print axioms Green51Hyperplane.one_half_codimension_one_iff
#print axioms Green51Hyperplane.guaranteed_above_threshold
