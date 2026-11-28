import Green28Variation

/-! Relative errors for approximate uniform independent sums on intervals. -/

namespace Green28NearInterval

open Green28 Green28Variation Finset
open scoped ENNReal NNReal

/-- A convex mixture, with both weights explicit to avoid truncated subtraction. -/
noncomputable def mix {α : Type*} (a b : ℝ≥0∞) (one : a+b=1) (P Q : PMF α) : PMF α :=
  ⟨fun x => a*P x+b*Q x, by
    apply ENNReal.summable.hasSum_iff.mpr
    rw [ENNReal.tsum_add,ENNReal.tsum_mul_left,ENNReal.tsum_mul_left,P.tsum_coe,Q.tsum_coe,mul_one,mul_one,one]⟩

private theorem convolution (P Q : PMF ℤ) (z : ℤ) :
    indepSum P Q z = ∑' x, P x * Q (z-x) := by
  change (P.bind fun x => Q.bind fun y => PMF.pure (x+y)) z = _
  rw [PMF.bind_apply]
  congr 1
  funext x
  rw [PMF.bind_apply,tsum_eq_single (z-x)]
  · simp [PMF.pure_apply]
  · intro y hy
    simp [PMF.pure_apply,show z≠x+y by omega]

/-- Replacing one input by a mixture mixes the output laws with the same weights. -/
private theorem mix_left (a b : ℝ≥0∞) (one : a+b=1) (P Q R : PMF ℤ) (z : ℤ) :
    indepSum (mix a b one P Q) R z = a*indepSum P R z+b*indepSum Q R z := by
  rw [convolution (mix a b one P Q) R z,convolution P R z,convolution Q R z]
  change (∑' x, (a*P x+b*Q x)*R (z-x))=_
  simp only [add_mul,mul_assoc,ENNReal.tsum_add,ENNReal.tsum_mul_left]

private theorem mix_right (a b : ℝ≥0∞) (one : a+b=1) (P Q R : PMF ℤ) (z : ℤ) :
    indepSum P (mix a b one Q R) z = a*indepSum P Q z+b*indepSum P R z := by
  rw [convolution P (mix a b one Q R) z,convolution P Q z,convolution P R z]
  change (∑' x, P x*(a*Q (z-x)+b*R (z-x)))=_
  simp only [mul_add,mul_left_comm (P _),ENNReal.tsum_add,ENNReal.tsum_mul_left]

private theorem mix_error (a b : ℝ≥0) (one : a+b=1) (u v : ℝ≥0∞) (hu : u≤1) (hv : v≤1) :
    |((a:ℝ≥0∞)*u+(b:ℝ≥0∞)*v).toReal-u.toReal| ≤ (b:ℝ) := by
  have hU : u ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hu
  have hV : v ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hv
  have au : (a:ℝ≥0∞)*u ≠ ⊤ := ENNReal.mul_ne_top ENNReal.coe_ne_top hU
  have bv : (b:ℝ≥0∞)*v ≠ ⊤ := ENNReal.mul_ne_top ENNReal.coe_ne_top hV
  rw [ENNReal.toReal_add au bv,ENNReal.toReal_mul,ENNReal.toReal_mul,ENNReal.coe_toReal,ENNReal.coe_toReal]
  have e : (a:ℝ)+(b:ℝ)=1 := by exact_mod_cast one
  have diff : (a:ℝ)*u.toReal+b*v.toReal-u.toReal=(b:ℝ)*(v.toReal-u.toReal) := by
    nlinarith [congrArg (·*u.toReal) e]
  rw [diff,abs_mul,abs_of_nonneg b.coe_nonneg]
  have h1 : v.toReal≤1 := by simpa using ENNReal.toReal_mono ENNReal.one_ne_top hv
  have h2 : u.toReal≤1 := by simpa using ENNReal.toReal_mono ENNReal.one_ne_top hu
  exact (mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by linarith [ENNReal.toReal_nonneg (a := v)],by linarith [ENNReal.toReal_nonneg (a := u)]⟩) b.coe_nonneg).trans_eq (mul_one _)

/-- Perturbing both factors by mixtures of weight b changes each sum
probability by at most 2b, uniformly over the replacement laws. -/
theorem two_mix_error (a b : ℝ≥0) (one : a+b=1) (P Q U V : PMF ℤ) (z : ℤ) :
    let h : (a:ℝ≥0∞)+(b:ℝ≥0∞)=1 := by exact_mod_cast one
    |(indepSum (mix a b h P U) (mix a b h Q V) z).toReal - (indepSum P Q z).toReal| ≤ 2*(b:ℝ) := by
  dsimp only
  have h : (a:ℝ≥0∞)+(b:ℝ≥0∞)=1 := by exact_mod_cast one
  let W := mix a b h Q V
  have l := mix_error a b one (indepSum P W z) (indepSum U W z) ((indepSum P W).coe_le_one _) ((indepSum U W).coe_le_one _)
  have r := mix_error a b one (indepSum P Q z) (indepSum P V z) ((indepSum P Q).coe_le_one _) ((indepSum P V).coe_le_one _)
  rw [←mix_left _ _ h] at l
  rw [←mix_right _ _ h] at r
  exact (abs_sub_le _ (indepSum P W z).toReal _).trans (by linarith)

/-- The middle base-`n` digit goes to the first factor. The low digit and
the bit selecting the upper block go to the second. -/
private def code (n x y : ℕ) : ℕ := y%n+n*(x+n*(y/n))

private theorem decode {n x y : ℕ} (pos : 0<n) (hx : x<n) :
    code n x y/n%n=x ∧ code n x y%n+n*(code n x y/n/n)=y := by
  have low := Nat.mod_lt y pos
  have div : code n x y/n=x+n*(y/n) := by
    rw [code,Nat.add_mul_div_left _ _ pos,Nat.div_eq_of_lt low,zero_add]
  have mod : code n x y%n=y%n := by simp [code]
  rw [div,mod,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hx,
    Nat.add_mul_div_left _ _ pos,Nat.div_eq_of_lt hx,zero_add,Nat.mod_add_div]
  exact ⟨rfl,rfl⟩

private theorem code_lt {n x y : ℕ} (pos : 0<n) (hx : x<n) (hy : y<2*n) :
    code n x y<2*n*n := by
  have low := Nat.mod_lt y pos
  have hi : y/n<2 := (Nat.div_lt_iff_lt_mul pos).mpr hy
  have bh := Nat.mul_le_mul_left n (show y/n≤1 by omega)
  have bound := Nat.mul_le_mul_left n (show x+n*(y/n)+1≤2*n by omega)
  unfold code
  nlinarith

private theorem code_surj {n z : ℕ} (pos : 0<n) (hz : z<2*n*n) :
    ∃ x<n, ∃ y<2*n, code n x y=z := by
  let x := z/n%n
  let j := z/n/n
  let y := z%n+n*j
  have low := Nat.mod_lt z pos
  have hx := Nat.mod_lt (z/n) pos
  have hi : j<2 := (Nat.div_lt_iff_lt_mul pos).mpr ((Nat.div_lt_iff_lt_mul pos).mpr hz)
  have bh := Nat.mul_le_mul_left n (show j≤1 by omega)
  refine ⟨x,hx,y,by dsimp [y]; omega,?_⟩
  have ym : y%n=z%n := by simp [y]
  have yd : y/n=j := by dsimp only [y]; rw [Nat.add_mul_div_left _ _ pos,Nat.div_eq_of_lt low,zero_add]
  have d := Nat.mod_add_div (z/n) n
  have e := Nat.mod_add_div z n
  rw [code,ym,yd]
  change z%n+n*(z/n%n+n*(z/n/n))=z
  rw [d,e]

private def left (n : ℕ) (j : ℕ) : ℤ := n*j
private def right (n : ℕ) (j : ℕ) : ℤ := (j%n:ℕ)+((n*n*(j/n):ℕ):ℤ)
private def A (n : ℕ) := (range n).image (left n)
private def B (n : ℕ) := (range (2*n)).image (right n)
/-- Integers from zero through `m-1`, with the empty interval at `m=0`. -/
def interval (m : ℕ) := (range m).image (fun z : ℕ => (z:ℤ))

private theorem cell (n x y : ℕ) : left n x+right n y=(code n x y:ℕ) := by
  unfold left right code
  push_cast
  ring

private theorem left_inj {n : ℕ} (pos : 0<n) : Function.Injective (left n) := by
  intro x y h
  unfold left at h
  exact_mod_cast (mul_left_cancel₀ (show (n:ℤ)≠0 by exact_mod_cast pos.ne') h)

private theorem right_inj {n : ℕ} (pos : 0<n) : Function.Injective (right n) := by
  intro x y e
  have eq' : code n 0 x=code n 0 y := by
    exact_mod_cast (show (code n 0 x:ℤ)=(code n 0 y:ℤ) by rw [←cell,←cell,e])
  have x' := (decode (n := n) (y := x) pos (show 0<n from pos)).2
  have y' := (decode (n := n) (y := y) pos (show 0<n from pos)).2
  rw [eq',y'] at x'
  exact x'.symm

private theorem exact_interval {n : ℕ} (pos : 0<n) :
    let add := fun p : ℤ×ℤ => p.1+p.2
    Set.InjOn add ((A n ×ˢ B n : Finset (ℤ×ℤ)):Set (ℤ×ℤ)) ∧
      (A n ×ˢ B n).image add=interval (2*n*n) := by
  dsimp only
  constructor
  · rintro ⟨x,y⟩ hv ⟨z,w⟩ hw he
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hv
    obtain ⟨hz,hw⟩ := Finset.mem_product.mp hw
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hw
    change left n i+right n j=left n k+right n l at he
    rw [cell,cell] at he
    have eq' : code n i j=code n k l := by exact_mod_cast he
    obtain ⟨i',j'⟩ := decode (y := j) pos (Finset.mem_range.mp hi)
    obtain ⟨k',l'⟩ := decode (y := l) pos (Finset.mem_range.mp hk)
    rw [eq',k'] at i'
    rw [eq',l'] at j'
    subst k; subst l; rfl
  · ext z
    constructor
    · rintro hz
      obtain ⟨⟨a,b⟩,hab,rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hb
      exact Finset.mem_image.mpr ⟨code n i j,Finset.mem_range.mpr (code_lt pos (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)),(cell n i j).symm⟩
    · intro hz
      obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨i,hi,j,hj,e⟩ := code_surj pos (Finset.mem_range.mp hw)
      exact Finset.mem_image.mpr ⟨(left n i,right n j),Finset.mem_product.mpr
        ⟨Finset.mem_image.mpr ⟨i,Finset.mem_range.mpr hi,rfl⟩,Finset.mem_image.mpr ⟨j,Finset.mem_range.mpr hj,rfl⟩⟩,
        (cell n i j).trans (congrArg Nat.cast e)⟩

theorem mem_interval {z : ℤ} {m : ℕ} : z ∈ interval m ↔ 0 ≤ z ∧ z < (m : ℤ) := by
  constructor
  · rintro h
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp h
    have := Finset.mem_range.mp hi
    omega
  · rintro ⟨lo,hi⟩
    exact Finset.mem_image.mpr ⟨z.toNat,Finset.mem_range.mpr (by omega),by omega⟩

private theorem interval_card (m : ℕ) : (interval m).card=m := by
  rw [interval,Finset.card_image_of_injective _ Nat.cast_injective,Finset.card_range]

private theorem a_sub {n : ℕ} : A n ⊆ interval (n*(n-1)+1) := by
  intro z hz
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hz
  have hj' := Finset.mem_range.mp hj
  have lim := Nat.mul_le_mul_left n (show j≤n-1 by omega)
  apply mem_interval.mpr
  unfold left
  exact_mod_cast (show 0≤n*j ∧ n*j<n*(n-1)+1 by omega)

private theorem b_sub {n : ℕ} (pos : 0<n) : B n ⊆ interval (n*n+n) := by
  intro z hz
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hz
  have h := (Nat.div_lt_iff_lt_mul pos).mpr (Finset.mem_range.mp hj)
  have low := Nat.mod_lt j pos
  have lim := Nat.mul_le_mul_left (n*n) (show j/n≤1 by omega)
  apply mem_interval.mpr
  unfold right
  exact_mod_cast (show 0≤j%n+n*n*(j/n) ∧ j%n+n*n*(j/n)<n*n+n by omega)

private theorem hull_sums {n : ℕ} (pos : 0<n) {x y : ℤ} (hx : x∈interval (n*(n-1)+1))
    (hy : y∈interval (n*n+n)) : x+y∈interval (2*n*n) := by
  obtain ⟨xl,xh⟩ := mem_interval.mp hx
  obtain ⟨yl,yh⟩ := mem_interval.mp hy
  apply mem_interval.mpr
  have sub : ((n-1:ℕ):ℤ)=(n:ℤ)-1 := by omega
  push_cast at xh yh ⊢
  rw [sub] at xh
  exact ⟨by omega,by nlinarith⟩

private theorem small_cards {n : ℕ} (pos : 0<n) : (A n).card=n ∧ (B n).card=2*n := by
  simp only [A,B,Finset.card_image_of_injective _ (left_inj pos),Finset.card_image_of_injective _ (right_inj pos),card_range,and_self]

private theorem flat_seed {n : ℕ} (pos : 0<n) (ha : (A n).Nonempty) (hb : (B n).Nonempty)
    {z : ℤ} (hz : z∈interval (2*n*n)) :
    indepSum (PMF.uniformOfFinset (A n) ha) (PMF.uniformOfFinset (B n) hb) z=(2*n*n:ℝ≥0∞)⁻¹ := by
  have ⟨inj,cover⟩ := exact_interval pos
  rw [←cover] at hz
  obtain ⟨⟨x,y⟩,hxy,eq⟩ := Finset.mem_image.mp hz
  obtain ⟨hx,hy⟩ := Finset.mem_product.mp hxy
  change x+y=z at eq
  rw [convolution,tsum_eq_single x]
  · rw [show z-x=y by omega,PMF.uniformOfFinset_apply_of_mem ha hx,PMF.uniformOfFinset_apply_of_mem hb hy]
    rw [(small_cards pos).1,(small_cards pos).2,Nat.cast_mul,Nat.cast_ofNat,←ENNReal.mul_inv (Or.inl (by exact_mod_cast pos.ne')) (Or.inl (by simp))]
    ring_nf
  · intro w ne
    by_cases hw : w∈A n
    · have out : z-w∉B n := by
        intro hv
        have e := inj (x₁ := (w,z-w)) (Finset.mem_product.mpr ⟨hw,hv⟩) (x₂ := (x,y))
          hxy (show w+(z-w)=x+y by omega)
        exact ne (congrArg Prod.fst e)
      rw [PMF.uniformOfFinset_apply_of_notMem hb out,mul_zero]
    · rw [PMF.uniformOfFinset_apply_of_notMem ha hw,zero_mul]

private theorem oneCoe {a b : ℝ≥0} (h : a+b=1) : (a:ℝ≥0∞)+(b:ℝ≥0∞)=1 := by exact_mod_cast h

private noncomputable def blend {a b : ℝ≥0} (h : a+b=1) {S I : Finset ℤ}
    (hs : S.Nonempty) (hi : I.Nonempty) :=
  mix a b (oneCoe h) (PMF.uniformOfFinset S hs) (PMF.uniformOfFinset I hi)

private theorem blend_support {a b : ℝ≥0} (h : a+b=1) (bp : 0<b) {S I : Finset ℤ}
    (hs : S.Nonempty) (hi : I.Nonempty) (sub : S⊆I) :
    (blend h hs hi).support=(I:Set ℤ) := by
  ext x
  rw [PMF.mem_support_iff]
  change (a:ℝ≥0∞)*PMF.uniformOfFinset S hs x+(b:ℝ≥0∞)*PMF.uniformOfFinset I hi x ≠ 0 ↔ x∈I
  by_cases hx : x∈I
  · simp [hx,PMF.uniformOfFinset_apply_of_mem hi hx,bp.ne']
  · simp [hx,PMF.uniformOfFinset_apply_of_notMem hi hx,PMF.uniformOfFinset_apply_of_notMem hs (fun s => hx (sub s))]

private theorem blend_atom {a b : ℝ≥0} (h : a+b=1) {S I : Finset ℤ}
    (hs : S.Nonempty) (hi : I.Nonempty) {x : ℤ} (hx : x∈I) :
    ((blend h hs hi) x).toReal=(if x∈S then (a:ℝ)/(S.card:ℝ) else 0)+(b:ℝ)/(I.card:ℝ) := by
  change ((a:ℝ≥0∞)*PMF.uniformOfFinset S hs x+(b:ℝ≥0∞)*PMF.uniformOfFinset I hi x).toReal=_
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.coe_ne_top ((PMF.uniformOfFinset S hs).apply_ne_top _))
    (ENNReal.mul_ne_top ENNReal.coe_ne_top ((PMF.uniformOfFinset I hi).apply_ne_top _)),
    PMF.uniformOfFinset_apply_of_mem hi hx]
  by_cases mem : x∈S <;> simp [PMF.uniformOfFinset_apply,mem,ENNReal.toReal_mul,div_eq_mul_inv]

private theorem blend_variation {a b : ℝ≥0} (h : a+b=1) {S I : Finset ℤ}
    (hs : S.Nonempty) (hi : I.Nonempty) (sub : S⊆I) :
    variation (blend h hs hi) I=(a:ℝ)*(1-(S.card:ℝ)/(I.card:ℝ)) := by
  have one : (a:ℝ)+(b:ℝ)=1 := by exact_mod_cast h
  have c := Finset.card_le_card sub
  have si : (0:ℝ)<S.card := by exact_mod_cast hs.card_pos
  have ii : (0:ℝ)<I.card := by exact_mod_cast hi.card_pos
  have le := inv_anti₀ si (show (S.card:ℝ)≤I.card by exact_mod_cast c)
  let f := fun x : ℤ => |((blend h hs hi) x).toReal-(I.card:ℝ)⁻¹|
  have at_s (x : ℤ) (hx : x∈S) : f x=(a:ℝ)*((S.card:ℝ)⁻¹-(I.card:ℝ)⁻¹) := by
    dsimp [f]
    rw [blend_atom h hs hi (sub hx),if_pos hx,div_eq_mul_inv,div_eq_mul_inv]
    rw [show (a:ℝ)*(S.card:ℝ)⁻¹+b*(I.card:ℝ)⁻¹-(I.card:ℝ)⁻¹=
      (a:ℝ)*((S.card:ℝ)⁻¹-(I.card:ℝ)⁻¹) by nlinarith [congrArg (·*(I.card:ℝ)⁻¹) one]]
    exact abs_of_nonneg (mul_nonneg a.coe_nonneg (sub_nonneg.mpr le))
  have at_d (x : ℤ) (hx : x∈I \ S) : f x=(a:ℝ)*(I.card:ℝ)⁻¹ := by
    obtain ⟨mem,out⟩ := Finset.mem_sdiff.mp hx
    dsimp [f]
    rw [blend_atom h hs hi mem,if_neg out,zero_add,div_eq_mul_inv]
    rw [show (b:ℝ)*(I.card:ℝ)⁻¹-(I.card:ℝ)⁻¹= -((a:ℝ)*(I.card:ℝ)⁻¹) by nlinarith [congrArg (·*(I.card:ℝ)⁻¹) one],abs_neg,abs_of_nonneg (by positivity)]
  change (∑ x ∈ I, f x)/2=_
  rw [←Finset.sum_sdiff sub,Finset.sum_congr rfl at_d,Finset.sum_congr rfl at_s,
    sum_const,sum_const,Finset.card_sdiff_of_subset sub,nsmul_eq_mul,nsmul_eq_mul,Nat.cast_sub c]
  field_simp
  ring

/-- At most two rational values on the occupied sites of a law. -/
def TwoRational (P : PMF ℤ) : Prop := ∃ l h : ℚ, ∀ x∈P.support,
  (P x).toReal=(l:ℝ) ∨ (P x).toReal=(h:ℝ)

/-- A certificate for the two interval inputs at a fixed radix. -/
structure Certificate (n : ℕ) where
  P : PMF ℤ
  Q : PMF ℤ
  left_support : P.support=(interval (n*(n-1)+1):Set ℤ)
  right_support : Q.support=(interval (n*n+n):Set ℤ)
  sum_support : (indepSum P Q).support=(interval (2*n*n):Set ℤ)
  rational : TwoRational P ∧ TwoRational Q
  left_distance : variation P (interval (n*(n-1)+1))=
    (1-(n:ℝ)⁻¹^4)*(1-(n:ℝ)/(n*(n-1)+1))
  right_distance : variation Q (interval (n*n+n))=
    (1-(n:ℝ)⁻¹^4)*(1-(2*n:ℝ)/(n*n+n))
  relative_error : ∀ z∈(indepSum P Q).support, |(2*n*n:ℝ)*(indepSum P Q z).toReal-1|≤4/(n:ℝ)^2

private theorem blend_rational {a b : ℝ≥0} (h : a+b=1) (bp : 0<b) (ar br : ℚ)
    (ea : (a:ℝ)=ar) (eb : (b:ℝ)=br) {S I : Finset ℤ} (hs : S.Nonempty) (hi : I.Nonempty) (sub : S⊆I) :
    TwoRational (blend h hs hi) := by
  refine ⟨br/I.card,ar/S.card+br/I.card,?_⟩
  intro x hx
  rw [blend_support h bp hs hi sub] at hx
  rw [blend_atom h hs hi hx,ea,eb]
  by_cases mem : x∈S <;> simp [mem]

/-- The two sparse inputs tile an interval. Adding mass n⁻⁴ on their full
hulls preserves pointwise relative accuracy while giving the two explicit
distances from the uniform laws on the enlarged supports. -/
theorem exists_certificate {n : ℕ} (hn : 2≤n) : Nonempty (Certificate n) := by
  have pos : 0<n := by omega
  let b : ℝ≥0 := (n:ℝ≥0)⁻¹^4
  let a : ℝ≥0 := 1-b
  have low : (1:ℝ≥0)≤n := by exact_mod_cast (show 1≤n by omega)
  have bp : 0<b := by dsimp [b]; positivity
  have small : b≤1 := pow_le_one₀ (by positivity) ((inv_le_one₀ (by positivity)).mpr low)
  have h : a+b=1 := tsub_add_cancel_of_le small
  have br : (b:ℝ)=(n:ℝ)⁻¹^4 := by simp [b]
  have ar : (a:ℝ)=1-(n:ℝ)⁻¹^4 := by
    have one : (a:ℝ)+(b:ℝ)=1 := by exact_mod_cast h
    linarith
  have ha : (A n).Nonempty := Finset.card_pos.mp ((small_cards pos).1.symm ▸ pos)
  have hb : (B n).Nonempty := Finset.card_pos.mp (by rw [(small_cards pos).2]; omega)
  have hi := ha.mono a_sub
  have hj := hb.mono (b_sub pos)
  let P := blend h ha hi
  let Q := blend h hb hj
  have ps := blend_support h bp ha hi a_sub
  have qs := blend_support h bp hb hj (b_sub pos)
  have sums : (indepSum P Q).support=(interval (2*n*n):Set ℤ) := by
    ext z
    rw [Green28FiniteSearch.mem_support_indepSum,ps,qs]
    constructor
    · rintro ⟨x,hx,y,hy,rfl⟩
      exact hull_sums pos hx hy
    · intro hz
      have eq := (exact_interval pos).2
      obtain ⟨⟨x,y⟩,mem,e⟩ := Finset.mem_image.mp (eq.symm ▸ hz)
      obtain ⟨hx,hy⟩ := Finset.mem_product.mp mem
      exact ⟨x,a_sub hx,y,b_sub pos hy,e⟩
  refine ⟨⟨P,Q,ps,qs,sums,?_,?_,?_,?_⟩⟩
  · have a' : (a:ℝ)=((1-(n:ℚ)⁻¹^4:ℚ):ℝ) := by simpa using ar
    have b' : (b:ℝ)=(((n:ℚ)⁻¹^4:ℚ):ℝ) := by simpa using br
    exact ⟨blend_rational h bp _ _ a' b' ha hi a_sub,blend_rational h bp _ _ a' b' hb hj (b_sub pos)⟩
  · rw [show variation P _=_ from blend_variation h ha hi a_sub,(small_cards pos).1,interval_card,ar]
    push_cast
    rw [Nat.cast_sub (show 1≤n by omega),Nat.cast_one]
  · rw [show variation Q _=_ from blend_variation h hb hj (b_sub pos),(small_cards pos).2,interval_card,ar]
    push_cast
    rfl
  · intro z hz
    rw [sums] at hz
    have error := two_mix_error a b h (PMF.uniformOfFinset (A n) ha) (PMF.uniformOfFinset (B n) hb)
      (PMF.uniformOfFinset (interval _) hi) (PMF.uniformOfFinset (interval _) hj) z
    change |(indepSum P Q z).toReal-_|≤_ at error
    rw [flat_seed pos ha hb hz,ENNReal.toReal_inv,ENNReal.toReal_mul,ENNReal.toReal_mul,ENNReal.toReal_natCast,
      ENNReal.toReal_ofNat,br] at error
    have np : (0:ℝ)<n := by exact_mod_cast pos
    have kp : (0:ℝ)<2*n*n := by positivity
    have eq : (2*n*n:ℝ)*(indepSum P Q z).toReal-1 =
        (2*n*n:ℝ)*((indepSum P Q z).toReal-(2*n*n:ℝ)⁻¹) := by
      field_simp
    rw [eq,abs_mul,abs_of_pos kp]
    apply (mul_le_mul_of_nonneg_left error kp.le).trans
    apply le_of_eq
    field_simp
    ring

/-- At every tolerance both inputs can be arbitrarily far from their support
uniforms, even with two rational weights and vanishing pointwise relative
error on the whole occupied interval of the independent sum. -/
theorem near_uniform_sum_far_inputs (ε : ℝ) (pos : 0<ε) :
    ∃ n≥2, ∃ C : Certificate n, 1-ε < variation C.P (interval (n*(n-1)+1)) ∧
      1-ε < variation C.Q (interval (n*n+n)) ∧
      ∀ z∈(indepSum C.P C.Q).support, |(2*n*n:ℝ)*(indepSum C.P C.Q z).toReal-1|<ε := by
  obtain ⟨n,big⟩ := exists_nat_gt (max (4/ε) 2)
  have large : 2<(n:ℝ) := (le_max_right _ _).trans_lt big
  have hn : 2≤n := by exact_mod_cast large.le
  have np : 0<(n:ℝ) := by linarith
  have tol : 4/(n:ℝ)<ε := (div_lt_iff₀ np).mpr (by
    have e := (div_lt_iff₀ pos).mp ((le_max_left _ _).trans_lt big)
    linarith)
  have tiny : (n:ℝ)⁻¹^4≤1/n := by
    have h := pow_le_pow_of_le_one (inv_nonneg.mpr np.le) ((inv_le_one₀ np).mpr (by linarith)) (by decide : 1≤4)
    simpa only [pow_one,one_div] using h
  have lpos : 0<(n:ℝ)*(n-1)+1 := by nlinarith
  have rpos : 0<(n:ℝ)*n+n := by positivity
  have lratio : (n:ℝ)/(n*(n-1)+1)≤2/n := by
    apply (div_le_div_iff₀ lpos np).mpr
    nlinarith [sq_nonneg ((n:ℝ)-1)]
  have rratio : (2*n:ℝ)/(n*n+n)≤2/n := by
    apply (div_le_div_iff₀ rpos np).mpr
    nlinarith
  have dist (r : ℝ) (hr : 0≤r) (upper : r≤2/n) : 1-ε<(1-(n:ℝ)⁻¹^4)*(1-r) := by
    have t : 1/(n:ℝ)+2/n≤4/n := by rw [←add_div]; apply div_le_div_of_nonneg_right (by norm_num) np.le
    nlinarith [mul_nonneg (pow_nonneg (inv_nonneg.mpr np.le) 4) hr]
  obtain ⟨C⟩ := exists_certificate hn
  refine ⟨n,hn,C,?_,?_,?_⟩
  · rw [C.left_distance]
    exact dist _ (div_nonneg np.le lpos.le) lratio
  · rw [C.right_distance]
    exact dist _ (by positivity) rratio
  · intro z hz
    have e : 4/(n:ℝ)^2≤4/n := by
      apply (div_le_div_iff₀ (by positivity) np).mpr
      nlinarith [mul_nonneg np.le (show 0≤(n:ℝ)-1 by linarith)]
    exact (C.relative_error z hz).trans_lt (e.trans_lt tol)

#print axioms two_mix_error
#print axioms exists_certificate
#print axioms near_uniform_sum_far_inputs

end Green28NearInterval
