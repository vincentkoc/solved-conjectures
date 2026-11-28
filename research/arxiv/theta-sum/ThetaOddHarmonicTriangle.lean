import ThetaDivisorLogMean

/-! Harmonic mass of coprime pairs of odd integers in an initial square. -/
namespace Arxiv.«2501.03234».ThetaOddHarmonicTriangle
open Finset
noncomputable section

def odds (T : ℕ) := (Icc 1 T).filter Odd
def H (T : ℕ) : ℝ := ∑ n∈odds T,(n:ℝ)⁻¹
def U (d : ℕ) : ℝ := ∑ w∈(odds d).filter (·.Coprime d),(w:ℝ)⁻¹

private theorem multiples {p T : ℕ} (hp : 0< p) :
    ∑ n∈(odds T).filter (p∣·),(n:ℝ)⁻¹ ≤ H T/p := by
  classical
  let D := (odds T).filter (p∣·)
  have hd {x : ℕ} (h : x∈D) := (mem_filter.mp h).2
  have hi : Set.InjOn (fun x : ℕ => x/p) D := by
    intro x hx y hy he
    simpa only [Nat.div_mul_cancel (hd hx),Nat.div_mul_cancel (hd hy)] using congrArg (·*p) he
  have hsub : D.image (·/p)⊆odds T := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hy
    obtain ⟨hx',hpx⟩ := mem_filter.mp hx
    obtain ⟨hr,ho⟩ := mem_filter.mp hx'
    have hn := mem_Icc.mp hr
    apply mem_filter.mpr
    constructor
    · exact mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hn.1 hpx) hp,(Nat.div_le_self ..).trans hn.2⟩
    · rw [←Nat.div_mul_cancel hpx] at ho; exact (Nat.odd_mul.mp ho).1
  rw [le_div_iff₀ (by exact_mod_cast hp : 0<(p:ℝ)),sum_mul]
  calc _ = ∑ x∈D,((x/p:ℕ):ℝ)⁻¹ := by
             apply sum_congr rfl; intro x hx
             have eq : (x:ℝ)=(x/p:ℕ)*(p:ℝ) := by exact_mod_cast (Nat.div_mul_cancel (hd hx)).symm
             rw [eq,mul_inv_rev]; field_simp
       _ = ∑ y∈D.image (·/p),(y:ℝ)⁻¹ := (sum_image (f:=fun n : ℕ => (n:ℝ)⁻¹) hi).symm
       _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)

private theorem reciprocal_sq (T : ℕ) : ∑ p∈Icc 3 T,((p:ℝ)⁻¹)^2 ≤ 1/2 := by
  suffices ∀ n : ℕ, ∑ p∈Icc 3 (n+2),((p:ℝ)⁻¹)^2 ≤ 1/2-1/(n+2:ℝ) by
    by_cases h : 2≤ T
    · specialize this (T-2); rw [Nat.sub_add_cancel h] at this
      linarith [show 0≤1/((T-2:ℕ)+2:ℝ) by positivity]
    · rw [Icc_eq_empty_of_lt (by omega),sum_empty]; norm_num
  intro n; induction n with
  | zero => norm_num
  | succ n ih =>
    rw [show n+1+2=n+2+1 by omega,sum_Icc_succ_top (by omega)]
    have hn : 0<(n:ℝ)+2 := by positivity
    have hk : 0<(n:ℝ)+2+1 := by positivity
    push_cast
    apply (add_le_add_left ih _).trans
    rw [show (n:ℝ)+1+2=n+2+1 by ring]
    field_simp; nlinarith

private def W (a : ℕ×ℕ) : ℝ := (a.1:ℝ)⁻¹*(a.2:ℝ)⁻¹

theorem coprime_square (T : ℕ) :
    (H T)^2/2 ≤ ∑ a∈((odds T)×ˢ(odds T)).filter (fun a => a.1.Coprime a.2), W a := by
  classical
  let Q := odds T×ˢodds T
  let bad := Q.filter (fun a => ¬a.1.Coprime a.2)
  let M (p : ℕ) := (odds T).filter (p∣·)
  have sqsum (s : Finset ℕ) : (∑ a∈s×ˢs,W a)=(∑ n∈s,(n:ℝ)⁻¹)^2 := by simp only [W,sum_product,←mul_sum,←sum_mul,sq]
  have hs (p : ℕ) (hp : p∈Icc 3 T) : ∑ a∈M p×ˢM p,W a ≤ (H T)^2*((p:ℝ)⁻¹)^2 := by
    rw [sqsum,←mul_pow,←div_eq_mul_inv]
    exact pow_le_pow_left₀ (sum_nonneg (fun i _ => by positivity)) (multiples (by have := (mem_Icc.mp hp).1; omega)) _
  let v (p : ℕ) (a : ℕ×ℕ) := if a∈M p×ˢM p then W a else 0
  have hn (p a) : 0≤ v p a := by
    unfold v; split
    · unfold W; positivity
    · exact le_rfl
  have hpair (a : ℕ×ℕ) (ha : a∈bad) : W a≤∑ p∈Icc 3 T,v p a := by
    obtain ⟨hq,hc⟩ := mem_filter.mp ha
    obtain ⟨hx,hy⟩ := mem_product.mp hq
    obtain ⟨p,hp,hx',hy'⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
    have hodd := (mem_filter.mp hx).2
    have htwo : p≠2 := by rintro rfl; exact hodd.not_two_dvd_nat hx'
    have h2 := hp.two_le
    have hh := mem_Icc.mp (mem_filter.mp hx).1
    have hpT := (Nat.le_of_dvd hh.1 hx').trans hh.2
    have hm : a∈M p×ˢM p := mem_product.mpr ⟨mem_filter.mpr ⟨hx,hx'⟩,mem_filter.mpr ⟨hy,hy'⟩⟩
    exact (show W a=v p a by simp only [v,if_pos hm]).trans_le (single_le_sum (fun i _ => hn i a) (mem_Icc.mpr ⟨by omega,hpT⟩))
  have hp (p : ℕ) : ∑ a∈bad,v p a≤∑ a∈M p×ˢM p,W a := by
    simp only [v,←sum_filter]
    apply sum_le_sum_of_subset_of_nonneg (fun i h => (mem_filter.mp h).2)
    intro i _ _; dsimp [W]; positivity
  have hb : ∑ a∈bad,W a≤(H T)^2/2 := by
    apply (sum_le_sum hpair).trans
    rw [sum_comm]
    apply (sum_le_sum (fun p h => (hp p).trans (hs p h))).trans
    rw [←mul_sum]; linarith only [mul_le_mul_of_nonneg_left (reciprocal_sq T) (sq_nonneg (H T))]
  have ht := sum_filter_add_sum_filter_not Q (fun a => a.1.Coprime a.2) W
  rw [sqsum] at ht
  change _+∑ a∈bad,W a=(H T)^2 at ht
  linarith
theorem triangle (T : ℕ) : (H T)^2/4 ≤ ∑ d∈odds T,U d/d := by
  classical
  let Q := ((odds T)×ˢ(odds T)).filter (fun a => a.1.Coprime a.2)
  let G := Q.filter (fun a => a.1≤ a.2)
  let D := Q.filter (fun a => ¬a.1≤ a.2)
  have hsub : D.image Prod.swap⊆G := by
    intro k hk; obtain ⟨⟨a,b⟩,h,rfl⟩ := mem_image.mp hk
    obtain ⟨hq,ht⟩ := mem_filter.mp h
    obtain ⟨hf,hc⟩ := mem_filter.mp hq; obtain ⟨ha,hb⟩ := mem_product.mp hf
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_product.mpr ⟨hb,ha⟩,hc.symm⟩,(le_of_not_ge ht)⟩
  have hb : ∑ k∈D,W k≤∑ k∈G,W k := by
    calc _ = ∑ k∈D,W k.swap := sum_congr rfl (fun k _ => mul_comm ..)
         _ = ∑ k∈D.image Prod.swap,W k := (sum_image Prod.swap_injective.injOn).symm
         _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (by intros; dsimp [W]; positivity)
  have hG : ∑ k∈G,W k = ∑ d∈odds T,U d/d := by
    simp only [G,Q,sum_filter,sum_product]
    rw [sum_comm]
    apply sum_congr rfl; intro d hd
    rw [U,sum_div,sum_filter]
    have hs : odds d = (odds T).filter (·≤ d) := by
      have hdt := (mem_Icc.mp (mem_filter.mp hd).1).2
      ext w; simp only [odds,mem_filter,mem_Icc]; constructor
      · rintro ⟨⟨hw,hl⟩,ho⟩; exact ⟨⟨⟨hw,hl.trans hdt⟩,ho⟩,hl⟩
      · tauto
    rw [hs,sum_filter]
    apply sum_congr rfl; intro w _
    dsimp [W]; split_ifs <;> simp_all [div_eq_mul_inv]
  have Hsplit := sum_filter_add_sum_filter_not Q (fun a => a.1≤ a.2) W
  have Hfull := coprime_square T
  change _ ≤ ∑ a∈Q,W a at Hfull
  change (∑ k∈G,W k)+(∑ k∈D,W k)=_ at Hsplit
  linarith

theorem odd_harmonic_lower (T : ℕ) : (harmonic T:ℝ)/2 ≤ H T := by
  classical
  have h := sum_filter_add_sum_filter_not (Icc 1 T) Odd (fun n => (n:ℝ)⁻¹)
  have hsub : (((Icc 1 T).filter (fun n => ¬Odd n)).image (·/2))⊆Icc 1 T := by
    intro y hy; obtain ⟨x,hx,rfl⟩ := mem_image.mp hy
    obtain ⟨hr,ho⟩ := mem_filter.mp hx
    obtain ⟨h1,hT⟩ := mem_Icc.mp hr
    exact mem_Icc.mpr ⟨by rw [Nat.odd_iff] at ho; omega,(Nat.div_le_self ..).trans hT⟩
  have he {x : ℕ} (hx : x∈(Icc 1 T).filter (fun n => ¬Odd n)) : 2∣x := by
    have hn := (mem_filter.mp hx).2
    rw [Nat.odd_iff] at hn; omega
  have hi : Set.InjOn (fun x : ℕ => x/2) ((Icc 1 T).filter (fun n => ¬Odd n)) := by
    intro x hx y hy eq
    have hh : x/2*2=y/2*2 := congrArg (·*2) eq
    rwa [Nat.div_mul_cancel (he hx),Nat.div_mul_cancel (he hy)] at hh
  let D := (Icc 1 T).filter (fun n => ¬Odd n)
  have hz : 2*∑ n∈D,(n:ℝ)⁻¹ ≤ (harmonic T:ℝ) := by
    rw [mul_sum]
    have hh (n : ℕ) (hn : n∈D) : 2*(n:ℝ)⁻¹=((n/2:ℕ):ℝ)⁻¹ := by
      have hmul : (n:ℝ)=((n/2:ℕ):ℝ)*2 := by exact_mod_cast (Nat.div_mul_cancel (he hn)).symm
      rw [hmul,mul_inv]; ring
    rw [sum_congr rfl hh,←sum_image (f:=fun n : ℕ => (n:ℝ)⁻¹) hi]
    simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
    exact sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
  have heq : H T+(∑ n∈D,(n:ℝ)⁻¹)=(harmonic T:ℝ) := by
    simp only [H,odds,D,harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
    convert h using 3 <;> ext x <;> simp
  linarith
#print axioms triangle
#print axioms odd_harmonic_lower

#print axioms coprime_square
end
end Arxiv.«2501.03234».ThetaOddHarmonicTriangle
