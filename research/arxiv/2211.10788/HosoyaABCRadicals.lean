import FormalConjectures.Wikipedia.ABC
import LucasFibonacciDiagonalUnion

/-! The rational abc conjecture applied to the norm-44 equations for both diagonals. -/

namespace Arxiv.«2211.10788».HosoyaRadical

open Finset Filter Real
open scoped Topology

private theorem rad_pos (n : ℕ) : 0 < ABC.radical n :=
  Finset.prod_pos fun _ hp => (Nat.prime_of_mem_primeFactors hp).pos

private theorem rad_le {n : ℕ} (hn : 0<n) : ABC.radical n ≤ n :=
  Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)

private theorem rad_mul (m n : ℕ) : ABC.radical (m*n) ≤ ABC.radical m * ABC.radical n := by
  have he := Nat.prod_primeFactors_gcd_mul_prod_primeFactors_mul m n id
  change ABC.radical (m.gcd n) * ABC.radical (m*n) = ABC.radical m * ABC.radical n at he
  rw [←he]
  exact Nat.le_mul_of_pos_left _ (rad_pos _)

private theorem rad_pow (n : ℕ) {k : ℕ} (hk : 0<k) : ABC.radical (n^k) = ABC.radical n := by
  simp only [ABC.radical,Nat.primeFactors_pow _ hk.ne']

private theorem rad_mono {a b : ℕ} (hb : b ≠ 0) (hd : a ∣ b) :
    ABC.radical a ≤ ABC.radical b :=
  Nat.le_of_dvd (rad_pos _) (Finset.prod_dvd_prod_of_subset _ _ _ (Nat.primeFactors_mono hd hb))

private theorem abc_constant (hA : type_of% @ABC.abc) {e : ℝ} (he : 0 < e) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ a b c : ℕ, 0<a → 0<b → 0<c →
      ({a,b,c} : Set ℕ).Pairwise Nat.Coprime → a+b=c →
      (c:ℝ) ≤ K*(ABC.radical (a*b*c):ℝ)^(1+e) := by
  obtain ⟨B,hB⟩ := ((hA e he).image (fun t : ℕ×ℕ×ℕ => t.2.2)).bddAbove
  refine ⟨(B:ℝ)+1,by linarith [Nat.cast_nonneg (α:=ℝ) B],?_⟩
  intro a b c ha hb hc hcop ht
  let R := (ABC.radical (a*b*c):ℝ)^(1+e)
  have hR : 1 ≤ R := Real.one_le_rpow (by exact_mod_cast (rad_pos (a*b*c))) (by linarith)
  by_cases hx : R < c
  · have hB' : c ≤ B := hB ⟨(a,b,c),⟨ha,hb,hc,hcop,ht,hx⟩,rfl⟩
    have hh : (c:ℝ) ≤ B := by exact_mod_cast hB'
    change _ ≤ _*R; nlinarith only [hh,hR,mul_nonneg (Nat.cast_nonneg B) (sub_nonneg.mpr hR)]
  · change _ ≤ _*R
    exact (le_of_not_gt hx).trans (le_mul_of_one_le_left (le_trans zero_le_one hR) (by linarith [Nat.cast_nonneg (α:=ℝ) B]))

private theorem bounded_gcd_abc (hA : type_of% @ABC.abc) {e : ℝ} (he : 0<e) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ a b : ℕ, 0<a → 0<b →
      ((a+b:ℕ):ℝ) ≤ (a.gcd b:ℝ)*K*(ABC.radical (a*b*(a+b)):ℝ)^(1+e) := by
  obtain ⟨K,hK,H⟩ := abc_constant hA he
  refine ⟨K,hK,?_⟩
  intro a b ha hb
  let g := a.gcd b
  let u := a/g
  let v := b/g
  have hgu : g*u=a := Nat.mul_div_cancel' (Nat.gcd_dvd_left ..)
  have hgv : g*v=b := Nat.mul_div_cancel' (Nat.gcd_dvd_right ..)
  have hu : 0<u := by by_contra! hh; rw [Nat.eq_zero_of_le_zero hh,mul_zero] at hgu; omega
  have hv : 0<v := by by_contra! hh; rw [Nat.eq_zero_of_le_zero hh,mul_zero] at hgv; omega
  have hcop : Nat.Coprime u v := Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_left b ha)
  have hp : ({u,v,u+v} : Set ℕ).Pairwise Nat.Coprime := by
    intro x hx y hy hxy
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx hy
    rcases hx with rfl|rfl|rfl <;> rcases hy with rfl|rfl|rfl <;>
      first | contradiction | simpa only [Nat.coprime_self_add_right,Nat.coprime_add_self_right,
        Nat.coprime_self_add_left,Nat.coprime_add_self_left] using hcop |
        simpa only [Nat.coprime_self_add_right,Nat.coprime_add_self_right,
        Nat.coprime_self_add_left,Nat.coprime_add_self_left] using hcop.symm
  have hh := H u v (u+v) hu hv (by omega) hp rfl
  have hgc : g*(u+v)=a+b := by rw [Nat.mul_add,hgu,hgv]
  have hd : u*v*(u+v) ∣ a*b*(a+b) := ⟨g^3,by rw [←hgc,←hgu,←hgv]; ring⟩
  have hrad := rad_mono (by positivity : a*b*(a+b)≠0) hd
  have hle := Real.rpow_le_rpow (by positivity : 0 ≤ (ABC.radical (u*v*(u+v)):ℝ))
    (show (ABC.radical (u*v*(u+v)):ℝ) ≤ (ABC.radical (a*b*(a+b)):ℝ) by exact_mod_cast hrad) (by linarith : 0 ≤ 1+e)
  calc ((a+b:ℕ):ℝ) = (g:ℝ)*(u+v:ℕ) := by exact_mod_cast hgc.symm
       _ ≤ (g:ℝ)*(K*(ABC.radical (a*b*(a+b)):ℝ)^(1+e)) := by
         gcongr
         exact hh.trans (mul_le_mul_of_nonneg_left hle (by linarith))
       _ = _ := by ring


private theorem pell_rad_bound (hA : type_of% @ABC.abc) {e : ℝ} (he : 0<e) :
    ∃ C : ℝ, 0<C ∧ ∀ x y : ℕ, 0<y → (x^2=5*y^2+44 ∨ x^2+44=5*y^2) →
      (y:ℝ)^2 ≤ C*((y:ℝ)*(ABC.radical y:ℝ))^(1+e) := by
  obtain ⟨K,hK,H⟩ := bounded_gcd_abc hA he
  refine ⟨44*K*1540^(1+e),by positivity,?_⟩
  intro x y hy hxy
  have hx' : x ≤ 7*y := by
    rcases hxy with h | h <;> by_contra! hh <;>
      nlinarith only [h, Nat.mul_self_le_mul_self (show 7*y+1≤x by omega),
        Nat.mul_self_le_mul_self (show 1≤y by omega)]
  have hx : 0<x := by
    by_contra! hh
    obtain rfl : x=0 := by omega
    rcases hxy with h | h <;> norm_num at h; omega
  have hr : ABC.radical (220*x^2*y^2) ≤ 1540*y*ABC.radical y := by
    calc ABC.radical (220*x^2*y^2) ≤ ABC.radical (220*x^2)*ABC.radical (y^2) := rad_mul ..
      _ ≤ (ABC.radical 220*ABC.radical (x^2))*ABC.radical (y^2) :=
        Nat.mul_le_mul_right _ (rad_mul ..)
      _ ≤ 1540*y*ABC.radical y := by
        rw [rad_pow _ (by decide : 0<2),rad_pow _ (by decide : 0<2)]
        have h220 : ABC.radical 220 ≤ 220 := rad_le (by decide)
        apply Nat.mul_le_mul_right
        calc ABC.radical 220*ABC.radical x ≤ 220*x := Nat.mul_le_mul h220 (rad_le hx)
          _ ≤ 1540*y := by omega
  have estimate (a : ℕ) (ha : 0<a) (hc : y^2 ≤ a+44) (hh : a*44*(a+44)=220*x^2*y^2) :
      (y:ℝ)^2 ≤ 44*K*1540^(1+e)*((y:ℝ)*(ABC.radical y:ℝ))^(1+e) := by
    have hd := Nat.le_of_dvd (by decide : 0<44) (Nat.gcd_dvd_right a 44)
    have h₁ := H a 44 ha (by decide)
    rw [hh] at h₁
    calc (y:ℝ)^2 ≤ ((a+44:ℕ):ℝ) := by exact_mod_cast hc
      _ ≤ _ := h₁
      _ ≤ 44*K*(1540*((y:ℝ)*(ABC.radical y:ℝ)))^(1+e) := by
        gcongr
        · exact_mod_cast hd
        · push_cast at *; exact_mod_cast (show ABC.radical (220*x^2*y^2) ≤ 1540*(y*ABC.radical y) by simpa [Nat.mul_assoc] using hr)
      _ = _ := by rw [Real.mul_rpow (by norm_num) (by positivity)]; ring
  rcases hxy with hh | hh
  · exact estimate (5*y^2) (by positivity) (by omega) (by rw [← hh]; ring)
  · exact estimate (x^2) (by positivity) (by omega) (by rw [hh]; ring)


/-- On the union of the two diagonals, rational abc forces the radical to
exceed every fixed power below the first power, eventually in the value. -/
theorem eventual_diagonal_radical (hA : type_of% @ABC.abc) {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ y : ℕ in atTop, ((∃ n, y=lucasFibonacciSum n) ∨ IsLowerNeighborValue y) →
      (y:ℝ)^(1-δ) < (ABC.radical y:ℝ) := by
  let e := δ/4
  have he : 0<e := by dsimp [e]; positivity
  obtain ⟨C,hC,hB⟩ := pell_rad_bound hA he
  have ht : Tendsto (fun y : ℕ => (y:ℝ)^(δ/2)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity : 0<δ/2)).comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually_gt_atTop C,eventually_ge_atTop 1] with y hy hy₁
  intro h
  obtain ⟨x,hx⟩ := (either_diagonal_iff_pell y).mp h
  have hB' := hB x y (by omega) hx
  have hy' : 1 ≤ (y:ℝ) := by exact_mod_cast hy₁
  have hypos : 0 < (y:ℝ) := by linarith
  by_contra! hbad
  have hineq : (y:ℝ)^2 ≤ C*(y:ℝ)^(2-δ/2) := by
    calc (y:ℝ)^2 ≤ _ := hB'
      _ ≤ C*((y:ℝ)*(y:ℝ)^(1-δ))^(1+e) := by gcongr
      _ = C*(y:ℝ)^((2-δ)*(1+e)) := by
        rw [show (2:ℝ)-δ = 1+(1-δ) by ring,Real.rpow_mul hypos.le,
          Real.rpow_add hypos,Real.rpow_one]
      _ ≤ _ := by
        gcongr
        dsimp [e]; nlinarith [sq_nonneg δ]
  have heq : (y:ℝ)^2 = (y:ℝ)^(δ/2)*(y:ℝ)^(2-δ/2) := by
    rw [←Real.rpow_add hypos,show δ/2+(2-δ/2)=2 by ring]; norm_num
  rw [heq] at hineq
  exact (not_le_of_gt hy) ((mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hypos _)).mp hineq)

#print axioms eventual_diagonal_radical


/-- Product of the prime divisors occurring with exponent exactly one. -/
def simplePart (y : ℕ) : ℕ := (y.primeFactors.filter (fun p => y.factorization p=1)).prod id

theorem radical_sq_le_simple {y : ℕ} (hy : y≠0) :
    (ABC.radical y)^2 ≤ y * simplePart y := by
  have he := Nat.prod_primeFactors_pow_factorization hy
  calc (ABC.radical y)^2 = ∏ p ∈ y.primeFactors, p^2 := by rw [ABC.radical,← Finset.prod_pow]; rfl
       _ ≤ ∏ p ∈ y.primeFactors, (p^(y.factorization p)*(if y.factorization p=1 then p else 1)) := by
          apply Finset.prod_le_prod'
          intro p hp
          have hpp := Nat.prime_of_mem_primeFactors hp
          have hf := hpp.factorization_pos_of_dvd hy (Nat.dvd_of_mem_primeFactors hp)
          split_ifs with hh
          · rw [hh,pow_one,pow_two]
          · rw [mul_one]; exact Nat.pow_le_pow_right hpp.pos (by omega)
       _ = y * simplePart y := by
          rw [Finset.prod_mul_distrib,← he,simplePart,Finset.prod_filter]; rfl

/-- Even after discarding every prime that occurs with multiplicity greater
than one, the remaining product exceeds y^(1−δ) eventually. -/
theorem eventual_diagonal_simple_part (hA : type_of% @ABC.abc) {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ y : ℕ in atTop, ((∃ n, y=lucasFibonacciSum n) ∨ IsLowerNeighborValue y) →
      (y:ℝ)^(1-δ) < (simplePart y:ℝ) := by
  filter_upwards [eventual_diagonal_radical hA (show 0<δ/2 by positivity),eventually_gt_atTop 0]
    with y hrad hy
  intro h
  have hy' : 0 < (y:ℝ) := by exact_mod_cast hy
  have hsq := pow_lt_pow_left₀ (hrad h) (Real.rpow_nonneg hy'.le _) (by decide : (2:ℕ)≠0)
  have he : ((y:ℝ)^(1-δ/2))^2 = (y:ℝ)*(y:ℝ)^(1-δ) := by
    rw [←Real.rpow_mul_natCast hy'.le,mul_comm (y:ℝ),←Real.rpow_add_one hy'.ne']
    congr 1; push_cast; ring
  have hh : (ABC.radical y:ℝ)^2 ≤ (y:ℝ)*(simplePart y:ℝ) := by exact_mod_cast radical_sq_le_simple hy.ne'
  rw [he] at hsq
  exact (mul_lt_mul_iff_right₀ hy').mp (hsq.trans_le hh)

#print axioms radical_sq_le_simple
#print axioms eventual_diagonal_simple_part

end Arxiv.«2211.10788».HosoyaRadical
