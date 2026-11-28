import research.arxiv.«1104.1579».CunninghamPrimeSquareTails
import research.arxiv.«1104.1579».CunninghamPrimeDirichletMass

/-! Squarefree sieving at prime arguments in a prescribed reduced residue class. -/

namespace CunninghamChain
namespace SquarefreeAtPrimes
open Filter Finset Topology PrimeMass

private def prog (m b : ℕ) : Set ℕ := {n | n ≡ b [MOD m]}

private theorem progression_mass {m b : ℕ} [NeZero m] (hc : b.Coprime m) :
    Tendsto (fun s : ℝ => (s-1)*mass (prog m b) s) (𝓝[>] 1) (𝓝 ((m.totient:ℝ)⁻¹)) := by
  have h : prog m b = {n : ℕ | (n:ZMod m)=(b:ZMod m)} :=
    Set.ext fun n => (ZMod.natCast_eq_natCast_iff ..).symm
  rw [h]
  exact mass_progression _ ((ZMod.isUnit_iff_coprime ..).mpr hc)

private theorem pair_mass {m b q a : ℕ} [NeZero m] (hc : b.Coprime m) (hp : q.Prime)
    (hm : m.Coprime q) (ha : a.Coprime q) :
    Tendsto (fun s : ℝ => (s-1)*mass (prog m b ∩ prog (q^2) a) s) (𝓝[>] 1)
      (𝓝 ((m.totient:ℝ)⁻¹*(1/((q:ℝ)*(q-1:ℕ))))) := by
  let : NeZero (m*q^2) := ⟨Nat.mul_ne_zero (NeZero.ne _) (pow_ne_zero _ hp.ne_zero)⟩
  have cop := hm.pow_right 2
  obtain ⟨b',hb,hq⟩ := Nat.chineseRemainder cop b a
  have hc₁ : b'.Coprime m := hb.gcd_eq.trans hc
  have hc₂ : b'.Coprime (q^2) := hq.gcd_eq.trans (ha.pow_right 2)
  have hset : prog m b ∩ prog (q^2) a = prog (m*q^2) b' := by
    ext n
    change (n≡b [MOD m] ∧ n≡a [MOD q^2]) ↔ n≡b' [MOD m*q^2]
    rw [←Nat.modEq_and_modEq_iff_modEq_mul cop]
    exact and_congr ⟨fun h => h.trans hb.symm,fun h => h.trans hb⟩
      ⟨fun h => h.trans hq.symm,fun h => h.trans hq⟩
  rw [hset]
  have lim := progression_mass (hc₁.mul_right hc₂)
  rw [Nat.totient_mul cop,Nat.totient_prime_pow_succ hp 1,pow_one] at lim
  simpa only [Nat.cast_mul,mul_inv_rev,one_div,mul_comm] using lim

private def largeHits (a : ℕ → ℕ) (D L : ℕ) : Set ℕ :=
  {p | ∃ q, q.Prime ∧ L<q ∧ q^2≤D*p ∧ p%q^2=a q}

private theorem big_weight (a : ℕ → ℕ) (D L : ℕ) (hL : 0<L) :
    ∀ᶠ X : ℕ in atTop, ∑ n ∈ range X,weight (largeHits a D L) n ≤ (1632/(L:ℝ))*X := by
  classical
  filter_upwards [eventually_large_square_class_primes a D L hL, eventually_ge_atTop 1] with X bound hx
  let A := largeSquareClassPrimes a D L X
  have incl {n : ℕ} (hn : n ∈ range X) (hp : n.Prime) (hi : n∈largeHits a D L) : n∈A := by
    obtain ⟨q,hq,hl,hd,he⟩ := hi
    exact mem_filter.mpr ⟨hn,hp,q,Nat.mem_primesLE.mpr
      ⟨Nat.le_sqrt'.mpr (hd.trans (Nat.mul_le_mul_left D (mem_range.mp hn).le)),hq⟩,hl,he⟩
  have per (n : ℕ) (hn : n∈range X) :
      weight (largeHits a D L) n ≤ if n∈A then Real.log X else 0 := by
    by_cases hh : n.Prime ∧ n∈largeHits a D L
    · rw [weight,if_pos hh,if_pos (incl hn hh.1 hh.2)]
      exact Real.log_le_log (by exact_mod_cast hh.1.pos) (by exact_mod_cast (mem_range.mp hn).le)
    · rw [weight,if_neg hh]; split_ifs
      · exact Real.log_nonneg (by exact_mod_cast hx)
      · rfl
  have sub : A ⊆ range X := filter_subset ..
  have cast : (range X).filter (fun n => n∈A)=A := by ext n; simp only [mem_filter]; exact and_iff_right_of_imp (fun h => sub h)
  calc
    _ ≤ _ := sum_le_sum per
    _ = (A.card:ℝ)*Real.log X := by rw [←sum_filter,cast,sum_const,nsmul_eq_mul]
    _ ≤ _ := by simpa [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using bound

private theorem small_sum {Q : Finset ℕ} {R L k : ℕ} {u : ℝ} (hu : 0≤u) (hR : 0<R)
    (hk : 4*k≤R) (hq : Q ⊆ Ioc R L) (hp : ∀ q ∈ Q,q.Prime) :
    ∑ j ∈ Q ×ˢ (univ : Finset (Fin k)), u*(1/((j.1:ℝ)*(j.1-1:ℕ))) ≤ u/2 := by
  have one (q : ℕ) (hq' : q∈Q) : 1/((q:ℝ)*(q-1:ℕ)) ≤ 2*(1/(q:ℝ)^2) := by
    have hq₂ : 2≤q := (hp q hq').two_le
    have hq₂' : (2:ℝ)≤q := by exact_mod_cast hq₂
    rw [Nat.cast_sub (by omega : 1≤q),Nat.cast_one]
    have hh : 0 < (q:ℝ)-1 := by linarith
    field_simp [hh]
    linarith only [hq₂']
  rw [sum_product]
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hsum := reciprocal_square_tail_finset hR hq
  have hscale : (k:ℝ)*2/(R:ℝ) ≤ 1/2 := by
    have hk' : (4:ℝ)*k≤R := by exact_mod_cast hk
    apply (div_le_iff₀ (by exact_mod_cast hR : (0:ℝ)<R)).mpr
    linarith
  calc
    _ ≤ ∑ q ∈ Q, (u*((k:ℝ)*2))*(1/(q:ℝ)^2) := sum_le_sum fun q hq' => by
      have h := mul_le_mul_of_nonneg_left (one q hq') (mul_nonneg (Nat.cast_nonneg k) hu)
      linarith only [h]
    _ = (u*((k:ℝ)*2))*(∑ q ∈ Q, 1/(q:ℝ)^2) := (mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity : 0≤u*((k:ℝ)*2))
    _ ≤ u/2 := by
      simpa only [div_eq_mul_inv,one_mul,mul_assoc] using mul_le_mul_of_nonneg_left hscale hu

/-- Infinitely many prime seeds in a reduced progression avoid all the prescribed
square classes above R, up to the sizes that can divide a linear value at the seed. -/
theorem infinitely_many_avoiding_squares {m b k R : ℕ} [NeZero m] (hb : b.Coprime m)
    (hR : 0<R) (hk : 4*k≤R) (D : ℕ) (a : Fin k → ℕ → ℕ)
    (hcop : ∀ q, q.Prime → R<q → m.Coprime q)
    (hunit : ∀ i q, q.Prime → R<q → (a i q).Coprime q) :
    {p : ℕ | p.Prime ∧ p ≡ b [MOD m] ∧ ∀ i q, q.Prime → R<q → q^2≤D*p →
      ¬p≡a i q [MOD q^2]}.Infinite := by
  classical
  let G := {p : ℕ | p.Prime ∧ p ≡ b [MOD m] ∧ ∀ i q, q.Prime → R<q → q^2≤D*p →
    ¬p≡a i q [MOD q^2]}
  change G.Infinite
  intro hfin
  let u := (m.totient:ℝ)⁻¹
  have hu : 0<u := inv_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos m))
  obtain ⟨L,hlarge⟩ := exists_nat_gt ((k:ℝ)*1632/(u/4)+R+1)
  have hR' : (R:ℝ) < L := by linarith only [hlarge,div_nonneg (show 0≤(k:ℝ)*1632 by positivity) (by positivity : 0 ≤ u/4)]
  have hL : 0<L := hR.trans (by exact_mod_cast hR')
  have hL' : 0<(L:ℝ) := by exact_mod_cast hL
  let Q := L.primesLE.filter (R<·)
  let J := Q ×ˢ (univ : Finset (Fin k))
  let S (j : ℕ × Fin k) := prog m b ∩ prog (j.1^2) (a j.2 j.1)
  let v (j : ℕ × Fin k) := u*(1/((j.1:ℝ)*(j.1-1:ℕ)))
  let Z (i : Fin k) := largeHits (fun q => a i q%q^2) D L
  let B := {p : ℕ | ∃ i, p∈Z i}
  have hQ {q} (hq : q∈Q) : q.Prime ∧ R<q ∧ q≤L := by
    obtain ⟨hp,hl⟩ := mem_filter.mp hq
    exact ⟨Nat.prime_of_mem_primesLE hp,hl,Nat.le_of_mem_primesLE hp⟩
  have hcov (p : ℕ) (hm : p∈prog m b) (hp : p.Prime) :
      (∃ j∈J,p∈S j) ∨ p∈B ∨ p∈G := by
    by_cases good : p∈G
    · exact Or.inr (Or.inr good)
    have hex : ∃ i q, q.Prime ∧ R<q ∧ q^2≤D*p ∧ p≡a i q [MOD q^2] := by
      by_contra! he
      exact good ⟨hp,hm,he⟩
    obtain ⟨i,q,hq,hr,hsize,he⟩ := hex
    by_cases hqL : q≤L
    · have hqin : q∈Q := mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hqL,hq⟩,hr⟩
      exact Or.inl ⟨(q,i),mem_product.mpr ⟨hqin,mem_univ _⟩,hm,he⟩
    · exact Or.inr (Or.inl ⟨i,q,hq,by omega,hsize,he⟩)
  have hBsum : ∀ᶠ X : ℕ in atTop, ∑ n ∈ range X,weight B n ≤ ((k:ℝ)*(1632/L))*X := by
    have each (i : Fin k) := big_weight (fun q => a i q%q^2) D L hL
    filter_upwards [eventually_all.mpr each] with X hX
    have per (n : ℕ) : weight B n ≤ ∑ i : Fin k,weight (Z i) n := by
      by_cases hn : n.Prime ∧ n∈B
      · obtain ⟨i,hi⟩ := hn.2
        rw [weight,if_pos hn]
        have hw := single_le_sum (f:=fun i : Fin k => weight (Z i) n)
          (fun j _ => weight_nonneg (Z j) n) (mem_univ i)
        rwa [show weight (Z i) n=Real.log n from if_pos ⟨hn.1,hi⟩] at hw
      · rw [weight,if_neg hn]; exact sum_nonneg (fun _ _ => weight_nonneg ..)
    calc
      _ ≤ ∑ n ∈ range X, ∑ i : Fin k,weight (Z i) n := sum_le_sum (fun n _ => per n)
      _ = _ := sum_comm
      _ ≤ ∑ _ : Fin k,(1632/(L:ℝ))*X := sum_le_sum (fun i _ => hX i)
      _ = _ := by simp [mul_assoc]
  have hC : (k:ℝ)*(1632/L)<u/4 := by
    have hl : (k:ℝ)*1632/(u/4)<L := by linarith only [hlarge,Nat.cast_nonneg (α:=ℝ) R]
    rw [div_lt_iff₀ (by positivity : 0<u/4)] at hl
    rw [←mul_div_assoc,div_lt_iff₀ hL']
    linarith
  have hBad := eventually_mass_lt_of_sum_le B (by positivity) hC hBsum
  have hsmall : Tendsto (fun s : ℝ => (s-1)*(∑ j ∈ J,mass (S j) s)) (𝓝[>] 1) (𝓝 (∑ j∈J,v j)) := by
    simp only [mul_sum]
    apply tendsto_finsetSum
    rintro ⟨q,i⟩ hj
    obtain ⟨hp,hr,_⟩ := hQ (mem_product.mp hj).1
    exact pair_mass hb hp (hcop q hp hr) (hunit i q hp hr)
  have total := ((hsmall.add_const (u/4)).add (finite_mass_tendsto hfin))
  have low := progression_mass hb
  have bound : u ≤ ((∑ j∈J,v j)+u/4)+0 := by
    apply le_of_tendsto_of_tendsto low total
    filter_upwards [self_mem_nhdsWithin,hBad] with s hs hsB
    have hs₁ : 1<s := hs
    have cover := mass_le_cover J S (prog m b) B G hcov hs₁
    have hmul := mul_le_mul_of_nonneg_left cover (sub_nonneg.mpr hs₁.le)
    linarith only [hmul,hsB]
  have localBound : ∑ j ∈ J,v j ≤ u/2 :=
    small_sum hu.le hR hk (fun q hq => mem_Ioc.mpr (hQ hq).2) (fun q hq => (hQ hq).1)
  linarith only [bound,localBound,hu]

#print axioms infinitely_many_avoiding_squares

end SquarefreeAtPrimes
end CunninghamChain
