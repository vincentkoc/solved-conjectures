import HosoyaIntegerPowerTests
import LucasFibonacciAlmostPrimeClosure

/-! Signed integral powers are the only congruence limits for the upper
Hosoya sequence on indices r+d n^e. -/

namespace Arxiv.«2211.10788».PowerIndex
open AlmostPrimeClosure CongruenceClosure ProgressionClosure

/-- Any arbitrarily well approximable signed base gives arbitrarily late
modular hits at its power in an affine index progression. -/
theorem hits_of_approximable_base {W : ℕ → Prop} {d r e : ℕ} {v y : ℤ}
    (ep : 0 < e) (val : signed (r+d*v^e)=y)
    (approx : ∀ T : ℕ, 0 < T → ∀ B : ℕ, ∃ n : ℕ, B<n ∧ W n ∧ (n:ℤ) ≡ v [ZMOD T])
    {M : ℕ} (mp : 0 < M) (B : ℕ) :
    ∃ n : ℕ, B<n ∧ W n ∧ Hit d r M y (n^e) := by
  let : NeZero M := ⟨mp.ne'⟩
  obtain ⟨T,tp,per⟩ := signed_forward_period M ((r:ℤ)+d*v^e)
  obtain ⟨n,big,weight,cl⟩ := approx T tp (max B (v^e).natAbs)
  have le := Nat.le_self_pow ep.ne' n
  have lt : v^e ≤ (↑(n^e):ℤ) := by omega
  have cls : ((n^e:ℕ):ℤ) ≡ v^e [ZMOD T] := by exact_mod_cast cl.pow e
  have mod := per ((r:ℤ)+d*(n^e:ℕ)) (by gcongr) ((cls.mul_left (d:ℤ)).add_left (r:ℤ))
  rw [val,show (r:ℤ)+d*(n^e:ℕ)=((r+d*n^e:ℕ):ℤ) by push_cast; rfl,signed_nat] at mod
  exact ⟨n,by omega,weight,(ZMod.intCast_eq_intCast_iff ..).mp (by simpa only [Int.cast_natCast] using mod)⟩

private lemma natural_approx (v : ℤ) (T B : ℕ) (tp : 0 < T) :
    ∃ n : ℕ, B<n ∧ (n:ℤ) ≡ v [ZMOD T] := by
  let a := (v % (T:ℤ)).toNat
  have mod : (a:ℤ) ≡ v [ZMOD T] := by
    dsimp [a]
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast tp.ne'))]
    exact Int.mod_modEq _ _
  let n := a+(B+1)*T
  have big : B<n := by
    have := Nat.le_mul_of_pos_right (B+1) tp
    dsimp [n]; omega
  refine ⟨n,big,?_⟩
  have z : (n:ℤ) ≡ a [ZMOD T] := by
    apply Int.modEq_iff_dvd.mpr
    refine ⟨-(B+1:ℤ),?_⟩
    dsimp [n]; ring
  exact z.trans mod

/-- All modulus tests for positive power indices, even with a prescribed
finite set of modulus primes omitted, recover an exact bilateral power. -/
theorem power_indices_iff {d r e E : ℕ} (hd : 0 < d) (ep : 0 < e) (pe : 0 < E) (y : ℤ) :
    (∀ M : ℕ, 0 < M → M.Coprime E → ∃ n : ℕ, Hit d r M y (n^e)) ↔
      ∃ v : ℤ, signed (r+d*v^e)=y := by
  constructor
  · intro all
    let B := y.natAbs+r+2
    let D := 4*B.factorial^2
    have dp : 0 < D := by dsimp [D]; positivity
    obtain ⟨h,_,cop⟩ := exists_coprime_detector (d*D) y pe
    have mp : 0 < detector (d*D) y h := Nat.mul_pos
      (Nat.zero_lt_of_lt (layer_size (Nat.mul_pos hd dp) y _))
      (Nat.zero_lt_of_lt (layer_size (Nat.mul_pos hd dp) y _))
    obtain ⟨n,hit⟩ := all _ mp cop
    obtain ⟨w,cl,val,small⟩ := recover_parameter hd dp r (n^e) h y hit
    obtain ⟨v,hv⟩ := bounded_power_test B (t:=(n:ℤ)) ep small (by simpa only [D,Nat.cast_pow] using cl)
    exact ⟨v,hv ▸ val⟩
  · rintro ⟨v,val⟩ M mp _
    have ap (T : ℕ) (tp : 0 < T) (B : ℕ) : ∃ n : ℕ, B<n ∧ True ∧ (n:ℤ) ≡ v [ZMOD T] := by
      obtain ⟨n,big,cl⟩ := natural_approx v T B tp
      exact ⟨n,big,trivial,cl⟩
    obtain ⟨n,_,_,hit⟩ := hits_of_approximable_base ep val ap mp 0
    exact ⟨n,hit⟩

/-- At even exponents the bilateral power is always a natural power. -/
theorem even_power_indices_iff {d r e E : ℕ} (hd : 0 < d) (ep : 0 < e) (ev : Even e)
    (pe : 0 < E) (y : ℤ) :
    (∀ M : ℕ, 0 < M → M.Coprime E → ∃ n : ℕ, Hit d r M y (n^e)) ↔
      ∃ n : ℕ, (lucasFibonacciSum (r+d*n^e):ℤ)=y := by
  rw [power_indices_iff hd ep pe]
  constructor
  · rintro ⟨v,val⟩
    refine ⟨v.natAbs,?_⟩
    have eq : (v.natAbs:ℤ)^e=v^e := by
      rw [Int.natCast_natAbs]
      rcases le_total 0 v with h|h
      · rw [abs_of_nonneg h]
      · rw [abs_of_nonpos h,ev.neg_pow]
    rw [←eq,show (r:ℤ)+d*(v.natAbs:ℤ)^e=((r+d*v.natAbs^e:ℕ):ℤ) by push_cast; rfl,signed_nat] at val
    exact val
  · rintro ⟨n,val⟩
    refine ⟨n,?_⟩
    rwa [show (r:ℤ)+d*(n:ℤ)^e=((r+d*n^e:ℕ):ℤ) by push_cast; rfl,signed_nat]

/-- Every odd exponent admits arbitrarily large positive congruence limits
which are absent even from the entire nonnegative upper diagonal. -/
theorem arbitrarily_large_odd_power_impostors {e E : ℕ} (od : Odd e) (pe : 0 < E) (B : ℕ) :
    ∃ y : ℕ, B<y ∧ (∀ n : ℕ, lucasFibonacciSum n≠y) ∧
      ∀ M : ℕ, 0 < M → M.Coprime E → ∃ n : ℕ, lucasFibonacciSum (n^e) ≡ y [MOD M] := by
  have ep : 0 < e := by obtain ⟨l,hl⟩ := od; omega
  let a := 2*B+11
  have ap : a ≤ a^e := Nat.le_self_pow ep.ne' a
  have oa : Odd a := ⟨B+5,by dsimp [a]; ring⟩
  let j := a^e-2
  have ix : a^e=j+2 := by dsimp [j,a] at *; omega
  have parity : Even (j+1) := by
    obtain ⟨u,hu⟩ := oa.pow (n:=e)
    exact ⟨u,by omega⟩
  let y := lowerNeighborAtAddTwo j
  have val : signed (-((a^e:ℕ):ℤ))=(y:ℤ) := by
    conv_lhs => rw [ix,signed_lower]
    simp [parity.neg_one_pow,y]
  have bound := signed_index_bound (-((a^e:ℕ):ℤ))
  rw [val] at bound
  simp only [Int.natAbs_neg,Int.natAbs_natCast] at bound
  have init : 2*B+11 ≤ a^e := ap
  change a^e ≤ y+2 at bound
  have low : B<y ∧ 5<y := by omega
  refine ⟨y,low.1,?_,?_⟩
  · intro n same
    exact low.2.ne' ((both_diagonals_iff_five y).mp ⟨⟨n,same.symm⟩,Or.inr ⟨j,rfl⟩⟩)
  · have hit := (power_indices_iff (r:=0) (d:=1) (by decide) ep pe (y:ℤ)).mpr
       ⟨-(a:ℤ),by simpa [od.neg_pow] using val⟩
    simpa only [Hit,one_mul,zero_add,Int.natCast_modEq_iff] using hit

#print axioms arbitrarily_large_odd_power_impostors
#print axioms hits_of_approximable_base
#print axioms power_indices_iff
#print axioms even_power_indices_iff

end Arxiv.«2211.10788».PowerIndex
