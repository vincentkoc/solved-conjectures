import HosoyaDetectedPowerWindows
import HosoyaPowerWindows

/-! Valuations at private primes detect every rational power relation modulo S-units. -/
namespace Arxiv.«2211.10788».PowerGaps
open Finset HosoyaPowerIsolation HosoyaNeighbor

private noncomputable def valuation (q : ℕ) [Fact q.Prime] : ℚˣ →* Multiplicative ℤ where
  toFun x := Multiplicative.ofAdd (padicValRat q (x:ℚ))
  map_one' := by simp
  map_mul' x y := padicValRat.mul (Units.ne_zero x) (Units.ne_zero y)

private theorem value_at (q : ℕ) (pr : q.Prime) (u : HosoyaNeighbor × ℕ) [Fact q.Prime] :
    valuation q (siteUnit u)=Multiplicative.ofAdd ((u.1.value u.2).factorization q:ℤ) := by
  change padicValRat q (u.1.value u.2:ℚ)=((u.1.value u.2).factorization q:ℤ)
  rw [padicValRat.of_nat,←Nat.factorization_def _ pr]

private theorem quotient_of_failure {k : ℕ} {e : ℤ} (kp : 0<k) (miss : ¬(k:ℤ)∣e) :
    ∃ t : ℕ, 2≤t ∧ t≤k ∧ ∀ v : ℕ, (k:ℤ)∣e*v → t∣v := by
  obtain ⟨g,t,b,gp,co,kt,eb⟩ := Nat.exists_coprime' (m:=k) (n:=e.natAbs)
    (Nat.gcd_pos_of_pos_left _ kp)
  have no : ¬k∣e.natAbs := fun h => miss (Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr h))
  have tp : t≠0 := by intro h;rw [h,zero_mul] at kt;omega
  have two : 2≤t := by
    by_contra! h
    have one : t=1 := by omega
    apply no
    rw [kt,one,one_mul,eb]
    exact dvd_mul_left ..
  refine ⟨t,two,kt ▸ Nat.le_mul_of_pos_right _ gp,?_⟩
  intro v dv
  have div : k∣e.natAbs*v := by
    simpa only [Int.natAbs_natCast,Int.natAbs_mul] using Int.natAbs_dvd_natAbs.mpr dv
  rw [kt,eb] at div
  exact co.dvd_of_dvd_mul_left (Nat.dvd_of_mul_dvd_mul_left gp
    (by simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using div))

/-- In a detected window the criterion applies to arbitrary signed exponents
and arbitrary rational S-units for each positive modulus through K. -/
theorem detected_power_iff (S : Finset ℕ) {H K n : ℕ} (good : goodWindow S H K n)
    (T : Finset (HosoyaNeighbor × ℕ)) (within : ∀ u∈T, n≤u.2 ∧ u.2≤n+H)
    (e : HosoyaNeighbor × ℕ → ℤ) {k : ℕ} (kp : 0<k) (small : k≤K) :
    (∃ a z : ℚˣ, IsRationalSUnit S a ∧ (∏ u∈T, siteUnit u ^ e u) = a*z^(k:ℤ)) ↔
      ∀ u∈T, (k:ℤ) ∣ e u := by
  classical
  constructor
  · rintro ⟨a,z,unit,eq⟩ u hu
    by_contra miss
    obtain ⟨t,two,tk,quot⟩ := quotient_of_failure kp miss
    obtain ⟨lo,hi⟩ := within u hu
    have atSite := good u.1 (u.2-n) (by omega) t two (tk.trans small)
    rw [Nat.add_sub_of_le lo] at atSite
    obtain ⟨q,pf,out,mult⟩ := atSite
    obtain ⟨pr,dv,_⟩ := Nat.mem_primeFactors.mp pf
    let : Fact q.Prime := ⟨pr⟩
    let V := valuation q
    have others (v : HosoyaNeighbor × ℕ) (hv : v∈T) (ne : v≠u) : V (siteUnit v ^ e v)=1 := by
      have diff : u.1≠v.1 ∨ u.2≠v.2 := by by_contra! h;exact ne (Prod.ext h.1 h.2).symm
      have bounds := within v hv
      have nd : ¬q∣v.1.value v.2 := fun shared => out (mem_union_right _ (Nat.mem_primeFactors.mpr
        ⟨pr,dvd_shiftDetProduct_of_shared diff (by simp only [Nat.dist];omega) dv shared,(shiftDetProduct_pos H).ne'⟩))
      rw [map_zpow,value_at q pr,Nat.factorization_eq_zero_of_not_dvd nd]
      simp
    have va : V a=1 := unit q pr (fun h => out (mem_union_left _ h))
    have mapped := congrArg (fun x : ℚˣ => V x) eq
    change V (∏ v∈T,siteUnit v^e v)=V (a*z^(k:ℤ)) at mapped
    rw [map_prod,map_mul,va,one_mul,map_zpow,prod_eq_single_of_mem u hu others,map_zpow,value_at q pr] at mapped
    have id := congrArg Multiplicative.toAdd mapped
    apply mult (quot _ ⟨(V z).toAdd,?_⟩)
    simpa [toAdd_zpow,zsmul_eq_mul] using id
  · intro yes
    refine ⟨1, ∏ u∈T, siteUnit u^(e u/k), ?_,?_⟩
    · intro p _ _;simp
    · rw [one_mul,←Finset.prod_zpow]
      exact prod_congr rfl (fun u hu => by rw [←zpow_mul,Int.ediv_mul_cancel (yes u hu)])

#print axioms detected_power_iff
end Arxiv.«2211.10788».PowerGaps
