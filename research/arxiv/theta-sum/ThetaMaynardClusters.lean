import ThetaAffineClusters

/-! An explicit admissible tuple for clusters of positive theta primes in the class one modulo eight. -/
namespace Arxiv.«2501.03234».ThetaMaynardClusters
open Finset Filter Real ThetaPrimeClusterTransfer ThetaClassOneClusters ThetaAffineClusters
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

def step (k : ℕ) := 8*k.factorial
def form (k n j : ℕ) := 8*n+1+step k*j
def diameter (k : ℕ) := 1+step k*k

/-- No prime divides the product of the fixed forms at every integer. -/
theorem admissible (k q : ℕ) (hq : q.Prime) : ∃ n : ℕ,∀ j<k,¬q∣form k n j := by
  let : Fact q.Prime := ⟨hq⟩
  by_cases hA : ((step k:ℕ):ZMod q)=0
  · refine ⟨0,?_⟩
    intro j _ hd
    have h := (ZMod.natCast_eq_zero_iff _ _).mpr hd
    simp [form,Nat.cast_add,Nat.cast_mul,hA] at h
  · have hqk : k<q := by
      by_contra! hl
      apply hA
      exact (ZMod.natCast_eq_zero_iff _ _).mpr ((Nat.dvd_factorial hq.pos hl).trans (dvd_mul_left _ _))
    have h8 : (8:ZMod q)≠0 := by
      intro hz
      apply hA
      simp [step,Nat.cast_mul,hz]
    let A := ((step k:ℕ):ZMod q)
    let x := (A-1)/8
    refine ⟨x.val,?_⟩
    intro j hj hd
    have hz := (ZMod.natCast_eq_zero_iff _ _).mpr hd
    have hj' : ((j+1:ℕ):ZMod q)≠0 := by
      intro h
      obtain h' := (ZMod.natCast_eq_zero_iff _ _).mp h
      have := Nat.le_of_dvd (Nat.succ_pos _) h'
      omega
    have hzero : A*((j+1:ℕ):ZMod q)=0 := by
      apply Eq.trans _ hz
      simp only [form,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,ZMod.natCast_zmod_val]
      dsimp [A,x]
      field_simp
      ring
    exact (mul_ne_zero hA hj') hzero

/-- For this tuple, Maynard's Theorem 3.4 gives the following ordinary-prime
sieve input with exponent 7/12+1/24, some k and some α>0 for each m. -/
def TupleCount (m k : ℕ) (α : ℝ) :=
  ∀ᶠ x : ℕ in atTop, ∀ y : ℕ, (x:ℝ)^(5/8:ℝ)≤y → y≤x →
    α*y/(1+log x)^k≤(((Icc x (x+y)).filter (fun n =>
      m≤((range k).filter (fun j => (form k n j).Prime)).card)).card:ℝ)

theorem class_of_forms (m k n : ℕ)
    (hm : m≤((range k).filter (fun j => (form k n j).Prime)).card) :
    classCluster m (diameter k) (8*n) := by
  apply hm.trans
  apply card_le_card_of_injOn (form k n)
  · intro j hj
    obtain ⟨hj,hp⟩ := mem_filter.mp hj
    have hj' := mem_range.mp hj
    apply mem_filter.mpr
    refine ⟨mem_Icc.mpr ⟨?_,?_⟩,hp,?_⟩
    · dsimp [form];omega
    · have := Nat.mul_le_mul_left (step k) hj'.le
      dsimp [form,diameter];omega
    · simp [form,step,Nat.add_mod,Nat.mul_mod]
  · intro i _ j _ h
    have hk : 0<step k := by dsimp [step];positivity [Nat.factorial_pos k]
    exact Nat.eq_of_mul_eq_mul_left hk (Nat.add_left_cancel h)

theorem scaled_of_tuple {m k : ℕ} {α : ℝ} (ordinary : TupleCount m k α) :
    Scaled m (diameter k) k α := by
  filter_upwards [ordinary] with x hx
  intro y hlow hhigh
  apply (hx y hlow hhigh).trans (Nat.cast_le.mpr (card_le_card ?_))
  intro n hn
  obtain ⟨hn,hm⟩ := mem_filter.mp hn
  apply mem_filter.mpr
  exact ⟨hn,class_of_forms m k n hm⟩

/-- With the classical ordinary-prime sieve as explicit input, a positive multiple
of H/(1+log X)^k bounded clusters lies entirely inside (X,X+H]. -/
theorem original {m k : ℕ} {α c : ℝ} (hα : 0<α) (hc : c<1/2) (ordinary : TupleCount m k α) :
    ∃ K : ℝ, 0<K ∧ ∀ᶠ X : ℕ in atTop, ∀ H : ℕ, 2*diameter k≤H → H≤X →
    K*(X:ℝ)^(3/4:ℝ)*(1+log X)^(8+k)≤H →
    (α/128)*H/(1+log X)^k ≤
      (((Ioc X (X+(H-diameter k))).filter (positive c m (diameter k))).card:ℝ) :=
  contained hα hc (scaled_of_tuple ordinary)

#print axioms admissible
#print axioms scaled_of_tuple
#print axioms original
end
end Arxiv.«2501.03234».ThetaMaynardClusters
