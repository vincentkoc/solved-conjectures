import ThetaMaynardClusters

/-! A fixed arithmetic progression rules out all intervening prime residues except one modulo eight. -/
namespace Arxiv.«2501.03234».ThetaConsecutiveProgression
open Finset ThetaMaynardClusters
noncomputable section

def scale (D : ℕ) := 8*D.factorial
def factor (D h : ℕ) := 1+scale D*h
def forbidden (D : ℕ) := (Icc 1 D).filter (fun h => h%8≠1)
def period (D : ℕ) := ∏ h∈forbidden D,factor D h

private theorem expand (D : ℕ) (H : Finset ℕ) :
    ∃ T : ℕ, (∏ h∈H,factor D h)=1+scale D*T := by
  induction H using Finset.induction_on with
  | empty => exact ⟨0,by simp⟩
  | @insert h H hmem ih =>
    obtain ⟨t,ht⟩ := ih
    refine ⟨h+t+scale D*h*t,?_⟩
    rw [prod_insert hmem,ht]
    dsimp [factor];ring

def quotient (D : ℕ) := Classical.choose (expand D (forbidden D))
theorem period_eq (D : ℕ) : period D=1+scale D*quotient D :=
  Classical.choose_spec (expand D (forbidden D))

def shift (D : ℕ) := D.factorial*(quotient D)^2
def base (D n : ℕ) := 8*(period D*n+shift D)

/-- Each forbidden offset has a fixed divisor greater than one. The identity
(CT²+h)+T(1+Ch)=(T+h)(1+CT) handles every offset with the same progression. -/
theorem divides {D h : ℕ} (hf : h∈forbidden D) (n : ℕ) : factor D h∣base D n+h := by
  have hd : factor D h∣period D := dvd_prod_of_mem (factor D) hf
  let T := quotient D
  have he : scale D*T^2+h+T*factor D h=(T+h)*period D := by
    rw [period_eq];dsimp only [factor,T];ring
  have h₁ : factor D h∣scale D*T^2+h := by
    apply (Nat.dvd_add_iff_left (dvd_mul_left _ T)).mpr
    rw [he];exact hd.trans (dvd_mul_left _ _)
  have h₂ := hd.trans (dvd_mul_left (period D) (8*n))
  rw [show base D n+h=(8*n)*period D+(scale D*T^2+h) by dsimp [base,shift,scale,T];ring]
  exact dvd_add h₂ h₁

private theorem large_prime {D h q : ℕ} (hq : q.Prime) (hd : q∣factor D h) : D<q := by
  by_contra! hsmall
  have hc : q∣scale D := (Nat.dvd_factorial hq.pos hsmall).trans (dvd_mul_left _ 8)
  have hz : q∣scale D*h := hc.trans (dvd_mul_right _ _)
  exact hq.not_dvd_one ((Nat.dvd_add_iff_left hz).mpr hd)

/-- On this progression every prime in the whole bounded interval is one modulo eight. -/
theorem covers (D n : ℕ) (hn : 2+factor D D≤n) {p : ℕ}
    (hp : p.Prime) (hlo : base D n≤p) (hhi : p≤base D n+D) : p%8=1 := by
  let h := p-base D n
  have hEq : p=base D n+h := by dsimp [h];omega
  have hQ : 1≤period D := by rw [period_eq];omega
  have hn' : n≤base D n := by
    have := Nat.mul_le_mul_right n hQ
    dsimp only [base];omega
  by_contra hoff
  by_cases hz : h=0
  · have he : p=base D n := by omega
    have hd : 8∣p := by rw [he];exact dvd_mul_right _ _
    rcases (Nat.dvd_prime hp).mp hd with h₈|h₈
    · omega
    · exact (by decide : ¬Nat.Prime 8) (h₈ ▸ hp)
  · have hh : h≤D := by omega
    have hmod : h%8≠1 := by
      intro he
      apply hoff
      rw [hEq,Nat.add_mod]
      simp [base,he]
    have hf : h∈forbidden D := mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,hh⟩,hmod⟩
    have hd := divides hf n
    rw [←hEq] at hd
    have h₁ : 1<factor D h := by
      have := Nat.mul_pos (Nat.mul_pos (by decide : 0<8) (Nat.factorial_pos D)) (Nat.pos_of_ne_zero hz)
      dsimp [factor,scale];omega
    have h₂ : factor D h≤factor D D := by
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hh) _
    rcases (Nat.dvd_prime hp).mp hd with he|he <;> omega

/-- Sieve forms on the restricted variable still have no fixed prime divisor. -/
theorem admissible (k q : ℕ) (hq : q.Prime) :
    ∃ n : ℕ, ∀ j<k, ¬q∣form k (period (diameter k)*n+shift (diameter k)) j := by
  let D := diameter k
  let Q := period D
  let U := shift D
  let : Fact q.Prime := ⟨hq⟩
  by_cases hqQ : q∣Q
  · obtain ⟨h,hh,hf⟩ := (hq.prime.dvd_finsetProd_iff (factor D)).mp hqQ
    have hlarge := large_prime hq hf
    obtain ⟨hr,hmod⟩ := mem_filter.mp hh
    refine ⟨0,?_⟩
    intro j hj hbad
    let t := 1+step k*j
    have ht : t≤D := Nat.add_le_add_left (Nat.mul_le_mul_left _ hj.le) _
    have hm : t%8=1 := by simp [t,step,Nat.add_mod,Nat.mul_mod]
    have h₁ : q∣base D 0+h := hf.trans (divides hh 0)
    have h₂ : q∣base D 0+t := by
      simpa [form,t,base,D,Nat.add_assoc] using hbad
    have he := Nat.ModEq.add_left_cancel' (base D 0)
      ((Nat.modEq_zero_iff_dvd.mpr h₁).trans (Nat.modEq_zero_iff_dvd.mpr h₂).symm)
    have := he.eq_of_lt_of_lt ((mem_Icc.mp hr).2.trans_lt hlarge) (ht.trans_lt hlarge)
    exact hmod (this ▸ hm)
  · obtain ⟨n₀,hn₀⟩ := ThetaMaynardClusters.admissible k q hq
    have hz : (Q:ZMod q)≠0 := fun he => hqQ ((ZMod.natCast_eq_zero_iff _ _).mp he)
    let x : ZMod q := ((n₀:ZMod q)-U)/Q
    have he : (Q:ZMod q)*x+U=n₀ := by dsimp [x];field_simp;ring
    refine ⟨x.val,?_⟩
    intro j hj hbad
    apply hn₀ j hj
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    have hzero := (ZMod.natCast_eq_zero_iff _ _).mpr hbad
    change ((form k (Q*x.val+U) j:ℕ):ZMod q)=0 at hzero
    simpa only [form,Nat.cast_add,Nat.cast_mul,ZMod.natCast_zmod_val,he] using hzero

#print axioms divides
#print axioms covers
#print axioms admissible
end
end Arxiv.«2501.03234».ThetaConsecutiveProgression
