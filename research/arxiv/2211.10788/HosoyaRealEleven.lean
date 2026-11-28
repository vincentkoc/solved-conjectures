import Mathlib

/-! A norm-Euclidean covering for the real quadratic ring of discriminant 44. -/

namespace Arxiv.«2211.10788».RealEleven

private def low (i a : ℤ) := min ((i-64*a)^2) ((i+1-64*a)^2)
private def high (i a : ℤ) := max ((i-64*a)^2) ((i+1-64*a)^2)

private def centers : List (ℤ × ℤ) := [(1,0),(-1,0),(2,1),(-5,2),(0,0),(5,-1)]

private def covers (i j : ℤ) (a : ℤ × ℤ) : Bool :=
  decide (-4096 < low i a.1 - 11 * high j a.2 ∧ high i a.1 - 11 * low j a.2 < 4096)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem covering_table : ∀ i j : Fin 32, centers.any (covers i.val j.val) = true := by
  decide +kernel

private theorem square_interval {i a : ℤ} {x : ℚ} (hx : i ≤ x) (hx' : x ≤ i+1) :
    (low i a:ℚ) ≤ (x-64*a)^2 ∧ (x-64*a)^2 ≤ (high i a:ℚ) := by
  let l := i-64*a
  have h₁ : (l:ℚ) ≤ x-64*a := by dsimp [l]; push_cast; linarith
  have h₂ : x-64*a ≤ (l:ℚ)+1 := by dsimp [l]; push_cast; linarith
  have he : i+1-64*a = l+1 := by dsimp [l]; ring
  simp only [low,high,he,Int.cast_min,Int.cast_max,Int.cast_pow,Int.cast_add,Int.cast_one]
  change min ((l:ℚ)^2) (((l:ℚ)+1)^2) ≤ _ ∧ _ ≤ max ((l:ℚ)^2) (((l:ℚ)+1)^2)
  by_cases h : 0 ≤ l
  · have hl : (0:ℚ) ≤ l := by exact_mod_cast h
    exact ⟨(min_le_left ..).trans (pow_le_pow_left₀ hl h₁ 2),
      (pow_le_pow_left₀ (hl.trans h₁) h₂ 2).trans (le_max_right ..)⟩
  · have hl : (l:ℚ)+1 ≤ 0 := by exact_mod_cast (show l+1 ≤ 0 by omega)
    have h₃ : (-((l:ℚ)+1))^2 ≤ (-(x-64*a))^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have h₄ : (-(x-64*a))^2 ≤ (-(l:ℚ))^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    simp only [neg_sq] at h₃ h₄
    exact ⟨(min_le_right ..).trans h₃,h₄.trans (le_max_left ..)⟩

private lemma choose_cell (x : ℚ) (hx : 0 ≤ x) (hx' : x ≤ 32) :
    ∃ i : Fin 32, (i.val:ℚ) ≤ x ∧ x ≤ (i.val:ℚ)+1 := by
  by_cases h : x < 32
  · exact ⟨⟨⌊x⌋₊,(Nat.floor_lt hx).mpr (by exact_mod_cast h)⟩,
      Nat.floor_le hx,(Nat.lt_floor_add_one _).le⟩
  · exact ⟨31,by norm_num; linarith,by norm_num; linarith⟩

/-- On the closed half-by-half square it suffices to try six integral centers. -/
theorem quadrant_cover (x y : ℚ) (hx : 0 ≤ x) (hx' : x ≤ 1/2)
    (hy : 0 ≤ y) (hy' : y ≤ 1/2) :
    ∃ a b : ℤ, |(x-a)^2-11*(y-b)^2| < 1 := by
  obtain ⟨i,hi,hi'⟩ := choose_cell (64*x) (by linarith) (by linarith)
  obtain ⟨j,hj,hj'⟩ := choose_cell (64*y) (by linarith) (by linarith)
  obtain ⟨⟨a,b⟩,_,hab⟩ := List.any_eq_true.mp (covering_table i j)
  have hh := of_decide_eq_true hab
  change -4096 < low i.val a - 11*high j.val b ∧ high i.val a - 11*low j.val b < 4096 at hh
  obtain ⟨hl,hh⟩ := hh
  have h₁ := square_interval (a:=a) (i:=(i.val:ℤ)) (x:=64*x) (by simpa using hi) (by simpa using hi')
  have h₂ := square_interval (a:=b) (i:=(j.val:ℤ)) (x:=64*y) (by simpa using hj) (by simpa using hj')
  have hl' : (-4096:ℚ) < (low i.val a:ℚ) - 11*(high j.val b:ℚ) := by exact_mod_cast hl
  have hh' : (high i.val a:ℚ) - 11*(low j.val b:ℚ) < 4096 := by exact_mod_cast hh
  refine ⟨a,b,abs_lt.mpr ⟨?_,?_⟩⟩ <;> nlinarith only [hl',hh',h₁.1,h₁.2,h₂.1,h₂.2]

#print axioms quadrant_cover

/-- Reflect a nearest-integer residual into the first quadrant, then undo both
reflections on the integral center. -/
theorem rational_cover (x y : ℚ) : ∃ a b : ℤ, |(x-a)^2-11*(y-b)^2| < 1 := by
  let u := x-(round x:ℤ)
  let v := y-(round y:ℤ)
  obtain ⟨a,b,hab⟩ := quadrant_cover |u| |v| (abs_nonneg _) (abs_sub_round x)
    (abs_nonneg _) (abs_sub_round y)
  let adjust (w : ℚ) (n : ℤ) := if 0 ≤ w then n else -n
  have hs (w : ℚ) (n : ℤ) : (w-(adjust w n:ℤ))^2 = (|w|-(n:ℤ))^2 := by
    by_cases hw : 0 ≤ w
    · simp [adjust,hw,abs_of_nonneg hw]
    · simp [adjust,hw,abs_of_neg (lt_of_not_ge hw)]; ring
  refine ⟨round x + adjust u a,round y + adjust v b,?_⟩
  push_cast
  rw [show x-((round x:ℚ)+(adjust u a:ℤ)) = u-(adjust u a:ℤ) by dsimp [u]; ring,
      show y-((round y:ℚ)+(adjust v b:ℤ)) = v-(adjust v b:ℤ) by dsimp [v]; ring,
      hs,hs]
  exact hab

#print axioms rational_cover

abbrev RingEleven := Zsqrtd 11

private theorem eleven_nonsquare (n : ℤ) : (11:ℤ) ≠ n*n := by
  intro he
  have h : -3 ≤ n ∧ n ≤ 3 := by constructor <;> by_contra! h <;> nlinarith
  obtain ⟨hl,hu⟩ := h
  interval_cases n <;> norm_num at he

private theorem remainder_exists (a b : RingEleven) (hb : b ≠ 0) :
    ∃ q : RingEleven, (a - b*q).norm.natAbs < b.norm.natAbs := by
  let m := b.norm
  have hm : m ≠ 0 := (Zsqrtd.norm_eq_zero eleven_nonsquare b).not.mpr hb
  have hm' : (m:ℚ) ≠ 0 := by exact_mod_cast hm
  let v := a*star b
  obtain ⟨u,w,hw⟩ := rational_cover ((v.re:ℚ)/m) ((v.im:ℚ)/m)
  let q : RingEleven := ⟨u,w⟩
  let s := v - (m : RingEleven)*q
  have hs : s = (a-b*q)*star b := by
    change a*star b - (b.norm:RingEleven)*q = _
    rw [Zsqrtd.norm_eq_mul_conj]; ring
  have hr : s.re = v.re - m*u := by simp [s,q]
  have hi : s.im = v.im - m*w := by simp [s,q]
  have hnorm : (s.norm:ℚ)/(m:ℚ)^2 = ((v.re:ℚ)/m-u)^2-11*((v.im:ℚ)/m-w)^2 := by
    rw [Zsqrtd.norm_def,hr,hi]
    push_cast
    field_simp
  rw [← hnorm,hs,Zsqrtd.norm_mul,Zsqrtd.norm_conj,Int.cast_mul,abs_div,abs_mul] at hw
  change |((a-b*q).norm:ℚ)| * |(m:ℚ)| / |(m:ℚ)^2| < 1 at hw
  rw [abs_pow,div_lt_one (by positivity),pow_two] at hw
  have h := lt_of_mul_lt_mul_right hw (abs_nonneg _)
  have hi : |(a-b*q).norm| < |b.norm| := by exact_mod_cast h
  exact ⟨q,by exact_mod_cast (show (((a-b*q).norm.natAbs:ℕ):ℤ) < (b.norm.natAbs:ℤ) by
    simpa only [Int.natCast_natAbs] using hi)⟩

open Classical in
private noncomputable def quotient (a b : RingEleven) : RingEleven :=
  if hb : b = 0 then 0 else (remainder_exists a b hb).choose

/-- Absolute norm gives Euclidean division in ℤ[√11]. -/
noncomputable scoped instance normEuclidean : EuclideanDomain RingEleven :=
  { (inferInstance : CommRing RingEleven), (inferInstance : Nontrivial RingEleven) with
    quotient := quotient
    remainder := fun a b => a-b*quotient a b
    quotient_zero := by simp [quotient]
    quotient_mul_add_remainder_eq := fun _ _ => by ring
    r := fun a b => a.norm.natAbs < b.norm.natAbs
    r_wellFounded := (measure fun a : RingEleven => a.norm.natAbs).wf
    remainder_lt := by
      intro a b hb
      simpa [quotient,hb] using (remainder_exists a b hb).choose_spec
    mul_left_not_lt := by
      intro a b hb
      change ¬(a*b).norm.natAbs < a.norm.natAbs
      rw [Zsqrtd.norm_mul,Int.natAbs_mul]
      exact Nat.not_lt.mpr (Nat.le_mul_of_pos_right _ (Int.natAbs_pos.mpr
        ((Zsqrtd.norm_eq_zero eleven_nonsquare b).not.mpr hb))) }

#print axioms normEuclidean

private def baseSolution : Pell.Solution₁ 11 := .mk 10 3 (by decide)

private theorem base_fundamental : Pell.IsFundamental baseSolution := by
  refine ⟨by decide,by decide,?_⟩
  intro b hb
  change 10 ≤ b.x
  by_contra! hx
  have he := b.prop
  have hx' : b.x^2 ≤ 81 := by
    nlinarith [mul_nonneg (show 0 ≤ 9-b.x by omega) (show 0 ≤ 9+b.x by omega)]
  have hy : -2 ≤ b.y ∧ b.y ≤ 2 := by constructor <;> by_contra! hh <;> nlinarith
  obtain ⟨hy₁,hy₂⟩ := hy
  interval_cases b.y <;> interval_cases b.x <;> norm_num at he

def baseUnit : RingElevenˣ := Unitary.toUnits (R := RingEleven) baseSolution

@[simp] theorem baseUnit_val : (baseUnit:RingEleven) = ⟨10,3⟩ := rfl

@[simp] theorem baseUnit_inv_val : (↑baseUnit⁻¹:RingEleven) = ⟨10,-3⟩ := rfl

theorem unit_signed_power (u : RingElevenˣ) : ∃ n : ℤ, u = baseUnit^n ∨ u = -(baseUnit^n) := by
  have hN : (u:RingEleven).norm = 1 := by
    rcases Int.isUnit_iff.mp (u.isUnit.map Zsqrtd.normMonoidHom) with h | h
    · exact h
    · change (u:RingEleven).norm = -1 at h
      have h' := congrArg (Int.castRingHom (ZMod 11)) h
      simp [Zsqrtd.norm,show (11:ZMod 11) = 0 by decide] at h'
      exact False.elim ((by decide : ∀ r : ZMod 11, r*r ≠ -1) _ h')
  let s : Pell.Solution₁ 11 := ⟨(u:RingEleven),Zsqrtd.norm_eq_one_iff_mem_unitary.mp hN⟩
  let f : Pell.Solution₁ 11 →* RingElevenˣ := Unitary.toUnits
  have hu : f s = u := Units.ext rfl
  obtain ⟨n,hn | hn⟩ := base_fundamental.eq_zpow_or_neg_zpow s
  · exact ⟨n,Or.inl (hu ▸ hn ▸ map_zpow f baseSolution n)⟩
  · refine ⟨n,Or.inr ?_⟩
    calc u = f (-baseSolution^n) := by rw [← hn,hu]
      _ = -(f (baseSolution^n)) := Units.ext rfl
      _ = -(baseUnit^n) := by rw [map_zpow]; rfl

#print axioms unit_signed_power

end Arxiv.«2211.10788».RealEleven
