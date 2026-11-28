import ThetaVarianceExhaustion

/-! Parseval's identity for the full primitive character spectrum of the original prime theta sum. -/
namespace Arxiv.«2501.03234».ThetaSpectralVariance
open Finset Filter Topology Complex DirichletCharacter ThetaPrimitiveSpectrum ThetaNaturalPrimeMeans
open ThetaLevelCoefficients ThetaDirichletRows ThetaFiniteProjection ThetaVarianceExhaustion
open ThetaCharacterPrimeMeans ThetaDiagonalConstant
noncomputable section

/-- Each primitive character is indexed once, at its conductor. -/
structure Mode where
  modulus : ℕ
  positive : 0 < modulus
  character : DirichletCharacter ℂ modulus
  primitive : character.IsPrimitive

instance (u : Mode) : NeZero u.modulus := ⟨u.positive.ne'⟩

def Mode.mass (u : Mode) : ℝ := ‖value u.character‖^2

def descend {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) : Mode :=
  ⟨χ.conductor,Nat.pos_of_ne_zero χ.conductor_ne_zero,χ.primitiveCharacter,χ.primitiveCharacter_isPrimitive⟩

private theorem same_of_lifts {m : ℕ} [NeZero m] {u v : Mode} (hu : u.modulus∣m) (hv : v.modulus∣m)
    (H : changeLevel hu u.character=changeLevel hv v.character) : u=v := by
  rcases u with ⟨q,hq,χ,hχ⟩
  rcases v with ⟨r,hr,ψ,hψ⟩
  have hc := congrArg DirichletCharacter.conductor H
  simp only [conductor_changeLevel] at hc
  change χ.conductor=ψ.conductor at hc
  have eq : q=r := hχ.symm.trans (hc.trans hψ)
  subst r
  have hh : χ=ψ := changeLevel_injective hu H
  subst ψ
  rfl

theorem descend_injective {m : ℕ} [NeZero m] :
    Function.Injective (descend (m:=m)) := by
  classical
  let lift (u : Mode) : DirichletCharacter ℂ m := if h:u.modulus∣m then changeLevel h u.character else 1
  have he (χ : DirichletCharacter ℂ m) : lift (descend χ)=χ := by
    simp only [lift,descend,dif_pos χ.conductor_dvd_level,changeLevel_primitiveCharacter]
  intro a b hab
  rw [←he a,←he b,hab]

private theorem descend_lift {m : ℕ} [NeZero m] (u : Mode) (hd : u.modulus∣m) :
    descend (changeLevel hd u.character)=u := by
  let χ := changeLevel hd u.character
  exact same_of_lifts (m:=m) χ.conductor_dvd_level hd χ.changeLevel_primitiveCharacter

theorem value_descend {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) (hAP : ProgressionMangoldt) :
    value (descend χ).character=value χ := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  change value χ.primitiveCharacter = value χ
  apply tendsto_nhds_unique (coefficient_limit χ.primitiveCharacter hAP)
  apply replace_at_primes (g:=fun p => symbol χ p*(centered p:ℂ)) _ (coefficient_limit χ hAP)
  filter_upwards [eventually_gt_atTop m] with p hp hprime
  have hg := hprime.coprime_iff_not_dvd.mpr (fun h => hp.not_ge (Nat.le_of_dvd (NeZero.pos m) h))
  have h := χ.primitiveCharacter_apply_of_isCoprime (a:=(p:ℤ))
    (by exact_mod_cast Nat.isCoprime_iff_coprime.mpr hg)
  simpa only [symbol,Int.cast_natCast] using congrArg (·*(centered p:ℂ)) h

private theorem mass_descend {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) (hAP : ProgressionMangoldt) :
    (descend χ).mass=‖value χ‖^2 := by
  exact congrArg (fun z : ℂ => ‖z‖^2) (value_descend χ hAP)

def modesAt (m : ℕ) [NeZero m] : Finset Mode := by classical exact univ.image (descend (m:=m))

theorem mem_modesAt {m : ℕ} [NeZero m] (u : Mode) : u∈modesAt m ↔ u.modulus∣m := by
  classical
  constructor
  · intro hu
    obtain ⟨χ,_,rfl⟩ := mem_image.mp hu
    exact χ.conductor_dvd_level
  · intro hd
    exact mem_image.mpr ⟨changeLevel hd u.character,mem_univ _,descend_lift u hd⟩

theorem sum_modes (m : ℕ) [NeZero m] (hAP : ProgressionMangoldt) :
    ∑ u∈modesAt m,u.mass=energy m := by
  classical
  rw [modesAt,sum_image (fun _ _ _ _ h => descend_injective h)]
  simp only [mass_descend _ hAP,energy]

theorem card_modesAt (m : ℕ) [NeZero m] : (modesAt m).card=m.totient := by
  classical
  rw [modesAt,card_image_of_injective _ descend_injective,card_univ,←Nat.card_eq_fintype_card]
  exact card_eq_totient_of_hasEnoughRootsOfUnity ℂ m

/-- The variance of the prime residual is exactly the sum of the squared magnitudes of
all primitive coefficients, counted once at their individual conductors. -/
theorem parseval {V : ℝ} (hV : Tendsto (primeMean (fun p => (centered p)^2)) atTop (𝓝 V))
    (hAP : ProgressionMangoldt) : HasSum Mode.mass V := by
  classical
  have hn (u : Mode) : 0≤u.mass := sq_nonneg _
  have hs (s : Finset Mode) : ∑ u∈s,u.mass≤V := by
    let m := ∏ u∈s,u.modulus
    let : NeZero m := ⟨(prod_pos (fun u _ => u.positive)).ne'⟩
    have hsub : s⊆modesAt m := fun u hu => (mem_modesAt u).mpr (dvd_prod_of_mem _ hu)
    calc ∑ u∈s,u.mass ≤ ∑ u∈modesAt m,u.mass := sum_le_sum_of_subset_of_nonneg hsub (fun u _ _ => hn u)
      _ = energy m := sum_modes m hAP
      _ ≤ V := energy_le hV hAP
  have H := summable_of_sum_le hn hs
  have hle := Real.tsum_le_of_sum_le hn hs
  let (n : ℕ) : NeZero n.factorial := ⟨(Nat.factorial_pos _).ne'⟩
  have hge : V≤∑' u : Mode,u.mass := by
    apply le_of_tendsto (factorial_energy hV hAP)
    apply Eventually.of_forall
    intro n
    rw [←sum_modes n.factorial hAP]
    exact H.sum_le_tsum _ (fun u _ => hn u)
  rw [←le_antisymm hle hge]
  exact H.hasSum

/-- Statement for the empirical variance of the original integer theta sum. -/
theorem original_variance (hAP : ProgressionMangoldt) :
    Summable Mode.mass ∧ Tendsto (sampleVariance (fun p => (S p:ℝ)/p-Real.log p/2)) atTop
      (𝓝 (∑' u : Mode,u.mass)) := by
  obtain ⟨_,V,_,_,_,_,hV,hvar⟩ := S_prime_class_statistics hAP
  have h := parseval hV hAP
  exact ⟨h.summable,h.tsum_eq.symm ▸ hvar⟩

#print axioms parseval
#print axioms original_variance
end
end Arxiv.«2501.03234».ThetaSpectralVariance
