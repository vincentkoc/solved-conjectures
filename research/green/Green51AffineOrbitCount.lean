import Green51AffineOrbitQuotient
import Green51AffineRankNumbers
import Green51RestrictedOrbitCount

/-! # Counting translation classes of affinely nonspanning missing sets -/

namespace Green51AffineTranslation
open Finset Green53ParityThreshold Green51AffineEnumeration Green51OriginRecovery Green51PeriodQuotients
open scoped Classical

theorem admits_iff_rank {n : ℕ} {D : Finset (𝔽₂ n)} (live : D.Nonempty) :
    admitsOrigin D ↔ affineRank D≠n := by
  let W := ((affineSpan F (D : Set (𝔽₂ n))) : Set (𝔽₂ n)).toFinset
  have criterion : admitsOrigin D ↔ W≠univ := by
    change (∃ b, separated (Green51OriginRecovery.translate D b)) ↔ _
    simp only [separating_origin_iff live]
    constructor
    · rintro ⟨b,h⟩ eq
      exact h (Set.mem_toFinset.mp (show b∈W from eq ▸ mem_univ b))
    · contrapose!
      intro h
      exact eq_univ_of_forall fun b => Set.mem_toFinset.mpr (h b)
  rw [criterion]
  apply not_congr
  rw [←W.card_eq_iff_eq_univ,show W.card=2^affineRank D from affine_span_card live]
  have amb : Fintype.card (𝔽₂ n)=2^n := by simp [𝔽₂,𝔽]
  rw [amb,(Nat.pow_right_injective (by decide : 2≤2)).eq_iff]

/-- Number of labelled masks admitting a separated translate, evaluated by rank-distribution rows. -/
def properNumber (n k : ℕ) : ℕ :=
  if k=0 then 1 else (2^n).descFactorial k/k.factorial - (rankNumbers n (k-1)).getD n 0

theorem proper_count (n k : ℕ) : (properOutputs (𝔽₂ n) k).card=properNumber n k := by
  classical
  let G := 𝔽₂ n
  let K := (univ : Finset G).powersetCard k
  have bij : (properOutputs G k).card=(K.filter admitsOrigin).card := by
    apply card_bij (fun S _ => Sᶜ)
    · intro S h
      obtain ⟨sz,good⟩ := (mem_filter.mp h).2
      exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _,sz⟩,good⟩
    · intro S _ U _ eq; simpa only [compl_compl] using congrArg (fun V : Finset G => Vᶜ) eq
    · intro D h
      obtain ⟨num,good⟩ := mem_filter.mp h
      refine ⟨Dᶜ,mem_filter.mpr ⟨mem_univ _,?_⟩,compl_compl _⟩
      simpa only [compl_compl] using And.intro (mem_powersetCard.mp num).2 good
  rw [bij]
  cases k with
  | zero =>
    have empty : admitsOrigin (∅ : Finset G) := ⟨0,by rw [Green51OriginRecovery.translate_zero]; exact ⟨0,by simp⟩⟩
    simp [K,properNumber,filter_singleton,empty]
  | succ k =>
    have eq : K.filter (fun D => ¬admitsOrigin D)=rankLayer G (k+1) n := by
      ext D; simp only [rankLayer,mem_filter]
      apply and_congr_right
      intro sz
      have num := (mem_powersetCard.mp sz).2
      have live := card_pos.mp (show 0<D.card by omega)
      simp [admits_iff_rank live]
    have count := card_filter_add_card_filter_not (s := K) admitsOrigin
    rw [eq,←rankNumbers_correct n k n le_rfl] at count
    have kc : K.card=(2^n).descFactorial (k+1)/(k+1).factorial := by
      simp [K,G,𝔽₂,𝔽,Nat.choose_eq_descFactorial_div_factorial]
    rw [kc] at count
    simp only [properNumber,Nat.succ_ne_zero,if_false,Nat.succ_sub_one]
    omega

private theorem fixed_proper {n : ℕ} (t : 𝔽₂ (n+1)) (nt : t≠0) (k : ℕ) :
    ((properOutputs (𝔽₂ (n+1)) k).filter (fun S => Green51OriginRecovery.translate S t=S)).card =
      if 2∣k then properNumber n (k/2) else 0 := by
  classical
  let P : Submodule F (𝔽₂ (n+1)) := F ∙ t
  obtain ⟨f,onto,ker⟩ := projection_with_kernel (h := 1) P (finrank_span_singleton nt)
  have rank : Module.finrank F f.ker=1 := ker ▸ finrank_span_singleton nt
  have sz : (f.ker : Set (𝔽₂ (n+1))).toFinset.card=2 := by
    rw [Set.toFinset_card]; change Fintype.card f.ker=2
    rw [Module.card_eq_pow_finrank (K := F),rank,pow_one];rfl
  have fix (S : Finset (𝔽₂ (n+1))) :
      (∀ b∈f.ker, Green51OriginRecovery.translate S b=S) ↔ Green51OriginRecovery.translate S t=S := by
    rw [ker];exact fixed_line_iff t S
  by_cases dvd : 2∣k
  · have count := proper_fixed_kernel f onto (k/2)
    simpa only [sz,Nat.mul_div_cancel' dvd,fix,proper_count,if_pos dvd] using count
  · rw [if_neg dvd,card_eq_zero,eq_empty_iff_forall_notMem]
    rintro S h
    obtain ⟨inF,stable⟩ := mem_filter.mp h
    have eq := (mem_filter.mp inF).2.1
    apply dvd
    simpa only [rank,pow_one,eq] using period_divides_missing f onto S ((fix S).mpr stable)

/-- Burnside's formula for all classes admitting a level-one missing mask, including even
cardinalities where nontrivial stabilizers contribute. -/
theorem proper_orbit_count (n k : ℕ) :
    ((properOutputs (𝔽₂ (n+1)) k).image translationClass).card*2^(n+1) =
    properNumber (n+1) k + (2^(n+1)-1)*(if 2∣k then properNumber n (k/2) else 0) := by
  classical
  let family := properOutputs (𝔽₂ (n+1)) k
  let f (t : 𝔽₂ (n+1)) := (family.filter fun S => Green51OriginRecovery.translate S t=S).card
  have count := restricted_orbit_count family (2^(n+1)) (by
    intro S hS
    have keep (t : 𝔽₂ (n+1)) : Green51OriginRecovery.translate S t∈family := (proper_translate S t k).mpr hS
    simp [keep,𝔽₂,𝔽])
  have zero : f 0=properNumber (n+1) k := by simp [f,family,proper_count]
  change _=∑ t, f t at count
  rw [count,←sum_erase_add _ _ (mem_univ (0 : 𝔽₂ (n+1))),zero,add_comm]
  apply congrArg (properNumber (n+1) k+·)
  rw [sum_congr rfl (fun t ht => fixed_proper t (ne_of_mem_erase ht) k),sum_const,smul_eq_mul,
    card_erase_of_mem (mem_univ _)]
  simp [𝔽₂,𝔽]

end Green51AffineTranslation
#print axioms Green51AffineTranslation.admits_iff_rank
#print axioms Green51AffineTranslation.proper_count
#print axioms Green51AffineTranslation.proper_orbit_count
