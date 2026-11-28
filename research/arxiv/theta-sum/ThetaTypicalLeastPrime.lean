import ThetaLateClassWitness

/-! An almost-all-moduli least prime bound, at every exponent strictly above two. -/
namespace Arxiv.«2501.03234».ThetaTypicalLeastPrime
open Filter Finset Real ThetaPrimeClassBV
open scoped Classical
noncomputable section

private theorem small {g A : ℝ} (hg : g<1) :
    ∀ᶠ Q : ℕ in atTop,(Q:ℝ)^g ≤ Q/(log Q)^A := by
  have hn := tendsto_natCast_atTop_atTop (R:=ℝ)
  have h := hn.eventually ((isLittleO_log_rpow_rpow_atTop A (sub_pos.mpr hg)).bound (by norm_num : (0:ℝ)<1))
  filter_upwards [h,hn.eventually_gt_atTop 1] with Q h hQ
  have hp : 0<(Q:ℝ) := by linarith
  have hl := log_pos hQ
  change ‖(log (Q:ℝ))^A‖ ≤ 1*‖(Q:ℝ)^(1-g)‖ at h
  rw [one_mul,Real.norm_of_nonneg (rpow_nonneg hl.le _),Real.norm_of_nonneg (rpow_nonneg hp.le _)] at h
  apply (le_div_iff₀ (rpow_pos_of_pos hl _)).mpr
  calc _ ≤ (Q:ℝ)^g*(Q:ℝ)^(1-g) := mul_le_mul_of_nonneg_left h (rpow_nonneg hp.le _)
       _ = _ := by rw [←rpow_add hp,show g+(1-g)=1 by ring,rpow_one]

private theorem endpoint {d t : ℝ} (hd : 1<d) (ht : d<t) (X₀ : ℕ) :
    ∀ᶠ Q : ℕ in atTop,∃ X : ℕ,X₀≤X ∧ Q≤X ∧ Q≤⌊(X:ℝ)^(1/d)⌋₊ ∧
      (⌊(X:ℝ)^(1/d)⌋₊:ℝ)≤2*Q ∧ ∀ q : ℕ,(Q:ℝ)^((d+t)/(2*t))≤q → (X:ℝ)≤(q:ℝ)^t := by
  have hn := tendsto_natCast_atTop_atTop (R:=ℝ)
  have hpow := ((tendsto_rpow_atTop (show 0<(t-d)/2 by linarith)).comp hn).eventually_ge_atTop 2
  filter_upwards [eventually_ge_atTop X₀,hn.eventually_ge_atTop 1,hpow] with Q hQ₀ hQ h2
  let X := ⌈(Q:ℝ)^d⌉₊
  have hp : 0<(Q:ℝ) := by linarith
  have hdp : 0<d := by linarith
  have htp : 0<t := by linarith
  have hi : 0≤1/d := by positivity
  have hlo : (Q:ℝ)^d≤X := Nat.le_ceil _
  have hbase : (Q:ℝ)≤(Q:ℝ)^d := by
    simpa using rpow_le_rpow_of_exponent_le hQ (le_of_lt hd)
  have hhi : (X:ℝ)≤2*(Q:ℝ)^d := by linarith only [Nat.ceil_lt_add_one (rpow_nonneg hp.le d),hQ,hbase]
  have hident : ((Q:ℝ)^d)^(1/d)=Q := by rw [←rpow_mul hp.le,show d*(1/d)=1 by field_simp,rpow_one]
  have hQX : Q≤X := Nat.cast_le.mp (hbase.trans hlo)
  refine ⟨X,hQ₀.trans hQX,hQX,Nat.le_floor ?_,?_,?_⟩
  · rw [←hident];exact rpow_le_rpow (rpow_nonneg hp.le d) hlo hi
  · calc _ ≤ (X:ℝ)^(1/d) := Nat.floor_le (rpow_nonneg (Nat.cast_nonneg _) _)
         _ ≤ (2*(Q:ℝ)^d)^(1/d) := rpow_le_rpow (Nat.cast_nonneg _) hhi hi
         _ = (2:ℝ)^(1/d)*Q := by rw [mul_rpow (by norm_num) (rpow_nonneg hp.le d),hident]
         _ ≤ 2*Q := by
           apply mul_le_mul_of_nonneg_right _ hp.le
           simpa using rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) ((div_le_one hdp).mpr hd.le)
  · intro q hq
    have hb := rpow_le_rpow (rpow_nonneg hp.le _) hq htp.le
    rw [←rpow_mul hp.le,show (d+t)/(2*t)*t=d+(t-d)/2 by field_simp;ring,rpow_add hp] at hb
    change 2≤(Q:ℝ)^((t-d)/2) at h2
    exact hhi.trans ((by nlinarith only [mul_le_mul_of_nonneg_left h2 (rpow_nonneg hp.le d)] :
      2*(Q:ℝ)^d≤(Q:ℝ)^d*(Q:ℝ)^((t-d)/2)).trans hb)

theorem from_sparse (H : Ordinary) {P : ℕ → Prop} (hP : Sparse P) {u t A : ℝ} (ht : 2<t) (hu : u<t) (hA : 0<A) :
    ∃ K : ℝ,0<K ∧ ∀ᶠ Q : ℕ in atTop,∃ D ⊆ Icc 1 Q,(D.card:ℝ)≤K*Q/(log Q)^A ∧
      ∀ q∈Icc 1 Q,q∉D → ∀ a : (ZMod q)ˣ,∃ p : ℕ,p.Prime ∧ (p:ZMod q)=a ∧
        ¬P p ∧ (q:ℝ)^u<p ∧ (p:ℝ)≤(q:ℝ)^t := by
  classical
  let v := max u 1
  let d := (max v 2+t)/2
  have hv1 : 1≤v := le_max_right ..
  have hvpos : 0<v := by linarith
  have hvt : v<t := max_lt hu (by linarith)
  have hvt' : max v 2<t := max_lt hvt ht
  have hvd : v<d := by dsimp [d];linarith only [le_max_left v (2:ℝ),hvt']
  let g := (d+t)/(2*t)
  have hd : 2<d := by dsimp [d];linarith only [le_max_right v (2:ℝ),hvt']
  have hdt : d<t := by dsimp [d];linarith
  have ht0 : 0<t := by linarith
  have hg : g<1 := (div_lt_one (by positivity)).mpr (by linarith only [hdt])
  obtain ⟨C,hC,h⟩ := ThetaPrimeClassCoverage.from_sparse H
    (show 1/d<1/2 by rw [div_lt_div_iff₀ (by linarith) (by norm_num)];linarith) hA hP
  obtain ⟨X₀,h₀⟩ := eventually_atTop.mp (h.and (ThetaLateClassWitness.lower
    (v:=v/d) ((div_lt_one (by linarith)).mpr hvd)))
  refine ⟨2*C+1,by positivity,?_⟩
  filter_upwards [endpoint (by linarith : 1<d) hdt X₀,small (A:=A) hg,eventually_ge_atTop 2]
    with Q hesc hsmall hQ
  obtain ⟨X,hX,hQX,hlow,hhi,hpower⟩ := hesc
  obtain ⟨hcover,hπ⟩ := h₀ X hX
  obtain ⟨B,hB,hBcard,hgood⟩ := hcover
  let D := Icc 1 Q ∩ (B ∪ Icc 1 ⌊(Q:ℝ)^g⌋₊)
  have hq : 1<(Q:ℝ) := by exact_mod_cast (show 1<Q by omega)
  have hlog := log_pos hq
  have hlogle := log_le_log (by linarith : 0<(Q:ℝ)) (Nat.cast_le.mpr hQX)
  have hD : D.card ≤ B.card+⌊(Q:ℝ)^g⌋₊ := by
    apply (card_le_card (inter_subset_right (s₁:=Icc 1 Q) (s₂:=B ∪ Icc 1 ⌊(Q:ℝ)^g⌋₊))).trans
    simpa using card_union_le B (Icc 1 ⌊(Q:ℝ)^g⌋₊)
  refine ⟨D,inter_subset_left,?_,?_⟩
  · have hB' : (B.card:ℝ) ≤ C*(2*Q)/(log Q)^A := by
      apply hBcard.trans
      exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hhi hC.le) (rpow_pos_of_pos hlog _)
        (rpow_le_rpow hlog.le hlogle hA.le)
    have h₁ : (D.card:ℝ) ≤ (B.card:ℝ)+(⌊(Q:ℝ)^g⌋₊:ℝ) := by exact_mod_cast hD
    have h₂ := (Nat.floor_le (rpow_nonneg (Nat.cast_nonneg (α:=ℝ) Q) g)).trans hsmall
    calc _ ≤ _ := h₁.trans (add_le_add hB' h₂)
         _ = _ := by ring
  · intro q hqq hn a
    have hnot : q∉B ∪ Icc 1 ⌊(Q:ℝ)^g⌋₊ := fun hmem => hn (mem_inter.mpr ⟨hqq,hmem⟩)
    have hlarge : (Q:ℝ)^g ≤ q := by
      apply le_of_lt (Nat.lt_of_floor_lt (lt_of_not_ge (fun hh => hnot
        (mem_union_right _ (mem_Icc.mpr ⟨(mem_Icc.mp hqq).1,hh⟩)))))
    have hnum := hgood q (mem_Icc.mpr ⟨(mem_Icc.mp hqq).1,(mem_Icc.mp hqq).2.trans hlow⟩)
      (fun hh => hnot (mem_union_left _ hh)) a
    have hqq' : 1≤(q:ℝ) := by exact_mod_cast (mem_Icc.mp hqq).1
    have hQ' : (Q:ℝ)≤(X:ℝ)^(1/d) := (Nat.cast_le.mpr hlow).trans
      (Nat.floor_le (rpow_nonneg (Nat.cast_nonneg _) _))
    have hc := rpow_le_rpow (Nat.cast_nonneg (α:=ℝ) Q) hQ' hvpos.le
    rw [←rpow_mul (Nat.cast_nonneg _),show 1/d*v=v/d by ring] at hc
    have hqv : (q:ℝ)^v ≤ (X:ℝ)^(v/d) := (rpow_le_rpow (Nat.cast_nonneg _)
      (Nat.cast_le.mpr (mem_Icc.mp hqq).2) hvpos.le).trans hc
    have hqr : (q:ℝ) ≤ (q:ℝ)^v := by simpa using rpow_le_rpow_of_exponent_le hqq' hv1
    have hsize : 8*q≤X.primeCounting := by
      exact_mod_cast (mul_le_mul_of_nonneg_left (hqr.trans hqv) (by norm_num : 0≤(8:ℝ))).trans hπ
    obtain ⟨p,hpr,hr,hs,hp,hbig⟩ := ThetaLateClassWitness.witness P (mem_Icc.mp hqq).1 a hsize hnum
    have hb : (X.primeCounting:ℝ)<8*(p:ℝ) := by exact_mod_cast hbig
    have htgt := (rpow_le_rpow_of_exponent_le hqq' (le_max_left u 1)).trans hqv
    refine ⟨p,hpr,hr,hs,?_,(Nat.cast_le.mpr hp).trans (hpower q hlarge)⟩
    linarith only [hπ,hb,htgt]

theorem original (H : Ordinary) (k : ℕ) {u t A : ℝ} (ht : 2<t) (hu : u<t) (hA : 0<A) :
    ∃ K : ℝ,0<K ∧ ∀ᶠ Q : ℕ in atTop,∃ D ⊆ Icc 1 Q,(D.card:ℝ)≤K*Q/(log Q)^A ∧
      ∀ q∈Icc 1 Q,q∉D → ∀ a : (ZMod q)ˣ,∃ p : ℕ,p.Prime ∧ (p:ZMod q)=a ∧
        (k:ℤ)*p<S p ∧ (q:ℝ)^u<p ∧ (p:ℝ)≤(q:ℝ)^t := by
  simpa only [not_le] using from_sparse H (ThetaWorstPrimeClasses.slope k) ht hu hA

theorem centered (H : Ordinary) : ∃ B : ℝ,0<B ∧ ∀ t> (2:ℝ),∀ u<t,∀ A>(0:ℝ),
    ∃ K : ℝ,0<K ∧ ∀ᶠ Q : ℕ in atTop,∃ D ⊆ Icc 1 Q,(D.card:ℝ)≤K*Q/(log Q)^A ∧
      ∀ q∈Icc 1 Q,q∉D → ∀ a : (ZMod q)ˣ,∃ p : ℕ,p.Prime ∧ (p:ZMod q)=a ∧
        |(S p:ℝ)/p-log p/2|<B*(1+log (log p))^2 ∧ (q:ℝ)^u<p ∧ (p:ℝ)≤(q:ℝ)^t := by
  obtain ⟨B,hB,h⟩ := ThetaWorstPrimeClasses.centered
  exact ⟨B,hB,fun _ ht _ hu _ hA => by simpa only [not_le] using from_sparse H h ht hu hA⟩

#print axioms from_sparse
#print axioms centered
#print axioms original
end
end Arxiv.«2501.03234».ThetaTypicalLeastPrime
