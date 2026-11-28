import ThetaLocalMarkedCorrelations

/-! Every fixed tail threshold in each reduced progression has a positive
unweighted pair excess at some logarithmic shift. -/
namespace Arxiv.«2501.03234».ThetaProgressionTailPairs
open Real Filter Finset ThetaNaturalPrimeMeans ThetaCharacterPrimeMeans ThetaDiagonalConstant
open ThetaPrimeLagBounds ThetaLogarithmicLags ThetaAsymmetricTails ThetaLagSignCounts
open ThetaDistinctPrimeQuadruples ThetaLocalMarkedCorrelations
open scoped Topology
noncomputable section

def centered (p : ℕ) : ℝ := residual p-diagonalConstant
def restricted (q r p : ℕ) : ℝ := if p%q=r then centered p else 0

def classCount (q r X h : ℕ) (P : ℝ → ℝ → Prop) : ℕ := by
  classical
  exact ((pairs X h).filter (fun p => p%q=r ∧ (p+h)%q=r ∧ P (centered p) (centered (p+h)))).card

theorem count_eq {q r X h : ℕ} {P : ℝ → ℝ → Prop} (h₁ : ∀ x,¬P 0 x) (h₂ : ∀ x,¬P x 0) :
    pairCount X h (restricted q r) P=classCount q r X h P := by
  classical
  unfold pairCount classCount
  apply congrArg Finset.card
  apply Finset.ext
  intro p
  simp only [Finset.mem_filter]
  by_cases a : p%q=r <;> by_cases b : (p+h)%q=r <;> simp [restricted,a,b,h₁,h₂]

theorem class_scales (hAP : ProgressionMangoldt) {q r : ℕ} (hq : 0<q) (hr : r<q) (hu : r.Coprime q)
    (t : ℝ) (ht : 0≤t) : ∃ D : ℕ,0<D ∧ q∣D ∧ ∃ c : ℝ,0<c ∧
      Scales D c (fun p => mark t (restricted q r p)) := by
  obtain ⟨D,hD,hd,c,hc,hs⟩ := scores hAP hq hr hu (diagonalConstant+t+2) (by norm_num : (0:ℝ)<1)
  let f (p : ℕ) := mark t (restricted q r p)
  have hb (p : ℕ) : |f p|≤1 := by dsimp [f,mark];split_ifs <;> norm_num
  have hf (p : ℕ) (_hpr : p.Prime) (hp : p%q=r) (he : |residual p-(diagonalConstant+t+2)|<1) :
      f p=1 := by
    have he' := (abs_lt.mp he).1
    have hh : t<centered p := by dsimp [centered];linarith
    have hn : ¬centered p< -t := by linarith
    simp [f,restricted,hp,mark,hh,hn]
  exact ⟨D,hD,hd,c,hc,hs f hb hf⟩

theorem all_levels (hAP : ProgressionMangoldt) {q r : ℕ} (hq : 0<q) (hr : r<q) (hu : r.Coprime q)
    (t : ℝ) (ht : 0≤t) : ∃ c A : ℝ,0<c ∧ 0<A ∧
    ∀ᶠ X : ℕ in atTop,∃ h : ℕ,0<h ∧ q∣h ∧ (h:ℝ)≤A*log X ∧
      c*X≤((classCount q r X h (sameTail t):ℝ)-classCount q r X h (oppositeTail t))*(log X)^2 := by
  obtain ⟨D,hD,hd,c,hc,hs⟩ := class_scales hAP hq hr hu t ht
  let f (p : ℕ) := mark t (restricted q r p)
  obtain ⟨A,hA,H⟩ := short hD hc hs
  refine ⟨c,A,hc,hA,?_⟩
  filter_upwards [H] with X hx
  obtain ⟨h,hh,hp,hl,he⟩ := hx
  refine ⟨h,hh,hd.trans hp,hl,?_⟩
  have a : ¬t<0 := not_lt.mpr ht
  have b : ¬0< -t := by linarith
  have s₁ := count_eq (q:=q) (r:=r) (X:=X) (h:=h) (P:=sameTail t)
    (fun x => by simp [sameTail,a,b]) (fun x => by simp [sameTail,a,b])
  have s₂ := count_eq (q:=q) (r:=r) (X:=X) (h:=h) (P:=oppositeTail t)
    (fun x => by simp [oppositeTail,a,b]) (fun x => by simp [oppositeTail,a,b])
  simpa only [f,marked X h t,s₁,s₂] using he

#print axioms all_levels
end
end Arxiv.«2501.03234».ThetaProgressionTailPairs
