import CunninghamCoefficientSlices
import research.arxiv.«1104.1579».CunninghamJonesLargeDegree
import research.arxiv.«1104.1579».CunninghamJonesSixCertificate
import research.arxiv.«1104.1579».CunninghamJonesPrimePowerDegrees

/-!
# Jones's polynomial question for k = 1

A reducible polynomial gives a coefficient list whose autocorrelations are prescribed by
the trinomial. Its two outer coefficients determine a state in the finite certificate.
Removing endpoints either advances the state or reaches a terminal.
-/

namespace CunninghamChain
open Polynomial CoefficientSlices
open scoped Polynomial

private noncomputable def sixT (N : ℕ) : ℤ[X] :=
  monomial N 1+monomial 1 5+monomial 0 (-6)

private lemma sixT_eq (N : ℕ) : sixT N = X^N+5*X-6 := by
  simp [sixT,← C_mul_X_pow_eq_monomial]
  ring

private lemma sixTrinomialCoeffs (N k : ℕ) (hN : 5 ≤ N) (hk : k ≤ N) :
    (sixT N * reflect N (sixT N)).coeff k =
      if k=0 then -6 else if k=1 then 5 else if k=N-1 then -30 else if k=N then 62 else 0 := by
  have hrev : reflect N (sixT N) =
      monomial 0 1+monomial (N-1) 5+monomial N (-6) := by
    simp only [sixT,← C_mul_X_pow_eq_monomial,reflect_add,reflect_C_mul_X_pow]
    simp [revAt_le (by omega : 1 ≤ N),revAt_le le_rfl]
  rw [hrev]
  simp only [sixT,add_mul,mul_add,monomial_mul_monomial,coeff_add,coeff_monomial]
  simp only [Nat.zero_add,Nat.add_zero,show N+N ≠ k by omega,
    show N+(N-1) ≠ k by omega,show 1+N ≠ k by omega,
    show 1+(N-1) = N by omega,if_false]
  simp only [@eq_comm ℕ 0 k,@eq_comm ℕ 1 k,@eq_comm ℕ (N-1) k,@eq_comm ℕ N k]
  split_ifs <;> omega

/-- The middle autocorrelation fixes the energy; the three adjacent ones test a terminal. -/
private lemma sixWitness_stats (N : ℕ) (hN : 5 ≤ N) (g : ℤ[X]) (hd : g.natDegree ≤ N)
    (he : g.eval 1 = 0) (hg : g*reflect N g = sixT N*reflect N (sixT N)) :
    let xs := slice (N+1) g.coeff
    xs.sum=0 ∧ squaredNorm xs=62 ∧ dot xs (xs.drop 1) = -30 ∧
      dot xs (xs.drop 2) = 0 ∧ dot xs (xs.drop 3) = 0 := by
  dsimp only
  have hl (k : ℕ) (hk : k ≤ N) :
      dot (slice (N+1) g.coeff) ((slice (N+1) g.coeff).drop k) =
      if N-k=0 then -6 else if N-k=1 then 5 else if N-k=N-1 then -30 else if N-k=N then 62 else 0 := by
    rw [full_lag N k hk,hg,sixTrinomialCoeffs N _ hN (Nat.sub_le ..)]
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [slice_sum,← he,Polynomial.eval_eq_sum_range' (by omega : g.natDegree < N+1)]
    simp
  · have h := hl 0 (Nat.zero_le _)
    simp only [tsub_zero,List.drop_zero,← squaredNorm_cast] at h
    split_ifs at h <;> omega
  · have h := hl 1 (by omega)
    split_ifs at h <;> omega
  · have h := hl 2 (by omega)
    split_ifs at h <;> omega
  · have h := hl 3 (by omega)
    split_ifs at h <;> omega

private lemma six_terminal_of_short (a b m : List ℤ) (hshort : m.length ≤ 1)
    (hlen : 6 ≤ (a.reverse++m++b).length) (hs : (a.reverse++m++b).sum = 0)
    (h₁ : dot (a.reverse++m++b) ((a.reverse++m++b).drop 1) = -30)
    (h₂ : dot (a.reverse++m++b) ((a.reverse++m++b).drop 2) = 0)
    (h₃ : dot (a.reverse++m++b) ((a.reverse++m++b).drop 3) = 0) :
    JonesSix.terminal (a,b,squaredNorm m) = true := by
  cases m with
  | nil =>
    have hz : -(a.sum+b.sum) = 0 := by simp at hs; omega
    simp only [List.append_nil] at hlen h₁ h₂ h₃
    simp only [JonesSix.terminal,Bool.or_eq_true]
    left
    simp only [squaredNorm,List.map_nil,List.sum_nil,hz,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq]
    tauto
  | cons c rest =>
    have hrest : rest = [] := by simpa using hshort
    subst rest
    have hc : -(a.sum+b.sum) = c := by simp at hs; omega
    simp only [List.append_assoc,List.cons_append,List.nil_append] at hlen h₁ h₂ h₃
    simp only [JonesSix.terminal,Bool.or_eq_true]
    right
    simp only [squaredNorm,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,hc,
      Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq]
    tauto

private lemma six_child_mem (a b : List ℤ) (budget : ℕ) (x y : ℤ)
    (hb : budget ≤ 62) (hw : x.natAbs^2+y.natAbs^2 ≤ budget)
    (he : 2*y-3*x = (if a.length=1 then 5 else 0)-dot a b.reverse.tail) :
    (x::a,y::b,budget-(x.natAbs^2+y.natAbs^2)) ∈ JonesSix.children (a,b,budget) := by
  have hx : x.natAbs ≤ 7 := by
    by_contra! hn
    have := Nat.pow_le_pow_left (by omega : 8 ≤ x.natAbs) 2
    omega
  have hreg : -7 ≤ x ∧ x ≤ 7 := by omega
  have hcode : (((x+7).toNat : ℕ) : ℤ)-7 = x := by omega
  have hy : (((if a.length=1 then 5 else 0)-dot a b.reverse.tail)+3*x)/2 = y := by omega
  unfold JonesSix.children
  apply List.mem_filterMap.mpr
  refine ⟨(x+7).toNat,List.mem_range.mpr (by omega),?_⟩
  simp only [show JonesSix.dot a b.reverse.tail=dot a b.reverse.tail by rfl,hcode,hy,he,hw,and_self,if_true]

private lemma six_no_polynomial (N : ℕ) (hN : 5 ≤ N) (g : ℤ[X]) (hgdeg : g.natDegree ≤ N)
    (h₀ : g.coeff 0 = 2) (h₁ : g.coeff N = -3) (heval : g.eval 1 = 0)
    (hg : g*reflect N g = sixT N*reflect N (sixT N)) : False := by
  let v := g.coeff
  let xs := slice (N+1) v
  let st (n : ℕ) : JonesSix.State :=
    (low v n,high N v n,squaredNorm (middle N v n))
  let Live (s : JonesSix.State) := ∃ n > 0, n+n ≤ N+1 ∧ s=st n
  obtain ⟨hsum,hE,hL₁,hL₂,hL₃⟩ := sixWitness_stats N hN g hgdeg heval hg
  have hlen : 6 ≤ xs.length := by simp [xs,slice]; omega
  have advance (s : JonesSix.State) (hlive : Live s) :
      JonesSix.terminal s = true ∨ ∃ c ∈ JonesSix.children s, Live c := by
    obtain ⟨n,hn,hnN,rfl⟩ := hlive
    let m := middle N v n
    let a := low v n
    let b := high N v n
    have hsp : xs = a.reverse++m++b := split_slice N n hnN v
    have hml : m.length=N+1-n-n := by simp [m,middle,slice]
    by_cases hshort : m.length ≤ 1
    · left
      apply six_terminal_of_short a b m hshort
      all_goals rw [← hsp]
      all_goals assumption
    · have hlong : n+n+2 ≤ N+1 := by omega
      let x := v n
      let y := v (N-n)
      have hmiddle : m = x :: (middle N v (n+1) ++ [y]) := middle_step N n v hlong
      have hmE := congrArg squaredNorm hmiddle
      simp only [squaredNorm_cons,squaredNorm_append,show squaredNorm []=0 from rfl,add_zero] at hmE
      have hbudget : squaredNorm m ≤ 62 := by
        change squaredNorm xs = 62 at hE
        rw [hsp,squaredNorm_append,squaredNorm_append] at hE
        omega
      have hn' : n ≤ N := by omega
      have hcoeff : (g*reflect N g).coeff n = if n=1 then 5 else 0 := by
        rw [hg,sixTrinomialCoeffs N n hN hn']
        simp [show n≠0 by omega,show n≠N-1 by omega,show n≠N by omega]
      rw [correlation g N n hn'] at hcoeff
      have hc := prefix_relation N n v hn hn'
      rw [show v 0=2 from h₀,show v N= -3 from h₁] at hc
      have hall : 2*y-3*x = (if a.length=1 then 5 else 0)-dot a b.reverse.tail := by
        have hal : a.length=n := by simp [a,low,slice]
        rw [hal]
        dsimp only [a,b,x,y,v] at hc ⊢
        linear_combination hc.symm.trans hcoeff
      have mem := six_child_mem a b (squaredNorm m) x y hbudget (by omega) hall
      have hdiff : squaredNorm m - (x.natAbs^2+y.natAbs^2) = squaredNorm (middle N v (n+1)) := by omega
      have hl : low v (n+1) = x::a := by simp [low,slice_succ,x,a]
      have hh : high N v (n+1) = y::b := by simp [high,slice_succ,y,b]
      right
      refine ⟨_,mem,n+1,by omega,by omega,?_⟩
      simp only [st,hl,hh,hdiff]
  have sound (s : JonesSix.State) (h : JonesSix.Excluded s) : ¬Live s := by
    induction h with
    | step nt children ih =>
      intro hL
      rcases advance _ hL with term|⟨child,hm,hchild⟩
      · simp [nt] at term
      · exact ih child hm hchild
  apply sound _ JonesSix.six_certificate
  refine ⟨1,by decide,by omega,?_⟩
  have hl : low v 1 = [2] := by simp [low,slice,List.range_succ,v,h₀]
  have hh : high N v 1 = [-3] := by simp [high,slice,List.range_succ,v,h₁]
  have hsp := split_slice N 1 (by omega) v
  rw [hl,hh] at hsp
  change squaredNorm (slice (N+1) v)=62 at hE
  rw [hsp,squaredNorm_append,squaredNorm_append] at hE
  norm_num [squaredNorm_cons,squaredNorm] at hE
  have h49 : squaredNorm (middle N v 1)=49 := by dsimp only [squaredNorm]; omega
  simp [st,hl,hh,h49]

/-- Jones's Conjecture 4.1 for its first parameter, k = 1, t = 3 and m = 6. -/
theorem jones_first_parameter_irreducible_iff (j : ℕ) (hj : 2 ≤ j) :
    Irreducible ((jonesSumPolynomial 6 j).map (Int.castRingHom ℚ)) ↔ j ≠ 3 := by
  constructor
  · intro hi h
    subst j
    have hh := (jones_rational_root_iff 3 3 (by decide) (by decide) (by decide)
      (by decide) (-2)).mpr ⟨rfl,rfl⟩
    rw [show jonesConstant 3=6 by decide] at hh
    have hd := natDegree_eq_of_degree_eq_some (degree_eq_one_of_irreducible_of_root hi hh)
    rw [natDegree_map_eq_of_injective Int.cast_injective,(jonesSumPolynomial_shape ..).1] at hd
    exact (by decide : (3 : ℕ) ≠ 1) hd
  · intro h3
    by_cases h2 : j=2
    · subst j
      simpa using dyadic_degree_irreducible (m:=6) (by decide) 1
    · by_contra hred
      obtain ⟨g,hd,h₀,h₁,he,hg⟩ := jones_six_factor_witness j (by omega) hred
      exact six_no_polynomial (j+1) (by omega) g hd h₀ h₁ he (by simpa only [sixT_eq] using hg)

#print axioms jones_first_parameter_irreducible_iff

end CunninghamChain
