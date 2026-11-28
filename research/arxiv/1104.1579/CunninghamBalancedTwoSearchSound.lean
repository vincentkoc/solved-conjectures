import CunninghamBalancedTwoEndpointMatch

/-! Soundness of the coefficient search for normalized balanced seed-two iterates. -/

namespace CunninghamChain.BalancedTwo
open Polynomial CoefficientSlices

private lemma final_state (k : Bool) (a b m : List ℤ) (hshort : m.length≤1)
    (hlen : 6≤(a.reverse++m++b).length) (exc : k=true ∨ (a.reverse++m++b).length≠6)
    (hs : (a.reverse++m++b).sum=0)
    (h₁ : dot (a.reverse++m++b) ((a.reverse++m++b).drop 1)=lagOne k)
    (h₂ : dot (a.reverse++m++b) ((a.reverse++m++b).drop 2)=lagTwo k) :
    terminal k (a,b,squaredNorm m)=true := by
  cases m with
  | nil =>
    have hz : -(a.sum+b.sum)=0 := by simp at hs; omega
    simp only [List.append_nil] at hlen exc h₁ h₂
    simp only [terminal,Bool.or_eq_true]
    left
    simp only [squaredNorm,List.map_nil,List.sum_nil,hz,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq,
      Bool.or_eq_true,bne_iff_ne]
    tauto
  | cons c rest =>
    have hrest : rest=[] := by simpa using hshort
    subst rest
    have hc : -(a.sum+b.sum)=c := by simp at hs; omega
    simp only [List.append_assoc,List.cons_append,List.nil_append] at hlen exc h₁ h₂
    simp only [terminal,Bool.or_eq_true]
    right
    simp only [squaredNorm,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,hc,
      Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq,Bool.or_eq_true,bne_iff_ne]
    tauto

private lemma child_mem (k : Bool) (a b : List ℤ) (budget : ℕ) (x y : ℤ)
    (hb : budget≤30) (hw : x.natAbs^2+y.natAbs^2≤budget)
    (he : y+leading k*x=edgeTarget k a.length-dot a b.reverse.tail) :
    (x::a,y::b,budget-(x.natAbs^2+y.natAbs^2)) ∈ children k (a,b,budget) := by
  have hx : x.natAbs≤5 := by
    by_contra! hn
    have := Nat.pow_le_pow_left (by omega : 6≤x.natAbs) 2
    omega
  have hcode : (((x+5).toNat : ℕ) : ℤ)-5=x := by omega
  unfold children
  apply List.mem_filterMap.mpr
  refine ⟨(x+5).toNat,List.mem_range.mpr (by omega : (x+5).toNat<11),?_⟩
  have hy : edgeTarget k a.length-dot a b.reverse.tail-leading k*x=y := by omega
  simp only [hcode,hy,hw,if_true]

/-- Orienting the outer coefficients to 1 and the prescribed leading
coefficient uniquely determines the polynomial at every nonexceptional degree. -/
theorem normalized_unique (k : Bool) {N : ℕ} (hN : 5≤N) (exc : k=true ∨ N≠5)
    (g : ℤ[X]) (dg : g.natDegree≤N) (h₀ : g.coeff 0=1) (h₁ : g.coeff N=leading k)
    (hg : g*reflect N g=sparse k N*reflect N (sparse k N)) : g=sparse k N := by
  by_contra bad
  let v := g.coeff
  let xs := slice (N+1) v
  let st (n : ℕ) : State := (low v n,high N v n,squaredNorm (middle N v n))
  let Live (s : State) := ∃ n > 0, n+n≤N+1 ∧ s=st n
  obtain ⟨hsum,hE,hL₁,hL₂⟩ := witness_data k hN g dg hg
  have hlen : 6≤xs.length := by simp [xs,slice]; omega
  have hex : k=true ∨ xs.length≠6 := by simp [xs,slice]; omega
  have miss (s : State) (hl : Live s) : matched k s=false := by
    obtain ⟨n,_,_,rfl⟩ := hl
    apply Bool.eq_false_iff.mpr
    intro hit
    apply bad
    exact rigid_match k hN g dg h₀ hg (beq_iff_eq.mp hit)
  have advance (s : State) (hlive : Live s) :
      terminal k s=true ∨ ∃ c ∈ children k s, Live c := by
    obtain ⟨n,hn,hnN,rfl⟩ := hlive
    let m := middle N v n
    let a := low v n
    let b := high N v n
    have hsp : xs=a.reverse++m++b := split_slice N n hnN v
    have hml : m.length=N+1-n-n := by simp [m,middle,slice]
    by_cases hshort : m.length≤1
    · left
      apply final_state k a b m hshort
      all_goals rw [←hsp]
      all_goals assumption
    · have hlong : n+n+2≤N+1 := by omega
      let x := v n
      let y := v (N-n)
      have hmiddle : m=x::(middle N v (n+1)++[y]) := middle_step N n v hlong
      have hmE := congrArg squaredNorm hmiddle
      simp only [squaredNorm_cons,squaredNorm_append,show squaredNorm []=0 from rfl,add_zero] at hmE
      have hbudget : squaredNorm m≤30 := by
        change squaredNorm xs=_ at hE
        rw [hsp,squaredNorm_append,squaredNorm_append] at hE
        split_ifs at hE <;> omega
      have hn' : n≤N := by omega
      have hcoeff : (g*reflect N g).coeff n=edgeTarget k n := by
        rw [hg,sparse_correlation k hN hn']
        simp [edgeTarget,show n≠0 by omega,show n≠N-2 by omega,show n≠N-1 by omega,show n≠N by omega]
      rw [correlation g N n hn'] at hcoeff
      have hc := prefix_relation N n v hn hn'
      rw [show v 0=1 from h₀,show v N=leading k from h₁] at hc
      have hall : y+leading k*x=edgeTarget k a.length-dot a b.reverse.tail := by
        have hal : a.length=n := by simp [a,low,slice]
        rw [hal]
        dsimp only [a,b,x,y,v] at hc ⊢
        linear_combination hc.symm.trans hcoeff
      have mem := child_mem k a b (squaredNorm m) x y hbudget (by omega) hall
      have hdiff : squaredNorm m-(x.natAbs^2+y.natAbs^2)=squaredNorm (middle N v (n+1)) := by omega
      have hl : low v (n+1)=x::a := by simp [low,slice_succ,x,a]
      have hh : high N v (n+1)=y::b := by simp [high,slice_succ,y,b]
      right
      refine ⟨_,mem,n+1,by omega,by omega,?_⟩
      simp only [st,hl,hh,hdiff]
  have sound (j : ℕ) (s : State) (hl : Live s) : check k j s=false := by
    induction j generalizing s with
    | zero => exact miss s hl
    | succ j ih =>
      rw [check,miss s hl,Bool.false_or]
      rcases advance s hl with ht|⟨c,hc,live⟩
      · simp [ht]
      · have no : (children k s).all (check k j)=false := by
          apply Bool.eq_false_iff.mpr
          intro all
          have := List.all_eq_true.mp all c hc
          simp [ih c live] at this
        simp [no]
  have live : Live (initial k) := by
    refine ⟨1,by decide,by omega,?_⟩
    have hl : low v 1=[1] := by simp [low,slice,List.range_succ,v,h₀]
    have hh : high N v 1=[leading k] := by simp [high,slice,List.range_succ,v,h₁]
    have hsp := split_slice N 1 (by omega) v
    rw [hl,hh] at hsp
    change squaredNorm (slice (N+1) v)=_ at hE
    rw [hsp,squaredNorm_append,squaredNorm_append] at hE
    cases k <;> simp [leading,squaredNorm] at hE <;>
      simp [initial,st,hl,hh,squaredNorm,leading] <;> omega
  cases k
  · have := sound 20 _ live
    simp [minus_search] at this
  · have := sound 30 _ live
    simp [plus_search] at this

#print axioms normalized_unique

end CunninghamChain.BalancedTwo
