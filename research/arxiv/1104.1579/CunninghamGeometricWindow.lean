import Mathlib

/-! A finite sum of geometric sequences is determined by a consecutive
window as long as the list of terms. Repeated bases are allowed. -/

namespace CunninghamChain.OrbitCover
open List

private def geometric (L : List (ℂ × ℂ)) (n : ℕ) : ℂ :=
  (L.map (fun v => v.1*v.2^n)).sum

private lemma difference (L : List (ℂ × ℂ)) (z : ℂ) (n : ℕ) :
    geometric L (n+1)-z*geometric L n =
      geometric (L.map (fun v => (v.1*(v.2-z),v.2))) n := by
  induction L with
  | nil => simp [geometric]
  | cons v L ih =>
    simp only [geometric,List.map_cons,List.sum_cons,pow_succ] at ih ⊢
    linear_combination ih

private theorem geometric_zero (L : List (ℂ × ℂ)) (nz : ∀ v∈L,v.2≠0) (s : ℕ)
    (block : ∀ j<L.length, geometric L (s+j)=0) : ∀ n, geometric L n=0 := by
  induction hlen : L.length generalizing L with
  | zero =>
    have e := List.length_eq_zero_iff.mp hlen
    simp [e,geometric]
  | succ k ih =>
    obtain _|⟨v,L⟩ := L
    · simp at hlen
    let next := L.map (fun x : ℂ × ℂ => (x.1*(x.2-v.2),x.2))
    have nl : next.length=k := by simpa [next] using hlen
    have nn : ∀ x∈next, x.2≠0 := by
      intro x hx
      obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
      exact nz y (List.mem_cons_of_mem _ hy)
    have diff (n : ℕ) :
        geometric (v::L) (n+1)-v.2*geometric (v::L) n=geometric next n := by
      have := difference L v.2 n
      simp only [geometric,List.map_cons,List.sum_cons,pow_succ] at this ⊢
      dsimp only [next]
      linear_combination this
    have van := ih next nn (fun j hj => by
      rw [←diff,show s+j+1=s+(j+1) by omega,block _ (by simp at hj hlen ⊢; omega),
        block _ (by simp at hj hlen ⊢; omega),mul_zero,sub_zero]) nl
    have eq (n : ℕ) : geometric (v::L) n = v.2^n*geometric (v::L) 0 := by
      induction n with
      | zero => simp
      | succ n hn =>
        have d := sub_eq_zero.mp ((diff n).trans (van n))
        rw [d,hn,pow_succ]; ring
    have start := block 0 (by simp)
    rw [Nat.add_zero,eq s] at start
    have first := (mul_eq_zero.mp start).resolve_left (pow_ne_zero _ (nz v (by simp)))
    intro n
    rw [eq,first,mul_zero]

private def expand : List (ℂ × ℂ) → List (ℂ × ℂ)
  | [] => [(1,1)]
  | (u,v)::f => (expand f).map (fun x => (x.1,u*x.2)) ++ (expand f).map (fun x => (-v*x.1,x.2))

private lemma expand_length (L : List (ℂ × ℂ)) : (expand L).length=2^L.length := by
  induction L with
  | nil => simp [expand]
  | cons v L ih =>
    rcases v with ⟨u,v⟩
    simp only [expand,List.length_append,List.length_map,List.length_cons,ih,pow_succ]
    omega

private lemma expand_nz (L : List (ℂ × ℂ)) (nz : ∀ x∈L,x.1≠0) :
    ∀ y∈expand L, y.2≠0 := by
  induction L with
  | nil => simp [expand]
  | cons v L ih =>
    rcases v with ⟨u,v⟩
    intro y hy
    have a := ih (fun x hx => nz x (by simp [hx]))
    rcases List.mem_append.mp hy with h|h <;> obtain ⟨x,hx,rfl⟩ := List.mem_map.mp h
    · exact mul_ne_zero (nz (u,v) (by simp)) (a x hx)
    · exact a x hx

private lemma expand_value (L : List (ℂ × ℂ)) (n : ℕ) :
    geometric (expand L) n=(L.map (fun v => v.1^n-v.2)).prod := by
  have scale (F : List (ℂ × ℂ)) (a b : ℂ) :
      geometric (F.map (fun x => (a*x.1,b*x.2))) n =
        a*b^n*geometric F n := by
    induction F with
    | nil => simp [geometric]
    | cons v F ih =>
      simp only [geometric,List.map_cons,List.sum_cons,mul_pow] at ih ⊢
      rw [mul_add]
      linear_combination ih
  induction L with
  | nil => simp [expand,geometric]
  | cons v L ih =>
    rcases v with ⟨u,v⟩
    have left := scale (expand L) 1 u
    have right := scale (expand L) (-v) 1
    simp only [one_mul,one_pow,mul_one] at left right
    simp only [expand,List.map_cons,List.prod_cons]
    have add (A B : List (ℂ × ℂ)) : geometric (A++B) n=geometric A n+geometric B n := by simp [geometric]
    rw [add]
    rw [left,right,ih]
    ring

/-- If each of k local obstructions is one nonzero-root geometric
equation, every simultaneous escape recurs in each block of length 2^k. -/
theorem product_escape_in_block (L : List (ℂ × ℂ)) (nz : ∀ x∈L,x.1≠0) {u : ℕ}
    (escape : ∀ x∈L,x.1^u≠x.2) (s : ℕ) :
    ∃ j<2^L.length, ∀ x∈L,x.1^(s+j)≠x.2 := by
  classical
  by_contra! none
  have zero (j : ℕ) (hj : j<(expand L).length) : geometric (expand L) (s+j)=0 := by
    obtain ⟨v,hv,hit⟩ := none j (expand_length L ▸ hj)
    rw [expand_value,List.prod_eq_zero_iff]
    exact List.mem_map.mpr ⟨v,hv,sub_eq_zero.mpr hit⟩
  have all := geometric_zero (expand L) (expand_nz L nz) s zero u
  rw [expand_value,List.prod_eq_zero_iff] at all
  obtain ⟨x,hx,eq⟩ := List.mem_map.mp all
  exact escape x hx (sub_eq_zero.mp eq)

#print axioms product_escape_in_block

end CunninghamChain.OrbitCover
