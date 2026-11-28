import Green51SectionCoordinates
import Green51EighteenSection

/-! # An eighteen-label section forces fifteen simplex labels and three parallel labels -/

open Finset Green50Downsets Green50Sharp Green51TenDimensions Green51SimplexSection
open Green51SimplexFibres Green51SectionCoordinates
open scoped Classical Pointwise
namespace Green51EighteenSection
local notation "F" => ZMod 2
variable {G : Type*} [AddCommGroup G] [Module F G] [DecidableEq G]

/-- In every ambient embedding, an eighteen-label flat-free section in eleven
dimensions contains the standard core and an exterior triple with differences
in the direction space of that core. -/
theorem embedded (f : Cube 11 →ₗ[F] G) (inj : Function.Injective f) (a : G)
    {A : Finset G} (avoid : ¬∃p, FlatAt A p) (U : Finset (Cube 11)) (card : U.card=18)
    (inc : ∀x∈U,f x+a∈A) :
    ∃ (L : Cube 10 →ₗ[F] G) (t : G) (B : Finset G), Function.Injective L ∧
      core L t⊆A ∧ B⊆A ∧ B.card=3 ∧ Disjoint B (core L t) ∧
      ∀x∈B,∀y∈B,x+y∈L.range := by
  classical
  have free : ¬∃p,FlatAt U p := fun ⟨p,h⟩ => avoid ⟨_,transfer f inj a inc h⟩
  obtain ⟨K,c,non,fifteen⟩ := hyperplane U card free
  let E := U.filter (fun x => K x=c)
  have sz : E.card=15 := fifteen
  have sub : E⊆U := filter_subset _ _
  obtain ⟨b,hb⟩ := card_pos.mp (show 0<E.card by omega)
  have eqb : K b=c := (mem_filter.mp hb).2
  obtain ⟨j,S,ji,range,repr⟩ := chart K non b E (fun x h => (mem_filter.mp h).2.trans eqb.symm)
  have affineInj : Function.Injective (fun x => j x+b) := fun _ _ eq => ji (add_right_cancel eq)
  have points : S.card=15 := by rwa [←repr,card_image_of_injective _ affineInj] at sz
  have inE (x) (hx:x∈S) : j x+b∈E := repr ▸ mem_image_of_mem _ hx
  have zero : ¬FlatAt S 0 := fun h => free ⟨_,transfer j ji b (fun x hx => sub (inE x hx)) h⟩
  let J := f.comp j
  obtain ⟨L,t,Li,same,coreEq⟩ := position J (inj.comp ji) (f b+a) S points zero
  let B := (U\E).image (fun x => f x+a)
  have mapped : core L t=E.image (fun x => f x+a) := by
    rw [coreEq,←repr,image_image]
    apply image_congr
    intro x _
    change f (j x)+(f b+a)=f (j x+b)+a
    rw [map_add,add_assoc]
  have outside {x} (hx:x∈U\E) : K x≠c :=
    fun eq => (mem_sdiff.mp hx).2 (mem_filter.mpr ⟨(mem_sdiff.mp hx).1,eq⟩)
  refine ⟨L,t,B,Li,?_,?_,?_,?_,?_⟩
  · rw [mapped]
    rintro x hx
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
    exact inc y (sub hy)
  · rintro x hx
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
    exact inc y (mem_sdiff.mp hy).1
  · change ((U\E).image _).card=3
    rw [card_image_of_injective _ (fun _ _ eq => inj (add_right_cancel eq)),
      card_sdiff_of_subset sub,card,sz]
  · rw [mapped,disjoint_left]
    intro x hx hE
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
    obtain ⟨z,hz,e⟩ := mem_image.mp hE
    exact (mem_sdiff.mp hy).2 (inj (add_right_cancel e) ▸ hz)
  · rintro x hx y hy
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hx
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hy
    have equal := (show ∀b d e:F,b≠e → d≠e → b=d from by decide) _ _ _ (outside hu) (outside hv)
    have pre : u+v∈j.range := by
      rw [range]; change K (u+v)=0; rw [map_add,equal,ZModModule.add_self]
    obtain ⟨w,hw⟩ := pre
    rw [same]
    refine ⟨w,?_⟩
    change f (j w)=(f u+a)+(f v+a)
    rw [hw,map_add,add_add_add_comm (f u) a (f v) a,ZModModule.add_self,add_zero]

end Green51EighteenSection
#print axioms Green51EighteenSection.embedded
