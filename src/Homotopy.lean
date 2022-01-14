import topology.basic
import data.real.basic
import topology.continuous_function.basic
import tactic
import topology.instances.real

open topological_space

namespace Alg_Top

noncomputable theory

def I : set ℝ := {x | 0 ≤ x ∧ x ≤ 1}  
variable y : ℝ 

theorem h: ↑0 ∈ I :=
begin
  rw I,
  simp,
end



variables {X Y: Type} [topological_space X][topological_space Y]

theorem ge_I (y : ℝ) : |y| + 1 >= 1 :=
begin
  simp,
  apply abs_nonneg,
end

instance : has_zero I := 
begin
  split,split, 
  have h: ↑0 ∈ I,
  {
    rw I, simp,
  },
  exact h,
end


instance : has_one I :=
begin
  split,split,
  have h: ↑1 ∈ I,
  {
    rw I, simp,
  },
  exact h,
end

variable α : Type 

/- Type of path from a to b

-/
structure Path (a : X)(b : X) :=
(Func : ℝ → X )
(Continuity : continuous Func)
(InitPT: Func 0 = a)
(EndPT: Func 1 = b)

structure Homotopy (f g: X → Y):=
(Func : ℝ × X → Y)
(Continuity : continuous Func)
(InitPT: ∀(x:X), Func (0,x) = f x)
(EndPT: ∀(x:X), Func (1,x) = g x)

structure Path_Homotopy {a b : X}(f g : Path a b):=
(Hom : Homotopy f.Func g.Func)
(FixInitPT: ∀(x:ℝ), Hom.Func (x,0) = a)
(FixEndPT: ∀(x:ℝ), Hom.Func (x,1) = b)

def Homotopic (f g: X → Y) := nonempty (Homotopy f g)

def Path_Homotopic {a b : X}(f g : Path a b) := nonempty (Path_Homotopy f g)

notation a ⟶ b := Path a b 
/-
notation f ≡ g := Homotopic f g
notation f ≃ g := Path_Homotopic f g
-/

/-
structure FixPTHomotopy (a : X)(b : X):=
(Func : C(I × I, X))
(InitPT: ∀(t:I), Func (t,0) = a)
(EndPT: ∀(t:I), Func (t,1) = b)

structure FixPTHomotopic_with (a : X)(b : X)(f : Path a b)(g : Path a b):=
(Homotopy_map : FixPTHomotopy a b)
(InitPTEquiv: ∀(x:I), (Homotopy_map.Func (0,x) = f.Func x ))
(EndPTEquiv: ∀(x:I), (Homotopy_map.Func (1,x) = g.Func x )) -/


noncomputable def func (x : ℝ × ℝ) : ℝ := (x.fst+x.snd)/2
lemma Con : continuous func :=
begin
  apply continuous.mul,
  continuity,
end





noncomputable def FixPT_Path_LinearHomotopy {a b: ℝ} (f : Path a b) (g : Path a b): Path_Homotopy f g:=
begin

  let Func: ℝ × ℝ → ℝ:= λx, (1-(x.fst)) * (f.Func (x.snd)) + x.fst * (g.Func (x.snd)),
  have InitPT: ∀(x:ℝ), Func (0,x) = f.Func x,
  {
    intro x, simp_rw Func, simp only [add_zero, one_mul, nat.cast_zero, zero_mul, sub_zero],
  },
  have EndPT: ∀(x:ℝ), Func (1,x) = g.Func x,
  {
    intro x, simp_rw Func, simp only [one_mul, zero_mul, zero_add, nat.cast_one, sub_self], 
  },
  have IsContinuous : continuous Func,
  {
    apply continuous.add,
    continuity, exact f.Continuity, exact g.Continuity,
  },
  let Hom: Homotopy f.Func g.Func,
  {
    split, exact IsContinuous,
    intro s, simp_rw Func, simp only [add_zero, one_mul, zero_mul, sub_zero],
    intro s, simp_rw Func, simp only [one_mul, zero_mul, zero_add, sub_self],
  },
  split, intro x, 
  change Hom.Func (x,0) = a,
  simp_rw Func, rw f.InitPT, rw g.InitPT, ring,
  intro x, simp_rw Func, rw f.EndPT, rw g.EndPT, ring,
end

def ConstantHomotopy (f : X → Y) : continuous f → Homotopy f f:=
begin
  intro cf,
  split,
  let Func: ℝ × X → Y:= λx , f (x.snd),
  have Continuity: continuous Func,
  {
    continuity,
  }, use Continuity,
  intro x, simp,
  intro x, simp,
end


def ConstantPathHomotopy {a b :X} (f : Path a b): Path_Homotopy f f :=
begin
  let Const : Homotopy f.Func f.Func := ConstantHomotopy f.Func f.Continuity,
  have H : ∀x y, Const.Func (x,y) = f.Func y,
  {
    intro y, exact congr_fun rfl,
  }, 
  split,
  intro x, 
  rw H, exact f.InitPT,
  intro x, rw H, exact f.EndPT,
end


lemma Homotopy_if_Homotopic {f g : X → Y} : Homotopic f g → Homotopy f g :=
begin
  intro fRg,
  rw Homotopic at fRg, apply classical.choice, exact fRg,
end

lemma Path_Homotopy_if_Homotopic {a b: X}{f g : Path a b} : Path_Homotopic f g → Path_Homotopy f g :=
begin
  intro fRg,
  rw Path_Homotopic at fRg, apply classical.choice, exact fRg,
end



theorem Path_Hom_Equiv {a b : X} : equivalence (@Path_Homotopic _ _ a b):=
begin
  split,
  {
    rw reflexive,
    intro Pab,
    split, apply ConstantPathHomotopy Pab,
  },
  split,
  {
    rw symmetric,
    intros x y h,
    have hxy: Path_Homotopy x y := Path_Homotopy_if_Homotopic h,
    split, 
    let Func: ℝ × ℝ → X,
    {
      intro x,
      exact hxy.Hom.Func (1-(x.fst),x.snd),
    },
    have IsContinuous : continuous Func,
    {
      continuity, exact hxy.Hom.Continuity,
    },
    let H: Homotopy y.Func x.Func,
    {
      split, exact IsContinuous,
      intro x, simp_rw Func,simp only [sub_zero], rw hxy.Hom.EndPT,
      intro x, simp_rw Func,simp only [sub_self], rw hxy.Hom.InitPT,
    },
    split, intro s, 
    change H.Func (s,0) = a,
    simp only, simp_rw Func, simp only, rw hxy.FixInitPT,
    simp only, simp_rw Func, simp only, intro x, rw hxy.FixEndPT,
  },

  {
    rw transitive,
    intros x y z xRy yRz,
    have hxy : Path_Homotopy x y := Path_Homotopy_if_Homotopic xRy,
    have hyz : Path_Homotopy y z := Path_Homotopy_if_Homotopic yRz,

    let Func: ℝ × ℝ → X := λ x, if x.fst ≤ 2⁻¹ then hxy.Hom.Func (2*x.fst,x.snd) else hyz.Hom.Func (2*x.fst-1,x.snd),
    have IsContinuous : continuous Func,
    {
      apply continuous.if, continuity,
      have h1: a_1 ∈ {x : ℝ × ℝ | x.fst = 2⁻¹},
      {
        apply frontier_le_subset_eq,continuity,
      },
      have h2: a_1.fst = 2⁻¹,
      {
        exact h1,
      },
      rw h2,simp, rw hxy.Hom.EndPT,rw hyz.Hom.InitPT,
      exact hxy.Hom.Continuity,
      exact hyz.Hom.Continuity,
    },
    let H: Homotopy x.Func z.Func,
    {
      split, exact IsContinuous,intro s, simp_rw Func,split_ifs,simp,
      rw hxy.Hom.InitPT,apply false.elim,
      simp only [zero_le_one, inv_nonneg, zero_le_bit0, not_true] at h, exact h,
      intro s, simp_rw Func,split_ifs,simp only [mul_one], apply false.elim,
      simp only at h, norm_num at h, simp, norm_num, rw hyz.Hom.EndPT,
      
    },
    split,split, intro s, change H.Func(s,0) = a,
    simp_rw Func,split_ifs, rw hxy.FixInitPT, rw hyz.FixInitPT,
    intro s, simp_rw Func, split_ifs, rw hxy.FixEndPT, rw hyz.FixEndPT,

  },  
end

end Alg_Top







