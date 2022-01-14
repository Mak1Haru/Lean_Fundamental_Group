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

structure Homotopy {a b c d:X}(f : Path a b)(g: Path c d):=
(Func : ℝ × ℝ →  X)
(Continuity : continuous Func)
(InitPT: ∀(x:ℝ), Func (0,x) = f.Func x)
(EndPT: ∀(x:ℝ), Func (1,x) = g.Func x)

/-structure Path_Homotopy-/

def Homotopic {a b c d:X}(f : Path a b)(g: Path c d) := nonempty (Homotopy f g)

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

variables a b: ℝ
variables f g: Path a b

noncomputable def LinFunc {a b:ℝ} (f g : Path a b) (x : ℝ × ℝ): ℝ :=
begin
  let Out := (1-(x.fst)) * (f.Func (x.snd)) + x.fst * (g.Func (x.snd)),
  exact Out,
end 

noncomputable def FixPTLinearHomotopy {a b: ℝ} (f : Path a b) (g : Path a b): Homotopy f g:=
begin

  let Func: ℝ × ℝ → ℝ,
  {
    use LinFunc f g,
  },
  let InitPT: ∀(x:ℝ), LinFunc f g (↑0,x) = f.Func x,
  {
    intro x, rw LinFunc, simp,
  }, simp at InitPT,
  let EndPT: ∀(x:ℝ), LinFunc f g (↑1,x) = g.Func x,
  {
    intro x, rw LinFunc, simp, 
  }, simp at EndPT,
  let IsContinuous : continuous (LinFunc f g),
  {
    apply continuous.add,
    continuity, exact f.Continuity, exact g.Continuity,
  },
  split, use IsContinuous, use InitPT,use EndPT,
end

def ConstantHomotopy {a b :X} (f : Path a b): Homotopy f f :=
begin
  split,
  let Func: ℝ × ℝ → X,
  {
    intro x, use f.Func x.snd,
  }, 
  let IsContinuous : continuous Func,
  {
    continuity,
    exact f.Continuity,
  },
  use IsContinuous,simp,simp,
end

/-
noncomputable lemma Homotopy_if_Homotopic : Homotopic f g → Homotopy f g :=
begin
  intro fRg,
  rw Homotopic at fRg, apply classical.choice, exact fRg,
end
-/


noncomputable theorem Hom_Equiv {a b : X} : equivalence (@Homotopic X _ a b a b):=
begin
  split,
  {
    rw reflexive,
    intro Pab,
    split, apply ConstantHomotopy Pab,
  },
  split,
  {
    rw symmetric,
    intros x y h,
    have hxy: Homotopy x y,
    {
      rw Homotopic at h,
      apply classical.choice, exact h,
    },
    split, split,
    let Func: ℝ × ℝ → X,
    {
      intro x,
      exact hxy.Func (1-(x.fst),x.snd),
    },
    let IsContinuous : continuous Func,
    {
      continuity, exact hxy.Continuity,
    },
    use IsContinuous,simp, intro x,
    rw hxy.EndPT,
    simp, intro x,
    rw hxy.InitPT,
  },

  {
    rw transitive,
    intros x y z xRy yRz,
    have hxy : Homotopy x y,
    {
      rw Homotopic at xRy, exact classical.choice xRy,
    },
    have hyz : Homotopy y z,
    {
      rw Homotopic at yRz, exact classical.choice yRz,
    },
    split, split,
    let Func: ℝ × ℝ → X := λ x, if x.fst ≤ 2⁻¹ then hxy.Func (2*x.fst,x.snd) else hyz.Func (2*x.fst-1,x.snd),
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
      rw h2,simp, rw hxy.EndPT,rw hyz.InitPT,
      exact hxy.Continuity,
      exact hyz.Continuity,
      
    },
    exact IsContinuous,
    simp, intro x_1, rw hxy.InitPT,
    simp, intro x_1, split_ifs, apply false.elim, norm_num at h, 
    norm_num, apply hyz.EndPT,
  },
end

lemma homotopic_have_hom {a b c d:X }{f:Path a b}{g:Path c d} : Homotopic f g → Homotopy f g :=
begin
  intro fRg, apply classical.choice,exact fRg,
end

end Alg_Top







