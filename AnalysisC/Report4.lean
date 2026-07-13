import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Order.Interval.Set.Defs

namespace Report4
/-
次の問1, 問2, および問3 を解き、レポートとして7/14に提出

問2 (有界収束定理) (S,F,μ)をμ(S)<∞を満たす測度空間とする. {f_n}_{n=1}^∞はS上で各点収束するF-可測関数の列であり、ある
非負実数Mが存在して、すべてのn∈ℕとx∈Sに対し|f_n(x)|≤Mが成り立つとする。このとき
lim_{n→∞} ∫_S f_n(x) dμ(x) = ∫_S lim_{n→∞} f_n(x) dμ(x) が成り立つことを次の２通りの方法で示しなさい

(1) Lebesgueの優収束定理を使う
(2) Egoroffの定理を用いる

問3 (S,F,μ)を測度空間とし, {f_n}_{n=1}^∞ をF-可測関数の列とする。あるS上のμ-可積分関数gが存在して、すべてのn∈ℕとx∈S
に対し|f_n(x)| ≤ g(x)が成り立つとする。このとき liminf_{n→ ∞} f_n と limsup_{n→∞}はS上のμ-可積分関数であり、
∫_S liminf_{n→∞} f_n dμ ≤ liminf_{n→∞} ∫_S f_n dμ ≤ limsup_{n→∞}∫_S f_n dμ ≤ ∫_S limsup_{n→∞} f_n dμ
を満たすことを示せ
-/

-- 測度空間にmspという名前をつける
variable {β : Type*} (msp : MeasureTheory.MeasureSpace β)

/-
問1
(S,F,μ)を測度空間とし、fをF-可測関数とする。以下の小問に答えなさい。

(1)(Chebysheffの不等式) α>0に対し
μ {|f| > α} ≤ α⁻¹  ∫_S |f| dμ
が成り立つことを示せ

(2) fが可積分なら |f| < ∞ a.e. であることを示しなさい

(3) ∫_S |f| dμ = 0 ならば f = 0 a.e. であることを示しなさい
-/


-- 右辺
noncomputable def problem_1_1_rhs (α : ENNReal) (f_abs : β → ENNReal) (μ : MeasureTheory.Measure β)
:= 1 / α * (∫⁻ x, f_abs x ∂μ)

-- ENNRealは0以上無限大以下の拡張された実数(Extended non-negative reals)
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/ENNReal/Basic.html
noncomputable def problem_1_1_lhs (α : ENNReal) (f_abs : β → ENNReal) (μ : MeasureTheory.Measure β)
:= μ { x | α < (f_abs x) }


-- Mathlibの定義にはENNReal(拡張された非負実数)値関数に関するLebesgue積分の定義があったので、それを使う
theorem problem_1_1 (α : ENNReal) (hα : α > 0) (f_abs : β → ENNReal) (μ : MeasureTheory.Measure β)
(hf : Measurable f_abs)
: problem_1_1_lhs msp α f_abs μ  ≤ problem_1_1_rhs msp α f_abs μ := by
  simp only [problem_1_1_lhs, problem_1_1_rhs]
  -- ⊢ μ {x | α < f_abs x} ≤ α⁻¹ * ∫⁻ (x: β), f_abs x ∂μ
  -- 両辺αかける
  have hα2 : α ≠ 0 := by
    simp_all only [gt_iff_lt, ne_eq]
    intro h
    rw [h] at hα
    -- hα : 0 < 0
    simp_all only [lt_self_iff_false]
  -- αがtopがどうかで場合分け
  by_cases hα_top : α = ⊤
  case pos =>
    simp_all only [gt_iff_lt, ENNReal.zero_lt_top, ne_eq, ENNReal.top_ne_zero,
      not_false_eq_true, not_top_lt, Set.setOf_false, MeasureTheory.measure_empty, one_div,
      ENNReal.inv_top, zero_mul, Std.le_refl]
  case neg =>
    -- hα_top: ¬ α = ⊤
    simp only [one_div, ge_iff_le]
    simp only [← ENNReal.mul_le_iff_le_inv hα2 hα_top]
    -- ⊢ α * μ {x | α < f_abs x} ≤   ∫⁻ (x: β), f_abs x ∂μ
    let s : Set β := {x | α < f_abs x}
    have hs : MeasurableSet s := by
      -- https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Constructions/BorelSpace/Order.html#Borel-sigma-algebras-on-spaces-with-orders
      exact hf measurableSet_Ioi
    --　左辺のαを中に入れたい
    rw [← MeasureTheory.setLIntegral_const s α]
    -- ⊢ ∫⁻ (x : β) in s, α ∂μ ≤ ...
    rw [← MeasureTheory.lintegral_indicator hs ]
    -- ⊢ ∫⁻ (a : β) s.indicator (fun x ↦ α) a ∂μ ≤ ∫⁻ (x : β), f_abs x ∂μ
    -- あとは各点での評価におちるはず
    apply MeasureTheory.lintegral_mono
    -- ⊢ (s.indicator fun x↦α) ≤ f_abs
    intro x
    simp only [s]
    by_cases hf : α < f_abs x
    case pos =>
      simp only [Set.mem_setOf_eq, hf, Set.indicator_of_mem]
      -- hf: α < f_abs x
      -- ⊢ α ≤ f_abs x
      exact le_of_lt hf
    case neg =>
      push Not at hf
      -- hf : f_abs x ≤ α
      simp [hf]

-- (2) fが可積分なら |f| < ∞ a.e. であることを示しなさい
theorem problem_1_2 (f_abs : β → ENNReal) (μ : MeasureTheory.Measure β)
(hf : Measurable f_abs) (hf_int : (∫⁻ x, f_abs x ∂μ) < ⊤)
  -- f-abs: |f|は非負拡大実数値関数
  -- μ : 測度
  -- hf: |f| は可測関数
  -- hf_int: |f| は可積分
: ∀ᵐ x ∂μ, f_abs x < ⊤ := by
  -- f_abs x < ⊤が μ-a.e.で成立することを示す
  let E : Set β  := {x | f_abs x = ⊤}
  simp only [MeasureTheory.ae_iff, not_lt, top_le_iff]
  change μ E = 0
  -- ⊢ μ E = 0
  by_contra h_nonzero
  -- h_nonzero ¬ μ E = 0
  have h_muE : μ {x ∈ E | f_abs x = ⊤ } ≠ 0 := by
    simpa [E]
  have hf_top_in_E : ∫⁻ x in E, f_abs x ∂μ = ⊤ := by
    apply MeasureTheory.setLIntegral_eq_top_of_measure_eq_top_ne_zero
    · -- ⊢ AEMeasurable f_abs (μ.restrict E)
      exact Measurable.aemeasurable hf
    · -- μ 
      -- μ {x | x ∈ E ∧ f_abs x = ⊤ } ≠ 0
      exact h_muE
  have hf_top1 : ∫⁻ x, f_abs x ∂μ ≥ ⊤ := by
    calc 
      _ ≥ ∫⁻ x in E, f_abs x ∂μ  := by simp [MeasureTheory.setLIntegral_le_lintegral]
      _ = ⊤ := by simp [hf_top_in_E]
  have hf_top : ∫⁻ x, f_abs x ∂μ = ⊤ := by
    simp_all only [ge_iff_le, top_le_iff]
  rw [hf_top] at hf_int
  -- hf_int : ⊤ < ⊤ 
  -- 矛盾
  contradiction

end Report4
