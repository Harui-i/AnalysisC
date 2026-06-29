import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-
次の問1, 問2, および問3 を解き、レポートとして7/14に提出

問2 (有界収束定理) (S,F,μ)をμ(S)<∞を満たす測度空間とする. {f_n}_{n=1}^∞はS上で各点収束するF-可測関数の列であり、ある
非負実数Mが存在して、すべてのn∈ℕとx∈Sに対し|f_n(x)|≤Mが成り立つとする。このとき
lim_{n→∞} ∫_S f_n(x) dμ(x) = ∫_S lim_{n→∞} f_n(x) dμ(x) が成り立つことを次の２通りの方法で示しなさい

(1) Lebesgueの優収束定理を使う
(2) Egoroffの定理を用いる

問3 (S,F,μ)を測度空間とし, {f_n}_{n=1}^∞ をF-可測関数の列とする。あるS上のμ-可積分関数gが存在して、すべてのn∈ℕとx∈S
に対し|f_n(x)| ≤ g(x)が成り立つとする。このとき liminf_{n→ ∞} f_n と limsup_{n→∞}はS上のμ-可積分関数であり、
∫_S liminf_{n→∞} f_n dμ ≤ liminf_{n→∞} ∫_S f_n dμ ≤ limsup_{n→∞} ∫_S f_n dμ ≤ ∫_S limsup_{n→∞} f_n dμ
を満たすことを示せ
-/

-- 測度空間にmspという名前をつける
variable {β : Type*} (msp : MeasureTheory.MeasureSpace β)

/-
問1
(S,F,μ)を測度空間とし、fをF-可測関数とする。以下の小問に答えなさい。

(1)(Chebysheffの不等式) α>0に対し
μ {|f| > α} ≤ 1 / α  ∫_S |f| dμ
が成り立つことを示せ

(2) fが可積分なら |f| < ∞ a.e. であることを示しなさい

(3) ∫_S |f| dμ = 0 ならば f = 0 a.e. であることを示しなさい
-/


noncomputable def problem_1_1_rhs (α : ENNReal) (f_abs : β → ENNReal) (μ : MeasureTheory.Measure β)
:= 1 / α * (∫⁻ x, f_abs x ∂μ)


-- ENNRealは0以上無限大以下の拡張された実数(Extended non-negative reals)
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/ENNReal/Basic.html
noncomputable def problem_1_1_lhs (α : ENNReal) (f_abs : β → ENNReal) (μ : MeasureTheory.Measure β)
:= μ { x | α < (f_abs x) }


-- Mathlibの定義にはENNReal(拡張された非負実数)値関数に関するLebesgue積分の定義があったので、それを使う
theorem problem_1_1 (α : ENNReal) (hα : α > 0) (f_abs : β → ENNReal) (μ : MeasureTheory.Measure β)
(hf : Measurable f_abs)
: (problem_1_1_lhs msp α f_abs μ)  < problem_1_1_rhs msp α f_abs μ := by
    simp [problem_1_1_lhs, problem_1_1_rhs]

    -- fをF-可測関数とする、の情報を使ってなくね


    sorry
