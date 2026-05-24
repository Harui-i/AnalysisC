import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.MeasureTheory.Measure.Dirac

/-
解析学Cレポート問題No.3

問1. Ω を集合とし，ω ∈ Ω とする．A は Ω を全体集合とする σ-加法族であり，
{ω} ∈ A をみたすとする．以下の小問に答えなさい．

(1) A 上の Dirac 測度 εω が完備ならば，A = P(Ω) が成り立つことを示しなさい．

(2) 測度空間 (Ω, A, εω) の完備化を求めなさい．

問2. (S, F) を可測空間とし，f を S 上の関数とし，D を R の稠密な部分集合とする．
以下の小問に答えなさい．

(1) すべての a ∈ D に対し {f < a} ∈ F が成り立つならば，
f は F-可測であることを示しなさい．

(2) すべての a ∈ D に対し {f ≤ a} ∈ F が成り立つならば，
f は F-可測であることを示しなさい．
-/

/-

まずは完備の定義がどこにあるかを調べるか
YumaMizunoの資料/autoresのノート見ても完備については言及なし

Mathlib:
https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/NullMeasurable.html#Complete-measures
-/

/-
問1. Ω を集合とし，ω ∈ Ω とする．A は Ω を全体集合とする σ-加法族であり，
{ω} ∈ A をみたすとする．以下の小問に答えなさい．

(1) A 上の Dirac 測度 ε_ω が完備ならば，A = P(Ω) が成り立つことを示しなさい．
-/

variable {α : Type*} (ω : α) [MeasurableSpace α]

-- TODO: 結論の定式化
theorem problem1_1 
  (h_dirac_complete : MeasureTheory.Measure.IsComplete (MeasureTheory.Measure.dirac ω)) 
  (hω : MeasurableSet ({ω} : Set α))
  : 1 = 1 := by rfl
