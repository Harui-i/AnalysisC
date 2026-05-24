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

-- MeasureTheory.Measure.dirac ω を打ち続けるのはダルいので。ここでdefとすると微妙
noncomputable abbrev dira (ω : α) : MeasureTheory.Measure α := MeasureTheory.Measure.dirac ω

-- TODO: 結論の定式化
theorem problem1_1 (h_dirac_complete : MeasureTheory.Measure.IsComplete (dira ω)) (hω : 
    MeasurableSet ({ω} : Set α))
  : ∀ (s : Set α), MeasurableSet s := by 
  intro s 
  -- ⊢ MeasurableSet s
  simp only [MeasureTheory.Measure.isComplete_iff] at h_dirac_complete
  -- h_dirac_complete : ∀ (s : Set α), (MeasureTheory.Measure.dirac ω) s = 0 → MeasurableSet s
  -- つまり (t : Set α)であって ω ∉ t → MeasurableSet t
  -- じゃあωを含むかどうかで場合分けすればいいんだ
  by_cases h_s_contains_omega : ω ∈ s
  case pos =>
    -- h_s_contains_omega : ω ∈ s
    sorry
  case neg =>
    -- h_s_contains_omega : ω ∉ s
    apply h_dirac_complete s
    -- ⊢ (MeasureTheory.Measure.dirac ω) s = 0
    have h1 : (dira ω) s = 0 ∨ (dira ω) s = 1:= MeasureTheory.Measure.dirac_apply_eq_zero_or_one
    rcases h1 with h1_0  | h1_1
    · exact h1_0
    ·
      -- h1_1 : (dira ω) s = 1
      -- h_ss_contains_omega : w ∉ s
      -- ⊢ (dira ω) s = 0

      sorry

