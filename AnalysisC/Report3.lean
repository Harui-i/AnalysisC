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

theorem problem1_1 (h_dirac_complete : MeasureTheory.Measure.IsComplete (dira ω)) (hω :
    MeasurableSet ({ω} : Set α))
  : ∀ (s : Set α), MeasurableSet s := by 
  intro s 
  -- ⊢ MeasurableSet s
  simp only [MeasureTheory.Measure.isComplete_iff] at h_dirac_complete
  -- h_dirac_complete : ∀ (s : Set α), (MeasureTheory.Measure.dirac ω) s = 0 → MeasurableSet s
  -- つまり (t : Set α)であって ω ∉ t → MeasurableSet t
  -- じゃあωを含むかどうかで場合分けすればいいんだ
  let omega_compl : Set α := ({ω} : Set α)ᶜ 
  by_cases h_s_contains_omega : ω ∈ s
  case pos =>
    -- h_s_contains_omega : ω ∈ s
    have h1 : (dira ω) s = 0 ∨ (dira ω) s = 1:= MeasureTheory.Measure.dirac_apply_eq_zero_or_one
    rcases h1 with h1_0  | h1_1
    · apply h_dirac_complete
      exact h1_0 
    · -- h_s_contains_omega : ω ∈ s
      -- h1_1 : (dira ω ) s = 1
      -- ⊢ MeasurableSet s
      -- s = {ω} ⊔ (S ∩  {ω}ᶜ)
      -- みたいに表せば右側がμ-0集合。完備だからこれは可測。
      have hs : s = {ω} ∪ (s ∩ omega_compl) := by
        ext x
        constructor
        · intro hx
          by_cases hxω : x = ω
          · left
            exact hxω
          · right
            exact ⟨hx, by simpa [omega_compl] using hxω⟩
        · intro hx
          rcases hx with hx | hx
          · rw [Set.mem_singleton_iff.mp hx]
            exact h_s_contains_omega
          · exact hx.1
      
      rw [hs]
      apply MeasurableSet.union 
      · exact hω
      · -- ⊢ MeasurableSet (s ∩ omega_compl)
        apply h_dirac_complete
        -- ⊢ (dira ω) (s ∩ omega_compl) = 0
        --
        have h1 : s ∩ omega_compl ⊆ omega_compl := by
          intro x hx
          exact hx.2
        have h2 : MeasurableSet omega_compl := by
          simp only [omega_compl]
          apply MeasurableSet.compl
          exact hω
        have h3 : (dira ω) omega_compl = 0 := by
          simp [MeasureTheory.dirac_eq_zero_iff_not_mem h2]
          simp [omega_compl]
        
        apply MeasureTheory.Measure.mono_null h1 h3
        
  case neg =>
    -- h_s_contains_omega : ω ∉ s
    apply h_dirac_complete s
    -- ⊢ (MeasureTheory.Measure.dirac ω) s = 0
    have h1 : (dira ω) s = 0 ∨ (dira ω) s = 1:= MeasureTheory.Measure.dirac_apply_eq_zero_or_one
    rcases h1 with h1_0  | h1_1
    · exact h1_0
    · -- h1_1 : (dira ω) s = 1
      -- h_ss_contains_omega : w ∉ s
      -- ⊢ (dira ω) s = 0
      have h2 : MeasurableSet omega_compl := by
        simp only [omega_compl]
        apply MeasurableSet.compl
        exact hω
      
      have h3 : (dira ω) omega_compl = 0 := by
        simp_all only [MeasureTheory.Measure.dirac_apply' ]
        simp_all only [Set.indicator_apply_eq_zero, Pi.one_apply, one_ne_zero, imp_false]
        simp_all only [omega_compl, MeasurableSet.compl_iff, Set.mem_compl_iff,
        Set.mem_singleton_iff, not_true_eq_false, not_false_eq_true]
      have h4 : s ⊆ omega_compl := by
        intro x hx
        simp only [omega_compl]
        intro hx2
        rw [hx2] at hx
        exact h_s_contains_omega hx
      -- 測度の単調性
      apply MeasureTheory.Measure.mono_null h4 h3
