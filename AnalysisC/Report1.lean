import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Countable
import Mathlib.MeasureTheory.MeasurableSpace.Defs

/--
解析学C レポート問題No.1
問1
集合Sを固定し、
F = {A ∈ 2^S | AまたはAᶜ は可算集合である}
とおく。ただしAᶜはSを全体集合とするAの補集合を表す。以下の問いに答えなさい

(1) FがSを全体集合とするσ-加法族であることを示しなさい

(2) FはSの有限部分集合全体が生成するσ-加法族であることを示しなさい。

問2
(1)FはSを全体集合とする σ-加法族とする。S'をSの部分集合とする
S' ∩ F := {S' ∩ A | A ∈ F} はS'を全体集合とするσ-加法族であることを示しなさい。

(2) S, S'を集合とし、F'をS'を全体集合とするσ-加法族とする。
写像T: S → S'に対し
T^-1(F') := {T^-1(A') | A' ∈ F }はSを全体集合とするσ-加法族であることを示しなさい

(3) 全体集合Sを固定する. A ∈ 2^S に対しσ[{A}] = {∅ , A, Aᶜ, S}が成り立つことを示しなさい.
ただしAᶜはSを全体集合とするAの補集合を表す.
-/
-- これがないとexpected lemmaで怒られてダルいので置く。本質的意味はない
lemma ezlemma : 1+1=2 := by
  rfl

section

/- ## 参考文献など

Mathlib doc: Measurable spaces and measurable functions:
https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/SetAlgebra.html#MeasureTheory.IsSetAlgebra
↑Mathlibのドキュメント

Mathlib probability study note documentation:
https://auto-res.github.io/mathlib_probability_study_note/
↑日本語で書いてくれるみなさんほんまありがとう

Yuma Mizunoさんによる講義ノート:
https://yuma-mizuno.github.io/measure-theory/ja/
↑versoで作られているらしい。
"最初は個人的な目的で（あまり人に見せる前提ではなく）講義で扱う定理の証明の整理や演習問題の解答作成など部分的にLeanを利用していたのですが、
それらのコードをもとにCodexの助けを借りながらまとまったドキュメントを作ることができました。

近い将来、このような形式化付きの数学教材は増えていきそうと思います。"とのこと。
UCC(University College Cork)
https://ucc-ie-public.courseleaf.com/modules/?details&srcdb=2025&code=MA3064


## メモ

MathlibのMeasurable spaceの定義はこのようになっている.

/-- A measurable space is a space equipped with a σ-algebra. -/
@[class] structure MeasurableSpace (α : Type*) where
  /-- Predicate saying that a given set is measurable. Use `MeasurableSet` in the root namespace
  instead. -/
  MeasurableSet' : Set α → Prop
  /-- The empty set is a measurable set. Use `MeasurableSet.empty` instead. -/
  measurableSet_empty : MeasurableSet' ∅
  /-- The complement of a measurable set is a measurable set. Use `MeasurableSet.compl` instead. -/
  measurableSet_compl : ∀ s, MeasurableSet' s → MeasurableSet' sᶜ
  /-- The union of a sequence of measurable sets is a measurable set. Use a more general
  `MeasurableSet.iUnion` instead. -/
  measurableSet_iUnion : ∀ f : ℕ → Set α, (∀ i, MeasurableSet' (f i)) → MeasurableSet' (⋃ i, f i)

自分で定義しようとすると、complの扱いが難しいなーと思っていた。
例えば
def F : Set S := {A | A.Countable ∨ (Aᶜ).Countable }
とか書くと

Invalid field `Countable`: The environment does not contain `Subtype.Countable`, so it is
not possible to project the field `Countable` from an expression A of type `{ x // x ∈ S }`
Error code: lean.invalidField

などと怒られる。よくわからんけど、Aが{x // x ∈ S}という部分型になってしまっていて、これのCountableがないとのこと。

MathlibだとMeasurableSet'というのを定義している。これはなに？MeasurableSetとの違いは？

これstructureの文法を勘違いしてたから、MeasurableSet'というのが事前に定義されていて参照されていたのかと思った。違う。
"""
structure Point (α : Type u) where
  mk ::
  x : α
  y : α

Values of type Point are created using Point.mk a b, and the fields of a point p are accessed
using Point.x p and Point.y p (but p.x and p.y also work, see below). The structure command also
generates useful recursors and theorems. Here are some of the constructions generated for the
declaration above.
""" (https://lean-lang.org/theorem_proving_in_lean4/Structures-and-Records/)
とあるのでMeasurableSet'というのは、 Setα → Prop という型を持つ項の名前だ。大文字にするの紛らわしくないんすか？
てかmeasurableSet_empty : MeasurableSet' ∅ してるけどこれRecursiveじゃね. まあええか
-/
-- これがないとexpected lemmaで怒られてダルいので置く。本質的意味はない
lemma ezlemma2 : 1+1=2 := by
  rfl

/--
問1

集合Sを固定し、
F = {A ∈ 2^S | AまたはAᶜ は可算集合である}
とおく。ただしAᶜはSを全体集合とするAの補集合を表す。以下の問いに答えなさい

(1) FがSを全体集合とするσ-加法族であることを示しなさい

(2) FはSの有限部分集合全体が生成するσ-加法族であることを示しなさい。
-/
theorem my_theorem : 1+1 = 2 := by simp

variable {α : Type*}

/-
通る
def F : Set (Set α) :=
  {A | A.Countable ∨ Aᶜ.Countable}

通る
def F : Set (Set S) :=
  { A | A.Countable  ∨ Aᶜ.Countable }
-/

-- (1) FがSを全体集合とするσ-加法族であることを示す。
-- Mathlibの定義にあるクラスの項を構成することで示したことにする。
-- instanceを使えば作れるっぽい。

def is_measurable (A : Set α) := A.Countable ∨ Aᶜ.Countable

lemma empty_set_is_measurable : is_measurable (∅: Set α) := by
  rw [is_measurable]
  left
  -- ⊢ : ∅.Countable
  simp

-- ∀ s, MeasurableSet' s → MeasurableSet' sᶜ
lemma compl_measurable : ∀ s: Set α, is_measurable s → is_measurable sᶜ  :=  by
  -- ⊢ : ∀ (s : Set α), is_measurable s → is_measurable sᶜ
  intro s hs
  -- hs : is_measurable s
  -- ⊢ is_measurable sᶜ
  rw [is_measurable] at *
  -- hs : s.Countable ∨ sᶜ.Countable
  -- ⊢: sᶜ.Countable ∨ sᶜᶜ.Countable
  rcases hs with hsl | hsr
  · -- hsl: s.Countable
    right
    --⊢ : sᶜᶜ.Countable
    -- ᶜᶜを外したい
    -- simp_all is all you need!
    simp_all
  · -- hsr: sᶜ.Countable
    left
    exact hsr


lemma iUnion_measurable : ∀ f : ℕ → Set α,
 (∀ i, is_measurable (f i)) → is_measurable (⋃i, f i) := by
  intro f h_all_i
  -- f: ℕ → Set α
  -- h_all_i:  ∀ i, is_measurable (f i)
  -- ⊢ is_measurable(⋃ i, f i)
  simp_all only [is_measurable] -- 定義を展開ざむらい
  -- h_all_i : ∀ i, (f i).Countable ∨ (f i)ᶜ.Countable
  -- ⊢ (⋃ i, f i).Countable ∨ (⋃ i, f i)ᶜ.Countable
  by_cases hAll_countable: ∀ n, (f n).Countable
  · -- ∀ n, (f n).Countable
    left
    -- ⊢ (⋃ i, f i).Countable
    simp_all
  · --
    push Not at hAll_countable
    -- hAll_countable: ∃ n, ¬(f n).Countable
    obtain ⟨n, hn⟩ := hAll_countable
    -- hn: ¬(f n).Countable
    -- ⊢ (⋃ i, f i).Countable ∨ (⋃ i, f i)ᶜ.Countable
    right
    -- ⊢ (⋃ i, f i)ᶜ.Countable
    -- ⊢ (⋂ i, (f i)ᶜ).Countable
    -- ∃ i, (f i)ᶜ.Countable なら十分だろ
    suffices hyp : ∃ i, (f i)ᶜ.Countable from by
      obtain ⟨i, hi⟩ := hyp
      -- hi : (f i)ᶜ.Countable
      -- ⊢ (⋂ i, (f i)ᶜ).Countable
      have h1 : (⋂ i, (f i)ᶜ) ⊆ (f i)ᶜ := by
        -- ⊢ ⋂ i, (f i)ᶜ ⊆ (f i)ᶜ
        intro x hx
        -- hx : x ∈ ⋂ i, (f i)ᶜ
        -- ⊢ x ∈ (f i)ᶜ
        simp_all
      simp only [Set.compl_iUnion]
      -- hi (f i)ᶜ.Countable
      -- h1: ⋂ i, (f i)ᶜ ⊆ (f i)ᶜ
      -- ⊢ (⋂ i, (f i)ᶜ).Countable
      -- A ⊆ B, B.Countable → A.Countable
      -- 名前がわかりづらすぎる。monoってなに？？？？
      exact Set.Countable.mono h1 hi
    grind





-- 可測空間の型クラスのインスタンスを作る(これで(1)が解けたということになる)
instance : MeasurableSpace α where
  MeasurableSet' := is_measurable
  measurableSet_empty := empty_set_is_measurable
  measurableSet_compl := compl_measurable
  measurableSet_iUnion := iUnion_measurable

end
