import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Countable
import Mathlib.MeasureTheory.MeasurableSpace.Defs --可測空間の定義など
import Mathlib.MeasureTheory.SetAlgebra --有限加法族

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

/- ## 参考文献など myrefs

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

-- (1) FがSを全体集合とするσ-加法族であることを示す。
-- Mathlibの定義にあるクラスの項を構成することで示したことにする。
-- instanceを使えば作れるっぽい。

def is_in_F (A : Set α) := A.Countable ∨ Aᶜ.Countable

lemma empty_set_in_F : is_in_F (∅: Set α) := by
  rw [is_in_F]
  left
  -- ⊢ : ∅.Countable
  simp

-- ∀ s, MeasurableSet' s → MeasurableSet' sᶜ
lemma compl_in_F : ∀ s: Set α, is_in_F s → is_in_F sᶜ  :=  by
  -- ⊢ : ∀ (s : Set α), is_measurable s → is_measurable sᶜ
  intro s hs
  -- hs : is_measurable s
  -- ⊢ is_measurable sᶜ
  rw [is_in_F] at *
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


lemma iUnion_in_F : ∀ f : ℕ → Set α,
 (∀ i, is_in_F (f i)) → is_in_F (⋃i, f i) := by
  intro f h_all_i
  -- f: ℕ → Set α
  -- h_all_i:  ∀ i, is_measurable (f i)
  -- ⊢ is_measurable(⋃ i, f i)
  simp_all only [is_in_F] -- 定義を展開ざむらい
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
instance f_measurable_space : MeasurableSpace α where
  MeasurableSet' := is_in_F
  measurableSet_empty := empty_set_in_F
  measurableSet_compl := compl_in_F
  measurableSet_iUnion := iUnion_in_F

-- (2) FはSの有限部分集合全体が生成するσ-加法族であることを示しなさい。
/-
生成するσ-加法族ってMathlibでどう定義されてるんだ
inductive generateSetAlgebra {α : Type*} (𝒜 : Set (Set α)) : Set (Set α)
  | base (s : Set α) (s_mem : s ∈ 𝒜) : generateSetAlgebra 𝒜 s
  | empty : generateSetAlgebra 𝒜 ∅
  | compl (s : Set α) (hs : generateSetAlgebra 𝒜 s) : generateSetAlgebra 𝒜 sᶜ
  | union (s t : Set α) (hs : generateSetAlgebra 𝒜 s) (ht : generateSetAlgebra 𝒜 t) :
      generateSetAlgebra 𝒜 (s ∪ t)

これか？　なんか違う気がするんだけど
これ有限加法族やん！！！！！
σ-加法族は有限加法族だけど、有限加法族はσ-加法族とは限らない。
だから、「FはSの有限部分集合全体が生成する有限加法族である」が示せるならこの定義を使っても示せるけど、無理ならむり。

というかNatの定義も自然数を定義してる感じしなかったし、帰納型がそもそも直感的じゃないのかも。
↓これが自然数なの！？って感じだろ.

inductive MyNat where
| zero
| succ (n : MyNat)

Mathlibのσ-加法族関連は、可測空間として定義されてるって感じかな？↓は生成するσ加法族っぽいかも

/-- Construct the smallest measure space containing a collection of basic sets -/
@[implicit_reducible]
def generateFrom (s : Set (Set α)) : MeasurableSpace α where
  MeasurableSet' := GenerateMeasurable s
  measurableSet_empty := .empty
  measurableSet_compl := .compl
  measurableSet_iUnion := .iUnion

/-- The smallest σ-algebra containing a collection `s` of basic sets -/
inductive GenerateMeasurable (s : Set (Set α)) : Set α → Prop
  | protected basic : ∀ u ∈ s, GenerateMeasurable s u
  | protected empty : GenerateMeasurable s ∅
  | protected compl : ∀ t, GenerateMeasurable s t → GenerateMeasurable s tᶜ
  | protected iUnion : ∀ f : ℕ → Set α, (∀ n, GenerateMeasurable s (f n)) →
      GenerateMeasurable s (⋃ i, f i)
-/
-- (2) FはSの有限部分集合全体が生成するσ-加法族であることを示しなさい。

def finsubs_of_f : (Set (Set α )) := {A | A.Finite }

-- Definition `generated_measurablespace` of class type must be marked with `@[reducible]` or
-- `@[implicit_reducible]`
-- とのこと。よくわからんけど!
--@[reducible]
--def generated_measurablespace := @MeasurableSpace.generateFrom α finsubs_of_f

@[implicit_reducible]
def generated_measurable : MeasurableSpace α := MeasurableSpace.generateFrom  finsubs_of_f



-- この形式化であってる？
-- (2) FはSの有限部分集合全体が生成するσ-加法族であることを示しなさい。
-- つまりσ加法族の一致を示さなきゃいけないけど、どういう定義になってるんだ
--

-- ≤ のimplicit argument αに、αを渡すために@を使う
lemma problem_2_l1 : generated_measurable ≤ @f_measurable_space α  := by
  /-
  theorem generateFrom_le_iff {s : Set (Set α)} (m : MeasurableSpace α) :
    generateFrom s ≤ m ↔ s ⊆ { t | MeasurableSet[m] t } :=
    Iff.intro (fun h _ hu => h _ <| measurableSet_generateFrom hu) fun h => generateFrom_le h
  -/

  -- generateFrom_le_iffを使う
  simp only [generated_measurable, MeasurableSpace.generateFrom_le_iff]
  intro s hs
  simp only [MeasurableSet] at *
  simp only [f_measurable_space, is_in_F, finsubs_of_f] at *
  -- hs: s ∈ {A | A.Finite}
  -- ⊢ s ∈ {t | t.Countable ∨ tᶜ.Countable}
  left
  -- ⊢ s.Countable
  -- theorem mem_setOf {a : α} {p : α → Prop} : a ∈ { x | p x } ↔ p a := Iff.rfl
  -- ↔ を→にするために.1を使う
  have hs2 : s.Finite := Set.mem_setOf.1 hs
  -- s.Finite → s.Countableは自明だろ　さすがに定理あるはず
  exact Set.Finite.countable hs2

lemma problem_2_l2 : @f_measurable_space α ≤ generated_measurable := by
  intro s hs
  simp [MeasurableSet] at *
  simp [generated_measurable, f_measurable_space, is_in_F, finsubs_of_f] at *
  sorry


theorem problem_2 : @MeasurableSpace.generateFrom α finsubs_of_f = f_measurable_space := by
  rw [f_measurable_space, MeasurableSpace.generateFrom]
  simp_all only [MeasurableSpace.mk.injEq]
  --⊢ MeasurableSpace.GenerateMeasurable finsubs_of_f = is_in_F
  ext x
  -- extは外延性を使うtactic
  -- 外延性とは、同じものから作られているものは同じ　という主張
  constructor <;> intro h
  · --
    rw [is_in_F]
    rw [finsubs_of_f] at h
    left
    -- x: Set α
    -- h: MeasurableSpace.GenerateMeasurable {A | A.Finite} x
    -- ⊢ x.Countable
    -- なんか MeasurableSpace.GenerateMeasurableが帰納型であることを利用すればうまく証明できるんじゃね
    -- 帰納法とかmatchできないすか

    sorry
  · --
    -- h: is_in_F x
    -- MeasurableSpace.GenerateMeasurable finsubs_of_f x
    rw [is_in_F] at h
    rw [finsubs_of_f]
    -- h: x.Countable ∨ xᶜ.Countable
    -- ⊢ MeasurableSpace.GenerateMeasurable {A | A.Finite} x
    cases h with
    | inl h1 =>
      -- h1: x.Countable
      sorry
    | inr h2 =>
      -- h2: xᶜ.Countable
      sorry


end
