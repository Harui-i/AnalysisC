import VersoManual
import AnalysisC

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option linter.hashCommand false

#doc (Manual) "解析学C レポート" =>
%%%
authors := ["harui"]
shortTitle := "解析学C"
%%%

このページは、解析学Cのレポート課題をLean 4で形式化したものへの案内です。
各レポートのLeanファイルは、このドキュメントと同じLakeプロジェクトで検査されます。

# レポート一覧

## レポート1

集合族
`F = {A | A または Aᶜ が可算集合である}`
がσ-加法族であること、および有限部分集合全体が生成するσ-加法族との関係を扱います。

Leanファイル: `AnalysisC/Report1.lean`

## レポート2

Leanファイル: `AnalysisC/Report2.lean`

## レポート3

Leanファイル: `AnalysisC/Report3.lean`

# ビルド

ローカルでは次のコマンドでHTMLを生成できます。

```
lake exe report
```

生成されたHTMLは `_out/html-multi/index.html` に置かれます。
GitHub Actionsでは、`main` または `master` ブランチへのpush時に `_out/html-multi` をGitHub Pagesへデプロイします。
