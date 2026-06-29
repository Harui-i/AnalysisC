# AnalysisC
解析学Cのレポート課題をLean4で解きます。

## レポートページ

レポート用のHTMLページはVersoで生成します。

```sh
lake exe report
```

生成されたHTMLは `_out/html-multi/index.html` に置かれます。
Versoのmulti-page HTMLは、ローカルで `file://` から直接開くとページ遷移が正しく動かないことがあります。
ローカルで確認する場合は、次のようにHTTPサーバ越しに開いてください。

```sh
python3 -m http.server 8000 -d _out/html-multi
```

その後、<http://localhost:8000/> をブラウザで開きます。

GitHub Actionsでは、`main` または `master` ブランチへのpush時に `_out/html-multi` をGitHub Pagesへデプロイします。

## GitHub configuration

To set up your new GitHub repository, follow these steps:

* Under your repository name, click **Settings**.
* In the **Actions** section of the sidebar, click "General".
* Check the box **Allow GitHub Actions to create and approve pull requests**.
* Click the **Pages** section of the settings sidebar.
* In the **Source** dropdown menu, select "GitHub Actions".

After following the steps above, you can remove this section from the README file.
