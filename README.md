## 始め方
1. VS Code, Git, Leanをインストールします。（参考: [Leanのインストール](https://leanprover.github.io/lean4/doc/quickstart.html)）
2. ターミナル上でチュートリアルファイルを置きたいフォルダに移動して、以下のコマンドを実行します: 
```
git clone https://github.com/yuma-mizuno/lean-math-workshop.git
cd lean-math-workshop
lake exe cache get
```
3. VS Codeで`lean-math-workshop`フォルダを開きます。
4. VS Codeのエクスプローラーから、最初のレクチャーファイル`Tutorial/Basic/Lecture1.lean`を開きます。

## 内容
準備中。今後、内容が更新される予定です。

準備状況
- [x] Basic/Lecture1 命題論理
- [x] Basic/Lecture2 mathlibの使い方
- [x] Basic/Lecture3 任意と存在
- [x] Basic/Lecture4 単射と全射
- [x] Advanced/Analysis/Lecture1 微分係数の定義および基本的な命題
- [x] Advanced/Analysis/Lecture2 平均値の定理
- [x] Advanced/Analysis/Lecture3 閉区間のコンパクト性
- [x] Advanced/Algebra/Lecture1 群・部分群の定義と基本性質
- [x] Advanced/Algebra/Lecture2 準同型の定義と基本性質
- [x] Advanced/Algebra/Lecture3 群の集合への作用や同変写像
- [x] Advanced/Algebra/Lecture4 左剰余類の集合、推移的`G`集合の構造定理
- [ ] Advanced/Algebra/Lecture5 群の準同型定理（予定）
- [x] Advanced/Category/Lecture1 圏の定義と例
- [x] Advanced/Category/Lecture2 余極限の定義と例

## 参考書など
- [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/)は基礎的なことが詳しく書いてある教科書です。Leanで証明を書いていて知りたいことが出てきたらまずはこれを参考にすると良いです。[日本語訳](https://aconite-ac.github.io/theorem_proving_in_lean4_ja/)もあります。

- [A mathlib overview](https://leanprover-community.github.io/mathlib-overview.html)では、Leanの数学ライブラリmathlibで扱われている数学を概観できます。