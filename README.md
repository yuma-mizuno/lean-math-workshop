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

以上の手順を最初から初心者向けにまとめたYouTubeの動画：
- [Windows編](https://youtu.be/LDfmNmzY5_8)
- [Mac編](https://youtu.be/d8DSHFBMWwU)

## 内容
Tutorialフォルダの中に以下の教材が入っています。
### Basic
Leanの基礎的な使い方や命題論理について
- Basic/Lecture1 命題論理
- Basic/Lecture2 mathlibの使い方
- Basic/Lecture3 任意と存在
- Basic/Lecture4 単射と全射
- Basic/Tactics 証明でよく使われるtacticについてのまとめ

### Advanced/Analysis
実関数の微分等の解析からいくつかのトピック
- Advanced/Analysis/Lecture1 微分係数の定義および基本的な命題
- Advanced/Analysis/Lecture2 平均値の定理
- Advanced/Analysis/Lecture3 閉区間のコンパクト性

### Advanced/Algebra
群論からいくつかのトピック
- Advanced/Algebra/Lecture1 群・部分群の定義と基本性質
- Advanced/Algebra/Lecture2 準同型の定義と基本性質
- Advanced/Algebra/Lecture3 群の集合への作用や同変写像
- Advanced/Algebra/Lecture4 左剰余類の集合、推移的`G`集合の構造定理
- Advanced/Algebra/Lecture5 正規部分群・商群・準同型定理

### Advanced/Category
圏論からいくつかのトピック
- Advanced/Category/Lecture1 圏の定義と例
- Advanced/Category/Lecture2 余極限の定義と例

## 参考書など
- [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/)は基礎的なことが詳しく書いてある教科書です。Leanで証明を書いていて知りたいことが出てきたらまずはこれを参考にすると良いです。[日本語訳](https://aconite-ac.github.io/theorem_proving_in_lean4_ja/)もあります。

- [A mathlib overview](https://leanprover-community.github.io/mathlib-overview.html)では、Leanの数学ライブラリmathlibで扱われている数学を概観できます。